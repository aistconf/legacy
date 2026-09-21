#!/usr/bin/env python3
"""Create a conservative static mirror from an Internet Archive snapshot."""

from __future__ import annotations

import argparse
import collections
import html
from html.parser import HTMLParser
import mimetypes
import os
from pathlib import Path
import posixpath
import re
import subprocess
import tempfile
import time
from urllib.error import HTTPError, URLError
from urllib.parse import quote, unquote, urljoin, urlparse, urlunparse
from urllib.request import Request, urlopen


SKIP_SCHEMES = ("mailto:", "tel:", "javascript:", "data:", "blob:")
SKIP_PATH_PARTS = ("/wp-admin", "/wp-login", "/xmlrpc.php", "/feed/", "/comments/")
ASSET_EXTS = {
    ".css", ".js", ".png", ".jpg", ".jpeg", ".gif", ".svg", ".webp", ".ico",
    ".woff", ".woff2", ".ttf", ".eot", ".pdf", ".doc", ".docx", ".xls", ".xlsx",
    ".zip", ".mp3", ".mp4", ".webm", ".ogg", ".xml", ".json", ".txt",
}
CSS_URL_RE = re.compile(r"url\(\s*(['\"]?)(.*?)\1\s*\)", re.I)
CSS_IMPORT_RE = re.compile(r"@import\s+(['\"])(.*?)\1", re.I)
URL_ATTRS = {"href", "src", "poster", "data-src", "data-lazy-src"}


def clean_original(raw: str, base: str) -> str | None:
    raw = html.unescape(raw.strip())
    if not raw or raw.startswith("#") or raw.lower().startswith(SKIP_SCHEMES):
        return None
    # Unwrap links which already contain a Wayback replay prefix.
    parsed_raw = urlparse(raw)
    if parsed_raw.netloc == "web.archive.org" and parsed_raw.path.startswith("/web/"):
        match = re.match(r"/web/[^/]+/(https?://.*)", parsed_raw.path)
        if match:
            raw = match.group(1)
            if parsed_raw.query:
                raw += "?" + parsed_raw.query
    absolute = urljoin(base, raw)
    parsed = urlparse(absolute)
    if parsed.scheme not in {"http", "https"}:
        return None
    # Fragments never affect the downloaded file.
    return urlunparse((parsed.scheme, parsed.netloc, parsed.path or "/", "", parsed.query, ""))


def safe_path(url: str, is_html: bool) -> Path:
    parsed = urlparse(url)
    raw_path = unquote(parsed.path or "/")
    parts = [p for p in raw_path.split("/") if p not in ("", ".", "..")]
    parts = [re.sub(r"[^A-Za-z0-9._@%+~()-]", "_", p) for p in parts]
    if is_html:
        if not parts:
            return Path("index.html")
        suffix = Path(parts[-1]).suffix.lower()
        if raw_path.endswith("/") or suffix not in {".html", ".htm"}:
            return Path(*parts, "index.html")
    return Path(*parts) if parts else Path("index.html")


class Collector(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=False)
        self.items: list[tuple[str, str, str]] = []

    def handle_starttag(self, tag, attrs):
        self._collect(tag, attrs)

    def handle_startendtag(self, tag, attrs):
        self._collect(tag, attrs)

    def _collect(self, tag, attrs):
        rel = ""
        for name, value in attrs:
            if name and name.lower() == "rel" and value:
                rel = value.lower()
        for name, value in attrs:
            if not name or not value:
                continue
            name = name.lower()
            if name in URL_ATTRS:
                kind = "page" if tag == "a" and name == "href" else "asset"
                if tag == "link" and name == "href":
                    kind = "asset" if any(x in rel for x in ("stylesheet", "icon", "preload")) else "ignore"
                self.items.append((name, value, kind))
            elif name == "srcset":
                for entry in value.split(","):
                    candidate = entry.strip().split()[0] if entry.strip() else ""
                    if candidate:
                        self.items.append((name, candidate, "asset"))


class Mirror:
    def __init__(self, root_url: str, timestamp: str, output: Path, base_path: str, max_urls: int):
        self.root_url = root_url.rstrip("/") + "/"
        self.timestamp = timestamp
        self.output = output
        self.base_path = "/" + base_path.strip("/") if base_path.strip("/") else ""
        root_host = urlparse(self.root_url).netloc.lower()
        self.allowed_hosts = {root_host, root_host.removeprefix("www."), "www." + root_host.removeprefix("www.")}
        self.queue = collections.deque([(self.root_url, "page")])
        self.seen: set[str] = set()
        self.max_urls = max_urls
        self.saved = 0
        self.saved_since_pause = 0
        self.failed: list[tuple[str, str]] = []
        self.attempts: collections.Counter[str] = collections.Counter()

    def is_internal(self, url: str) -> bool:
        return urlparse(url).netloc.lower() in self.allowed_hosts

    def should_skip(self, url: str) -> bool:
        parsed = urlparse(url)
        low_path = parsed.path.lower()
        if any(part in low_path for part in SKIP_PATH_PARTS):
            return True
        if parsed.query and any(k in parsed.query.lower() for k in ("replytocom=", "s=", "ical=", "share=")):
            return True
        return False

    def replay_url(self, original: str) -> str:
        return f"https://web.archive.org/web/{self.timestamp}id_/{original}"

    def local_url(self, target: str, kind: str) -> str:
        parsed = urlparse(target)
        ext = Path(parsed.path).suffix.lower()
        is_html = kind == "page" and ext not in ASSET_EXTS
        rel = safe_path(target, is_html).as_posix()
        return f"{self.base_path}/{rel}"

    def enqueue(self, target: str, kind: str):
        if not self.is_internal(target) or self.should_skip(target):
            return
        parsed = urlparse(target)
        # Strip tracking/cache-busting query strings; WordPress assets remain addressable.
        target = urlunparse((parsed.scheme, parsed.netloc, parsed.path or "/", "", "", ""))
        if target not in self.seen:
            self.queue.append((target, kind))

    def replace_url(self, raw: str, base: str, kind: str) -> str:
        target = clean_original(raw, base)
        if not target or not self.is_internal(target) or self.should_skip(target):
            return raw
        self.enqueue(target, kind)
        return self.local_url(target, kind)

    def rewrite_html(self, text: str, base: str) -> str:
        collector = Collector()
        try:
            collector.feed(text)
        except Exception:
            pass
        replacements: dict[str, str] = {}
        for attr, raw, kind in collector.items:
            if kind == "ignore":
                continue
            replacements[raw] = self.replace_url(raw, base, kind)
        # Attribute-aware replacement avoids changing visible text accidentally.
        for raw in sorted(replacements, key=len, reverse=True):
            new = replacements[raw]
            escaped_raw = re.escape(raw)
            text = re.sub(
                rf"(?P<prefix>\b(?:href|src|poster|data-src|data-lazy-src)\s*=\s*['\"]){escaped_raw}(?P<suffix>['\"])",
                lambda m, n=new: m.group("prefix") + n + m.group("suffix"),
                text,
                flags=re.I,
            )
        # srcset needs token-level rewriting.
        def srcset_repl(match):
            quote, value = match.group(1), match.group(2)
            entries = []
            for entry in value.split(","):
                bits = entry.strip().split()
                if bits:
                    bits[0] = self.replace_url(bits[0], base, "asset")
                entries.append(" ".join(bits))
            return f"srcset={quote}{', '.join(entries)}{quote}"
        text = re.sub(r"srcset\s*=\s*(['\"])(.*?)\1", srcset_repl, text, flags=re.I | re.S)
        return text

    def rewrite_css(self, text: str, base: str) -> str:
        def css_url(match):
            quote, raw = match.group(1), match.group(2)
            new = self.replace_url(raw, base, "asset")
            return f"url({quote}{new}{quote})"
        text = CSS_URL_RE.sub(css_url, text)
        text = CSS_IMPORT_RE.sub(lambda m: f"@import {m.group(1)}{self.replace_url(m.group(2), base, 'asset')}{m.group(1)}", text)
        return text

    def fetch(self, original: str):
        replay = quote(self.replay_url(original), safe="/:?=&%+@")
        # curl follows Wayback's nearest-capture redirects more reliably than
        # urllib on snapshots whose original host no longer resolves.
        with tempfile.NamedTemporaryFile() as tmp:
            proc = subprocess.run(
                [
                    "curl", "-fsSL", "--retry", "3", "--retry-delay", "1",
                    "--connect-timeout", "15", "--max-time", "90",
                    "-A", "Mozilla/5.0 AIST archival mirror",
                    "-o", tmp.name, "-w", "%{content_type}\n%{url_effective}", replay,
                ],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
            )
            if proc.returncode != 0:
                raise URLError(proc.stderr.decode("utf-8", errors="replace").strip())
            metadata = proc.stdout.decode("utf-8", errors="replace").splitlines()
            content_type = metadata[0] if metadata else ""
            final_url = metadata[1] if len(metadata) > 1 else replay
            tmp.seek(0)
            return tmp.read(), content_type, final_url

    def run(self):
        self.output.mkdir(parents=True, exist_ok=True)
        while self.queue and len(self.seen) < self.max_urls:
            original, kind = self.queue.popleft()
            parsed = urlparse(original)
            original = urlunparse((parsed.scheme, parsed.netloc, parsed.path or "/", "", "", ""))
            if original in self.seen:
                continue
            self.seen.add(original)
            try:
                body, content_type, final_url = self.fetch(original)
            except (HTTPError, URLError, TimeoutError, OSError) as exc:
                self.attempts[original] += 1
                network_block = "curl: (7)" in str(exc) or "curl: (28)" in str(exc)
                limit = 12 if network_block else 3
                if self.attempts[original] < limit:
                    print(f"RETRY {self.attempts[original]}/{limit - 1} {original}: {exc}", flush=True)
                    self.seen.discard(original)
                    self.queue.append((original, kind))
                    time.sleep(65 if network_block else 5)
                else:
                    self.failed.append((original, str(exc)))
                    print(f"FAIL {original}: {exc}", flush=True)
                continue
            lowered = content_type.lower()
            ext = Path(urlparse(original).path).suffix.lower()
            is_html = "text/html" in lowered or (kind == "page" and ext not in ASSET_EXTS)
            is_css = "text/css" in lowered or ext == ".css"
            target_path = self.output / safe_path(original, is_html)
            target_path.parent.mkdir(parents=True, exist_ok=True)
            if is_html or is_css:
                charset_match = re.search(r"charset=([^;\s]+)", content_type, re.I)
                charset = charset_match.group(1).strip("\"'") if charset_match else "utf-8"
                try:
                    text = body.decode(charset, errors="replace")
                except LookupError:
                    text = body.decode("utf-8", errors="replace")
                text = self.rewrite_html(text, original) if is_html else self.rewrite_css(text, original)
                body = text.encode("utf-8")
            target_path.write_bytes(body)
            self.saved += 1
            self.saved_since_pause += 1
            print(f"SAVE {original} -> {target_path.relative_to(self.output)}", flush=True)
            if self.saved_since_pause >= 14:
                print("PAUSE 65s to respect Internet Archive limits", flush=True)
                time.sleep(65)
                self.saved_since_pause = 0
            else:
                time.sleep(1.0)
        (self.output / ".nojekyll").touch()
        print(f"DONE saved={self.saved} seen={len(self.seen)} queued={len(self.queue)} failed={len(self.failed)}")
        if self.failed:
            (self.output / "mirror-failures.txt").write_text(
                "\n".join(f"{url}\t{error}" for url, error in self.failed) + "\n", encoding="utf-8"
            )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--url", required=True)
    parser.add_argument("--timestamp", required=True)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--base", required=True)
    parser.add_argument("--max-urls", type=int, default=800)
    args = parser.parse_args()
    Mirror(args.url, args.timestamp, args.output, args.base, args.max_urls).run()


if __name__ == "__main__":
    main()
