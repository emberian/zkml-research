#!/usr/bin/env python3
"""Dependency-free, allowlisted static research index. Never publish source trees."""
from __future__ import annotations

import argparse
import hashlib
import html
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
from html.parser import HTMLParser
from urllib.parse import quote, unquote, urlsplit

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OUT = HERE / "dist"
STATUSES = {"executed": "Executed", "derived": "Derived", "source": "Source", "open": "Open"}
TOPICS = {"proof-systems": "Proof systems", "encrypted-learning": "Encrypted learning", "mental-autarky": "Mental autarky"}


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(*args: str) -> bytes:
    return subprocess.check_output(["git", "-C", str(ROOT), *args], stderr=subprocess.PIPE)


def esc(value: object) -> str:
    return html.escape(str(value), quote=True)


def json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode()


def public_source(path: str) -> Path:
    p = Path(path)
    if p.is_absolute() or ".." in p.parts or not p.parts:
        raise ValueError(f"Non-relative source: {path}")
    if path != "README.md" and p.parts[0] not in {"docs", "notes", "research"}:
        raise ValueError(f"Source outside public evidence roots: {path}")
    if any(part.startswith(".") or part in {"runtime", "archive", "signer_route_001", "verified_route_001"} for part in p.parts):
        raise ValueError(f"Excluded source path: {path}")
    for ancestor in [p, *p.parents]:
        if (ROOT / ancestor).is_symlink():
            raise ValueError(f"Symlink source: {path}")
    resolved = (ROOT / p).resolve()
    if not resolved.is_relative_to(ROOT) or not resolved.is_file():
        raise ValueError(f"Missing public source: {path}")
    git("ls-files", "--error-unmatch", "--", path)
    ignored = subprocess.run(["git", "-C", str(ROOT), "check-ignore", "--no-index", "-q", "--", path])
    if ignored.returncode == 0:
        raise ValueError(f"Ignored source cannot be published: {path}")
    return resolved


def source_records(data: dict, preview: bool) -> tuple[dict, dict]:
    records, lock = {}, {}
    for key, source in data["sources"].items():
        path = source["path"]
        raw = public_source(path).read_bytes()
        lines = raw.splitlines(keepends=True)
        start, end = source["lines"]
        if not (1 <= start <= end <= len(lines)):
            raise ValueError(f"Invalid source line range {key}: {start}–{end}; file has {len(lines)} lines")
        excerpt = b"".join(lines[start - 1:end])
        lock[key] = {"path": path, "lines": [start, end], "excerpt_sha256": digest(excerpt)}
        revision = git("log", "-1", "--format=%H", "--", path).decode().strip()
        committed = git("show", f"{revision}:{path}")
        committed_excerpt = b"".join(committed.splitlines(keepends=True)[start - 1:end])
        if committed_excerpt != excerpt:
            if not preview:
                raise ValueError(f"Reviewed source differs from committed evidence: {path}. Commit it before publication; --preview permits a local draft.")
            revision = data["branch"]
            committed = raw
        anchor = f"#L{start}" + (f"-L{end}" if end != start else "")
        records[key] = {**lock[key], "label": source["label"], "revision": revision,
                        "source_sha256": digest(committed),
                        "url": f'{data["repository"]}/blob/{revision}/{quote(path)}{anchor}'}
    return records, lock


def source_link(source: dict, text: str | None = None, cls: str = "") -> str:
    return f'<a class="{esc(cls)}" href="{esc(source["url"])}">{esc(text or source["label"])} <span aria-hidden="true">↗</span></a>'


def render(data: dict, records: dict) -> bytes:
    base, repo = data["base_path"], data["repository"]
    paths = []
    for path in data["paths"]:
        steps = "".join(f'<li>{source_link(records[step["source"]], step["label"])}</li>' for step in path["steps"])
        paths.append(f'''<article class="reading-path" id="path-{esc(path['id'])}">
          <div class="path-label"><span>{esc(path['number'])}</span><h3>{esc(path['title'])}</h3></div>
          <p class="path-question">{esc(path['question'])}</p><p>{esc(path['description'])}</p>
          <ol>{steps}</ol><a class="path-result" href="#{esc(path['result'])}">See a related result <span aria-hidden="true">↓</span></a>
        </article>''')
    cards = []
    for card in data["cards"]:
        if card["status"] not in STATUSES or card["topic"] not in TOPICS:
            raise ValueError(f"Unknown card category: {card['id']}")
        evidence = "".join(f'<li>{source_link(records[key])}<span class="source-id">SHA-256 {records[key]["excerpt_sha256"][:12]}… · excerpt</span></li>' for key in card["sources"])
        cards.append(f'''<article class="result-card" id="{esc(card['id'])}" data-topic="{esc(card['topic'])}" data-status="{esc(card['status'])}">
          <div class="card-meta"><span class="badge {esc(card['status'])}">{STATUSES[card['status']]}</span><span>{TOPICS[card['topic']]}</span></div>
          <h3><a href="#{esc(card['id'])}">{esc(card['title'])}</a></h3>
          <div class="metric">{esc(card['metric'])}</div><p class="metric-label">{esc(card['metric_label'])}</p>
          <p class="card-body">{esc(card['body'])}</p>
          <div class="boundary"><span>What this does not establish</span><p>{esc(card['limit'])}</p></div>
          <details><summary>Evidence and scope <span>{len(card['sources'])} {'source' if len(card['sources']) == 1 else 'sources'}</span></summary><ul class="evidence-list">{evidence}</ul></details>
        </article>''')
    topic_options = "".join(f'<option value="{key}">{value}</option>' for key, value in TOPICS.items())
    status_options = "".join(f'<option value="{key}">{value}</option>' for key, value in STATUSES.items())
    template = (HERE / "index.html").read_text()
    replacements = {
        "BASE": base, "REPO": repo, "REVIEWED": esc(data["reviewed"]),
        "PATHS": "\n".join(paths), "CARDS": "\n".join(cards),
        "TOPIC_OPTIONS": topic_options, "STATUS_OPTIONS": status_options,
        "CARD_COUNT": str(len(cards)),
        "VERDICTS": f'{repo}/blob/{data["branch"]}/docs/VERDICTS.md',
        "GAME_LINK": source_link(records["game"], "Read the resident security game"),
        "HOUSE_LINK": source_link(records["house"], "Read the repository’s house rule"),
        "CREDENTIALS_LINK": source_link(records["credentials"], "Read the credential boundary"),
    }
    for key, value in replacements.items():
        template = template.replace("{{" + key + "}}", value)
    if re.search(r"\{\{[A-Z_]+\}\}", template):
        raise ValueError("Unexpanded template token")
    return template.encode()


class Links(HTMLParser):
    def __init__(self):
        super().__init__()
        self.ids: set[str] = set()
        self.references: list[str] = []
        self.errors: list[str] = []

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if "id" in attrs:
            if attrs["id"] in self.ids:
                self.errors.append(f'Duplicate id: {attrs["id"]}')
            self.ids.add(attrs["id"])
        for key in ("href", "src"):
            if key in attrs:
                self.references.append(attrs[key])
        if tag == "img" and "alt" not in attrs:
            self.errors.append("Image missing alternative text")


def validate(files: dict[str, bytes], data: dict, records: dict) -> dict:
    page = Links()
    page.feed(files["index.html"].decode())
    issues = page.errors
    allowed_external = {data["repository"], data["repository"] + "/blob/" + data["branch"] + "/docs/VERDICTS.md"}
    allowed_external.update(source["url"] for source in records.values())
    for ref in page.references:
        url = urlsplit(ref)
        if url.scheme:
            if ref.startswith("https://emberian.github.io/zkml-research/"):
                continue
            if ref not in allowed_external:
                issues.append(f"External URL outside the curated allowlist: {ref}")
        elif ref.startswith("#"):
            if unquote(url.fragment) not in page.ids:
                issues.append(f"Missing fragment: {ref}")
        elif ref.startswith(data["base_path"]):
            relative = unquote(url.path[len(data["base_path"]):]) or "index.html"
            if relative not in files:
                issues.append(f"Missing generated asset: {ref}")
        else:
            issues.append(f"Local URL missing project base path: {ref}")
    forbidden = re.compile(rb"/Users/|/home/|file://|localhost|127\.0\.0\.1|BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY|github_pat_|gh[pousr]_[A-Za-z0-9]{20,}|sk-[A-Za-z0-9]{20,}")
    for name, content in files.items():
        if forbidden.search(content):
            issues.append(f"Private/local material detected in output: {name}")
    if issues:
        raise ValueError("\n".join(issues))
    return {"ok": True, "cards": len(data["cards"]), "sources": len(records), "html_links_and_assets": len(page.references), "generated_files": len(files), "public_bytes": sum(map(len, files.values()))}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Verify the existing build exactly, without writing")
    parser.add_argument("--refresh-sources", action="store_true", help="Explicitly accept the currently selected evidence excerpts after review")
    parser.add_argument("--preview", action="store_true", help="Permit reviewed but not yet committed evidence for a local draft")
    args = parser.parse_args()
    if args.check and args.refresh_sources:
        parser.error("--check and --refresh-sources cannot be combined")
    data = json.loads((HERE / "catalog.json").read_text())
    if data["base_path"] != "/zkml-research/" or data["repository"] != "https://github.com/emberian/zkml-research":
        raise ValueError("Unexpected publication target")
    if len({c["id"] for c in data["cards"]}) != len(data["cards"]):
        raise ValueError("Duplicate result IDs")
    records, lock = source_records(data, args.preview)
    lock_path = HERE / "source-lock.json"
    if args.refresh_sources:
        lock_path.write_bytes(json_bytes(lock))
    if not lock_path.exists() or json.loads(lock_path.read_text()) != lock:
        raise ValueError("Evidence excerpts changed. Review the selected source text and card wording, then use --refresh-sources explicitly.")
    files = {"index.html": render(data, records), ".nojekyll": b"",
             "source-manifest.json": json_bytes({"schema": 1, "reviewed": data["reviewed"], "scope": "Curated excerpts; current verdicts remain authoritative. Source files are linked, not copied.", "sources": records})}
    for name in ("style.css", "app.js", "favicon.svg"):
        files["assets/" + name] = (HERE / "assets" / name).read_bytes()
    report = validate(files, data, records)
    files["build-manifest.json"] = json_bytes({"schema": 1, "files": {name: digest(content) for name, content in sorted(files.items())}})
    if args.check:
        actual = {str(path.relative_to(OUT)): path.read_bytes() for path in OUT.rglob("*") if path.is_file()}
        if actual != files:
            differing = sorted(name for name in set(actual) | set(files) if actual.get(name) != files.get(name))
            raise ValueError("Build drift: " + ", ".join(differing))
    else:
        if OUT.is_symlink():
            raise ValueError("Refusing symlink output directory")
        if OUT.exists():
            shutil.rmtree(OUT)
        OUT.mkdir()
        for name, content in files.items():
            destination = OUT / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(content)
    report["mode"] = "checked" if args.check else "built"
    report["generated_files"] = len(files)
    report["public_bytes"] = sum(map(len, files.values()))
    print(json.dumps(report, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        print(f"Site build failed: {error}", file=sys.stderr)
        raise SystemExit(1)
