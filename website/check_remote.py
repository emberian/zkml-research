#!/usr/bin/env python3
"""Opt-in check: fetch the exact public evidence blobs and verify their hashes."""
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
from urllib.parse import quote
from urllib.request import Request, urlopen

HERE = Path(__file__).resolve().parent


def check(source):
    url = "https://raw.githubusercontent.com/emberian/zkml-research/" + source["revision"] + "/" + quote(source["path"])
    try:
        with urlopen(Request(url, headers={"User-Agent": "zkml-research-evidence-check/1"}), timeout=30) as response:
            actual = hashlib.sha256(response.read()).hexdigest()
            return {"path": source["path"], "revision": source["revision"], "status": response.status,
                    "sha256_matches": actual == source["source_sha256"], "ok": actual == source["source_sha256"]}
    except Exception as error:
        return {"path": source["path"], "revision": source["revision"], "ok": False, "error": str(error)}


if __name__ == "__main__":
    manifest = json.loads((HERE / "dist/source-manifest.json").read_text())
    sources = {(s["path"], s["revision"]): s for s in manifest["sources"].values()}
    with ThreadPoolExecutor(max_workers=4) as executor:
        results = list(executor.map(check, sources.values()))
    print(json.dumps({"ok": all(r["ok"] for r in results), "checks": results}, indent=2))
    raise SystemExit(0 if all(r["ok"] for r in results) else 1)
