"""Fetch exactly the bytes a recompute needs from Hugging Face at the pinned revision, and check them.

The anchor chain: the registry's full-mode commitment pins each shard's file hash and header hash; the
Mac's shards matched those hashes (G0); `plan` runs on those shards and records the SHA-256 of every
byte range a job will read (shard headers, the layers' tensors, the embedding rows of the prompt).
`materialize` fetches those ranges by HTTP Range at the pinned revision, refuses any range whose
digest differs, and writes them at their offsets into sparse files, so `weights.Shards` reads them
unchanged. Bytes outside the plan are never read: a sparse hole reads as zeros, and nothing in the
plan's tensors lies in a hole.
"""
import hashlib
import json
import os
import sys
import time
import urllib.request

REPO = "openai/gpt-oss-20b"
REV = "6cee5e81ee83917806bbde320786a8fb61efebee"
BASE = f"https://huggingface.co/{REPO}/resolve/{REV}"


def plan(layers, ids, out_path):
    from weights import Shards, MANIFEST
    S = Shards()
    core = json.load(open(MANIFEST))["core"]
    shards = {s["path"]: s for s in core["shards"]}
    ranges = []

    def add(shard, off, n, what):
        with open(os.path.join(S.root, shard), "rb") as f:
            f.seek(off)
            b = f.read(n)
        assert len(b) == n
        ranges.append({"shard": shard, "off": off, "len": n, "sha256": hashlib.sha256(b).hexdigest(), "what": what})

    for shard in sorted(shards):
        (hdr, base), _ = S._open(shard)
        add(shard, 0, base, "header")
        hh = hashlib.sha256(open(os.path.join(S.root, shard), "rb").read(base)[8:]).hexdigest()
        assert hh == shards[shard]["header_hash"], (shard, "header hash differs from the registry")
    want = [n for n in S.where if any(n.startswith(f"model.layers.{l}.") for l in layers)]
    for n in sorted(want):
        shard = S.where[n]
        (hdr, base), _ = S._open(shard)
        b, e = hdr[n]["data_offsets"]
        add(shard, base + b, e - b, n)
    emb = "model.embed_tokens.weight"
    shard = S.where[emb]
    (hdr, base), _ = S._open(shard)
    row = hdr[emb]["shape"][1] * 2
    b0 = base + hdr[emb]["data_offsets"][0]
    for i in sorted(set(ids)):
        add(shard, b0 + i * row, row, f"{emb}[{i}]")
    idx = open(os.path.join(S.root, "model.safetensors.index.json"), "rb").read()
    aux = {a["path"]: a["hash"] for a in core["aux_files"]}
    assert hashlib.sha256(idx).hexdigest() == aux["model.safetensors.index.json"]
    rec = {"repo": REPO, "revision": REV, "commitment": json.load(open(MANIFEST))["commitment"],
           "shards": {k: {"byte_len": v["byte_len"], "file_hash": v["file_hash"], "header_hash": v["header_hash"]} for k, v in shards.items()},
           "index_sha256": aux["model.safetensors.index.json"], "ranges": ranges}
    json.dump(rec, open(out_path, "w"), indent=0)
    return rec


def _get(url, rng=None, tries=5):
    for k in range(tries):
        try:
            req = urllib.request.Request(url)
            if rng:
                req.add_header("Range", f"bytes={rng[0]}-{rng[1] - 1}")
            with urllib.request.urlopen(req, timeout=600) as r:
                if rng and r.status != 206:
                    raise IOError(f"range ignored ({r.status})")
                return r.read()
        except Exception as e:
            if k == tries - 1:
                raise
            time.sleep(2 ** k)


def materialize(plan_path, dst):
    P = json.load(open(plan_path))
    os.makedirs(dst, exist_ok=True)
    idx = _get(f"{BASE}/model.safetensors.index.json")
    assert hashlib.sha256(idx).hexdigest() == P["index_sha256"], "index.json differs from the registry"
    open(os.path.join(dst, "model.safetensors.index.json"), "wb").write(idx)
    for shard, s in P["shards"].items():
        with open(os.path.join(dst, shard), "wb") as f:
            f.truncate(s["byte_len"])
    t0, nbytes = time.time(), 0
    for r in P["ranges"]:
        b = _get(f"{BASE}/{r['shard']}", (r["off"], r["off"] + r["len"]))
        if hashlib.sha256(b).hexdigest() != r["sha256"]:
            raise SystemExit(f"FETCHED BYTES DIFFER: {r['what']}")
        with open(os.path.join(dst, r["shard"]), "r+b") as f:
            f.seek(r["off"])
            f.write(b)
        nbytes += len(b)
    return {"ranges": len(P["ranges"]), "bytes": nbytes, "seconds": round(time.time() - t0, 1)}


if __name__ == "__main__":
    if sys.argv[1] == "plan":
        layers = [int(x) for x in sys.argv[2].split(",")]
        ids = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "params-v0.json")))["ids"]
        r = plan(layers, ids, sys.argv[3])
        print(len(r["ranges"]), sum(x["len"] for x in r["ranges"]))
    else:
        print(materialize(sys.argv[2], sys.argv[3]))
