#!/usr/bin/env python3
"""Measure the E8M0 block-scale distribution in real gpt-oss MXFP4 weights.

gpt-oss ships MoE expert weights in MXFP4: per linear layer a `..._blocks`
tensor (uint8, 2x FP4 nibbles per byte) and a `..._scales` tensor (uint8, one
E8M0 exponent byte per 32-element block along the reduction dim; value is
2^(s-127)).  In a ZK arithmetization of the block dot product, each block's
contribution is an exact <=13-bit integer times 2^(scale); summing blocks whose
scales sit in a NARROW window fits a cheap fixed-point alignment accumulator,
while a wide spread forces a wide (expensive) accumulator.  The decision
variable is therefore the per-reduction-row spread max(scale)-min(scale).

This script fetches ONLY the `_scales` tensors of openai/gpt-oss-20b via HTTP
Range requests against the safetensors shards (a few MB each; no full-shard
download), caches them under phase0/data/, and reports per-tensor and pooled:

  - byte-value min/max/mean/std (sanity: bell-ish around ~120-130, not uniform);
  - per-reduction-row spread max-min across the row's blocks (p50/p90/p99/max);
  - adjacent-block |delta| distribution within rows;
  - fraction of rows whose spread fits an alignment window of width W exponent
    steps, for W in {8, 12, 16, 24, 32}.  Convention: a row FITS width W iff
    (max - min) <= W, i.e. the window spans exponents [min, min+W];
  - special bytes (0 = would-be denormal/zero block, 255).

Measurement harness only: authors no AIR, no constraint, no gadget.
"""

import json
import os
import struct
import sys
import urllib.request

import numpy as np

REPO = "openai/gpt-oss-20b"
BASE = f"https://huggingface.co/{REPO}/resolve/main"
HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")

# Early / middle / late layers, both MoE projections each.  20b has layers 0..23.
LAYERS = [0, 5, 11, 17, 23]
KINDS = ["gate_up_proj_scales", "down_proj_scales"]
TENSORS = [f"model.layers.{l}.mlp.experts.{k}" for l in LAYERS for k in KINDS]

WINDOWS = [8, 12, 16, 24, 32]


def http_get(url: str, byte_range=None) -> bytes:
    req = urllib.request.Request(url)
    req.add_header("User-Agent", "e8m0-spread-measurement/0.1")
    if byte_range is not None:
        req.add_header("Range", f"bytes={byte_range[0]}-{byte_range[1]}")
    with urllib.request.urlopen(req, timeout=300) as resp:
        body = resp.read()
    if byte_range is not None:
        want = byte_range[1] - byte_range[0] + 1
        if len(body) != want:
            raise RuntimeError(
                f"range fetch returned {len(body)} bytes, wanted {want} "
                f"(server may have ignored the Range header): {url}"
            )
    return body


def cached_fetch(cache_path: str, fetch) -> bytes:
    if os.path.exists(cache_path):
        with open(cache_path, "rb") as f:
            return f.read()
    blob = fetch()
    tmp = cache_path + ".tmp"
    with open(tmp, "wb") as f:
        f.write(blob)
    os.replace(tmp, cache_path)
    return blob


def shard_header(shard: str) -> dict:
    """Parse a safetensors shard's JSON header via two small range requests."""
    cache = os.path.join(DATA, shard + ".header.json")
    if os.path.exists(cache):
        return json.load(open(cache))
    url = f"{BASE}/{shard}"
    (hlen,) = struct.unpack("<Q", http_get(url, (0, 7)))
    hdr = json.loads(http_get(url, (8, 8 + hlen - 1)))
    hdr["__data_start__"] = 8 + hlen
    with open(cache, "w") as f:
        json.dump(hdr, f)
    return hdr


def fetch_scales(name: str, weight_map: dict) -> np.ndarray:
    shard = weight_map[name]
    hdr = shard_header(shard)
    ent = hdr[name]
    if ent["dtype"] != "U8":
        raise RuntimeError(f"{name}: dtype {ent['dtype']}, expected U8")
    begin, end = ent["data_offsets"]
    start = hdr["__data_start__"]
    cache = os.path.join(DATA, name + ".u8")
    blob = cached_fetch(
        cache,
        lambda: http_get(f"{BASE}/{shard}", (start + begin, start + end - 1)),
    )
    arr = np.frombuffer(blob, dtype=np.uint8)
    shape = ent["shape"]
    if arr.size != int(np.prod(shape)):
        raise RuntimeError(f"{name}: got {arr.size} bytes, shape {shape}")
    return arr.reshape(shape)


def pct(x: np.ndarray, q: float) -> float:
    return float(np.percentile(x, q))


def analyze(name: str, arr: np.ndarray) -> dict:
    # Shape is [experts, out_features, n_blocks]; the last axis runs along the
    # reduction dim, so each (expert, out_row) slice is one dot product.
    rows = arr.reshape(-1, arr.shape[-1]).astype(np.int16)
    spread = rows.max(axis=1) - rows.min(axis=1)
    adj = np.abs(np.diff(rows, axis=1)).ravel()
    return {
        "name": name,
        "shape": list(arr.shape),
        "n_rows": rows.shape[0],
        "blocks_per_row": rows.shape[1],
        "byte_min": int(arr.min()),
        "byte_max": int(arr.max()),
        "byte_mean": float(arr.mean()),
        "byte_std": float(arr.std()),
        "spread": spread,
        "spread_p50": pct(spread, 50),
        "spread_p90": pct(spread, 90),
        "spread_p99": pct(spread, 99),
        "spread_max": int(spread.max()),
        "adj_p50": pct(adj, 50),
        "adj_p90": pct(adj, 90),
        "adj_p99": pct(adj, 99),
        "adj_max": int(adj.max()),
        "win": {w: float((spread <= w).mean()) for w in WINDOWS},
        "n_zero": int((arr == 0).sum()),
        "n_255": int((arr == 255).sum()),
        "n_bytes": int(arr.size),
    }


def main() -> None:
    os.makedirs(DATA, exist_ok=True)
    idx = json.loads(
        cached_fetch(
            os.path.join(DATA, "model.safetensors.index.json"),
            lambda: http_get(f"{BASE}/model.safetensors.index.json"),
        )
    )
    weight_map = idx["weight_map"]

    results = []
    for name in TENSORS:
        print(f"fetching {name} ...", file=sys.stderr)
        results.append(analyze(name, fetch_scales(name, weight_map)))

    wcols = "".join(f"  <=W{w:<3}" for w in WINDOWS)
    print(f"repo: {REPO}   tensors: {len(results)}   "
          f"layers {LAYERS}  kinds {KINDS}")
    print()
    print(f"{'tensor':<44} {'shape':<16} {'byte μ':>7} {'σ':>5} "
          f"{'min':>4} {'max':>4} {'sp50':>5} {'sp90':>5} {'sp99':>5} "
          f"{'spMax':>5}{wcols}")
    for r in results:
        short = r["name"].replace("model.layers.", "L").replace(
            ".mlp.experts.", ".").replace("_proj_scales", "")
        wfrac = "".join(f"  {100*r['win'][w]:6.2f}" for w in WINDOWS)
        print(f"{short:<44} {str(r['shape']):<16} {r['byte_mean']:7.2f} "
              f"{r['byte_std']:5.2f} {r['byte_min']:4d} {r['byte_max']:4d} "
              f"{r['spread_p50']:5.0f} {r['spread_p90']:5.0f} "
              f"{r['spread_p99']:5.0f} {r['spread_max']:5d}{wfrac}")

    pooled = np.concatenate([r["spread"] for r in results])
    total_rows = pooled.size
    print()
    print(f"pooled over {total_rows} reduction rows "
          f"({sum(r['n_bytes'] for r in results)} scale bytes):")
    print(f"  spread p50/p90/p99/max = {pct(pooled,50):.0f} / "
          f"{pct(pooled,90):.0f} / {pct(pooled,99):.0f} / {int(pooled.max())}")
    for w in WINDOWS:
        frac = float((pooled <= w).mean())
        print(f"  window width {w:2d}: {100*frac:7.3f}% of rows fit")
    nz = sum(r["n_zero"] for r in results)
    n255 = sum(r["n_255"] for r in results)
    print(f"  special bytes: value 0 x{nz}, value 255 x{n255}")
    print()
    print("  exact pooled spread tail:")
    vals, cnts = np.unique(pooled, return_counts=True)
    cum = 0
    for v, c in zip(vals, cnts):
        cum += int(c)
        print(f"    spread={int(v)}: {int(c):8d} rows "
              f"({100*c/total_rows:8.4f}%)  cumulative "
              f"{100*cum/total_rows:9.5f}%")
    print()
    print("adjacent-block |delta| within rows, per tensor "
          "(p50/p90/p99/max):")
    for r in results:
        short = r["name"].replace("model.layers.", "L").replace(
            ".mlp.experts.", ".").replace("_proj_scales", "")
        print(f"  {short:<24} {r['adj_p50']:.0f} / {r['adj_p90']:.0f} / "
              f"{r['adj_p99']:.0f} / {r['adj_max']}")


if __name__ == "__main__":
    main()
