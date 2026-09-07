#!/usr/bin/env python3
"""Pin/verify read-only source evidence; never invokes production arithmetic."""
import argparse
import json
from pathlib import Path
from reference import require, sha

HERE = Path(__file__).resolve().parent
E2E = HERE.parent
VENDOR = Path("/Users/ember/dev/breadstuffs/vendor/fhe-dregg")
REGISTRY = Path("/Users/ember/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f")
MATH = REGISTRY / "fhe-math-0.1.1"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--verify", action="store_true")
    args = parser.parse_args()
    target = HERE / "source-map.json"
    if args.verify:
        manifest = json.loads(target.read_bytes())
        for entry in manifest["sources"]:
            require(sha(Path(entry["path"]).read_bytes()) == entry["sha256"], "source changed: " + entry["path"])
        print(json.dumps({"ok": True, "sources_rehashed": len(manifest["sources"]), "source_map_sha256": sha(target.read_bytes())}))
        return
    require(not target.exists(), "do not overwrite frozen source pins")
    evidence = [
        (E2E / "crypto/src/main.rs", [[15, 37], [75, 132], [220, 254]], "[SOURCE: implementation] Fixed parameters, canonical full-CT wrapper and public Learn/Infer commands"),
        (E2E / "crypto/Cargo.toml", [[1, 20]], "[SOURCE: dependency selection] Path dependency and no optional TFHE NTT feature"),
        (E2E / "crypto/Cargo.lock", [], "[SOURCE: dependency versions] Frozen resolved crate graph"),
        (E2E / "crypto/params.json", [], "[SOURCE: retained metadata] Parameter identity used by captured execution"),
        (VENDOR / "src/proto/bfv.proto", [[1, 9]], "[SOURCE: schema] Repeated ciphertext polynomial bytes; absent seed and zero level"),
        (VENDOR / "src/bfv/ciphertext.rs", [[167, 223]], "[SOURCE: implementation] Full ciphertext protobuf encoding and polynomial decoder"),
        (VENDOR / "src/bfv/ops/mod.rs", [[54, 69], [149, 164], [229, 255]], "[SOURCE: implementation] Componentwise add/sub and unscaled ciphertext-plaintext polynomial product"),
        (VENDOR / "src/bfv/plaintext_vec.rs", [[93, 139]], "[SOURCE: implementation] Polynomial encoding copies query prefix and zero-pads; converts to NTT"),
        (VENDOR / "src/bfv/plaintext.rs", [[153, 166]], "[SOURCE: implementation] UInt plaintext encoder delegates to PlaintextVec"),
        (MATH / "src/proto/rq.proto", [[1, 17]], "[SOURCE: schema] NTT tag=2; degree, coefficient bytes, variable-time flag"),
        (MATH / "src/rq/convert.rs", [[15, 47], [151, 210]], "[SOURCE: implementation] Serialized coefficients are power basis regardless of representation tag; inverse then forward on roundtrip"),
        (MATH / "src/rq/ops.rs", [[112, 163]], "[SOURCE: implementation] NTT polynomial multiplication is per-limb pointwise modular multiplication"),
        (MATH / "src/rq/mod.rs", [[161, 208], [303, 323]], "[SOURCE: implementation] Representation switch and variable-time/public transform dispatch"),
        (MATH / "src/zq/mod.rs", [[747, 770]], "[SOURCE: implementation] Coefficient packing width is bit_length(q-1)"),
        (REGISTRY / "fhe-util-0.1.1/src/lib.rs", [[58, 125]], "[SOURCE: implementation] Contiguous little-endian bitstream transcode"),
        (MATH / "src/ntt/mod.rs", [[5, 15]], "[SOURCE: backend selection] Native NTT when optional TFHE features absent"),
        (MATH / "src/ntt/native.rs", [[28, 64], [67, 124], [126, 232], [244, 311], [314, 347]], "[SOURCE: implementation] Bit-reversed root tables, butterfly schedules, inverse scale, deterministic primitive-root selection"),
        (E2E / "crypto/target/release/.fingerprint/fhe-math-6bfde6bc930a05a6/lib-fhe_math.json", [], "[SOURCE: local build metadata] Actual retained dependency feature list is empty; native backend selected"),
        (E2E / "host_runtime/benchmark.py", [[173, 201]], "[SOURCE: fixture construction] Explicit public deterministic synthetic vectors/queries; 40 Learns, four Infers, window32"),
        (E2E / "host_runtime/source_pins.json", [], "[SOURCE: retained provenance] Source and binary hashes for captured original run"),
        (E2E / "host_runtime/runtime/run_001/resident-crypto", [], "[SOURCE: executable identity only] Historical copied binary is rehashed, never executed here"),
    ]
    sources = [{"path": str(p.resolve()), "sha256": sha(p.read_bytes()), "line_ranges": ranges, "claim": claim}
               for p, ranges, claim in evidence]
    historical = json.loads((E2E / "host_runtime/source_pins.json").read_bytes())
    require(sources[0]["sha256"] == historical["crypto_source_sha256"]["src/main.rs"], "historical source identity")
    require(sources[-1]["sha256"] == historical["crypto_binary_sha256"], "historical binary identity")
    features = json.loads(Path(sources[17]["path"]).read_bytes())["features"]
    require(features == "[]", "native backend fingerprint")
    manifest = {"schema": "independent-public-arithmetic-source-map-v1", "sources": sources,
                "source_and_captured_binary_pins_match": True, "search_queries": 0,
                "scope": "Read-only local source inspection and hashes, not Rust execution semantics or a source-to-binary proof"}
    target.write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({"ok": True, "sources_pinned": len(sources), "source_map_sha256": sha(target.read_bytes())}))


if __name__ == "__main__":
    main()
