#!/usr/bin/env python3
"""Public metadata only: source pins and cost table for the single frozen run."""
import csv
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[4]
TFHE = Path("/Users/ember/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/tfhe-1.6.3")
OLD = REPO / "research/learn_infer_only/experiments/he_closure_costs/tfhe_ema_probe"


def pin(path, scope):
    return {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "bytes": path.stat().st_size, "read_scope": scope}


def main():
    results_path = ROOT / "runs/run_001/results.json"
    results = json.loads(results_path.read_text())
    assert not results["errors"]
    assert results["source_hashes_unchanged"]
    own = [ROOT / "CONTRACT.md", ROOT / "Cargo.toml", ROOT / "Cargo.lock", ROOT / "run.py",
           ROOT / "collect.py", *sorted((ROOT / "src").rglob("*.rs"))]
    sources = {
        "schema": "resident-private-ema-sources-v1",
        "scope": "Two-step honest encrypted EMA, API/file role separation and sampled exact byte replay; no implementation privacy proof.",
        "rustc": subprocess.check_output(["rustc", "--version", "--verbose"], text=True),
        "cargo": subprocess.check_output(["cargo", "--version"], text=True).strip(),
        "build_command": "cargo build --offline --release --manifest-path Cargo.toml > build.log 2>&1",
        "run_command": "python3 -u run.py > run_001.log 2>&1",
        "collection_command": "python3 collect.py",
        "build_log": pin(ROOT / "build.log", "Complete retained successful compiler log"),
        "own_sources": [pin(path, "Owned full source; Cargo.lock pins resolved dependencies") for path in own],
        "prior_probe": [pin(OLD / "src/main.rs", "Complete prior arithmetic source read, unchanged"),
                        pin(OLD / "Cargo.toml", "Complete prior dependency declaration read, unchanged"),
                        pin(OLD / "Cargo.lock", "Copied then Cargo updated the new package entry; dependency lock retained unchanged here")],
        "tfhe_source_locations": [
            pin(TFHE / "src/boolean/server_key/mod.rs", "Complete public gate wrappers, including MUX, read"),
            pin(TFHE / "src/boolean/ciphertext/mod.rs", "Complete ciphertext enum/Serde and compressed-ciphertext source read"),
            pin(TFHE / "src/boolean/engine/mod.rs", "Lines 411-580 read: MUX branch equations and beginning of AND; randomness locations searched, not a whole-engine audit"),
            pin(TFHE / "src/boolean/engine/bootstrapping.rs", "Lines 430-610 read: bootstrap/key-switch evaluation; random-generator uses searched, not a whole-file audit"),
            pin(TFHE / "src/boolean/parameters/params.rs", "Lines 46-80 read: selected and adjacent named Boolean parameter constants"),
            pin(TFHE / "src/boolean/public_key/standard.rs", "Randomness/test names searched only; not complete source inspection"),
        ],
        "parameter_claim": "Uses PARAMETERS_ERROR_PROB_2_POW_MINUS_165 exactly; source name only, no new noise/security/PQ estimate",
        "binary_hashes": results["binary_hashes"],
        "result_file": pin(results_path, "Public run record only; private key/request/audit files are not read by this collector"),
        "private_material_policy": "No private-key hash or plaintext audit content in this manifest. Client key and synthetic audit files remain in ignored private run directory. Large public keys remain locally retained but ignored for repository size.",
        "runtime_test_scope": "Normal setup, encrypted init/ingress, two logical Learn and two Infer operations, each host operation replayed exactly once. No malformed-input, routing, extraction or 384-step run.",
    }
    (ROOT / "source_manifest.json").write_text(json.dumps(sources, indent=2, sort_keys=True) + "\n")
    columns = ["operation", "role", "wall_seconds", "peak_rss_bytes", "read_seconds", "keygen_seconds",
               "encrypt_seconds", "evaluate_seconds", "serialize_write_seconds", "decrypt_seconds",
               "work_seconds", "serialized_bytes", "output_bits", "and_calls", "xor_calls", "not_calls",
               "mux_calls", "trivial_encrypt_calls"]
    with (ROOT / "costs.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=columns)
        writer.writeheader()
        for operation in results["operations"]:
            report = operation.get("reported", {})
            row = {"operation": operation["name"], "role": report.get("role", ""),
                   "wall_seconds": operation["subprocess_wall_ns"] / 1e9,
                   "peak_rss_bytes": operation.get("peak_rss_bytes", ""),
                   "serialized_bytes": report.get("serialized_bytes", ""),
                   "output_bits": report.get("output_bits", report.get("ciphertext_bits", ""))}
            for timing in ("read", "keygen", "encrypt", "evaluate", "serialize_write", "decrypt", "work"):
                row[timing + "_seconds"] = report.get(timing + "_ns", 0) / 1e9
            for gate in ("and", "xor", "not", "mux", "trivial_encrypt"):
                row[gate + "_calls"] = report.get("gate_api_calls", {}).get(gate, 0)
            writer.writerow(row)
    print(json.dumps({"source_manifest_sha256": hashlib.sha256((ROOT / "source_manifest.json").read_bytes()).hexdigest(),
                      "results_sha256": hashlib.sha256(results_path.read_bytes()).hexdigest(),
                      "operations": len(results["operations"]),
                      "logical_learns": results["logical_learn_count"],
                      "correctness": results["all_correctness_checks_passed"],
                      "byte_replay": results["all_tested_byte_replays_match"]}))


if __name__ == "__main__":
    main()
