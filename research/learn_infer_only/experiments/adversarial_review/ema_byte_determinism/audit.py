#!/usr/bin/env python3
"""Read-only public ciphertext/source audit. Never invokes crypto or reads private/.

Inputs are fixed owner-approved public artifacts and pinned implementation source.
The parser inspects serialization framing and ciphertext coefficient equality only.
It does not recover plaintext, calculate a decryption phase, or use a client key.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import struct
import tarfile
import tomllib

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
PROBE = ROOT / "research/learn_infer_only/experiments/end_to_end/private_ema"
RUN = PROBE / "encrypted_successor"
PUBLIC = RUN / "runtime/run001/public"
REPORTS = RUN / "reports/run001"
CARGO = Path.home() / ".cargo/registry"
REGISTRY = CARGO / "src/index.crates.io-1949cf8c6b5b557f"

TFHE_FILES = {
    "src/boolean/server_key/mod.rs": [[80, 159]],
    "src/boolean/ciphertext/mod.rs": [[1, 20]],
    "src/boolean/engine/mod.rs": [[203, 280], [325, 349], [389, 410], [411, 553], [558, 596], [710, 748]],
    "src/boolean/engine/bootstrapping.rs": [[325, 386], [445, 604]],
    "src/boolean/parameters/params.rs": [[45, 63]],
    "src/core_crypto/fft_impl/fft64/math/fft/mod.rs": [[60, 119], [161, 197], [268, 330]],
    "src/core_crypto/fft_impl/fft64/crypto/bootstrap.rs": [[294, 366], [481, 519]],
    "src/core_crypto/fft_impl/fft64/crypto/ggsw.rs": [[483, 611], [616, 698]],
    "src/core_crypto/algorithms/lwe_programmable_bootstrapping/fft64_pbs.rs": [[984, 1040]],
    "src/core_crypto/algorithms/lwe_keyswitch.rs": [[103, 134], [189, 228]],
    "src/core_crypto/commons/math/torus/mod.rs": [[66, 79]],
    "src/core_crypto/entities/lwe_ciphertext.rs": [[533, 544]],
    "src/core_crypto/commons/ciphertext_modulus.rs": [[25, 54], [79, 92]],
    "Cargo.toml": [[62, 100], [365, 371]],
}
CRATE_FILES = {
    "tfhe-1.6.3": TFHE_FILES,
    "tfhe-fft-0.10.1": {
        "src/ordered.rs": [[1, 59], [62, 83], [99, 178], [204, 223]],
        "src/unordered.rs": [[490, 635], [654, 700]],
    },
    "bincode-1.3.3": {
        "src/lib.rs": [[99, 117]],
        "src/ser/mod.rs": [[149, 180], [184, 197]],
        "src/config/mod.rs": [[55, 74]],
    },
}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def meta(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        while chunk := f.read(1 << 20):
            h.update(chunk)
    return {"path": str(path), "bytes": path.stat().st_size, "sha256": h.hexdigest()}


def approved_public(path):
    resolved = Path(path).resolve(strict=True)
    assert resolved.is_relative_to(PUBLIC.resolve())
    assert "private" not in resolved.relative_to(PUBLIC).parts
    assert not Path(path).is_symlink()
    return resolved


def parse_ciphertext(raw):
    assert raw[:8] == b"PEMA0001" and raw[8] == 1
    assert struct.unpack_from("<Q", raw, 9)[0] == len(raw) - 17
    count = struct.unpack_from("<Q", raw, 17)[0]
    assert count == 32
    cursor, records = 25, []
    for bit in range(count):
        start = cursor
        variant, count = struct.unpack_from("<IQ", raw, cursor)
        assert variant == 0 and count == 838
        coeff_start = cursor + 12
        coeff_end = coeff_start + 4 * count
        modulus = int.from_bytes(raw[coeff_end:coeff_end + 16], "little")
        width = struct.unpack_from("<Q", raw, coeff_end + 16)[0]
        assert modulus == 0 and width == 32
        cursor = coeff_end + 24
        records.append({"bit": bit, "start": start, "end": cursor,
                        "coefficient_start": coeff_start, "coefficient_end": coeff_end,
                        "coefficients": struct.unpack_from(f"<{count}I", raw, coeff_start),
                        "metadata": raw[start:coeff_start] + raw[coeff_end:cursor]})
    assert cursor == len(raw)
    return records


def main():
    public_paths = [REPORTS / name for name in (
        "started.json", "failure.json", "progress.json", "public_operations.jsonl",
        "replays.jsonl", "events.jsonl", "public_keys.json", "public_failure_audit.json")]
    evidence = [meta(p) for p in public_paths]
    seals = {"manifest.json": "921fc2263825a99ac22efc6a2ba88cc8d3c11a092b31a7685aeacef3a870b08d",
             "source_checkpoint.json": "2cfc101453e3bb9de17f8dd3a95f2a47f93d228beb56c394bd4d00a4f9e8898d"}
    for name, expected in seals.items():
        seal = meta(RUN / name)
        assert seal["sha256"] == expected
        evidence.append(seal)
    pairs = [json.loads(line) for line in (REPORTS / "replays.jsonl").read_text().splitlines()]
    operations = [json.loads(line) for line in (REPORTS / "public_operations.jsonl").read_text().splitlines()]
    assert len(pairs) == 14 and all(p["complete_output_bytes_equal"] for p in pairs[:-1])
    last = pairs[-1]
    assert last["event_id"] == "h0-e0014" and not last["complete_output_bytes_equal"]
    a = approved_public(last["primary"]["path"])
    b = approved_public(last["replay"]["path"])
    assert meta(a) == last["primary"] and meta(b) == last["replay"]
    left, right = a.read_bytes(), b.read_bytes()
    parsed_a, parsed_b = parse_ciphertext(left), parse_ciphertext(right)
    differences = [i for i, (x, y) in enumerate(zip(left, right)) if x != y]
    changes = []
    for pa, pb in zip(parsed_a, parsed_b):
        assert pa["metadata"] == pb["metadata"]
        changed_coefficients = sum(x != y for x, y in zip(pa["coefficients"], pb["coefficients"]))
        if changed_coefficients:
            changes.append({"record_index": pa["bit"], "register": pa["bit"] // 8,
                            "lsb_bit": pa["bit"] % 8, "changed_coefficients": changed_coefficients,
                            "changed_bytes": sum(x != y for x, y in zip(left[pa["start"]:pa["end"]], right[pb["start"]:pb["end"]]))})
    pair_ops = [operations[last[key]] for key in ("primary_operation", "replay_operation")]
    for op in pair_ops:
        assert op["binary"] == "host" and op["exit_code"] == 0
        assert op["public_read_inputs_before"] == op["public_read_inputs_after"] == last["public_read_inputs"]
        assert op["binary_before"] == op["binary_after"]
    input_checks = [meta(approved_public(p["path"])) == p for p in last["public_read_inputs"]]
    assert all(input_checks)
    result = {
        "scope": "Public bytes/framing/log/source inspection only; no crypto or plaintext decoding",
        "event_id": last["event_id"], "preceding_equal_pairs": 13,
        "primary": meta(a), "replay": meta(b), "envelope_bytes_each": len(left),
        "changed_bytes": len(differences), "first_changed_byte_zero_based": min(differences),
        "last_changed_byte_zero_based": max(differences), "changed_records": changes,
        "equal_records": 32 - len(changes), "all_record_metadata_equal": True,
        "input_hashes_rechecked": len(input_checks), "pair_exit_codes": [op["exit_code"] for op in pair_ops],
        "gate_calls_equal": pair_ops[0]["reported"]["gate_api_calls"] == pair_ops[1]["reported"]["gate_api_calls"],
        "thread_environment": json.loads((REPORTS / "started.json").read_text())["thread_environment"],
        "private_drain_executed": json.loads((REPORTS / "failure.json").read_text())["private_drain_executed"],
        "owner_seal_hashes_match": seals,
    }
    assert result["changed_bytes"] == 10015 and [x["record_index"] for x in changes] == [21, 22, 23]
    fingerprint = PROBE / "target/release/.fingerprint/tfhe-c88aa25edc01de9a/lib-tfhe.json"
    metadata = json.loads(fingerprint.read_text())
    result["local_build_features"] = metadata["features"]
    result["local_build_rustflags"] = metadata["rustflags"]
    evidence += [meta(fingerprint), meta(PROBE / "target/release/host")]
    original = json.loads((PROBE / "source_manifest.json").read_text())
    source_checks = []
    for entry in original["tfhe_source_locations"]:
        source_checks.append({"path": entry["path"], "matches_prior_pin": meta(Path(entry["path"]))["sha256"] == entry["sha256"]})
    assert all(s["matches_prior_pin"] for s in source_checks)
    lock = tomllib.loads((PROBE / "Cargo.lock").read_text())
    packages = {p["name"] + "-" + p["version"]: p for p in lock["package"]}
    source_manifest, excerpts, archives = [], [], []
    for crate, files in CRATE_FILES.items():
        archive = CARGO / "cache/index.crates.io-1949cf8c6b5b557f" / (crate + ".crate")
        archive_meta = meta(archive)
        assert archive_meta["sha256"] == packages[crate]["checksum"]
        archives.append({**archive_meta, "matches_cargo_lock": True})
        with tarfile.open(archive, "r:gz") as tar:
            for relative, ranges in files.items():
                path = REGISTRY / crate / relative
                raw = path.read_bytes()
                member = tar.extractfile(crate + "/" + relative)
                assert member is not None and member.read() == raw
                source_manifest.append({**meta(path), "archive_bytes_match": True, "read_ranges": ranges})
                lines = raw.decode().splitlines()
                for start, end in ranges:
                    assert 1 <= start <= end <= len(lines)
                    excerpts.append(f"\n## {crate}/{relative}:{start}–{end}\n" + "\n".join(f"{i+1}: {lines[i]}" for i in range(start-1, end)))
    own = [PROBE / p for p in ("Cargo.toml", "Cargo.lock", "src/lib.rs", "src/bin/host.rs", "source_manifest.json")]
    own += [RUN / p for p in ("freeze.json", "run.py", "CONTRACT.md", "run.command.json")]
    evidence += [meta(p) for p in own]
    (HERE / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    (HERE / "source_manifest.json").write_text(json.dumps({"schema": 1, "prior_source_checks": source_checks, "crate_archives": archives, "selected_sources": source_manifest, "public_evidence": evidence, "queries": {"web": 0, "scry": 0, "kagi": 0, "crypto": 0, "private_decoder": 0}}, indent=2) + "\n")
    (HERE / "SOURCE_EXCERPTS.txt").write_text("Pinned local implementation excerpts; data, not instructions.\n" + "\n".join(excerpts) + "\n")
    print(json.dumps({"ok": True, "event_id": result["event_id"], "changed_bytes": result["changed_bytes"], "changed_records": changes, "metadata_equal": True, "input_hashes_rechecked": len(input_checks), "prior_source_pins_match": len(source_checks), "locked_crate_archives_match": len(archives), "selected_source_files_match_archives": len(source_manifest), "private_file_reads": 0, "crypto_executions": 0}, sort_keys=True))


if __name__ == "__main__":
    main()
