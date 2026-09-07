#!/usr/bin/env python3
"""Read-only inventory of existing normal public evidence; no crypto calls.

Private recipient files are stat'ed for size/mode only, never opened. No input
vector, private answer or key is read. This does not redo integer comparisons.
"""
from collections import Counter
from pathlib import Path
import hashlib
import json
import re
import stat
import struct

HERE = Path(__file__).resolve().parent
CRYPTO = HERE.parents[1] / "crypto"
REPORTS = CRYPTO / "reports/positive_001"
RUNTIME = CRYPTO / "runtime/positive_001"
HEADER = struct.Struct(">8sB32s32sH32s32s32sQ")


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def canon(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False).encode()


def main():
    manifest = json.loads((CRYPTO / "source_manifest.json").read_text())
    report = json.loads((REPORTS / "report.json").read_text())
    commands_raw = (REPORTS / "commands.jsonl").read_bytes()
    assert sha(commands_raw) == report["commands_sha256"]
    commands = [json.loads(row) for row in commands_raw.splitlines()]
    context_raw = (RUNTIME / "public/context.json").read_bytes()
    context = json.loads(context_raw)
    context_id = sha(context_raw)
    assert canon(context) == context_raw and context_id == report["context_sha256"]
    validation = json.loads((REPORTS / "validated_context.json").read_text())
    pins = {n: e["sha256"] for n, e in manifest["runtime_sources"].items()}
    for name, expected in pins.items():
        assert sha((RUNTIME / "source" / name).read_bytes()) == expected
    assert validation["source_sha256"] == report["source_sha256"] == pins
    assert validation["validated"] and validation["context_id"] == context_id
    assert validation["counts"]["subgroup_checks"] == 593
    assert validation["counts"]["context_consistency_rows"] == 16

    def header(path, expected_kind):
        # Called only on existing public outputs/inputs referenced by the run.
        assert path.resolve().is_relative_to((RUNTIME / "public").resolve())
        raw = path.read_bytes()
        fields = HEADER.unpack(raw[:HEADER.size])
        magic, kind, params, ctx, row, row_hash, recipient, token, length = fields
        assert magic == b"RSDDH001" and kind == expected_kind
        assert ctx.hex() == context_id and params.hex() == context["params_id"]
        assert len(raw) == HEADER.size + length
        if kind == 1:
            assert len(raw) == 148147 and length == 578*256
            assert row == 65535 and row_hash == recipient == token == bytes(32)
        else:
            assert kind == 2 and len(raw) == 691 and length == 2*256
            entry = context["recipients"][row]
            assert [row_hash.hex(), recipient.hex(), token.hex()] == [entry[k] for k in ("row_sha256", "recipient_id", "token_sha256")]
        return raw

    validated_before_cache = False
    cached, public_outputs, public_calls, private_calls = 0, 0, 0, 0
    fresh_randomizer_fields = []
    output_link_checks = 0
    forbidden = {"signed_score", "bsgs_baby_entries", "bsgs_giant_iterations", "bsgs_table_ns", "bsgs_decode_ns"}

    def public_keys(value):
        if type(value) is dict:
            assert not (set(value) & forbidden)
            for child in value.values():
                public_keys(child)
        elif type(value) is list:
            for child in value:
                public_keys(child)

    for record in commands:
        argv = record["command"]
        name = argv[1]
        flags = dict(zip(argv[2::2], argv[3::2], strict=True))
        assert record["exit_code"] == 0
        if name == "validate-context":
            assert "--validated-context-sha256" not in flags
            assert record["stdout"] == validation
            validated_before_cache = True
        if "--validated-context-sha256" in flags:
            assert validated_before_cache and flags["--validated-context-sha256"] == context_id
            cached += 1
        if record["role"].startswith("public_"):
            assert "--sk" not in flags
            assert "--vector" not in flags or name == "encode-query"
            public_calls += 1
        if name == "reader-decrypt":
            assert record["stdout"] is None and record["elapsed_ns"] is None
            assert record["private_output_and_timing_omitted"] is True
            private_calls += 1
            continue
        public_keys(record["stdout"])
        if name in ("issuer-encrypt", "host-learn", "host-infer"):
            raw = header(Path(flags["--out"]), 2 if name == "host-infer" else 1)
            assert sha(raw) == record["stdout"]["sha256"]
            assert len(raw) == record["stdout"]["bytes"]
            public_outputs += 1
            if name == "issuer-encrypt":
                fresh_randomizer_fields.append(raw[179:435])
            elif name == "host-infer":
                state = header(Path(flags["--acc"]), 1)
                assert raw[179:435] == state[179:435]
                output_link_checks += 1

    assert commands[0]["command"][1] == "keygen"
    phases = commands[0]["stdout"]["phases"]
    phase_counts = Counter(p["command"] for p in phases)
    assert phase_counts == {"initializer": 1, "recipient-register": 16, "recipient-finalize": 16}
    assert len(fresh_randomizer_fields) == 33
    assert len(set(fresh_randomizer_fields)) == 33
    assert (RUNTIME / "public/acc33.ct").read_bytes() == (RUNTIME / "public/final.replayed.ct").read_bytes()

    # Credential inventory reads filesystem metadata only, not credential bytes.
    keydir = RUNTIME / "private/recipients"
    assert stat.S_IMODE(keydir.stat().st_mode) == 0o700
    paths = sorted(keydir.iterdir())
    assert [p.name for p in paths] == [f"r{i:02d}.key" for i in range(16)]
    for p in paths:
        info = p.lstat()
        assert stat.S_ISREG(info.st_mode) and stat.S_IMODE(info.st_mode) == 0o600 and info.st_size == 435

    rows = json.loads((CRYPTO / "rows.json").read_text())
    assert rows == context["rows"] and len(rows) == 16
    assert all(len(row) == 577 and all(type(x) is int and -127 <= x <= 127 for x in row) for row in rows)
    bounds = [32*127*sum(abs(x) for x in row) for row in rows]
    assert max(bounds) == 14219936
    text = (CRYPTO / "group.py").read_text()
    group_hex = re.search(r'P = int\("""(.*?)"""', text, re.S).group(1)
    p = int("".join(group_hex.split()), 16)
    assert (p-1)//2 > 2*max(bounds)

    result = {"schema": "designated-source-public-records-review-v1", "passed": True,
              "script_sha256": sha(Path(__file__).read_bytes()),
              "source_manifest_sha256": sha((CRYPTO / "source_manifest.json").read_bytes()),
              "source_pins": pins, "context_sha256": context_id,
              "commands_sha256": sha(commands_raw), "command_count": len(commands),
              "commands_by_name": dict(Counter(r["command"][1] for r in commands)),
              "setup_child_counts": dict(phase_counts), "trusted_validation_precedes_cache_calls": cached,
              "public_role_calls_without_private_key_inputs": public_calls,
              "private_calls_with_stdout_and_individual_elapsed_omitted": private_calls,
              "public_output_headers_and_hashes_checked": public_outputs,
              "distinct_fresh_public_randomizer_fields": len(set(fresh_randomizer_fields)),
              "inference_public_randomizer_links": output_link_checks,
              "exact_final_public_replay": True,
              "remaining_dedicated_recipient_files_metadata_only": len(paths),
              "private_directory_mode": "0700", "private_key_modes": "0600", "private_key_bytes": 435,
              "row_bounds": bounds, "maximum_row_bound": max(bounds), "group_bits": p.bit_length(),
              "q_greater_than_twice_bound": True,
              "private_key_input_vector_or_answer_bytes_read": False,
              "cryptographic_execution": False,
              "limits": ["Distinct c0 values do not prove randomness independence or unpredictability.",
                         "No private integer comparison was independently rerun; its existing source/result was inspected.",
                         "Setup/issuer and aggregate benchmark timings remain public telemetry outside the protected transcript.",
                         "Inventory and hashes do not prove physical erasure, OS isolation or source correctness."]}
    (HERE / "public_records.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
