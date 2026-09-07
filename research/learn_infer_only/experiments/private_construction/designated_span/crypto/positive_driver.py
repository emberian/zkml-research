#!/usr/bin/env python3
"""Normal positive designated-DDH path. No adversarial or extraction experiments."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import platform
import secrets
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
SOURCES = ["crypto.py", "group.py", "native_pow.py", "rows.json"]
READS = {0: 0, 1: 7, 32: 8, 33: 15}  # Declared before sampling any inputs.


def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), allow_nan=False).encode()


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write(path, obj, private=False):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True, mode=0o700 if private else 0o755)
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600 if private else 0o644)
    with os.fdopen(fd, "wb") as out:
        out.write(canonical(obj) + b"\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime", type=Path, default=HERE / "runtime/positive_001")
    parser.add_argument("--reports", type=Path, default=HERE / "reports/positive_001")
    args = parser.parse_args()
    runtime, reports = args.runtime.resolve(), args.reports.resolve()
    runtime.mkdir(parents=True, mode=0o700, exist_ok=False)
    reports.mkdir(parents=True, exist_ok=False)
    private, public, source = runtime / "private", runtime / "public", runtime / "source"
    private.mkdir(mode=0o700)
    public.mkdir()
    source.mkdir()
    for name in SOURCES:
        shutil.copy2(HERE / name, source / name)
    source_pins = {name: sha(source / name) for name in SOURCES}
    native = Path("/opt/homebrew/opt/openssl@3/lib/libcrypto.3.dylib").resolve()
    predeclared = {"classification": "predeclared positive normal flow", "learn_count": 33, "capacity": 32,
                   "reads_after_admissions": {str(k): v for k, v in READS.items()}, "expected_expiries": 1,
                   "dimension": 577, "inputs": "fresh OS-backed private signed int8 vectors", "source_sha256": source_pins,
                   "driver_sha256": sha(__file__), "native_library": str(native), "native_library_sha256": sha(native)}
    write(reports / "predeclared.json", predeclared)
    rows = json.loads((source / "rows.json").read_text())
    context, zero = public / "context.json", public / "zero.ct"
    binary = source / "crypto.py"
    records, private_records = [], []
    expected_digest = None

    def call(command, role, private_output=False, cache=True, **flags):
        argv = [str(binary), command]
        if command not in ("keygen", "params"):
            argv += ["--context", str(context)]
            if cache and expected_digest:
                argv += ["--validated-context-sha256", expected_digest]
        for key, value in flags.items():
            if value is not None:
                argv += ["--" + key.replace("_", "-"), str(value)]
        before = time.perf_counter_ns()
        done = subprocess.run(argv, capture_output=True, timeout=300)
        elapsed = time.perf_counter_ns() - before
        assert done.returncode == 0, f"normal {command} failed; diagnostic retained privately"
        result = json.loads(done.stdout)
        record = {"command": argv, "role": role, "exit_code": done.returncode,
                  "elapsed_ns": None if private_output else elapsed,
                  "stdout": None if private_output else result,
                  "private_output_and_timing_omitted": private_output}
        records.append(record)
        with (reports / "commands.jsonl").open("ab") as sink:
            sink.write(canonical(record) + b"\n")
        if private_output:
            private_records.append({"command": argv, "elapsed_ns": elapsed, "result": result})
        return result

    start = time.perf_counter_ns()
    setup = call("keygen", "setup_orchestrator", pk=context, sk=private / "recipients", zero=zero)
    validation = call("validate-context", "trusted_setup_public_validation", cache=False)
    assert validation["validated"] and validation["source_sha256"] == source_pins
    assert validation["context_id"] == setup["context_id"] == sha(context)
    expected_digest = validation["context_id"]
    write(reports / "validated_context.json", validation)
    queries = {}
    for row_id in READS.values():
        row_path = public / f"row{row_id:02d}.json"
        row_path.write_bytes(canonical(rows[row_id]))
        query_path = public / f"query{row_id:02d}.json"
        call("encode-query", "public_query_encoder", vector=row_path, out=query_path)
        queries[row_id] = query_path
    # Both branches use the same honest public bytes; this is a normal cache equivalence check.
    full_query = public / "query00.full.json"
    call("encode-query", "full_validation_comparison", cache=False, vector=public / "row00.json", out=full_query)
    assert full_query.read_bytes() == queries[0].read_bytes()
    accumulator, queue, plain_queue = zero, [], []
    exact_results, inputs = [], []
    live_byte_counts = []

    def infer(admissions):
        row_id = READS[admissions]
        output = public / f"read{admissions:02d}.ct"
        result = call("host-infer", "public_host", acc=accumulator, query=queries[row_id], out=output)
        assert result["object_type"] == "recipient_output" and result["row_id"] == row_id
        meta = call("inspect", "public_output_inspector", ct=output)
        assert meta["sha256"] == result["sha256"] and meta["bytes"] == 691
        answer = call("reader-decrypt", f"dedicated_recipient_{row_id:02d}", private_output=True,
                      sk=private / "recipients" / f"r{row_id:02d}.key", ct=output)
        expected = sum(sum(a * b for a, b in zip(x, rows[row_id], strict=True)) for x in plain_queue)
        assert answer["signed_score"] == expected
        assert answer["ciphertext_sha256"] == result["sha256"]
        exact_results.append({"after_admissions": admissions, "row_id": row_id, "exact_private_integer_match": True,
                              "state_queue_count": len(queue), "output_bytes": output.stat().st_size})

    infer(0)
    for index in range(33):
        x = [secrets.randbelow(255) - 127 for _ in range(577)]
        vector_path = private / f"input{index:02d}.json"
        write(vector_path, x, True)
        inputs.append(x)
        fresh = public / f"fresh{index:02d}.ct"
        call("issuer-encrypt", "private_issuer_public_key_only", pk=context, vector=vector_path, out=fresh)
        old = queue.pop(0) if len(queue) == 32 else None
        if old:
            plain_queue.pop(0)
        next_acc = public / f"acc{index + 1:02d}.ct"
        result = call("host-learn", "public_host", acc=accumulator, fresh=fresh, old=old, out=next_acc)
        assert result["object_type"] == "state" and result["bytes"] == 148147
        queue.append(fresh)
        plain_queue.append(x)
        accumulator = next_acc
        live_byte_counts.append((len(queue) + 1) * 148147)
        if index + 1 in READS:
            infer(index + 1)
        if (index + 1) % 8 == 0:
            print(canonical({"event": "normal_progress", "learn_completed": index + 1, "private_integer_matches": len(exact_results)}).decode(), flush=True)
    # Recompute the final normal Learn from the same immutable originals, compare exact public bytes.
    replay = public / "final.replayed.ct"
    call("host-learn", "public_exact_replay", acc=public / "acc32.ct", fresh=public / "fresh32.ct",
         old=public / "fresh00.ct", out=replay)
    assert replay.read_bytes() == accumulator.read_bytes()
    elapsed = time.perf_counter_ns() - start
    write(private / "reader_records.json", private_records, True)
    assert sorted(p.name for p in (private / "recipients").iterdir()) == [f"r{i:02d}.key" for i in range(16)]
    assert all((p.stat().st_mode & 0o777) == 0o600 and p.stat().st_size == 435 for p in (private / "recipients").iterdir())
    assert source_pins == {n: sha(source / n) for n in SOURCES}
    assert sha(native) == predeclared["native_library_sha256"]
    totals = {}
    for record in records:
        if record["private_output_and_timing_omitted"]:
            continue
        key = record["command"][1]
        aggregate = totals.setdefault(key, {"calls": 0, "elapsed_ns": 0, "counts": {}})
        aggregate["calls"] += 1
        aggregate["elapsed_ns"] += record["elapsed_ns"]
        for k, v in record["stdout"]["counts"].items():
            aggregate["counts"][k] = aggregate["counts"].get(k, 0) + v
    report = {"passed": True, "classification": "EXECUTED normal designated-recipient DDH positive suite",
              "predeclared_sha256": sha(reports / "predeclared.json"), "source_sha256": source_pins,
              "driver_sha256": sha(__file__), "context_sha256": expected_digest, "validation_source_pinned": True,
              "learn_count": 33, "infer_count": 4, "expiry_count": 1, "capacity": 32, "dimension": 577,
              "recipient_count": 16, "private_integer_matches": exact_results, "exact_original_expiry_replay_equal": True,
              "full_and_cached_query_bytes_equal": True, "state_bytes": 148147, "output_bytes": 691,
              "public_context_bytes": context.stat().st_size, "live_state_ciphertexts_final": 33,
              "live_state_ciphertext_bytes_final": live_byte_counts[-1], "private_recipient_key_bytes_each": 435,
              "total_run_ns": elapsed, "public_command_totals": totals,
              "private_recipient_commands": 4, "private_scores_vectors_keys_hashes_and_decode_timings_omitted": True,
              "master_serialized": False, "remaining_projection_delivery_files": 0, "physical_erasure_verified": False,
              "randomness": "secrets.randbelow / OS-backed SystemRandom; no seeds recorded",
              "constant_time_claim": False, "post_quantum_claim": False,
              "scope": "fresh synthetic private vectors; honest fixed-row arithmetic; no new utility accuracy or adversarial tests; same OS account",
              "python": sys.version, "platform": platform.platform(), "native_library": str(native),
              "native_library_sha256": sha(native), "commands_sha256": sha(reports / "commands.jsonl")}
    write(reports / "report.json", report)
    print(canonical({"passed": True, "learn_count": 33, "infer_count": 4, "expiry_count": 1,
                     "exact_private_integer_matches": 4, "total_run_ns": elapsed}).decode(), flush=True)


if __name__ == "__main__":
    main()
