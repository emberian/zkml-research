#!/usr/bin/env python3
"""One reviewed normal seed setup and 33/4/1 workload; no retry; drain last."""
from pathlib import Path
import argparse
import collections
import hashlib
import json
import os
import platform
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
CORE = HERE / "source/public_setup/source/crypto"
sys.path.insert(0, str(CORE))
import crypto as c
from native_pow import LIBRARY


def save(path, obj, private=False):
    c.save(path, c.canonical(obj), private)


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument("--root", required=True)
    args = parser.parse_args()
    run = Path(args.root).resolve()
    c.require(sys.flags.optimize == 0, "normal interpreter with assertions enabled")
    c.require(run == HERE / "reports/normal_001", "one named normal run only")
    c.require(not run.exists(), "no retry or existing runtime")
    pins_raw = (HERE / "SOURCE_PINS.json").read_bytes()
    pins = json.loads(pins_raw)
    gate = json.loads((HERE / "PRELAUNCH_REVIEW.json").read_text())
    c.require(gate["disposition"] == "accepted" and gate["source_pins_sha256"] == c.sha(pins_raw), "prelaunch review of exact sources")
    review = Path(gate["review_report_path"])
    c.require(c.sha(review.read_bytes()) == gate["review_report_sha256"], "pinned independent source review")
    c.require(gate["root_notified"] is True, "root notified after source review")

    def check_pins():
        c.require(all(c.sha((HERE / name).read_bytes()) == digest for name, digest in pins["source_sha256"].items()), "frozen source/contract bytes")
        c.require(c.sha(LIBRARY.read_bytes()) == pins["native_dependency"]["sha256"], "frozen native bytes")

    check_pins()
    run.mkdir(parents=True)
    public, private = run / "public", run / ".private"
    public.mkdir()
    private.mkdir(mode=0o700)
    for name in ("pending", "recipients"):
        (private / name).mkdir(mode=0o700)
    for name in ("announcements", "inputs", "ciphertexts", "states", "queries", "outputs"):
        (public / name).mkdir()
    started = time.perf_counter_ns()
    deadline = time.monotonic()+1200
    calls = []
    private_calls = []
    public_closed = False
    context_id = None
    save(public / "execution_pins.json", {"source_manifest": pins, "source_manifest_sha256": c.sha(pins_raw),
         "prelaunch_review": gate, "python": sys.version, "platform": platform.platform()})

    def call(program, command=None, is_private=False, **kwargs):
        nonlocal context_id
        c.require(is_private or not public_closed, "public phase permanently closed")
        c.require(not is_private or public_closed, "private drain only after public closure")
        remaining = deadline-time.monotonic()
        c.require(remaining > 0, "20 minute normal cap")
        check_pins()
        argv = [sys.executable, "-B", str(program)]
        if command:
            argv.append(command)
        if program == CORE / "crypto.py":
            c.require(command in {"validate-context", "recipient-finalize", "issuer-encrypt", "host-learn", "encode-query", "host-infer", "reader-decrypt"}, "only reviewed normal backend commands")
            argv += ["--context", str(public / "context.json")]
            if command != "validate-context":
                argv += ["--validated-context-sha256", context_id]
        for key, value in kwargs.items():
            if value is not None:
                argv += ["--"+key.replace("_", "-"), str(value)]
        begin = time.perf_counter_ns()
        try:
            out = subprocess.run(argv, capture_output=True, timeout=min(remaining, 300))
        except subprocess.TimeoutExpired:
            failure = {"program": str(program.relative_to(HERE)), "command": command,
                       "reason": "normal child/overall timeout; no retry", "private_operation": is_private}
            save(private / "STOPPED.json" if is_private else run / "STOPPED.json", failure, is_private)
            raise RuntimeError("normal timeout; no retry") from None
        record = {"ordinal": len(calls)+len(private_calls), "program": str(program.relative_to(HERE)),
                  "command": command, "argv": argv, "elapsed_ns": time.perf_counter_ns()-begin,
                  "exit_code": out.returncode}
        if out.returncode:
            if not is_private:
                record.update(stdout=out.stdout.decode(), stderr=out.stderr.decode())
            save(private / "STOPPED.json" if is_private else run / "STOPPED.json", record, is_private)
            raise RuntimeError("normal operation failed; no retry")
        result = json.loads(out.stdout)
        record["result"] = result
        if is_private:
            private_calls.append(record)
            log = private / "commands.jsonl"
        else:
            c.require("signed_score" not in result and command != "reader-decrypt", "no private decode in public log")
            calls.append(record)
            log = public / "commands.jsonl"
        with log.open("ab") as sink:
            sink.write(c.canonical(record)+b"\n")
            sink.flush()
            os.fsync(sink.fileno())
        os.chmod(log, 0o600 if is_private else 0o644)
        return result

    def progress(stage, **extra):
        print(json.dumps({"stage": stage, "elapsed_ns": time.perf_counter_ns()-started, **extra}), flush=True)

    setup, backend = HERE / "seed_setup.py", CORE / "crypto.py"
    registry = public / "registry.json"
    reg = call(setup, "auth-init", private=private / "auth", out=registry)
    reg_sha = reg["registry_sha256"]
    for i in range(c.K):
        call(setup, "recipient-init", registry=registry, registry_sha256=reg_sha, row=i,
             auth_key=private / "auth" / f"r{i:02d}.sigkey", pending=private / "pending" / f"r{i:02d}.scalar",
             out=public / "announcements" / f"r{i:02d}.json")
    progress("fresh_complete_registry_fixed", recipients=c.K)
    build = call(setup, "public-build", registry=registry, registry_sha256=reg_sha,
                 announcements=public / "announcements", context=public / "context.json",
                 transcript=public / "transcript.json", zero=public / "zero.ct")
    context_id = build["context_id"]
    call(setup, "verify-public", registry=registry, registry_sha256=reg_sha,
         context=public / "context.json", transcript=public / "transcript.json")
    validation = call(backend, "validate-context")
    c.require(validation["validated"] and validation["source_sha256"] == pins["frozen_crypto"], "uncached full frozen context validation")
    save(public / "context_validation.json", validation)
    for i in range(c.K):
        pending = private / "pending" / f"r{i:02d}.scalar"
        call(backend, "recipient-finalize", row=i, secret=pending, out=private / "recipients" / f"r{i:02d}.key")
        pending.unlink()
    setup_ns = time.perf_counter_ns()-started
    c.require(not list((private / "pending").iterdir()), "no redundant pending files")
    c.require(len(list((private / "recipients").glob("*.key"))) == c.K, "all recipient scalar envelopes")
    progress("setup_verified", setup_ns=setup_ns, context_id=context_id)

    queue = []
    acc = public / "zero.ct"
    selected = {1: 0, 16: 1, 32: 2, 33: 3}
    tickets = []
    for t in range(1, 34):
        vector = [((t+3)*(j+5) % 17)-8 for j in range(c.D)]
        path = public / "inputs" / f"x{t:02d}.json"
        save(path, vector)
        fresh = public / "ciphertexts" / f"c{t:02d}.ct"
        call(backend, "issuer-encrypt", pk=public / "context.json", vector=path, out=fresh)
        old = queue.pop(0) if len(queue) == c.W else None
        output = public / "states" / f"a{t:02d}.ct"
        call(backend, "host-learn", acc=acc, fresh=fresh, old=old, out=output)
        queue.append(fresh)
        acc = output
        if t in selected:
            row = selected[t]
            qvector = public / "queries" / f"y{row:02d}.json"
            query = public / "queries" / f"q{row:02d}.json"
            save(qvector, c.ROWS[row])
            call(backend, "encode-query", vector=qvector, out=query)
            transformed = public / "outputs" / f"o{row:02d}.ct"
            call(backend, "host-infer", acc=acc, query=query, out=transformed)
            tickets.append({"learns": t, "row": row, "output": str(transformed.relative_to(public))})
        if t % 8 == 0 or t == 33:
            progress("normal_public_workload", learns=t, infers=len(tickets))

    replay = call(HERE / "public_reference.py", root=public)
    save(public / "public_replay.json", replay)
    final_setup = call(setup, "verify-public", registry=registry, registry_sha256=reg_sha,
                       context=public / "context.json", transcript=public / "transcript.json")
    save(public / "final_setup_replay.json", final_setup)
    save(public / "drain_tickets.json", tickets)
    public_ns = time.perf_counter_ns()-started
    save(public / "public_report.json", {
        "ok": True, "context_id": context_id, "learns": 33, "infers": 4, "exact_expiries": 1,
        "fresh_recipients": c.K, "public_seed_candidates": 1, "setup_ns": setup_ns,
        "public_phase_ns": public_ns, "public_process_calls": len(calls),
        "private_decode_calls_so_far": 0, "all_public_processes_exited": True,
        "setup_hash_and_context_replays": 2, "complete_state_byte_replays": 33,
        "complete_output_byte_replays": 4, "scalar_master_computed_in_setup_path": False,
        "scalar_projection_delivery_computed_in_setup_path": False,
        "scope": "normal known public integer fixture; classical conditional ROM/DDH only; no timing/privacy or selected-span restriction claim"})
    check_pins()
    inventory = {str(p.relative_to(public)): {"bytes": p.stat().st_size, "sha256": c.sha(p.read_bytes())}
                 for p in sorted(public.rglob("*")) if p.is_file()}
    save(public / "PUBLIC_COMPLETE.json", {"schema": "public-seed-positive-evidence-closure-v1",
         "context_id": context_id, "files": inventory, "all_public_children_exited": True,
         "private_decryptions_so_far": 0, "source_manifest_sha256": c.sha(pins_raw)})
    public_closed = True
    progress("public_evidence_closed_before_private_drain", public_phase_ns=public_ns)

    comparisons = []
    for ticket in tickets:
        row, t = ticket["row"], ticket["learns"]
        answer = call(backend, "reader-decrypt", is_private=True,
                      sk=private / "recipients" / f"r{row:02d}.key", ct=public / ticket["output"])
        expected = sum((((step+3)*(j+5) % 17)-8)*c.ROWS[row][j]
                       for step in range(max(1, t-c.W+1), t+1) for j in range(c.D))
        c.require(answer["signed_score"] == expected and answer["row_id"] == row and answer["key_id"] == context_id,
                  "independent normal integer comparison")
        comparisons.append({"learns": t, "row": row, "expected": expected,
                            "actual": answer["signed_score"], "matches": True})
    save(private / "integer_comparisons.json", comparisons, True)
    total_ns = time.perf_counter_ns()-started
    save(run / "RESEARCH_RESULT.json", {"ok": True, "all_four_integer_comparisons_match": True,
         "learns": 33, "infers": 4, "exact_expiries": 1, "context_id": context_id,
         "setup_ns": setup_ns, "public_phase_ns": public_ns, "total_ns": total_ns,
         "public_evidence_closed_before_first_private_decode": True,
         "private_decode_processes": len(private_calls),
         "scope": "aggregate research result outside closed public/ security transcript; known public fixture, no timing/privacy claim"})
    print(json.dumps({"ok": True, "all_match": True, "public_phase_seconds": public_ns/1e9,
                      "total_seconds": total_ns/1e9}), flush=True)


if __name__ == "__main__":
    main()
