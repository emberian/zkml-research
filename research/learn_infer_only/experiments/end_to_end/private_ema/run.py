#!/usr/bin/env python3
"""One bounded honest fixture; subprocess roles and independent integer oracle.

No TFHE imports here. This driver is a private fixture coordinator, not the host.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import platform
import re
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parent
RUN = ROOT / "runs" / "run_001"
BINS = ROOT / "target" / "release"


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def dump(path: Path, obj) -> None:
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n")


def metadata(path: Path) -> dict:
    return {"path": str(path.relative_to(ROOT)), "bytes": path.stat().st_size,
            "sha256": digest(path)}


def main() -> None:
    os.umask(0o077)
    RUN.mkdir(parents=True, exist_ok=False)
    public = RUN / "public"
    private = RUN / "private"
    logs = RUN / "logs"
    for directory in (public, private, logs):
        directory.mkdir()
    result = {
        "schema": "resident-private-address-ema-feasibility-v1",
        "fixture": "two preregistered synthetic updates; not an unknown-input privacy experiment",
        "full_read_all_client_key_retained": True,
        "roles_share_os_account": True,
        "platform": {"system": platform.system(), "machine": platform.machine(),
                     "python": platform.python_version()},
        "operations": [], "logical_steps": [], "replay_pairs": [],
        "public_artifacts": [], "errors": [],
    }
    baseline_sources = {}
    for path in [ROOT / "CONTRACT.md", ROOT / "Cargo.toml", ROOT / "Cargo.lock",
                 ROOT / "run.py", *sorted((ROOT / "src").rglob("*.rs"))]:
        baseline_sources[str(path.relative_to(ROOT))] = digest(path)
    result["source_hashes_before"] = baseline_sources
    result["binary_hashes"] = {name: digest(BINS / name) for name in ("setup", "issuer", "host", "reader")}

    def save():
        dump(RUN / "results.json", result)

    def execute(name: str, binary: str, *args: Path | str, timeout: int = 240) -> dict:
        command = [str(BINS / binary), *map(str, args)]
        time_path = logs / f"{name}.time.txt"
        # Preserve per-process resource evidence using the platform's time utility.
        prefix = ["/usr/bin/time", "-l" if platform.system() == "Darwin" else "-v", "-o", str(time_path)]
        started = time.perf_counter_ns()
        process = subprocess.Popen(prefix + command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   start_new_session=True)
        try:
            stdout, stderr = process.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            stdout, stderr = process.communicate()
            (logs / f"{name}.stdout").write_bytes(stdout)
            (logs / f"{name}.stderr").write_bytes(stderr)
            raise RuntimeError(f"bounded operation {name} exceeded {timeout} seconds")
        elapsed = time.perf_counter_ns() - started
        (logs / f"{name}.stdout").write_bytes(stdout)
        (logs / f"{name}.stderr").write_bytes(stderr)
        record = {"name": name, "command": command, "measurement_command": prefix,
                  "wrapper_pid": process.pid, "subprocess_wall_ns": elapsed,
                  "exit_code": process.returncode,
                  "stdout_path": str((logs / f"{name}.stdout").relative_to(ROOT)),
                  "stderr_path": str((logs / f"{name}.stderr").relative_to(ROOT)),
                  "resource_log": str(time_path.relative_to(ROOT))}
        if time_path.exists():
            text = time_path.read_text()
            if platform.system() == "Darwin":
                match = re.search(r"(\d+)\s+maximum resident set size", text)
                if match:
                    record["peak_rss_bytes"] = int(match.group(1))
            else:
                match = re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", text)
                if match:
                    record["peak_rss_bytes"] = int(match.group(1)) * 1024
        if process.returncode == 0:
            record["reported"] = json.loads(stdout)
        result["operations"].append(record)
        save()
        print(json.dumps({"completed": name, "exit_code": process.returncode,
                          "wall_seconds": elapsed / 1e9}), flush=True)
        if process.returncode:
            raise RuntimeError(f"{name} exited with code {process.returncode}; see retained logs")
        return record

    def compare_replay(name: str, first: Path, second: Path,
                       first_record: dict, second_record: dict) -> bool:
        left, right = first.read_bytes(), second.read_bytes()
        equal = left == right
        record = {"name": name, "equal_complete_serialized_bytes": equal,
                  "first": metadata(first), "replay": metadata(second),
                  "separate_wrapper_pids": [first_record["wrapper_pid"], second_record["wrapper_pid"]],
                  "same_serialized_read_inputs": first_record["command"][2:-1] == second_record["command"][2:-1]}
        if not equal:
            record["first_difference_byte"] = next((i for i, (a, b) in enumerate(zip(left, right)) if a != b), min(len(left), len(right)))
        result["replay_pairs"].append(record)
        save()
        return equal

    try:
        keys = public / "keys"
        reader_dir = private / "reader"
        execute("setup", "setup", keys, reader_dir)
        pk, sk = keys / "public_key.bin", keys / "server_key.bin"
        ck = reader_dir / "client_key.bin"
        result["public_key_artifacts"] = [metadata(pk), metadata(sk)]
        # No secret-key value or hash enters this public report.
        result["private_client_key_bytes"] = ck.stat().st_size
        init_request = private / "request_init.txt"
        init_request.write_text("")
        initial = public / "state_000.ct"
        execute("issuer_init", "issuer", "init", pk, init_request, initial)
        initial_audit = private / "audit_state_000.json"
        execute("reader_state_000", "reader", "state", ck, initial, initial_audit)
        oracle = [0, 0, 0, 0]
        result["initial_state_matches"] = json.loads(initial_audit.read_text())["state"] == oracle
        assert result["initial_state_matches"]
        query_request = private / "request_query.txt"
        query_request.write_text("2\n")
        query = public / "query_001.ct"
        execute("issuer_query", "issuer", "query", pk, query_request, query)
        parent = initial
        for step, (address, label) in enumerate(((2, 120), (2, -120)), 1):
            tag = f"{step:03d}"
            request = private / f"request_learn_{tag}.txt"
            request.write_text(f"{address} {label}\n")
            input_ct = public / f"input_{tag}.ct"
            execute(f"issuer_learn_{tag}", "issuer", "learn", pk, request, input_ct)
            state = public / f"state_{tag}.ct"
            replay_state = public / f"state_{tag}_replay.ct"
            first = execute(f"host_learn_{tag}", "host", "learn", sk, parent, input_ct, state)
            second = execute(f"replay_learn_{tag}", "host", "learn", sk, parent, input_ct, replay_state)
            learn_replay = compare_replay(f"learn_{tag}", state, replay_state, first, second)
            # Independent ordinary-integer oracle, separate from the Boolean implementation.
            previous = list(oracle)
            oracle[address] = (7 * oracle[address] + label) // 8
            audit_state = private / f"audit_state_{tag}.json"
            execute(f"reader_state_{tag}", "reader", "state", ck, state, audit_state)
            got_state = json.loads(audit_state.read_text())["state"]
            state_matches = got_state == oracle
            unselected_unchanged = all(got_state[j] == previous[j] for j in range(4) if j != address)
            output, replay_output = public / f"output_{tag}.ct", public / f"output_{tag}_replay.ct"
            first = execute(f"host_infer_{tag}", "host", "infer", sk, state, query, output)
            second = execute(f"replay_infer_{tag}", "host", "infer", sk, state, query, replay_output)
            infer_replay = compare_replay(f"infer_{tag}", output, replay_output, first, second)
            audit_output = private / f"audit_output_{tag}.json"
            execute(f"reader_output_{tag}", "reader", "output", ck, output, audit_output)
            output_matches = json.loads(audit_output.read_text())["negative"] == (oracle[2] < 0)
            result["logical_steps"].append({"step": step, "all_four_registers_match": state_matches,
                "unselected_registers_unchanged": unselected_unchanged, "private_sign_matches": output_matches,
                "learn_exact_replay": learn_replay, "infer_exact_replay": infer_replay})
            dump(private / f"oracle_{tag}.json", {"state": oracle, "negative": oracle[2] < 0})
            save()
            assert state_matches and unselected_unchanged and output_matches
            parent = state
            if not (learn_replay and infer_replay):
                result["stopped_after_replay_mismatch"] = True
                break
        result["logical_learn_count"] = len(result["logical_steps"])
        result["all_correctness_checks_passed"] = all(s["all_four_registers_match"] and s["private_sign_matches"] and s["unselected_registers_unchanged"] for s in result["logical_steps"])
        result["all_tested_byte_replays_match"] = all(p["equal_complete_serialized_bytes"] for p in result["replay_pairs"])
        result["completed_prespecified_two_step_run"] = len(result["logical_steps"]) == 2
    except Exception as error:
        result["errors"].append(f"{type(error).__name__}: {error}")
        raise
    finally:
        result["public_artifacts"] = [metadata(path) for path in sorted(public.glob("*.ct"))]
        result["source_hashes_after"] = {name: digest(ROOT / name) for name in baseline_sources}
        result["source_hashes_unchanged"] = result["source_hashes_after"] == baseline_sources
        save()
    print(json.dumps({"finished": True, "logical_learns": result["logical_learn_count"],
                      "correctness": result["all_correctness_checks_passed"],
                      "byte_replay": result["all_tested_byte_replays_match"]}), flush=True)


if __name__ == "__main__":
    main()
