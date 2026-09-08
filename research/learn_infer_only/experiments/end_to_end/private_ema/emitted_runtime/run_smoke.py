#!/usr/bin/env python3
"""Authorized positive two-step smoke, frozen files, public-first execution."""
from pathlib import Path
import datetime
import json
import os
import platform
import re
import signal
import subprocess
import time
from freeze import HERE, FORMAL, PRIOR, sha


def main():
    os.umask(0o077)
    freeze_path = HERE / "freeze.json"
    frozen = json.loads(freeze_path.read_text())
    freeze_digest = sha(freeze_path)
    report = HERE / "reports/smoke"
    runtime = HERE / "runs/smoke"
    report.mkdir(parents=True, exist_ok=False)
    runtime.mkdir(parents=True, exist_ok=False)
    public, private = runtime / "public", runtime / "private"
    public.mkdir(); private.mkdir(mode=0o700)
    binary = HERE / "target/release/resident-emitted-bool-runtime"
    reader = PRIOR / "target/release/reader"
    old_public = PRIOR / "runs/run_001/public"
    sk = old_public / "keys/server_key.bin"
    ck = PRIOR / "runs/run_001/private/reader/client_key.bin"
    result = {"schema": "emitted-bool-runtime-positive-smoke-v1", "claim": "EXECUTED",
              "freeze_sha256": freeze_digest, "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "operations": [], "replays": [], "public_hash_checks": [], "private_audits": [],
              "full_read_all_client_key_retained": True, "roles_share_os_account": True,
              "private_key_read_or_hashed_by_host_or_coordinator": False,
              "host_concurrency": 1, "rayon_num_threads": "1", "contention": frozen["contention"],
              "universal_rust_tfhe_semantics_or_replay_theorem": False, "success": False, "error": None}

    def save():
        (report / "results.json").write_text(json.dumps(result, indent=2) + "\n")

    def check_frozen(stage):
        if sha(freeze_path) != freeze_digest:
            raise RuntimeError("freeze manifest changed")
        for entry in frozen["files"]:
            path = Path(entry["path"])
            if path.stat().st_size != entry["bytes"] or sha(path) != entry["sha256"]:
                raise RuntimeError(f"frozen public file changed: {path}")
        result["public_hash_checks"].append({"stage": stage, "files_matched": len(frozen["files"]),
                                             "checked_utc": datetime.datetime.now(datetime.timezone.utc).isoformat()})
        save()

    def execute(name, argv):
        resource = report / f"{name}.time.txt"
        prefix = ["/usr/bin/time", "-l" if platform.system() == "Darwin" else "-v", "-o", str(resource)]
        env = os.environ.copy(); env["RAYON_NUM_THREADS"] = "1"
        started = time.perf_counter_ns()
        process = subprocess.Popen(prefix + [str(x) for x in argv], cwd=HERE, env=env,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
        timed_out = False
        try:
            stdout, stderr = process.communicate(timeout=600)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(process.pid, signal.SIGKILL)
            stdout, stderr = process.communicate()
        elapsed = time.perf_counter_ns() - started
        (report / f"{name}.stdout.json").write_bytes(stdout)
        (report / f"{name}.stderr.txt").write_bytes(stderr)
        record = {"name": name, "argv": [str(x) for x in argv], "measurement_argv_prefix": prefix,
                  "wrapper_pid": process.pid, "wall_ns": elapsed, "returncode": process.returncode,
                  "timed_out": timed_out}
        if resource.exists():
            pattern = r"(\d+)\s+maximum resident set size" if platform.system() == "Darwin" else r"Maximum resident set size \(kbytes\):\s*(\d+)"
            match = re.search(pattern, resource.read_text())
            if match:
                record["peak_rss_bytes"] = int(match[1]) * (1 if platform.system() == "Darwin" else 1024)
        if process.returncode == 0:
            record["reported"] = json.loads(stdout)
        result["operations"].append(record); save()
        print(json.dumps({"completed": name, "returncode": process.returncode, "wall_seconds": elapsed / 1e9}), flush=True)
        if process.returncode or timed_out:
            raise RuntimeError(f"{name} failed; preserved logs")
        return record

    def pair(op, tag, parent, input_path, output):
        check_frozen(f"before_{op}_{tag}")
        schedule = FORMAL / f"artifacts/{op}.json"
        replay = public / f"{op}_{tag}_replay.ct"
        read_inputs = [schedule, sk, parent, input_path]
        input_hashes = {str(p): sha(p) for p in read_inputs}
        first = execute(f"{op}_{tag}", [binary, "host", schedule, sk, parent, input_path, output])
        second = execute(f"{op}_{tag}_replay", [binary, "host", schedule, sk, parent, input_path, replay])
        equal = output.read_bytes() == replay.read_bytes()
        inputs_unchanged = input_hashes == {str(p): sha(p) for p in read_inputs}
        record = {"operation": op, "step": tag, "complete_serialized_bytes_equal": equal,
                  "same_serialized_read_arguments": first["argv"][1:-1] == second["argv"][1:-1],
                  "input_hashes": input_hashes, "input_hashes_unchanged_after_pair": inputs_unchanged,
                  "separate_wrapper_pids": [first["wrapper_pid"], second["wrapper_pid"]],
                  "first_path": str(output), "replay_path": str(replay),
                  "first_sha256": sha(output), "replay_sha256": sha(replay), "bytes": output.stat().st_size}
        result["replays"].append(record); save()
        if not equal or not inputs_unchanged:
            raise RuntimeError(f"{op}_{tag} replay or public input hash mismatch; no further Learn")

    save()
    try:
        check_frozen("before_public_evaluations")
        parent = old_public / "state_000.ct"
        states, outputs = [], []
        for step in [1, 2]:
            tag = f"{step:03d}"
            state = public / f"state_{tag}.ct"
            output = public / f"output_{tag}.ct"
            pair("learn", tag, parent, old_public / f"input_{tag}.ct", state)
            pair("infer", tag, state, old_public / "query_001.ct", output)
            states.append(state); outputs.append(output); parent = state
        check_frozen("after_all_public_evaluations_before_private_audit")
        for replay in result["replays"]:
            for prefix in ["first", "replay"]:
                if sha(Path(replay[f"{prefix}_path"])) != replay[f"{prefix}_sha256"]:
                    raise RuntimeError("public result hash changed before private audit")
        result["all_public_result_hashes_rechecked_before_private_audit"] = True
        result["public_execution_complete_before_private_audit"] = True
        result["public_execution_complete_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        save()
        # Only now does a reader process access the retained client key.
        oracle = [0, 0, 0, 0]
        for step, label in enumerate([120, -120], 1):
            tag = f"{step:03d}"
            previous = oracle.copy(); oracle[2] = (7 * oracle[2] + label) // 8
            state_audit = private / f"state_{tag}.json"
            output_audit = private / f"output_{tag}.json"
            execute(f"reader_state_{tag}", [reader, "state", ck, states[step-1], state_audit])
            execute(f"reader_output_{tag}", [reader, "output", ck, outputs[step-1], output_audit])
            state = json.loads(state_audit.read_text())["state"]
            answer = json.loads(output_audit.read_text())["negative"]
            audit = {"step": step, "all_registers_match_integer_oracle": state == oracle,
                     "unselected_registers_unchanged": all(state[j] == previous[j] for j in [0, 1, 3]),
                     "private_sign_matches": answer == (oracle[2] < 0)}
            result["private_audits"].append(audit); save()
        check_frozen("after_private_audit")
        result["success"] = all(a[k] for a in result["private_audits"] for k in
                                ["all_registers_match_integer_oracle", "unselected_registers_unchanged", "private_sign_matches"])
        if not result["success"]:
            raise RuntimeError("private oracle comparison mismatch; no retry")
    except Exception as exc:
        result["error"] = str(exc)
        raise
    finally:
        result["ended_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        save()


if __name__ == "__main__":
    main()
