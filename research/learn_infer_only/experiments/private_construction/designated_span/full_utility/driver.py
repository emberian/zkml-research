#!/usr/bin/env python3
"""Prepare/run the complete existing utility fixture through designated DDH.

Preparation executes no crypto or services. Launch requires a matching successful
small integration report and separate root authorization. All public work ends
before recipient-private drains; no adversarial/control code is imported.
"""
from pathlib import Path
import argparse
import collections
import gzip
import hashlib
import importlib.metadata
import importlib.util
import json
import os
import platform
import select
import shutil
import sqlite3
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
CRYPTO_FILES = ["crypto.py", "group.py", "native_pow.py", "rows.json"]
ACCEPTED_SMALL_REPORT_SHA256 = "dbc7b6b41ff27a380755c210d9a1c190b3792fb1922f0a492add065312113ece"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load(path):
    return json.loads(Path(path).read_bytes())


def dump(path, obj, private=False):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True, mode=0o700 if private else 0o755)
    raw = json.dumps(obj, sort_keys=True, separators=(",", ":"), allow_nan=False).encode() + b"\n"
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600 if private else 0o644)
    with os.fdopen(fd, "wb") as out:
        out.write(raw)
        out.flush()
        os.fsync(out.fileno())


def prepare(args):
    runtime, reports = args.runtime.resolve(), args.reports.resolve()
    runtime.mkdir(parents=True, exist_ok=False, mode=0o700)
    reports.mkdir(parents=True, exist_ok=False)
    source = runtime / "source"
    source.mkdir()
    designated = HERE.parent
    worker = designated / "host_runtime"
    worker_manifest = load(worker / "artifact_manifest.json")
    for name, entry in worker_manifest["files"].items():
        assert sha(worker / name) == entry["sha256"]
    host_pins = load(worker / "source_pins.json")
    for name, entry in host_pins["core"].items():
        origin = designated / "integration/source" / name
        assert sha(origin) == entry["sha256"]
        target = source / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(origin, target)
    for name in CRYPTO_FILES:
        target = source / "crypto" / name
        target.parent.mkdir(exist_ok=True)
        shutil.copy2(designated / "crypto" / name, target)
        assert sha(target) == host_pins["crypto_runtime"][name]
    for name in ["host.py", "source_pins.json", *["frozen_source/" + k for k in host_pins["core"]]]:
        target = source / "host_runtime" / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(worker / name, target)
    for name in ("driver.py", "private_oracle.py"):
        shutil.copy2(HERE / name, source / name)
    # Existing public utility fixture; no model execution, new selection or encoder.
    utility = designated.parents[1] / "end_to_end/utility"
    materialized = load(utility / "materialized_inputs_manifest.json")
    assert materialized["passed"] and materialized["issuer_vector_count"] == 384
    index_path = utility / "issuer_oracle/input_index.json"
    oracle_path = utility / "issuer_oracle/expected_scalars.json"
    assert sha(index_path) == materialized["private_index_sha256"]
    assert sha(oracle_path) == materialized["oracle_sha256"]
    events = load(index_path)
    assert len(events["events"]) == 480
    private = runtime / ".private_fixture"
    private.mkdir(mode=0o700)
    queries = runtime / "public_queries"
    queries.mkdir()
    fixture_files = {}
    for event in events["events"]:
        field = "issuer_vector_path" if event["kind"] == "Learn" else "public_query_vector_path"
        original = Path(event[field])
        assert sha(original) == materialized["files_sha256"][str(original)]
        target = (private if event["kind"] == "Learn" else queries) / original.name
        shutil.copyfile(original, target)
        os.chmod(target, 0o600 if event["kind"] == "Learn" else 0o644)
        event[field] = str(target)
        fixture_files[str(target.relative_to(runtime))] = sha(target)
    dump(private / "input_index.json", events, True)
    shutil.copyfile(oracle_path, private / "expected_scalars.json")
    os.chmod(private / "expected_scalars.json", 0o600)
    source_files = {str(p.relative_to(source)): sha(p) for p in sorted(source.rglob("*")) if p.is_file()}
    native = Path("/opt/homebrew/opt/openssl@3/lib/libcrypto.3.dylib").resolve()
    interpreter = Path(sys.executable).resolve()
    distribution = importlib.metadata.distribution("cryptography")
    signature_dependencies = {}
    for entry in distribution.files or []:
        candidate = Path(distribution.locate_file(entry)).resolve()
        if candidate.is_file() and (candidate.suffix in [".py", ".so", ".dylib"] or candidate.name in ["METADATA", "RECORD"]):
            signature_dependencies[str(candidate)] = sha(candidate)
    # This installed distribution has no RECORD inventory. Pin the actual
    # import package and native extension instead of accepting an empty set.
    specification = importlib.util.find_spec("cryptography")
    for directory in specification.submodule_search_locations or []:
        for candidate in Path(directory).rglob("*"):
            if candidate.is_file() and candidate.suffix in [".py", ".so", ".dylib"]:
                signature_dependencies[str(candidate.resolve())] = sha(candidate)
    assert signature_dependencies and any(Path(p).suffix == ".so" for p in signature_dependencies), "nonempty signature implementation pins"
    prep = {"schema": "designated-complete-utility-preparation-v1", "prepared_only": True,
            "source_files_sha256": source_files, "native_dependency": {"path": str(native), "sha256": sha(native)},
            "interpreter": {"path": str(interpreter), "sha256": sha(interpreter), "version": sys.version},
            "signature_dependency": {"package": "cryptography", "version": distribution.version,
                                     "files_sha256": signature_dependencies},
            "platform": platform.platform(), "host_artifact_manifest_sha256": sha(worker / "artifact_manifest.json"),
            "original_materialized_manifest_sha256": sha(utility / "materialized_inputs_manifest.json"),
            "original_index_sha256": materialized["private_index_sha256"], "original_oracle_sha256": materialized["oracle_sha256"],
            "mapping_sha256": materialized["mapping_sha256"], "copied_index_sha256": sha(private / "input_index.json"),
            "fixture_files_sha256": fixture_files, "public_fixture_provenance_only": True,
            "events": 480, "histories": 2, "learns": 384, "infers": 96, "expiries": 256,
            "public_query_rows": 16, "dimension": 577, "capacity_per_route": 32,
            "fresh_setup_per_history": True, "fresh_OS_random_issuance": True,
            "all_public_checks_before_any_private_drain": True, "new_model_runs": 0,
            "launch_requires_matching_small40_4_8_pass_and_root_signal": True}
    dump(reports / "preparation.json", prep)
    dump(reports / "launch_command.json", {"argv_template": [str(interpreter), str(source / "driver.py"), "run", "--runtime", str(runtime),
         "--reports", str(reports), "--small-pass", "ABSOLUTE_PATH_TO_MATCHING_NORMAL_REPORT.json"], "not_executed": True})
    print(json.dumps({"prepared": True, "crypto_commands_executed": 0, "services_launched": 0,
                      "source_files": len(source_files), "preparation_sha256": sha(reports / "preparation.json")}))


def check_preparation(runtime, reports):
    prep = load(reports / "preparation.json")
    source = runtime / "source"
    for name, expected in prep["source_files_sha256"].items():
        assert sha(source / name) == expected, "prepared source changed: " + name
    assert sha(prep["native_dependency"]["path"]) == prep["native_dependency"]["sha256"]
    assert str(Path(sys.executable).resolve()) == prep["interpreter"]["path"]
    assert sha(sys.executable) == prep["interpreter"]["sha256"]
    for path, expected in prep["signature_dependency"]["files_sha256"].items():
        assert sha(path) == expected, "signature dependency changed"
    for name, expected in prep["fixture_files_sha256"].items():
        assert sha(runtime / name) == expected, "prepared fixture changed"
    assert sha(runtime / ".private_fixture/input_index.json") == prep["copied_index_sha256"]
    assert sha(runtime / ".private_fixture/expected_scalars.json") == prep["original_oracle_sha256"]
    return prep


def run(args):
    runtime, reports = args.runtime.resolve(), args.reports.resolve()
    prep = check_preparation(runtime, reports)
    source = runtime / "source"
    assert HERE == source, "launch the staged immutable driver"
    sys.path.insert(0, str(source / "journal"))
    from run import Run
    from common import canonical, digest, read_json, require, rpc, write_json
    # No cryptographic setup or process starts before this gate succeeds.
    small_path = args.small_pass.resolve()
    require(sha(small_path) == ACCEPTED_SMALL_REPORT_SHA256, "rootAcceptedSmallReportBytes")
    small = read_json(small_path)
    require(small["ok"] and small["learns"] == 40 and small["infers"] == 4 and small["exact_original_expiries"] == 8,
            "smallNormalIntegrationMustPass")
    require(small["all_private_integer_comparisons_match"] and small["public_acceptance_precedes_any_scalar_decode"], "smallPrivateComparisonAndPublicPhasePass")
    small_genesis = read_json(small_path.parent / "genesis.json")
    require(digest(small_genesis) == small["genesis"], "smallReportGenesis")
    for name, expected in small_genesis["journal_sources"].items():
        require(sha(source / "journal" / name) == expected, "sameSmallJournalSource")
    for name, expected in small_genesis["crypto_sources"].items():
        require(sha(source / "crypto" / name) == expected, "sameSmallCryptoSource")
    require(not (reports / "launched.json").exists(), "freshLaunchOnly")
    dump(reports / "launched.json", {"small_report_sha256": sha(small_path), "small_genesis_sha256": digest(small_genesis),
                                   "preparation_sha256": sha(reports / "preparation.json"), "all_source_checks_passed": True,
                                   "small_harness_guard_qualification": small.get("harness_guard_correction")})
    events = read_json(runtime / ".private_fixture/input_index.json")["events"]
    policy = runtime / "query_policy.json"
    write_json(policy, [{"route": 0 if i < 8 else 1, "path": str(runtime / "public_queries" / f"q{i:02d}.json")} for i in range(16)])

    class PersistentRun(Run):
        def __init__(self, root):
            self.host_worker = None
            self.worker_events = []
            self.worker_report = None
            try:
                super().__init__(root, policy, source / "crypto/crypto.py")
            except Exception:
                for process in getattr(self, "processes", []):
                    self.stop(process)
                raise
            try:
                self.worker_argv = [sys.executable, str(source / "host_runtime/host.py"), "serve", "--config",
                                    str(self.root / "host_config.json"), "--cas", str(self.host_cas.root)]
                self.worker_log = (self.root / "host_worker.stderr").open("wb")
                self.worker_started = time.perf_counter_ns()
                self.host_worker = subprocess.Popen(self.worker_argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=self.worker_log)
                require(select.select([self.host_worker.stdout], [], [], 300)[0], "hostStartupTimeout")
                ready = read_line(self.host_worker)
                require(ready.get("ok") and ready.get("ready") and ready["context_id"] == self.g["context_id"], "hostReadyContext")
                self.worker_startup_ns = time.perf_counter_ns() - self.worker_started
                self.worker_pid = self.host_worker.pid
            except Exception:
                if self.host_worker is not None:
                    self.stop(self.host_worker)
                if hasattr(self, "worker_log"):
                    self.worker_log.close()
                for process in self.processes:
                    self.stop(process)
                raise

        def role(self, command, **kwargs):
            if command != "propose":
                return super().role(command, **kwargs)
            require(set(kwargs) == {"config", "head", "authorization", "cas", "out"}, "normalHostArguments")
            require(Path(kwargs["config"]).resolve() == self.root / "host_config.json" and
                    Path(kwargs["cas"]).resolve() == self.host_cas.root.resolve(), "fixedHostPaths")
            message = {k: str(kwargs[k]) for k in ("head", "authorization", "out")}
            raw = canonical(message) + b"\n"
            started = time.perf_counter_ns()
            self.host_worker.stdin.write(raw)
            self.host_worker.stdin.flush()
            require(select.select([self.host_worker.stdout], [], [], 300)[0], "hostProposalTimeout")
            line = self.host_worker.stdout.readline()
            reply = json.loads(line)
            elapsed = time.perf_counter_ns() - started
            require(reply.get("ok"), "normalHostRejected")
            require(reply["request_stats"]["cas_get_calls"] == reply["request_stats"]["full_blob_sha256_calls"], "hostEveryGetRehashed")
            action = read_json(kwargs["authorization"])["payload"]
            record = {"event_id": action["request_id"], "kind": action["kind"], "request_bytes": len(raw), "response_bytes": len(line),
                      "caller_ns": elapsed, "inside_propose_ns": reply["elapsed_ns"], "request_stats": reply["request_stats"],
                      "cumulative_stats": reply["cumulative_stats"], "inspection_cache_entries": reply["inspection_cache_entries"]}
            self.worker_events.append(record)
            with (self.root / "host_worker.jsonl").open("ab") as sink:
                sink.write(canonical(record) + b"\n")
            call = {"role_process": "propose", "transport": "persistent_public_stdio", "worker_argv": self.worker_argv,
                    "message": message, "elapsed_ns": elapsed, "exit_code": 0, "stdout": canonical(reply["result"]).decode(), "stderr": ""}
            self.calls.append(call)
            with (self.root / "role_calls.jsonl").open("ab") as sink:
                sink.write(canonical(call) + b"\n")
            return reply["result"]

        def close(self):
            if self.host_worker is not None:
                if self.host_worker.poll() is None:
                    self.host_worker.stdin.close()
                    self.host_worker.wait(timeout=30)
                lifetime = time.perf_counter_ns() - self.worker_started
                self.worker_log.close()
                rows = self.worker_events
                self.worker_report = {"worker_processes": 1, "worker_pid": self.worker_pid, "requests": len(rows),
                    "startup_ns": self.worker_startup_ns, "lifetime_including_idle_public_pipeline_and_shutdown_ns": lifetime,
                    "proposal_caller_total_ns": sum(r["caller_ns"] for r in rows),
                    "proposal_inside_function_total_ns": sum(r["inside_propose_ns"] for r in rows),
                    "stats": rows[-1]["cumulative_stats"] if rows else None,
                    "inspection_cache_entries": rows[-1]["inspection_cache_entries"] if rows else 0,
                    "stdio_request_bytes": sum(r["request_bytes"] for r in rows), "stdio_response_bytes": sum(r["response_bytes"] for r in rows),
                    "clean_exit": self.host_worker.returncode == 0, "cache_scope": "one full public history, no eviction; metadata only"}
                self.host_worker = None
            super().close()

    def read_line(worker):
        raw = worker.stdout.readline()
        require(bool(raw), "emptyWorkerResponse")
        return json.loads(raw)

    histories = []
    public_start = time.perf_counter_ns()
    phase = "public"
    active = None
    try:
        for history in (0, 1):
            history_start = time.perf_counter_ns()
            selected = [e for e in events if e["event_id"].startswith(f"h{history}-")]
            require(len(selected) == 240, "historyCompleteDenominator")
            report_dir = reports / f"history_{history}"
            report_dir.mkdir()
            active = instance = PersistentRun(runtime / f"history_{history}")
            setup_ns = time.perf_counter_ns() - history_start
            accepted, transitions, fresh, query_ids = [], [], [], []
            expiry = 0
            for ordinal, event in enumerate(selected, 1):
                begun = time.perf_counter_ns()
                extra = {"vector": event["issuer_vector_path"]} if event["kind"] == "Learn" else {
                    "query_index": int(Path(event["public_query_vector_path"]).stem[1:])}
                request = instance.prepare(event["kind"], event["route"], event["event_id"], **extra)
                reply = instance.accepted(request)
                require(reply["status"] == "accepted" and reply["envelope"]["payload"]["revision"] == ordinal, "orderedNewAcceptance")
                if event["kind"] == "Learn":
                    require(reply["delivery"]["status"] == "verified_not_a_release", "learnPublicIndependentSync")
                    fresh.append(request["action"]["fresh_ct"])
                    expiry += request["proposal"]["expired_ct"] is not None
                else:
                    require(reply["delivery"]["reader"]["status"] == "ciphertextAccepted", "ciphertextOnlyPublicAck")
                    query_ids.append(event["event_id"])
                require(not (instance.root / ".private/reader/answers.sqlite3").exists(), "noPrivateDrainDuringPublicHistory")
                accepted.append(reply["envelope"])
                row = {"event_id": event["event_id"], "kind": event["kind"], "route": event["route"], "revision": ordinal,
                       "elapsed_ns": time.perf_counter_ns() - begun, "envelope_sha256": digest(reply["envelope"])}
                transitions.append(row)
                with (instance.root / "transitions.jsonl").open("ab") as sink:
                    sink.write(canonical(row) + b"\n")
                dump(reports / "checkpoint.json", {"phase": "public", "history": history, "last_completed_revision": ordinal,
                     "learns": len(fresh), "infers": len(query_ids), "expiries": expiry, "last_envelope_sha256": row["envelope_sha256"],
                     "elapsed_public_ns": time.perf_counter_ns() - public_start})
                if ordinal % 20 == 0:
                    print(json.dumps({"phase": "public", "history": history, "events": ordinal, "accepted_ciphertext_outputs": len(query_ids)}), flush=True)
            # All replay, state, history and public-domain checks precede any drain.
            head = instance.head()
            verified = rpc(instance.rcfg["socket"], {"op": "verified_status"})
            status = rpc(instance.rcfg["socket"], {"op": "status"})
            require(verified["revision"] == 240 and status["received"] == status["selected"] == 48, "completePublicHistory")
            with sqlite3.connect(instance.rcfg["db"]) as db:
                vstate = json.loads(db.execute("SELECT state FROM verified_head").fetchone()[0])
                rows = [json.loads(r[0]) for r in db.execute("SELECT envelope FROM verified_journal ORDER BY revision")]
                columns = [r[1] for r in db.execute("PRAGMA table_info(received)")]
                require("answer" not in columns, "publicAcceptanceHasNoScalarColumn")
            require(rows == accepted and vstate == head["state"] and digest(vstate) == verified["state_digest"], "exactIndependentHistoryAndState")
            require(len(fresh) == len(set(fresh)) == 192 and len(query_ids) == 48 and expiry == 128, "allHistoryEventsAndExpiries")
            replay_start = time.perf_counter_ns()
            replay = instance.replay(True)
            replay_ns = time.perf_counter_ns() - replay_start
            require(replay["revision"] == 240 and replay["state_digest"] == verified["state_digest"], "fullPublicRecomputedReplay")
            require(replay["admissions"] == {"0": 128, "1": 64} and replay["queue_lengths"] == {"0": 32, "1": 32}, "exactFinalRouteCounts")
            calls = [json.loads(line) for line in (instance.root / "commands.jsonl").read_bytes().splitlines()]
            costs, counts = collections.defaultdict(list), collections.Counter()
            host_counts, cache = collections.Counter(), {}
            setup_phases = []
            for call in calls:
                command = call["command"][1]
                require(call["exit_code"] == 0 and command != "reader-decrypt" and not call["private_output_omitted"], "publicCommandsOnly")
                payload = json.loads(call["stdout"])
                require("signed_score" not in payload, "noScalarInPublicLog")
                costs[(call["role"], command)].append(call["elapsed_ns"])
                counts.update(payload.get("counts", {}))
                if call["role"] in ["host", "authority", "reader", "public_transport", "independent_public_replay"]:
                    require(command in ["inspect", "host-learn", "host-infer"] and "--sk" not in call["command"] and "--vector" not in call["command"], "keylessPublicProcessArguments")
                if call["role"] == "host":
                    host_counts[command] += 1
                    if command == "inspect":
                        cache[payload["sha256"]] = payload
                if command == "keygen":
                    setup_phases = payload["phases"]
                    require(payload["master_serialized"] is False and payload["projection_delivery_files_remaining"] == 0, "setupLifecycleReport")
            scalar_dir = instance.root / ".private/reader/recipient_keys"
            require(sorted(p.name for p in scalar_dir.iterdir()) == [f"r{i:02d}.key" for i in range(16)], "onlyFinalRecipientFiles")
            require(all(p.stat().st_size == 435 and p.stat().st_mode & 0o777 == 0o600 for p in scalar_dir.iterdir()), "recipientScalarInventory")
            require(not any("recipient_key" in k or "private_db" in k for k in instance.rcfg), "publicAcceptorConfigNoScalarPaths")
            live = [route["acc_ct"] for route in vstate["routes"].values()] + [e["ct_sha256"] for route in vstate["routes"].values() for e in route["queue"]]
            storage = {}
            for name, directory in [("host", instance.host_cas.root), ("authority", Path(instance.acfg["cas"])), ("verified_acceptor", Path(instance.rcfg["cas"]))]:
                fs = [p for p in directory.iterdir() if p.is_file() and len(p.name) == 64]
                storage[name] = {"objects": len(fs), "bytes": sum(p.stat().st_size for p in fs)}
            logical_bytes = sum((instance.host_cas.root / h).stat().st_size for h in live)
            # All public services/workers are closed before any recipient scalar is loaded.
            instance.close()
            active = None
            host_report = instance.worker_report
            require(host_report["requests"] == 240 and host_report["clean_exit"], "onePersistentWorkerCompleteHistory")
            require(host_report["stats"]["crypto_calls"] == dict(host_counts) and len(cache) == host_report["inspection_cache_entries"], "workerMeterAndActualCalls")
            host_report["cache_canonical_json_bytes"] = len(canonical(cache))
            host_report["cache_bytes_are_not_heap_rss"] = True
            child_counts = collections.Counter()
            for item in setup_phases:
                child_counts.update(item["counts"])
            hreport = {"ok": True, "history": history, "events": 240, "learns": 192, "infers": 48, "expiries": 128,
                "context_id": instance.g["context_id"], "genesis_sha256": digest(instance.g), "independent_verified_status": verified,
                "exact_authority_verified_journal_and_state": True, "public_replay": replay,
                "setup_and_public_services_start_ns": setup_ns, "public_recomputed_replay_ns": replay_ns,
                "public_history_elapsed_ns": time.perf_counter_ns() - history_start,
                "private_answer_db_absent_through_public_checks": True, "public_services_closed_before_private_drain": True,
                "public_cli_calls": len(calls), "top_level_native_counts": dict(counts), "setup_child_native_counts": dict(child_counts),
                "role_command_costs": [{"role": role, "command": cmd, "count": len(xs), "sum_ns": sum(xs), "min_ns": min(xs), "max_ns": max(xs)} for (role, cmd), xs in sorted(costs.items())],
                "bytes": {"logical_live_state_ciphertexts": len(live), "logical_live_state_ciphertext_bytes": logical_bytes,
                          "state_json_bytes": len(canonical(vstate)), "public_context_bytes": (instance.root / "public_context.json").stat().st_size,
                          "retained_cas": storage, "recipient_keys": 16, "recipient_key_bytes_each": 435},
                "host_worker": host_report, "setup_phases": setup_phases}
            dump(report_dir / "public_report.json", hreport)
            dump(report_dir / "accepted_envelopes.json", accepted)
            for name in ["commands.jsonl", "role_calls.jsonl", "events.jsonl", "host_worker.jsonl", "transitions.jsonl", "genesis.json", "context_validation.json", "replay.json"]:
                with gzip.open(report_dir / (name + ".gz"), "wb") as sink:
                    sink.write((instance.root / name).read_bytes())
            histories.append(hreport)
        public_end_ns = time.perf_counter_ns() - public_start
        check_preparation(runtime, reports)
        dump(reports / "public_complete.json", {"ok": True, "histories": histories, "events": 480, "learns": 384,
             "infers": 96, "expiries": 256, "whole_public_phase_ns": public_end_ns,
             "all_public_replay_status_history_checks_before_any_private_drain": True,
             "all_public_workers_and_services_closed": True})
        phase = "private"
        # Nothing below performs a host/authority/acceptor RPC or logs a private elapsed time publicly.
        private_root = runtime / ".private_postprotocol"
        private_root.mkdir(mode=0o700)
        drains = []
        for history in (0, 1):
            config = runtime / f"history_{history}/.private/reader/drain_config.json"
            command = [sys.executable, str(source / "journal/drain.py"), "--config", str(config)]
            begun = time.perf_counter_ns()
            out = subprocess.run(command, capture_output=True, timeout=1800)
            dump(private_root / f"drain{history}.json", {"argv": command, "elapsed_ns": time.perf_counter_ns() - begun,
                 "exit_code": out.returncode, "stdout": out.stdout.decode(), "stderr": out.stderr.decode()}, True)
            require(out.returncode == 0, "privateDrainFailed")
            result = json.loads(out.stdout)
            require(result["new_private_decodes"] == result["private_decodes_total"] == 48, "allPrivateRecipientOutputs")
            drains.append({"history": history, "private_decodes": 48})
        oracle_out = private_root / "utility_comparison.json"
        command = [sys.executable, str(source / "private_oracle.py"), "--runtime", str(runtime), "--out", str(oracle_out)]
        begun = time.perf_counter_ns()
        out = subprocess.run(command, capture_output=True, timeout=300)
        dump(private_root / "oracle_call.json", {"argv": command, "elapsed_ns": time.perf_counter_ns() - begun,
             "exit_code": out.returncode, "stdout": out.stdout.decode(), "stderr": out.stderr.decode()}, True)
        require(out.returncode == 0, "privateIntegerOracleFailed")
        comparison = read_json(oracle_out)
        require(comparison["all_96_direct_and_frozen_integer_matches"] and comparison["private_output_count"] == 96, "completeIntegerComparison")
        report = {"ok": True, "schema": "complete-designated-fixed-span-utility-v1", "events": 480, "learns": 384,
                  "infers": 96, "expiries": 256, "histories": histories, "private_drains": drains,
                  "all_96_exact_integer_matches": True, "utility_counts": comparison["utility_counts"],
                  "event_outcomes": comparison["event_outcomes"], "original_errors_retained": comparison["original_errors_retained"],
                  "whole_public_phase_ns": public_end_ns, "private_decode_timing_and_scores_omitted": True,
                  "public_completion_precedes_any_private_drain": True, "preparation_sha256": sha(reports / "preparation.json"),
                  "small_integration_pass_sha256": sha(small_path), "source_context_native_interpreter_pins_checked": True,
                  "scope": ["Complete original public577D utility fixture; same52/96,44/80,18/32 outcomes, no model rerun or new utility estimate.",
                            "Fresh classical DDH setup/issuance per history; fixed16-row dedicated recipient coalition, no retained serialized master.",
                            "All public history verification/replay and service shutdown precede private recipient decoding and aggregate comparison.",
                            "Known public fixture is not private-input confidentiality or actual encoder-image nonvacuity evidence.",
                            "Trusted setup/issuer/command policy, erasure and reader persistence; same-account processes, no OS isolation or PQ claim.",
                            "Recipient scalar holders retain fixed-span capability outside the local finality gate; no adversarial experiments."]}
        dump(reports / "report.json", report)
        print(json.dumps({"ok": True, "events": 480, "exact_integer_matches": 96, "original_utility_outcomes_retained": True}), flush=True)
    except Exception as error:
        # Public checkpoints stop before private work; private failures/details stay private.
        target = reports / "failure.json" if phase == "public" else runtime / ".private_postprotocol/failure.json"
        dump(target, {"phase": phase, "error_type": type(error).__name__, "reason": str(error)}, phase != "public")
        if phase == "private":
            print(json.dumps({"ok": False, "phase": "private", "diagnostics_retained_privately": True}), flush=True)
            raise SystemExit(2) from None
        raise
    finally:
        if active is not None:
            active.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="mode", required=True)
    for mode in ("prepare", "run"):
        p = sub.add_parser(mode)
        p.add_argument("--runtime", type=Path, default=HERE / "runtime/full_001")
        p.add_argument("--reports", type=Path, default=HERE / "reports/full_001")
        if mode == "run":
            p.add_argument("--small-pass", type=Path, required=True)
    args = parser.parse_args()
    prepare(args) if args.mode == "prepare" else run(args)


if __name__ == "__main__":
    main()
