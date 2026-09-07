#!/usr/bin/env python3
"""Paired normal encrypted proposals around a frozen, unchanged journal core."""
import argparse
import collections
import gzip
import json
import shutil
import statistics
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE / "frozen_core"))
from common import *
from run import Run


def snapshot_check():
    pins = read_json(HERE / "source_pins.json")
    for name, record in pins["core"].items():
        require(sha((HERE / "frozen_core" / name).read_bytes()) == record["sha256"], "coreSnapshotChanged")
    source = Path(pins["crypto_binary_source"])
    require(sha(source.read_bytes()) == pins["crypto_binary_sha256"], "cryptoSourceChanged")
    return pins


class PairedRun(Run):
    def __init__(self, root, queries, binary, report_dir):
        self.pairs = []
        self.report_dir = report_dir
        self.worker = None
        super().__init__(root, queries, binary=binary)
        self.peer_cas = self.root / "peer_cas"
        self.peer_cas.mkdir()
        for source in self.host_cas.root.iterdir():
            if source.is_file() and len(source.name) == 64:
                shutil.copyfile(source, self.peer_cas / source.name)
        self.peer_config = self.root / "peer_host_config.json"
        write_json(self.peer_config, {**self.hcfg, "command_log": str(self.root / "peer_commands.jsonl")})
        self.worker_argv = [sys.executable, str(HERE / "host.py"), "serve",
                            "--config", str(self.peer_config), "--cas", str(self.peer_cas)]
        self.worker_stderr = (self.root / "worker.stderr").open("wb")
        start = time.perf_counter_ns()
        self.worker = subprocess.Popen(self.worker_argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                       stderr=self.worker_stderr)
        ready = parse_json(self.worker.stdout.readline())
        require(ready == {"ok": True, "ready": True}, "workerStartup")
        self.worker_startup_ns = time.perf_counter_ns() - start

    def role(self, command, **kwargs):
        if command != "propose":
            return super().role(command, **kwargs)
        auth = read_json(kwargs["authorization"])
        a = auth["payload"]
        if a["kind"] == "Learn":
            source = self.host_cas.path(a["fresh_ct"])
            target = self.peer_cas / a["fresh_ct"]
            require(not target.exists(), "freshCiphertextUnique")
            shutil.copyfile(source, target)
        peer_out = Path(kwargs["out"]).with_name("peer-request.json")
        peer_message = {"head": str(kwargs["head"]), "authorization": str(kwargs["authorization"]), "out": str(peer_out)}
        argv = [sys.executable, str(HERE / "host.py"), "once"]
        for key, value in kwargs.items():
            argv.extend(["--" + key.replace("_", "-"), str(value)])

        def baseline():
            start = time.perf_counter_ns()
            call = subprocess.run(argv, capture_output=True, timeout=180)
            elapsed = time.perf_counter_ns() - start
            require(call.returncode == 0, "baselineRejected:" + call.stdout.decode() + call.stderr.decode())
            reply = parse_json(call.stdout)
            require(reply["ok"], "baselineReply")
            return reply, elapsed

        def persistent():
            start = time.perf_counter_ns()
            self.worker.stdin.write(canonical(peer_message) + b"\n")
            self.worker.stdin.flush()
            reply = parse_json(self.worker.stdout.readline())
            elapsed = time.perf_counter_ns() - start
            require(reply.get("ok"), "workerRejected:" + str(reply))
            return reply, elapsed

        order = "baseline-first" if len(self.pairs) % 2 == 0 else "persistent-first"
        if order == "baseline-first":
            b, bt = baseline()
            p, pt = persistent()
        else:
            p, pt = persistent()
            b, bt = baseline()
        br, pr = Path(kwargs["out"]).read_bytes(), peer_out.read_bytes()
        require(br == pr, "pairedCanonicalRequestBytes")
        require(b["result"] == p["result"], "pairedCLIResult")
        request = parse_json(br)
        ct_hash = request["proposal"]["result_ct"]
        baseline_bytes = (self.host_cas.root / ct_hash).read_bytes()
        persistent_bytes = (self.peer_cas / ct_hash).read_bytes()
        require(baseline_bytes == persistent_bytes and sha(baseline_bytes) == ct_hash, "pairedCiphertextBytes")
        for field in ("cas_get_calls", "full_blob_sha256_calls", "full_blob_sha256_bytes"):
            require(b["request_stats"][field] == p["request_stats"][field], "pairedRehash:" + field)
        require(b["request_stats"]["cas_get_calls"] == b["request_stats"]["full_blob_sha256_calls"], "allGetsHashed")
        pair = {"event_id": a["request_id"], "kind": a["kind"], "order": order,
                "request_sha256": sha(br), "request_digest": digest(request), "result_ct": ct_hash,
                "next_state": request["proposal"]["next_state"], "expired_ct": request["proposal"]["expired_ct"],
                "request_bytes": len(br), "ciphertext_bytes": len(baseline_bytes),
                "canonical_request_bytes_equal": True, "ciphertext_bytes_equal": True,
                "baseline_caller_ns": bt, "persistent_caller_ns": pt, "baseline": b, "persistent": p}
        self.pairs.append(pair)
        with (self.report_dir / "pairs.jsonl").open("ab") as sink:
            sink.write(canonical(pair) + b"\n")
        # One direct original CLI agreement checks the instrumentation adapter.
        if len(self.pairs) == 1:
            direct_out = Path(kwargs["out"]).with_name("direct-cli-request.json")
            direct_args = {**kwargs, "out": direct_out}
            direct = super().role("propose", **direct_args)
            require(direct_out.read_bytes() == br and direct == b["result"], "directOriginalCLIIdentity")
        return b["result"]

    def close(self):
        if self.worker is not None:
            self.worker.stdin.close()
            self.worker.wait(timeout=15)
            self.worker_stderr.close()
        super().close()


def command_totals(pairs, label):
    totals = collections.Counter()
    gets = hashes = size = 0
    for pair in pairs:
        stats = pair[label]["request_stats"]
        totals.update(stats["crypto_calls"])
        gets += stats["cas_get_calls"]
        hashes += stats["full_blob_sha256_calls"]
        size += stats["full_blob_sha256_bytes"]
    wall = [pair[label + "_caller_ns"] for pair in pairs]
    inner = [pair[label]["elapsed_ns"] for pair in pairs]
    return {"crypto_calls": dict(totals), "crypto_subprocesses": sum(totals.values()),
            "host_processes": len(pairs) if label == "baseline" else 1,
            "cas_get_calls": gets, "full_blob_sha256_calls": hashes, "full_blob_sha256_bytes": size,
            "caller_total_ns": sum(wall), "caller_median_ns": statistics.median(wall),
            "inside_propose_total_ns": sum(inner), "inside_propose_median_ns": statistics.median(inner)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--name", default="run_001")
    args = parser.parse_args()
    require(re.fullmatch(r"run_[0-9]{3}", args.name), "runName")
    pins = snapshot_check()
    report_dir = HERE / "results" / args.name
    report_dir.mkdir(parents=True, exist_ok=False)
    runtime = HERE / "runtime" / args.name
    runtime.mkdir(parents=True, exist_ok=False)
    binary = runtime / "resident-crypto"
    shutil.copy2(pins["crypto_binary_source"], binary)
    require(sha(binary.read_bytes()) == pins["crypto_binary_sha256"], "copiedBinaryIdentity")
    fixture_dir = runtime / "fixtures"
    fixture_dir.mkdir()
    queries = [[(j * 11 + shift) % 31 - 15 for j in range(577)] for shift in (0, 7)]
    for i, query in enumerate(queries):
        write_json(fixture_dir / f"query{i}.json", query)
    policy = fixture_dir / "queries.json"
    write_json(policy, [{"route": 0, "path": str(fixture_dir / f"query{i}.json")} for i in range(2)])
    vectors = [[(step * 17 + j * 5) % 255 - 127 for j in range(577)] for step in range(1, 41)]
    for step, vector in enumerate(vectors, 1):
        write_json(fixture_dir / f"vector{step:03d}.json", vector)
    write_json(report_dir / "fixture.json", {"public_deterministic_fixture": True, "vectors": vectors,
               "queries": queries, "infer_after_learns": [1, 16, 33, 40], "capacity": 32})
    write_json(report_dir / "source_pins.json", pins)
    start = time.perf_counter_ns()
    run = PairedRun(runtime / "journal", policy, binary, report_dir)
    oracle = {}
    queue = collections.deque()
    try:
        for step, vector in enumerate(vectors, 1):
            queue.append(vector)
            if len(queue) > 32:
                queue.popleft()
            request = run.prepare("Learn", 0, f"learn-{step:03d}", vector=fixture_dir / f"vector{step:03d}.json")
            run.accepted(request)
            if step in [1, 16, 33, 40]:
                qi = step % 2
                event_id = f"infer-{step:03d}"
                oracle[event_id] = sum(sum(x * y for x, y in zip(row, queries[qi])) for row in queue)
                request = run.prepare("Infer", 0, event_id, query_index=qi)
                run.accepted(request)
            if step % 10 == 0:
                print(json.dumps({"learns_complete": step, "paired_events": len(run.pairs)}), flush=True)
        answers = run.answers()
        require(answers == oracle, "exactReaderOracle")
        replay_start = time.perf_counter_ns()
        replay = run.replay(True)
        replay_ns = time.perf_counter_ns() - replay_start
        baseline = command_totals(run.pairs, "baseline")
        persistent = command_totals(run.pairs, "persistent")
        persistent["worker_startup_ns"] = run.worker_startup_ns
        persistent["final_cache_entries"] = run.pairs[-1]["persistent"]["inspection_cache_entries"]
        report = {"ok": True, "schema": "resident-host-runtime-paired-v1", "events": len(run.pairs),
            "learns": 40, "infers": 4, "expiries": sum(p["expired_ct"] is not None for p in run.pairs),
            "paired_request_bytes_all_equal": True, "paired_ciphertext_bytes_all_equal": True,
            "all_cas_gets_fully_rehashed": True, "direct_original_cli_agreement": True,
            "oracle_all_match": True, "public_fixture_oracle": oracle, "replay": replay,
            "baseline": baseline, "persistent": persistent,
            "host_caller_speedup_excluding_worker_startup": baseline["caller_total_ns"] / persistent["caller_total_ns"],
            "host_caller_speedup_including_worker_startup": baseline["caller_total_ns"] / (persistent["caller_total_ns"] + run.worker_startup_ns),
            "paired_harness_total_ns": time.perf_counter_ns() - start, "public_recomputed_replay_ns": replay_ns,
            "worker_argv": run.worker_argv, "python": sys.version, "source_pins_sha256": sha((HERE / "source_pins.json").read_bytes()),
            "scope": "Paired host-only timing in one normal encrypted journal history; harness includes both proposal paths, setup, issuer, authority, reader, transport and replay. One shared Apple M2 Max run, no optimized end-to-end timing, secrecy or OS isolation claim."}
        require(report["expiries"] == 8 and report["events"] == 44, "workloadCounts")
        write_json(report_dir / "report.json", report)
        # Retain public command/event/proposal evidence, never runtime keys or DBs.
        for name in ("commands.jsonl", "peer_commands.jsonl", "events.jsonl", "role_calls.jsonl", "replay.json"):
            with gzip.GzipFile(filename=str(report_dir / (name + ".gz")), mode="wb", mtime=0) as output:
                output.write((run.root / name).read_bytes())
        requests = [read_json(path) for path in sorted(run.work.glob("*/request.json"))]
        with gzip.GzipFile(filename=str(report_dir / "requests.json.gz"), mode="wb", mtime=0) as output:
            output.write(canonical(requests))
        print(json.dumps({"ok": True, "events": 44, "baseline": baseline, "persistent": persistent,
                          "speedup": report["host_caller_speedup_including_worker_startup"]}), flush=True)
    finally:
        run.close()


if __name__ == "__main__":
    main()
