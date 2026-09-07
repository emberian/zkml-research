#!/usr/bin/env python3
"""Eight normal public proposals; no recipient keys, decode or adverse controls."""
from pathlib import Path
import argparse
import copy
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime", type=Path, default=HERE / "runtime/paired_001")
    parser.add_argument("--reports", type=Path, default=HERE / "reports/paired_001")
    args = parser.parse_args()
    runtime, reports = args.runtime.resolve(), args.reports.resolve()
    runtime.mkdir(parents=True, exist_ok=False, mode=0o700)
    reports.mkdir(parents=True, exist_ok=False)
    adapter = runtime / "adapter"
    adapter.mkdir()
    for name in ("host.py", "source_pins.json"):
        shutil.copy2(HERE / name, adapter / name)
    shutil.copytree(HERE / "frozen_source", adapter / "frozen_source", ignore=shutil.ignore_patterns("__pycache__"))
    pins = json.loads((adapter / "source_pins.json").read_text())
    for name, entry in pins["core"].items():
        assert sha(adapter / "frozen_source" / name) == entry["sha256"]
    sys.path.insert(0, str(adapter / "frozen_source/journal"))
    import common
    import model
    canonical, write_json, read_json, digest = common.canonical, common.write_json, common.read_json, common.digest
    crypto_dir = runtime / "crypto"
    crypto_dir.mkdir()
    crypto_source = HERE.parent / "crypto"
    for name, expected in pins["crypto_runtime"].items():
        shutil.copy2(crypto_source / name, crypto_dir / name)
        assert sha(crypto_dir / name) == expected
    public, private = runtime / "public", runtime / "private"
    public.mkdir()
    private.mkdir(mode=0o700)
    # Import only already-public artifacts from the completed private-setup run.
    context_source = crypto_source / "runtime/positive_001/public/context.json"
    zero_source = crypto_source / "runtime/positive_001/public/zero.ct"
    shutil.copy2(context_source, public / "public_context.json")
    shutil.copy2(zero_source, public / "zero.ct")
    source_report = read_json(crypto_source / "reports/positive_001/report.json")
    assert sha(public / "public_context.json") == source_report["context_sha256"]
    events = []
    for n in range(1, 7):
        events.append({"kind": "Learn", "admission": n})
        if n in (3, 6):
            events.append({"kind": "Infer", "admission": n, "row": 0 if n == 3 else 1})
    pre = {"schema": "designated-host-positive-paired-predeclaration-v1", "events": events,
           "capacity": 32, "expected_expiries": 0, "dimension": 577,
           "public_vector_formula": "x[n,j]=((17*n+13*j)%255)-127; n=1..6,j=0..576",
           "same_ciphertexts_and_signed_actions_both_modes": True, "alternate_first_mode": True,
           "recipient_or_master_scalar_files_copied": 0, "recipient_decode_commands": 0,
           "source_pins_sha256": sha(adapter / "source_pins.json"), "host_sha256": sha(adapter / "host.py"),
           "driver_sha256": sha(__file__), "protocol_sha256": sha(HERE / "PROTOCOL.md"),
           "source_public_context_sha256": sha(context_source),
           "source_positive_report_sha256": sha(crypto_source / "reports/positive_001/report.json")}
    write_json(reports / "predeclared.json", pre)
    start = time.perf_counter_ns()
    native = Path("/opt/homebrew/opt/openssl@3/lib/libcrypto.3.dylib").resolve()
    base = {"crypto_binary": str(crypto_dir / "crypto.py"), "crypto_binary_sha256": sha(crypto_dir / "crypto.py"),
            "crypto_sources": pins["crypto_runtime"], "native_dependency": {"path": str(native), "sha256": sha(native)},
            "crypto_context": str(public / "public_context.json"), "crypto_context_sha256": sha(public / "public_context.json")}
    setup = common.Crypto(base, "public_fixture_preparation", reports / "preparation_commands.jsonl")
    params = setup.run("params")
    validation = setup.run("validate-context")
    assert validation["validated"] and validation["source_sha256"] == pins["crypto_runtime"]
    write_json(public / "context_validation.json", validation)
    rows = read_json(crypto_dir / "rows.json")
    policy, bindings, queries = [], {}, {}
    for i in (0, 1):
        row_path = public / f"row{i:02d}.json"
        row_path.write_bytes(canonical(rows[i]))
        query_path = public / f"query{i:02d}.json"
        meta = setup.run("encode-query", vector=row_path, out=query_path)
        query = read_json(query_path)
        policy.append({"query_ct": meta["sha256"], "route": 0})
        bindings[meta["sha256"]] = {k: query[k] for k in ("context_id", "row_id", "row_sha256", "recipient_id", "token_sha256")}
        queries[i] = query_path
    issuer_vk = common.create_signing_key(private / "issuer-signing.key")
    command_vk = common.create_signing_key(private / "command-signing.key")
    authority_vk = common.create_signing_key(private / "unused-authority-signing.key")
    journal_sources = {(name[len("journal/"):] if name.startswith("journal/") else "../" + name): entry["sha256"]
                       for name, entry in pins["core"].items()}
    g = {"schema": "resident-genesis-v1", "crypto": params, "key_id": base["crypto_context_sha256"],
         "context_id": base["crypto_context_sha256"], "public_key_sha256": base["crypto_context_sha256"],
         "zero_ct_sha256": sha(public / "zero.ct"), "capacity": 32, "routes": [0, 1],
         "issuer_vk": issuer_vk, "command_vk": command_vk, "authority_vk": authority_vk,
         "recipient": "dedicated-fixed-span-recipient-coalition", "query_policy": policy, "query_bindings": bindings,
         "feature_policy": "trusted-issuer-signed577-int8-bound127-v1",
         "journal_program": "designated-ddh-keyless-recomputation-delta-journal-two-phase-v1",
         "crypto_binary_sha256": base["crypto_binary_sha256"], "crypto_sources": base["crypto_sources"],
         "native_dependency": base["native_dependency"], "context_validation_sha256": sha(public / "context_validation.json"),
         "journal_sources": journal_sources,
         "fixture_scope": "public proposal comparison only; no authority or reader process and no recipient scalar"}
    write_json(public / "genesis.json", g)
    base.update(genesis_path=str(public / "genesis.json"), genesis_sha256=digest(g))
    configs, cases = {}, {}
    for mode in ("once", "persistent", "original"):
        cfg = {**base, "command_log": str(reports / f"{mode}_crypto_commands.jsonl")}
        config = public / f"{mode}_config.json"
        write_json(config, cfg)
        cas = runtime / f"{mode}_cas"
        cas.mkdir()
        for path in [public / "zero.ct", *queries.values()]:
            shutil.copy2(path, cas / sha(path))
        configs[mode], cases[mode] = config, cas
    startup_begin = time.perf_counter_ns()
    worker = subprocess.Popen([sys.executable, str(adapter / "host.py"), "serve", "--config", str(configs["persistent"]),
                               "--cas", str(cases["persistent"])], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    ready = common.parse_json(worker.stdout.readline())
    startup_ns = time.perf_counter_ns() - startup_begin
    assert ready["ok"] and ready["ready"] and ready["inspection_cache_entries"] == 0
    head = {"ok": True, "revision": 0, "state": common.initial_state(g)}
    head["state_digest"] = digest(head["state"])
    pairs, issuer_inputs = [], []
    try:
        for index, event in enumerate(events):
            case = public / f"event{index:02d}"
            case.mkdir()
            head_path, authorization = case / "head.json", case / "authorization.json"
            write_json(head_path, head)
            if event["kind"] == "Learn":
                n = event["admission"]
                values = [((17 * n + 13 * j) % 255) - 127 for j in range(577)]
                vector_path = case / "public_vector.json"
                write_json(vector_path, values)
                fresh = case / "fresh.ct"
                meta = setup.run("issuer-encrypt", pk=public / "public_context.json", vector=vector_path, out=fresh)
                for directory in cases.values():
                    shutil.copy2(fresh, directory / meta["sha256"])
                action = model.make_action(g, head, "Learn", 0, f"normal-learn-{n}", f"normal-nonce-{index}",
                                          record_id=f"public-input-{n}", fresh_ct=meta["sha256"],
                                          feature_policy=g["feature_policy"], range_assertion=[-127, 127])
                auth = common.sign(action, private / "issuer-signing.key", "resident-issuer-v1")
                issuer_inputs.append({"admission": n, "public_vector_sha256": sha(vector_path), "fresh_ct_sha256": meta["sha256"]})
            else:
                query = read_json(queries[event["row"]])
                action = model.make_action(g, head, "Infer", 0, f"normal-infer-{index}", f"normal-nonce-{index}",
                                          query_ct=sha(queries[event["row"]]), recipient=query["recipient_id"], row_id=query["row_id"],
                                          row_sha256=query["row_sha256"], token_sha256=query["token_sha256"])
                auth = common.sign(action, private / "command-signing.key", "resident-query-authorization-v1")
            write_json(authorization, auth)
            replies = {}
            for mode in (("once", "persistent") if index % 2 == 0 else ("persistent", "once")):
                out = case / f"{mode}_request.json"
                before = time.perf_counter_ns()
                if mode == "once":
                    argv = [sys.executable, str(adapter / "host.py"), "once", "--config", str(configs[mode]), "--cas", str(cases[mode]),
                            "--head", str(head_path), "--authorization", str(authorization), "--out", str(out)]
                    done = subprocess.run(argv, capture_output=True, timeout=300)
                    assert done.returncode == 0, done.stderr.decode()
                    reply = common.parse_json(done.stdout)
                else:
                    request = {"head": str(head_path), "authorization": str(authorization), "out": str(out)}
                    worker.stdin.write(canonical(request) + b"\n")
                    worker.stdin.flush()
                    reply = common.parse_json(worker.stdout.readline())
                wall = time.perf_counter_ns() - before
                assert reply["ok"]
                replies[mode] = {"reply": reply, "caller_wall_ns": wall, "request_bytes": out.read_bytes()}
            assert replies["once"]["request_bytes"] == replies["persistent"]["request_bytes"]
            req = read_json(case / "once_request.json")
            result_hash = req["proposal"]["result_ct"]
            assert (cases["once"] / result_hash).read_bytes() == (cases["persistent"] / result_hash).read_bytes()
            for key in ("cas_get_calls", "full_blob_sha256_calls", "full_blob_sha256_bytes"):
                assert replies["once"]["reply"]["request_stats"][key] == replies["persistent"]["reply"]["request_stats"][key]
            if index == 0:
                out = case / "original_request.json"
                argv = [sys.executable, str(adapter / "frozen_source/journal/roles.py"), "propose", "--config", str(configs["original"]),
                        "--cas", str(cases["original"]), "--head", str(head_path), "--authorization", str(authorization), "--out", str(out)]
                done = subprocess.run(argv, capture_output=True, timeout=300)
                assert done.returncode == 0 and out.read_bytes() == replies["once"]["request_bytes"]
                assert (cases["original"] / result_hash).read_bytes() == (cases["once"] / result_hash).read_bytes()
                write_json(reports / "original_first_proposal.json", {"argv": argv, "exit_code": 0, "stdout": common.parse_json(done.stdout),
                                                                       "request_bytes_equal": True, "result_ciphertext_bytes_equal": True})
            state = copy.deepcopy(head["state"])
            if event["kind"] == "Learn":
                route = state["routes"]["0"]
                route["queue"].append({"record_id": action["record_id"], "ct_sha256": action["fresh_ct"]})
                route["admissions"] += 1
                route["acc_ct"] = result_hash
            assert digest(state) == req["proposal"]["next_state"] and req["proposal"]["expired_ct"] is None
            head = {"ok": True, "revision": head["revision"] + 1, "state": state, "state_digest": digest(state)}
            pair = {"index": index, **event, "same_proposal_bytes": True, "same_result_ciphertext_bytes": True,
                    "same_full_get_hash_counts_and_bytes": True, "request_sha256": digest(req), "result_ct_sha256": result_hash,
                    "once": {k: v for k, v in replies["once"].items() if k != "request_bytes"},
                    "persistent": {k: v for k, v in replies["persistent"].items() if k != "request_bytes"}}
            pairs.append(pair)
            with (reports / "pairs.jsonl").open("ab") as sink:
                sink.write(canonical(pair) + b"\n")
            print(canonical({"event": "normal_pair_passed", "index": index, "kind": event["kind"]}).decode(), flush=True)
        worker.stdin.close()
        assert worker.wait(timeout=30) == 0
        assert not worker.stderr.read()
    finally:
        if worker.poll() is None:
            worker.terminate()
            worker.wait(timeout=30)
    total_ns = time.perf_counter_ns() - start
    totals = {}
    for mode in ("once", "persistent"):
        totals[mode] = {"caller_wall_ns": sum(p[mode]["caller_wall_ns"] for p in pairs),
                        "propose_function_ns": sum(p[mode]["reply"]["elapsed_ns"] for p in pairs),
                        "cas_get_calls": sum(p[mode]["reply"]["request_stats"]["cas_get_calls"] for p in pairs),
                        "full_blob_sha256_calls": sum(p[mode]["reply"]["request_stats"]["full_blob_sha256_calls"] for p in pairs),
                        "full_blob_sha256_bytes": sum(p[mode]["reply"]["request_stats"]["full_blob_sha256_bytes"] for p in pairs),
                        "crypto_calls": {}}
        for pair in pairs:
            for command, count in pair[mode]["reply"]["request_stats"]["crypto_calls"].items():
                totals[mode]["crypto_calls"][command] = totals[mode]["crypto_calls"].get(command, 0) + count
        commands = [read_json_line for read_json_line in map(common.parse_json, (reports / f"{mode}_crypto_commands.jsonl").read_bytes().splitlines())]
        assert all(r["command"][1] in ("inspect", "host-learn", "host-infer") and "--sk" not in r["command"] and "--vector" not in r["command"] for r in commands)
    assert all(sha(adapter / "frozen_source" / name) == entry["sha256"] for name, entry in pins["core"].items())
    assert sha(adapter / "host.py") == pre["host_sha256"] and sha(adapter / "source_pins.json") == pre["source_pins_sha256"]
    assert sha(native) == base["native_dependency"]["sha256"]
    report = {"passed": True, "classification": "EXECUTED normal paired designated keyless host proposal comparison",
              "predeclared_sha256": sha(reports / "predeclared.json"), "pairs_sha256": sha(reports / "pairs.jsonl"),
              "source_pins_sha256": pre["source_pins_sha256"], "host_sha256": pre["host_sha256"], "driver_sha256": sha(__file__),
              "context_id": g["context_id"], "genesis_sha256": digest(g), "normal_proposals": 8, "learns": 6, "infers": 2,
              "expiries": 0, "capacity": 32, "all_proposals_and_result_bytes_equal": True, "original_entrypoint_first_pair_equal": True,
              "all_CAS_full_read_hash_counts_and_bytes_equal": True, "totals": totals,
              "paired_caller_wall_ratio_once_over_persistent": totals["once"]["caller_wall_ns"] / totals["persistent"]["caller_wall_ns"],
              "worker_startup_ns": startup_ns, "worker_ready": ready, "worker_instances": 1,
              "worker_requests": 8, "final_inspection_cache_entries": pairs[-1]["persistent"]["reply"]["inspection_cache_entries"],
              "cache_scope": "existing public Ct inspection metadata retained until worker exit; no eviction",
              "harness_total_ns": total_ns, "harness_total_is_not_full_end_to_end_optimization": True,
              "public_issuer_inputs": issuer_inputs, "host_has_scalar_key_or_vector_arguments": False,
              "recipient_master_scalar_files_in_fixture": 0, "recipient_decodes": 0, "authority_commits": 0,
              "source_and_native_pins_unchanged": True, "native_dependency": base["native_dependency"],
              "scope": "public fixture, proposal equivalence only; no utility/private-ingress/recipient release or adversarial tests",
              "python": sys.version}
    write_json(reports / "report.json", report)
    print(canonical({"passed": True, "proposals": 8, "paired_wall_ratio": report["paired_caller_wall_ratio_once_over_persistent"],
                     "harness_total_ns": total_ns}).decode(), flush=True)


if __name__ == "__main__":
    main()
