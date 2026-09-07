#!/usr/bin/env python3
"""Summarize completed owned evidence without rerunning crypto or exposing secrets."""
from pathlib import Path
import argparse
import hashlib
import json

HERE=Path(__file__).resolve().parent
OUT=HERE/"outputs"
def read(path):return json.loads(Path(path).read_text())
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    execution=read(OUT/"crypto_execution.json")
    comparison=read(OUT/"comparison.json")
    assert execution["passed"] and comparison["passed"]
    setup=read(OUT/"setup_cost_private.json")
    issuance=read(OUT/"issuer_progress_private.json")
    host=read(OUT/"host_results.json");stats=host["stats"]
    ciphertexts=sorted((OUT/"ciphertexts").glob("*.bin"))
    checkpoints=sorted((OUT/"checkpoints").glob("*.bin"))
    assert len(ciphertexts)==384 and all(p.stat().st_size==147968 for p in ciphertexts)
    current=read(OUT/"checkpoint.json")
    active=sum(len(q) for q in current["queues"].values())
    assert active==64 and current["completed_events"]==480
    native_counts={"setup":setup["native_powers"],
        "issuer_encryptions":issuance["native_powers"],"issuer_message_table":1,
        "host_subgroup_validation":stats["validation_native_powers"],
        "host_fixed_projections":stats["projection_native_powers"],"host_decoder_setup":2}
    assert sum(native_counts.values())==499972
    role_timing={p["role"]:p["wall_ns"]/1e9 for p in execution["phases"]}
    timings={"setup_measured_seconds":setup["elapsed_ns"]/1e9,
        "issuer_encryption_seconds":issuance["encryption_ns"]/1e9,
        "issuer_serialization_seconds":issuance["serialization_ns"]/1e9,
        "issuer_input_read_seconds":issuance["input_read_ns"]/1e9,
        **{key[:-3]+"_seconds":value/1e9 for key,value in stats.items() if key.endswith("_ns")},
        "host_decoder_setup_seconds":host["decoder_setup_ns_this_process"]/1e9,
        "phase_wall_seconds":role_timing,"full_crypto_wall_seconds":execution["wall_seconds"]}
    files={str(p.relative_to(OUT)):{"bytes":p.stat().st_size,"sha256":sha(p)}
           for p in sorted(OUT.rglob("*")) if p.is_file() and p.name not in ("observed_memory.json","SUMMARY.json")}
    memory=read(OUT/"observed_memory.json") if (OUT/"observed_memory.json").exists() else None
    report={"passed":True,"scope":"completed public-fixture DDH-IPFE fixed-span arithmetic; conditional privacy and private setup/issuer assumptions",
        "script_sha256":sha(__file__),"fixture":{"dimension":577,"fixed_queries":16,"rank":16,
            "kernel_dimension":561,"window_per_route":32,"routes":2,"histories":2},
        "execution_counts":{"learns":384,"selected_scores":96,"expirations":256,
            "exact_queue_product_checks":384,"subgroup_elements_checked":384*578,
            "native_powers_by_phase":native_counts,"native_powers_total":sum(native_counts.values()),
            "native_counter_scope":"from completed call loops; no low-level instruction/RNG-retry count",
            "unissued_queries":0,"full_run_python_secret_exponent_comparisons":0,
            "model_runs":0,"training":0,"fresh_unknown_input_trials":0,"extraction_tests":0},
        "correctness":{"scores_matched":96,"score_comparison_sha256":sha(OUT/"comparison.json"),
            "utility_unchanged":comparison["utility_unchanged"]},
        "timing":timings,
        "storage":{"ciphertext_bytes_each":147968,"public_key_bytes":(OUT/"public.bin").stat().st_size,
            "fixed_keys_bytes":(OUT/"fixed_keys.bin").stat().st_size,
            "retained_issued_ciphertext_count":len(ciphertexts),
            "retained_issued_ciphertext_bytes":sum(p.stat().st_size for p in ciphertexts),
            "final_live_queue_ciphertexts":active,"final_live_queue_plus_aggregates_bytes":(active+2)*147968,
            "retained_aggregate_checkpoint_count":len(checkpoints),
            "retained_aggregate_checkpoint_bytes":sum(p.stat().st_size for p in checkpoints),
            "other_recorded_evidence_bytes":sum(v["bytes"] for key,v in files.items() if not key.startswith(("ciphertexts/","checkpoints/"))),
            "issuer_model_included":False,"encoder_cost_measured":False},
        "observed_memory":None if memory is None else {"scope":memory["scope"],
            "max_observed_rss_kib_by_role":memory["max_observed_rss_kib_by_role"],"samples":len(memory["samples"]),
            "sha256":sha(OUT/"observed_memory.json")},
        "credential_lifecycle":{"master_exported":False,"fixed_keys_exported":16,
            "issuer_uses":"public key plus its input/coins in private process",
            "host_uses":"16 fixed scalar keys, ciphertexts, public queries, queue/checkpoints",
            "erasure_assumption_verified_by_machine":False,"constant_time_protocol_claim":False},
        "full_exposure":"all16 per-input/span/group projections and all retained snapshots remain allowed; no recipient/finality/upgrade/PQ claim",
        "sources":read(OUT/"run_manifest.json"),"artifact_files":files,
        "searches":{"scry_sql":0,"schema":0,"web":0,"kagi":0,"downloads":0,"installs":0}}
    (OUT/"SUMMARY.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({k:report[k] for k in ["passed","execution_counts","correctness","timing","storage","observed_memory"]},indent=2))


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out",type=Path,default=OUT)
    OUT=parser.parse_args().out
    main()
