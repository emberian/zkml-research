#!/usr/bin/env python3
"""Summarize completed model-specific attack costs without hiding gaps."""
import csv
import hashlib
import json
import math
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
FILES = ["first_pass_ready.jsonl", "additional_attacks.jsonl",
         "quantum_depth_width.jsonl", "nonlattice_attacks.jsonl", "bkw_with_maxima.jsonl"]
rows = []
inputs = []
for name in FILES:
    path = HERE / name
    if not path.exists():
        continue
    content = path.read_bytes()
    parsed = [json.loads(line) for line in content.splitlines()]
    inputs.append({"file": name, "sha256": hashlib.sha256(content).hexdigest(),
                   "rows": len(parsed), "status_counts": dict(Counter(r["status"] for r in parsed))})
    rows.extend(dict(r, result_file=name) for r in parsed)

models = ["MATZOV_classical", "ADPS16_classical", "ADPS16_quantum_core_svp",
          "MATZOV_quantum_depth_width"]
summary = []
for q in ["83", "109"]:
    for samples in ["4096", "infinity"]:
        for model in models:
            group = [r for r in rows if r["Q_bits_label"] == q and r["samples"] == samples
                     and r["model"] == model and r["attack"] not in ["bkw", "arora_gb"]]
            expected_names = {"usvp", "bdd", "dual", "dual_hybrid"}
            if model != "MATZOV_quantum_depth_width":
                expected_names |= {"bdd_hybrid", "bdd_mitm_hybrid"}
            expected = len(expected_names)
            good = [r for r in group if r["status"] == "EXECUTED"
                    and isinstance(r.get("log2_fields", {}).get("rop"), (int, float))
                    and math.isfinite(r["log2_fields"]["rop"])]
            best = min(good, key=lambda r: r["log2_fields"]["rop"]) if good else None
            summary.append({"Q_bits_label": q, "samples": samples, "model": model,
                            "expected_lattice_attacks": expected,
                            "attempted_lattice_attacks": len({r["attack"] for r in group}),
                            "finite_completed_lattice_attacks": len({r["attack"] for r in good}),
                            "coverage_complete_for_named_suite": expected_names <= {r["attack"] for r in good},
                            "best_completed_lattice_attack": best["attack"] if best else None,
                            "selected_result_file": best["result_file"] if best else None,
                            "log2_estimated_cost": best["log2_fields"]["rop"] if best else None,
                            "beta": best["fields"].get("beta") if best else None,
                            "failures": [{"attack": r["attack"], "status": r["status"],
                                           "exception": r.get("exception")} for r in group if r not in good]})

isolated = []
invocations = HERE / "isolated_invocations.json"
if invocations.exists():
    for invocation in json.loads(invocations.read_text()):
        record_path = HERE / (invocation["name"] + ".jsonl")
        row = json.loads(record_path.read_text())
        prior = next((r for r in rows if all(r[k] == row[k] for k in ["Q_bits_label", "samples", "model", "attack"])), None)
        bits = row.get("log2_fields", {}).get("rop")
        prior_bits = prior.get("log2_fields", {}).get("rop") if prior else None
        difference = bits - prior_bits if isinstance(bits, (int, float)) and isinstance(prior_bits, (int, float)) else None
        isolated.append({"result_file": record_path.name,
                         **{k: row[k] for k in ["Q_bits_label", "samples", "model", "attack", "status"]},
                         "log2_estimated_cost": bits, "difference_from_original": difference,
                         "exception": row.get("exception")})
    checked = [r for r in isolated if r["difference_from_original"] is not None]
    assert len(checked) == 16 and all(abs(r["difference_from_original"]) < 1e-12 for r in checked)

result = {
    "status": "EXECUTED aggregation of pinned heuristic attack estimates",
    "scope": "minimum of completed named lattice attacks per model; not an all-attacks security bound or a PQ proof",
    "input_results": inputs, "lattice_summary": summary,
    "isolated_verification": isolated,
    "isolated_scope": "separate rechecks, not duplicate attack coverage; 16 original minimum candidates exactly reproduced; previously failed calls keep their failure history",
    "nonlattice_attempts": [{k: r.get(k) for k in ["Q_bits_label", "samples", "attack", "status", "log2_fields", "exception", "result_file"]}
                           for r in rows if r["attack"] in ["bkw", "arora_gb"]],
}
(HERE / "summary.json").write_text(json.dumps(result, indent=2) + "\n")
with (HERE / "summary.csv").open("w", newline="") as output:
    keys = [k for k in summary[0] if k != "failures"]
    writer = csv.DictWriter(output, fieldnames=keys)
    writer.writeheader()
    writer.writerows({k: r[k] for k in keys} for r in summary)
print(json.dumps({"inputs": inputs, "lattice_summary": summary}, indent=2))
