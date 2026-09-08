#!/usr/bin/env python3
"""Read frozen public inputs; compare retained checks and seal this review only."""
from pathlib import Path
from hashlib import sha256
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
AUTHOR = ROOT / "research/learn_infer_only/experiments/private_construction/public_setup_pq/finite_sampler"


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


author_manifest_hash = "23226a36d44899189716a63bd97378bdf114b8791fa0f80a39ed3f212b1adf4e"
assert digest(AUTHOR / "MANIFEST.json") == author_manifest_hash
manifest = json.loads((AUTHOR / "MANIFEST.json").read_text())
inputs = []
for name, expected in manifest["artifacts"].items():
    path = AUTHOR / name
    assert digest(path) == expected, path
    inputs.append({"path": str(path), "sha256": expected, "scope": "Frozen author artifact"})
for item in manifest["public_input_files"]:
    path = Path(item["path"])
    assert digest(path) == item["sha256"], path
    inputs.append({**item, "scope": "Pinned public parameter/proof provenance; no estimator execution"})
inputs.append({"path": str(AUTHOR / "MANIFEST.json"), "sha256": author_manifest_hash,
               "scope": "Frozen author manifest"})
(HERE / "source_pins.json").write_text(json.dumps({
    "scope": "Read-only public input integrity; optional web leads not independently audited",
    "records": inputs, "new_web_search_queries": 0, "new_scry_calls": 0, "pdf_downloads": 0,
}, indent=2) + "\n")

ours = json.loads((HERE / "results.json").read_text())
theirs = json.loads((AUTHOR / "RESULTS.json").read_text())
assert ours["status"] == theirs["status"] == "PASS"
assert (HERE / "stdout.txt").read_bytes() == (HERE / "results.json").read_bytes()
assert (HERE / "stderr.txt").read_bytes() == b""
assert ours["spec_sha256"] == digest(AUTHOR / "SPEC.md")
assert ours["pi_lower_grid_numerator"] == theirs["pi_certificate"]["lower_scaled_integer"]
assert ours["pi_upper_grid_numerator"] == theirs["pi_certificate"]["upper_scaled_integer"]
assert ours["combined_gaussian_error_coefficient"] == theirs["combined_Gaussian_loss_coefficient"]
assert theirs["combined_uniform_loss_coefficient"] <= ours["combined_uniform_error_coefficient_overallowance"] < 2**45
field_map = {
    "actual_gaussian_draws": "actual_Gaussian_draws",
    "key_coefficients": "actual_key_draws",
    "error_coefficients": "actual_encryption_error_draws",
    "reduction_gaussian_allowance": "one_reduction_Gaussian_allowance",
    "gaussian_error_coefficient": "Gaussian_loss_coefficient_2Qactual_plus_4TQred",
    "actual_uniform_draws": "actual_uniform_output_count",
    "actual_gaussian_expected_attempt_upper": "reference_expected_proposal_upper",
    "actual_gaussian_worst_attempt_upper": "reference_worst_proposal_cap",
    "actual_gaussian_expected_product_upper": "reference_expected_integer_product_upper",
    "actual_gaussian_worst_product_upper": "reference_worst_integer_product_upper",
    "actual_gaussian_expected_bit_upper": "reference_expected_random_bit_upper",
    "actual_gaussian_worst_bit_upper": "reference_worst_random_bit_upper",
    "key_threshold_table_bytes": "threshold_table_key_bytes",
    "error_threshold_table_bytes": "threshold_table_error_bytes",
}
for our_point, their_point in zip(ours["points"], theirs["workloads"], strict=True):
    for our_field, their_field in field_map.items():
        assert our_point[our_field] == their_point[their_field], (our_field, their_field)

verification = {
    "status": "PASS",
    "author_manifest_sha256": author_manifest_hash,
    "author_artifacts_checked": len(manifest["artifacts"]),
    "author_public_inputs_checked": len(manifest["public_input_files"]),
    "independent_threshold_controls": len(ours["threshold_controls"]),
    "exhaustive_finite_probability_tapes": ours["finite_probability_controls"]["exhaustive_two_attempt_tapes"],
    "author_resource_and_count_fields_compared": 2*len(field_map),
    "pi_endpoints_and_gaussian_ledger_match": True,
    "independent_uniform_overallowance_dominates_author": True,
    "independent_check_exit_code": 0, "stdout_equals_results": True, "stderr_empty": True,
    "random_draws": 0, "cryptographic_executions": 0, "estimator_executions": 0,
    "author_files_mutated": False,
}
(HERE / "verification.json").write_text(json.dumps(verification, indent=2) + "\n")
files = ["REPORT.md", "STATUS.md", "NEXT.md", "check.py", "results.json", "stdout.txt",
         "stderr.txt", "source_pins.json", "verification.json", "seal.py"]
review_manifest = {
    "status": "PASS", "scope": "Independent finite independent-bit sampler specification review",
    "verdict": "Accepted within stated source/math scope; no mathematical correction required",
    "author_manifest_sha256": author_manifest_hash,
    "artifacts": {name: digest(HERE / name) for name in files},
    "execution": "Only deterministic public integer/Fraction and provenance checks; no random or cryptographic output",
}
(HERE / "manifest.json").write_text(json.dumps(review_manifest, indent=2) + "\n")
print(json.dumps({"status": "PASS", "report_sha256": digest(HERE / "REPORT.md"),
                  "manifest_sha256": digest(HERE / "manifest.json"),
                  "verification": verification}, indent=2))
