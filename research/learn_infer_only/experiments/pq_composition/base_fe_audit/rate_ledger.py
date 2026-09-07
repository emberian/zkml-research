#!/usr/bin/env python3
"""Exact bookkeeping witnesses, not encryption or a quantum security proof."""
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
# A negligible function need not meet a stretched-exponential target, even
# after a fixed polynomial rescaling of its argument. Work in base-two exponents
# so no huge floating-point values or invented primitive security estimates arise.
rate_witnesses = []
for log_kappa in (32, 64, 128):
    for polynomial_rescale in (1, 2, 4):
        slow_exponent = (polynomial_rescale * log_kappa) ** 2
        target_exponent = 2 ** (log_kappa // 4)
        rate_witnesses.append({"log2_kappa": log_kappa,
            "argument_rescaled_to_kappa_power": polynomial_rescale,
            "minus_log2_slow_negligible": slow_exponent,
            "minus_log2_target_2_to_minus_kappa_quarter": target_exponent,
            "slow_error_exceeds_target": slow_exponent < target_exponent})
assert rate_witnesses[-1]["slow_error_exceeds_target"]

# Literal independent-bit extension: L output bits need L independently keyed
# Boolean FE encryptions. Fix the base ciphertext length to one unit; this
# simply measures the wrapper's unavoidable repetition factor.
output_wrapper = [{"output_bits": 2 ** k, "boolean_ciphertext_copies": 2 ** k,
                   "log2_output_bits": k} for k in (4, 8, 12, 16)]

# Every branch of the static GKP hybrid reduction forwards its one advice
# token to the final distinguisher only; classical sampled data may be copied.
paths = {
    "fhe_single_bit": ["classical_setup_other_components", "embed_one_fhe_challenge", "assemble_classical_view", "consume_rho_once_in_D"],
    "garbling": ["classical_setup_fhe_and_abe", "request_one_real_or_simulated_garbling", "assemble_classical_view", "consume_rho_once_in_D"],
    "abe_hidden_label": ["sample_static_attribute_and_predicate", "choose_unopened_branch", "embed_one_abe_challenge", "assemble_classical_view", "consume_rho_once_in_D"],
    "lwe_joint_block": ["embed_one_classical_lwe_tuple", "simulate_classical_trapdoor_transcript", "assemble_classical_view", "consume_rho_once_in_D"],
}
assert all(path.count("consume_rho_once_in_D") == 1 for path in paths.values())
result = {"schema": "base-fe-bookkeeping-v1", "scope": "Exact scalar/routing bookkeeping only; no cryptographic implementation or machine proof of quantum security",
    "gkp_one_leg_bound": "n*eps_FHE + eps_GC + L*eps_ABE2 + delta_FHE",
    "gkp_static_ind_bound": "2*(n*eps_FHE + eps_GC + L*eps_ABE2 + delta_FHE)",
    "gkp_correctness_bound": "delta_FHE + delta_GC + L*delta_ABE2",
    "rate_counterexamples": rate_witnesses, "independent_boolean_wrapper": output_wrapper,
    "one_advice_reduction_paths": paths}
(HERE / "rate_ledger.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"rate_examples": len(rate_witnesses), "last_rate_example": rate_witnesses[-1],
                  "wrapper_rows": len(output_wrapper), "one_advice_paths": len(paths)}, indent=2))
