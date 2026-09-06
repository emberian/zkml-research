#!/usr/bin/env python3
"""Exact window arithmetic/source-equation ledger; reads saved real-BFV output.

This does not implement encryption or establish a security estimate. The
deterministic bounds assume the source encryption/scale-round equations and
the pinned sampler's support; real-library evidence remains the saved run.
"""
import hashlib
import itertools
import json
import math
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
Q = 68719403009 * 68719230977 * 137438822401
N = 4096
SUPPORT = 20
FRESH_ERROR = 2 * N * SUPPORT**2 + SUPPORT


def bound_row(width, window, contribution, query, t):
    l1 = width * query
    # pk=(e-a*s,a), Enc(m)=(u*pk0+e1+floor(Qm/t),u*pk1+e2).
    # Each ring product coefficient has N signed products. The final phase
    # relative to ideal Q/t times the answer has <= W*l1*(E+1) error.
    phase_error = window * l1 * (FRESH_ERROR + 1)
    minimum_q_exclusive = 2 * t * phase_error
    score_bound = width * window * contribution * query
    assert 2 * score_bound < t
    assert minimum_q_exclusive < Q
    raw_ct = 2 * N * 3 * 8
    return {
        "width": width, "window": window, "contribution_abs_bound": contribution,
        "query_abs_bound": query, "plaintext_modulus": t,
        "state_coefficient_abs_bound": window * contribution,
        "score_abs_bound": score_bound, "query_l1_bound": l1,
        "fresh_integer_noise_abs_bound": FRESH_ERROR,
        "readout_ideal_phase_error_abs_bound": phase_error,
        "correctness_inequality": f"{minimum_q_exclusive} < {Q}",
        "minimum_ciphertext_modulus_exclusive": minimum_q_exclusive,
        "minimum_integer_modulus_bit_length": (minimum_q_exclusive + 1).bit_length(),
        "sampled_bit_counts_are_not_this_bound": True,
        "nonwrap_product_degree": 2 * (width - 1),
        "live_acc_plus_queue_raw_RNS_bytes": (window + 1) * raw_ct,
        "update_peak_ciphertext_raw_RNS_bytes": (window + 2) * raw_ct,
        "signed_readout_peak_ciphertext_raw_RNS_bytes": (window + 3) * raw_ct,
        "raw_buffer_scope": "ct RNS arrays only; excludes plaintext/key/codec/allocator/test-oracle buffers",
        "security_estimate": None,
        "parameter_frontier_scope": "sufficient-bound threshold in this algebra only, not a necessary condition; no prime selection or security certification",
    }


def check_rounding_and_expiry():
    # floor(Q*m/t) is not additive, even though the ciphertext ring is.
    q, t = 97, 7
    checked = 0
    lo = hi = 0
    for values in itertools.product(range(t), repeat=4):
        total = sum(values)
        defect = sum(q * m // t for m in values) - q * (total % t) // t - q * (total // t)
        assert -3 <= defect <= 0
        lo, hi = min(lo, defect), max(hi, defect)
        checked += 1
    signed_checked = 0
    for values in itertools.product(range(t), repeat=2):
        for weights in itertools.product(range(-3, 4), repeat=2):
            # Avoid floating arithmetic: q*m-t*floor(q*m/t) is in [0,t).
            residual_scaled = sum(w * (t * (q * m // t) - q * m)
                                  for m, w in zip(values, weights))
            assert abs(residual_scaled) <= t * sum(abs(w) for w in weights)
            signed_checked += 1
    # Independent exact group witness, plus the debt from replacing an old
    # group object by another object with the same intended plaintext.
    queue, acc, wrong, debt = [], 0, 0, 11
    for step in range(1, 10001):
        fresh = (17 * step**2 + 3 * step + 5) % q
        acc = (acc + fresh) % q
        wrong = (wrong + fresh) % q
        queue.append(fresh)
        if len(queue) > 8:
            expired = queue.pop(0)
            acc = (acc - expired) % q
            wrong = (wrong - expired - debt) % q
        assert acc == sum(queue) % q
        assert wrong == (acc - max(0, step - 8) * debt) % q
    return {"floor_carry_cases": checked, "floor_carry_extrema": [lo, hi],
            "signed_rounding_bound_cases": signed_checked,
            "exact_group_queue_steps": 10000,
            "replacement_debt_identity": "bad_acc = true_queue_sum - expiries*Z (mod Q)"}


def parse_actual():
    text = (HERE / "sliding_window_wide_final_run.log").read_text()
    cases, params = [], None
    for line in text.splitlines():
        if line.startswith("PARAMS"):
            params = {k: int(v) for k, v in re.findall(r"(N|t|width|window|steps|input_bound)=(\d+)", line)}
        if line.startswith("WINDOW_POSITIVE"):
            values = {k: int(v) for k, v in re.findall(r"(\w+)=(-?\d+)", line)}
            cases.append({**params, **values})
        if line.startswith("WINDOW_BYTES"):
            cases[-1]["bytes"] = {k: int(v) for k, v in re.findall(r"(\w+)=(\d+)", line) if k != "seed"}
        if line.startswith("RERANDOMIZED_EXPIRY_DEBT_FAILURE"):
            cases[-1]["rerandomized_expiry_falsifier"] = {
                k: int(v) for k, v in re.findall(r"(\w+)=(\d+)", line) if k != "seed"}
    assert len(cases) == 3
    assert all(c["exact_queue_equalities"] == 16 for c in cases)
    return cases


def main():
    paths = ["sliding_window_probe/src/main.rs", "sliding_window_probe/Cargo.toml",
             "sliding_window_probe/Cargo.lock", "sliding_window_wide_final_run.log",
             "sliding_window_wide_final_build.log", "window_ledger.py"]
    sources = [Path("/Users/ember/dev/breadstuffs/vendor/fhe-dregg/src/bfv") / s
               for s in ["keys/public_key.rs", "keys/secret_key.rs", "plaintext.rs", "parameters.rs", "ops/mod.rs"]]
    sources += [Path("/Users/ember/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/fhe-util-0.1.1/src/lib.rs")]
    manifest = [{"path": str(p), "sha256": hashlib.sha256(p.read_bytes()).hexdigest(),
                 "bytes": p.stat().st_size} for p in [HERE / s for s in paths] + sources]
    result = {
        "status": "EXECUTED exact algebra plus parsed saved genuine BFV run; not a confidentiality theorem",
        "ciphertext_modulus": Q, "ciphertext_modulus_log2": math.log2(Q),
        "equation_assumptions": [
            "all fresh secret/error/u coefficients have absolute value at most 20",
            "N=4096 negacyclic ring; exact ct group arithmetic; fixed level",
            "fresh phase = floor(Q*m/t) + e mod Q; exact scale-and-round decryption",
            "public fixed readout coefficients; old identical ciphertext expires",
            "authorized inputs satisfy the stated message bounds",
        ],
        "not_established": ["library correctness proof", "post-quantum security bits",
                            "malicious input/queue proof", "scalar-only release", "key absence", "cryptographic forgetting"],
        "algebra_checks": check_rounding_and_expiry(),
        "uniform_horizon_bounds": [bound_row(16, 8, 1, 1, 1032193),
                                   bound_row(577, 128, 127, 127, 4294828033)],
        "actual_BFV_cases": parse_actual(),
        "actual_run_command": "CARGO_TARGET_DIR=research/learn_infer_only/experiments/he_closure_costs/bfv_probe/target cargo run --offline --release --manifest-path research/learn_infer_only/experiments/he_closure_costs/sliding_window_probe/Cargo.toml",
        "log_scope_note": "The generic final PASS line is repeated after the wide run; only the 16-dimensional cases execute expiry falsifiers.",
        "rng_scope": "secret/error/u fixture stream is ChaCha20 seeded by repeated byte; library public uniform a seed uses rand::rng internally, so ciphertext bytes are not cross-run deterministic",
        "manifest": manifest,
    }
    (HERE / "window_results.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ["status", "algebra_checks", "uniform_horizon_bounds", "actual_BFV_cases"]}, indent=2))


if __name__ == "__main__":
    main()
