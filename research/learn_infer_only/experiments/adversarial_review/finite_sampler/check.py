#!/usr/bin/env python3
"""Deterministic public interval/probability audit; no sampling or crypto.

The threshold control evaluates specified public integers only. It never reads
random coins or returns a draw. Exact Fraction comparisons decide every check.
"""
from fractions import Fraction as F
from pathlib import Path
from math import factorial
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
AUTHOR = ROOT / "research/learn_infer_only/experiments/private_construction/public_setup_pq"
SPEC_HASH = "2fef91992b092f93f6023a02b0072008a2f4f46e5601ea8fd71eb8d0972e1576"
P, BITS, CAP = 320, 256, 4096
Q = 1 << P


def ceil_fraction(x):
    return -((-x.numerator) // x.denominator)


def floor_fraction(x):
    return x.numerator // x.denominator


def pi_interval():
    # Exact rational sums, with the sign of the first omitted term preserved.
    bounds = {}
    for c in [5, 239]:
        lo = sum((F((-1) ** j, (2*j+1)*c**(2*j+1)) for j in range(80)), F(0))
        bounds[c] = (lo, lo + F(1, 161*c**161))
    lo = 16*bounds[5][0] - 4*bounds[239][1]
    hi = 16*bounds[5][1] - 4*bounds[239][0]
    assert 3 < lo < hi < F(22, 7) < 4
    assert hi-lo < F(1, 1 << 360)
    p_lo, p_hi = floor_fraction(lo*Q), ceil_fraction(hi*Q)
    assert 0 < p_hi-p_lo <= 3
    return p_lo, p_hi


def exact_taylor(x, terms=96):
    # Independent exact-rational evaluation, followed by one outward rounding.
    term = F(1)
    total = term
    for j in range(1, terms+1):
        term *= x / j
        total += (-1)**j * term
    assert terms % 2 == 0 and 0 <= x <= 1
    return total - term*x/(terms+1), total


def interval_control(a, k, p_lo, p_hi):
    sigma = 1 << a
    assert abs(k) < 8*sigma
    u_lo = p_lo*k*k // (256*sigma*sigma)
    u_hi = -((-p_hi*k*k) // (256*sigma*sigma))
    assert 0 <= u_lo <= u_hi <= Q and u_hi-u_lo <= 4
    lows, highs = [Q], [Q]
    for j in range(1, 81):
        lows.append(lows[-1]*u_lo // (j*Q))
        highs.append(min(Q, -((-highs[-1]*u_hi) // (j*Q))))
        assert 0 <= lows[-1] <= highs[-1] <= Q
        assert highs[-1]-lows[-1] <= 8
    lo = max(0, sum(lows[::2])-sum(highs[1::2])-1)
    hi = min(Q, sum(highs[::2])-sum(lows[1::2]))
    assert hi-lo <= 641

    # Verify the initial enclosure against exact polynomials at both exponent
    # endpoints, independent of the interval recurrence used in the spec.
    independent_lo, _ = exact_taylor(F(p_hi*k*k, 256*sigma*sigma*Q))
    _, independent_hi = exact_taylor(F(p_lo*k*k, 256*sigma*sigma*Q))
    assert F(lo, Q) <= independent_lo <= independent_hi <= F(hi, Q)
    # Carry the independent enclosure at 600 bits, avoiding enormous exact
    # denominators after raising to the 256th power.
    QQ = 1 << 600
    fine_lo = max(0, floor_fraction(independent_lo*QQ))
    fine_hi = min(QQ, ceil_fraction(independent_hi*QQ))
    for _ in range(8):
        lo = lo*lo // Q
        hi = min(Q, -((-hi*hi) // Q))
        fine_lo = fine_lo*fine_lo // QQ
        fine_hi = min(QQ, -((-fine_hi*fine_hi) // QQ))
        assert F(lo, Q) <= F(fine_lo, QQ) <= F(fine_hi, QQ) <= F(hi, Q)
    threshold = lo >> (P-BITS)
    assert 0 <= threshold <= 1 << BITS
    assert hi-lo < 1 << 19
    assert 0 <= F(fine_lo, QQ)-F(threshold, 1 << BITS)
    assert F(fine_hi, QQ)-F(threshold, 1 << BITS) < F(2, 1 << BITS)
    return {"a": a, "k": k, "u_width": u_hi-u_lo, "rho_width_units": hi-lo,
            "threshold": str(threshold)}


def point_counts(label, dim, n, a_key, q_bits, flood_exponent, ring):
    d, r, t = 577, 16, 384
    keys, errors = r*dim, t*dim
    actual, red = (r+t)*dim, (d+t)*dim
    gauss_coefficient = 2*actual + 4*t*red
    # Includes a full A even when the challenge supplies A; all d public P
    # entries and two further full d-row mask arrays; a spare target uniform
    # vector. These extras dominate what the one-shot reduction actually draws.
    a_coefficients = dim if ring else dim*n
    uni_actual = a_coefficients + (d-r)*n + t*(n+d)
    uni_red = a_coefficients + 3*d*n + t*(n+d) + dim
    uni_coefficient = 2*uni_actual + 4*t*uni_red
    bit_per_attempt_sum = keys*(a_key+4+BITS) + errors*(10+4+BITS)
    return {
        "label": label, "dimension": dim, "uniform_secret_coefficients": n,
        "key_coefficients": keys, "error_coefficients": errors,
        "actual_gaussian_draws": actual, "reduction_gaussian_allowance": red,
        "gaussian_error_coefficient": gauss_coefficient,
        "actual_uniform_draws": uni_actual, "reduction_uniform_overallowance": uni_red,
        "uniform_error_coefficient": uni_coefficient,
        "actual_gaussian_expected_attempt_upper": 17*actual,
        "actual_gaussian_worst_attempt_upper": CAP*actual,
        "actual_gaussian_expected_product_upper": 179*17*actual,
        "actual_gaussian_worst_product_upper": 179*CAP*actual,
        "actual_gaussian_expected_bit_upper": 17*bit_per_attempt_sum,
        "actual_gaussian_worst_bit_upper": CAP*bit_per_attempt_sum,
        "actual_uniform_worst_bit_upper": 512*(
            (a_coefficients+(d-r)*n+t*n)*q_bits + t*d*(flood_exponent+2)),
        "key_threshold_table_bytes": 32*((1 << (a_key+4))-1),
        "error_threshold_table_bytes": 32*((1 << 14)-1),
    }


def finite_controls():
    # Exhaustive 2-attempt probability law for a public finite weight table.
    # This checks the accepted-law/fallback mixture, independently of Gaussian
    # approximation. It does not implement or draw from the reference sampler.
    weights = [0, 0, 0, 0, 0, 0, 1, 4, 8, 4, 1, 0, 0, 0, 0, 0]
    words = [(v, u) for v in range(16) for u in range(8)]
    counts = [0]*16
    for v1, u1 in words:
        for v2, u2 in words:
            if u1 < weights[v1]:
                counts[v1] += 1
            elif u2 < weights[v2]:
                counts[v2] += 1
            else:
                counts[8] += 1
    alpha = F(sum(weights), 128)
    fail = (1-alpha)**2
    accepted = [F(w, sum(weights)) for w in weights]
    mixture = [(1-fail)*p + (fail if i == 8 else 0) for i, p in enumerate(accepted)]
    assert [F(c, len(words)**2) for c in counts] == mixture
    tv = sum(abs(x-y) for x, y in zip(mixture, accepted))/2
    assert tv == fail*(1-accepted[8]) < fail
    # Lower mass normalization costs removed fraction E/Z, even when the
    # removed mass is concentrated away from the retained support.
    original, retained = [F(7), F(2), F(1)], [F(7), F(1), F(0)]
    Z, Zret = sum(original), sum(retained)
    removed = Z-Zret
    target = [x/Z for x in original]
    rounded = [x/Zret for x in retained]
    assert sum(abs(x-y) for x, y in zip(target, rounded))/2 <= removed/Z
    return {"exhaustive_two_attempt_tapes": len(words)**2,
            "boundary_support_sigma_1": list(range(-7, 8)),
            "fallback_mixture_identity": True, "removed_mass_coupling": True}


def main():
    spec = AUTHOR / "finite_sampler/SPEC.md"
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_HASH
    grid = json.loads((AUTHOR / "ring_candidate/hardness/GRID.json").read_text())
    ring = next(x for x in grid["points"] if x["label"] == "ring_joint_repair_16384")
    scalar = next(x for x in json.loads((AUTHOR / "alternatives/hardness/REBUILT.json").read_text())["rows"]
                  if x["n"] == 16384)
    assert grid["shared"]["d"] == 577 and grid["shared"]["r"] == 16 and grid["shared"]["T"] == 384
    assert ring["N"]*ring["w_ring_samples"] == 1 << 20
    assert ring["sigma_K_width_pow2"] == 25 and ring["sigma_e_width_pow2"] == 10
    assert scalar["l"] == 1 << 18 and scalar["sigma_K_width"] == 1 << 32
    assert scalar["sigma_e_width"] == 1 << 10

    p_lo, p_hi = pi_interval()
    assert factorial(81) > Q
    assert sum((F(7, 10)**j/factorial(j) for j in range(5)), F(0)) > 2
    assert F(17, 16)**16 > 2
    tau = F(3, 1 << 256)
    rho_error = F(2, 1 << 256)
    assert (1-tau)/16-rho_error > F(1, 17)
    assert 16*rho_error/(1-tau) < F(64, 1 << 256)
    assert (641+2)*256-2 < 1 << 19
    assert F(1, 1 << 256) + F(1, 1 << 301) < rho_error
    controls = []
    for a in [0, 10, 25, 32]:
        sigma = 1 << a
        for k in sorted({0, 1, sigma, 2*sigma, 4*sigma, 8*sigma-1}):
            controls.append(interval_control(a, k, p_lo, p_hi))

    points = [point_counts("repaired_ring", 1 << 20, 16384, 25, 289, 247, True),
              point_counts("repaired_scalar", 1 << 18, 16384, 32, 293, 248, False)]
    c_gauss = sum(p["gaussian_error_coefficient"] for p in points)
    c_uniform = sum(p["uniform_error_coefficient"] for p in points)
    assert c_gauss < 1 << 41
    assert c_uniform < 1 << 45
    gauss_loss = c_gauss * F(68, 1 << 256)
    uniform_loss = c_uniform * F(1, 1 << 512)
    assert gauss_loss < F(1, 1 << 208)
    assert uniform_loss < F(1, 1 << 467)
    assert gauss_loss+uniform_loss < F(1, 1 << 207) < F(1, 1 << 192)
    result = {
        "status": "PASS", "scope": "Deterministic public integer/Fraction controls only; no random samples, keys, encryption, estimator, or timing measurements.",
        "spec_sha256": SPEC_HASH,
        "pi_interval_grid_width": p_hi-p_lo, "pi_lower_grid_numerator": str(p_lo),
        "pi_upper_grid_numerator": str(p_hi), "threshold_controls": controls,
        "finite_probability_controls": finite_controls(), "points": points,
        "combined_gaussian_error_coefficient": c_gauss,
        "combined_uniform_error_coefficient_overallowance": c_uniform,
        "gaussian_loss_below_2_minus_208": True, "uniform_loss_below_2_minus_467": True,
        "combined_loss_below_2_minus_207": True,
        "checks_are_not_a_general_machine_proof_or_sampler_implementation": True,
    }
    out = json.dumps(result, indent=2) + "\n"
    (HERE / "results.json").write_text(out)
    print(out, end="")


if __name__ == "__main__":
    main()
