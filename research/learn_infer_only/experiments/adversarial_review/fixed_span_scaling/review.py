#!/usr/bin/env python3
"""Independent public linear algebra and fixed-kernel hybrid checks only.

No encrypted benchmark, state recovery, extraction, or author-writing main()
is executed. The only sampled messages below are public toy vectors used to
verify finite probability identities in a group with no hardness claim.
"""
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import product
from pathlib import Path
import importlib.util
import json
import math
import platform
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
TASK = HERE.parents[2]
AUTHOR = TASK / "experiments/private_construction/fixed_span/scaling"
QUERY_DIR = TASK / "experiments/end_to_end/utility/public_queries"
BASE = TASK / "experiments/private_construction/additive_ipfe.py"


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def bareiss_det(matrix):
    a = [list(row) for row in matrix]
    sign, previous = 1, 1
    for j in range(len(a)-1):
        pivot = next(i for i in range(j, len(a)) if a[i][j])
        if pivot != j:
            a[pivot], a[j] = a[j], a[pivot]
            sign = -sign
        value = a[j][j]
        for i in range(j+1, len(a)):
            for k in range(j+1, len(a)):
                numerator = value*a[i][k] - a[i][j]*a[j][k]
                assert numerator % previous == 0
                a[i][k] = numerator // previous
            a[i][j] = 0
        previous = value
    return sign*a[-1][-1]


def rref(matrix, q=None):
    a = [[v % q if q else Fraction(v) for v in row] for row in matrix]
    rows, cols = len(a), len(a[0])
    pivots = []
    for col in range(cols):
        row = len(pivots)
        candidates = [i for i in range(row, rows) if a[i][col]]
        if not candidates:
            continue
        selected = candidates[0]
        a[row], a[selected] = a[selected], a[row]
        inverse = pow(a[row][col], -1, q) if q else 1/a[row][col]
        a[row] = [(v*inverse) % q if q else v*inverse for v in a[row]]
        for i in range(rows):
            if i != row:
                scalar = a[i][col]
                a[i] = [(x-scalar*y) % q if q else x-scalar*y for x, y in zip(a[i], a[row])]
        pivots.append(col)
        if len(pivots) == rows:
            break
    return a, pivots


def mv(matrix, vector, q=None):
    return tuple(sum(x*y for x, y in zip(row, vector)) % q if q else sum(x*y for x, y in zip(row, vector)) for row in matrix)


def basis(matrix, q):
    reduced, pivots = rref(matrix, q)
    d = len(matrix[0])
    free = [j for j in range(d) if j not in pivots]
    L = [[int(i == p) for p in pivots] for i in range(d)]
    N = [[0]*len(free) for _ in range(d)]
    for j, f in enumerate(free):
        N[f][j] = 1
        for row, p in enumerate(pivots):
            N[p][j] = -reduced[row][f] % q
    return L, N, pivots, free


def matrix_review(saved):
    paths = sorted(QUERY_DIR.glob("q*.json"))
    assert len(paths) == 16
    rows = [json.loads(path.read_text()) for path in paths]
    assert all(len(row) == 577 and all(type(v) is int and abs(v) <= 127 for v in row) for row in rows)
    det = bareiss_det([row[:16] for row in rows])
    assert det == saved["pivot_minor_determinant"] == -812032080
    reduced, pivots = rref(rows)
    assert pivots == saved["pivot_columns"] == list(range(16))
    free = list(range(16, 577))
    top = [[-reduced[i][j] for j in free] for i in range(16)]
    serial = [[str(v) for v in row] for row in top]
    basis_hash = sha256(json.dumps(serial, separators=(",", ":")).encode()).hexdigest()
    assert basis_hash == saved["basis"]["top_block_rational_sha256"]
    for j, f in enumerate(free):
        assert all(sum(Fraction(rows[i][p])*top[p][j] for p in range(16)) + rows[i][f] == 0 for i in range(16))
    spec = importlib.util.spec_from_file_location("reference_constants_only", BASE)
    base = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(base)
    q = base.Q
    assert 0 < abs(det) < q and math.gcd(det, q) == 1
    # Independently verify denominator reduction and every column over actual F_q.
    modular = [[(v.numerator*pow(v.denominator, -1, q)) % q for v in row] for row in top]
    for j, f in enumerate(free):
        assert all((sum(rows[i][p]*modular[p][j] for p in range(16)) + rows[i][f]) % q == 0 for i in range(16))
    witness = saved["kernel_witness"]
    assert len(witness) == 577 and any(witness) and all(type(v) is int for v in witness)
    assert not any(witness[32:]) and max(map(abs, witness)) == 3
    assert sum(v*v for v in witness) == 80 and mv(rows, witness) == (0,)*16
    fixture_path = TASK / "experiments/end_to_end/utility/issuer_oracle/vectors/h0-e0001.json"
    fixture = json.loads(fixture_path.read_text())
    assert digest(fixture_path) == saved["public_fixture_shifted_pair"]["baseline_sha256"]
    shifted = [a+b for a, b in zip(fixture, witness)]
    assert len(fixture) == 577 and [min(shifted), max(shifted)] == [-22, 24]
    assert all(-127 <= v <= 127 for v in shifted) and shifted[-1] == fixture[-1]
    assert mv(rows, shifted) == mv(rows, fixture)
    bound = 32*127*max(sum(map(abs, row)) for row in rows)
    assert bound == saved["max_window_score_bound"] == 14219936
    width = math.isqrt(2*bound+1)
    width += int(width*width < 2*bound+1)
    assert width == saved["bsgs"]["baby_entries"] == 5333
    return {"shape": [16, 577], "rank": 16, "kernel_dimension": 561,
            "independent_Bareiss_determinant": det, "rational_basis_sha256": basis_hash,
            "rational_and_actual_field_columns_checked": 561,
            "nonzero_integer_witness_max_abs": 3, "witness_squared_norm": 80,
            "public_fixture_shifted_range": [-22, 24], "bias_preserved": True,
            "encoder_image_membership": "not tested or claimed",
            "window_projection_bound": bound, "baby_step_entries": width,
            "author_LLL_or_main_rerun": False, "old_reference_main_called": False}


def finite_bases():
    matrices = samples = 0
    histogram = Counter()
    for q, d in ((2, 2), (2, 3), (3, 2), (3, 3)):
        for entries in product(range(q), repeat=2*d):
            Y = [list(entries[:d]), list(entries[d:])]
            L, N, pivots, free = basis(Y, q)
            r, k = len(pivots), len(free)
            U = [l+n for l, n in zip(L, N)]
            image = Counter()
            for vector in product(range(q), repeat=d):
                s = mv(U, vector, q)
                image[s] += 1
                keys = mv(Y, s, q)
                assert keys == mv(Y, mv(L, vector[:r], q), q)
                if all(v == 0 for v in mv(Y, s, q)):
                    assert s == mv(N, tuple(s[f] for f in free), q)
                samples += 1
            assert len(image) == q**d and set(image.values()) == {1}
            for j in range(k):
                assert mv(Y, tuple(row[j] for row in N), q) == (0, 0)
            histogram[f"q={q},d={d},rank={r},kernel={k}"] += 1
            matrices += 1
    return {"all_2_by_2_and_2_by_3_matrices_over_F2_F3": matrices,
            "uniform_master_and_exposed_key_cases": samples,
            "rank_histogram": dict(histogram), "includes_zero_and_redundant_rows": True}


Q, P, G = 3, 7, 2
L = ((1,), (0,), (0,))
N = ((-1, -1), (1, 0), (0, 1))
Y = ((1, 1, 1),)


def public_setup(t, aa):
    s = tuple((t*l[0] + sum(n*a for n, a in zip(row, aa))) % Q for l, row in zip(L, N))
    return tuple(pow(G, v, P) for v in s), (t,)


def encrypt(h, x, coins):
    return (pow(G, coins, P),) + tuple(pow(v, coins, P)*pow(G, z, P) % P for v, z in zip(h, x))


def masked(t, B, masks, x):
    result = [B]
    for row, l, z in zip(N, L, x):
        value = pow(B, t*l[0], P)*pow(G, z, P) % P
        for c, n in zip(masks, row):
            value = value*pow(c, n, P) % P
        result.append(value)
    return tuple(result)


def pair(h, keys, history):
    checksum = sum(h)+sum(keys)+sum(sum(c) for c in history)
    left = (checksum % Q, (checksum//Q+len(history)) % Q, len(history) % Q)
    v = ((checksum+1) % Q, (checksum+len(history)+2) % Q)
    shift = mv(N, v, Q)
    right = tuple((a+b) % Q for a, b in zip(left, shift))
    assert mv(Y, left, Q) == mv(Y, right, Q)
    return left, right


def run_strategy(h, keys, coins, boundary, selected=None, mu=0, callback=None):
    history = []
    reached = False
    for rank, r in enumerate(coins, 1):
        # A public common-abort branch, also valid in intermediate mask games.
        if len(history) == 2 and history[-1][1] == 1:
            return 0, reached, True
        choices = pair(h, keys, history)
        if rank == selected:
            ct = callback(choices[mu])
            reached = True
        else:
            ct = encrypt(h, choices[int(rank > boundary)], r)
        history.append(ct)
        if rank == 1 and ct[0] == 1:
            break
    return int((sum(history[-1])+sum(h)) % 2 == 0), reached, False


def adaptive_masks():
    T, k, M = 3, 2, 8
    tapes = tuple(product(range(Q), repeat=T))
    p = []
    for boundary in range(T+1):
        ones = total = 0
        for t, a0, a1 in product(range(Q), repeat=3):
            h, keys = public_setup(t, (a0, a1))
            for coins in tapes:
                z, _, _ = run_strategy(h, keys, coins, boundary)
                ones += z
                total += 1
        p.append(Fraction(ones, total))
    transition_gaps = []
    all_omitted = all_abort = implicit_setup_checks = 0
    for rank in range(1, T+1):
        for ell in range(k):
            probabilities = []
            for random_selected in (False, True):
                twice_ones = total = 0
                for t, a0, a1, b in product(range(Q), repeat=4):
                    aa = (a0, a1)
                    h, keys = public_setup(t, aa)
                    A_unknown = pow(G, aa[ell], P)
                    h_sim = tuple(pow(G, (t*l[0]+sum(row[j]*aa[j] for j in range(k) if j != ell)) % Q, P)
                                  * pow(A_unknown, row[ell], P) % P for l, row in zip(L, N))
                    assert h_sim == h and keys == mv(Y, mv(L, (t,), Q), Q)
                    implicit_setup_checks += 1
                    earlier_values = tuple(product(range(Q), repeat=ell))
                    c_values = range(Q) if random_selected else ((aa[ell]*b) % Q,)
                    for earlier, c, coins, mu in product(earlier_values, c_values, tapes, (0, 1)):
                        B = pow(G, b, P)
                        masks = [pow(G, z, P) for z in earlier] + [pow(G, c, P)] + [pow(B, aa[j], P) for j in range(ell+1, k)]
                        callback = lambda x: masked(t, B, masks, x)
                        z, reached, aborted = run_strategy(h, keys, coins, rank-1, rank, mu, callback)
                        twice_ones += 2*int(z == mu) if reached else 1
                        all_omitted += int(not reached)
                        all_abort += int(aborted)
                        total += 1
                probabilities.append(Fraction(twice_ones, 2*total))
            transition_gaps.append({"request": rank, "mask": ell+1,
                                    "real": str(probabilities[0]), "random": str(probabilities[1]),
                                    "gap": str(probabilities[0]-probabilities[1])})
            if ell == 0:
                assert probabilities[0] == Fraction(1, 2)+(p[rank-1]-p[rank])/2
            else:
                assert probabilities[0] == previous
            previous = probabilities[1]
        assert previous == Fraction(1, 2)
    total_gap = sum((Fraction(item["gap"]) for item in transition_gaps), Fraction())
    assert total_gap == (p[0]-p[-1])/2
    assert abs(total_gap)/M == abs(p[0]-p[-1])/(2*M)
    assert all_omitted > 0 and all_abort > 0
    return {"q": Q, "dimension": 3, "rank": 1, "kernel": k, "T": T, "M": M,
            "endpoint_hybrid_probabilities": list(map(str, p)), "transitions": transition_gaps,
            "signed_transition_sum": str(total_gap), "padded_DDH_gap": str(abs(total_gap)/M),
            "endpoint_gap": str(abs(p[0]-p[-1])), "dummy_padded_ranks": M-T*k,
            "unreached_cases": all_omitted, "common_abort_cases": all_abort,
            "one_unknown_direction_public_setup_checks": implicit_setup_checks,
            "identity_Delta_equals_2M_times_gap": True,
            "scope": "exact public toy-group distribution control, no hardness or recovery claim"}


def snapshots(saved):
    paths = [AUTHOR / name for name in ("GENERAL_FIXED_SPAN.md", "linear_audit.py", "linear_results.json", "linear_stdout.txt")]
    paths += [BASE, TASK / "experiments/end_to_end/utility/issuer_oracle/vectors/h0-e0001.json"]
    paths += [Path(path) for path in saved["query_files_sha256"]]
    for path, expected in saved["query_files_sha256"].items():
        assert digest(Path(path)) == expected
    assert digest(AUTHOR / "linear_audit.py") == saved["script_sha256"]
    return [{"path": str(path), "sha256": digest(path)} for path in paths]


def main():
    saved = json.loads((AUTHOR / "linear_results.json").read_text())
    before = snapshots(saved)
    result = {"classification": "EXECUTED independent general fixed-span proof and public matrix review",
              "command": [sys.executable, "-B", str(Path(__file__).resolve())],
              "python": platform.python_version(), "script_sha256": digest(Path(__file__)),
              "matrix": matrix_review(saved), "finite_bases": finite_bases(),
              "adaptive_masks": adaptive_masks(), "input_hashes_before": before,
              "coefficient_checks": [{"T": T, "k": 561, "M": 1 << (max(1, T*561)-1).bit_length(),
                                      "coefficient": 2 << (max(1, T*561)-1).bit_length()} for T in (1, 384)]}
    assert before == snapshots(saved)
    result["input_hashes_after_equal_before"] = True
    result["accounting"] = {"Scry_queries": 0, "Kagi_queries": 0, "web_queries": 0,
                             "PDF_downloads_or_new_extractions": 0,
                             "encrypted_benchmark_runs": 0, "recovery_or_extraction_experiments": 0}
    text = json.dumps(result, indent=2) + "\n"
    (HERE / "results.json").write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
