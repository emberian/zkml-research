"""C19 for initiative 16: the sufficient-statistics learner in a FIXED PUBLIC SUBSPACE, and its falsifier.

2026-11-06. psi(x) = U^T (x, 1) with U a data-independent integer basis: the 15 lowest 2-D DCT-II frequencies of the
8 x 8 digit (u + v <= 4), scaled by 64 and rounded, plus the bias. The state is r x r + r x 10 integers (r = 16)
instead of 65 x 65 + 65 x 10. Exactness is C18's theorem with phi := psi, so the C18 driver runs unchanged.

The falsifier (program C19 / C18 falsifier 2): U computed FROM the data (PCA of D). Deleting d should move U; the
subtraction keeps the old U, so the "deleted" state is not the learner on D \\ {d}. Measured, not argued.
"""
import math

import unlearn_c18 as U

def dct_basis(maxfreq=4, scale=64):
    cols = []
    for u in range(8):
        for v in range(8):
            if u + v <= maxfreq:
                cols.append([round(scale * math.cos(math.pi * (2 * m + 1) * u / 16) *
                                   math.cos(math.pi * (2 * n + 1) * v / 16)) for m in range(8) for n in range(8)])
    Um = [[cols[k][i] for k in range(len(cols))] + [0] for i in range(64)]
    Um.append([0] * len(cols) + [1])
    return Um

def pca_basis(rows, r=15, scale=10 ** 6, iters=60):
    """Top-r principal directions of the pixel covariance of `rows` (power iteration with deflation), rounded."""
    n = len(rows)
    mean = [sum(row[i] for row in rows) / n for i in range(64)]
    C = [[0.0] * 64 for _ in range(64)]
    for row in rows:
        x = [row[i] - mean[i] for i in range(64)]
        for i in range(64):
            xi = x[i]
            if xi:
                Ci = C[i]
                for j in range(64):
                    Ci[j] += xi * x[j]
    vecs = []
    for k in range(r):
        v = [1.0 / 8 + 0.01 * ((i * 7 + k) % 5) for i in range(64)]
        for _ in range(iters):
            w = [sum(C[i][j] * v[j] for j in range(64)) for i in range(64)]
            for u in vecs:
                d = sum(a * b for a, b in zip(w, u))
                w = [a - d * b for a, b in zip(w, u)]
            nrm = math.sqrt(sum(a * a for a in w))
            v = [a / nrm for a in w]
        vecs.append(v)
    Um = [[round(scale * vecs[k][i]) for k in range(r)] + [0] for i in range(64)]
    Um.append([0] * r + [1])
    return Um

def run(RESULTS, run_c18):
    phi = U.Phi("dct-lowfreq-u+v<=4-x64-bias-v1", dct_basis())
    ok = run_c18(phi=phi, label="c19")
    # the data-dependent-subspace falsifier
    tra = U.load("optdigits.tra")
    d = tra[17]
    rest = tra[:17] + tra[18:]
    U_D, U_rest = pca_basis(tra), pca_basis(rest)
    moved = sum(a != b for ra, rb in zip(U_D, U_rest) for a, b in zip(ra, rb))
    phiD, phiR = U.Phi("pca-of-D", U_D), U.Phi("pca-of-D-minus-d", U_rest)
    S_sub = U.fold(tra, phiD)
    U.add_contrib(S_sub, phiD(d), d[64], sign=-1, count=False)        # what subtraction certifies
    S_cmp = U.fold(rest, phiR)                                        # the learner on D \\ {d}
    differs = U.stats_commit(S_sub) != U.stats_commit(S_cmp)
    print(f"[c19] falsifier (U = PCA of D): deleting one record moves {moved} of {len(U_D) * len(U_D[0])} "
          f"basis entries; subtracted state == learner on D \\ d: {not differs} (must be False)")
    RESULTS["c19_pca_falsifier"] = dict(basis_entries_moved=moved, subtracted_equals_retrained=not differs,
                                        bites=moved > 0 and differs)
    return ok and moved > 0 and differs
