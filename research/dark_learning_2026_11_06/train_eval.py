"""The custodians' evaluation and release rule (gen 6, train lane): the reference the release proof proves.

Under custody the weights stay shared; the eval examples are PUBLIC (test split indices 0..n-1, their images and
labels), so z1 = W1 x is local on shares. Per example t, with label l:

    z1 = W1 x_t                          (public x: linear on shares)
    u1 = trunc(z1, S1, K1); h = SIG[u1]  (the step's own gates; DSIG not needed)
    z2_c = W2[c] . h,  c = 0..10R-1      (secret x secret: the HE matvec on the class rows only)
    o_c = trunc(z2_c, S1, K1)
    s_k = sum_{c = k mod 10} o_c         (linear)
    q_k = trunc(s_l - s_k - 1, KC, KC)   in {-1, 0}: -1 iff s_l <= s_k   (k != l; l public: linear selection)
    ok_t = prod_{k != l} (1 + q_k)       (8 Beaver products)
    C = sum_t ok_t                       -> the ONLY opening of the release

The release is (n, C): the number of the first n public test examples the custodied model classifies strictly
correctly (ties count as wrong). Nothing else leaves custody: no weights, no scores, no per-example predictions.
KC = K1 - S1 + 2 + ceil(log2 R) bounds |s_l - s_k - 1|.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import step_spec as S


def kc(prog, reps):
    return prog.K1 - prog.S1 + 2 + (reps - 1).bit_length()


def correct_one(prog, W1, W2, x, label, reps):
    """ok_t, computed with the gate sequence above (floor shifts; bounds asserted as the MPC needs them)."""
    d = len(x)
    z1 = [sum(W1[i][j] * x[j] for j in range(d) if x[j]) for i in range(d)]
    assert all(abs(v) < 1 << prog.K1 for v in z1)
    u1 = [v >> prog.S1 for v in z1]
    assert all(prog.T_LO <= u < prog.T_LO + 256 for u in u1)
    h = [prog.SIG[u] for u in u1]
    z2 = [sum(a * b for a, b in zip(W2[c], h)) for c in range(10 * reps)]
    assert all(abs(v) < 1 << prog.K1 for v in z2)
    o = [v >> prog.S1 for v in z2]
    s = [sum(o[c] for c in range(10 * reps) if c % 10 == k) for k in range(10)]
    K = kc(prog, reps)
    ok = 1
    for k in range(10):
        if k == label:
            continue
        v = s[label] - s[k] - 1
        assert abs(v) < 1 << K
        ok *= 1 + (v >> K)
    return ok


def release(prog, W1, W2, examples, reps):
    """(n, C) over examples = [(x, label), ...]."""
    return len(examples), sum(correct_one(prog, W1, W2, x, l, reps) for x, l in examples)
