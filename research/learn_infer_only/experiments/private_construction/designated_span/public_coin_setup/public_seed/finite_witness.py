"""Exhaustive public F_7 arithmetic and finite probability counts, not crypto.

No keys, ciphertexts, CSPRNG, private inputs, native dependencies, or network.
The tiny exponent table is public and deliberately exhaustible.
"""
from collections import Counter
from itertools import product
from fractions import Fraction
import json

P, Q, G = 7, 3, 2
R = 2
qr = {pow(G, b, P) for b in range(Q)}
assert qr == {1, 2, 4}
roots = {}
for B in sorted(qr):
    v = pow(B, (Q + 1) // 2, P)
    actual = {u for u in range(1, P) if u * u % P == B}
    assert actual == {v, -v % P} and len(actual) == 2
    roots[B] = sorted(actual)

def first(tape, accepted):
    return next((i for i, value in enumerate(tape) if value in accepted), None)

def replace_first(tape, accepted, target):
    i = first(tape, accepted)
    out = list(tape)
    if i is not None:
        out[i] = target
    return tuple(out)

tapes_tau = list(product(range(4), repeat=R))
tapes_u = list(product(range(8), repeat=R))
st, su = set(range(Q)), set(range(1, P))

def sampler_count(tapes, accepted):
    push = Counter(replace_first(tape, accepted, u)
                   for u in accepted for tape in tapes)
    assert set(push) == set(tapes)
    assert set(push.values()) == {len(accepted)}
    counts = Counter(None if (i := first(t, accepted)) is None else t[i]
                     for t in tapes)
    assert len({counts[u] for u in accepted}) == 1
    return {"raw_tapes": len(tapes), "failure_tapes": counts[None],
            "tapes_per_accepted_value": counts[next(iter(accepted))],
            "replacement_preimages_per_tape": len(accepted)}

samplers = {"tau": sampler_count(tapes_tau, st),
            "u": sampler_count(tapes_u, su)}

# Exact accepted-value joint law: real (a,tau,u) versus base-IPFE variables.
real = Counter()
for a, tau, u in product(range(Q), range(Q), range(1, P)):
    A, B = pow(G, a, P), u * u % P
    H = A * pow(G, tau, P) % P
    h = (H * pow(B, -1, P) % P, B)
    assert h[0] * h[1] % P == H
    real[(a, A, tau, u, h)] += 1

sim = Counter()
full_tapes = Counter()
completed = 0
for s0, s1, tau in product(range(Q), repeat=3):
    h = (pow(G, s0, P), pow(G, s1, P))
    k = (s0 + s1) % Q
    a = (k - tau) % Q
    A = pow(G, a, P)
    for u in roots[h[1]]:
        sim[(a, A, tau, u, h)] += 1
        for tw, uw in product(tapes_tau, tapes_u):
            tp = replace_first(tw, st, tau)
            up = replace_first(uw, su, u)
            full_tapes[(a, tp, up)] += 1
            ti, ui = first(tp, st), first(up, su)
            if ti is not None and ui is not None:
                B = up[ui] * up[ui] % P
                H = A * pow(G, tp[ti], P) % P
                assert (H * pow(B, -1, P) % P, B) == h
                completed += 1
assert real == sim
assert len(full_tapes) == Q * len(tapes_tau) * len(tapes_u)
assert set(full_tapes.values()) == {18}

# The success-conditioned single-candidate distribution is unbiased;
# selecting among candidates need not preserve it.
failure = 1 - (1 - Fraction(1, 4) ** R) ** 2
assert failure == Fraction(31, 256)
assert Fraction(completed, sum(full_tapes.values())) == 1 - failure
one_identity = Fraction(1, Q)
two_identity = 1 - (1 - one_identity) ** 2
assert two_identity == Fraction(5, 9) and two_identity != one_identity

# Distinct admissible messages for Y=(1,1), even with all recipients exposed.
x0, x1 = (0, 0), (1, 2)
assert x0 != x1 and sum(x0) % Q == sum(x1) % Q
# Incorrect shortcut: deterministically choosing just the subgroup root
# cannot reproduce uniform nonzero field outputs.
canonical_roots = {pow(B, (Q + 1) // 2, P) for B in qr}
assert canonical_roots == qr and len(canonical_roots) != P - 1

report = {
    "status": "all exact public arithmetic checks passed",
    "scope": "finite probability/field witness only; no cryptographic security experiment",
    "parameters": {"p": P, "q": Q, "g": G, "Y": [[1, 1]], "cap": R},
    "roots": roots,
    "accepted_joint_atoms_each_model": sum(real.values()),
    "complete_tape_simulator_random_choices": sum(full_tapes.values()),
    "distinct_real_complete_tape_transcripts": len(full_tapes),
    "simulator_preimages_per_transcript": 18,
    "samplers": samplers,
    "single_candidate_failure_probability": str(failure),
    "accepted_identity_probability": str(one_identity),
    "identity_probability_after_two_candidate_selection": str(two_identity),
    "nonvacuous_pair": [x0, x1],
    "falsified_shortcuts": ["canonical root without sign is uniform",
                            "selected seed retains unselected uniform law"],
}
print(json.dumps(report, indent=2, sort_keys=True))
