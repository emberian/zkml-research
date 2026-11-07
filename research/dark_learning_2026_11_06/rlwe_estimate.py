"""Lattice-estimator run for the exact RLWE instances of the dark-learning HE helpers (gen 4, decision doc §21).
Secret uniform ternary {-1,0,1}, error uniform on [-8,8], one ring sample per secret (m = n): the registered key
b = -(a s + e), and each return's a_j u + e1 (H2). Run under Sage's python with the estimator on sys.path."""
import json
import sys
sys.path.insert(0, "/srv/lanes/dl-gen4/lattice-estimator")
from estimator import LWE
from estimator import nd as ND
from math import log2, prod

def ntt_primes(bits, count, two_n):
    from sympy import isprime
    out, p = [], ((1 << bits) - 1) // two_n * two_n + 1
    while len(out) < count:
        if isprime(p):
            out.append(p)
        p -= two_n
    return out

res = {}
for name, N, L in (("deployed N=16384 L=4", 16384, 4), ("demo N=8192 L=3", 8192, 3)):
    pr = ntt_primes(61, L + 1, 2 * N)
    Q = prod(pr[:L])
    params = LWE.Parameters(n=N, q=Q, Xs=ND.Uniform(-1, 1), Xe=ND.Uniform(-8, 8), m=N, tag=name)
    out = {"log2_q": round(log2(Q), 2)}
    rough = LWE.estimate.rough(params)
    out["rough"] = {k: round(log2(v["rop"]), 1) for k, v in rough.items()}
    print(name, "rough", out["rough"], flush=True)
    full = LWE.estimate(params, deny_list=("arora-gb", "bkw"), jobs=4)
    out["full"] = {k: round(log2(v["rop"]), 1) for k, v in full.items() if v is not None and "rop" in v}
    print(name, "full", out["full"], flush=True)
    res[name] = out
json.dump(res, open("/srv/lanes/dl-gen4/rlwe_estimate.json", "w"), indent=1)
print("ESTIMATE DONE")
