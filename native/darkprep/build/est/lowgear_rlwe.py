"""Lattice-estimator run for MP-SPDZ LowGear BGV keys as built (v0.4.4, -S 60, p = 2^61 field):
secret and error centered binomial eta = 1 (FHE_Params Chi(0.7): NewHopeB = round(2 * 0.7^2) = 1), m = N samples,
0-level ciphertext modulus of 312 bits (verbose_he_setup: "Need ciphertext modulus of length 312 and 8192 slots")."""
import json, sys
sys.path.insert(0, "/srv/lanes/dl-gen4/lattice-estimator")
from estimator import LWE
from estimator import nd as ND
from math import log2
res = {}
for N, lq in ((8192, 312), (16384, 314)):
    name = f"N={N} logq={lq}"
    params = LWE.Parameters(n=N, q=2**lq - 1, Xs=ND.CenteredBinomial(1), Xe=ND.CenteredBinomial(1), m=N, tag=name)
    out = {}
    rough = LWE.estimate.rough(params)
    out["rough"] = {k: round(log2(v["rop"]), 1) for k, v in rough.items()}
    print(name, "rough", out["rough"], flush=True)
    full = LWE.estimate(params, deny_list=("arora-gb", "bkw"), jobs=4)
    out["full"] = {k: round(log2(v["rop"]), 1) for k, v in full.items() if v is not None and "rop" in v}
    print(name, "full", out["full"], flush=True)
    res[name] = out
json.dump(res, open("/srv/lanes/dl-gen6-prep/est/lowgear_rlwe.json", "w"), indent=1)
print("ESTIMATE DONE")
