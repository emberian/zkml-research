import os
import sys
import json
import math
from fractions import Fraction
from pathlib import Path

here = Path(__file__).resolve().parent
os.environ["DOT_SAGE"] = str(here / "runtime/sage_cache")
os.environ["MPLCONFIGDIR"] = str(here / "runtime/mpl")
sys.dont_write_bytecode = True
sys.path.insert(0, str(here / "runtime/pinned-estimator"))
from sage.all import log
from estimator import LWE, schemes, ND

cost = LWE.primal_usvp(schemes.Kyber512)
bits = float(log(cost["rop"], 2))
# The pinned README quick-start gives 143.8 for this exact default call.
assert round(bits, 1) == 143.8, (bits, repr(cost))
pmf = {x: Fraction(math.comb(40, 20 + x), 2**40) for x in range(-20, 21)}
mass = sum(pmf.values())
mean = sum(x * p for x, p in pmf.items())
variance = sum(x*x*p for x, p in pmf.items()) - mean*mean
assert (mass, mean, variance) == (1, 0, 10)
dist = ND.CenteredBinomial(20)
assert dist.bounds == (-20, 20)
assert abs(float(dist.stddev)**2 - float(variance)) < 1e-12
print(json.dumps({"status": "EXECUTED", "control": "pinned README Kyber512 primal_usvp default",
                  "expected_rounded_log2_rop": 143.8, "observed_log2_rop": bits,
                  "repr": repr(cost), "scope": "estimator environment/regression control, not an attack benchmark",
                  "CBD20_exact_PMF_check": {"formula": "Pr[X=x]=binomial(40,20+x)/2^40 for -20<=x<=20",
                    "mass": str(mass), "mean": str(mean), "variance": str(variance),
                    "support_points": len(pmf), "nonzero_probability": str(1-pmf[0]),
                    "numerical_entropy_bits": -sum(float(p)*math.log2(float(p)) for p in pmf.values())}}, indent=2))
