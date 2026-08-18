"""
FCT-1: CLAASP-MP FALSIFICATION GUARD.

Before CLAASP-MP is pointed at anything of ours, it must reproduce a result
PUBLISHED IN ITS OWN PAPER, and the check must be shown to be capable of
going red.

Source of the expected values: eprint 2026/735 (Bellini, Rachidi, Tiwari),
"CLAASP-MP: An Automated MILP Framework for Monomial Prediction",
Appendix B, Listing 1 -- "Example usage of the monomial prediction model on
SIMON-32".  Local copy: ~/paperbin/claasp-mp-monomial-prediction-2026-735.txt
lines 1688-1721.  Every expected value below is transcribed from that listing
and NOT from CLAASP's own test suite.

Why this matters here specifically: this repo has already shipped a guard row
asserting a number the source paper does not contain (the "21-22 at degree 8"
row, formal-cryptanalysis-pipeline.md sec.8 C1).  So each row below states
where in the paper it came from, and the script ends by DELIBERATELY
FALSIFYING each row to prove the comparison is live.

Run:
  PYTHONPATH=<claasp-mp-src> python fct1_claasp_mp_guard.py
"""
import sys, time

from claasp.ciphers.block_ciphers.simon_block_cipher import SimonBlockCipher
from claasp.cipher_modules.models.milp.milp_models.Gurobi.monomial_prediction \
    import MilpMonomialPredictionModel

PAPER = "eprint 2026/735 App. B, Listing 1 (SIMON-32, number_of_rounds=3)"

rows = []          # (name, got, expected, ok)
def check(name, got, expected):
    ok = (got == expected)
    rows.append((name, got, expected, ok))
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}")
    print(f"         paper : {expected}")
    print(f"         got   : {got}")
    return ok


print("=" * 78)
print("FCT-1  CLAASP-MP falsification guard")
print(f"       expectations transcribed from {PAPER}")
print("=" * 78)

t0 = time.time()
cipher = SimonBlockCipher(number_of_rounds=3)
print(f"\ncipher: {cipher.id}   output bits = {cipher.output_bit_size}")

# ---- row 1: upper bound on the degree of output bit 0.  Paper: "Output = 5"
milp = MilpMonomialPredictionModel(cipher)
ub0 = milp.find_upper_bound_degree_of_specific_output_bit(0)
check("find_upper_bound_degree_of_specific_output_bit(0)", ub0, 5)

# ---- row 2: exact degree of output bit 0.  Paper: "Output = 5"
milp = MilpMonomialPredictionModel(cipher)
ex0 = milp.find_exact_degree_of_specific_output_bit(0)
check("find_exact_degree_of_specific_output_bit(0)", ex0, 5)

# ---- row 3: upper bounds for ALL output bits.
# Paper prints "[5, 5, ..., 5, 5, 3, 3, ..., 3, 3]" -- an elided list.  SIMON-32
# has a 32-bit output, so the paper's shape asserts: first half 5, second half 3.
# We assert the SHAPE the paper states, not a number it does not print.
milp = MilpMonomialPredictionModel(cipher)
uball = milp.find_upper_bound_degree_of_all_output_bits()
check("find_upper_bound_degree_of_all_output_bits() -- paper's stated shape",
      (uball[:16], uball[16:]), ([5] * 16, [3] * 16))

# ---- row 4: exact degree of the superpoly of bit 0 for cube ["p16"].
# Paper: "Output = 2"
milp = MilpMonomialPredictionModel(cipher)
sd = milp.find_exact_degree_of_superpoly_of_specific_output_bit(0, ["p16"])
check("find_exact_degree_of_superpoly_of_specific_output_bit(0, ['p16'])", sd, 2)

# ---- row 5: upper bound on the degree of the cube monomial.  Paper: "Output = 1"
milp = MilpMonomialPredictionModel(cipher)
cm = milp.find_upper_bound_degree_of_cube_monomial_of_specific_output_bit(0, ["p16"])
check("find_upper_bound_degree_of_cube_monomial_of_specific_output_bit(0, ['p16'])",
      cm, 1)

# ---- row 6: the key coefficient.  Paper: "k33*k57 + k50*k57 + k51*k57 + 1"
# The strongest row: a full polynomial, printed unelided in the paper.
milp = MilpMonomialPredictionModel(cipher)
R = milp.get_boolean_polynomial_ring()
kc = milp.find_keycoeff_of_cube_monomial_of_specific_output_bit(0, ["p16"])
check("find_keycoeff_of_cube_monomial_of_specific_output_bit(0, ['p16'])",
      kc, R("k33*k57 + k50*k57 + k51*k57 + 1"))

elapsed = time.time() - t0

# ------------------------------------------------------------------ the guard
print()
print("=" * 78)
print("IS THE GUARD LIVE?  Each row is re-run against a DELIBERATELY WRONG")
print("expectation.  A row that still passes is a dead row and is reported.")
print("=" * 78)
dead = []
for name, got, expected, _ in rows:
    if isinstance(expected, int):
        wrong = expected + 1
    elif isinstance(expected, tuple):
        wrong = ([9] * 16, [3] * 16)
    else:                                  # a polynomial
        wrong = expected + R("k33*k57")    # flip one term
    if got == wrong:
        dead.append(name)
        print(f"  [DEAD] {name} -- passes even against a wrong expectation")
    else:
        print(f"  [LIVE] {name} -- refuses the wrong expectation")

print()
print("=" * 78)
n_pass = sum(1 for *_, ok in rows if ok)
print(f"RESULT: {n_pass}/{len(rows)} paper rows reproduced, "
      f"{len(rows) - len(dead)}/{len(rows)} rows LIVE, in {elapsed:.1f}s")
if dead:
    print(f"  DEAD ROWS: {dead}  -- the guard is not trustworthy.")
    sys.exit(3)
if n_pass != len(rows):
    print("  CLAASP-MP does NOT reproduce its own published example here.")
    print("  Nothing this tool says about our primitive may be quoted.")
    sys.exit(1)
print("  CLAASP-MP reproduces its own published SIMON-32 example exactly, and")
print("  every row is refutable.  The instrument is armed.")
