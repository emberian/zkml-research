"""
FCT-2: does CLAASP's `modulus` field on MODADD reach the MODELS -- and in
particular does it reach CLAASP-MP's monomial-prediction model?

Why the lane cares: our candidate lives over Z_q with q = 2^64-257, an ODD
PRIME.  CLAASP's MODADD component accepts a `modulus` argument.  If the models
honoured it, expressing the gadget-Feistel would be nearly free.

Method
  A. sensitivity controls -- prove the fingerprint/ANF comparison CAN go red:
       A1 same modulus, different WIDTH (8-bit vs 7-bit modadd)
       A2 MODADD vs XOR at the same width
     Both must change the model text.  If they do not, this script has no
     instrument and says so.
  B. the measurement -- width fixed, modulus 2^8 vs the largest 8-bit odd
     prime 251.  Compare (i) the evaluator, (ii) the constraint text,
     (iii) CLAASP-MP's computed ANF, (iv) CLAASP-MP's OWN self-check
     `check_anf_correctness`, which evaluates the cipher and compares.

(iv) is the one that decides whether the tool is merely silent or actively
self-blind: it is the routine whose whole job is to notice this.

Run:  PYTHONPATH=<claasp-mp-src> python fct2_modulus_trap.py
"""
import sys, hashlib

from claasp.cipher import Cipher
from claasp.cipher_modules.models.milp.milp_models.Gurobi.monomial_prediction \
    import MilpMonomialPredictionModel

W = 8


def build(modulus, out_bits=W, op="MODADD"):
    c = Cipher("modtrap", "permutation", ["input"], [2 * W], out_bits)
    c.add_round()
    links, poss = ["input", "input"], [list(range(W)), list(range(W, 2 * W))]
    if op == "MODADD":
        c.add_MODADD_component(links, poss, out_bits, modulus)
        cid = "modadd_0_0"
    else:
        c.add_XOR_component(links, poss, out_bits)
        cid = "xor_0_0"
    c.add_cipher_output_component([cid], [list(range(out_bits))], out_bits)
    return c, cid


def model_text(cipher, cid):
    """The constraint text the component hands the model layers.
    The `description` field is EXCLUDED on purpose: it carries the modulus
    verbatim, so including it would mask exactly what we are testing."""
    comp = cipher.get_component_from_id(cid)
    blobs = []
    for meth in ("sat_constraints", "cp_constraints", "smt_constraints", "cms_constraints"):
        try:
            blobs.append(meth + repr(getattr(comp, meth)()))
        except Exception as e:
            blobs.append(f"{meth}:ERR:{type(e).__name__}")
    return hashlib.sha256("\n".join(blobs).encode()).hexdigest()[:16]


def eval_all(cipher):
    outs = [cipher.evaluate([(a << W) | b])
            for a in range(1 << W) for b in range(1 << W)]
    return hashlib.sha256(repr(outs).encode()).hexdigest()[:16], outs


print("=" * 78)
print("FCT-2  Does CLAASP's MODADD `modulus` reach the models?")
print("=" * 78)

# ------------------------------------------------------- A. sensitivity controls
print("\nA. SENSITIVITY CONTROLS -- the comparison must be able to go red.")
c8, _ = build(1 << W, out_bits=W)
c7, _ = build(1 << (W - 1), out_bits=W - 1)
cx, _ = build(None, out_bits=W, op="XOR")
t8, t7, tx = model_text(c8, "modadd_0_0"), model_text(c7, "modadd_0_0"), model_text(cx, "xor_0_0")
a1 = t8 != t7
a2 = t8 != tx
print(f"  A1 MODADD width 8 vs width 7 : {t8} vs {t7}  differs={a1}")
print(f"  A2 MODADD vs XOR at width 8  : {t8} vs {tx}  differs={a2}")
if not (a1 and a2):
    print("\n  CONTROLS FAILED -- the fingerprint is not sensitive to real")
    print("  semantic change, so it cannot testify about the modulus.  NO VERDICT.")
    sys.exit(2)
print("  controls pass: the fingerprint moves when the component's meaning moves.")

# ---------------------------------------------------------- B. the measurement
print("\nB. THE MEASUREMENT -- width fixed at 8, modulus 2^8 vs 251 (odd prime).")
cA, cidA = build(1 << W)
cB, cidB = build(251)
evA, oA = eval_all(cA)
evB, oB = eval_all(cB)
ndiff = sum(1 for x, y in zip(oA, oB) if x != y)
tA, tB = model_text(cA, cidA), model_text(cB, cidB)
print(f"  (i)  EVALUATOR    : {evA} vs {evB}  differs={evA != evB}"
      f"  ({ndiff}/{len(oA)} inputs disagree)")
print(f"  (ii) MODEL TEXT   : {tA} vs {tB}  differs={tA != tB}")

# (iii) CLAASP-MP's ANF of one output bit
milpA = MilpMonomialPredictionModel(cA)
RA = milpA.get_boolean_polynomial_ring()
anfA = milpA.find_anf_of_specific_output_bit(0)
milpB = MilpMonomialPredictionModel(cB)
anfB = milpB.find_anf_of_specific_output_bit(0)
print(f"  (iii) CLAASP-MP ANF of output bit 0 differs = {anfA != anfB}")
print(f"        mod 2^8 : {str(anfA)[:70]}")
print(f"        mod 251 : {str(anfB)[:70]}")

# (iv) CLAASP-MP's own correctness self-check
okA = MilpMonomialPredictionModel(cA).check_anf_correctness(0, num_tests=20)
okB = MilpMonomialPredictionModel(cB).check_anf_correctness(0, num_tests=20)
print(f"  (iv) check_anf_correctness  mod 2^8 -> {okA}   mod 251 -> {okB}")

print()
print("=" * 78)
if (evA != evB) and (tA == tB) and (anfA == anfB):
    print("VERDICT: the `modulus` field is honoured by the EVALUATOR ONLY.")
    print("  The constraint text is byte-identical and CLAASP-MP returns the")
    print("  IDENTICAL ANF for two components computing different functions.")
    print("  A primitive declared over Z_p, p odd, is SILENTLY MODELLED over")
    print("  Z_{2^n}.  The tool does not refuse -- it answers a question about")
    print("  a DIFFERENT primitive, in the same output format as a correct answer.")
    if okB:
        print()
        print("  AND `check_anf_correctness` returns True for the mod-251 cipher,")
        print("  so the tool's OWN self-check does not catch it either.")
    else:
        print()
        print("  `check_anf_correctness` DOES return False for mod-251: the tool")
        print("  can detect the divergence if the user thinks to ask.")
else:
    print("VERDICT: not the expected pattern -- re-read before quoting.")
    print(f"  evaluator differs={evA != evB}  text differs={tA != tB}  anf differs={anfA != anfB}")
