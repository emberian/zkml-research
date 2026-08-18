"""
FCT-2b: HOW BLIND is CLAASP-MP's `check_anf_correctness` to the odd-prime
modulus?  FCT-2 saw it return True at num_tests=20 for a mod-251 MODADD whose
ANF was computed mod 2^8.  20 samples is not evidence of blindness -- it could
be luck.  This measures the actual per-bit disagreement rate and the detection
probability, so the claim in the note is a measured number and not a vibe.
"""
from claasp.cipher import Cipher
from claasp.cipher_modules.models.milp.milp_models.Gurobi.monomial_prediction \
    import MilpMonomialPredictionModel

W = 8


def build(modulus):
    c = Cipher("modtrap", "permutation", ["input"], [2 * W], W)
    c.add_round()
    c.add_MODADD_component(["input", "input"],
                           [list(range(W)), list(range(W, 2 * W))], W, modulus)
    c.add_cipher_output_component(["modadd_0_0"], [list(range(W))], W)
    return c


cA, cB = build(1 << W), build(251)

print("=" * 78)
print("FCT-2b  per-output-bit disagreement, mod 2^8 vs mod 251, all 2^16 inputs")
print("=" * 78)
N = 1 << (2 * W)
diff = [0] * W
for a in range(1 << W):
    for b in range(1 << W):
        x = (a << W) | b
        oa, ob = cA.evaluate([x]), cB.evaluate([x])
        d = oa ^ ob
        for k in range(W):
            if (d >> k) & 1:
                diff[k] += 1

print(f"  inputs = {N}")
print(f"  {'bit (lsb=0)':<14}{'disagreements':>15}{'rate':>10}"
      f"{'P(20 samples all agree)':>26}")
for k in range(W - 1, -1, -1):
    r = diff[k] / N
    print(f"  bit {k:<10}{diff[k]:>15}{r:>10.4f}{(1 - r) ** 20:>26.3e}")

msb_rate = diff[W - 1] / N
print()
print(f"  output_bit_index=0 with endian='msb' tests bit {W-1} (the MSB).")
print(f"  its disagreement rate is {msb_rate:.4f}, so a 20-sample check misses")
print(f"  the divergence with probability {(1-msb_rate)**20:.3e}.")

print()
print("=" * 78)
print("Does check_anf_correctness catch it as num_tests grows?  (bit index 0)")
print("=" * 78)
for n in (10, 20, 50, 200, 1000):
    ok = MilpMonomialPredictionModel(build(251)).check_anf_correctness(0, num_tests=n)
    print(f"  num_tests={n:<6} -> {ok}   ({'MISSES the divergence' if ok else 'catches it'})")

print()
print("Control: the same check on the mod-2^8 cipher must stay True.")
for n in (20, 200):
    ok = MilpMonomialPredictionModel(build(1 << W)).check_anf_correctness(0, num_tests=n)
    print(f"  num_tests={n:<6} -> {ok}   ({'as expected' if ok else 'CONTROL BROKEN'})")
