"""
RE-PRICING after the Chaghri finding. This CORRECTS the 8.9x headline in costmodel.py.

Chaghri's designers chose a SPARSE Frobenius layer for precisely the reason I chose a
sparse sigma layer (eprint 2022/592, quoted in 2022/991):

  "in ZK, to compute x^{2^k}, the intermediate value x^{2^{k-1}} must be computed first,
   and this motivates the choice of a DENSE F2-linearized affine polynomial in Vision.
   However, this is not the case in BGV as x^{2^k} can be directly computed by a Frobenius
   automorphism. Therefore, a SPARSE F2-linearized affine polynomial is a natural choice
   for Chaghri."

and it was broken in 2^38 because "the algebraic degree increases LINEARLY rather than
exponentially" -- with the MDS layer present and irrelevant ("our attacks apply to any
choice of M").

*** THE SELF-CORRECTION ***
Chaghri's premise is that the automorphism is FREE in its cost model (BGV). In MY cost
model it is NOT: each chained sigma application costs 1 constraint + 1 witness per ring
element, so sigma_{5^2} costs 2, sigma_{5^4} costs 4. I am therefore in VISION's regime,
where density is priced and worth paying -- not Chaghri's. My 8.9x headline was computed
at sigma-support 3 with ONE application per round, which is exactly Chaghri's sparse
regime. Respecting the lesson costs real constraints. Here is the honest curve.
"""
import math
S, RF, RP, t, rate, d = 4, 8, 22, 9, 8, 16
base = 716.8; tot_ring = 3479; small_ch, pow_ch = 14208, 416
nrounds = RF + RP

def price(applications_per_elt_per_round, rounds_with_sigma, label):
    sbox = S * (RF*t + RP)
    sig  = applications_per_elt_per_round * rounds_with_sigma * t
    per  = (sbox + sig) / rate
    total = tot_ring/rate*(sbox+sig) + small_ch + pow_ch
    print(f"  {label:<52} {sbox:>4}+{sig:>5} = {sbox+sig:>5}/perm  "
          f"{per:6.1f}/elt  {base/per:5.2f}x")
    return per

print(__doc__)
print(f"  {'sigma-layer density':<52} {'constraints/perm':>22} {'per elt':>9} {'gain':>7}")
print("  " + "-"*94)
price(1, nrounds,  "support 3 {1,s5,s-1}, 1 appl/round  [WAS MY HEADLINE]")
price(1, RF,       "support 3, full rounds only")
price(3, nrounds,  "support 4 butterfly {1,s5,s25,s17}, 3 chained appl")
price(3, RF,       "support 4 butterfly, full rounds only")
price(7, nrounds,  "support 8, 7 chained applications")
price(d-1, nrounds,"support 16 = FULLY DENSE (all of G), 15 chained")
price(d-1, RF,     "fully dense, full rounds only")
print(f"\n  baseline (Poseidon over Z_q, 2026/1127 App C.3): {base:.1f} constraints per ring element")

print("""
HONEST HEADLINE, revised: the defensible range is ~3.9x to ~4.8x, not 8.9x.
  * 8.9x requires sigma-support 3 at one application per round -- Chaghri's exact regime.
  * A butterfly layer (support 4, 3 chained applications) gives 4.8x and reaches the
    structural diffusion floor in 2 rounds (branch.py).
  * A fully dense layer -- the direct analogue of the fix that repaired Chaghri -- gives
    only 1.3x, i.e. it very nearly erases the win.

WHERE THE NUANCE ACTUALLY LIES, and it matters:
Chaghri's failure mechanism is the algebraic degree of an F2-LINEARIZED POLYNOMIAL over an
EXTENSION field. At tau = 1 (fully splitting ring) sigma_k carries NO Frobenius twist -- it
is a pure permutation of the d slot coordinates, an F_q-linear permutation matrix -- so
there is no linearized polynomial and coefficient grouping does not literally apply. What
DOES apply at tau=1 is the ordinary wide-trail requirement on a structured (non-MDS)
linear layer, which is the AES situation, and AES reaches full diffusion in 2 rounds with
a layer that is not full-state MDS. At tau > 1 the Frobenius twists are real and Chaghri
applies directly.

So: this is a FIFTH independent argument for choosing a fully splitting ring, and the
4.8x butterfly figure is defensible at tau=1 and NOT defensible at tau>1 without a
coefficient-grouping-style degree analysis that I have not done.""")
