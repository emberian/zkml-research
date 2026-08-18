"""
decidable-by-design: the FreeLunch/regular-sequence boundary, exhibited.

Prints the grevlex leading-monomial structure of the naive per-S-box CICO model
for a full-inverse-layer design (Rescue/RPO/XHash12/Twill shape) and a sparse
1-branch design (Griffin/Arion/XHash8 shape), under a POWER-MAP witness y^a = x.

Result [MEASURED]: both have pairwise-coprime PURE-POWER leading monomials
(LM = y_i^a), so both are FreeLunch systems (Buchberger Prop.1) with ideal degree
prod(alpha_i) known by construction. => 'is there a regular sequence / is D_I
known by construction' is YES for BOTH; it is NOT the discriminator (see the note
sec.1a). Contrast dbd_bobbin.py: the deg-2 inversion witness x*y=1 does NOT give
pure powers and chain-collides.

Reuses helpers (grevlex_LM, builders, P, ALPHA) from dbd_ideal_degree.py.
"""
import time
from sympy import Poly, groebner
exec(open('dbd_ideal_degree.py').read().split('def report')[0])  # grevlex_LM, naive_full, naive_sparse, P, ALPHA

def show(name, builder, t, R):
    eqs, gens, sv = builder(t, R)
    sbox = [e for e in eqs
            if any(e.has(v) for v in sv)
            and Poly(e, *gens, modulus=P).total_degree() >= ALPHA]
    lms = [grevlex_LM(e, gens) for e in sbox]
    supp = [set(i for i, x in enumerate(m) if x > 0) for _, m in lms]
    coprime = all(not (supp[i] & supp[j])
                  for i in range(len(supp)) for j in range(i + 1, len(supp)))
    purepow = all(len(s) == 1 for s in supp)
    print("%-46s vars=%2d  sbox=%2d  coprime=%s  pure_power=%s  D_I=alpha^%d"
          % (name, len(gens), len(sbox), coprime, purepow, len(sbox)))
    print("     leading monomials:", [str(l) for l, _ in lms[:6]])

if __name__ == "__main__":
    for t, R in [(2, 2), (2, 3), (3, 2)]:
        show("FULL inverse layer  (Rescue/RPO/XHash12/Twill) t=%d R=%d" % (t, R),
             naive_full, t, R)
        show("SPARSE 1-branch     (Griffin/Arion/XHash8)     t=%d R=%d" % (t, R),
             naive_sparse, t, R)
        print()
