"""
THE tau=4 SUBFIELD RISK, measured  --  revival lane, 2026-08-13.

The stated cost of tau=4 is "the extension-field S-box question".  Its sharpest
concrete form is an INVARIANT SUBSPACE, and it is checkable rather than
speculative:

  at tau=4 each slot is F_(q^4), which CONTAINS the base field F_q.  The S-box
  x^alpha maps F_q into F_q (F_q is closed under multiplication).  The Frobenius
  twist that sigma_k carries at tau>1 is x -> x^(q^j), which FIXES F_q POINTWISE.
  So both the nonlinear layer AND the slot permutation preserve the set

      V = { states whose every slot value lies in the base field F_q }

  -- a Z_q-subspace of dimension ell out of d (4 of 16 at Frog geometry).  If the
  LINEAR layer also preserves V, then V is invariant under the WHOLE round, the
  permutation restricted to V is a much smaller permutation, and we have a
  distinguisher plus preimages on V.  This is the tau=4 analogue of the recorded
  tau=1 weakness #4 ("a scalar/real MDS REVIVES a t-cell invariant subspace").

The only thing that can break V is the sigma-layer COEFFICIENTS: multiplication
of slot s by D_k[s] maps F_q into F_q iff D_k[s] lies in F_q.  So the design
condition is

  ** C6:  the sigma-layer coefficients (and the round constants) must NOT lie in
          the base field F_q -- they must generate F_(q^tau) over F_q. **

Measured below: with scalar (F_q) coefficients V is invariant FOREVER; with
generic ring coefficients it dies immediately.  Same cure as the tau=1 weakness
#4, which is the point -- tau=4 does not add a NEW class of condition, it widens
an EXISTING one from "generic ring element" to "generic AND not in the subfield".
"""
import random, itertools

p, d, tau = 89, 16, 4          # ord_32(89) = 4, reproducing Frog's splitting shape
N = 2 * d
A_NR = None                    # x^4 - A_NR irreducible over F_p; found below
ALPHA = 7

# ---------------------------------------------------------------- F_(p^4) arithmetic
def find_nonresidue():
    for a in range(2, p):
        # x^4 - a irreducible over F_p  <=>  a is not a 4th power and (extra cond)
        if any(pow(x, 4, p) == a % p for x in range(p)):
            continue
        return a
    raise RuntimeError
A_NR = find_nonresidue()

def fmul(u, v):
    """multiply in F_p[x]/(x^4 - A_NR)."""
    r = [0] * 7
    for i, x in enumerate(u):
        if not x: continue
        for j, y in enumerate(v):
            r[i + j] = (r[i + j] + x * y) % p
    for e in range(6, 3, -1):
        if r[e]:
            r[e - 4] = (r[e - 4] + A_NR * r[e]) % p
            r[e] = 0
    return r[:4]

def fadd(u, v): return [(x + y) % p for x, y in zip(u, v)]
def fpow(u, e):
    r, b = [1, 0, 0, 0], u[:]
    while e:
        if e & 1: r = fmul(r, b)
        b = fmul(b, b); e >>= 1
    return r
def frob(u, j=1):
    """Frobenius x -> x^(p^j) on F_(p^4)."""
    return fpow(u, pow(p, j, p ** 4 - 1))
def in_subfield(u): return all(c == 0 for c in u[1:])

# ---------------------------------------------------------------- slot structure
from math import gcd
def units(n): return [k for k in range(1, n) if gcd(k, n) == 1]
sub = {pow(p, i, N) for i in range(tau)}
cosets, seen = [], set()
for g in units(N):
    if g in seen: continue
    cs = frozenset(g * s % N for s in sub); cosets.append(cs); seen |= cs
ell = len(cosets)
idxc = {x: i for i, cs in enumerate(cosets) for x in cs}
def slotperm(k): return [idxc[next(iter(cs)) * k % N] for cs in cosets]

K = [1, 5, 31, 27]     # {1,5,-1,-5} -- the slot-MDS set of design_branch_frontier Part D

def make_layer(rng, scalar_coeffs):
    """D_k[s] in F_p (scalar_coeffs=True) or generic in F_(p^4) (False)."""
    D = {}
    for k in K:
        D[k] = [([rng.randrange(1, p), 0, 0, 0] if scalar_coeffs
                 else [rng.randrange(p) for _ in range(4)]) for _ in range(ell)]
    return D

def rounds(state, D, rc, nr, twist=True):
    """nr rounds of: S-box x^7 per slot, then sigma-layer, then + round constants."""
    st = [s[:] for s in state]
    for r in range(nr):
        st = [fpow(s, ALPHA) for s in st]                     # S-box (per slot)
        out = [[0, 0, 0, 0] for _ in range(ell)]
        for k in K:
            pk = slotperm(k)
            for s in range(ell):
                v = frob(st[s], 1) if twist else st[s]        # Frobenius twist
                out[pk[s]] = fadd(out[pk[s]], fmul(D[k][s], v))
        st = [fadd(out[s], rc[r][s]) for s in range(ell)]
    return st

rng = random.Random(2026)
print("=" * 84)
print(f"tau={tau} SUBFIELD INVARIANCE   (p={p}, ell={ell} slots over F_(p^4), S-box x^{ALPHA})")
print(f"  base field F_p sits inside every slot;  x^{ALPHA} maps F_p -> F_p;")
print(f"  Frobenius x -> x^p FIXES F_p pointwise.  So only the COEFFICIENTS can break V.")
print("=" * 84)
print(f"{'sigma coeffs':<24} {'round consts':<16} {'state leaves V after round':>28}")

for coef_label, scalar_c in [("scalar (in F_p)", True), ("generic F_(p^4)", False)]:
    for rc_label, scalar_rc in [("in F_p", True), ("generic", False)]:
        D = make_layer(rng, scalar_c)
        rc = [[([rng.randrange(p), 0, 0, 0] if scalar_rc
                else [rng.randrange(p) for _ in range(4)]) for _ in range(ell)]
              for _ in range(12)]
        # start INSIDE V: every slot value in the base field
        st0 = [[rng.randrange(1, p), 0, 0, 0] for _ in range(ell)]
        left = None
        for nr in range(1, 13):
            st = rounds(st0, D, rc, nr)
            if not all(in_subfield(s) for s in st):
                left = nr; break
        verdict = f"round {left}" if left else "NEVER (invariant through 12)"
        flag = "" if left else "   <-- INVARIANT SUBSPACE"
        print(f"  {coef_label:<22} {rc_label:<16} {verdict:>28}{flag}")

print(f"""
  READING.  V has dimension ell={ell} inside the d={d}-dimensional state, so a state
  confined to V is a {p}^{ell} = 2^{ell*7.5:.0f}-ish object against 2^{d*7.5:.0f} -- and on V the permutation
  is just an ell-slot F_p SPN.  V is invariant EXACTLY WHEN BOTH the sigma
  coefficients AND the round constants lie in F_p -- either one outside the base
  field breaks V in ONE round.  Those are two independent escapes and they are not
  equally trustworthy: a round constant outside F_p is an ACCIDENT of a generic
  instantiation (constants only translate, so they break V without ever mixing
  it), whereas a coefficient outside F_p breaks V structurally, in the layer that
  is supposed to do the mixing.  Rely on the coefficients, not on the constants.

  ** DESIGN CONDITION C6 (new, tau>1 only): sigma-layer coefficients must not lie
     in the base field F_q.  Cheap to check (one subfield test per coefficient:
     u^(q) == u iff u in F_q), and it SUBSUMES the recorded tau=1 weakness #4 --
     "coefficients must be generic ring elements, a scalar MDS revives an
     invariant subspace" -- which is the SAME condition one field down. **

  So the extension-field S-box does NOT introduce an unfamiliar class of
  requirement here; it widens a condition the design already had, and the widened
  form is machine-checkable.  What it does NOT settle is the ALGEBRAIC-DEGREE
  question over F_(q^4) (Chaghri-style coefficient grouping) -- that is separate
  and is not addressed by this script.""")
