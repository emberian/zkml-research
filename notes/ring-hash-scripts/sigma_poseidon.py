"""
sigma-Poseidon: a ring-native sponge over R_q = Z_q[X]/(X^d+1).

Answers the open problem of eprint 2026/1127 Sec. D by REPAIRING THE ARITHMETIZATION
rather than by inventing a new hash. Section D observes that every R_q-POLYNOMIAL map
acts independently on the CRT/NTT slots, so ring-Poseidon is trivially distinguishable.
The gap in that argument: an R_q-CCS *with automorphisms* -- which 2026/1127 itself
introduces (Def. 9), and uses only for constant-checks -- can also express Galois
automorphisms sigma_k : X -> X^k.  Those are NOT slot-local: they permute the slots.
And by Galois descent (verified in galois_span.py), the R_q-span of {sigma_k : k in G}
is ALL of End_{Z_q}(R_q).  So the constraint language already contains every Z_q-linear
map; nothing about "compact arithmetization" forces slot-locality.

The construction is therefore just Poseidon, with the linear layer widened from
"R_q-linear" to "Z_q-linear expressed in the sigma basis".

DESIGN CONDITIONS (all machine-checked by validate(), none folklore):
  C1  gcd(alpha, q^tau - 1) = 1        S-box permutes R_q. STRICTLY STRONGER than the
                                       field condition gcd(alpha, q-1) = 1.
  C2  each sigma-layer invertible      det(I + D.P_pi) != 0 in slot coordinates.
  C3  <sigma-exponents> surjects onto  G/<q>.  sigma_5 ALONE fails: |<5>| = d/2, so half
                                       the slots never activate. sigma_-1 is REQUIRED.
  C4  |Cap| = q^(c*d) >= 2^(2*lambda)  sponge capacity bound 2Q^2/|Cap|.
  C5  the round LINEAR LAYER must have multiplicative order (up to scalar) >= t*d-1.
      Poseidon2's criterion (eprint 2020/500 Thm 8) and Out of Oddity (2020/188 Lem 1-2)
      both bite on finite-order linear layers, and a BARE automorphism has order d or 2 --
      measured 4 and 2, both FAILING. The candidate is two steps away from that trap: a
      ring coefficient alone lifts c*sigma_5 to order 1024, and MDS o (I + c*sigma) exceeds
      3000. Real condition, cheap to check: see order_check.py. CHECK IT PER INSTANCE.

COST (constraints in R1CS-over-R_q, one R_q multiplication = one constraint):
  S-box layer   S_alpha per ring element per full round   (alpha=7 -> 4)
  sigma layer   1 constraint + 1 witness per ring element per CHAINED APPLICATION per
                round -- so sigma-support s costs (s-1) per element per round. Do NOT
                default to s=3: see density_repricing.py and the Chaghri note below.
                (the sigma terms in Def. 9 live on the RHS only, so the layer's output
                 must be materialised as a witness before it can enter a multiplicand)
  R_q-MDS       FREE  (folds into the CCS matrices)
  round consts  FREE

⚠ THE KNOWN FAILURE MODE OF THIS EXACT SHAPE -- read before choosing sigma_exps.
Chaghri (FHE-friendly cipher over F_{2^63}) used a round function AK o M o B o G with
G a power map, M a 3x3 MDS, and B(x) = c1*x^(2^3) + c2 -- a SINGLE Frobenius term, i.e.
sigma-support 1. Liu-Sarkar-Wang-Meier-Isobe, "Coefficient Grouping: Breaking Chaghri and
More" (eprint 2022/991) break the full 8 rounds in 2^38 data and time, reaching 13.5
rounds: "the vulnerability of Chaghri exists in the usage of a SPARSE affine transform
(an F_2-linearized affine polynomial)". Their fix is a DENSER one, B'(x) = c1'x + c2'x^(2^2)
+ c3'x^(2^8) + c4' -- sigma-support 3 -- restoring almost-exponential algebraic degree
growth at "little overhead"; the designers adopted it. Note also "our attacks apply to ANY
choice of M": the MDS layer does NOT rescue a sparse linearized layer.

Two consequences, and they are not the same requirement:
  (i)  DIFFUSION -- measured here (slot_diffusion.py, branch.py): support 1 is dead,
       support 2 hits the <5>-orbit trap, support 3 reaches the structural floor.
  (ii) ALGEBRAIC DEGREE GROWTH -- NOT measured here, and Chaghri is the proof that (i)
       does not imply (ii). Any instantiation owes a coefficient-grouping-style degree
       analysis before it is used.
Both land on "support >= 3", which is exactly {1, sigma_5, sigma_-1} -- the pair already
native to 2026/1127 Definition 9. That is a coincidence worth NOT relying on.

⚠ AND: the Chaghri failure mode is about a linearized polynomial over an EXTENSION field.
At tau = 1 (fully splitting ring) sigma_k carries NO Frobenius twist -- it is a pure
permutation of the d slot coordinates, an F_q-linear permutation matrix -- and the design
is then literally Poseidon over F_q of width t*d with a structured linear layer. This is
the FOURTH independent reason to prefer full splitting; see sbox_law.py for the others.

WHAT THIS IS NOT: the sponge mode reduces "RO" to "P is an ideal permutation".
That P is ideal is a CRYPTANALYTIC HEURISTIC, exactly as for Poseidon, and nothing
here establishes it. See the report for the residual: for tau > 1 the S-box is a power
map over F_{q^tau}, which 2026/1127 flags as open -- NB the marker is fn.11 but
footnote 11 is a bare URL; the substance is the sentence carrying it: "The study
of Poseidon over extension fields is left for now as an open problem."
"""
from math import gcd

# ------------------------------------------------------------------ ring
class Rq:
    def __init__(self, q, d):
        self.q, self.d = q, d
        self.tau = self._ord(q, 2*d)
        self.ell = d // self.tau
    @staticmethod
    def _ord(a, n):
        o, x = 1, a % n
        while x != 1: x = x*a % n; o += 1
        return o
    def zero(self): return [0]*self.d
    def add(self, a, b): return [(x+y) % self.q for x, y in zip(a, b)]
    def mul(self, a, b):
        q, d = self.q, self.d; r = [0]*d
        for i, x in enumerate(a):
            if not x: continue
            for j, y in enumerate(b):
                e = i+j
                if e < d: r[e] = (r[e] + x*y) % q
                else:     r[e-d] = (r[e-d] - x*y) % q
        return r
    def pow(self, a, n):
        r = [1]+[0]*(self.d-1); b = a[:]
        while n:
            if n & 1: r = self.mul(r, b)
            b = self.mul(b, b); n >>= 1
        return r
    def sigma(self, a, k):
        """sigma_k : X -> X^k, k in (Z/2d)^*."""
        q, d = self.q, self.d; r = [0]*d
        for j, cj in enumerate(a):
            e = (j*k) % (2*d); s = 1
            if e >= d: e -= d; s = -1
            r[e] = (r[e] + s*cj) % q
        return r

# ------------------------------------------------------------------ parameters
class Params:
    def __init__(self, q, d, t, rate, alpha, RF, RP, sigma_exps, sigma_rounds, rc, mds, sc):
        self.R = Rq(q, d)
        self.t, self.rate, self.alpha = t, rate, alpha
        self.RF, self.RP = RF, RP
        self.cap = t - rate
        self.sigma_exps = sigma_exps          # per-round automorphism exponent, len RF+RP
        self.sigma_rounds = sigma_rounds      # set of round indices where sigma is applied
        self.rc, self.mds, self.sc = rc, mds, sc

    def validate(self, lam=128):
        R = self.R; q, d = R.q, R.d; out = []
        # C1
        ok1 = gcd(self.alpha, q**R.tau - 1) == 1
        out.append(("C1 S-box permutes R_q  gcd(a, q^tau-1)=1", ok1,
                    f"tau={R.tau}, gcd={gcd(self.alpha, q**R.tau - 1)}"
                    + ("" if gcd(self.alpha, q-1) != 1 or ok1 else "  <-- FIELD-OK BUT RING-BAD")))
        # C3: do the sigma exponents used generate the full slot permutation group G/<q>?
        N = 2*d
        sub = {pow(q, i, N) for i in range(R.tau)}
        cos, seen = [], set()
        for g in [k for k in range(1, N) if gcd(k, N) == 1]:
            if g in seen: continue
            cs = frozenset((g*s) % N for s in sub); cos.append(cs); seen |= cs
        idx = {x: i for i, cs in enumerate(cos) for x in cs}
        used = {self.sigma_exps[r] for r in self.sigma_rounds}
        gen = {tuple(range(len(cos)))}
        frontier = list(gen)
        gens = [tuple(idx[(next(iter(cs))*k) % N] for cs in cos) for k in used]
        changed = True
        while changed:
            changed = False
            for p in list(gen):
                for g in gens:
                    np_ = tuple(g[p[i]] for i in range(len(cos)))
                    if np_ not in gen: gen.add(np_); changed = True
        ok3 = len(gen) == len(cos)
        out.append(("C3 sigma exps generate G/<q> (all slots)", ok3,
                    f"ell={len(cos)} slots, group generated has order {len(gen)}"))
        # C4
        capbits = self.cap * d * (q.bit_length()-1)
        ok4 = capbits >= 2*lam
        out.append(("C4 capacity  |Cap| = q^(cap*d) >= 2^(2 lambda)", ok4,
                    f"|Cap| ~ 2^{capbits}, need 2^{2*lam}"))
        return out

    def cost_per_ring_element(self):
        S = {3: 2, 5: 3, 7: 4, 11: 5}[self.alpha]      # square-and-multiply chain length
        sbox  = S * (self.RF * self.t + self.RP)
        sig   = len(self.sigma_rounds) * self.t
        return (sbox + sig) / self.rate, sbox, sig

# ------------------------------------------------------------------ permutation
def permutation(P, state):
    R, t = P.R, P.t
    s = list(state)
    nrounds = P.RF + P.RP
    half = P.RF // 2
    for rd in range(nrounds):
        s = [R.add(x, P.rc[rd][i]) for i, x in enumerate(s)]
        full = rd < half or rd >= nrounds - half
        if full: s = [R.pow(x, P.alpha) for x in s]
        else:    s = [R.pow(s[0], P.alpha)] + s[1:]            # partial round
        s = [ _mds_row(R, P.mds, s, i, t) for i in range(t) ]  # R_q-MDS: slot-LOCAL, FREE
        if rd in P.sigma_rounds:                               # Galois layer: slot-MOVING
            k = P.sigma_exps[rd]
            s = [R.add(x, R.mul(P.sc[rd][i], R.sigma(x, k))) for i, x in enumerate(s)]
    return s

def _mds_row(R, mds, s, i, t):
    acc = R.zero()
    for j in range(t): acc = R.add(acc, R.mul(mds[i][j], s[j]))
    return acc

# ------------------------------------------------------------------ sponge
def sponge(P, msg, out_len=1):
    """msg : list of R_q elements (coefficient lists). Padding is [SPONGE-padding]:
       append a 1 ring-element then zeros to a multiple of the rate."""
    R = P.R
    m = list(msg) + [[1]+[0]*(R.d-1)]
    while len(m) % P.rate: m.append(R.zero())
    st = [R.zero() for _ in range(P.t)]
    for blk in range(0, len(m), P.rate):
        for i in range(P.rate): st[i] = R.add(st[i], m[blk+i])
        st = permutation(P, st)
    out = []
    while len(out) < out_len:
        out += st[:P.rate]; st = permutation(P, st)
    return out[:out_len]

# ------------------------------------------------------------------ instance
def frog_like(q=18446744073707454521, d=16, t=9, rate=8, alpha=7, RF=8, RP=22, seed=2026):
    import random
    rng = random.Random(seed)
    nr = RF + RP
    # butterfly schedule, closed under the FULL group: powers of 5, with sigma_-1 injected
    exps = []
    for r in range(nr):
        exps.append((2*d-1) if r % 3 == 2 else pow(5, 1 << ((r // 3) % 4), 2*d))
    sigma_rounds = set(range(nr))                     # conservative: every round
    rc  = [[[rng.randrange(q) for _ in range(d)] for _ in range(t)] for _ in range(nr)]
    mds = [[[rng.randrange(q) for _ in range(d)] for _ in range(t)] for _ in range(t)]
    sc  = [[[rng.randrange(q) for _ in range(d)] for _ in range(t)] for _ in range(nr)]
    return Params(q, d, t, rate, alpha, RF, RP, exps, sigma_rounds, rc, mds, sc)

def pick_modulus(d=16, tau=4, alpha=7, near=2**64):
    """Smallest prime >= near with inertia degree tau AND a permutive S-box exponent."""
    import sympy
    from math import gcd
    p = sympy.nextprime(near)
    while True:
        if Rq(p, d).tau == tau and gcd(alpha, p**tau - 1) == 1:
            return p
        p = sympy.nextprime(p)

if __name__ == "__main__":
    P = frog_like()
    print("sigma-Poseidon @ Frog-like ring  q~2^64, d=16, tau=%d, ell=%d slots, t=%d, rate=%d\n"
          % (P.R.tau, P.R.ell, P.t, P.rate))
    for name, ok, note in P.validate():
        print(f"  [{'PASS' if ok else 'FAIL'}] {name:<42} {note}")
    per, sbox, sig = P.cost_per_ring_element()
    print(f"\n  cost: {sbox} S-box + {sig} sigma = {sbox+sig} constraints/permutation")
    print(f"        {per:.1f} constraints per RING element absorbed")
    print(f"        (2026/1127 App C.3 baseline: 716.8)  ->  {716.8/per:.1f}x")
    import random
    rng = random.Random(1)
    m = [[rng.randrange(P.R.q) for _ in range(P.R.d)] for _ in range(3)]
    h = sponge(P, m)
    print(f"\n  test vector  H(3 random R_q elements)[0][:4] = {h[0][:4]}")
    m2 = [r[:] for r in m]; m2[0][0] = (m2[0][0] + 1) % P.R.q
    h2 = sponge(P, m2)
    diff = sum(1 for i in range(P.R.d) if h[0][i] != h2[0][i])
    print(f"  avalanche: one coefficient flipped -> {diff}/{P.R.d} output coefficients change")
