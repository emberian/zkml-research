"""
GADGET-DECOMPOSITION FEISTEL ("MSIS-Feistel") -- the second candidate, developed.

decomp_direction.py identified the direction and resolved bijectivity on a toy.
This script gives the PRECISE round function, scales the bijectivity check to
full Frog-class parameters (explicit inverse, roundtripped), measures slot
mixing and the additive-differential structure that decides the design, and
prices it in 2026/1127's own accounting.

------------------------------------------------------------------- THE DESIGN
Ring R_q = Z_q[X]/(X^16+1).  Gadget base B = 2^16, K = 4 planes (B^K = 2^64).
State (L, R) in R_q^w x R_q^w, w = 4  (t = 8 ring elements total; sponge rate 7,
capacity 1 element = 1024 bits >= 2*128).

Round r (r = 0..NR-1), with public dense round constants a_{r,i} in R_q and
public dense coefficient tables g, h:

  1. DECOMPOSE (per element i < w):   R_i + a_{r,i}  =  sum_j B^j Y_{i,j},
     planes Y_{i,j} with coefficients in [0,B).       [1 linear row per element;
     the plane norm bound is LatticeFold's own infinity-norm check -- FREE]
  2. MIX (products of adjacent planes, P per element):
         Z_{i,j} = Y_{i,j} * Y_{i,j+1},  j < P.       [P mult rows per element]
  3. FEISTEL:  (L, R)  <-  (R,  L + F_r(R))  where
         F_r(R)_i = sum_{i',j} g_{r,i,i',j} Y_{i',j} + sum_{i',j<P} h_{r,i,i',j} Z_{i',j}
     [FREE: linear in witnessed planes/products; it fuses into the NEXT round's
      decomposition row, so the Feistel add is never materialized on its own]

Cost per round: w * (1 + P) rows.  NR = 16 rounds (>= 14, the HKT
indifferentiability precedent for 2-branch Feistel with ideal round functions,
plus margin over measured diffusion; NO real cryptanalysis exists -- this
number is a target for the attack lane, not a validated margin).

WHY the products are load-bearing and P >= 1 is REQUIRED, not optional:
without them (P = 0) the round function is linear-up-to-carries, and the
additive differential  Delta -> G.gadget(Delta)  passes each round with
probability ~ 1 - c/B; measured below, it survives the FULL 16-round
permutation with overwhelming probability.  P = 0 is BROKEN as an RO.

--------------------------------------------------- THE FUNCTION-NESS OBLIGATION
A sponge permutation must be a FUNCTION of its input.  Base-B decomposition
constrained only by "planes recompose to the value mod q" + "coefficients < B"
pins the planes UNIQUELY iff the integer value V = sum B^j v_j < B^K has
V + q >= B^K, i.e. for all coefficients c >= gamma := B^K - q.  Coefficients
c < gamma admit TWO valid plane vectors (c and c+q), and the prover picks:
each ambiguous coefficient hands a malicious prover a free binary choice OF THE
CHALLENGE -- Fiat-Shamir grinding at zero cost.  gamma is a property of the
MODULUS:

    deployed Frog q = 15912092521325583641:  gamma/q = 0.159  -> ~2.5 free
        challenge bits PER ABSORBED ELEMENT.  Fatal without a canonicality
        gate, and the gate needs per-coefficient range logic that R_q-CCS
        cannot express cheaply (that is Sec. D's own lament).  The deployed
        Frog modulus is Feistel-HOSTILE.
    gadget-friendly q = 2^64 - 59 (largest prime < 2^64): gamma/q = 2^-57.9
        -> a malicious prover must GRIND ~2^54 transcripts to find ONE ambiguous
        coefficient; priced into the ROM bound as Q * 2^-54, NO gate needed.

(The same representative-malleability exists in 2026/1127's OWN App C.4 use of
the MSIS hash for IVC instance compression, at gamma/q = 0.159; whether it is
exploitable there depends on how u_i enters knowledge soundness -- flagged as a
question, not claimed as an attack.)
"""
import random, sympy
from math import gcd, log2

# ----------------------------------------------------------------- parameters
D = 16
B = 1 << 16
K = 4
W = 4          # elements per Feistel branch
P = 2          # plane products per element per round
NR = 16

Q_FROG = 15912092521325583641
Q_GF   = (1 << 64) - 59        # gadget-friendly modulus

assert sympy.isprime(Q_GF), "2^64-59 must be prime"
assert sympy.isprime(Q_FROG)

def ring_ops(q, d=D):
    def add(a, b): return [(x + y) % q for x, y in zip(a, b)]
    def sub(a, b): return [(x - y) % q for x, y in zip(a, b)]
    def mul(a, b):
        r = [0] * d
        for i, x in enumerate(a):
            if not x: continue
            for j, y in enumerate(b):
                e = i + j
                if e < d: r[e] = (r[e] + x * y) % q
                else: r[e - d] = (r[e - d] - x * y) % q
        return r
    return add, sub, mul

def gadget(a, q, base=B, k=K):
    """canonical planes of a ring element (coefficients in [0,q) -> [0,base)^k)."""
    return [[(c >> (16 * j)) & (base - 1) if base == 1 << 16 else (c // base**j) % base
             for c in a] for j in range(k)]

def recompose(planes, q, base=B):
    return [sum(planes[j][i] * base**j for j in range(len(planes))) % q
            for i in range(D)]

class Feistel:
    def __init__(self, q, seed=2026, w=W, p=P, nr=NR, base=B, k=K):
        self.q, self.w, self.p, self.nr, self.base, self.k = q, w, p, nr, base, k
        self.add, self.sub, self.mul = ring_ops(q)
        rng = random.Random(seed)
        rr = lambda: [rng.randrange(q) for _ in range(D)]
        self.a = [[rr() for _ in range(w)] for _ in range(nr)]
        self.g = [[[[rr() for _ in range(k)] for _ in range(w)] for _ in range(w)] for _ in range(nr)]
        self.h = [[[[rr() for _ in range(p)] for _ in range(w)] for _ in range(w)] for _ in range(nr)]

    def F(self, R_, r):
        q, w, p, k = self.q, self.w, self.p, self.k
        planes = [gadget(self.add(R_[i], self.a[r][i]), q, self.base, k) for i in range(w)]
        prods = [[self.mul(planes[i][j], planes[i][j + 1]) for j in range(p)] for i in range(w)]
        out = []
        for i in range(w):
            acc = [0] * D
            for i2 in range(w):
                for j in range(k):
                    acc = self.add(acc, self.mul(self.g[r][i][i2][j], planes[i2][j]))
                for j in range(p):
                    acc = self.add(acc, self.mul(self.h[r][i][i2][j], prods[i2][j]))
            out.append(acc)
        return out

    def perm(self, L, R_, rounds=None):
        for r in range(rounds if rounds is not None else self.nr):
            L, R_ = R_, [self.add(L[i], self.F(R_, r)[i]) for i in range(self.w)]
        return L, R_

    def perm_inv(self, L, R_, rounds=None):
        for r in reversed(range(rounds if rounds is not None else self.nr)):
            L, R_ = [self.sub(R_[i], self.F(L, r)[i]) for i in range(self.w)], L
        return L, R_

# ================================================== (1) bijectivity, full scale
print("=" * 78)
print(f"(1) BIJECTIVITY at full scale: q = 2^64-59, d={D}, w={W}, K={K}, P={P}, {NR} rounds")
print("=" * 78)
F = Feistel(Q_GF)
rng = random.Random(5)
ok = 0
TRIALS = 25
for _ in range(TRIALS):
    L = [[rng.randrange(Q_GF) for _ in range(D)] for _ in range(W)]
    R_ = [[rng.randrange(Q_GF) for _ in range(D)] for _ in range(W)]
    L2, R2 = F.perm(L, R_)
    L3, R3 = F.perm_inv(L2, R2)
    ok += (L3 == L and R3 == R_)
print(f"  explicit inverse roundtrips {ok}/{TRIALS} random full-size states "
      f"({2*W} ring elements = {2*W*D*64} bits of state each)")
print("  (bijectivity is STRUCTURAL -- Feistel inverts for ANY round function --")
print("   verified exhaustively on a toy by the prior lane; here CONSTRUCTIVELY")
print("   at deployment size by exhibiting the inverse.)")

# ================================================== (2) canonicality / gamma
print()
print("=" * 78)
print("(2) FUNCTION-NESS: decomposition ambiguity, deployed Frog vs 2^64-59")
print("=" * 78)
for name, q in [("deployed Frog", Q_FROG), ("gadget-friendly 2^64-59", Q_GF)]:
    gamma = (1 << 64) - q
    frac = gamma / q
    per_elt = D * frac
    print(f"  {name:<26} gamma = 2^64-q = {gamma}"
          f"  gamma/q = {frac:.3g} (2^{log2(frac):.1f})"
          f"  E[ambiguous coeffs/elt] = {per_elt:.3g}")
# constructive two-representation witness at the deployed Frog modulus
c = 12345  # any c < gamma works at Frog
digs1 = [(c >> (16 * j)) & 0xFFFF for j in range(4)]
v2 = c + Q_FROG
digs2 = [(v2 >> (16 * j)) & 0xFFFF for j in range(4)]
r1 = sum(x << (16 * j) for j, x in enumerate(digs1)) % Q_FROG
r2 = sum(x << (16 * j) for j, x in enumerate(digs2)) % Q_FROG
assert r1 == r2 == c and all(0 <= x < B for x in digs1 + digs2) and digs1 != digs2
print(f"\n  constructive check at Frog: coefficient {c} has TWO valid plane vectors")
print(f"    {digs1}  and  {digs2}  -- both recompose to {c} mod q, both pass the")
print(f"    norm check.  A prover chooses; each choice changes the hash output.")
print(f"  at q = 2^64-59 the same freedom needs a coefficient < 59: grinding cost")
print(f"    ~2^{log2(Q_GF/59/D):.0f} per ambiguous coefficient FOUND; ROM-bound term Q*2^-54.")

# ================================================== (3) slot mixing (tau=1 toy)
print()
print("=" * 78)
print("(3) SLOT MIXING, tau=1 toy (q=12289 splits X^16+1; B=16, K=4, w=2, P=2)")
print("=" * 78)
qt, Bt, Kt, wt = 12289, 16, 4, 2
roots = sorted(w for w in range(1, qt) if pow(w, D, qt) == qt - 1)
assert len(roots) == D

def slots(a):
    out = []
    for w_ in roots:
        v = 0
        for c in reversed(a): v = (v * w_ + c) % qt
        out.append(v)
    return out

def unslot(sl):
    A = [[pow(w_, i, qt) for i in range(D)] + [sl[j]] for j, w_ in enumerate(roots)]
    for c in range(D):
        p_ = next(r for r in range(c, D) if A[r][c] % qt)
        A[c], A[p_] = A[p_], A[c]
        inv = pow(A[c][c], qt - 2, qt); A[c] = [v * inv % qt for v in A[c]]
        for r in range(D):
            if r != c and A[r][c]:
                f = A[r][c]; A[r] = [(A[r][k] - f * A[c][k]) % qt for k in range(D + 1)]
    return [A[i][D] for i in range(D)]

Ft = Feistel(qt, seed=7, w=wt, p=2, nr=8, base=Bt, k=Kt)
rng3 = random.Random(11)
for nr in range(1, 7):
    tot = 0; trials = 12
    for _ in range(trials):
        L = [[rng3.randrange(qt) for _ in range(D)] for _ in range(wt)]
        R_ = [[rng3.randrange(qt) for _ in range(D)] for _ in range(wt)]
        sl = slots(R_[0]); j = rng3.randrange(D)
        sl2 = sl[:]; sl2[j] = (sl2[j] + 1) % qt
        R2 = [unslot(sl2)] + [r_[:] for r_ in R_[1:]]
        a1 = Ft.perm(L, R_, rounds=nr); a2 = Ft.perm(L, R2, rounds=nr)
        for half in (0, 1):
            for i in range(wt):
                tot += sum(1 for x, y in zip(slots(a1[half][i]), slots(a2[half][i])) if x != y)
    print(f"  {nr} round(s): mean active output slots = {tot/trials:5.1f} / {2*wt*D}"
          f"   (one input slot flipped; RO ~ {2*wt*D*(1-1/qt):.1f})")

# ================================================== (4) additive differentials
print()
print("=" * 78)
print("(4) ADDITIVE DIFFERENTIALS at full scale (q = 2^64-59) -- why P >= 1")
print("=" * 78)
Delta = [[1 if (i == 0 and c == 0) else 0 for c in range(D)] for i in range(W)]

for p_, label in [(0, "P=0 (no products: linear-mod-carries)"),
                  (2, "P=2 (adjacent-plane products)")]:
    Fp = Feistel(Q_GF, seed=2026, p=p_)
    # reference output difference from one random base state
    rngd = random.Random(77)
    def outdiff(rounds):
        L = [[rngd.randrange(Q_GF) for _ in range(D)] for _ in range(W)]
        R_ = [[rngd.randrange(Q_GF) for _ in range(D)] for _ in range(W)]
        Rd = [Fp.add(R_[i], Delta[i]) for i in range(W)]
        a1 = Fp.perm(L, R_, rounds=rounds); a2 = Fp.perm(L, Rd, rounds=rounds)
        return tuple(tuple(Fp.sub(a2[h][i], a1[h][i])[c] for c in range(D))
                     for h in (0, 1) for i in range(W))
    for rounds in (1, 4, 16):
        ref = outdiff(rounds)
        match = sum(1 for _ in range(40) if outdiff(rounds) == ref)
        print(f"  {label:<40} rounds={rounds:>2}: output diff constant in {match}/40 samples")

print("""
  ^ P=0 propagates a fixed input difference to a FIXED output difference through
    all 16 rounds with probability ~1 - the permutation is trivially
    distinguishable from ideal, hence P >= 1 is a hard requirement.
    P=2 kills the order-1 differential.  Order 2 does NOT die at one round:""")

Fp2 = Feistel(Q_GF, seed=2026, p=2)
rngd = random.Random(78)
def F_second_diff():
    y = [[rngd.randrange(Q_GF) for _ in range(D)] for _ in range(W)]
    y1 = [Fp2.add(y[i], Delta[i]) for i in range(W)]
    y2 = [Fp2.add(y1[i], Delta[i]) for i in range(W)]
    f0, f1, f2 = Fp2.F(y, 0), Fp2.F(y1, 0), Fp2.F(y2, 0)
    return tuple(tuple((f2[i][c] - 2 * f1[i][c] + f0[i][c]) % Q_GF for c in range(D))
                 for i in range(W))
ref2 = F_second_diff()
m2 = sum(1 for _ in range(40) if F_second_diff() == ref2)
print(f"  ONE round function F, second-order difference D^2_Delta F: constant in {m2}/40")
print("""  -- the degree-2 plane structure makes the SECOND derivative of a single F
    state-independent (up to carries).  Through multiple rounds the next
    decomposition destroys the polynomial structure, but meet-in-the-middle /
    boomerang constructions from both ends are the obvious attack: FIRST ITEM
    on the attack-me list for this candidate.""")

# ================================================== (5) cost
print()
print("=" * 78)
print("(5) COST in 2026/1127's accounting (R1CS-with-automorphisms rows)")
print("=" * 78)
rows_round = W * (1 + P)
rows_perm = NR * rows_round
rate = 2 * W - 1
per_elt = rows_perm / rate
wit_round = W * K + W * P * (1 + 3)      # planes + products (+ base-B planes of each product)
print(f"  rows/round      = w*(1+P) = {rows_round}")
print(f"  rows/perm       = {NR} rounds * {rows_round} = {rows_perm}")
print(f"  rate            = {rate} ring elements (capacity 1 elt = 1024 bits)")
print(f"  rows / absorbed ring element = {per_elt:.1f}")
print(f"  witness/round   ~ {wit_round} ring elements (planes {W*K}, products {W*P}, product planes {W*P*3})")
print(f"  vs Poseidon-over-Z_q baseline 716.8/elt: {716.8/per_elt:.0f}x cheaper")
print(f"  vs sigma-Poseidon (dense-in-full-rounds) 143.8/elt: {143.8/per_elt:.1f}x cheaper")
print("""
  CAVEATS THAT KEEP THIS HONEST:
  * the norm-check freeness assumes LatticeFold's infinity-norm check covers
    every plane witness at bound B -- true in 2026/1127's own C.4 accounting,
    but the products Z have coefficients < d*B^2, so they are witnessed via
    their OWN base-B planes (priced above as witness, not rows).
  * NR = 16 is a structural precedent (HKT 14-round indifferentiability for
    ideal round functions) + margin, NOT a cryptanalytic result.  Nothing
    about F is an ideal round function.
  * requires the gadget-friendly modulus 2^64-59 (or any q with tiny gamma);
    at the deployed Frog modulus the design is BROKEN-BY-DEFAULT (Sec. 2).""")
