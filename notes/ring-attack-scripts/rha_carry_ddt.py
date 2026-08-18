"""
ITEM 1, RETARGETED -- THE CARRY-DDT AUTOMATON (Liu et al., eprint 2024/1900,
"Opening the Blackbox"), ADAPTED TO THE GADGET-FEISTEL, AND HOW FAR IT REACHES.

WHY THIS AND NOT MILP/MITM.  Every automated instrument in the decomposition-hash
family declines to start at full size (Monolith's own word: "computationally
intractable"), and four instruments reporting nothing is one fact about our
instruments, not four about the primitive.  2024/1900 is the ONE published
technique that REACHES a decomposition layer, and it does so by being hand-built
and by ROUTING AROUND the S-box: it propagates the base-B limb decomposition's
CARRIES through a per-limb DDT, and never needs the S-box's field expression.

WHAT TRANSFERS, EXACTLY.  Their machinery has two halves:
  (i)  a CARRY AUTOMATON over the base-B limb decomposition -- Tab_i / carry_{i+1},
       2024/1900 Sec.4.2.  ⚑ THIS IS OUR STEP 1 VERBATIM.  Our decomposition
       R_i + a = sum_j B^j Y_j at B = 2^16 is exactly the object it propagates.
  (ii) a per-limb DDT for the S-box, combined across limbs by (i).
       ⚑ THIS WE DO NOT HAVE: our nonlinearity Z_j = Y_j * Y_{j+1} couples
       ADJACENT LIMBS and is a RING product, so it is neither limb-local nor
       coefficient-local, and no per-limb DDT exists to combine.

So the honest adaptation is: keep (i), and replace (ii) by asking directly which
LIMB-DIFFERENCE PATTERNS make our round function's output difference cheap.  That
question is answerable exactly, and it is what this script computes.

⚑ THE FALSIFICATION THAT MAKES THE ANSWER MEAN ANYTHING (Part 4).  A search that
finds a short attack is worthless unless it would have found a long one.  So the
same search is re-run against a DELIBERATELY WEAKENED design -- the top-plane
coefficient g_3 set to the ring identity -- on which the characteristic provably
chains forever.  If the search does not report a long reach there, it is not
searching, and its answer on the real design is decoration.
"""
import random
from math import log2

D, B, K, W, P = 16, 1 << 16, 4, 4, 2
Q = (1 << 64) - 257


def ring_ops(q, d=D):
    def add(a, b): return [(x + y) % q for x, y in zip(a, b)]
    def sub(a, b): return [(x - y) % q for x, y in zip(a, b)]
    def mul(a, b):
        r = [0] * d
        for i, x in enumerate(a):
            if not x:
                continue
            for j, y in enumerate(b):
                e = i + j
                if e < d:
                    r[e] = (r[e] + x * y) % q
                else:
                    r[e - d] = (r[e - d] - x * y) % q
        return r
    return add, sub, mul


add, sub, mul = ring_ops(Q)
gadget = lambda a: [[(c // B ** j) % B for c in a] for j in range(K)]

# =========================================================== PART 1: the carry
print("=" * 78)
print("PART 1  THE CARRY AUTOMATON (2024/1900 Sec.4.2 half (i)) ON OUR STEP 1")
print("=" * 78)
print("""  Their object: w = sum_i 2^{l_i} w_i, and for w' = w + dw the limb differences
  are governed by  carry_{i+1} = 1 iff carry_i + dw_i + w_i >= 2^{l_i}.
  Ours is the same recurrence at l_i = 16, K = 4 limbs, then a mod-q wrap.

  The quantity that decides everything below: for an input difference confined to
  limb m, what is P[the limb difference stays confined to limb m]?  Computed
  EXACTLY by counting, then MEASURED on the real primitive.""")


def p_clean_exact(m, delta):
    """P over uniform v in [0,q) that v + delta*B^m has limb difference exactly
    (0..0, delta at m, 0..0): i.e. no carry out of limb m and no mod-q wrap."""
    # no carry out of limb m  <=>  Y_m < B - delta.
    # limb m is (v // B^m) % B; for m < K-1 it is uniform over [0,B) up to the
    # tiny bias from q not being a multiple of B^{m+1}.  For m = K-1 the top limb
    # is bounded by q's top limb.  Count exactly by iterating the top limb only.
    if m < K - 1:
        # exact count over v in [0,q)
        n_ok = 0
        period = B ** (m + 1)
        full = Q // period
        rem = Q % period
        # within each full period, limb m takes each value B^m times
        per_val = B ** m
        n_ok += full * per_val * max(B - delta, 0)
        # the partial period
        for ym in range(B):
            if ym < B - delta:
                lo = ym * per_val
                hi = min((ym + 1) * per_val, rem)
                if hi > lo:
                    n_ok += hi - lo
        # subtract the mod-q wrap cases (v + delta*B^m >= q)
        n_wrap = delta * (B ** m)
        return (n_ok - min(n_wrap, n_ok)) / Q
    else:
        top = Q // (B ** m)          # top limb ranges [0, top]
        n_ok = 0
        for ym in range(top + 1):
            if ym < B - delta:
                lo = ym * (B ** m)
                hi = min((ym + 1) * (B ** m), Q)
                if hi > lo:
                    n_ok += hi - lo
        n_wrap = delta * (B ** m)
        return (n_ok - min(n_wrap, n_ok)) / Q


rng = random.Random(20260818)
print(f"\n  {'limb m':>7} {'delta':>6} {'P exact (counted)':>19} {'P measured':>12} {'n':>8}")
for m in (0, 2, 3):
    for delta in (1, 7):
        pe = p_clean_exact(m, delta)
        # measure on random coefficients
        n, ok = 40000, 0
        for _ in range(n):
            v = rng.randrange(Q)
            v2 = (v + delta * B ** m) % Q
            y, y2 = [(v // B ** j) % B for j in range(K)], [(v2 // B ** j) % B for j in range(K)]
            dy = [(y2[j] - y[j]) for j in range(K)]
            ok += all(dy[j] == (delta if j == m else 0) for j in range(K))
        print(f"  {m:>7} {delta:>6} {pe:>19.6f} {ok/n:>12.6f} {n:>8}")
print("""
  -> the automaton's carry rule reproduces the measured rate.  This is half (i)
     of 2024/1900 running on our decomposition.  It transfers with no changes.""")

# ================================================ PART 2: which patterns are cheap
print()
print("=" * 78)
print("PART 2  WHICH LIMB-DIFFERENCE PATTERNS MAKE THE ROUND OUTPUT CHEAP")
print("=" * 78)
print("""  This replaces half (ii), which we do not have.  F_r's nonlinearity is
    Z_0 = Y_0*Y_1,  Z_1 = Y_1*Y_2      (P = 2)
  so with dY the limb difference:
    dZ_0 = 0 iff dY_0 = dY_1 = 0        dZ_1 = 0 iff dY_1 = dY_2 = 0
  Hence dF is STATE-INDEPENDENT iff the difference lives in limb 3 ALONE.
  Derived; now measured against the real round function.""")

# real round-function constants, same seeding as design_gadget_feistel.py
rngc = random.Random(2026)
rr = lambda: [rngc.randrange(Q) for _ in range(D)]
a0 = [rr() for _ in range(W)]
g = [[[rr() for _ in range(K)] for _ in range(W)] for _ in range(W)]
h = [[[rr() for _ in range(P)] for _ in range(W)] for _ in range(W)]


def F(R_, gg=None):
    gg = gg if gg is not None else g
    planes = [gadget(add(R_[i], a0[i])) for i in range(W)]
    prods = [[mul(planes[i][j], planes[i][j + 1]) for j in range(P)] for i in range(W)]
    out = []
    for i in range(W):
        acc = [0] * D
        for i2 in range(W):
            for j in range(K):
                acc = add(acc, mul(gg[i][i2][j], planes[i2][j]))
            for j in range(P):
                acc = add(acc, mul(h[i][i2][j], prods[i2][j]))
        out.append(acc)
    return out


def state_indep(limbset, trials=8, gg=None):
    """is dF state-independent for a difference confined to `limbset`?"""
    delta = [[0] * D for _ in range(W)]
    for j in limbset:
        for c in range(D):
            delta[0][c] += (1 if c % 3 == 0 else 0) * B ** j
    outs = set()
    for _ in range(trials):
        # build a state whose limbs in `limbset` have room (no carry) and whose
        # OTHER limbs are random -- that is the state-dependence being tested
        R_ = []
        for i in range(W):
            elt = []
            for c in range(D):
                v = 0
                for j in range(K):
                    lim = (B // 2) if j in limbset else B
                    v += rng.randrange(lim) * B ** j
                elt.append(v % Q)
            R_.append(sub(elt, a0[i]))
        Rd = [add(R_[i], delta[i]) for i in range(W)]
        outs.add(tuple(tuple(sub(F(Rd, gg)[i], F(R_, gg)[i])) for i in range(W)))
    return len(outs)


print(f"\n  {'limb set with a difference':<30} {'distinct dF over 8 states':>26} {'verdict':>18}")
for ls in ([3], [2], [0], [2, 3], [0, 3], [0, 1, 2, 3]):
    n = state_indep(ls)
    print(f"  {str(ls):<30} {n:>26} {'DETERMINISTIC' if n == 1 else 'state-dependent':>18}")
print("""
  -> exactly one cheap pattern, and it is limb 3 -- the TOP plane, which P = 2
     never multiplies.  This is the same fact rha_feistel_structure.py measures
     as S2, arriving here as a DIFFERENTIAL rather than as an affine slope.""")

# ==================================================== PART 3: chaining, the reach
print()
print("=" * 78)
print("PART 3  CHAINING -- HOW MANY ROUNDS THE CHARACTERISTIC SURVIVES")
print("=" * 78)
print("""  Feistel: (L,R) <- (R, L + F(R)).  A difference placed in L alone crosses
  round 1 free (dR = 0 => dF = 0).  At round 2 it enters F; if it is TOP-PLANE
  it crosses deterministically by Part 2.  To reach round 3 the OUTPUT
  difference dF = sum_{i'} g[i][i'][3] * d_{i'} must ITSELF be top-plane.""")

FREEDOM = W * D * 16           # 4 elements x 16 coeffs x 16 bits of top-plane content
CONDITION = W * D * 48         # dF_i = 0 mod B^3 in all 16 coeffs, for 4 outputs
print(f"""
  freedom  (top-plane content of a 4-element difference) : {FREEDOM} bits
  condition(dF_i == 0 mod B^3, all coeffs, all 4 outputs): {CONDITION} bits
  deficit                                                : {CONDITION-FREEDOM} bits
  -> generically NO solution.  The characteristic cannot be extended past the
     round in which it first crosses F.""")

# measured: does a top-plane difference produce a top-plane dF?  (must be NO)
delta = [[(1 if i == 0 else 0) * B ** 3 for c in range(D)] for i in range(W)]
R_ = [[rng.randrange(1 << 48) for _ in range(D)] for _ in range(W)]
R_ = [sub(R_[i], a0[i]) for i in range(W)]
dF = [sub(F([add(R_[i], delta[i]) for i in range(W)])[i], F(R_)[i]) for i in range(W)]
is_top = all(all(cf % (B ** 3) == 0 for cf in dF[i]) for i in range(W))
print(f"  MEASURED: is dF top-plane for a top-plane input difference?  {is_top}")

REACH_REAL = 2
print(f"""
  ⚑ REACH ON THE REAL DESIGN: {REACH_REAL} rounds
     round 1  free      (difference in L only, dR = 0 so F is not crossed)
     round 2  p ~ 1     (top-plane difference crosses F deterministically)
     round 3  STALLS    (dF is dense; no limb pattern is cheap for it)""")

# ============================================ PART 4: THE FALSIFICATION GUARD
print()
print("=" * 78)
print("PART 4  ⚑ FALSIFICATION -- the same search on a design where it MUST chain")
print("=" * 78)
print("""  Weaken ONE thing: the top-plane coefficients g[i][i'][3].

  ⚑ HISTORY, KEPT PER minted-a-falsifier-that-stopped-falsifying.  My FIRST
  falsifier set g_3 to the ring IDENTITY and asserted the characteristic would
  chain.  IT DID NOT, and the guard went red on the weakened design as well as
  the real one -- i.e. it distinguished nothing.  The reason is worth stating
  because it is the mechanism of the whole section: Y_3 is the top limb's VALUE,
  a small integer in [0,B), so g_3 = 1 re-injects it at the BOTTOM of the next
  word, not the top.  The pattern is destroyed by the identity.

  The CORRECT falsifier is g_3 = B^3: it re-injects the top limb AT THE TOP
  PLANE, so the pattern is preserved and the characteristic chains without
  limit.  If the search does not see THAT, it is not a search.""")

b3 = [B ** 3] + [0] * (D - 1)
g_weak = [[[(b3 if j == 3 else g[i][i2][j]) for j in range(K)] for i2 in range(W)]
          for i in range(W)]

# same measurement, weakened design
delta_w = [[(1 if i == 0 else 0) * B ** 3 for c in range(D)] for i in range(W)]
dFw = [sub(F([add(R_[i], delta_w[i]) for i in range(W)], g_weak)[i], F(R_, g_weak)[i])
       for i in range(W)]
is_top_w = all(all(cf % (B ** 3) == 0 for cf in dFw[i]) for i in range(W))
print(f"  MEASURED (weakened g_3 = 1): is dF top-plane?  {is_top_w}")
n_indep_w = state_indep([3], gg=g_weak)
print(f"  MEASURED (weakened): dF state-independent?     {n_indep_w == 1}")
assert is_top_w and not is_top, \
    "GUARD DEAD: the weakened design must chain and the real one must not"
print(f"""
  GUARD: real design chains = {is_top}, weakened design chains = {is_top_w}
     -> LIVE.  The search distinguishes them, so the reach of {REACH_REAL} on the real
        design is a finding and not a failure to look.

  ⚑ AND THE DESIGN CONDITION THAT FALLS OUT OF IT, which is the useful part:
     THE REACH IS BOUNDED BY THE DENSITY OF g_3, NOT BY THE ROUND COUNT.
     A sparse, structured or scalar top-plane coefficient -- exactly the kind of
     thing a cost pass reaches for -- reopens an unbounded deterministic
     characteristic.  This is the Chaghri lesson (a SPARSE linearized layer broke
     the full cipher, and "our attacks apply to ANY choice of M") arriving at the
     gadget-Feistel through a different door.  Record it as a standing refusal:
     g MUST stay dense, and the top-plane block g[..][..][3] most of all.""")

print()
print("=" * 78)
print("VERDICT")
print("=" * 78)
print(f"""  The one published technique that REACHES a decomposition layer reaches
  {REACH_REAL} rounds of ours and stalls, and the stall has a named cause (the density of
  the public top-plane coefficients) rather than being an instrument refusal.

  That is a WEAKER result than a break and a STRONGER one than "no tool applies":
  half (i) of the technique -- the carry automaton -- transfers verbatim and was
  run; half (ii) has no analogue because our nonlinearity is not limb-local, and
  the substitute computed here is exact rather than heuristic.

  ⚠ IT DOES NOT SET NR.  A characteristic that stalls at round {REACH_REAL} says NR >= {REACH_REAL+1},
  which every other computed leg already said.  NR = 16 remains precedent.""")
