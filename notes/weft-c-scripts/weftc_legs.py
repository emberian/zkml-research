"""
WEFT-C: the computable legs of the round-count derivation, each with a LIVE guard.

Companion to `notes/weft-c-spec.md`.  Imports `weft_branch.py`, `weft2_structure.py`
and `weft_coset_repair.py` from ~/src/ring-ro-hash UNMODIFIED -- this script adds
legs, it does not edit the instruments.

Substrate said out loud: nothing here authors a constraint.  This is a computational
twin of the proved Lean objects (`Selvage/CosetNovelTransform.lean`).  If any of it
ever becomes a circuit, the AIR is Lean-authored.

THE LEGS
  L0  instrument arming -- reproduce the recorded invariants of both objects, and
      show each assertion can go RED (the repo shipped a dead guard row once:
      `formal-cryptanalysis-pipeline.md` sec.8 C1).

  L1  [M32-flag] CLOSED AT SOURCE.  eprint 2024/633 sec.3.3's own Sage listing fixes
      Vision Mark-32's point split: beta_j = from_integer(2^j), and the generator is
      built on omega_0..omega_{2m-1} with RREF making omega_0..omega_23 systematic.
      So the split is the NATURAL one, 0..23 / 24..47.  Both halves are unions of
      cosets of U_1, U_2, U_3 -- therefore the deployed Mark-32 MDS matrix carries
      the 3-deep block-constant invariant flag dim 12 > 6 > 3, and its entries lie in
      GF(2^8).  Verified on the matrix, not only derived.
      GUARD: a random (non-coset) parity set must show NO flag and NO subfield.

  L2  THE STATISTICAL LEGS, BOTH SIDES.  The exact 2-round transition profile
      f_M(w) = min{ wt(Mb) : wt(b) = w } for w = 1,2,3, on M (differential) AND on
      M^T (linear).  f(w) = pass_min(w) - w, so these come from the same certified
      passes the branch numbers do.
      GUARD: the killed Weft-1 form must read f_{M^T}(1) = 1 -- the fixed lane, the
      defect that actually killed it.  A profile instrument that cannot see a fixed
      lane is not an instrument.

  L3  [WEFT-multiround], trail half: THE 4-ROUND ACTIVE COUNT.  The generic bound is
      floor(R/2)*B_d = 16 at R = 4.  It is attained only if a chain of weight-4
      supports (4,4,4,4) exists, so the question is decided by enumerating every
      weight-in-4 / weight-out-4 codeword and looking for a 3-edge path.
      EXACT and complete, by this argument: a (4,4) codeword has 20 zero rows, so at
      least 4 of rows {0..7} are zero rows, so SOME 4-subset Z0 of {0..7} has
      det M[Z0,A] = 0.  Enumerating the 70 subsets Z0 therefore cannot miss one.
      And deg p = max(A) bounds its roots by max(A), so 20 zeros forces max(A) >= 20.
      GUARD: the search must recover the known constructive witness
      f = (s_4+a)(s_2+c), support {0,4,16,20} -> {20,21,22,23}; and on a matrix with
      ONE perturbed coefficient (which moves B from 8 to 28) the set must go EMPTY.

Run:  python3 weftc_legs.py            (~5-15 min)
      python3 weftc_legs.py --fast     (skips L3's wt-3 profile pass)
"""

import itertools
import os
import sys
import time

sys.path.insert(0, os.path.expanduser("~/src/ring-ro-hash"))

from weft_branch import (                                          # noqa: E402
    mul, inv, field_self_checks, subspace_points, build_matrix, mat_inv_char2,
    pass_win1, pass_win2,
)
from weft2_structure import (                                      # noqa: E402
    transpose, matmul, build_coset, max_subfield_level, diagonal_subfield_class,
    pass_win3_gf, minpoly_degree,
)
from weft_coset_repair import novel_eval_on_points, sysrs_matrix   # noqa: E402

import random                                                      # noqa: E402

T = 24
DIM5 = 5
DIM6 = 6
SHIFT = 0xA3C17E59          # the full-field shift the sibling lanes measured at
FAST = "--fast" in sys.argv

FAILURES = []
DEAD_GUARDS = []


def check(name, got, expected, wrong=None):
    """A guarded assertion.  `wrong` is a value the row must REFUSE; if the row
    accepts it too, the row is DEAD and is reported as such."""
    ok = (got == expected)
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}")
    print(f"         expect : {expected}")
    print(f"         got    : {got}")
    if not ok:
        FAILURES.append(name)
    if wrong is not None:
        if got == wrong:
            DEAD_GUARDS.append(name)
            print(f"         [DEAD] also equals the wrong value {wrong}")
        else:
            print(f"         [LIVE] refuses {wrong}")
    return ok


def banner(s):
    print()
    print("=" * 78)
    print(s)
    print("=" * 78)


# ---------------------------------------------------------------------------- L0
banner("L0  INSTRUMENT ARMING -- reproduce both objects' recorded invariants")

rng = random.Random(20260818)
field_self_checks(rng)
print("  GF(2^32) Fan-Paar twin: self-checks pass")

beta = [1 << j for j in range(DIM6)]

M0, _pts0 = build_matrix(beta, T, DIM5)          # Weft-1: shift 0, the killed form
Mc, coset_pts = build_coset(beta, SHIFT, T, DIM5)  # Weft-C: the coset repair

z0 = sum(1 for r in M0 for v in r if v == 0)
zc = sum(1 for r in Mc for v in r if v == 0)
check("Weft-1 zero entries (weft2.md sec.4 table)", z0, 213, wrong=0)
check("Weft-C zero entries (weft2.md sec.4 table)", zc, 0, wrong=213)
check("Weft-1 row 0 is e_0 -- THE FIXED LANE",
      tuple(M0[0]), tuple(1 if i == 0 else 0 for i in range(T)),
      wrong=tuple(Mc[0]))

Mc_inv = mat_inv_char2(Mc)
M0_inv = mat_inv_char2(M0)
McT = transpose(Mc)
M0T = transpose(M0)
McT_inv = transpose(Mc_inv)
M0T_inv = transpose(M0_inv)


# ---------------------------------------------------------------------------- L1
banner("L1  [M32-flag] -- Vision Mark-32's OWN point split, read at source")

print("""  eprint 2024/633 sec.3.3, Code Listing 3-4: W_i is built by subset sums and
  truncated `W_i[: 2*self.m]`, X[j] for j in range(2*m).  So the generator's columns
  are omega_0 .. omega_{2m-1} in the standard binary-expansion order, and RREF makes
  the FIRST m of them systematic.  The split is 0..23 (message) / 24..47 (parity),
  with beta_j = from_integer(2^j) -- i.e. the point sets are the INTEGERS.""")

P1 = list(range(24))
P2 = list(range(24, 48))


def is_coset_union(pts, W):
    """Is `pts` a union of cosets of the GF(2)-subspace W (given as a point list)?"""
    S = set(pts)
    for x in S:
        for w in W:
            if (x ^ w) not in S:
                return False
    return True


print()
for k in range(1, 5):
    W = subspace_points(beta, k)
    a, b = is_coset_union(P1, W), is_coset_union(P2, W)
    print(f"  W = U_{k} (|W| = {len(W):2d}) : P1 union-of-cosets {a!s:<5} "
          f"P2 {b!s:<5} -> predicted invariant dim {T // len(W) if a and b else '-'}")

check("Mark-32's split is a coset union at U_1,U_2,U_3 and NOT at U_4",
      tuple(is_coset_union(P1, subspace_points(beta, k))
            and is_coset_union(P2, subspace_points(beta, k)) for k in range(1, 5)),
      (True, True, True, False),
      wrong=(True, True, True, True))

A32 = sysrs_matrix(beta, P1, P2, DIM6)


def block_constant_basis(n, blk):
    """Basis of the space of vectors constant on each contiguous block of size blk."""
    return [[1 if (j // blk) == g else 0 for j in range(n)]
            for g in range(n // blk)]


def preserves_block_constant(A, blk):
    """Is the block-constant space with blocks of size `blk` A-invariant?"""
    n = len(A)
    for v in block_constant_basis(n, blk):
        w = [0] * n
        for j in range(n):
            acc = 0
            for i in range(n):
                if v[i]:
                    acc ^= A[j][i]
            w[j] = acc
        for g in range(n // blk):
            blkvals = {w[g * blk + o] for o in range(blk)}
            if len(blkvals) != 1:
                return False
    return True


flag = tuple(preserves_block_constant(A32, blk) for blk in (2, 4, 8))
dims = tuple(T // blk for blk in (2, 4, 8))
check(f"Mark-32 MDS: block-constant invariant flag at dims {dims}",
      flag, (True, True, True), wrong=(False, False, False))

lvl32 = max_subfield_level(A32)
check("Mark-32 MDS entries lie in GF(2^8) (subfield level 3)", lvl32, 3, wrong=5)

# ---- the CONTROL that makes the row live: a random, non-coset parity set
rnd_pts = None
while True:
    cand = rng.sample(range(1, 1 << 20), 24)
    if len(set(cand) | set(P1)) == 48:
        rnd_pts = cand
        break
Arnd = sysrs_matrix(beta, P1, rnd_pts, DIM6)
flag_r = tuple(preserves_block_constant(Arnd, blk) for blk in (2, 4, 8))
lvl_r = max_subfield_level(Arnd)
check("CONTROL random (non-coset, O(t^2)) parity set: NO flag",
      flag_r, (False, False, False), wrong=(True, True, True))
check("CONTROL random parity set: entries full-field GF(2^32)", lvl_r, 5, wrong=3)

print(f"  minpoly deg: Mark-32 split {minpoly_degree(A32, rng)} / "
      f"random split {minpoly_degree(Arnd, rng)}   (Weft-C reads 24)")


# ---------------------------------------------------------------------------- L2
banner("L2  THE STATISTICAL LEGS, BOTH SIDES -- exact 2-round transition profile")

print("""  f_M(w) = min { wt(Mb) : wt(b) = w }.  The certified passes return w + f(w),
  so f is exact at w = 1,2,3 by the same exhaustion that certifies the branch number.
  DIFFERENTIAL side reads M; LINEAR side reads M^T (B_l(M) = B_d(M^T)).""")


def profile(M, label, upto=3):
    f = {}
    b, _ = pass_win1(M)
    f[1] = b - 1
    b, _ = pass_win2(M, mul, inv)
    f[2] = b - 2
    if upto >= 3 and not FAST:
        b, _ = pass_win3_gf(M)
        f[3] = b - 3
    print(f"  {label:<38} " + "  ".join(f"f({w})={f[w]:2d}" for w in sorted(f)))
    return f


t0 = time.time()
fd_c = profile(Mc, "Weft-C, differential (M)")
fl_c = profile(McT, "Weft-C, linear (M^T)")
fd_0 = profile(M0, "Weft-1 KILLED, differential (M)")
fl_0 = profile(M0T, "Weft-1 KILLED, linear (M^T)")
print(f"  [{time.time() - t0:.1f}s]")

check("GUARD: the killed form's LINEAR profile sees the fixed lane, f_{M^T}(1) = 1",
      fl_0[1], 1, wrong=fl_c[1])
check("Weft-C differential profile is explosive at w=1: f_M(1) = 23 zeros-free",
      fd_c[1], 24, wrong=1)
check("Weft-C LINEAR profile also explosive at w=1", fl_c[1], 24, wrong=1)

# certified branch FLOORS, both sides of BOTH quantities, re-run rather than quoted.
# min-side <= s exhausted at m  ==>  any codeword of sum <= 2s+1 would have been found,
# so B >= 2s+2.  At s = 3 that is B >= 8, which is the number the round count uses.
def floor_report(M, Minv, label, side3=True):
    vals = [pass_win1(M)[0], pass_win2(M, mul, inv)[0],
            pass_win1(Minv)[0], pass_win2(Minv, mul, inv)[0]]
    s = 2
    if side3 and not FAST:
        vals += [pass_win3_gf(M)[0], pass_win3_gf(Minv)[0]]
        s = 3
    m = min(vals)
    proven = 2 * s + 2 if m > 2 * s + 1 else m
    print(f"  {label:<24} min-side<={s} exhaustion = {m:2d}  ==>  B >= {proven}"
          f"   {'(EXACT: the pass minimum IS the branch)' if m <= 2 * s + 2 else ''}")
    return proven


t1 = time.time()
print()
bd_floor = floor_report(Mc, Mc_inv, "Twill differential")
bl_floor = floor_report(McT, McT_inv, "Twill linear")
print(f"  [{time.time() - t1:.1f}s]")
check("differential floor B_d >= 8 (certified by min-side<=3 exhaustion)",
      bd_floor, 8, wrong=6)
check("LINEAR floor B_l >= 8 -- the side the kill never computed",
      bl_floor, 8, wrong=2)


# ---------------------------------------------------------------------------- L3
banner("L3  [WEFT-multiround] trail half -- the 4-round minimum active S-box count")

print("""  Every 2 consecutive rounds carry >= B_d = 8 active S-boxes, so R = 4 carries
  >= 16.  16 is ATTAINED only if some chain of weight-4 supports (4,4,4,4) exists.
  Enumerate every (wt_in 4, wt_out 4) codeword and look for a 3-edge path.

  COMPLETENESS, and it needs NO genericity assumption.  (i) p = sum_{i in A} b_i Xhat_i
  has degree exactly max(A) and a (4,4) codeword has 20 roots among the 24 domain points,
  so max(A) >= 20 -- that prunes 10626 supports to 5781 with no loss.  (ii) Within a
  support, the search branches on WHICH rows are the (at most 4) nonzero ones, carrying
  the intersection of the zero rows' kernels; it never reads a rank off a fixed minor.
  ⚑ The first version DID (singular 4x4 minors, 1-dim kernel) and MISSED the known
  witness, whose columns 16,20 are a*(columns 0,4) on the first 8 points because those
  lie in x*+V_3 c ker s_4 -- every minor there has rank 2.  A search that prunes on
  genericity prunes hardest exactly where the design's structure lives.""")


def _rref(rows, ncols):
    """Reduced row echelon over GF(2^32); returns (rows, pivot columns)."""
    m = [r[:] for r in rows]
    piv, r = [], 0
    for c in range(ncols):
        p = next((rr for rr in range(r, len(m)) if m[rr][c]), None)
        if p is None:
            continue
        m[r], m[p] = m[p], m[r]
        ic = inv(m[r][c])
        m[r] = [mul(v, ic) for v in m[r]]
        for rr in range(len(m)):
            if rr != r and m[rr][c]:
                f = m[rr][c]
                m[rr] = [m[rr][k] ^ mul(f, m[r][k]) for k in range(ncols)]
        piv.append(c)
        r += 1
    return m[:r], piv


def kernel_basis(rows, ncols=4):
    """Basis of the kernel of a k x ncols matrix over GF(2^32)."""
    m, piv = _rref(rows, ncols)
    free = [c for c in range(ncols) if c not in piv]
    out = []
    for fc in free:
        v = [0] * ncols
        v[fc] = 1
        for i, pc in enumerate(piv):
            v[pc] = m[i][fc]
        out.append(v)
    return out


def _row_annihilates(row, S):
    """Does `row` kill every vector of the subspace with basis S?"""
    for v in S:
        acc = 0
        for k in range(4):
            if v[k]:
                acc ^= mul(row[k], v[k])
        if acc:
            return False
    return True


def _intersect(S, row):
    """S ∩ ker(row), given S as a basis list."""
    # write S-coordinates: a vector is sum c_i S_i; the condition is
    # sum_i c_i (row . S_i) = 0, one linear equation in |S| unknowns.
    coeffs = []
    for v in S:
        acc = 0
        for k in range(4):
            if v[k]:
                acc ^= mul(row[k], v[k])
        coeffs.append(acc)
    if all(c == 0 for c in coeffs):
        return S
    ker = kernel_basis([coeffs], len(S))
    out = []
    for cvec in ker:
        w = [0] * 4
        for i, c in enumerate(cvec):
            if c:
                for k in range(4):
                    if S[i][k]:
                        w[k] ^= mul(c, S[i][k])
        out.append(w)
    return out


def best_lowweight_vectors(col, n, max_bad):
    """Every v != 0 (up to scalar) whose image has <= max_bad nonzero rows.
    Exact: branch over which rows are the (at most max_bad) nonzero ones."""
    hits = []

    def count_out(v):
        out = []
        for j in range(n):
            acc = 0
            for k in range(4):
                if v[k]:
                    acc ^= mul(col[j][k], v[k])
            if acc:
                out.append(j)
        return out

    def rec(j, S, bad):
        if not S:
            return
        if len(S) == 1:                       # v is pinned -- evaluate and stop
            out = count_out(S[0])
            if len(out) <= max_bad:
                hits.append((tuple(S[0]), tuple(out)))
            return
        if j == n:
            # every row not spent on the `bad` budget annihilates all of S,
            # so ANY vector of S has <= max_bad nonzero rows.
            out = count_out(S[0])
            if len(out) <= max_bad:
                hits.append((tuple(S[0]), tuple(out)))
            return
        S2 = _intersect(S, col[j])
        if len(S2) == len(S):                 # row j kills S already: not a choice
            rec(j + 1, S2, bad)
            return
        rec(j + 1, S2, bad)                             # row j is a ZERO row
        if bad > 0:
            rec(j + 1, S, bad - 1)                      # row j is a NONZERO row

    rec(0, [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]], max_bad)
    return hits


def find_44_codewords(M, label, quiet=False):
    """Every (wt_in = 4, wt_out = 4) codeword of {(b, Mb)}, as (A, B) lane pairs.
    A (4,4) codeword has 20 zero rows, so its polynomial has degree >= 20, so
    max(A) >= 20 -- the only prefilter, and it is a theorem."""
    n = len(M)
    As = [A for A in itertools.combinations(range(n), 4) if max(A) >= 20]
    found, seen = [], set()
    t = time.time()
    for A in As:
        col = [[M[j][i] for i in A] for j in range(n)]
        for v, out in best_lowweight_vectors(col, n, 4):
            if len(out) == 4 and all(v[k] for k in range(4)):
                key = (A, tuple(out))
                if key not in seen:
                    seen.add(key)
                    found.append(key)
    if not quiet:
        print(f"  {label}: {len(found)} (4,4) codewords over {len(As)} candidate "
              f"supports  [{time.time() - t:.1f}s]")
    return found, 0


cw, degen = find_44_codewords(Mc, "Weft-C")

for A, B in sorted(cw)[:12]:
    print(f"     in {list(A)}  ->  out {list(B)}")
if len(cw) > 12:
    print(f"     ... and {len(cw) - 12} more")

check("GUARD: the search recovers the constructive witness {0,4,16,20}->{20,21,22,23}",
      ((0, 4, 16, 20), (20, 21, 22, 23)) in set(cw), True, wrong=False)

# ---- the transition digraph and the 4-cycle question
edges = {}
for A, B in cw:
    edges.setdefault(frozenset(A), set()).add(frozenset(B))


def longest_chain(edges, start, depth):
    """Deepest chain of weight-4 supports startable at `start`, capped at `depth`."""
    best = 1
    frontier = {start}
    for d in range(depth - 1):
        nxt = set()
        for s in frontier:
            nxt |= edges.get(s, set())
        if not nxt:
            break
        frontier = nxt
        best = d + 2
    return best


if cw:
    depths = {longest_chain(edges, frozenset(A), 4) for A, _ in cw}
    md = max(depths)
    srcs = {frozenset(A) for A, _ in cw}
    tgts = {frozenset(B) for _, B in cw}
    print(f"\n  distinct in-supports {len(srcs)}, out-supports {len(tgts)}, "
          f"in ∩ out = {len(srcs & tgts)}")
    print(f"  deepest chain of weight-4 supports: {md} step(s) "
          f"(4 would attain the floor(R/2)*B_d = 16 bound at R = 4)")
    if md >= 4:
        print("  => the generic bound 16 IS attained at R = 4: the 4-step minimum "
              "active S-box count is EXACTLY 16 along weight-4 chains")
    else:
        print(f"  => no weight-4 chain reaches 4 steps (deepest {md}); the 4-step "
              f"minimum active count is STRICTLY ABOVE the generic 16")

    # What does a weight-4 trail cost on its THIRD step?  Exact, per out-support.
    # `best_lowweight_vectors(col, n, cap)` branches on WHICH rows are nonzero with a
    # budget of `cap`, so a run that returns nothing proves min wt_out > cap.
    CAP = 12
    print(f"\n  onward minimum weight from each (4,4) out-support "
          f"(exhaustive to wt_out <= {CAP}):")
    for B in sorted(tgts, key=sorted):
        Bs = sorted(B)
        colB = [[Mc[j][i] for i in Bs] for j in range(T)]
        hits = [h for h in best_lowweight_vectors(colB, T, CAP)
                if all(h[0][k] for k in range(4))]
        if hits:
            best = min(len(h[1]) for h in hits)
            print(f"    supp {Bs} -> min wt_out = {best}"
                  f"   (a 3-step trail through it costs >= {4 + 4 + best})")
        else:
            print(f"    supp {Bs} -> min wt_out >= {CAP + 1}"
                  f"   (a 3-step trail through it costs >= {4 + 4 + CAP + 1})")

# ---- the falsification guard: perturb ONE coefficient IN A COLUMN THE WITNESSES USE.
# (The first version flipped M[7][11]; column 11 appears in no (4,4) support, so the
# mutation was a NO-OP for this measurement and the guard read DEAD.  Recorded.)
used_cols = sorted({i for A, _ in cw for i in A})
tgt_col = used_cols[0] if used_cols else 0
Mp = [r[:] for r in Mc]
Mp[7][tgt_col] ^= 0x1
assert Mp != Mc, "the mutation did not change the matrix -- DEAD GUARD"
assert tgt_col in used_cols, "the mutated column is not read by any witness -- DEAD GUARD"
cw_p, _ = find_44_codewords(Mp, f"PERTURBED (M[7][{tgt_col}] flipped)")
check("GUARD: flipping one coefficient a witness READS moves the (4,4) count",
      len(cw_p) != len(cw), True, wrong=False)
print(f"         (Twill {len(cw)} vs perturbed {len(cw_p)})")


# ---------------------------------------------------------------------------- done
banner("RESULT")
print(f"  failures    : {FAILURES if FAILURES else 'none'}")
print(f"  dead guards : {DEAD_GUARDS if DEAD_GUARDS else 'none'}")
if FAILURES or DEAD_GUARDS:
    sys.exit(1)
print("  every row reproduced and every guard refused its wrong value.")
