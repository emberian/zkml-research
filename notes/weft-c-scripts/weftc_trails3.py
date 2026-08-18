"""
L4: the block-constant subspace-trail scan EXTENDED to |S| = 3, plus a random-partition
arm -- the item `weft-coset-repair.md` sec.3d listed as NARROWED, not closed.

The family: a lane-wise S-box preserves a subspace for EVERY S-box iff the subspace is
BLOCK-CONSTANT, and that is exactly where 2026/306's low-weight invariant subspaces of
`M_eps = P_{t/4} (x) M_4` live.  `weft_coset_repair.py`'s `trail_scan` covered
|S| <= 2 plus the regular contiguous/strided block families (370 starts): 0/370 stalls
for the coset form, 117/370 for both fast systematic-RS splits.

This adds:
  (a) EVERY |S| = 3 start                            (C(24,3) = 2024, exhaustive at 3)
  (b) 500 random irregular partitions with 2..6 live blocks (a sample, said so)
run on Twill, on the KILLED form, and on Mark-32's OWN matrix.

GUARDS.  The killed form must stall on every start (it has a fixed lane), and Mark-32's
matrix must stall on the (0,1)(2,3)...(22,23) family -- if either comes back clean the
instrument is not measuring anything and the run fails.

Run: python3 -u weftc_trails3.py    (~10 min)
"""

import itertools
import os
import random
import sys
import time

sys.path.insert(0, os.path.expanduser("~/src/ring-ro-hash"))

from weft_branch import build_matrix, subspace_points                  # noqa: E402
from weft2_structure import build_coset                                # noqa: E402
from weft_coset_repair import block_constant_trail, sysrs_matrix       # noqa: E402

T = 24
SHIFT = 0xA3C17E59
FAILURES = []

beta = [1 << j for j in range(6)]
Mc, _ = build_coset(beta, SHIFT, T, 5)
M0, _ = build_matrix(beta, T, 5)
A32 = sysrs_matrix(beta, list(range(24)), list(range(24, 48)), 6)

rng = random.Random(20260818)


def starts_wt3():
    return [set(S) for S in itertools.combinations(range(T), 3)]


def starts_random_partitions(n_samples):
    out = []
    for _ in range(n_samples):
        k = rng.randint(2, 6)                      # number of live blocks
        lanes = list(range(T))
        rng.shuffle(lanes)
        cut = sorted(rng.sample(range(1, T), k - 1))
        prev, blocks = 0, []
        for c in cut + [T]:
            blocks.append(set(lanes[prev:c]))
            prev = c
        out.append(blocks[0])                      # seed from one live block
    return out


def scan(M, label, starts, rounds=6):
    t = time.time()
    stalled = []
    for S in starts:
        v = [0] * T
        for i in S:
            v[i] = 1
        dims = block_constant_trail(M, v, rounds)
        if dims[-1] != T:
            stalled.append((tuple(sorted(S)), dims))
    print(f"  {label:<44} {len(stalled):5d} / {len(starts):5d} stalled "
          f"[{time.time() - t:.1f}s]")
    if stalled:
        seen = set()
        for S, dims in stalled[:4]:
            if tuple(dims) in seen:
                continue
            seen.add(tuple(dims))
            print(f"      e.g. start {list(S)} -> dims {dims}")
    return stalled


print("=" * 78)
print("L4  block-constant subspace trails, |S| = 3 (exhaustive) + random partitions")
print("=" * 78)

w3 = starts_wt3()
print(f"\n|S| = 3, all {len(w3)} starts, 6 rounds:")
s_c = scan(Mc, "Twill (coset, 1 pass)", w3)
s_0 = scan(M0, "Weft-1 KILLED (control, must stall)", w3)
s_m = scan(A32, "Mark-32's OWN matrix (control, must stall)", w3)

rp = starts_random_partitions(500)
print(f"\nrandom irregular partitions, {len(rp)} starts, 6 rounds:")
r_c = scan(Mc, "Twill (coset, 1 pass)", rp)
r_0 = scan(M0, "Weft-1 KILLED (control, must stall)", rp)
r_m = scan(A32, "Mark-32's OWN matrix (control, must stall)", rp)

print()
print("=" * 78)
print("GUARDS -- an instrument that finds nothing anywhere is not an instrument")
print("=" * 78)


def guard(name, cond, detail):
    ok = bool(cond)
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}   ({detail})")
    if not ok:
        FAILURES.append(name)


guard("the KILLED form stalls at |S| = 3", len(s_0) > 0,
      f"{len(s_0)}/{len(w3)}")
guard("the KILLED form stalls on random partitions", len(r_0) > 0,
      f"{len(r_0)}/{len(rp)}")

# Mark-32's flag lives on the CONTIGUOUS-PAIR family (0,1)(2,3)...(22,23), not on
# arbitrary 3-subsets, so that is where its control arm belongs.  A 3-subset start has
# bc-hull dim 1 and explodes on the next step for any dense matrix; reading Mark-32's
# 0/2024 there as "no structure" would be exactly the wrong conclusion.
pairs = [set((2 * i, 2 * i + 1)) for i in range(T // 2)]
print("\ncontiguous-pair family (0,1)(2,3)...(22,23), 12 starts -- where the flag lives:")
p_c = scan(Mc, "Twill (coset, 1 pass)", pairs)
p_m = scan(A32, "Mark-32's OWN matrix (must stall)", pairs)
guard("Mark-32's OWN matrix stalls on the contiguous-pair family", len(p_m) > 0,
      f"{len(p_m)}/{len(pairs)}")
guard("Twill does NOT stall on the contiguous-pair family", len(p_c) == 0,
      f"{len(p_c)}/{len(pairs)}")

print()
print("=" * 78)
print(f"RESULT  Twill: {len(s_c)}/{len(w3)} stalled at |S|=3, "
      f"{len(r_c)}/{len(rp)} on random partitions")
print(f"        failures: {FAILURES if FAILURES else 'none'}")
if FAILURES:
    sys.exit(1)
