#!/usr/bin/env python3
"""Exact Merkle-commit permutation geometry for the deployed IR-v2 transfer batch.

Model = the vendored p3 merkle_tree.rs algorithm (plonky3-fri-82cfad73 /
~/.cargo git checkout 82cfad7), read at source 2026-08-18:
  - first_digest_layer: one PaddingFreeSponge row-hash per row of the tallest
    matrices (matrices of equal height hashed together into one digest);
    perms per row = ceil(sum_width / RATE).
  - compress_and_inject: per level, len/step compressions; when matrices inject
    at a level, EACH node additionally row-hashes the injected rows (one sponge,
    ceil(w_inj/RATE) perms) and spends ONE extra compression to mix it in.
  - N (compression arity) must be a power of two (const assert in new()).

Committed matrices of the deployed transfer batch, read off the plonky3 DFT
spans (fo/raw-spans.log, §C run 2026-08-18, lb=6 q=19):
  round 1 (main):     236x64, 2x16, 386x8
  round 2 (perm):     72x64,  4x16, 12x8
  round 3 (quotient): 8x64,   8x16, 32x8
LDE height = h * 2^b.

VALIDATION: at b=6 the model must reproduce the measured 211,965 Merkle-commit
permutations (ir2_phase_profile §D, notes/phase-profile.md §7) EXACTLY, and
x2 per rung reproduces 26,493/52,989/105,981/423,933 (all heights double and
the injection structure is height-ratio-invariant).

Native ns/perm measured this lane (scratchpad p2bench, interleaved A/B,
min-of-41, contended laptop -- RATIO is the deliverable):
  w16 836.5 ns, w24 1195.7 ns  => r24_nat = 1.429
In-circuit cells/perm ratios (w24/w16):
  wide (deployed 352-aux shape): (29+1)*24 / (21+1)*16 = 720/352 = 2.045
  narrow (p3-poseidon2-air REG=0, virtualization arm B): 237/157 = 1.510
"""

RATE16 = 8   # w16 sponge: rate 8, cap 8
RATE24 = 16  # w24 sponge: rate 16, cap 8

ROUNDS = [
    [(236, 64), (2, 16), (386, 8)],
    [(72, 64), (4, 16), (12, 8)],
    [(8, 64), (8, 16), (32, 8)],
]


def ceil_div(a, b):
    return -(-a // b)


def tree_perms(mats, b, rate, node_arity=2):
    """(leaf_sponge_perms, node_compressions) for one MMCS tree.

    mats: [(width, base_height)] sorted any order; heights are distinct
    powers-of-two multiples here so the p3 balancing rule holds.
    node_arity: power of two. Injection levels fall back to binary steps
    exactly when an intermediate matrix height sits between N-ary targets
    (select_arity_step); with our height set every injection level is a
    binary step, modeled as: pair-compress + inject-compress.
    """
    mats = sorted(((w, h << b) for w, h in mats), key=lambda x: -x[1])
    max_h = mats[0][1]
    tallest_w = sum(w for w, h in mats if h == max_h)
    leaf = max_h * ceil_div(tallest_w, rate)
    node = 0
    level = max_h
    rest = [(w, h) for w, h in mats if h != max_h]
    while level > 1:
        # does a matrix inject at level/step for some step?
        # p3: step=N unless an intermediate height sits above the N-ary target
        # (select_arity_step), and step=2 whenever level < N.
        target = level // node_arity
        inject_here = [(w, h) for w, h in rest if h == level // 2]
        if level < node_arity:
            step = 2
        elif inject_here and node_arity != 2:
            step = 2  # binary bridge step
        elif any(h > target for w, h in rest):
            step = 2
        else:
            step = node_arity
        nxt = level // step
        node += nxt  # one compression per parent
        injected = [(w, h) for w, h in rest if h == nxt]
        for w, h in injected:
            leaf += h * ceil_div(w, rate)
            node += h  # the extra inject-compression per node
            rest.remove((w, h))
        level = nxt
    return leaf, node


def batch(b, rate, node_arity=2):
    L = N = 0
    for r in ROUNDS:
        l, n = tree_perms(r, b, rate, node_arity)
        L += l
        N += n
    return L, N


if __name__ == "__main__":
    # 1. validation
    for b, want in [(3, 26493), (4, 52989), (5, 105981), (6, 211965), (7, 423933)]:
        l, n = batch(b, RATE16, 2)
        tot = l + n
        print(f"b={b}: leaf {l:>7} + node {n:>6} = {tot:>7}  measured {want:>7}  "
              f"{'EXACT' if tot == want else 'MISMATCH'}")
    l6, n6 = batch(6, RATE16, 2)
    print(f"\ndeployed split at b=6: leaf {l6} ({100*l6/(l6+n6):.2f}%)  "
          f"node {n6} ({100*n6/(l6+n6):.2f}%)")

    # 2. w24 rate-16 leaf sponge, nodes unchanged (w16 2:1)
    l24, n24 = batch(6, RATE24, 2)
    r24 = 1195.7 / 836.5
    cost = l24 * r24 + n24
    base = l6 + n6
    print(f"\nw24 rate-16 sponge: leaf {l24} w24-perms + node {n24} w16-perms")
    print(f"  native w16-equivalents: {cost:,.0f} vs {base:,} -> x{cost/base:.3f}")

    # 3. hypothetical arity-4 (w32 nodes, does not exist in p3-baby-bear):
    #    node count with N=4; per-node cost extrapolated by S-box count
    #    (w32 ~ (32*8+30)/(16*8+13) = 2.03x w16 -- bracket, not a measurement)
    l4, n4 = batch(6, RATE16, 4)
    for r32 in (1.8, 2.03, 2.3):
        c = l4 + n4 * r32
        print(f"  arity-4 nodes (r32={r32}): leaf {l4} + node {n4} -> x{c/base:.3f}")

    # 4. in-circuit wrap: shares from leaf-vs-recursion.md §2c
    absorb, leaf_sh, path = 0.292, 0.649, 0.059
    cnt = 52 / 98  # sum ceil(w/16) / sum ceil(w/8) over the IR2 batch (calibration)
    for name, rc in [("wide 720/352", 2.045), ("narrow 237/157", 1.510)]:
        wrap = absorb + leaf_sh * cnt * rc + path
        print(f"  wrap perm-cost multiplier, w24 leaves ({name}): x{wrap:.3f}")

    # 5. the wrap PADDING STAIRCASE under a two-table split (narrow cols).
    # Today: one w16 table of 38,168 perm-rows -> pads to 2^16.
    # Split: w16 rows = absorb+path share of 38,168; w24 rows = leaf share
    # scaled by the count ratio. Each pads to its own power of two.
    perms = 38168
    npo2 = lambda x: 1 << (x - 1).bit_length()
    w16_rows = round(perms * (absorb + path))
    w24_rows = round(perms * leaf_sh * cnt)
    today = npo2(perms) * 157
    split = npo2(w16_rows) * 157 + npo2(w24_rows) * 237
    print(f"\n  staircase (narrow cols): today {npo2(perms)}x157 = {today:,} cells;"
          f"\n  split {npo2(w16_rows)}x157 + {npo2(w24_rows)}x237 = {split:,} cells"
          f" -> x{split/today:.3f}  [staircase-dependent: valid only at these counts]")
