"""
FCT-5: build a FULL gadget-Feistel round as a CLAASP component graph and check
it against the VERSIONED spec, then measure what the graph costs.

The reference is `~/src/ring-ro-hash/design_gadget_feistel.py` -- loaded, not
re-implemented.  Only its parameter block is patched (the ring degree D is a
module global there), and the patch is ASSERTED to have happened, because a
mutation that silently becomes a no-op is how a falsifier dies.

Toy parameters keep every STRUCTURAL invariant of the deployment:
    n = K*b            digits are exact bit-slices
    q < 2^n, gamma = 2^n - q small     the canonicality shape
    d*B^2 < q          the Y*Y products need no wide reduction
"""
import os, random, sys, textwrap

from claasp.cipher import Cipher
from gf_claasp import Wire
from gf_round import RingFeistelEncoder

SPEC = os.path.expanduser("~/src/ring-ro-hash/design_gadget_feistel.py")

# ---------------------------------------------------- load the versioned spec
src = open(SPEC).read()
cut = src.index("# ================================================== (1) bijectivity")
prefix = src[:cut]

D_TOY = 4
patched, nsub = __import__("re").subn(r"^D = 16$", f"D = {D_TOY}", prefix, flags=8)
assert nsub == 1, (f"the D-patch matched {nsub} lines, not 1 -- the spec's "
                   f"parameter block moved; this harness is testing nothing")
assert f"D = {D_TOY}" in patched and "\nD = 16\n" not in patched, "patch did not take"
ns = {"__name__": "spec"}
exec(compile(patched, SPEC, "exec"), ns)
Feistel = ns["Feistel"]
print(f"loaded spec {SPEC}\n  ring degree patched 16 -> {D_TOY} (1 substitution, asserted)")

# ------------------------------------------------------------- toy parameters
N, Q = 12, 4093            # 2^12 - 3: the small-gamma shape (gamma/q = 2^-10.4)
DEG, Wd, K, BEXP, P = D_TOY, 1, 4, 3, 2
B = 1 << BEXP
assert N == K * BEXP and DEG * B * B < Q < (1 << N)
print(f"toy: n={N} q={Q} (gamma={2**N-Q}) d={DEG} w={Wd} K={K} B=2^{BEXP} P={P}")
print(f"     deployment: n=64 q=2^64-257 (gamma=257) d=16 w=4 K=4 B=2^16 P=2 NR=16")

ref = Feistel(Q, seed=2026, w=Wd, p=P, nr=1, base=B, k=K)

# --------------------------------------------------------------- build the graph
NBITS = 2 * Wd * DEG * N
cipher = Cipher("gadget_feistel", "permutation", ["input"], [NBITS], NBITS)
cipher.add_round()
enc = RingFeistelEncoder(cipher, N, Q, DEG, Wd, K, BEXP, P)

inp = Wire("input", range(NBITS))
def take(idx):
    return inp.slice(idx * N, (idx + 1) * N)

L = [[take(i * DEG + c) for c in range(DEG)] for i in range(Wd)]
R = [[take(Wd * DEG + i * DEG + c) for c in range(DEG)] for i in range(Wd)]

L2, R2 = enc.round(L, R, ref.a[0], ref.g[0], ref.h[0])
flat = [x for e in L2 for x in e] + [x for e in R2 for x in e]
cipher.add_cipher_output_component([x.cid for x in flat], [x.pos for x in flat], NBITS)

print(f"\nbuilt: {enc.B.n_components} components, "
      f"{enc.free_digit_slices} base-B digit extractions costing ZERO components")

# ------------------------------------------------------------------ verify
def pack(Lv, Rv):
    bits = 0
    for e in Lv + Rv:
        for c in e:
            bits = (bits << N) | (c % Q)
    return bits

def unpack(v):
    coeffs = [(v >> (N * (2 * Wd * DEG - 1 - i))) & ((1 << N) - 1)
              for i in range(2 * Wd * DEG)]
    out = []
    for k in range(2 * Wd):
        out.append(coeffs[k * DEG:(k + 1) * DEG])
    return out[:Wd], out[Wd:]

rng = random.Random(20260818)
TRIALS = 40
bad = []
for _ in range(TRIALS):
    Lv = [[rng.randrange(Q) for _ in range(DEG)] for _ in range(Wd)]
    Rv = [[rng.randrange(Q) for _ in range(DEG)] for _ in range(Wd)]
    want = ref.perm([e[:] for e in Lv], [e[:] for e in Rv], rounds=1)
    got = unpack(cipher.evaluate([pack(Lv, Rv)]))
    if (list(got[0]), list(got[1])) != ([list(x) for x in want[0]], [list(x) for x in want[1]]):
        bad.append((Lv, Rv, got, want))

print(f"\nAGREEMENT with the versioned spec: {TRIALS - len(bad)}/{TRIALS} random states")
if bad:
    print("  MISMATCH, first:", bad[0])

# guard: a perturbed reference must disagree
badg = 0
for _ in range(TRIALS):
    Lv = [[rng.randrange(Q) for _ in range(DEG)] for _ in range(Wd)]
    Rv = [[rng.randrange(Q) for _ in range(DEG)] for _ in range(Wd)]
    wrong = Feistel(Q, seed=2027, w=Wd, p=P, nr=1, base=B, k=K)  # different constants
    want = wrong.perm([e[:] for e in Lv], [e[:] for e in Rv], rounds=1)
    got = unpack(cipher.evaluate([pack(Lv, Rv)]))
    if (list(got[0]), list(got[1])) != ([list(x) for x in want[0]], [list(x) for x in want[1]]):
        badg += 1
print(f"GUARD (spec with different round constants): {badg}/{TRIALS} disagree"
      f"  ({'LIVE' if badg == TRIALS else 'DEAD -- the comparison proves nothing'})")

if bad or badg != TRIALS:
    print("\nEXPRESSIBILITY NOT ESTABLISHED.")
    sys.exit(1)

# --------------------------------------------------------------- the cost
print()
print("=" * 78)
print("COMPONENT CENSUS for one toy round")
print("=" * 78)
tot_w = 0
for kind, (cnt, wsum) in sorted(enc.B.by_kind.items(), key=lambda kv: -kv[1][0]):
    tot_w += wsum
    print(f"  {kind:<15}{cnt:>8} components{wsum:>12} output bits")
print(f"  {'TOTAL':<15}{enc.B.n_components:>8} components{tot_w:>12} output bits")
print(f"  base-B digit extraction: {enc.free_digit_slices} slices, 0 components"
      f"  <-- the decomposition layer is FREE")

print()
print("=" * 78)
print("VERDICT")
print("=" * 78)
print(textwrap.dedent(f"""\
    The gadget-Feistel round IS expressible as a CLAASP component graph.  The
    graph built here reproduces the versioned spec exactly on {TRIALS}/{TRIALS} random
    states, and the comparison is live.  NO component is missing from CLAASP's
    vocabulary; what is missing is odd-prime arithmetic as a PRIMITIVE, so every
    mod-q step is paid for in emulation:
      addq        {8:>4} components
      subq        {6:>4} components
      mulq_const  ~2n addq  (double-and-add; no Barrett, no wide arithmetic)
      digits         0 components  (base-B decomposition IS bit-slicing)
      Y*Y products   mod-2^n exact -- CLAASP-MP's own Algorithm 4 shape
    """))
