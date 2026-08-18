"""
FCT-3: are the mod-q primitives EXPRESSIBLE as CLAASP components, exactly?

CLAASP has no odd-prime arithmetic (fct2).  gf_claasp.py emulates it from
mod-2^n components.  This checks each emulation EXHAUSTIVELY against Python
ground truth -- if any row is not exhaustive-exact, the expressibility claim
in the note is void.

Falsification guard: a deliberately WRONG reference (q+1 instead of q) must
make the same comparison go red.
"""
import sys
from claasp.cipher import Cipher
from gf_claasp import Builder, Wire

N = 6
Q = 61                       # 6-bit odd prime; 2^6 - 61 = 3, the small-gamma shape


def harness(build_fn, in_bits, out_bits):
    c = Cipher("gf", "permutation", ["input"], [in_bits], out_bits)
    c.add_round()
    b = Builder(c)
    out = build_fn(b, Wire("input", range(in_bits)))
    c.add_cipher_output_component([out.cid], [out.pos], len(out))
    return c, b


def exhaustive(cipher, in_bits, ref, domain):
    bad = []
    for x in domain:
        got = cipher.evaluate([x])
        want = ref(x)
        if got != want:
            bad.append((x, got, want))
    return bad


print("=" * 78)
print(f"FCT-3  mod-q primitives as CLAASP graphs   (n={N}, q={Q})")
print("=" * 78)

results = []

# ---------------------------------------------------------------- addq
def build_addq(b, inp):
    a = inp.slice(0, N)
    bb = inp.slice(N, 2 * N)
    return b.addq(a, bb, N, Q)

cipher, bld = harness(build_addq, 2 * N, N)
dom = [(a << N) | v for a in range(Q) for v in range(Q)]
bad = exhaustive(cipher, 2 * N, lambda x: ((x >> N) + (x & ((1 << N) - 1))) % Q, dom)
print(f"\naddq : {len(dom)} pairs (a,b) in [0,q)^2, {bld.n_components} components")
print(f"       mismatches = {len(bad)}" + (f"   e.g. {bad[:3]}" if bad else "   EXACT"))
results.append(("addq", len(bad) == 0))

# guard: the same graph must FAIL against a wrong reference
badg = exhaustive(cipher, 2 * N, lambda x: ((x >> N) + (x & ((1 << N) - 1))) % (Q + 1), dom)
print(f"       GUARD vs wrong modulus q+1={Q+1}: mismatches = {len(badg)}"
      f"  ({'LIVE' if badg else 'DEAD -- comparison proves nothing'})")
guard_live = len(badg) > 0

# ---------------------------------------------------------------- mulq_const
gvals = [1, 2, 3, Q - 1, 37, 60]
mul_ok = True
print(f"\nmulq_const : a*g mod q, a over all of [0,q), g public constant")
for g in gvals:
    cipher, bld = harness(lambda b, inp, g=g: b.mulq_const(inp.slice(0, N), g, N, Q), N, N)
    bad = exhaustive(cipher, N, lambda x, g=g: (x * g) % Q, range(Q))
    ok = len(bad) == 0
    mul_ok &= ok
    print(f"       g={g:<4} components={bld.n_components:<5} mismatches={len(bad)}"
          f"  {'EXACT' if ok else bad[:2]}")
results.append(("mulq_const", mul_ok))

# ---------------------------------------------------------------- mul_exact
NB = 8                        # operands < 2^4, product < 2^8: exact in 8-bit arithmetic
def build_mulx(b, inp):
    a = inp.slice(0, NB)
    bb = inp.slice(NB, 2 * NB)
    return b.mul_exact(a, bb, NB)

cipher, bld = harness(build_mulx, 2 * NB, NB)
dom = [(a << NB) | v for a in range(16) for v in range(16)]
bad = exhaustive(cipher, 2 * NB, lambda x: ((x >> NB) * (x & 0xFF)) % (1 << NB), dom)
print(f"\nmul_exact : 4x4->8 bit products, {bld.n_components} components")
print(f"       mismatches = {len(bad)}" + (f"   e.g. {bad[:3]}" if bad else "   EXACT"))
results.append(("mul_exact", len(bad) == 0))

print()
print("=" * 78)
if not guard_live:
    print("GUARD DEAD -- the exhaustive comparison cannot go red.  NO VERDICT.")
    sys.exit(2)
allok = all(ok for _, ok in results)
for name, ok in results:
    print(f"  {'EXACT ' if ok else 'FAILED'}  {name}")
print()
if allok:
    print("VERDICT: every mod-q operation the gadget-Feistel needs is EXACTLY")
    print("  expressible in CLAASP's existing component vocabulary.  Nothing")
    print("  is missing from the vocabulary -- the emulation is the cost.")
else:
    print("VERDICT: at least one primitive is NOT exactly expressible as built.")
    sys.exit(1)
