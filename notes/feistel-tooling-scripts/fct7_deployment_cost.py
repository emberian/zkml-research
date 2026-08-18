"""
FCT-7: EXACT size of the CLAASP graph at DEPLOYMENT parameters.

fct5 verified the encoder exactly at toy scale.  This runs the SAME encoder
code against a counting-only Builder, so the deployment figure is produced by
the verified construction rather than by an estimate.

Deployment: q = 2^64-257 (tau=2), d=16, w=4, K=4, B=2^16, P=2, NR=16.
"""
import random, sys
from gf_claasp import Wire
import gf_claasp, gf_round


class CountingBuilder:
    """Same surface as gf_claasp.Builder; allocates no CLAASP objects."""

    def __init__(self):
        self.n_components = 0
        self.total_output_bits = 0
        self.by_kind = {}
        self._const_cache = {}
        self._uid = 0

    def _emit(self, kind, width):
        self.n_components += 1
        self.total_output_bits += width
        k = self.by_kind.setdefault(kind, [0, 0])
        k[0] += 1
        k[1] += width
        self._uid += 1
        return Wire(f"{kind}_{self._uid}", range(width))

    def const(self, width, value):
        key = (width, value)
        if key not in self._const_cache:
            self._const_cache[key] = self._emit("constant", width)
        return self._const_cache[key]

    def modadd(self, wires, width):  return self._emit("modadd", width)
    def modsub(self, wires, width):  return self._emit("modsub", width)
    def xor(self, wires, width):     return self._emit("xor", width)
    def and_(self, wires, width):    return self._emit("and", width)
    def shift(self, wire, width, a): return self._emit("shift", width)

    def linear(self, wire, matrix, width):
        return self._emit("linear_layer", width)

    def broadcast_msb(self, wire, width):
        assert len(wire) == width
        return self.linear(wire, None, width)

    def broadcast_bit(self, bit, width):
        zw = self.const(width, 0)
        self.xor(None, width)
        return self.modsub(None, width)

    # the mod-q layer, byte-identical in structure to gf_claasp.Builder
    addq = gf_claasp.Builder.addq
    dblq = gf_claasp.Builder.dblq
    mulq_const = gf_claasp.Builder.mulq_const
    mul_exact = gf_claasp.Builder.mul_exact


def measure(n, q, d, w, K, b, P, label, seed=2026):
    B = CountingBuilder()
    enc = gf_round.RingFeistelEncoder.__new__(gf_round.RingFeistelEncoder)
    enc.B = B
    enc.n, enc.q, enc.d, enc.w, enc.K, enc.b, enc.P = n, q, d, w, K, b, P
    enc.free_digit_slices = 0

    rng = random.Random(seed)
    rr = lambda: [rng.randrange(q) for _ in range(d)]
    a_r = [rr() for _ in range(w)]
    g_r = [[[rr() for _ in range(K)] for _ in range(w)] for _ in range(w)]
    h_r = [[[rr() for _ in range(P)] for _ in range(w)] for _ in range(w)]

    nbits = 2 * w * d * n
    inp = Wire("input", range(nbits))
    take = lambda i: inp.slice(i * n, (i + 1) * n)
    L = [[take(i * d + c) for c in range(d)] for i in range(w)]
    R = [[take(w * d + i * d + c) for c in range(d)] for i in range(w)]
    enc.round(L, R, a_r, g_r, h_r)

    print(f"\n{label}")
    print(f"  n={n} d={d} w={w} K={K} B=2^{b} P={P}   state = {nbits} bits")
    for kind, (cnt, wsum) in sorted(B.by_kind.items(), key=lambda kv: -kv[1][0]):
        print(f"    {kind:<14}{cnt:>14,} components{wsum:>18,} output bits")
    print(f"    {'TOTAL/round':<14}{B.n_components:>14,} components"
          f"{B.total_output_bits:>18,} output bits")
    print(f"    base-B digit extractions: {enc.free_digit_slices} -- ZERO components")
    return B.n_components, B.total_output_bits


print("=" * 78)
print("FCT-7  size of the CLAASP component graph, toy vs deployment")
print("=" * 78)

# cross-check against the toy that fct5 verified against the versioned spec
tc, tb = measure(12, 4093, 4, 1, 4, 3, 2, "TOY (the instance fct5 verified exact)")

dc, db = measure(64, (1 << 64) - 257, 16, 4, 4, 16, 2, "DEPLOYMENT")

NR = 16
print()
print("=" * 78)
print("WHAT THIS MEANS FOR THE MILP")
print("=" * 78)
print(f"  per round      : {dc:,} components, {db:,} wire bits")
print(f"  NR=16 rounds   : {dc*NR:,} components, {db*NR:,} wire bits")
print()
print("  CLAASP-MP allocates at least one binary exponent variable per wire bit,")
print("  plus COPY variables per fan-out, so the MILP has >= that many binaries.")
print()
print("  For scale, the instances CLAASP-MP actually solves (eprint 2026/735):")
print("    SIMON-32, 3 rounds     32-bit block, solved here in ~1s")
print("    ChaCha 6.75 rounds     512-bit state   (the paper's headline)")
print("    Trivium                288-bit state")
print("    MSX-128, 6 rounds      128-bit state")
print(f"  our 1 round is {db:,} wire bits against a 512-bit ChaCha state.")
print()
print(f"  the Gurobi size-limited license available here caps at ~2,000 variables;")
print(f"  a full license does not close a gap of this size either.")
