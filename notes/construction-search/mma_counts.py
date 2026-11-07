#!/usr/bin/env python3
"""mma_counts.py -- counts-exact model of field kernels as tensor-core MMA work (initiative 14, F3).

2026-11-06.  stdlib only.  Companion to notes/tensor-core-holography/F3-MODEL.md.

    python3 -I notes/construction-search/mma_counts.py              # everything
    python3 -I notes/construction-search/mma_counts.py --validate   # TensorZKP + mma-field-mapping checks only

For an MMA kind (operand format, accumulator semantics), a SKU (published dense rates, HBM bandwidth),
a field (BabyBear^k / KoalaBear^k / Goldilocks^2 as integer limbs; Tower256 / GF(2^128) as GF(2) bit
matrices) and an operation (inner product, fold by a sampled challenge, sumcheck round of degree d,
cSHAKE Merkle layer, additive-NTT butterfly layer), it prints
  MACs and MMA instructions (tile-padded), the exact block length (products per accumulator before an
  off-MMA reduction or promotion), HBM bytes, SIMT int32 ops, and a three-term floor
  max(bytes/BW, MACs/TC, ops/SIMT) naming the binding term.
The floor is a roofline proxy, not a measurement.  Counts are exact for the stated algorithm; every
rate carries a tag: [X:src] published elsewhere, [READ:src] read by us in the source, [A] assumption,
[D] derived in this file.

Exactness semantics (the Lean side is minidregg Theory/MmaAccumulatorExact.lean on lane/mma-exact):
  int-wrap   .s32 accumulator, wraps mod 2^32 without .satfinite [READ: PTX ISA 9.x, mma integer]
             signed reading exact iff every partial sum in [-2^31, 2^31); unsigned reading of a
             nonnegative sum exact iff < 2^32; parity reading exact for EVERY length.
  fp-m       floating accumulator holding integers exactly while |partial| < 2^m.  m is per kind and
             per SKU and is MEASURED, not published: PTX 9.2 says FP8 wgmma accumulates "higher than half
             but lower than single precision" (so 12 <= m <= 23); DeepSeek-V3 reports ~14 on H800.
             Blackwell tcgen05 f8f6f4 / mxf4: no published statement found -> parameter.
  promotion  every K_p products the tensor-core partial is moved to an INT32 register (cvt + iadd):
             exact iff K_p * P < 2^m and N * P < 2^31.
"""
import argparse
import math

# ------------------------------------------------------------------------------------------------
# 0. SKUs.  Dense tensor rates in MAC/s (= published dense OPS / 2).  BW in bytes/s.  SIMT int32 op/s.
# ------------------------------------------------------------------------------------------------
SKUS = {
    # name: dict(int8, fp8, fp4, b1 MAC/s; bw; simt; note)
    "A100": dict(int8=624e12 / 2, fp8=None, fp4=None, b1=4992e12 / 2, bw=2.039e12,
                 simt=108 * 64 * 1.41e9,
                 src="[X: A100 datasheet dense INT8 624 TOPS, binary 4992 TOPS, 2.0 TB/s; SIMT 108 SM x 64 x 1.41 GHz A]"),
    "H100": dict(int8=1979e12 / 2, fp8=1979e12 / 2, fp4=None, b1=None, bw=3.35e12, simt=16.7e12,
                 src="[X: H100 SXM datasheet dense 1979 TOPS INT8 and FP8, 3.35 TB/s; SIMT 16.7e12 from space.py; "
                     "b1 wgmma exists in PTX (sm_90a) but no rate is published]"),
    "B200": dict(int8=4.5e15 / 2, fp8=4.5e15 / 2, fp4=9e15 / 2, b1=None, bw=8.0e12, simt=148 * 128 * 1.9e9,
                 src="[X: arXiv 2608.11693 Table I (INT8 = FP8 = 4.5 P dense); FP4 9 P dense NVIDIA; 8 TB/s; "
                     "SIMT 148 SM x 128 x 1.9 GHz A]"),
    "B300": dict(int8=0.15e15 / 2, fp8=4.5e15 / 2, fp4=15e15 / 2, b1=None, bw=8.0e12, simt=160 * 128 * 1.9e9,
                 src="[X: arXiv 2608.11693 Table I (INT8 0.15 P = FP8/30; kind::i8 absent on sm_103a); "
                     "FP4 15 P dense NVIDIA Blackwell Ultra; 8 TB/s; SIMT 160 SM x 128 x 1.9 GHz A]"),
}
I32 = 2 ** 31 - 1

# ------------------------------------------------------------------------------------------------
# 1. Limb schemes for prime fields (the mma-field-mapping encoder, reimplemented and asserted equal)
# ------------------------------------------------------------------------------------------------
FP4_DIGITS = [0, 1, -1, 2, -2, 3, -3, 4, -4, 6, -6, 8, -8, 12, -12]   # doubled E2M1 [READ: obend Accelerators.lean:36]


def _reps(base, ds):
    return {r: min((d for d in ds if d % base == r and d <= r), key=abs) for r in range(base)}


def limbs(p, base, ds):
    """Certified limb count of the explicit quotient/remainder encoder (mma_limbs.py after the Astra patch)."""
    reps = _reps(base, ds)
    terminal = 0
    while terminal + 1 in ds:
        terminal += 1
    bound, count = p - 1, 1
    while bound > terminal:
        bound, count = (bound - min(reps.values())) // base, count + 1
    return count, max(terminal, max(abs(d) for d in reps.values()))


SCHEMES = {   # kind -> (format key in SKU, base, digit set, accumulator kind, simt ops per limb to encode [A])
    "int8": ("int8", 256, list(range(256)), "int-wrap", 0.0),     # a byte IS a limb: reinterpretation
    "fp8": ("fp8", 16, list(range(16)), "fp", 1.0),              # nibble split + PRMT code lookup [A]
    "fp4": ("fp4", 13, FP4_DIGITS, "fp", 4.0),                   # mulhi/13, mul, sub, gapped-code LUT [A]
}

PRIMES = {"BabyBear": 2 ** 31 - 2 ** 27 + 1, "KoalaBear": 2 ** 31 - 2 ** 24 + 1, "Goldilocks": 2 ** 64 - 2 ** 32 + 1}
FIELDS = {   # name: (prime or None for char 2, extension degree k, bits per element)
    "BabyBear^4": ("BabyBear", 4), "BabyBear^8": ("BabyBear", 8), "KoalaBear^4": ("KoalaBear", 4),
    "Goldilocks^2": ("Goldilocks", 2), "Tower256": (None, 256), "GF2^128": (None, 128),
}
# SIMT cost of one extension-field multiplication (Hadamard products that cannot go on the MMA) [A]:
#   prime: 6 int32 ops per base Montgomery mult, Karatsuba k^log2(3) base mults + 2 ops per add (~3 k^1.58 adds),
#          plus (k-1) multiply-by-constant reductions; char 2: bit-sliced Karatsuba, 3^lg ANDs + ~2.5x XORs, /32 lanes.
def simt_mult_ops(field):
    pr, k = FIELDS[field]
    if pr is None:
        lg = int(math.log2(k))
        return (3 ** lg) * 3.5 / 32
    base = 6 if pr != "Goldilocks" else 14
    km = k ** math.log2(3)
    return km * base + 3 * km * 2 + (k - 1) * (base + 2)


def elem_bytes(field):
    pr, k = FIELDS[field]
    return k // 8 if pr is None else k * math.ceil(math.log2(PRIMES[pr]) / 8)


# ------------------------------------------------------------------------------------------------
# 2. Exactness: the longest block (products summed into one accumulator) for a kind
# ------------------------------------------------------------------------------------------------
def block_len(P, acc, m=None, reading="signed"):
    if acc == "int-wrap":
        if reading == "parity":
            return math.inf
        return (2 ** 32 - 1) // P if reading == "unsigned" else I32 // P
    return (2 ** m - 1) // P


def product_set(kind):
    """Products the explicit encoder can emit (its representatives and terminal digits), not the whole format."""
    _, base, ds, _, _ = SCHEMES[kind]
    reps = set(_reps(base, ds).values())
    t = 0
    while t + 1 in ds:
        t += 1
    digits = reps | set(range(-t, t + 1) if min(ds) < 0 else range(0, t + 1))
    return sorted({abs(a * b) for a in digits for b in digits})


def representable(x, m):
    a = abs(x)
    if a < 2 ** m:
        return True
    k = a.bit_length() - m
    return a % (2 ** k) == 0


def first_failure(products, m, n_max=100000):
    """Smallest N at which some N products (each from `products`, 0 allowed) sum, in left-to-right order, through a
    partial sum an m-bit truncating accumulator cannot hold.  Exact search over reachable sums (bitset DP);
    nonnegative products only (the gapped digit set's signs only add cancellation, never a smaller failure)."""
    reach = 1                      # bit s set <=> sum s reachable with exactly n products
    top = max(products)
    for n in range(1, n_max):
        nxt = 0
        for p in products:
            nxt |= reach << p
        reach = nxt
        lo = 2 ** m
        for s_ in range(lo, n * top + 1):
            if (reach >> s_) & 1 and not representable(s_, m):
                return n
    return None


# ------------------------------------------------------------------------------------------------
# 3. Kernels.  Each returns a dict of counts for one call on vectors of length N (elements).
# ------------------------------------------------------------------------------------------------
def prime_layout(field, kind):
    pr, k = FIELDS[field]
    fmt, base, ds, acc, enc_ops = SCHEMES[kind]
    L, maxd = limbs(PRIMES[pr], base, ds)
    return dict(L=L, kL=k * L, P=maxd * maxd, acc=acc, fmt=fmt, enc=enc_ops, k=k)


def kar_depth(bits, min_tile=16):
    """Karatsuba levels over the tower, stopping at sub-widths of min_tile bits (the MMA's smallest M/N).
    Lazy reduction commutes with Karatsuba: each of the 3^j sub-products is an outer-product sum reduced once
    by its own fixed bilinear map, and the recombination is linear [INFERRED; Lean: kar_lazy_commutes]."""
    return max(0, int(math.log2(bits // min_tile)))


def kar_macs(bits, j):
    return (3 ** j) * (bits >> j) ** 2


def kar_xor_ops(bits, j):
    """32-bit XORs to form the 3^j Karatsuba operand pieces from one element (pre-additions) [D]."""
    return sum((3 ** i) * (bits >> (i + 1)) for i in range(j)) / 32


def unpack_ops(bits, j):
    """bits -> one-byte 0/1 MMA operands for the 3^j pieces: per 4 output bytes, extract a nibble (shift, and)
    and spread it, (v * 0x00204081) & 0x01010101 (mul, and): 4 ops [D, Codex audit 2026-11-06]."""
    return (3 ** j) * (bits >> j) / 4 * 4


LIMB_BYTES = {"int8": 1.0, "fp8": 1.0, "fp4": 0.5}


def promote_ops(n_acc, P, m, kind, n_products):
    """SIMT cost of moving FP partials into INT32 every K_p products (K_p*P < 2^m), scale (doubled E2M1 digits are
    physical d/2, so products are d_i d_j / 4: one FMUL), cvt, IADD per accumulator per promotion."""
    if kind == "int8":
        return 0.0
    kp = (2 ** m - 1) // P
    per = 3 if kind == "fp4" else 2
    return n_acc * per * n_products / kp


def inner_product(field, kind, N, m=14, storage="canonical"):
    """<v,u> as V^T U (TensorZKP eq. 15): (kL x N) x (N x kL); lazy reduction once per chunk.
    storage 'canonical': HBM holds 32-bit coefficients, every read is encoded to limbs on SIMT;
    storage 'limb': HBM holds the limbs (kL x LIMB_BYTES bytes per element), no encode on read."""
    eb = elem_bytes(field)
    pr, k = FIELDS[field]
    if pr is None:   # GF(2): bits as 0/1 operands; outer-product sum S = sum a b^T then a fixed bilinear map
        bits, j = k, kar_depth(k)
        macs = kar_macs(bits, j) * N
        blk = math.inf if kind in ("int8", "b1") else block_len(1, "fp", m)
        simt = N * 2 * (kar_xor_ops(bits, j) + (0 if kind == "b1" else unpack_ops(bits, j)))
        return dict(macs=macs, bytes=2 * N * eb, simt=simt, block=blk, P=1, M=bits >> j, Nd=bits >> j)
    lay = prime_layout(field, kind)
    macs = lay["kL"] ** 2 * N
    blk = block_len(lay["P"], lay["acc"], m)
    by = 2 * N * (eb if storage == "canonical" else lay["kL"] * LIMB_BYTES[kind])
    simt = 0 if storage == "limb" else 2 * N * lay["kL"] * lay["enc"]
    simt += promote_ops(lay["kL"] ** 2, lay["P"], m, kind, N)
    simt += (lay["kL"] ** 2) * 4 * math.ceil(N / min(blk, N))     # per-chunk recombination
    return dict(macs=macs, bytes=by, simt=simt, block=blk, P=lay["P"], M=lay["kL"], Nd=lay["kL"])


def fold(field, kind, N, m=14, layout="matrix", storage="canonical"):
    """f' = f_e + r (f_o - f_e) for N outputs.  layout 'tzkp': V x C with C (kL x 4kL) as TensorZKP eq. 19;
    layout 'matrix': r precomputed as the k x k base-field matrix of multiply-by-r, limb-expanded
    (kL x k(2L-1)), so the extension reduction is folded into the matrix [INFERRED; one operand known]."""
    eb = elem_bytes(field)
    pr, k = FIELDS[field]
    rd = 3 * N * eb      # read f_e, f_o, write f'
    if pr is None:   # multiply-by-r is GF(2)-linear; Karatsuba over the tower: 3^j fixed sub-scalars
        bits, j = k, kar_depth(k)
        simt = N * (2 * kar_xor_ops(bits, j) + (0 if kind == "b1" else unpack_ops(bits, j)) + bits / 32)
        return dict(macs=kar_macs(bits, j) * N, bytes=rd, simt=simt, block=bits >> j, P=1, per_acc=bits >> j)
    lay = prime_layout(field, kind)
    L, kL = lay["L"], lay["kL"]
    if layout == "tzkp":
        cols = 4 * kL
        per_acc = k * L                  # a degree-d coefficient's limb position sums over s+t=d and limb pairs
        post = (2 * k - 1) * ((2 * L - 1) + 6) + (k - 1) * 8
    else:
        cols = k * (2 * L - 1)
        per_acc = k * L                  # sum over k coefficients and <= L limb pairs at one position
        post = k * ((2 * L - 1) + 6)
    enc_in = 0 if storage == "limb" else 2 * kL * lay["enc"]
    enc_out = kL * lay["enc"] if storage == "limb" else 0
    simt = N * (post + enc_in + enc_out + k * 2)       # recombine + reduce, encode, f_o - f_e
    if storage == "limb":
        rd = 3 * N * kL * LIMB_BYTES[kind]
    assert per_acc * lay["P"] < (2 ** 31 if lay["acc"] == "int-wrap" else 2 ** m), (field, kind, layout, m)
    return dict(macs=kL * cols * N, bytes=rd, simt=simt, block=per_acc, P=lay["P"], per_acc=per_acc)


def sumcheck_round(field, kind, t, d, m=14, storage="canonical"):
    """One round over d multilinears of 2t entries each, points method: S(x) at d+1 points.
    SIMT: f_j(x) = f_e + x (f_o - f_e) for x >= 2 (adds for small integer x in a prime field; one
    multiply-by-constant in char 2), then (d-2) Hadamard products per point; MMA: (d+1) inner products of
    length t; then d folds.  Unfused: evaluation pass reads all tables, fold pass reads and writes."""
    pts = d + 1
    if FIELDS[field][0] is None:
        ip, fo = inner_product(field, kind, t, m), fold(field, kind, t, m)
    else:
        ip, fo = inner_product(field, kind, t, m, storage), fold(field, kind, t, m, storage=storage)
    eb = ip["bytes"] / (2 * t)
    had = max(0, d - 2) * pts * t * simt_mult_ops(field)
    pr, k = FIELDS[field]
    lin = d * (pts - 2) * t * (2 * k if pr else 8 * k / 32)   # small-integer x (prime) / fixed x (char 2)
    return dict(macs=pts * ip["macs"] + d * fo["macs"],
                bytes=d * 2 * t * eb + d * fo["bytes"],
                simt=had + lin + pts * ip["simt"] + d * fo["simt"],
                block=min(ip["block"], fo["block"]))


def sumcheck(field, kind, mu, d, m=14, storage="canonical"):
    tot = dict(macs=0, bytes=0, simt=0)
    for i in range(1, mu + 1):
        r = sumcheck_round(field, kind, 2 ** (mu - i), d, m, storage)
        for x in tot:
            tot[x] += r[x]
    tot["launches"] = 2 * mu
    return tot


def tzkp_sumcheck_deg2(mu):
    """TensorZKP Algorithm 1 literally (1250.txt:505-536): per round 4 inner products <f_a, g_b>, a,b in {e,o}, and
    each of f, g folded by TWO scalar-vector products plus an add.  Bytes under the fused-read schedule (one pass
    reads f_e, f_o, g_e, g_o for all four products; one pass per vector reads both halves and writes the fold);
    the paper does not publish its schedule, and four separately streamed products would cost 15.03 GB."""
    tot = dict(macs=0, bytes=0, simt=0, launches=2 * mu)
    sv = fold("BabyBear^8", "int8", 1, layout="tzkp")
    for i in range(1, mu + 1):
        t = 2 ** (mu - i)
        tot["macs"] += 4 * 1024 * t + 2 * 2 * sv["macs"] * t
        tot["bytes"] += 4 * t * 32 + 2 * 3 * t * 32
        tot["simt"] += 2 * 2 * sv["simt"] * t
    return tot


# Keccak-f[1600] on SIMT, 32-bit lanes with LOP3 and funnel shifts [D]:
#   theta: C = 5-way xor (2 LOP3 per half-lane x 5 lanes x 2) = 20; A ^= C[x-1] ^ rot1(C[x+1]): 50 LOP3 + 10 SHF
#   rho: 24 lanes x 2 SHF = 48; pi: renaming; chi: 1 LOP3 per half-lane = 50; iota 2.  180 per round x 24.
KECCAK_F_OPS = 24 * (20 + 50 + 10 + 48 + 50 + 2)
# theta is the only linear step that does arithmetic (rho, pi permute bits; iota is affine).  As a dense GF(2) GEMM: 1600 x 1600 bit-MACs per state per round (11 ones per row).
KECCAK_THETA_MACS = 1600 * 1600 * 24


def merkle_layer(n_nodes):
    """One cSHAKE256 node layer of the Tower256 controller: 131 data bytes < rate 136, so 1 Keccak-f per node
    [READ: TOWER256-FRI-PROVER-WORK.md section 2]; reads two 32-byte children, writes one."""
    return dict(macs=0, bytes=96 * n_nodes, simt=KECCAK_F_OPS * n_nodes, block=None,
                theta_as_gemm_macs=KECCAK_THETA_MACS * n_nodes)


def ntt_layer(n, layer, subfield_bits=256, kind="int8", tile_m=64):
    """One additive-NTT butterfly layer over Tower256: n/2 butterflies u' = u + t v, v' = v + u'.  Twiddles are
    fixed per block; at layer `layer` (0 = finest) each twiddle is shared by 2^layer butterflies.  A twiddle in a
    subfield GF(2^s) acts block-diagonally: 256/s identical s x s blocks, so 256*s bit-MACs per butterfly instead
    of 65,536.  A twiddle group smaller than the MMA's M dimension pads (utilisation < 1)."""
    s = subfield_bits
    share = 2 ** layer
    groups = (n // 2) // share
    rows = share * (256 // s)              # M dimension of one twiddle's GEMM
    util = rows / (math.ceil(rows / tile_m) * tile_m)
    macs = (n // 2) * 256 * s
    tw_bytes = groups * (s * s // 8)       # one s x s bit matrix per distinct twiddle
    return dict(macs=macs, macs_issued=macs / util, util=util, bytes=4 * 32 * (n // 2) + tw_bytes,
                simt=(n // 2) * (256 / 32) * 4, block=s)


# ------------------------------------------------------------------------------------------------
# 4. Floors
# ------------------------------------------------------------------------------------------------
def rate(sku, kind):
    s = SKUS[sku]
    return s.get(kind)


def floor_s(sku, kind, c, macs_key="macs"):
    s = SKUS[sku]
    r = rate(sku, kind)
    terms = {"hbm": c["bytes"] / s["bw"], "simt": c["simt"] / s["simt"]}
    terms["tc"] = (c[macs_key] / r) if (c[macs_key] and r) else (math.inf if c[macs_key] else 0.0)
    b = max(terms, key=terms.get)
    return terms[b], b, terms


# ------------------------------------------------------------------------------------------------
# 5. Validation
# ------------------------------------------------------------------------------------------------
def validate():
    ok = True
    print("VALIDATION 1: mma-field-mapping (degg-research RESULTS.txt) reproduced")
    exp = {("int8", "BabyBear"): (4, 16, 65025, 33025), ("fp8", "BabyBear"): (8, 64, 225, 9544371),
           ("fp4", "BabyBear"): (9, 81, 64, 33554431), ("int8", "Goldilocks"): (8, 64, 65025, 33025)}
    for (kind, pr), (L, P2, mp, n31) in exp.items():
        _, base, ds, _, _ = SCHEMES[kind]
        Lg, md = limbs(PRIMES[pr], base, ds)
        got = (Lg, Lg * Lg, md * md, I32 // (md * md))
        flag = "ok" if got == (L, P2, mp, n31) else "MISMATCH"
        ok &= flag == "ok"
        print(f"  {pr:10} {kind:5} L={got[0]} products={got[1]} max|ab|={got[2]} N<2^31={got[3]}  {flag}")
    for kind, m, want in (("fp4", 24, 262143), ("fp4", 14, 255), ("fp8", 14, 72)):
        _, base, ds, _, _ = SCHEMES[kind]
        md = limbs(PRIMES["BabyBear"], base, ds)[1]
        got = block_len(md * md, "fp", m)
        ok &= got == want
        print(f"  BabyBear   {kind:5} m={m}: N={got} (want {want})")
    be4 = 81 / 16
    print(f"  FP4 break-even vs INT8: {be4:.2f} (want 5.06); FP8: {64 / 16:.2f} (want 4.00)")
    print("  TensorZKP eq. 23: N*(255)^2 < 2^31-1 gives N_max =", I32 // 65025,
          "; unsigned reading of the same .s32 register:", (2 ** 32 - 1) // 65025,
          "; parity reading (GF(2)): unbounded")
    for kind, m in (("fp4", 14), ("fp8", 14), ("fp4", 7)):
        ps = product_set(kind)
        P = max(ps)
        print(f"  {kind} encoder products (max {P}), m={m}: bound N <= {(2 ** m - 1) // P}, first failing length "
              f"{first_failure(ps, m)} (exact search over reachable sums)")

    print("\nVALIDATION 2: TensorZKP 2026/1250 primitives, H100, BabyBear^8 (32 B/element), N = 2^25")
    N = 2 ** 25
    sv = fold("BabyBear^8", "int8", N, layout="tzkp")
    sv = dict(sv, bytes=sv["bytes"] * 2 / 3)    # z = c*v: one stream in, one out (a fold reads two)
    rows = [("inner product", inner_product("BabyBear^8", "int8", N), 0.85),
            ("scalar-vector (their layout)", sv, 0.91),
            ("deg-2 sumcheck, Alg. 1 literal [schedule A]", tzkp_sumcheck_deg2(25), 4.04)]
    zc = sumcheck("BabyBear^8", "int8", 25, 3)
    zc7 = dict(zc)
    zc7["bytes"] = zc["bytes"] * 7 / 3        # HyperPlonk gate: q_A, q_M, q_O, w_a, w_b, w_c, eq [A]
    zc7["simt"] = zc["simt"] * 7 / 3
    rows.append(("zero-check [A: 7 tables; NOT a check]", zc7, 16.96))
    for name, c, meas in rows:
        f, b, terms = floor_s("H100", "int8", c)
        launch = c.get("launches", 1) * 5e-6
        pred = f + launch
        print(f"  {name:32} floor {f * 1e3:6.3f} ms ({b}-bound; tc {terms['tc'] * 1e3:.3f}, simt "
              f"{terms['simt'] * 1e3:.3f})  +launch {launch * 1e3:.2f}  measured {meas:6.2f} ms  "
              f"measured/pred {meas / (pred * 1e3):.2f}")
    print("  reading: inner product and scalar-vector are consistent with HBM-bound kernels; the tensor cores run at "
          f"{100 * (inner_product('BabyBear^8', 'int8', N)['macs'] / SKUS['H100']['int8']) / 0.85e-3:.1f}% of INT8 peak "
          "in the inner product. The end-to-end 215.28 ms is NOT reproduced: perm-check (134 ms) is a GKR product")
    print("  argument whose layer schedule the paper does not give at count level.")
    print("  MEASURED on H100 by initiative 17 (paid-h100-mma-03): the same INT8 inner product at 2^25, plane layout,")
    print("  0.734 ms = 0.97 of the measured copy bandwidth (3.03 TB/s): the HBM-bound classification holds, and")
    print("  TensorZKP's 0.85 ms sits 1.16x above a kernel that runs at copy speed.")
    print("\nVALIDATION 3: DATE'26 SumCATS (GF(2^128), bit-sliced SIMT, A100): n=24 d=2 measured 108.65 ms")
    c = sumcheck("GF2^128", "b1", 24, 2)
    f, b, terms = floor_s("A100", "b1", c)
    print(f"  model, same GPU, GF(2) on b1 tensor cores: floor {f * 1e3:.2f} ms ({b}-bound) -> the published SIMT")
    print(f"  kernel is {108.65e-3 / f:.0f}x above this floor.  This shows how far the SIMT kernel sits from HBM; whether an")
    print("  MMA mapping closes the gap is what the GPU protocol measures (SumCATS also works over small base fields).")
    return ok


# ------------------------------------------------------------------------------------------------
# 6. Tables
# ------------------------------------------------------------------------------------------------
def exactness_table():
    print("\nEXACTNESS PER SHAPE (block = products summed into one accumulator before reduction/promotion)")
    print(f"  {'kind':26} {'shape (PTX)':34} {'acc':22} {'P':>6} {'block':>12}")
    rows = [
        ("u8 limbs, signed read", "mma m16n8k32 / wgmma m64nNk32", "s32 wrap", 65025, block_len(65025, "int-wrap")),
        ("u8 limbs, unsigned read", "same", "s32 wrap", 65025, block_len(65025, "int-wrap", reading="unsigned")),
        ("0/1 bits (GF(2)), s8", "same", "s32 wrap, parity", 1, "unbounded"),
        ("b1 AND.popc (GF(2))", "mma m16n8k256 / wgmma m64nNk256", "s32 wrap, parity", 1, "unbounded"),
        ("e4m3 base-16 limbs", "wgmma m64nNk32 (H100)", "fp, 12<=m<=23 (PTX 9.2)", 225,
         f"{block_len(225, 'fp', 12)}..{block_len(225, 'fp', 23)}"),
        ("e4m3 base-16 limbs", "wgmma, m=14 (DeepSeek-V3)", "fp m=14", 225, block_len(225, "fp", 14)),
        ("e2m1 base-13 limbs", "tcgen05 kind::f8f6f4 (B200/B300)", "fp, m unpublished", 64,
         f"m=14: {block_len(64, 'fp', 14)}, m=24: {block_len(64, 'fp', 24)}"),
        ("e2m1 base-13 + int promote", "every K_p <= 255 products at m=14", "s32 after cvt", 64, I32 // 64),
        ("0/1 bits on e2m1/e4m3", "tcgen05 (no b1 kind on sm_100/103)", "fp m", 1,
         f"m=14: {block_len(1, 'fp', 14)}, m=24: {block_len(1, 'fp', 24)}"),
    ]
    for r in rows:
        print(f"  {r[0]:26} {r[1]:34} {r[2]:22} {r[3]:>6} {str(r[4]):>12}")
    print("  folds by a known challenge (matrix layout) sum <= k*L products per accumulator:"
          f" BabyBear^8 int8 {8 * 4}, fp8 {8 * 8}, fp4 {8 * 9} -> all exact even at m=14 (64*225=14400 < 16384).")


def pareto_table(N=2 ** 25):
    print(f"\nSUMCHECK, degree 2, mu = {int(math.log2(N))} (all rounds), floor per SKU x field x kind [proxy]")
    print("  storage: c = canonical 32-bit coefficients in HBM (encode on every read), l = limbs in HBM (no encode on")
    print("  read, more bytes for fp8; folds re-encode their outputs).  FP partials promoted to INT32 at m=14.")
    print(f"  {'SKU':5} {'field':13} {'kind':5} {'st':2} {'MACs':>9} {'GB':>6} {'Gop':>7} {'floor ms':>9} {'bound':>5}")
    out = []
    for sku in SKUS:
        for field in FIELDS:
            for kind in ("int8", "fp8", "fp4", "b1"):
                pr = FIELDS[field][0]
                if pr is None and kind == "fp8" or (pr is not None and kind == "b1"):
                    continue
                if rate(sku, kind) is None:
                    continue
                if pr is None and kind not in ("int8", "b1", "fp4"):
                    continue
                for st in (("canonical", "limb") if pr is not None and kind != "int8" else ("canonical",)):
                    c = sumcheck(field, kind, int(math.log2(N)), 2, storage=st)
                    f, b, _ = floor_s(sku, kind, c)
                    out.append((sku, field, kind, st, c, f, b))
                    print(f"  {sku:5} {field:13} {kind:5} {st[0]:2} {c['macs']:9.2e} {c['bytes'] / 1e9:6.2f} "
                          f"{c['simt'] / 1e9:7.2f} {f * 1e3:9.3f} {b:>5}")
        # SIMT-only reference row for the same field set
    print("  SIMT-only reference (no MMA; every product a SIMT ext mult):")
    for sku in ("H100", "B300"):
        for field in ("BabyBear^8", "Tower256"):
            c = sumcheck(field, "int8", int(math.log2(N)), 2)
            ext = sum(2 ** (int(math.log2(N)) - i) * (3 + 2) for i in range(1, int(math.log2(N)) + 1))
            simt = ext * simt_mult_ops(field)
            f = max(c["bytes"] / SKUS[sku]["bw"], simt / SKUS[sku]["simt"])
            print(f"  {sku:5} {field:13} simt  {simt / 1e9:7.2f} Gop  floor {f * 1e3:8.3f} ms")
    return out


def tower_prover(ell_list=(14, 16, 20, 22), lb=2, mult_scale=1.0):
    """Tower256 additive-FRI prover (one column).  Hash: ~4*2^ell Keccak-f [READ: work item section 2].
    Encode: additive NTT of 2^ell points, (n/2)*ell butterflies; folds: sum_j 2*2^(ell-j-1) fixed-r mults."""
    print(f"\nTOWER256 ADDITIVE-FRI PROVER (one column, lb=2): what tensor cores can buy [proxy]; SIMT Tower256 "
          f"multiply = {mult_scale:g} x {simt_mult_ops('Tower256'):.0f} ops [A]")
    print(f"  {'SKU':4} {'kind':4} {'ell':>3} {'Keccak-f':>10} {'hash ms':>8} {'arith SIMT':>10} "
          f"{'arith TC':>8} {'TC, GF(2^32) basis':>18} {'hash share':>10} {'ceiling':>8}")
    for sku, kind in (("H100", "int8"), ("B300", "fp4")):
        s = SKUS[sku]
        for ell in ell_list:
            n, m = 2 ** ell, ell - lb - 2
            kf = 4 * n
            h = kf * KECCAK_F_OPS / s["simt"]
            n_mults = (n // 2) * ell + sum(2 * 2 ** (ell - j - 1) for j in range(m))
            arith_simt = n_mults * mult_scale * simt_mult_ops("Tower256") / s["simt"]
            def arith_tc(sub):
                t = 0.0
                for layer in range(ell):
                    c = ntt_layer(n, layer, sub)
                    t += floor_s(sku, kind, dict(c, macs=c["macs_issued"]))[0]
                for j in range(m):
                    t += floor_s(sku, kind, fold("Tower256", kind, 2 ** (ell - j - 1)))[0]
                return t
            tc256, tc32 = arith_tc(256), arith_tc(32)
            best = min(arith_simt, tc256, tc32)
            print(f"  {sku:4} {kind:4} {ell:3d} {kf:10,d} {h * 1e3:8.3f} {arith_simt * 1e3:10.3f} "
                  f"{tc256 * 1e3:8.3f} {tc32 * 1e3:18.3f} {h / (h + arith_simt):10.2f} "
                  f"{(h + arith_simt) / (h + best):7.2f}x")
    s = SKUS["H100"]
    print("  Keccak theta as a dense GF(2) GEMM costs", f"{KECCAK_THETA_MACS:.2e}",
          "bit-MACs per Keccak-f against", KECCAK_F_OPS, "SIMT ops for the whole permutation:",
          f"{KECCAK_THETA_MACS / s['int8'] / (KECCAK_F_OPS / s['simt']):.0f}x slower even at INT8 peak. MMA share of the hash = 0.")
    print("  ceiling = (hash + arith on SIMT) / (hash + best arith); the hash stays on SIMT in every column.")
    print("  arithmetic-free bound (Amdahl) = 1/hash share.  The hash share is MODELLED from two assumed op counts")
    print("  (Keccak-f 4,320; Tower256 multiply above), not measured; NTT passes are unfused (one HBM trip per layer).")


def ntt_table(ell=20):
    print(f"\nADDITIVE NTT over Tower256, n = 2^{ell}, per layer (INT8 0/1 operands, M tile 64) [proxy, H100]")
    s = SKUS["H100"]
    for sub in (256, 32, 16):
        tot = 0.0
        worst = None
        for layer in range(ell):
            c = ntt_layer(2 ** ell, layer, sub)
            c2 = dict(c, macs=c["macs_issued"])
            f, b, _ = floor_s("H100", "int8", c2)
            tot += f
            if layer in (0, 5, ell - 1):
                worst = (worst or []) + [(layer, round(c["util"], 3), b)]
        simt_ref = ell * (2 ** ell // 2) * simt_mult_ops("Tower256") / s["simt"]
        print(f"  twiddles in GF(2^{sub:<3}): {tot * 1e3:7.3f} ms over {ell} layers "
              f"(layers (i, util, bound): {worst}); SIMT bit-sliced reference {simt_ref * 1e3:.3f} ms")


# ================================================================================================
# 7. THE ROTATION (2026-11-06, after the T4 dry run): per target, the fastest exact-integer datapath that
#    actually exists, and each workload re-mapped onto it.  Evidence: notes/accelerator-readiness/MMA.md.
# ================================================================================================
# Per target and datapath: dense MAC/s, accumulator class, m (integer-exact width), status tag.
#   m=24 "spec": PTX says f16/bf16 accumulate "at least single precision" [READ]; T4 HMMA integer-addend C path
#   measured exact through 2^24 [MEASURED: MMA.md section 4].  FP8 on Hopper: "higher than half, lower than
#   single" [READ PTX 9.2], m unmeasured (12..23, 14 at DeepSeek).  tcgen05 f8f6f4/mxf4: unpublished.
#   "emulated" = the SASS census shows a software sequence, not a tensor instruction [MEASURED: MMA.md section 3].
TARGETS = {
    "T4": dict(bw=2.42e11, simt=40 * 64 * 1.59e9, paths={
        "int8": (6.28e13, "int", 31, "MEASURED mma.sync m8n8k16"),
        "fp16": (0.48 * 6.28e13, "fp", 24, "MEASURED HMMA, m=24 measured"),
        "b1x": (7.94 * 6.28e13, "int", 31, "MEASURED BMMA xor.popc (GF(2) via xor identity)")}),
    "A100": dict(bw=2.039e12 * 0.75, simt=108 * 64 * 1.41e9, paths={
        "int8": (624e12 / 2, "int", 31, "X datasheet"),
        "fp16": (312e12 / 2, "fp", 24, "X datasheet; PTX: multiply and accumulate at least single precision"),
        "bf16": (312e12 / 2, "fp", 24, "X datasheet; product precision 16 bits UNVERIFIED (PTX: specified precision)"),
        "b1": (4992e12 / 2, "int", 31, "X datasheet; BMMA and/xor native (SASS)")}),
    "H100": dict(bw=3.03e12, simt=16.7e12, paths={
        # [MEASURED paid-h100-mma-03, 2026-11-07]: copy 3.03 TB/s read+write; wgmma rates; QGMMA m=14
        # (exact through 2^14, inexact from 2^14.5); HGMMA m=24; bias read passes on QGMMA m=12..14, fails m=24.
        "int8": (9.999e14, "int", 31, "MEASURED wgmma IGMMA 1.00e15 (cuBLAS 8192^3 6.96e14)"),
        "fp8": (8.82e14, "fp", 14, "MEASURED wgmma QGMMA 8.82e14, m=14 MEASURED (cuBLASLt fast-accum off: 0/1 exact to K=2^20)"),
        "fp16": (4.54e14, "fp", 24, "MEASURED wgmma HGMMA 4.54e14, m=24 MEASURED"),
        "b1": (7.988e15, "int", 31, "MEASURED wgmma BGMMA and.popc 7.99e15 = 8.0x IGMMA")}),
    "B200": dict(bw=8.0e12 * 0.75, simt=148 * 128 * 1.9e9, paths={
        "int8": (4.5e15 / 2, "int", 31, "X 2608.11693"),
        "fp8": (4.5e15 / 2, "fp", 14, "X; tcgen05 m UNPUBLISHED (placeholder = Hopper QGMMA measured 14)"),
        "fp4": (9e15 / 2, "fp", 14, "X; tcgen05 m UNPUBLISHED (placeholder 14)"),
        "fp16": (2.25e15 / 2, "fp", 24, "X; m=24 [A for tcgen05: no precision text found]"),
        "b1": (None, "int", 31, "EMULATED (SASS: CALL + IMMA)")}),
    "B300": dict(bw=7.7e12 * 0.75, simt=160 * 128 * 1.9e9, paths={
        "int8": (0.15e15 / 2, "int", 31, "X 2608.11693: FP8/30, no kind::i8 on sm_103a"),
        "fp8": (4.5e15 / 2, "fp", 14, "X; tcgen05 m UNPUBLISHED (placeholder = Hopper QGMMA measured 14)"),
        "fp4": (14e15 / 2, "fp", 14, "X HGX B300 datasheet 14 P dense (mxf4 kind); tcgen05 m UNPUBLISHED (placeholder 14)"),
        "fp16": (2.25e15 / 2, "fp", 24, "X 4.5 P sparse / 2; m=24 [A for tcgen05: no precision text found]"),
        "b1": (None, "int", 31, "EMULATED")}),
    "TPUv5e": dict(bw=8.19e11 * 0.75, simt=None, paths={
        "int8": (394e12 / 2, "int", 31, "X Google spec; int32 accumulate, overflow semantics UNVERIFIED"),
        "bf16": (197e12 / 2, "fp", 24, "X Google: bf16 multiply, f32 accumulate; m=24 [A, unmeasured]")}),
    "TPUv6e": dict(bw=1.64e12 * 0.75, simt=None, paths={
        "int8": (1836e12 / 2, "int", 31, "X Google spec [A int8 rate]"),
        "bf16": (918e12 / 2, "fp", 24, "X Google spec; m=24 [A]")}),
}
# bw carries a 0.75 copy-efficiency factor: T4 measured 0.75-0.76 of datasheet copy (MMA.md section 4) [A elsewhere].

# Exact operand classes: max |integer| the format holds exactly, and limb base for BabyBear.
#   int8: u8 limbs base 256 (P 65025) or 0/1; fp16: integers <= 2048 -> base 256 limbs (P 65025);
#   bf16: integers <= 256 -> base 256 limbs (P 65025); fp8 e4m3: integers <= 16 -> base 16 (P 225);
#   fp4 e2m1 doubled: base 13 gapped (P 64); b1: bits.
ROT_LIMB = {"int8": (4, 65025, 0.0), "fp16": (4, 65025, 1.0), "bf16": (4, 65025, 1.0),
            "fp8": (8, 225, 1.0), "fp4": (9, 64, 4.0)}   # (limbs per 31-bit base element, P, SIMT encode ops/limb [A])
LIMB_B = {"int8": 1, "fp16": 2, "bf16": 2, "fp8": 1, "fp4": 0.5}
# operand expansion for 0/1 operands from packed bits, SIMT ops per operand [D/A]:
#   int8 0/1: nibble extract + (v*0x00204081)&0x01010101 = 4 ops / 4 operands; fp8 adds *0x38 (e4m3 1.0);
#   fp16/bf16: 2-byte operands, 2x the words; fp4 e2m1: 8 nibbles per word, ~5 ops per 8 [A]; b1: none.
UNPACK01 = {"int8": 1.0, "fp8": 1.25, "fp16": 2.0, "bf16": 2.0, "fp4": 0.625, "b1": 0.0, "b1x": 0.0}
# parity repack per output bit: m>=24 path: accumulator initialised to 2^23 so the raw low mantissa bit IS the
# parity (needs count < 2^23), then and + ballot: 2 ops/bit; m<24 or int: cvt/and + ballot: 2-3 ops/bit [D].
# Generalised bias (Codex audit): initialise the FP32 accumulator to 2^(m-1), keep the count below 2^(m-1), and the
# raw bit (24 - m) of the register is the parity (m <= 24, given the exactness premise): and + ballot = 2 ops/bit for
# every m; the price is a halved block (2^(m-1) - 1).  Fragment-to-packed-word layout is NOT costed [A].
REPACK = {"fp": 2.0, "int": 2.0, "fp-m14": 2.0}


def block_exact(acc, m, P, reading="signed"):
    if acc == "int":
        return math.inf if reading == "parity" else I32 // P
    return (2 ** m - 1) // P


def best_rate(tgt, kinds):
    T = TARGETS[tgt]["paths"]
    return [(k, T[k]) for k in kinds if k in T and T[k][0]]


def rot_datapaths():
    print("\nROTATION 1: per target, the exact-integer datapaths that exist (dense MAC/s; exact block per accumulator)")
    print(f"  {'target':7} {'path':5} {'MAC/s':>9} {'acc':4} {'m':>3} {'blk BB limbs':>12} {'blk 0/1':>10} {'status'}")
    for tgt, T in TARGETS.items():
        for k, (r, acc, m, tag) in T["paths"].items():
            P = ROT_LIMB.get(k, (0, 1, 0))[1]
            bl = block_exact(acc, m, P) if k in ROT_LIMB else "-"
            b01 = "inf (parity)" if acc == "int" else f"{2 ** m - 1:,}"
            rs = f"{r:9.2e}" if r else "  unmeas."
            print(f"  {tgt:7} {k:5} {rs} {acc:4} {m:3d} {str(bl):>12} {b01:>10} {tag}")
    print("  0/1 column: parity read; with promotion by parity XOR every block it is exact at every length.  Integer limb")
    print("  totals promoted by cvt + iadd.s32 stay bounded by the INT32 total (33,025 u8 products) unless reduced")
    print("  mod p or widened.  H100 QGMMA m=14 and HGMMA m=24 are MEASURED (paid-h100-mma-03); tcgen05 has no")
    print("  precision text, so Blackwell FP8/FP4 carry 14 as a placeholder until the B200 hour.  bf16 byte limbs need 16-bit products,")
    print("  which PTX does not promise for bf16 ('specified precision'); fp16 byte limbs are promised (single precision).")


def rot_prime(N=2 ** 25, k=8):
    """(a) BabyBear^k degree-2 sumcheck at 2^mu, best exact datapath per target.  Inner products + matrix folds;
    canonical storage (32-bit coefficients) with SIMT encode on read; promotion SIMT per block."""
    print(f"\nROTATION 2a: BabyBear^{k} degree-2 sumcheck, 2^{int(math.log2(N))} (canonical storage; floor = max of HBM, TC, SIMT)")
    out = {}
    for tgt, T in TARGETS.items():
        rows = []
        for kind, (r, acc, m, tag) in T["paths"].items():
            if kind not in ROT_LIMB or not r:
                continue
            L, P, enc = ROT_LIMB[kind]
            kL = k * L
            blk = block_exact(acc, m, P)
            # per round t: 3 inner products (S(0), S(1), S(2) via f(2) on SIMT) of kL^2 MACs/pair; 2 folds of
            # kL x k(2L-1) MACs/element; bytes 128 t (4 half-vectors) + 2 x 96 t (folds); SIMT encode on read
            # (4 vectors x kL limbs x enc), promotion, fold recombine (k(2L-1+6)) + re-encode.
            tot = dict(macs=0.0, bytes=0.0, simt=0.0)
            for i in range(1, int(math.log2(N)) + 1):
                t = 2 ** (int(math.log2(N)) - i)
                tot["macs"] += t * (3 * kL * kL + 2 * kL * k * (2 * L - 1))
                tot["bytes"] += t * (4 * 4 * k + 2 * 3 * 4 * k)
                prom = 0 if acc == "int" else 2 * (3 * kL * kL) / max(1, min(blk, 1 << 30))
                tot["simt"] += t * (4 * kL * enc + 2 * kL * enc + prom + 2 * k * (2 * L - 1 + 6) + 2 * kL * enc)
            terms = {"hbm": tot["bytes"] / T["bw"], "tc": tot["macs"] / r}
            if T["simt"]:
                terms["simt"] = tot["simt"] / T["simt"]
            b = max(terms, key=terms.get)
            # tie-break HBM-bound ties by headroom: the smaller non-HBM term wins
            rows.append((terms[b], max(v for k_, v in terms.items() if k_ != "hbm"), kind, b, blk, tag))
        rows.sort()
        rows = [(f, k_, b_, bl_, tg_) for f, _, k_, b_, bl_, tg_ in rows]
        best = rows[0]
        out[tgt] = best
        alts = ", ".join(f"{k_} {f * 1e3:.2f} ({b_})" for f, k_, b_, _, _ in rows[1:])
        print(f"  {tgt:7} best {best[1]:5} {best[0] * 1e3:7.3f} ms ({best[2]}-bound, block {best[3]}); others: {alts}")
    print("  TPU rows have no VPU term (encode/promotion unmodelled there).")
    return out


def tower_ip_cost(kind, acc, m, macs_rate, simt_rate, bw, kar=True):
    """Tower256 inner product per element pair: Karatsuba to 16-bit pieces (81 x 16 x 16 bit-MACs) when operands
    are packed bits (b1); dense 256 x 256 when they must be unpacked (fewer operands to expand: 256 vs 1,296)."""
    cands = []
    for kar_ in ((True,) if kind.startswith("b1") else (False, True)):
        if kar_:
            macs, unpack = 81 * 256, 2 * kar_xor_ops(256, 4) + (0 if kind.startswith("b1") else 2 * 1296 * UNPACK01[kind])
        else:
            macs, unpack = 256 * 256, 2 * 256 * UNPACK01[kind]
        # promotion: per accumulator per block (cvt/and/xor = 3 ops) when the block is finite (fp paths)
        blk = (2 ** (m - 1) - 1) if acc == "fp" else math.inf
        prom = 0.0 if blk == math.inf else 3 * macs / blk
        t = {"tc": macs / macs_rate, "simt": (unpack + prom) / simt_rate if simt_rate else 0.0, "hbm": 64 / bw}
        cands.append((max(t.values()), t))
    return min(cands, key=lambda c: c[0])


def tower_lin_cost(kind, acc, m, macs_rate, simt_rate, bw):
    """Tower256 multiply by a FIXED element (fold by r, NTT twiddle): dense 256 x 256 GF(2) matrix (B operand,
    expanded once), A operand unpacked per element, 256 counts repacked to bits per element; plus 64 B traffic."""
    macs = 256 * 256
    unpack = 256 * UNPACK01.get(kind, 0.0)
    repack = 256 * (REPACK["fp"] if (acc == "fp" and m >= 24) else (REPACK["int"] if acc == "int" else REPACK["fp-m14"]))
    t = {"tc": macs / macs_rate, "simt": (unpack + repack) / simt_rate if simt_rate else 0.0, "hbm": 96 / bw}
    return max(t.values()), t


# Measured SIMT anchors (T4, notes/accelerator-readiness/TOWER256.md section 4), in T4 int32-op equivalents.
KECCAK_OPS_MEAS = 5900          # 6.9e8 Keccak-f/s on T4 (tune-03); 9,350 at 4.35e8 (dryrun-04)
T256_MUL_TABLE_OPS = 12000      # log/exp GF(2^8) tables: 12,000-17,400 [MEASURED T4, TOWER256.md section 8]
T256_MUL_TABLE_HI = 17400
T256_MUL_BITSLICED_OPS = 52700  # bit-sliced, resident planes, v2 [MEASURED T4, section 8]; fused 71,500
T256_MUL_IDEAL_OPS = 860        # Karatsuba-to-bits instruction count with LOP3 fusion (1,284 two-input) [D, section 8]
T256_MUL_WARPCOOP_EST = 1700    # warp-cooperative bit slicing, readiness lane's estimate [A, unbuilt]


def rot_binary(N=2 ** 25):
    print(f"\nROTATION 2b: Tower256 on the tensor units, per element (ns).  SIMT baselines in T4 op-eq scaled by SIMT rate:")
    print(f"  table {T256_MUL_TABLE_OPS:,}-{T256_MUL_TABLE_HI:,} and bit-sliced {T256_MUL_BITSLICED_OPS:,} [MEASURED T4]; "
          f"ideal instruction count {T256_MUL_IDEAL_OPS} [D, unreachable: 256 planes do not fit 255 registers]")
    print(f"  {'target':7} {'path':5} {'inner product':>14} {'fixed-r mult':>13} {'table (best)':>12} {'ideal':>7} "
          f"{'win vs table':>12} {'vs ideal':>9}  binding")
    res = {}
    for tgt, T in TARGETS.items():
        if not T["simt"]:
            continue
        sm_tbl = T256_MUL_TABLE_OPS / T["simt"]
        sm_bs = T256_MUL_IDEAL_OPS / T["simt"]
        for kind, (r, acc, m, tag) in T["paths"].items():
            if not r or kind in ("fp16",) and tgt not in ("T4",):
                continue
            ip, ipt = tower_ip_cost(kind, acc, m, r, T["simt"], T["bw"])
            ln, lnt = tower_lin_cost(kind, acc, m, r, T["simt"], T["bw"])
            bi = max(ipt, key=ipt.get)
            bl = max(lnt, key=lnt.get)
            res[(tgt, kind)] = (ip, ln, sm_tbl, sm_bs)
            print(f"  {tgt:7} {kind:5} {ip * 1e9:11.3f} ns {ln * 1e9:10.3f} ns {sm_tbl * 1e9:9.3f} ns {sm_bs * 1e9:6.3f}"
                  f" {sm_tbl / ln:10.1f}x {sm_bs / ln:8.2f}x  ip:{bi} lin:{bl}")
    print("  'win' columns compare the fixed-r multiply (the harder case; inner products win by more).  The table")
    print("  and bit-sliced rates are measured on T4 only and scaled by SIMT throughput; the tensor rows are model.")
    return res


def ntt_tensor_layer(tgt, kind, n, layer, tile=64):
    """One additive-NTT layer on the tensor path: the twiddle of a block is shared by 2^layer butterflies, so the
    twiddle matrix (65,536 operand bits, expanded on chip from 8 KiB packed: 65,536 x UNPACK01 SIMT ops) is
    amortised over 2^layer rows and the MMA tile pads to min(1, 2^layer / tile).  Per butterfly: one fixed-r
    multiply (unpack 256 + repack 256 bits), plus the shared matrix."""
    T = TARGETS[tgt]
    r, acc, m, _ = T["paths"][kind]
    share = 2 ** layer
    util = min(1.0, share / tile)
    _, lt = tower_lin_cost(kind, acc, m, r, T["simt"], T["bw"])
    tc = lt["tc"] / util
    simt = lt["simt"] + (65536 * UNPACK01.get(kind, 0.0) / T["simt"]) / share
    hbm = lt["hbm"] + (8192 / share) / T["bw"]
    return max(tc, simt, hbm)


def rot_tower_prover(ells=(14, 20, 22)):
    print("\nROTATION 2c: Tower256 FRI prover (one column) per target, ms per proof [proxy].  Encode = additive NTT with")
    print("  per-layer twiddle reuse (fine layers fall back to SIMT); folds = fixed-r multiplies; hash on SIMT.")
    for tgt, T in TARGETS.items():
        if not T["simt"]:
            continue
        kinds = [k for k, v in T["paths"].items() if v[0]]
        for ell in ells:
            n = 2 ** ell
            kf = 4 * n
            m_ = ell - 4
            h = kf * KECCAK_OPS_MEAS / T["simt"]
            fold_mults = sum(2 * 2 ** (ell - j - 1) for j in range(m_))
            per = lambda ops: ops / T["simt"]
            tbl = ((n // 2) * ell + fold_mults) * per(T256_MUL_TABLE_OPS)
            bs = ((n // 2) * ell + fold_mults) * per(T256_MUL_IDEAL_OPS)
            best_k, best_t = None, math.inf
            for k in kinds:
                enc = sum((n // 2) * min(ntt_tensor_layer(tgt, k, n, L), per(T256_MUL_TABLE_OPS)) for L in range(ell))
                r, acc, m, _ = T["paths"][k]
                fo = fold_mults * tower_lin_cost(k, acc, m, r, T["simt"], T["bw"])[0]
                if enc + fo < best_t:
                    best_k, best_t = k, enc + fo
            tc = best_t
            print(f"  {tgt:5} ell {ell:2d}: hash {h * 1e3:8.3f} | arith: table {tbl * 1e3:8.3f}, tensor({best_k}) "
                  f"{tc * 1e3:7.3f} ({tbl / tc:.1f}x), ideal-SIMT {bs * 1e3:7.3f} | proof: table {(h + tbl) * 1e3:7.3f} -> "
                  f"tensor {(h + tc) * 1e3:7.3f} ({(h + tbl) / (h + tc):.2f}x); hash share {h / (h + tbl):.2f} -> {h / (h + tc):.2f}")


def rot_keccak():
    print("\nROTATION 2c': Keccak-f has no tensor mapping (theta is the only arithmetic linear step; dense GEMM 240x")
    print(f"  slower at INT8 peak).  Bit-sliced SIMT bound: {KECCAK_OPS_MEAS} op-eq per Keccak-f measured on T4 "
          f"(model 4,320). Per target Keccak-f/s:")
    for tgt, T in TARGETS.items():
        if T["simt"]:
            print(f"  {tgt:5} {T['simt'] / KECCAK_OPS_MEAS:.2e}/s")


def rot_mxfp4(M=4096, Nn=4096, K=4096):
    """(d) MXFP4 exact recompute of one GEMM: per 32-block the dot of e2m1 values is an exact multiple of 1/4 with
    |sum| <= 32 x 36 = 1152 (4608 quarter units < 2^13): exact on any accumulator with m >= 13.  Exact path:
    run block dots with unit scales, apply the E8M0 scale pair per block per output on SIMT as an exact integer
    shift-add into a wide (Kulisch-style) accumulator: 2 ops per output per block."""
    print(f"\nROTATION 2d: MXFP4 exact recompute, {M}x{Nn}x{K} GEMM (scales applied exactly on SIMT per 32-block)")
    macs = M * Nn * K
    # per output per 32-block: shift + add-with-carry into a 2-word window of a wide accumulator (the 13-bit block
    # sum spans <= 2 words) = 4 ops [A]; worst case over all finite E8M0 scales needs 529 bits (17 words).
    simt = 4 * M * Nn * (K // 32)
    for tgt in ("B200", "B300", "H100", "A100", "T4"):
        T = TARGETS[tgt]
        # separate 32-blocks need one block per instruction: tcgen05 kind::f8f6f4 (K=32) runs e2m1 at the FP8 rate;
        # the faster mxf4 kind (K=64) merges two differently scaled blocks.  Else FP8 / fp16 (e2m1 values exact).
        k = "fp8" if "fp8" in T["paths"] else "fp16"
        r = T["paths"][k][0]
        tc, sm = macs / r, simt / T["simt"]
        print(f"  {tgt:5} via {k:4}: TC {tc * 1e3:7.3f} ms, SIMT scale-apply {sm * 1e3:7.3f} ms -> "
              f"{max(tc, sm) * 1e3:7.3f} ms ({'SIMT' if sm > tc else 'TC'}-bound)")
    print("  a 32-block's dot is <= 32 x 36 = 1,152 (4,608 quarter-units < 2^13): exact inside any accumulator with")
    print(f"  m >= 13; equal-scale blocks per accumulator before promotion: m=14 -> {(2 ** 14 - 1) // 4608}, m=24 -> {(2 ** 24 - 1) // 4608:,}")
    print("  Faster variant [INFERRED]: mxf4 with hardware scales when, per K-chunk, the scale span s_max - s_min")
    print("  + 13 + log2(chunk/32) < m AND every scaled partial stays inside FP32's normal range (span alone is not")
    print("  enough: equal scales of 2^-127 underflow); certify per tile, fall back to f8f6f4 otherwise.")


def rot_rns_ntt(N=16384, L=4, P=128):
    """(e) BFV RNS NTT, four-step as matrix products (BFV.md section 5b).  int8 / fp16: 8 balanced bytes; the top
    digit of a canonical 61-bit residue is <= 16, so |Y| <= 15,204,352 < 2^24 (Codex): exact at m = 24.  fp8: 16
    balanced nibbles [-8, 7], |Y| <= 124,928 < 2^17: exact at m >= 17, else promote every (2^m - 1) // 64 terms.
    SIMT per output digit-row: carry chain + Barrett-style fold ~ 3 D + 10 ops, plus promotion 3 ops per accumulator
    per block.  MACs per NTT per prime = N1 (D N2)^2 + (D N1)^2 N2."""
    N1 = 64 if N == 8192 else 128
    N2 = N // N1
    print(f"\nROTATION 2e: RNS NTT, N={N}, L={L} primes, batch P={P} polynomials, forward only, four-step N1={N1}")
    for tgt, T in TARGETS.items():
        rows = []
        for kind, (r, acc, m, tag) in T["paths"].items():
            if not r or kind in ("b1", "b1x", "fp4", "bf16"):
                continue
            D = 16 if kind == "fp8" else 8
            macs = (N1 * (D * N2) ** 2 + (D * N1) ** 2 * N2) * L * P
            mat = (N1 * N2 ** 2 + N1 ** 2) * D * D * (1 if kind in ("int8", "fp8") else 2) * L
            data = 2 * P * L * N * 8
            outs = 2 * P * L * N * D                       # two stages, D output digits per coefficient
            Kterm = D * max(N1, N2)
            blk = math.inf if acc == "int" else ((2 ** m - 1) // (64 if kind == "fp8" else 2 ** 14))
            blk = math.inf if (acc == "fp" and kind == "fp8" and m >= 17) or (acc == "fp" and kind != "fp8" and m >= 24) else blk
            prom = 0 if blk == math.inf else outs * 3 * math.ceil(Kterm / blk)
            simt = outs * (3 * D + 10) / D + prom
            terms = {"tc": macs / r, "hbm": (mat + data) / T["bw"]}
            if T["simt"]:
                terms["simt"] = simt / T["simt"]
            t = max(terms.values())
            rows.append((t, kind, max(terms, key=terms.get)))
        rows.sort()
        print(f"  {tgt:7} " + ", ".join(f"{k} {t * 1e3:.3f} ms ({b})" for t, k, b in rows))
    print("  TPU rows: no VPU term.  bf16 excluded (16-bit products unpromised); fp16 carries the byte digits.")


def rotation():
    rot_datapaths()
    rot_prime()
    rot_binary()
    rot_tower_prover()
    rot_keccak()
    rot_mxfp4()
    rot_rns_ntt()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--validate", action="store_true")
    ap.add_argument("--rotation", action="store_true", help="only the per-target rotation tables (section 7)")
    a = ap.parse_args()
    if a.rotation:
        rotation()
        return
    ok = validate()
    if a.validate:
        raise SystemExit(0 if ok else 1)
    exactness_table()
    pareto_table()
    tower_prover()
    tower_prover(mult_scale=4.0)
    ntt_table()
    rotation()
    print("\nSKU sources:")
    for k, v in SKUS.items():
        print(f"  {k}: {v['src']}")
    raise SystemExit(0 if ok else 1)


if __name__ == "__main__":
    main()
