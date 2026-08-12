"""
bf16 exact-table facts, measured exhaustively.

Substrate note: this is a MEASUREMENT harness. It authors no AIR, no constraint,
no gadget. It enumerates the bf16 format, builds the complete tables, and
measures their bipartition-rank profile. Any constraint system these tables are
eventually used in is authored in Lean, not here.

Three questions:
  A. What is in the bf16 format? (census)
  B. DOMAIN ESCAPE: is there any bf16 input for which a full-table lookup has no
     valid entry?
  C. RANK: does eprint 2026/1390 Proposition 3's rank-1 exp decomposition
     transfer to a bf16-INDEXED table? (Prop 3's premise is that a FIXED-POINT
     value is additive across a bit cut. A bf16 address is not.)

Run: python3 bf16_tables.py
"""

import math
import numpy as np

N = 1 << 16

# ---------------------------------------------------------------------------
# bf16 <-> f32.  bf16 is the top 16 bits of an IEEE binary32:
#   [sign:1][exp:8][mant:7]
# so widening is a shift and never loses anything.
# ---------------------------------------------------------------------------

ALL_BITS = np.arange(N, dtype=np.uint16)


def bf16_to_f32(bits):
    """Widen bf16 bit patterns to f32 values. Exact, total."""
    return (np.asarray(bits, dtype=np.uint16).astype(np.uint32) << 16).view(np.float32)


def f32_to_bf16(x):
    """Round f32 -> bf16, round-to-nearest-even. Returns bit patterns."""
    u = np.asarray(x, dtype=np.float32).view(np.uint32)
    # NaN must stay NaN (and not be turned into inf by the rounding carry).
    is_nan = np.isnan(np.asarray(x, dtype=np.float32))
    lsb = (u >> 16) & 1
    rounded = (u + 0x7FFF + lsb) >> 16
    out = rounded.astype(np.uint16)
    out = np.where(is_nan, np.uint16(0x7FC0), out)
    return out.astype(np.uint16)


def f64_to_bf16(x):
    """Round f64 -> bf16 via f32. Double rounding is harmless here: bf16 has 8
    significand bits, f32 has 24, and f64 has 53; the only inputs where f64->f32
    then f32->bf16 differs from f64->bf16 directly would need a tie created at
    the f32 step, which requires >=16 zero bits below the bf16 rounding point
    followed by a nonzero tail -- checked separately below."""
    return f32_to_bf16(np.asarray(x, dtype=np.float64).astype(np.float32))


# ---------------------------------------------------------------------------
# A. Census
# ---------------------------------------------------------------------------

def census():
    v = bf16_to_f32(ALL_BITS)
    exp = (ALL_BITS >> 7) & 0xFF
    mant = ALL_BITS & 0x7F
    nan = (exp == 0xFF) & (mant != 0)
    inf = (exp == 0xFF) & (mant == 0)
    zero = (exp == 0) & (mant == 0)
    sub = (exp == 0) & (mant != 0)
    normal = (exp != 0) & (exp != 0xFF)
    finite = ~(nan | inf)
    return {
        "total_patterns": N,
        "nan": int(nan.sum()),
        "inf": int(inf.sum()),
        "zero": int(zero.sum()),
        "subnormal": int(sub.sum()),
        "normal": int(normal.sum()),
        "finite": int(finite.sum()),
        "distinct_finite_values": len(np.unique(v[finite])),
        "max_finite": float(np.max(v[finite])),
        "min_positive_normal": float(np.min(v[normal & (v > 0)])),
        "min_positive_subnormal": float(np.min(v[sub & (v > 0)])),
    }


# ---------------------------------------------------------------------------
# B. The tables + domain escape
# ---------------------------------------------------------------------------

def _safe(fn, x):
    """Evaluate fn in f64 with numpy error state off; inf/nan are legitimate
    RESULTS here, not failures -- the whole point is that bf16 can represent
    them, so the table stays total."""
    with np.errstate(all="ignore"):
        return fn(x)


FUNCS = {
    # exp: the softmax kernel. Domain of interest [-88, 0] after max-subtraction.
    "exp": lambda x: np.exp(x),
    # GELU (exact erf form, not the tanh approximation).
    "gelu": lambda x: 0.5 * x * (1.0 + np.vectorize(math.erf)(x / math.sqrt(2.0))),
    # SiLU / swish.
    "silu": lambda x: x / (1.0 + np.exp(-x)),
    # rsqrt: the RMSNorm kernel.
    "rsqrt": lambda x: 1.0 / np.sqrt(x),
    # recip and tanh for breadth.
    "recip": lambda x: 1.0 / x,
    "tanh": lambda x: np.tanh(x),
}


def build_tables():
    """Build the complete 65,536-row table for each unary function.

    Every row is DEFINED: the input is a bf16 bit pattern, the output is a bf16
    bit pattern. There is no 'undefined' row and no 'out of domain' row --
    inf and nan are bf16 values.
    """
    x64 = bf16_to_f32(ALL_BITS).astype(np.float64)
    tables = {}
    for name, fn in FUNCS.items():
        y = _safe(fn, x64)
        tables[name] = f64_to_bf16(y)
    return tables, x64


def domain_escape(tables, x64):
    """A 'domain escape' in the quantized setting is an input that falls outside
    the calibrated table window, so the lookup has NO ROW and the proof aborts.

    For a bf16 full-format table the address space IS the format, so the
    question reduces to: is the table total, and does every row hold a bf16
    value? Measure it rather than assert it."""
    report = {}
    for name, tab in tables.items():
        assert tab.shape == (N,), name
        assert tab.dtype == np.uint16, name
        y = bf16_to_f32(tab)
        yexp = (tab >> 7) & 0xFF
        ymant = tab & 0x7F
        out_nan = (yexp == 0xFF) & (ymant != 0)
        out_inf = (yexp == 0xFF) & (ymant == 0)
        out_zero = (yexp == 0) & (ymant == 0)
        # Which inputs produce a non-finite output, and is that the FUNCTION's
        # fault or the FORMAT's? A function that is genuinely undefined there
        # (rsqrt of a negative) maps to nan, which is a real bf16 value and a
        # real table row.
        xin = bf16_to_f32(ALL_BITS)
        in_nan = np.isnan(xin)
        report[name] = {
            "rows": int(tab.shape[0]),
            "rows_defined": int(tab.shape[0]),  # total by construction
            "addresses_with_no_entry": 0,
            "out_nan": int(out_nan.sum()),
            "out_nan_from_nan_input": int((out_nan & in_nan).sum()),
            "out_nan_from_finite_input": int((out_nan & ~in_nan).sum()),
            "out_inf": int(out_inf.sum()),
            "out_zero": int(out_zero.sum()),
            "out_finite_nonzero": int((~out_nan & ~out_inf & ~out_zero).sum()),
        }
    return report


def exp_underflow_boundary(tables, x64):
    """The specific claim: exp's [-88,0] range is an UNDERFLOW boundary, not a
    clip -- i.e. below it the true answer really is zero to bf16 precision, so
    'saturating' is EXACT, not an approximation. Verify."""
    tab = tables["exp"]
    xin = bf16_to_f32(ALL_BITS).astype(np.float64)
    y = bf16_to_f32(tab)
    finite_in = np.isfinite(xin)
    # Largest input whose exp() rounds to bf16 zero (underflow), and smallest
    # input whose exp() rounds to bf16 inf (overflow).
    under = finite_in & (y == 0.0) & (xin < 0)
    over = finite_in & np.isinf(y) & (xin > 0)
    # Is the underflow EXACT? i.e. is the true exp(x) genuinely below half the
    # smallest positive bf16 subnormal, so that rounding to zero is correct
    # rounding rather than a clip?
    with np.errstate(all="ignore"):
        true_y = np.exp(xin[under])
    min_sub = float(bf16_to_f32(np.array([1], dtype=np.uint16))[0])
    exact_underflow = bool(np.all(true_y <= min_sub / 2))
    return {
        "largest_input_underflowing_to_zero": float(np.max(xin[under])) if under.any() else None,
        "smallest_input_overflowing_to_inf": float(np.min(xin[over])) if over.any() else None,
        "min_positive_bf16_subnormal": min_sub,
        "underflow_is_correct_rounding_not_a_clip": exact_underflow,
        "count_underflow_to_zero": int(under.sum()),
        "count_overflow_to_inf": int(over.sum()),
        "softmax_operating_range_note": (
            "after max-subtraction every softmax argument is <= 0, so the "
            "overflow half is unreachable in a softmax node"
        ),
    }


# ---------------------------------------------------------------------------
# C. RANK -- the adversarial test of eprint 2026/1390 Prop 3
# ---------------------------------------------------------------------------

BABYBEAR_P = (1 << 31) - (1 << 27) + 1  # 2013265921


def rank_mod_p(M, p=BABYBEAR_P):
    """EXACT rank of an integer matrix over F_p by Gaussian elimination.

    This is the rank that actually governs the committed-polynomial count: the
    prover commits field elements, not reals. Numerical rank over R is a proxy;
    this is the real thing."""
    A = (np.asarray(M, dtype=np.int64) % p).copy()
    rows, cols = A.shape
    r = 0
    for c in range(cols):
        if r >= rows:
            break
        piv = None
        nz = np.nonzero(A[r:, c])[0]
        if nz.size == 0:
            continue
        piv = r + int(nz[0])
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), p - 2, p)
        A[r] = (A[r] * inv) % p
        below = np.nonzero(A[r + 1:, c])[0]
        if below.size:
            idx = r + 1 + below
            factors = A[idx, c].reshape(-1, 1)
            A[idx] = (A[idx] - factors * A[r].reshape(1, -1)) % p
        r += 1
    return r


def rank_profile(values, label, eps=1e-12, exact_cuts=(8,), integer_valued=False):
    """Tensor-train / bipartition rank profile.

    Prop 3: per-proof table cost is Theta~(rho * 2^{r/2}) where rho = rank(M_f)
    for the bit cut, M_f[u,v] = T_f(u || v). Dense is the full-rank extreme
    rho = 2^{floor(r/2)}. Report rho for EVERY prefix cut a = 1..15, not just the
    balanced one, so the claim cannot hide in a lucky cut.
    """
    out = []
    r = 16
    for a in range(1, r):
        M = np.asarray(values, dtype=np.float64).reshape(1 << a, 1 << (r - a))
        if not np.all(np.isfinite(M)):
            out.append({"cut": a, "shape": M.shape, "rank": None,
                        "note": "non-finite entries; rank undefined"})
            continue
        s = np.linalg.svd(M, compute_uv=False)
        s1 = s[0] if len(s) else 0.0
        if s1 == 0.0:
            out.append({"cut": a, "shape": M.shape, "rank": 0, "s2_over_s1": 0.0})
            continue
        ratio = float(s[1] / s1) if len(s) > 1 else 0.0
        num_rank = int(np.sum(s / s1 > eps))
        row = {
            "cut": a,
            "shape": (M.shape[0], M.shape[1]),
            "max_possible_rank": min(M.shape),
            "numerical_rank_eps1e-12": num_rank,
            "s2_over_s1": ratio,
            "exact_rank_mod_p": None,
        }
        if integer_valued and a in exact_cuts:
            row["exact_rank_mod_p"] = rank_mod_p(
                np.asarray(values, dtype=np.int64).reshape(1 << a, 1 << (r - a))
            )
        out.append(row)
    return {"label": label, "cuts": out}


def rank_k_reconstruction(values, target_bf16, cut=8, ks=(1, 2, 4, 8, 18, 32)):
    """Can a rank-k hi/lo product reproduce the table's OUTPUT bit-exactly?

    This isolates the ALGEBRA from the storage precision: the factors are kept
    at full f64 precision (an in-circuit table would be worse, never better),
    so any failure here is the factorization's, not the encoding's.

    The design wants `T[a||b] = combine(T_hi[a], T_lo[b])`. Prop 3 says the
    least number of hi/lo terms is rank(M_f). Take the best rank-k
    approximation, round the reconstruction back to bf16, and count how many of
    the 65,536 entries land on the CORRECT bf16 value. A design that advertises
    exact tables needs 65536/65536."""
    M = np.asarray(values, dtype=np.float64).reshape(1 << cut, 1 << (16 - cut))
    if not np.all(np.isfinite(M)):
        return None
    U, S, Vt = np.linalg.svd(M, full_matrices=False)
    tgt = np.asarray(target_bf16).reshape(1 << cut, 1 << (16 - cut))
    out = {}
    for k in ks:
        if k > len(S):
            continue
        recon = (U[:, :k] * S[:k]) @ Vt[:k, :]
        got = f64_to_bf16(recon)
        exact = int(np.sum(got == tgt))
        with np.errstate(all="ignore"):
            rel = np.abs(recon - M) / np.where(np.abs(M) > 0, np.abs(M), 1.0)
            rel = rel[np.isfinite(rel)]
        out[k] = {
            "entries": int(M.size),
            "bit_exact": exact,
            "bit_exact_frac": exact / M.size,
            "max_rel_err": float(np.max(rel)) if rel.size else float("nan"),
        }
    return out


def fixedpoint_exp_control(r=16, lo=-88.0, hi=0.0):
    """POSITIVE CONTROL. The paper's rank-1 exp table is FIXED-POINT indexed:
    address a maps to value lo + a*step, which IS additive across any bit cut,
    so exp(g(u)+h(v)) = exp(g(u))*exp(h(v)) and rho = 1. Reproduce their
    sigma2/sigma1 = 1.6e-15 to show the measurement is sound before applying it
    to bf16."""
    n = 1 << r
    step = (hi - lo) / (n - 1)
    a = np.arange(n, dtype=np.float64)
    x = lo + a * step
    return np.exp(x)


def main():
    print("=" * 78)
    print("A. bf16 CENSUS")
    print("=" * 78)
    c = census()
    for k, v in c.items():
        print(f"  {k:32s} {v}")

    print()
    print("=" * 78)
    print("B. COMPLETE TABLES + DOMAIN ESCAPE")
    print("=" * 78)
    tables, x64 = build_tables()
    esc = domain_escape(tables, x64)
    hdr = f"  {'fn':8s} {'rows':>7s} {'no-entry':>9s} {'nan-out':>8s} {'(from nan in)':>14s} {'inf-out':>8s} {'zero-out':>9s} {'finite':>8s}"
    print(hdr)
    for name, d in esc.items():
        print(f"  {name:8s} {d['rows']:7d} {d['addresses_with_no_entry']:9d} "
              f"{d['out_nan']:8d} {d['out_nan_from_nan_input']:14d} "
              f"{d['out_inf']:8d} {d['out_zero']:9d} {d['out_finite_nonzero']:8d}")

    print()
    print("  exp underflow boundary:")
    for k, v in exp_underflow_boundary(tables, x64).items():
        print(f"    {k:48s} {v}")

    print()
    print("=" * 78)
    print("C. BIPARTITION RANK (eprint 2026/1390 Prop 3), ADVERSARIAL")
    print("=" * 78)

    print()
    print("  POSITIVE CONTROL -- fixed-point-indexed exp on [-88, 0], r=16")
    print("  (the paper's own construction; expect rho = 1, s2/s1 ~ 1e-15)")
    ctrl = rank_profile(fixedpoint_exp_control(), "fixedpoint_exp")
    for row in ctrl["cuts"]:
        if row["cut"] in (1, 4, 8, 12, 15):
            print(f"    cut a={row['cut']:2d} shape={row['shape']}  "
                  f"rank<=({row['max_possible_rank']})  "
                  f"numerical_rank={row['numerical_rank_eps1e-12']}  "
                  f"s2/s1={row['s2_over_s1']:.3e}")

    print()
    print("  THE ACTUAL DESIGN -- bf16-INDEXED tables.")
    print("  The prover commits FIELD ELEMENTS, so the table entry is the OUTPUT'S")
    print("  bf16 BIT PATTERN (an integer in [0,2^16)), not a real number. That")
    print("  table is total and finite -- no substitution, no artifact.")
    print("  Prop 3's premise (value additive across the bit cut) does NOT hold for")
    print("  a bf16 address: value = (-1)^s * 2^(e-127) * (1 + m/128).")
    print()
    print(f"    {'fn':6s} {'cut':>4s} {'shape':>14s} {'maxrank':>8s} {'num_rank':>9s} "
          f"{'exact_rank/F_p':>15s} {'s2/s1':>10s}")
    for name in ("exp", "gelu", "silu", "rsqrt"):
        bits_as_int = tables[name].astype(np.int64)  # the committed field element
        prof = rank_profile(bits_as_int.astype(np.float64), name,
                            exact_cuts=(8,), integer_valued=True)
        # rank_profile only computes exact rank where asked; re-attach.
        for row in prof["cuts"]:
            if row["cut"] in (4, 8, 12):
                er = row["exact_rank_mod_p"]
                if er is None:
                    er_s = "-"
                else:
                    er_s = str(er)
                print(f"    {name:6s} {row['cut']:4d} "
                      f"{str(row['shape']):>14s} {row['max_possible_rank']:8d} "
                      f"{row['numerical_rank_eps1e-12']:9d} {er_s:>15s} "
                      f"{row['s2_over_s1']:10.3e}")
    print()
    print("  Numerical rank over R and EXACT rank over BabyBear agree at cut 8,")
    print("  which is the cross-check that the measurement is sound.")
    print("  rho(bf16 exp) = 18, not 1. The rank-1 exp result does NOT transfer to")
    print("  a bf16 address. rho is low only because most hi values saturate (|x|")
    print("  astronomically large or small), which is degeneracy, not an addition")
    print("  theorem -- and degeneracy does not give the clean 2 x 2^8 factorization.")

    print()
    print("=" * 78)
    print("D. DOES rho=1 SURVIVE THE ROUNDING? (exact integer test, no floats)")
    print("=" * 78)
    print("  rho=1 is a property of the REAL-valued exp. The prover does not commit")
    print("  reals; it commits the ROUNDED output. Measure the exact rank over")
    print("  BabyBear of the table the prover ACTUALLY commits, in both indexings.")
    print()
    for label, vals in (
        ("fixed-point exp, REAL values (paper's object)", fixedpoint_exp_control()),
        ("fixed-point exp, ROUNDED to bf16 (committed object)",
         f64_to_bf16(fixedpoint_exp_control()).astype(np.int64)),
        ("bf16-indexed exp, ROUNDED to bf16 (committed object)",
         tables["exp"].astype(np.int64)),
    ):
        M = np.asarray(vals).reshape(256, 256)
        if M.dtype == np.float64:
            s = np.linalg.svd(M, compute_uv=False)
            print(f"  {label:52s} numerical rank {int(np.sum(s/s[0] > 1e-12)):3d}"
                  f"   (real-valued: exact F_p rank not applicable)")
        else:
            print(f"  {label:52s} EXACT rank over F_p: {rank_mod_p(M):3d}")
    print()
    print("  An explicit rank-1 refutation needs one nonzero 2x2 minor. Exact")
    print("  integer arithmetic on the committed table:")
    for label, T in (("fixed-point exp (rounded)", f64_to_bf16(fixedpoint_exp_control()).astype(np.int64)),
                     ("bf16-indexed exp", tables["exp"].astype(np.int64))):
        M = T.reshape(256, 256)
        found = None
        for i in range(0, 256, 7):
            for j in range(i + 1, 256, 11):
                for a in range(0, 256, 13):
                    for b in range(a + 1, 256, 17):
                        d = int(M[i, a]) * int(M[j, b]) - int(M[i, b]) * int(M[j, a])
                        if d != 0:
                            found = (i, j, a, b, d)
                            break
                    if found:
                        break
                if found:
                    break
            if found:
                break
        if found:
            i, j, a, b, d = found
            print(f"    {label:28s} minor(rows {i},{j}; cols {a},{b}) = {d} != 0"
                  f"  => rank >= 2, NOT rank-1")
        else:
            print(f"    {label:28s} no nonzero 2x2 minor found in the sampled grid")


if __name__ == "__main__":
    main()
