"""
Phase 0 cost model: bf16 exact tables vs DeepProve fused requantization.

SUBSTRATE NOTE. This is a COUNTING harness. It authors no AIR, no constraint,
no gadget, and links no proof system. Every constraint system it prices would
be authored in Lean. Nothing here is a circuit.

WHAT IS BEING PRICED, AND IN WHAT CURRENCY
------------------------------------------
DeepProve Table 7 splits total prover time into:
    witness generation   5.97%
    witness COMMITMENT  56.85%   <- proportional to COMMITTED FIELD ELEMENTS
    opening              1.04%
    PIOP                35.25%   <- proportional to SUMCHECK/GKR WORK
    others               0.89%
(GPT-2, BaseFold, seq 512, 48 threads.)

So we price two currencies and weight them by that split:
  C = committed base-field elements  (witness commit; LDE + Merkle are linear in it)
  P = lookup-fraction-rows           (PIOP; one fraction folded per lookup per row)

SUBSTRATE ACCOUNTING (measured, not assumed)
--------------------------------------------
Read out of Plonky3 `p3-lookup` at the rev this workspace pins
(82cfad73cd734d37a0d51953094f970c531817ec), file `lookup/src/logup.rs`:

  * `let width = lookups.len();` and `aux_trace = Challenge::zero_vec(height*width)`
    -> ONE EXTENSION-FIELD auxiliary column per `Lookup`, full trace height.
  * `Lookup.elements: Vec<Vec<...>>` -> a LOCAL lookup may batch several
    (tuple, multiplicity) fractions into ONE aux column via a common
    denominator, at constraint degree `1 + max(deg num, deg den)`, i.e. degree
    grows about linearly in the batch factor. So aux columns trade against
    constraint degree.
  * `num_challenges() == 2` (alpha, beta) per lookup.

BabyBear's extension degree for a ~100-bit-soundness challenge is 4, so one aux
column costs 4 BASE field elements per row. That is the marginal cost of one
lookup at one row, and it is the single most important constant here.

EVERY PARAMETER BELOW IS LABELLED:
  STATED  - written in the cited paper
  MEASURED- measured by this harness or read out of the pinned substrate
  ASSUMED - our choice; swept in the sensitivity analysis
"""

import itertools

# ---------------------------------------------------------------------------
# Substrate constants
# ---------------------------------------------------------------------------

EXT_DEGREE = 4          # MEASURED: BabyBear quartic extension, p3 config
AUX_COLS_PER_LOOKUP = 1  # MEASURED: p3-lookup logup.rs, one aux col per Lookup
BASE_PER_LOOKUP_ROW = EXT_DEGREE * AUX_COLS_PER_LOOKUP  # = 4

# Table-side committed columns per table row: the multiplicity column (1 base)
# plus the table's own running-sum aux column (EXT_DEGREE base). The (address,
# value) pair is a public constant and can be preprocessed, so it is NOT
# charged per proof.
BASE_PER_TABLE_ROW = 1 + EXT_DEGREE  # = 5

# DeepProve Table 7 prover split, GPT-2 / BaseFold.  STATED.
W_COMMIT = 0.5685
W_PIOP = 0.3525


# ---------------------------------------------------------------------------
# Model shapes
# ---------------------------------------------------------------------------

class Model:
    def __init__(self, name, d_model, d_ff, n_layers, n_heads, seq, vocab):
        self.name, self.d_model, self.d_ff = name, d_model, d_ff
        self.n_layers, self.n_heads, self.seq, self.vocab = n_layers, n_heads, seq, vocab

    @property
    def gelu_elems(self):
        return self.n_layers * self.seq * self.d_ff

    @property
    def softmax_elems(self):
        return self.n_layers * self.n_heads * self.seq * self.seq

    @property
    def norm_elems(self):
        return self.n_layers * 2 * self.seq * self.d_model

    @property
    def matmul_out_elems(self):
        """Every element that comes out of a matmul and must be renormalized /
        requantized before it can index the next table."""
        per_layer = self.seq * (3 * self.d_model      # Q, K, V
                                + self.d_model        # attention output
                                + self.d_ff           # FF up
                                + self.d_model)       # FF down
        attn = self.n_heads * self.seq * self.seq * 2  # scores and context
        return self.n_layers * (per_layer + attn)

    @property
    def accum_depth(self):
        return self.d_model


GPT2 = Model("GPT-2", d_model=768, d_ff=3072, n_layers=12, n_heads=12,
             seq=512, vocab=50257)


# ---------------------------------------------------------------------------
# The two protocols
# ---------------------------------------------------------------------------

def deepprove_requant(q, f, accum_bits, s_clamp, k, signed=True):
    """DeepProve Protocol 5 + Appendix C, fused requantization.

        eps*2^f*In + 2^{f+n-1} = 2^{f+n}*Out + sum_{i=1}^{t} 2^{k(i-1)}*Shifted_i
        t = ceil((f+n)/k)

    DeepProve sets k = q (STATED, dp1112 lines 834, 4925-4927) so the range
    table is the same table as the quantization range. But k is a FREE design
    parameter, so it is passed in and swept jointly with the bf16 path's chunk
    width -- otherwise the comparison manufactures a gap out of a choice
    neither format forces.

    The shift is f + n where n = accum_bits - q. The `f` term is the precision
    of the fixed-point multiplier Quant(2^f * eps): the quantized path must
    multiply by an ARBITRARY REAL scale factor, so it carries a multiplier.

    Returns (committed_base_cols, lookups, t) PER ELEMENT.
    """
    n = accum_bits - q          # bits shifted away to get back to q bits
    t = -(-(f + n) // k)        # ceil

    cols = 1 + t                # Out, plus the t shifted-away chunks
    lookups = t                 # t-1 range checks + 1 merged activation lookup

    # Clamping. int-q has no saturation value, so out-of-range must be proved
    # and clamped explicitly (Appendix C, "Proving clamping").
    if signed:
        cols += 2 * (s_clamp - 1) + 2 + 1   # ZeroIn/Out pairs, SgnIn/Out, Value
    else:
        cols += 2 * s_clamp + 1
    lookups += s_clamp
    return cols, lookups, t


def bf16_renorm_dynamic(accum_window_bits, k, sig_bits=8):
    """THE ASSUMPTION MOST LIKELY TO BE WRONG, PRICED.

    `bf16_renorm` below assumes the renormalizing shift is STATIC because the
    block exponent is shared. But bf16 is NOT a block format -- it carries a
    PER-ELEMENT exponent. Converting a block-float fixed-point accumulator into
    a per-element bf16 value therefore requires finding THIS element's leading
    one, which is DATA-DEPENDENT.

    The dilemma has three horns and every one of them costs something:

      1. Keep the output in block float (shared output exponent). Then the
         table is indexed by a FIXED-POINT MANTISSA -- which is the quantized
         design, and the bf16 exact-table thesis evaporates.

      2. Normalize per element from an integer accumulator. Pay for a variable
         shift: this function.

      3. Accumulate in genuine IEEE fp32, whose bit pattern truncates to bf16
         by a STATIC 32 = 16+16 split, so renormalization really is two
         columns and a range check. But an fp32 accumulator means proving a
         SEQUENCE OF ROUNDED FLOAT ADDS, and matmul-by-sumcheck proves a
         linear form over FIELD elements, not that. Horn 3 buys a cheap
         renormalization by making matmul expensive -- and matmul being 5.3%
         is the premise the whole plan rests on.

    Horns 1 and 3 each dissolve a different premise of the thesis. Horn 2 is
    the one that keeps both premises, and it is the one priced here.

    Priced here: the static chunks, PLUS a committed exponent column, PLUS a
    lookup resolving 2^e, PLUS a boundary-chunk lookup that enforces
    rem < 2^e for variable e (a fixed-width chunked comparison cannot do it).
    """
    shift = accum_window_bits - sig_bits
    t = -(-shift // k)
    cols = 1 + t + 1        # Out, chunks, and the per-element exponent
    lookups = t + 2         # chunks, the 2^e resolution, the boundary chunk
    return cols, lookups, t


def bf16_renorm(accum_window_bits, k, sig_bits=8):
    """The bf16 path's honest analogue of requantization.

    A matmul accumulates into a block-float window (STATED for A100, arXiv
    2606.00279 sec 4.1: 26 bits = 2 integer + 23 fraction + 1 alignment). To
    index a 2^16 bf16 table the accumulator must be renormalized back to a bf16
    value. With a SHARED per-block exponent the shift is static per block, so
    the relation has exactly the requantization shape:

        Acc = 2^shift * Out + sum_{i=1}^{t'} 2^{k(i-1)} * Shifted_i

    TWO STRUCTURAL DIFFERENCES, and they are the whole of the bf16 advantage:

      1. NO MULTIPLIER. The block scale is a power of two, so rescaling is a
         pure shift. There is no `f` term -- no Quant(2^f * eps) multiplier to
         carry. The quantized path needs one because its scale factor is an
         arbitrary real.
      2. NO CLAMPING. bf16 saturates to +/-inf, which is a VALID TABLE ROW.
         int-q has no saturation value, so DeepProve must prove and clamp.
    """
    shift = accum_window_bits - sig_bits
    t = -(-shift // k)
    cols = 1 + t
    lookups = t          # last one is the merged activation table
    return cols, lookups, t


def table_cost(table_rows, n_tables):
    """Per-PROOF committed cost of the shared tables. This is the term
    eprint 2026/1390 Prop 3 governs (Theta~(rho * 2^{r/2})); here it is charged
    densely, which is the pessimistic and honest choice given the measured
    rank."""
    return table_rows * BASE_PER_TABLE_ROW * n_tables


def renorm_sites(model):
    """Number of elements that pay ONE requantization / renormalization.

    NO DOUBLE COUNTING. A GELU input IS a matmul output; DeepProve's own
    Appendix B.2.1 merges the activation lookup INTO that element's
    requantization, so GELU costs nothing beyond the requant its input already
    pays. The sites are:

      * every matmul output element (the requant/renorm proper), and
      * softmax's post-division rescale and the norm's post-scale rescale,
        which are genuinely extra elementwise rescales after a reduction.

    The per-row reciprocal (softmax denominator) and per-row rsqrt (norm) are
    amortized over seq / d_model respectively and are counted separately."""
    return (model.matmul_out_elems      # requant/renorm after every matmul
            + model.softmax_elems       # rescale by 1/rowsum
            + model.norm_elems)         # rescale by rsqrt


def row_reductions(model):
    """Per-ROW lookups: one reciprocal per softmax row, one rsqrt per norm row.
    Amortized, and reported so they are visible rather than quietly dropped."""
    return (model.n_layers * model.n_heads * model.seq   # softmax rows
            + model.n_layers * 2 * model.seq)            # norm rows


def price(model, path, params):
    """Return committed elements, PIOP fraction-rows, and the blended cost."""
    m = renorm_sites(model)
    m_row = row_reductions(model)

    if path == "quantized":
        q = params["q"]
        cols, lk, t = deepprove_requant(
            q, params["f"], params["accum_bits"], params["s_clamp"], params["k"])
        table_rows, n_tables = 1 << max(q, params["k"]), params["n_tables"]
    elif path == "bf16":
        cols, lk, t = bf16_renorm(params["accum_window"], params["k"])
        table_rows, n_tables = 1 << 16, params["n_tables"]
    elif path == "bf16_dynamic":
        cols, lk, t = bf16_renorm_dynamic(params["accum_window"], params["k"])
        table_rows, n_tables = 1 << 16, params["n_tables"]
    else:
        raise ValueError(path)

    batch = params.get("batch", 1)
    per_elem = cols + BASE_PER_LOOKUP_ROW * lk / batch

    C = m * per_elem + m_row * (1 + BASE_PER_LOOKUP_ROW) \
        + table_cost(table_rows, n_tables)
    P = m * lk + m_row + table_rows * n_tables

    return {
        "committed_elements": C,
        "piop_fraction_rows": P,
        "per_elem_cols": cols,
        "per_elem_lookups": lk,
        "chunks_t": t,
        "table_rows": table_rows,
        "table_term": table_cost(table_rows, n_tables),
        "table_term_frac": table_cost(table_rows, n_tables) / C,
        "renorm_sites": m,
        "row_reductions": m_row,
    }


def blended_ratio(q_res, b_res):
    """Blend the two currencies by DeepProve's own measured prover split."""
    cw = q_res["committed_elements"] / b_res["committed_elements"]
    pw = q_res["piop_fraction_rows"] / b_res["piop_fraction_rows"]
    total_w = W_COMMIT + W_PIOP
    # Speedup of bf16 over quantized, weighted by where the time actually goes.
    # Amdahl over the two components, with the remaining 7.9% (witness gen,
    # open, others) assumed UNCHANGED -- the conservative choice.
    frac_unchanged = 1.0 - total_w
    speedup = 1.0 / (frac_unchanged
                     + W_COMMIT / cw
                     + W_PIOP / pw)
    return cw, pw, speedup


def main():
    m = GPT2
    print("=" * 86)
    print("PHASE 0 COST MODEL -- bf16 exact tables vs DeepProve fused requantization")
    print("=" * 86)
    print(f"model {m.name}  seq {m.seq}  d_model {m.d_model}  d_ff {m.d_ff} "
          f"layers {m.n_layers}  heads {m.n_heads}")
    print(f"  matmul output elements                 : {m.matmul_out_elems:,}")
    print(f"  softmax elements                       : {m.softmax_elems:,}")
    print(f"  norm elements                          : {m.norm_elems:,}")
    print(f"  GELU elements (MERGED into the FF-up requant, cost 0 extra)")
    print(f"                                         : {m.gelu_elems:,}")
    print(f"  -> renormalization SITES (no double count): {renorm_sites(m):,}")
    print(f"  -> per-row reductions (recip / rsqrt)     : {row_reductions(m):,}")
    print()
    print("SUBSTRATE (measured from the pinned Plonky3 p3-lookup)")
    print(f"  aux columns per LogUp lookup       : {AUX_COLS_PER_LOOKUP} (extension field)")
    print(f"  BabyBear extension degree          : {EXT_DEGREE}")
    print(f"  base field elements per lookup-row : {BASE_PER_LOOKUP_ROW}")
    print(f"  base field elements per table row  : {BASE_PER_TABLE_ROW} (multiplicity + aux)")
    print()

    # Baseline parameter choice.  k is held EQUAL across both paths.
    K = 12                        # chunk width, EQUAL for both. Swept below.
    qp = dict(q=12,               # STATED: dp1112 line 1436, deployed config
              f=16,               # ASSUMED: dp1112 never states f. Swept below.
              accum_bits=12 + 12 + 10,  # q + q + ceil(log2 d_model=768)
              s_clamp=2,          # ASSUMED: dp1112 never states s. Swept below.
              k=K, n_tables=3)
    bp = dict(accum_window=26,    # STATED: A100 window, arXiv 2606.00279 sec 4.1
              k=K, n_tables=3)

    qr = price(m, "quantized", qp)
    br = price(m, "bf16", bp)
    cw, pw, sp = blended_ratio(qr, br)

    print("BASELINE POINT")
    print(f"  quantized: q={qp['q']} f={qp['f']} accum={qp['accum_bits']}b "
          f"s_clamp={qp['s_clamp']}  ->  t={qr['chunks_t']} chunks")
    print(f"  bf16     : accumulator window {bp['accum_window']}b, 16-bit chunks "
          f"->  t'={br['chunks_t']} chunks")
    print()
    hdr = f"  {'':26s} {'quantized':>18s} {'bf16':>18s} {'ratio':>9s}"
    print(hdr)
    print(f"  {'committed cols / elem':26s} {qr['per_elem_cols']:>18d} "
          f"{br['per_elem_cols']:>18d} {qr['per_elem_cols']/br['per_elem_cols']:>9.2f}x")
    print(f"  {'lookups / elem':26s} {qr['per_elem_lookups']:>18d} "
          f"{br['per_elem_lookups']:>18d} {qr['per_elem_lookups']/br['per_elem_lookups']:>9.2f}x")
    print(f"  {'table rows':26s} {qr['table_rows']:>18,} {br['table_rows']:>18,}")
    print(f"  {'table term (elements)':26s} {qr['table_term']:>18,} {br['table_term']:>18,}")
    print(f"  {'table term as % of total':26s} {100*qr['table_term_frac']:>17.4f}% "
          f"{100*br['table_term_frac']:>17.4f}%")
    print(f"  {'COMMITTED ELEMENTS':26s} {qr['committed_elements']:>18,.0f} "
          f"{br['committed_elements']:>18,.0f} {cw:>9.2f}x")
    print(f"  {'PIOP fraction-rows':26s} {qr['piop_fraction_rows']:>18,.0f} "
          f"{br['piop_fraction_rows']:>18,.0f} {pw:>9.2f}x")
    print()
    print(f"  BLENDED PROVER SPEEDUP (Table 7 weights, 7.9% held unchanged): "
          f"{sp:.2f}x")
    print()

    # -----------------------------------------------------------------
    print("=" * 86)
    print("SENSITIVITY -- f and s_clamp are NOT STATED by DeepProve; k is a free")
    print("design parameter for BOTH paths, so it is held EQUAL and swept.")
    print("=" * 86)
    print(f"  {'k':>3s} {'f':>4s} {'s':>3s} {'q':>3s} | {'t':>3s} {'q cols':>7s} {'q lk':>5s} "
          f"| {'t2':>3s} {'bf cols':>8s} {'bf lk':>6s} | {'commit':>7s} {'piop':>6s} {'SPEEDUP':>8s}")
    rows = []
    for k, f, s_clamp, q in itertools.product((8, 12, 16), (8, 16, 24), (1, 2, 4), (8, 12)):
        qp2 = dict(qp, f=f, s_clamp=s_clamp, q=q, k=k, accum_bits=q + q + 10)
        bp2 = dict(bp, k=k)
        qr2 = price(m, "quantized", qp2)
        br2 = price(m, "bf16", bp2)
        cw2, pw2, sp2 = blended_ratio(qr2, br2)
        rows.append((sp2, k, f, s_clamp, q))
        print(f"  {k:>3d} {f:>4d} {s_clamp:>3d} {q:>3d} | {qr2['chunks_t']:>3d} "
              f"{qr2['per_elem_cols']:>7d} {qr2['per_elem_lookups']:>5d} | "
              f"{br2['chunks_t']:>3d} {br2['per_elem_cols']:>8d} {br2['per_elem_lookups']:>6d} | "
              f"{cw2:>6.2f}x {pw2:>5.2f}x {sp2:>7.2f}x")
    print()
    lo, hi = min(rows), max(rows)
    print(f"  speedup range: {lo[0]:.2f}x (k={lo[1]} f={lo[2]} s={lo[3]} q={lo[4]}) "
          f".. {hi[0]:.2f}x (k={hi[1]} f={hi[2]} s={hi[3]} q={hi[4]})")
    med = sorted(r[0] for r in rows)[len(rows) // 2]
    print(f"  median speedup over the sweep: {med:.2f}x")
    n_under2 = sum(1 for r in rows if r[0] < 2.0)
    print(f"  parameter points below 2x: {n_under2} of {len(rows)}")
    print()

    print("=" * 86)
    print("THE LOAD-BEARING ASSUMPTION: is the renormalizing shift STATIC?")
    print("=" * 86)
    print("  bf16 carries a PER-ELEMENT exponent, so converting a block-float")
    print("  accumulator to bf16 needs THIS element's leading one -- data-dependent.")
    print("  Price the dynamic version and see whether the verdict survives.")
    print()
    print(f"  {'':34s} {'cols':>6s} {'lk':>4s} {'commit':>8s} {'piop':>7s} {'SPEEDUP':>9s}")
    bdyn = price(m, "bf16_dynamic", bp)
    cwd, pwd_, spd = blended_ratio(qr, bdyn)
    print(f"  {'static shift (assumed above)':34s} {br['per_elem_cols']:>6d} "
          f"{br['per_elem_lookups']:>4d} {cw:>7.2f}x {pw:>6.2f}x {sp:>8.2f}x")
    print(f"  {'dynamic per-element normalization':34s} {bdyn['per_elem_cols']:>6d} "
          f"{bdyn['per_elem_lookups']:>4d} {cwd:>7.2f}x {pwd_:>6.2f}x {spd:>8.2f}x")
    print()
    dyn_rows = []
    for k, f, s_clamp, q in itertools.product((8, 12, 16), (8, 16, 24), (1, 2, 4), (8, 12)):
        qp3 = dict(qp, f=f, s_clamp=s_clamp, q=q, k=k, accum_bits=q + q + 10)
        bp3 = dict(bp, k=k)
        _, _, s3 = blended_ratio(price(m, "quantized", qp3),
                                 price(m, "bf16_dynamic", bp3))
        dyn_rows.append(s3)
    print(f"  dynamic-normalization sweep: {min(dyn_rows):.2f}x .. {max(dyn_rows):.2f}x, "
          f"median {sorted(dyn_rows)[len(dyn_rows)//2]:.2f}x, "
          f"{sum(1 for r in dyn_rows if r < 2.0)} of {len(dyn_rows)} below 2x")
    print()
    print("  If normalization is dynamic, the honest range straddles 2x and the")
    print("  thesis is not safe. Resolving static-vs-dynamic is the highest-value")
    print("  next measurement, and it is a SPEC question (what does the block-float")
    print("  spec say the output format is), not a prover question.")
    print()

    print("=" * 86)
    print("ABLATION -- where does the bf16 advantage actually come from?")
    print("=" * 86)
    print("  Turn off one structural difference at a time, at the baseline point.")
    base_sp = sp
    # (a) give the quantized path saturation too, i.e. remove clamping
    qp_noclamp = dict(qp, s_clamp=0)
    r = price(m, "quantized", qp_noclamp)
    _, _, sp_a = blended_ratio(r, br)
    print(f"  baseline                                        {base_sp:5.2f}x")
    print(f"  ...if int-q had a saturation value (no clamping) {sp_a:5.2f}x   "
          f"(clamping is worth {base_sp - sp_a:+.2f}x)")
    # (b) give the quantized path a power-of-two scale, i.e. remove the multiplier
    qp_nof = dict(qp, f=0)
    r = price(m, "quantized", qp_nof)
    _, _, sp_b = blended_ratio(r, br)
    print(f"  ...if the scale were a power of two (f = 0)      {sp_b:5.2f}x   "
          f"(the multiplier is worth {base_sp - sp_b:+.2f}x)")
    # (c) both
    qp_both = dict(qp, f=0, s_clamp=0)
    r = price(m, "quantized", qp_both)
    _, _, sp_c = blended_ratio(r, br)
    print(f"  ...both                                          {sp_c:5.2f}x")
    print()
    print("  Whatever survives (c) is the pure accumulator-width effect: a")
    print("  block-float 26-bit window vs a 34-bit int-12 accumulator.")
    print()

    # -----------------------------------------------------------------
    print("=" * 86)
    print("THE OPTIMISTIC BOUND -- what the plan ASSUMES (renormalization is free)")
    print("=" * 86)
    print("  If the bf16 path really paid NOTHING to get from a matmul accumulator")
    print("  back to a bf16 table index -- the plan's 'requantization is ABSENT' --")
    print("  then bf16 costs 1 committed column + 1 lookup per element and nothing")
    print("  else. Price that too, so the gap between the two readings is visible.")
    # The free-renorm ideal: 1 col + 1 lookup per element, no chunks at all.
    m_sites = renorm_sites(m)
    C_ideal = m_sites * (1 + BASE_PER_LOOKUP_ROW * 1) + table_cost(1 << 16, 3)
    P_ideal = m_sites * 1 + (1 << 16) * 3
    ideal = {"committed_elements": C_ideal, "piop_fraction_rows": P_ideal}
    cwi, pwi, spi = blended_ratio(qr, ideal)
    print(f"  committed elements : {C_ideal:,.0f}   vs quantized {qr['committed_elements']:,.0f}"
          f"   ratio {cwi:.2f}x")
    print(f"  PIOP fraction-rows : {P_ideal:,.0f}   vs quantized {qr['piop_fraction_rows']:,.0f}"
          f"   ratio {pwi:.2f}x")
    print(f"  BLENDED SPEEDUP (ideal, renorm free, requant elems vanish) : {spi:.2f}x")
    print()
    print("  The gap between this and the honest number is the price of the")
    print("  assumption that renormalization is free. It is not free: a block-float")
    print("  accumulator must be normalized and rounded to index a bf16 table, and")
    print("  that step has exactly the requantization shape.")
    print()

    # -----------------------------------------------------------------
    print("=" * 86)
    print("WHEN WOULD THE RANK-1 exp SPLIT ACTUALLY BUY ANYTHING?")
    print("=" * 86)
    print("  eprint 2026/1390 Prop 3 governs the PER-PROOF table term only, and")
    print("  Corollary 3 says the per-lookup term is Omega(m) regardless. So the")
    print("  rank-1 split can only matter when the table term is a real share of")
    print("  the proof. Find the break-even.")
    per_elem_bf = br["per_elem_cols"] + BASE_PER_LOOKUP_ROW * br["per_elem_lookups"]
    dense_tab = table_cost(1 << 16, 1)
    print()
    print(f"  one dense 2^16 table costs        : {dense_tab:,} committed elements")
    print(f"  one bf16 element costs            : {per_elem_bf} committed elements")
    print(f"  elements per proof for the table")
    print(f"    to be 50% of the proof          : {dense_tab // per_elem_bf:,}")
    print(f"    to be 10% of the proof          : {9 * dense_tab // per_elem_bf:,}")
    print(f"    to be  1% of the proof          : {99 * dense_tab // per_elem_bf:,}")
    print(f"  actual elements in a GPT-2 seq-512 proof : {renorm_sites(m):,}")
    print(f"  -> table term is {100*br['table_term_frac']:.4f}% of the proof")
    print()
    for split in (1, 12, 144, 1728):
        per = renorm_sites(m) / split
        frac = dense_tab * 3 / (per * per_elem_bf + dense_tab * 3)
        print(f"  if the proof is split into {split:5d} chunks "
              f"({per:>12,.0f} elems each): table term {100*frac:6.3f}%")
    print()
    print("  Reading: rank-1 would divide the table term by ~256. At the measured")
    print("  operating point that term is a fraction of a percent, so the certified")
    print("  rank-1 optimum is worth a fraction of a percent. It only becomes")
    print("  interesting for proofs of a few tens of thousands of elements.")


if __name__ == "__main__":
    main()
