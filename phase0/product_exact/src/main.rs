//! Exhaustive test of the claim "bf16 x bf16 -> fp32 NEVER ROUNDS".
//!
//! SUBSTRATE NOTE: this is a measurement harness. It authors no AIR, no
//! constraint, no gadget, and links no proof system. It is arithmetic
//! enumeration only.
//!
//! The claim in the plan was verified over 200k RANDOM pairs. Random sampling
//! from a 2^32 space concentrates on mid-range exponents, which is exactly
//! where the claim is true. This runs ALL 2^32 ordered pairs and classifies
//! every one.
//!
//! Method: bf16 widens to f32 exactly (it is the top 16 bits of a binary32).
//! The exact real product of two bf16 values is ALWAYS representable in f64:
//! each operand carries at most 8 significant bits, so the product carries at
//! most 16, well inside f64's 53; and the exponent range of a bf16 product,
//! [2^-266, 2^256], sits well inside f64's normal range [2^-1022, 2^1023].
//! So `(a as f64) * (b as f64)` is the EXACT product, with no rounding of its
//! own, and we can ask directly whether f32 can hold it.
//!
//! No dependencies; std::thread only.

const N: usize = 1 << 16;

#[inline(always)]
fn bf16_to_f32(bits: u16) -> f32 {
    f32::from_bits((bits as u32) << 16)
}

#[derive(Default, Clone, Copy, Debug)]
struct Counts {
    /// Both operands finite, product finite in f32 and EXACTLY equal to the
    /// real product. This is the case the claim asserts.
    exact: u64,
    /// Both operands finite, but the real product exceeds f32's range and the
    /// f32 result is +/-inf. A rounding of the WORST kind: unbounded error.
    overflow_to_inf: u64,
    /// Both operands finite and nonzero, real product nonzero, but the f32
    /// result is a SUBNORMAL that differs from the real product: f32
    /// subnormals carry fewer than 24 significand bits, so the 16-bit
    /// significand no longer fits. Genuine rounding.
    inexact_subnormal: u64,
    /// Both operands finite and nonzero, real product nonzero, but the f32
    /// result is exactly zero: total underflow. Rounding with 100% relative
    /// error.
    underflow_to_zero: u64,
    /// Both operands finite, result normal in f32, and yet inexact. If this is
    /// nonzero the significand argument itself is wrong.
    inexact_normal: u64,
    /// At least one operand is inf or nan.
    nonfinite_operand: u64,
}

impl Counts {
    fn merge(&mut self, o: &Counts) {
        self.exact += o.exact;
        self.overflow_to_inf += o.overflow_to_inf;
        self.inexact_subnormal += o.inexact_subnormal;
        self.underflow_to_zero += o.underflow_to_zero;
        self.inexact_normal += o.inexact_normal;
        self.nonfinite_operand += o.nonfinite_operand;
    }
    fn total(&self) -> u64 {
        self.exact
            + self.overflow_to_inf
            + self.inexact_subnormal
            + self.underflow_to_zero
            + self.inexact_normal
            + self.nonfinite_operand
    }
}

/// Smallest positive f32 normal, 2^-126.
const F32_MIN_NORMAL: f64 = 1.1754943508222875e-38;

fn classify(xa: f32, xb: f32, c: &mut Counts, witness: &mut Witness, a: u16, b: u16) {
    if !xa.is_finite() || !xb.is_finite() {
        c.nonfinite_operand += 1;
        return;
    }
    // EXACT real product (see header: f64 cannot round a bf16 x bf16 product).
    let p: f64 = (xa as f64) * (xb as f64);
    let q: f32 = p as f32;
    if q as f64 == p {
        c.exact += 1;
        return;
    }
    if q.is_infinite() {
        c.overflow_to_inf += 1;
        witness.note_overflow(a, b, p);
        return;
    }
    if q == 0.0 {
        c.underflow_to_zero += 1;
        witness.note_underflow(a, b, p);
        return;
    }
    if (q as f64).abs() < F32_MIN_NORMAL {
        c.inexact_subnormal += 1;
        witness.note_subnormal(a, b, p, q);
        return;
    }
    // Should be impossible if the 8+8 <= 24 significand argument is right.
    c.inexact_normal += 1;
    witness.note_normal(a, b, p, q);
}

#[derive(Default, Clone)]
struct Witness {
    overflow: Option<(u16, u16, f64)>,
    underflow: Option<(u16, u16, f64)>,
    subnormal: Option<(u16, u16, f64, f32)>,
    normal: Option<(u16, u16, f64, f32)>,
    /// Largest relative error observed among inexact-but-finite-nonzero cases.
    max_rel_err: f64,
}

impl Witness {
    fn note_overflow(&mut self, a: u16, b: u16, p: f64) {
        if self.overflow.is_none() {
            self.overflow = Some((a, b, p));
        }
    }
    fn note_underflow(&mut self, a: u16, b: u16, p: f64) {
        if self.underflow.is_none() {
            self.underflow = Some((a, b, p));
        }
        self.max_rel_err = self.max_rel_err.max(1.0);
    }
    fn note_subnormal(&mut self, a: u16, b: u16, p: f64, q: f32) {
        if self.subnormal.is_none() {
            self.subnormal = Some((a, b, p, q));
        }
        let e = ((q as f64 - p) / p).abs();
        if e > self.max_rel_err {
            self.max_rel_err = e;
        }
    }
    fn note_normal(&mut self, a: u16, b: u16, p: f64, q: f32) {
        if self.normal.is_none() {
            self.normal = Some((a, b, p, q));
        }
    }
    fn merge(&mut self, o: &Witness) {
        if self.overflow.is_none() {
            self.overflow = o.overflow;
        }
        if self.underflow.is_none() {
            self.underflow = o.underflow;
        }
        if self.subnormal.is_none() {
            self.subnormal = o.subnormal;
        }
        if self.normal.is_none() {
            self.normal = o.normal;
        }
        self.max_rel_err = self.max_rel_err.max(o.max_rel_err);
    }
}

/// The structural half of the claim, checked separately and exhaustively:
/// the product of two 8-bit significands needs at most 16 bits. If this holds,
/// every failure above is an EXPONENT-range failure, not a significand one.
fn significand_width_check() -> (u32, u64) {
    let mut max_bits = 0u32;
    let mut n = 0u64;
    // bf16 normal significand is 1.mmmmmmm, i.e. the 8-bit integer 128..255.
    // Subnormal significand is 0.mmmmmmm, i.e. 1..127. Together: 1..255, plus
    // the implicit-bit-set range 128..255. Enumerate every 8-bit significand.
    for sa in 1u32..256 {
        for sb in 1u32..256 {
            let prod = sa * sb;
            let bits = 32 - prod.leading_zeros();
            if bits > max_bits {
                max_bits = bits;
            }
            n += 1;
        }
    }
    (max_bits, n)
}

/// The claim is rescued by a RANGE HYPOTHESIS. A product is exact exactly when
/// it lands in fp32's normal range, i.e. when the unbiased exponents satisfy
/// `-126 <= ex + ey <= 127`. In a BLOCK-FLOAT design the block exponent is
/// known before the multiply, so this is a STATIC, per-block, checkable side
/// condition -- not a per-element runtime risk. Measure the exact fraction
/// under the hypothesis to confirm it is the right one.
fn range_hypothesis() -> (u64, u64) {
    let mut in_range = 0u64;
    let mut exact = 0u64;
    for a in 0..N {
        let xa = bf16_to_f32(a as u16);
        if !xa.is_finite() || xa == 0.0 {
            continue;
        }
        let ea = ((a as u16 >> 7) & 0xFF) as i32 - 127;
        for b in 0..N {
            let xb = bf16_to_f32(b as u16);
            if !xb.is_finite() || xb == 0.0 {
                continue;
            }
            let eb = ((b as u16 >> 7) & 0xFF) as i32 - 127;
            // Conservative window: leave one bit of headroom for the
            // significand product carrying into the next binade.
            if ea + eb < -126 || ea + eb > 126 {
                continue;
            }
            in_range += 1;
            let p = (xa as f64) * (xb as f64);
            if (p as f32) as f64 == p {
                exact += 1;
            }
        }
    }
    (in_range, exact)
}

fn main() {
    let t0 = std::time::Instant::now();

    let (max_sig_bits, sig_pairs) = significand_width_check();

    let nthreads: usize = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(8);

    let chunk = N.div_ceil(nthreads);
    let mut results: Vec<(Counts, Witness)> = Vec::new();

    std::thread::scope(|s| {
        let mut handles = Vec::new();
        for t in 0..nthreads {
            let lo = t * chunk;
            let hi = ((t + 1) * chunk).min(N);
            handles.push(s.spawn(move || {
                let mut c = Counts::default();
                let mut w = Witness::default();
                for a in lo..hi {
                    let xa = bf16_to_f32(a as u16);
                    for b in 0..N {
                        let xb = bf16_to_f32(b as u16);
                        classify(xa, xb, &mut c, &mut w, a as u16, b as u16);
                    }
                }
                (c, w)
            }));
        }
        for h in handles {
            results.push(h.join().unwrap());
        }
    });

    let mut total = Counts::default();
    let mut wit = Witness::default();
    for (c, w) in &results {
        total.merge(c);
        wit.merge(w);
    }

    let elapsed = t0.elapsed();
    let all = (N as u64) * (N as u64);

    println!("================================================================");
    println!("EXHAUSTIVE bf16 x bf16 -> fp32 ROUNDING CENSUS");
    println!("================================================================");
    println!("ordered pairs enumerated : {}", total.total());
    println!("expected (2^32)          : {}", all);
    assert_eq!(total.total(), all, "did not cover the full space");
    println!("wall clock               : {:.2?}  ({} threads)", elapsed, nthreads);
    println!();
    println!("STRUCTURAL CHECK (significand width)");
    println!("  8-bit x 8-bit significand pairs enumerated : {}", sig_pairs);
    println!("  max bits in the integer product            : {}", max_sig_bits);
    println!("  fp32 significand bits available            : 24");
    println!(
        "  significand argument holds                 : {}",
        max_sig_bits <= 24
    );
    println!();
    println!("CENSUS OVER ALL 2^32 ORDERED PAIRS");
    let pct = |x: u64| 100.0 * (x as f64) / (all as f64);
    println!(
        "  exact (no rounding)        {:>12}   {:8.5}%",
        total.exact,
        pct(total.exact)
    );
    println!(
        "  overflow to +/-inf         {:>12}   {:8.5}%",
        total.overflow_to_inf,
        pct(total.overflow_to_inf)
    );
    println!(
        "  underflow to zero          {:>12}   {:8.5}%",
        total.underflow_to_zero,
        pct(total.underflow_to_zero)
    );
    println!(
        "  inexact (fp32 subnormal)   {:>12}   {:8.5}%",
        total.inexact_subnormal,
        pct(total.inexact_subnormal)
    );
    println!(
        "  inexact (fp32 NORMAL)      {:>12}   {:8.5}%   <-- must be 0",
        total.inexact_normal,
        pct(total.inexact_normal)
    );
    println!(
        "  non-finite operand         {:>12}   {:8.5}%",
        total.nonfinite_operand,
        pct(total.nonfinite_operand)
    );
    println!();
    let rounding = total.overflow_to_inf + total.underflow_to_zero + total.inexact_subnormal
        + total.inexact_normal;
    let finite_pairs = all - total.nonfinite_operand;
    println!(
        "  ROUNDING EVENTS among finite-operand pairs : {} / {}  = {:.5}%",
        rounding,
        finite_pairs,
        100.0 * (rounding as f64) / (finite_pairs as f64)
    );
    println!("  max relative error (finite results)        : {:.6e}", wit.max_rel_err);
    println!();
    println!("FIRST WITNESSES");
    if let Some((a, b, p)) = wit.overflow {
        println!(
            "  overflow : bf16 0x{:04x} ({:e}) * 0x{:04x} ({:e}) = {:e} -> inf",
            a,
            bf16_to_f32(a),
            b,
            bf16_to_f32(b),
            p
        );
    } else {
        println!("  overflow : none");
    }
    if let Some((a, b, p)) = wit.underflow {
        println!(
            "  underflow: bf16 0x{:04x} ({:e}) * 0x{:04x} ({:e}) = {:e} -> 0",
            a,
            bf16_to_f32(a),
            b,
            bf16_to_f32(b),
            p
        );
    } else {
        println!("  underflow: none");
    }
    if let Some((a, b, p, q)) = wit.subnormal {
        println!(
            "  subnormal: bf16 0x{:04x} * 0x{:04x} = {:e} -> {:e}  (rel err {:.3e})",
            a,
            b,
            p,
            q,
            ((q as f64 - p) / p).abs()
        );
    } else {
        println!("  subnormal: none");
    }
    if let Some((a, b, p, q)) = wit.normal {
        println!(
            "  NORMAL-RANGE INEXACT (breaks the significand argument): \
             0x{:04x} * 0x{:04x} = {:e} -> {:e}",
            a, b, p, q
        );
    } else {
        println!("  normal-range inexact: NONE (significand argument intact)");
    }
    println!();
    println!("VERDICT");
    if total.inexact_normal == 0 {
        println!("  The SIGNIFICAND claim is exhaustively TRUE: whenever the product");
        println!("  lands in fp32's normal range it is represented exactly.");
    } else {
        println!("  The SIGNIFICAND claim is FALSE. See witness above.");
    }
    if rounding == 0 {
        println!("  The UNQUALIFIED claim 'never rounds' is exhaustively TRUE.");
    } else {
        println!(
            "  The UNQUALIFIED claim 'never rounds' is FALSE: {} of {} finite-operand",
            rounding, finite_pairs
        );
        println!("  pairs round. All failures are EXPONENT-RANGE, not significand.");
        println!("  bf16 shares fp32's 8-bit exponent field, so a bf16 product has");
        println!("  twice fp32's dynamic range and cannot always land in it.");
    }

    println!();
    println!("RANGE HYPOTHESIS -- the claim, correctly qualified");
    let (in_range, exact_in_range) = range_hypothesis();
    println!("  hypothesis: both operands normal/subnormal and nonzero, and the");
    println!("              unbiased exponents satisfy -126 <= ex + ey <= 126");
    println!("  pairs satisfying it        : {}", in_range);
    println!("  of those, EXACT            : {}", exact_in_range);
    println!(
        "  fraction exact             : {:.10}%",
        100.0 * (exact_in_range as f64) / (in_range as f64)
    );
    if in_range == exact_in_range {
        println!();
        println!("  So the correct statement is: bf16 x bf16 -> fp32 is EXACT whenever");
        println!("  the exponent sum stays in fp32's normal range, and that condition is");
        println!("  STATIC per block in a block-float design -- it is discharged once per");
        println!("  block, not sampled per element. The unqualified 'never rounds' is");
        println!("  false; the qualified version is exhaustively true.");
    } else {
        println!();
        println!("  The range hypothesis is NOT sufficient: {} counterexamples.",
                 in_range - exact_in_range);
    }
}
