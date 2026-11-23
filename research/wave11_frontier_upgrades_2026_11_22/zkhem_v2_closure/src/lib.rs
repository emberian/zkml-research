//! Standalone differential replica of the dregg-sig zk-Hem v2 millibit ledger, plus
//! quintic-Goldilocks (`F_{p^5} = F_p[X]/(X^5 - 3)`) rank checks for the Stage-0 mask-point
//! blinding argument. Research artifact; not a claim about a shipped system.
//!
//! Ledger formulas and constants ported from the dregg-sig working tree, read-only, as of
//! 2026-11-22 (paths relative to `/Users/ember/dev/dregg-sig/`):
//!
//! * `crates/agg/src/zk_hem/bounds.rs`
//!   - `log2_lo` :39, `log2_hi` :56, `log2_one_plus` :66, `sum_bits` :78, `query_bits` :84,
//!     `johnson_list` :104, `interpolation_margin` :111, `interpolation_holds` :133,
//!     `StageBound` :237, `siblings` :429.
//! * `crates/agg/src/zk_hem/v2/bounds.rs`
//!   - `FIELD_MILLIBITS` :38, `V2_STAGE_LIST_CAP` :42, QROM constants :45-50,
//!     `TARGET_LEVEL_MILLIBITS` :53, `Round` :57, `interpolation_witness_v2` :79,
//!     `affine_fold_numerator_v2` :113, `stage_lists_v2` :133, `stage_bound_v2` :144,
//!     `mask_line_bad_challenges` :195, `mask_line` :220,
//!     `dkt26_beyond_johnson_first_order` :230, `Report` :297 (+ impl :319-423),
//!     `opening_byte_and_digest_bounds` :425, `report_with`/`report_with_lookup` :456/:477
//!     (lookup path elided: `lookup = None` throughout), `report` :667,
//!     `min_stage0_queries` :751, `size` :790.
//! * `crates/agg/src/zk_hem/v2/params.rs`
//!   - constants :11-46, `Profile` :51, `StageSpec` :94, `Schedule` :101, `STAGE0_QUERIES` :111,
//!     `later_stage_queries` :115, `schedule` :120, `schedule_with_stage0` :128, `ShapeSize`
//!     :155, `Layout` :240 (lookup field elided), `mask_cells` :257, `blind_cells_for` :263,
//!     `Layout::new` :269, `Layout::search` :283.
//! * `crates/agg/src/pcs.rs`
//!   - `MAX_PCS_NUM_VARS` :86, `stage_geometry` :355-452 (blowup / step_vars / early_stop only).
//! * `crates/agg/src/zk_hem/v2/pcs.rs`
//!   - `mask_points_good` :731-738.
//! * `crates/agg/src/zk_hem/v2/field5.rs`
//!   - `FP5_W = 3` :25, `FROBENIUS_ZETA5` :29-32 (pinned `1_041_288_259_238_279_555`),
//!     `frobenius_pow` :336 (coefficient `i` scaled by `zeta5^(i k)`), `is_base` :195.
//!
//! The classical and QROM work searches scan downward because rounding can create disjoint
//! passing intervals. The upstream patch contains the same repair.
//! The field arithmetic below is an independent, deliberately naive re-implementation
//! (`u128 % p`), not a port of dregg-sig's constant-time code.

#![forbid(unsafe_code)]

// =====================================================================================
// Shared millibit ledger: crates/agg/src/zk_hem/bounds.rs
// =====================================================================================

/// A lower bound on `-log2` of a probability, in thousandths of a bit.
pub type MilliBits = i64;

/// `crates/agg/src/pcs.rs:86`.
pub const MAX_PCS_NUM_VARS: usize = 28;

/// A lower bound on `1000 log2(x)` with downward rounding; `x > 0`. (bounds.rs:39)
pub fn log2_lo(x: u128) -> MilliBits {
    assert!(x > 0);
    let lz = x.leading_zeros();
    let exponent = (127 - lz) as i64;
    let mut y = (x << lz) >> 64;
    let mut frac = 0i64;
    for bit in (0..24).rev() {
        y = (y * y) >> 63;
        if y >= 1u128 << 64 {
            y >>= 1;
            frac |= 1 << bit;
        }
    }
    exponent * 1000 + (frac * 1000) / (1 << 24)
}

/// An upper bound on `1000 log2(x)`; `x > 0`. (bounds.rs:56)
pub fn log2_hi(x: u128) -> MilliBits {
    if x.is_power_of_two() {
        log2_lo(x)
    } else {
        log2_lo(x) + 2
    }
}

/// An upper bound on `1000 log2(1 + 2^(-d / 1000))` for `d >= 0`. (bounds.rs:66)
pub fn log2_one_plus(d: MilliBits) -> MilliBits {
    const EIGHTHS: [i64; 8] = [1000, 918, 841, 772, 708, 649, 595, 546];
    assert!(d >= 0);
    let steps = d / 125;
    let shift = steps / 8;
    if shift >= 40 {
        return 1;
    }
    (((1443 * EIGHTHS[(steps % 8) as usize] + 999) / 1000) >> shift).min(999) + 1
}

/// A lower bound on `-log2(2^(-a / 1000) + 2^(-b / 1000))`. (bounds.rs:78)
pub fn sum_bits(a: MilliBits, b: MilliBits) -> MilliBits {
    a.min(b) - log2_one_plus((a - b).abs())
}

/// `-log2` of the probability that `queries` distinct uniform positions out of `n` all fall in
/// a set of `agreement` positions; `None` when that probability is zero. (bounds.rs:84)
pub fn query_bits(n: u128, agreement: u128, queries: usize) -> Option<MilliBits> {
    if agreement < queries as u128 {
        return None;
    }
    assert!(agreement <= n);
    let mut mantissa = 1u128 << 64;
    let mut exponent = 0i64;
    for i in 0..queries as u128 {
        mantissa = (mantissa * (agreement - i)).div_ceil(n - i);
        while mantissa < 1u128 << 63 {
            mantissa *= 2;
            exponent += 1;
        }
    }
    Some(exponent * 1000 + 64_000 - log2_hi(mantissa))
}

/// Johnson list bound (`[CWYZ26]` Lemma 3.2). (bounds.rs:104)
pub fn johnson_list(n: u128, agree: u128, d: u128) -> Option<u128> {
    let denominator = (agree * agree).checked_sub(n * d).filter(|&v| v > 0)?;
    Some(n * agree.checked_sub(d)? / denominator)
}

/// `[CWYZ26]` interpolation inequality (4.5): `(M, lhs - rhs)`. (bounds.rs:111)
pub fn interpolation_margin(
    n: u128,
    d: u128,
    a: u128,
    m: u128,
    big_d: u128,
) -> Option<(u128, i128)> {
    let big_m = big_d.min((m * a).checked_sub(big_d + 1)? / d);
    if big_m == 0 {
        return None;
    }
    let lhs: u128 = (0..=big_m)
        .map(|j| (m * a - big_d - d * j) * (big_d - j + 1))
        .sum();
    let rhs: u128 = n
        * (0..=big_m.min(m - 1))
            .map(|s| (m - s) * (big_d - s + 1))
            .sum::<u128>();
    Some((big_m, lhs as i128 - rhs as i128))
}

/// Whether (4.5) holds; returns `M`. (bounds.rs:133)
pub fn interpolation_holds(n: u128, d: u128, a: u128, m: u128, big_d: u128) -> Option<u128> {
    interpolation_margin(n, d, a, m, big_d)
        .filter(|&(_, margin)| margin > 0)
        .map(|(big_m, _)| big_m)
}

/// Bounds for one WHIR stage. (bounds.rs:237)
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StageBound {
    pub blowup: usize,
    pub step_vars: usize,
    pub queries: usize,
    pub fibers: u128,
    pub agreement: u128,
    pub word_list: u128,
    pub list: u128,
    pub query_bits: Option<MilliBits>,
    pub fold_bits: MilliBits,
}

/// Authentication siblings of `queries` leaves in a tree of `2^log_leaves` leaves. (bounds.rs:429)
pub fn siblings(queries: usize, log_leaves: usize) -> usize {
    if queries >> log_leaves != 0 {
        return 0;
    }
    queries * (log_leaves - queries.ilog2() as usize)
}

// =====================================================================================
// Parameters: crates/agg/src/zk_hem/v2/params.rs and crates/agg/src/pcs.rs
// =====================================================================================

pub const DIGEST_BYTES: usize = 50;
pub const TREE_NONCE_BYTES: usize = 32;
pub const SALT_BYTES: usize = 32;
pub const LIMBS: usize = 5;
pub const EXT_BYTES: usize = 8 * LIMBS;
pub const MASK_POINTS: usize = 5;
pub const LATER_OOD_POINTS: usize = 2;
pub const ROW_DEGREE: usize = 9;
pub const COL_DEGREE: usize = 2;
pub const LOOKUP_DEGREE: usize = 4;
pub const ROW_MASK_BITS: usize = 4;
pub const COL_MASK_BITS: usize = 2;
pub const LOOKUP_MASK_BITS: usize = 3;
pub const PAD_VARS: usize = LIMBS;
pub const PAD_ROWS: usize = 24;
pub const VAR_ALIGN_MIN: usize = 4;
pub const MIN_LOG_CELLS: usize = 16;
pub const MAX_LOG_CELLS: usize = 28;

/// params.rs:51.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub enum Profile {
    CshakeJohnson400,
    #[default]
    TurboShakeJohnson400,
}

impl Profile {
    pub const ALL: [Self; 2] = [Self::CshakeJohnson400, Self::TurboShakeJohnson400];
}

/// params.rs:94.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StageSpec {
    pub blowup: usize,
    pub step_vars: usize,
    pub num_queries: usize,
}

/// params.rs:101.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Schedule {
    pub early_stop_vars: usize,
    pub stages: Vec<StageSpec>,
}

/// `crates/agg/src/pcs.rs:355` `stage_geometry` (blowup / step_vars / early_stop; queries 0).
pub fn stage_geometry(num_vars: usize) -> Schedule {
    assert!(
        (2..=MAX_PCS_NUM_VARS).contains(&num_vars),
        "unsupported PCS num_vars={num_vars}"
    );
    let sp = |blowup: usize, step_vars: usize| StageSpec {
        blowup,
        step_vars,
        num_queries: 0,
    };
    let mk = |es: usize, stages: Vec<StageSpec>| Schedule {
        early_stop_vars: es,
        stages,
    };
    if num_vars <= 6 {
        let es = if num_vars <= 3 { 1 } else { 2 };
        return mk(es, vec![sp(16, num_vars - es)]);
    }
    if num_vars <= 11 {
        let es = if num_vars <= 8 { 3 } else { 4 };
        let rem = num_vars - es;
        let s0 = rem.div_ceil(2);
        let s1 = rem - s0;
        return mk(es, vec![sp(4, s0), sp(16, s1)]);
    }
    if num_vars <= 16 {
        let es = if num_vars <= 13 {
            4
        } else if num_vars <= 15 {
            5
        } else {
            6
        };
        let rem = num_vars - es;
        let s0 = 4usize.min(rem - 4);
        let s1 = (rem - s0) / 2;
        let s2 = rem - s0 - s1;
        return mk(es, vec![sp(4, s0), sp(16, s1), sp(64, s2)]);
    }
    if num_vars <= 20 {
        let es = num_vars - 12;
        return mk(es, vec![sp(4, 5), sp(16, 3), sp(64, 4)]);
    }
    match num_vars {
        21 => mk(8, vec![sp(4, 6), sp(16, 3), sp(64, 4)]),
        22 => mk(8, vec![sp(4, 6), sp(16, 4), sp(64, 4)]),
        23 => mk(7, vec![sp(4, 6), sp(16, 4), sp(64, 3), sp(256, 3)]),
        24 => mk(8, vec![sp(4, 6), sp(16, 4), sp(64, 3), sp(256, 3)]),
        25 => mk(8, vec![sp(4, 6), sp(16, 4), sp(64, 4), sp(256, 3)]),
        26 => mk(8, vec![sp(4, 6), sp(16, 5), sp(64, 4), sp(256, 3)]),
        27 => mk(8, vec![sp(4, 6), sp(16, 5), sp(64, 4), sp(256, 4)]),
        28 => mk(8, vec![sp(4, 6), sp(16, 6), sp(64, 4), sp(256, 4)]),
        _ => unreachable!(),
    }
}

/// params.rs:111.
pub const STAGE0_QUERIES: [usize; MAX_LOG_CELLS - MIN_LOG_CELLS + 1] =
    [267, 267, 267, 267, 267, 267, 267, 267, 266, 266, 266, 266, 266];

/// params.rs:115.
pub const fn later_stage_queries(blowup: usize) -> usize {
    (532usize).div_ceil(blowup.trailing_zeros() as usize) + 3
}

/// params.rs:120.
pub fn schedule(log_cells: usize) -> Option<Schedule> {
    if !(MIN_LOG_CELLS..=MAX_LOG_CELLS).contains(&log_cells) {
        return None;
    }
    schedule_with_stage0(log_cells, STAGE0_QUERIES[log_cells - MIN_LOG_CELLS])
}

/// params.rs:128.
pub fn schedule_with_stage0(log_cells: usize, stage0_queries: usize) -> Option<Schedule> {
    if !(MIN_LOG_CELLS..=MAX_PCS_NUM_VARS).contains(&log_cells) {
        return None;
    }
    let geometry = stage_geometry(log_cells);
    let stages = geometry
        .stages
        .iter()
        .enumerate()
        .map(|(i, st)| StageSpec {
            blowup: st.blowup,
            step_vars: st.step_vars,
            num_queries: if i == 0 {
                stage0_queries
            } else {
                later_stage_queries(st.blowup)
            },
        })
        .collect();
    Some(Schedule {
        early_stop_vars: geometry.early_stop_vars,
        stages,
    })
}

/// params.rs:155.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShapeSize {
    pub log_rows: usize,
    pub num_vars: usize,
    pub num_public: usize,
}

/// params.rs:240 (lookup field elided).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layout {
    pub log_cells: usize,
    pub var_bits: usize,
    pub var_cells: usize,
    pub var_align: usize,
    pub mask_base: usize,
    pub blind_cells: usize,
    pub schedule: Schedule,
}

/// params.rs:257.
pub const fn mask_cells(log_rows: usize, var_bits: usize) -> usize {
    ((log_rows * LIMBS) << ROW_MASK_BITS) + ((var_bits * LIMBS) << COL_MASK_BITS)
}

/// params.rs:263.
pub const fn blind_cells_for(step_vars: usize, opened_fibers: usize) -> usize {
    (opened_fibers + LIMBS * MASK_POINTS) << step_vars
}

impl Layout {
    /// params.rs:269.
    pub fn new(size: ShapeSize) -> Option<Self> {
        Self::search(size, schedule)
    }

    /// params.rs:283.
    pub fn search(size: ShapeSize, schedule: impl Fn(usize) -> Option<Schedule>) -> Option<Self> {
        if size.num_vars < 1 + 3 * PAD_VARS
            || size.num_vars > 1usize << MAX_LOG_CELLS
            || size.num_public > size.num_vars - 1 - 3 * PAD_VARS
            || !(5..usize::BITS as usize).contains(&size.log_rows)
        {
            return None;
        }
        let var_bits = size.num_vars.next_power_of_two().trailing_zeros().max(1) as usize;
        let var_align = VAR_ALIGN_MIN.max(var_bits.saturating_sub(8));
        let var_cells = size.num_vars.next_multiple_of(1 << var_align);
        let masks = mask_cells(size.log_rows, var_bits);
        (var_bits.max(MIN_LOG_CELLS)..=MAX_LOG_CELLS).find_map(|log_cells| {
            let schedule = schedule(log_cells)?;
            let st0 = schedule.stages[0];
            let cells = 1usize << log_cells;
            let fibers = (cells * st0.blowup) >> st0.step_vars;
            let blind_cells = blind_cells_for(st0.step_vars, st0.num_queries.min(fibers));
            (var_cells + masks + blind_cells <= cells).then_some(Self {
                log_cells,
                var_bits,
                var_cells,
                var_align,
                mask_base: var_cells,
                blind_cells,
                schedule,
            })
        })
    }
}

// =====================================================================================
// v2 bounds: crates/agg/src/zk_hem/v2/bounds.rs
// =====================================================================================

/// `floor(1000 log2(p^5 - 1)) - 1`. (v2/bounds.rs:38)
pub const FIELD_MILLIBITS: MilliBits = 319_998;
/// v2/bounds.rs:42.
pub const V2_STAGE_LIST_CAP: u128 = 16_384;
/// v2/bounds.rs:45.
pub const QROM_RBR_CONST: MilliBits = 8_322;
/// v2/bounds.rs:47.
pub const QROM_MERKLE_CONST: MilliBits = 12_640;
/// v2/bounds.rs:50.
pub const QROM_ROUND_SLACK: MilliBits = 23;
/// v2/bounds.rs:53.
pub const TARGET_LEVEL_MILLIBITS: MilliBits = 128_000;

/// v2/bounds.rs:57.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Round {
    Sumcheck,
    OutOfDomain(usize),
    KernelFold(usize),
    AffineFold(usize),
    MaskLine,
    Query(usize),
    LookupCompression,
    LookupPoles,
    LookupSumcheck,
}

/// v2/bounds.rs:79.
pub fn interpolation_witness_v2(n: u128, d: u128, a: u128, m: u128) -> Option<(u128, u128)> {
    let margin = |big_d: u128| interpolation_margin(n, d, a, m, big_d).map_or(i128::MIN, |v| v.1);
    let (mut lo, mut hi) = (
        1u128,
        ((2 * m + 1) * (2 * m + 1) * n).div_ceil(12 * d).max(2),
    );
    while hi - lo > 2 {
        let third = (hi - lo) / 3;
        let (left, right) = (lo + third, hi - third);
        if margin(left) < margin(right) {
            lo = left + 1;
        } else {
            hi = right - 1;
        }
    }
    let peak = (lo..=hi).max_by_key(|&v| margin(v))?;
    if margin(peak) <= 0 {
        return None;
    }
    let (mut lo, mut hi) = (1u128, peak);
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if margin(mid) > 0 {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    interpolation_holds(n, d, a, m, lo).map(|big_m| (lo, big_m))
}

/// v2/bounds.rs:113.
pub fn affine_fold_numerator_v2(n: u128, d: u128, a: u128) -> Option<u128> {
    let b = a.checked_sub(1)?;
    let list = johnson_list(n, b, d + 1)?;
    let list0 = johnson_list(n, b, d)?;
    let mut m = 1u128;
    while m <= 1024 {
        if let Some((big_d, big_m)) = interpolation_witness_v2(n, d, a, m) {
            let nonpersistent = (2 * log2_hi(big_d))
                .max(2000 + 2 * log2_hi(d) + 2 * log2_hi(big_m) + 3 * log2_hi(big_d))
                + 1000
                + 2 * log2_hi(n);
            if nonpersistent < FIELD_MILLIBITS {
                return Some(list + 2 * list0 + 1);
            }
        }
        m *= 2;
    }
    None
}

/// v2/bounds.rs:133.
pub fn stage_lists_v2(fibers: u128, blowup: u128, folds: u32, a: u128) -> Option<u128> {
    let mut worst = 0u128;
    for level in 0..folds {
        let scale = 1u128 << level;
        let n = fibers * scale;
        worst = worst.max(affine_fold_numerator_v2(n, n / blowup + 2, a * scale)?);
    }
    (u128::from(folds) * worst + 1 < V2_STAGE_LIST_CAP).then_some(worst)
}

/// v2/bounds.rs:144.
pub fn stage_bound_v2(
    blowup: usize,
    step_vars: usize,
    queries: usize,
    rem_after: usize,
    agreement: Option<u128>,
) -> Option<StageBound> {
    let fibers = (blowup as u128) << rem_after;
    let folds = step_vars as u32;
    let top = fibers.checked_sub(u128::from(folds))?;
    let feasible = |a: u128| stage_lists_v2(fibers, blowup as u128, folds, a);
    let agreement = match agreement {
        Some(a) => a.min(top),
        None => {
            feasible(top)?;
            let (mut lo, mut hi) = (1u128, top);
            while lo < hi {
                let mid = lo + (hi - lo) / 2;
                if feasible(mid).is_some() {
                    hi = mid;
                } else {
                    lo = mid + 1;
                }
            }
            lo
        }
    };
    let list = feasible(agreement)?;
    let points = fibers << folds;
    Some(StageBound {
        blowup,
        step_vars,
        queries,
        fibers,
        agreement,
        word_list: johnson_list(points, agreement << folds, points / blowup as u128 + 2)?,
        list,
        query_bits: query_bits(
            fibers,
            agreement + u128::from(folds),
            queries.min(fibers as usize),
        ),
        fold_bits: FIELD_MILLIBITS - log2_hi(list),
    })
}

/// `[DKT26]` Theorem 5.12 with `d = 1`: `(agreement_threshold, b_cf)`. (v2/bounds.rs:195)
pub fn mask_line_bad_challenges(blowup: usize, rem: usize, m: u128) -> (u128, u128) {
    assert!((3..=512).contains(&m));
    assert!(blowup.is_power_of_two() && blowup <= 256 && rem <= MAX_PCS_NUM_VARS);
    let fibers = (blowup as u128) << rem;
    let k = (1u128 << rem) + 2;
    let big_d = k - 1;
    let covers = |a: u128| (2 * m * a) * (2 * m * a) >= (2 * m + 1) * (2 * m + 1) * fibers * k;
    assert!(covers(fibers), "line threshold exceeds the domain");
    let (mut lo, mut hi) = (1u128, fibers);
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if covers(mid) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    let two_m_plus_1 = 2 * m + 1;
    let cube = two_m_plus_1 * two_m_plus_1 * two_m_plus_1;
    let b_cf = (cube * fibers * fibers).div_ceil(3 * big_d);
    (lo, b_cf)
}

/// v2/bounds.rs:220.
pub fn mask_line(blowup: usize, rem: usize, m: u128) -> (u128, MilliBits) {
    let (lo, b_cf) = mask_line_bad_challenges(blowup, rem, m);
    (lo, FIELD_MILLIBITS - log2_hi(b_cf.max(1)))
}

/// v2/bounds.rs:230.
pub fn dkt26_beyond_johnson_first_order(
    blowup: usize,
    rem: usize,
    step_vars: usize,
    eta_inv: u128,
) -> (u128, MilliBits, usize) {
    assert!(blowup.is_power_of_two() && (4..=256).contains(&blowup));
    assert!(rem <= MAX_PCS_NUM_VARS && step_vars <= 6);
    assert!((4..=1 << 20).contains(&eta_inv));
    let fibers = (blowup as u128) << rem;
    let k = (1u128 << rem) + 2;
    let rhs = eta_inv * (fibers + k) + 3 * fibers;
    let denom = 3 * eta_inv;
    let threshold = rhs.div_ceil(denom);
    assert!(threshold + step_vars as u128 <= fibers);
    let bad = eta_inv * fibers * fibers + 4;
    let mca_bits = FIELD_MILLIBITS - log2_hi(bad);
    let agree_after_folds = threshold + step_vars as u128;
    let mut lo = 1usize;
    let mut hi = 2048usize;
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if query_bits(fibers, agree_after_folds, mid.min(fibers as usize))
            .is_none_or(|b| b - 1000 >= 265_010)
        {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    (threshold, mca_bits, lo)
}

/// v2/bounds.rs:297 (lookup-only fields kept for shape; always single-tree here).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Report {
    pub profile: Profile,
    pub log_cells: usize,
    pub schedule: Schedule,
    pub stages: Vec<StageBound>,
    pub rounds: usize,
    pub rbr_bits: MilliBits,
    pub rbr_round: Round,
    pub mask_m: u128,
    pub mask_bits: MilliBits,
    pub blind_cells: usize,
    pub opened_symbols: usize,
    pub mask_values: usize,
    pub stage0_trees: usize,
    pub helper_mask_budget: Option<(usize, usize, usize)>,
    pub proof_bytes: usize,
    pub digests: usize,
    pub merkle_hashes: u128,
}

impl Report {
    /// v2/bounds.rs:320.
    pub fn view_perfectly_simulated(&self) -> bool {
        self.blind_cells >= self.opened_symbols + LIMBS * self.mask_values
            && self
                .helper_mask_budget
                .is_none_or(|(b, opened, masks)| b >= opened + LIMBS * masks)
    }

    fn digest_millibits(&self) -> MilliBits {
        8000 * DIGEST_BYTES as i64
    }

    pub fn classical_sum_bits(&self, log_t: MilliBits) -> MilliBits {
        sum_bits(
            self.rbr_bits - log_t,
            self.digest_millibits() - 2000 - 2 * log_t,
        )
    }

    pub fn classical_work_bits(&self) -> MilliBits {
        let (lo, hi) = (0, self.rbr_bits.min((self.digest_millibits() - 2000) / 2));
        assert!(self.classical_sum_bits(lo) >= 0);
        // Rounding the log-sum correction to eighth-bit buckets can split the passing set.
        (lo..=hi).rev().find(|&w| self.classical_sum_bits(w) >= 0).unwrap()
    }

    pub fn classical_error_bits(&self, log_queries: u32) -> MilliBits {
        assert!(log_queries >= 2);
        let t = 1000 * i64::from(log_queries);
        self.classical_sum_bits(t)
    }

    pub fn qrom_work_terms(&self) -> (MilliBits, MilliBits) {
        (
            (self.rbr_bits - QROM_RBR_CONST - QROM_ROUND_SLACK) / 2,
            (self.digest_millibits() - QROM_MERKLE_CONST - QROM_ROUND_SLACK) / 3,
        )
    }

    pub fn qrom_sum_bits(&self, log_t: MilliBits) -> MilliBits {
        sum_bits(
            self.rbr_bits - QROM_RBR_CONST - QROM_ROUND_SLACK - 2 * log_t,
            self.digest_millibits() - QROM_MERKLE_CONST - QROM_ROUND_SLACK - 3 * log_t,
        )
    }

    pub fn qrom_work_bits(&self) -> MilliBits {
        let (rbr, digest) = self.qrom_work_terms();
        let (lo, hi) = (24_000, rbr.min(digest));
        assert!(self.rounds < 1 << 9 && self.qrom_sum_bits(lo) >= 0 && hi >= lo);
        // Rounding the log-sum correction to eighth-bit buckets can split the passing set.
        (lo..=hi).rev().find(|&w| self.qrom_sum_bits(w) >= 0).unwrap()
    }

    pub fn qrom_error_bits(&self, log_queries: u32) -> MilliBits {
        assert!(log_queries >= 24 && self.rounds < 1 << 9);
        let t = 1000 * i64::from(log_queries);
        self.qrom_sum_bits(t)
    }

    fn with_salt_collisions(&self, query_bits: MilliBits, log_proofs: u32) -> MilliBits {
        if log_proofs == 0 {
            return query_bits;
        }
        let collision_bits =
            1000 * (8 * TREE_NONCE_BYTES as i64 + 1 - 2 * i64::from(log_proofs));
        sum_bits(query_bits, collision_bits)
    }

    pub fn classical_hiding_bits(&self, log_queries: u32, log_proofs: u32) -> MilliBits {
        let log_proofs = log_proofs + self.stage0_trees.ilog2();
        self.with_salt_collisions(
            1000 * (8 * SALT_BYTES as i64 - i64::from(log_queries) - i64::from(log_proofs)),
            log_proofs,
        )
    }

    pub fn quantum_hiding_bits(&self, log_queries: u32, log_proofs: u32) -> MilliBits {
        let log_proofs = log_proofs + self.stage0_trees.ilog2();
        self.with_salt_collisions(
            500 * (8 * SALT_BYTES as i64 - i64::from(log_proofs))
                - 1000 * (i64::from(log_queries) + 1),
            log_proofs,
        )
    }
}

/// v2/bounds.rs:425.
pub fn opening_byte_and_digest_bounds(
    log_cells: usize,
    schedule: &Schedule,
    stages: &[StageBound],
) -> (usize, usize, u128) {
    let fold_vars = log_cells - schedule.early_stop_vars;
    let mut digests = stages.len();
    let mut bytes = TREE_NONCE_BYTES
        + DIGEST_BYTES
        + EXT_BYTES * (MASK_POINTS + 5 * fold_vars + 1 + (1usize << schedule.early_stop_vars) + 2);
    let mut merkle_hashes = 0u128;
    let mut rem = log_cells;
    for (i, st) in stages.iter().enumerate() {
        let log_leaves = rem + st.blowup.trailing_zeros() as usize - st.step_vars;
        let opened = st.queries.min(st.fibers as usize);
        let sib = siblings(opened, log_leaves);
        digests += sib;
        merkle_hashes += 2 * st.fibers;
        bytes += 4 + DIGEST_BYTES * sib;
        bytes += if i == 0 {
            opened * (SALT_BYTES + (8usize << st.step_vars) + EXT_BYTES)
        } else {
            DIGEST_BYTES + LATER_OOD_POINTS * EXT_BYTES + opened * (EXT_BYTES << st.step_vars)
        };
        rem -= st.step_vars;
    }
    (bytes, digests, merkle_hashes)
}

/// v2/bounds.rs:456/477 `report_with` (= `report_with_lookup(.., lookup = None, ..)`).
pub fn report_with(
    profile: Profile,
    size: ShapeSize,
    log_cells: usize,
    var_bits: usize,
    blind_cells: usize,
    schedule: &Schedule,
) -> Option<Report> {
    if !(MIN_LOG_CELLS..=MAX_PCS_NUM_VARS).contains(&log_cells)
        || !(5..usize::BITS as usize).contains(&size.log_rows)
        || !(16..=1usize << log_cells).contains(&size.num_vars)
        || size.num_public > size.num_vars - 16
        || !(1..=log_cells).contains(&var_bits)
        || schedule.stages.is_empty()
        || schedule.early_stop_vars >= log_cells
        || schedule.stages.iter().any(|st| {
            st.step_vars == 0
                || st.step_vars > log_cells
                || st.num_queries == 0
                || !st.blowup.is_power_of_two()
                || !(4..=256).contains(&st.blowup)
        })
        || schedule
            .stages
            .iter()
            .try_fold(log_cells, |rem, st| rem.checked_sub(st.step_vars))
            != Some(schedule.early_stop_vars)
    {
        return None;
    }
    let mut rem = log_cells;
    let base: Vec<StageBound> = schedule
        .stages
        .iter()
        .map(|spec| {
            rem -= spec.step_vars;
            stage_bound_v2(spec.blowup, spec.step_vars, spec.num_queries, rem, None)
        })
        .collect::<Option<_>>()?;
    let spec0 = schedule.stages[0];
    let rem0 = log_cells - spec0.step_vars;

    let evaluate = |stages: &[StageBound], mask: MilliBits| -> (MilliBits, Round) {
        let mut worst = (MilliBits::MAX, Round::Sumcheck);
        let mut note = |bits: MilliBits, round: Round| {
            if bits < worst.0 {
                worst = (bits, round);
            }
        };
        let degree = size
            .log_rows
            .max(ROW_DEGREE)
            .max((1 << ROW_MASK_BITS) - 1)
            .max(4 + size.num_public) as u128;
        note(
            FIELD_MILLIBITS - log2_hi(degree * stages[0].word_list),
            Round::Sumcheck,
        );
        // (lookup rounds elided: lookup = None)
        note(mask, Round::MaskLine);
        let mut rem = log_cells;
        for (i, st) in stages.iter().enumerate() {
            let degree = (1u128 << rem) + 2;
            let points = if i == 0 {
                MASK_POINTS
            } else {
                LATER_OOD_POINTS
            } as i64;
            let mut ood =
                points * (FIELD_MILLIBITS - log2_hi(degree)) + 1000 - 2 * log2_hi(st.word_list);
            if i == 0 {
                ood = ood.min(FIELD_MILLIBITS - log2_hi(MASK_POINTS as u128 * st.word_list));
            }
            note(ood, Round::OutOfDomain(i));
            let fold = FIELD_MILLIBITS - log2_hi(st.list);
            note(fold, Round::KernelFold(i));
            note(fold, Round::AffineFold(i));
            let batch = stages.get(i + 1).map_or(MilliBits::MAX, |next| {
                FIELD_MILLIBITS - log2_hi((st.queries as u128 + 2) * next.word_list) - 1000
            });
            let query = st.query_bits.map_or(MilliBits::MAX, |bits| bits - 1000);
            if query.min(batch) != MilliBits::MAX {
                note(query.min(batch), Round::Query(i));
            }
            rem -= st.step_vars;
        }
        worst
    };

    let mut best: Option<(MilliBits, Round, u128, MilliBits, Vec<StageBound>)> = None;
    for m in 3..=512u128 {
        let (threshold, b_cf) = mask_line_bad_challenges(spec0.blowup, rem0, m);
        let binding = threshold > base[0].agreement;
        let mut stages = base.clone();
        if binding {
            stages[0] = stage_bound_v2(
                spec0.blowup,
                spec0.step_vars,
                spec0.num_queries,
                rem0,
                Some(threshold),
            )?;
        }
        let pairs = johnson_list(stages[0].fibers, stages[0].agreement, (1u128 << rem0) + 1)?;
        let mask = FIELD_MILLIBITS - log2_hi((b_cf + pairs).max(1));
        let (bits, round) = evaluate(&stages, mask);
        if best.as_ref().is_none_or(|b| bits > b.0) {
            best = Some((bits, round, m, mask, stages));
        }
        if !binding {
            break;
        }
    }
    let (rbr_bits, rbr_round, mask_m, mask_bits, stages) = best?;

    let fold_vars = log_cells - schedule.early_stop_vars;
    let rounds =
        5 + size.log_rows + var_bits + 2 + 2 * fold_vars + 1 + (stages.len() - 1) + stages.len();
    let front = 1 + (ROW_DEGREE + 1) * size.log_rows + 3 + 1 + (COL_DEGREE + 1) * var_bits;
    let (open_bytes, digests, merkle_hashes) =
        opening_byte_and_digest_bounds(log_cells, schedule, &stages);
    let proof_bytes = 8 + 1 + 1 + EXT_BYTES * front + open_bytes;

    let opened0 = spec0.num_queries.min(stages[0].fibers as usize);
    Some(Report {
        profile,
        log_cells,
        schedule: schedule.clone(),
        stages,
        rounds,
        rbr_bits,
        rbr_round,
        mask_m,
        mask_bits,
        blind_cells,
        opened_symbols: opened0 << spec0.step_vars,
        mask_values: MASK_POINTS << spec0.step_vars,
        stage0_trees: 1,
        helper_mask_budget: None,
        proof_bytes,
        digests,
        merkle_hashes,
    })
}

/// v2/bounds.rs:667.
pub fn report(profile: Profile, size: ShapeSize) -> Option<Report> {
    let layout = Layout::new(size)?;
    report_with(
        profile,
        size,
        layout.log_cells,
        layout.var_bits,
        layout.blind_cells,
        &layout.schedule,
    )
}

/// v2/bounds.rs:751.
pub fn min_stage0_queries(log_cells: usize, target: MilliBits) -> Option<usize> {
    if !(MIN_LOG_CELLS..=MAX_PCS_NUM_VARS).contains(&log_cells) {
        return None;
    }
    let size = ShapeSize {
        log_rows: log_cells,
        num_vars: 1 << (log_cells - 1),
        num_public: 0,
    };
    let meets = |q: usize| {
        schedule_with_stage0(log_cells, q)
            .and_then(|s| {
                report_with(
                    Profile::CshakeJohnson400,
                    size,
                    log_cells,
                    log_cells - 1,
                    0,
                    &s,
                )
            })
            .is_some_and(|r| r.qrom_sum_bits(24_000) >= 0 && r.qrom_work_bits() >= target)
    };
    let (mut lo, mut hi) = (1usize, 2048usize);
    if !meets(hi) {
        return None;
    }
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if meets(mid) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    Some(lo)
}

/// v2/bounds.rs:790.
pub fn size(log_rows: usize, num_vars: usize) -> ShapeSize {
    ShapeSize {
        log_rows,
        num_vars,
        num_public: 0,
    }
}

// =====================================================================================
// Goldilocks and F_{p^5} = F_p[X]/(X^5 - 3) (independent naive implementation)
// =====================================================================================

/// `p = 2^64 - 2^32 + 1`.
pub const P: u64 = 0xFFFF_FFFF_0000_0001;
/// dregg-sig `v2/field5.rs:30` pinned value of `3^((p-1)/5)`.
pub const PINNED_FROBENIUS_ZETA5: u64 = 1_041_288_259_238_279_555;

#[inline]
pub fn fadd(a: u64, b: u64) -> u64 {
    ((a as u128 + b as u128) % P as u128) as u64
}
#[inline]
pub fn fsub(a: u64, b: u64) -> u64 {
    ((a as u128 + P as u128 - b as u128) % P as u128) as u64
}
#[inline]
pub fn fmul(a: u64, b: u64) -> u64 {
    ((a as u128 * b as u128) % P as u128) as u64
}
pub fn fpow(mut a: u64, mut e: u64) -> u64 {
    let mut r = 1u64;
    a %= P;
    while e > 0 {
        if e & 1 == 1 {
            r = fmul(r, a);
        }
        a = fmul(a, a);
        e >>= 1;
    }
    r
}
pub fn finv(a: u64) -> u64 {
    assert!(a % P != 0);
    fpow(a, P - 2)
}

/// `zeta5 = 3^((p-1)/5)`.
pub fn zeta5() -> u64 {
    fpow(3, (P - 1) / 5)
}

/// Element of `F_p[X]/(X^5 - 3)` in the power basis.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Fp5(pub [u64; 5]);

impl Fp5 {
    pub const ZERO: Self = Self([0; 5]);
    pub const ONE: Self = Self([1, 0, 0, 0, 0]);

    pub fn from_base(a: u64) -> Self {
        Self([a % P, 0, 0, 0, 0])
    }
    pub fn is_base(self) -> bool {
        self.0[1..].iter().all(|&c| c == 0)
    }
    pub fn is_zero(self) -> bool {
        self.0.iter().all(|&c| c == 0)
    }
    pub fn add(self, o: Self) -> Self {
        Self(core::array::from_fn(|i| fadd(self.0[i], o.0[i])))
    }
    pub fn sub(self, o: Self) -> Self {
        Self(core::array::from_fn(|i| fsub(self.0[i], o.0[i])))
    }
    pub fn neg(self) -> Self {
        Self::ZERO.sub(self)
    }
    pub fn scale(self, c: u64) -> Self {
        Self(core::array::from_fn(|i| fmul(self.0[i], c)))
    }
    pub fn mul(self, o: Self) -> Self {
        let mut c = [0u64; 5];
        for i in 0..5 {
            for j in 0..5 {
                let t = fmul(self.0[i], o.0[j]);
                if i + j < 5 {
                    c[i + j] = fadd(c[i + j], t);
                } else {
                    c[i + j - 5] = fadd(c[i + j - 5], fmul(3, t));
                }
            }
        }
        Self(c)
    }
    pub fn square(self) -> Self {
        self.mul(self)
    }
    pub fn pow(self, mut e: u64) -> Self {
        let (mut r, mut b) = (Self::ONE, self);
        while e > 0 {
            if e & 1 == 1 {
                r = r.mul(b);
            }
            b = b.square();
            e >>= 1;
        }
        r
    }
    /// `self^e` for a little-endian multi-limb exponent.
    pub fn pow_big(self, e: &[u64]) -> Self {
        let mut r = Self::ONE;
        for &limb in e.iter().rev() {
            for bit in (0..64).rev() {
                r = r.square();
                if (limb >> bit) & 1 == 1 {
                    r = r.mul(self);
                }
            }
        }
        r
    }
    /// `phi^k`, table form (dregg-sig field5.rs:336): coefficient `i` scaled by `zeta5^(i k)`.
    pub fn frobenius_pow(self, k: usize) -> Self {
        let z = zeta5();
        Self(core::array::from_fn(|i| {
            fmul(self.0[i], fpow(z, ((i * (k % 5)) % 5) as u64))
        }))
    }
    /// `phi^k` computed from the definition, `x -> x^p` applied `k` times.
    pub fn frobenius_by_pow(self, k: usize) -> Self {
        (0..k).fold(self, |acc, _| acc.pow(P))
    }
    /// `N(x) = prod_k phi^k(x)`, in `F_p`.
    pub fn norm(self) -> u64 {
        let n = (0..5).fold(Self::ONE, |acc, k| acc.mul(self.frobenius_pow(k)));
        assert!(n.is_base());
        n.0[0]
    }
    /// Inverse via `x^{-1} = (phi x)(phi^2 x)(phi^3 x)(phi^4 x) / N(x)`; zero maps to zero.
    pub fn inv(self) -> Self {
        if self.is_zero() {
            return Self::ZERO;
        }
        let c = (1..5).fold(Self::ONE, |acc, k| acc.mul(self.frobenius_pow(k)));
        let n = self.mul(c);
        assert!(n.is_base());
        c.scale(finv(n.0[0]))
    }
}

/// Deterministic splitmix64 stream.
#[derive(Clone, Debug)]
pub struct SplitMix(pub u64);

impl SplitMix {
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    pub fn fp(&mut self) -> u64 {
        loop {
            let x = self.next_u64();
            if x < P {
                return x;
            }
        }
    }
    pub fn fp5(&mut self) -> Fp5 {
        Fp5(core::array::from_fn(|_| self.fp()))
    }
    /// A uniform element outside `F_p`.
    pub fn fp5_nonbase(&mut self) -> Fp5 {
        loop {
            let z = self.fp5();
            if !z.is_base() {
                return z;
            }
        }
    }
}

// --- multi-limb helpers for exponents like p^5 - 1 ---

fn big_mul_small(a: &[u64], m: u64) -> Vec<u64> {
    let mut out = Vec::with_capacity(a.len() + 1);
    let mut carry = 0u128;
    for &x in a {
        let t = x as u128 * m as u128 + carry;
        out.push(t as u64);
        carry = t >> 64;
    }
    if carry > 0 {
        out.push(carry as u64);
    }
    out
}

/// `p^5 - 1` as little-endian limbs.
pub fn p5_minus_one() -> Vec<u64> {
    let mut a = vec![1u64];
    for _ in 0..5 {
        a = big_mul_small(&a, P);
    }
    // subtract one (p^5 is odd, so no borrow beyond limb 0)
    assert!(a[0] & 1 == 1);
    a[0] -= 1;
    a
}

/// `(v2(x), x >> v2(x))` for a nonzero little-endian big integer.
pub fn big_split_two_adic(a: &[u64]) -> (u32, Vec<u64>) {
    let mut v = 0u32;
    let mut x = a.to_vec();
    while x[0] & 1 == 0 {
        let mut carry = 0u64;
        for limb in x.iter_mut().rev() {
            let next = *limb & 1;
            *limb = (*limb >> 1) | (carry << 63);
            carry = next;
        }
        v += 1;
    }
    while x.len() > 1 && *x.last().unwrap() == 0 {
        x.pop();
    }
    (v, x)
}

// =====================================================================================
// F_p-rank checks for the Stage-0 mask-point blinding map
// =====================================================================================

/// Rank over `F_p` of a dense matrix (rows of `u64` in `[0, p)`), by Gaussian elimination.
pub fn rank_fp(mut m: Vec<Vec<u64>>) -> usize {
    let rows = m.len();
    if rows == 0 {
        return 0;
    }
    let cols = m[0].len();
    let mut rank = 0;
    for c in 0..cols {
        let Some(piv) = (rank..rows).find(|&r| m[r][c] != 0) else {
            continue;
        };
        m.swap(rank, piv);
        let inv = finv(m[rank][c]);
        for x in m[rank].iter_mut() {
            *x = fmul(*x, inv);
        }
        let pivot_row = m[rank].clone();
        for (r, row) in m.iter_mut().enumerate() {
            if r != rank && row[c] != 0 {
                let f = row[c];
                for (x, &pv) in row.iter_mut().zip(&pivot_row) {
                    *x = fsub(*x, fmul(f, pv));
                }
            }
        }
        rank += 1;
        if rank == rows {
            break;
        }
    }
    rank
}

/// The `F_p`-linear map `B (F_p coefficients, deg < 5 * t * 2^s) -> (B mod (x^{2^s} - z_j))_j`
/// into `(F_{p^5}^{2^s})^t = F_p^{5 t 2^s}`, as a matrix (rows = output coords, cols = coeffs).
/// For `s = 0` this is `B -> (B(z_0), .., B(z_{t-1}))`. Residue coefficient `r` of `x^i` modulo
/// `x^{2^s} - z` is `z^(i >> s)` at position `i mod 2^s`, so no `2^s`-th roots are needed.
pub fn residue_matrix(zs: &[Fp5], s: usize, ncoeffs: usize) -> Vec<Vec<u64>> {
    let w = 1usize << s;
    let nrows = 5 * zs.len() * w;
    let mut m = vec![vec![0u64; ncoeffs]; nrows];
    for (j, z) in zs.iter().enumerate() {
        let mut zp = Fp5::ONE; // z^(i >> s)
        for i in 0..ncoeffs {
            if i > 0 && i % w == 0 {
                zp = zp.mul(*z);
            }
            let pos = i % w;
            for limb in 0..5 {
                m[j * 5 * w + pos * 5 + limb][i] = zp.0[limb];
            }
        }
    }
    m
}

/// Rank of [`residue_matrix`] with the square size `ncoeffs = 5 * t * 2^s`.
pub fn residue_rank(zs: &[Fp5], s: usize) -> usize {
    rank_fp(residue_matrix(zs, s, 5 * zs.len() << s))
}

/// Rank of `k` base-field blinding coefficients mapped to one evaluation `B(z)`, `B = sum_{i<k}
/// b_i x^i`: the insufficient-blinders case (`k < 5` cannot fill `F_{p^5} = F_p^5`).
pub fn single_eval_rank(z: Fp5, k: usize) -> usize {
    rank_fp(residue_matrix(&[z], 0, k))
}

/// Replica of dregg-sig `crates/agg/src/zk_hem/v2/pcs.rs:731-738` (`mask_points_good`):
/// condition (G2), each `omega_j^(2^step_vars)` outside `F_p` and no two Frobenius conjugates.
pub fn mask_points_good(omegas: &[Fp5], step_vars: usize) -> bool {
    let z: Vec<Fp5> = omegas
        .iter()
        .map(|w| (0..step_vars).fold(*w, |acc, _| acc.square()))
        .collect();
    z.iter().all(|x| !x.is_base())
        && (0..z.len()).all(|i| (0..i).all(|j| (0..5).all(|k| z[i].frobenius_pow(k) != z[j])))
}

/// Five deterministic pseudo-random non-base points with pairwise distinct Frobenius orbits.
pub fn distinct_orbit_points(seed: u64) -> [Fp5; 5] {
    let mut rng = SplitMix(seed);
    loop {
        let zs: [Fp5; 5] = core::array::from_fn(|_| rng.fp5_nonbase());
        if mask_points_good(&zs, 0) {
            return zs;
        }
    }
}

/// The named rank experiments: `(label, s, rank, expected)`; expected values are `[DERIVED]`
/// (rank = degree of `lcm_j m_{z_j}(x^{2^s})` over `F_p`).
pub fn rank_experiments() -> Vec<(String, usize, usize, usize)> {
    let mut out = Vec::new();
    let zs = distinct_orbit_points(0x5EED_0001);
    for s in 0..=2usize {
        let w = 1usize << s;
        let tag = |name: &str| {
            if s == 0 {
                name.to_string()
            } else {
                format!("{name}_s{s}")
            }
        };
        out.push((tag("distinct"), s, residue_rank(&zs, s), 25 * w));
        for k in 1..=4usize {
            let mut c = zs;
            c[1] = zs[0].frobenius_pow(k);
            let name = if k == 1 {
                "conjugate".to_string()
            } else {
                format!("conjugate_k{k}")
            };
            out.push((tag(&name), s, residue_rank(&c, s), 20 * w));
        }
        let mut b = zs;
        b[2] = Fp5::from_base(0x1234_5678_9ABC_DEF0);
        out.push((tag("one_base"), s, residue_rank(&b, s), 21 * w));
    }
    let z = zs[0];
    for k in 1..=6usize {
        out.push((format!("insufficient_k{k}"), 0, single_eval_rank(z, k), k.min(5)));
    }
    out
}

// =====================================================================================
// Conformance JSON and blinder model table
// =====================================================================================

/// One row of the conformance table, from `report_with(Cshake, size(L, 1 << (L-1)), L, L-1, 0,
/// schedule(L))` exactly as `directed_rounding_and_summed_crossovers` (v2/bounds.rs:960-975).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConformanceRow {
    pub log_cells: usize,
    pub stage0_queries: usize,
    pub stage0_step_vars: usize,
    pub stage0_agreement: u128,
    pub rbr_bits: MilliBits,
    pub rbr_round: String,
    pub mask_m: u128,
    pub mask_bits: MilliBits,
    pub classical_work_bits: MilliBits,
    pub qrom_work_bits: MilliBits,
    pub qrom_terms: (MilliBits, MilliBits),
    pub qrom_error_bits_t64: MilliBits,
    pub rounds: usize,
    pub proof_bytes: usize,
    /// `blind_cells_for(step_vars0, q0) = (q0 + 25) << s` (the `Layout` value; the report
    /// itself is run with `blind_cells = 0` as in the dregg-sig test).
    pub blind_cells: usize,
}

pub fn conformance_row(l: usize) -> ConformanceRow {
    let s = schedule(l).unwrap();
    let r = report_with(
        Profile::CshakeJohnson400,
        size(l, 1 << (l - 1)),
        l,
        l - 1,
        0,
        &s,
    )
    .unwrap();
    let st0 = s.stages[0];
    ConformanceRow {
        log_cells: l,
        stage0_queries: st0.num_queries,
        stage0_step_vars: st0.step_vars,
        stage0_agreement: r.stages[0].agreement,
        rbr_bits: r.rbr_bits,
        rbr_round: format!("{:?}", r.rbr_round),
        mask_m: r.mask_m,
        mask_bits: r.mask_bits,
        classical_work_bits: r.classical_work_bits(),
        qrom_work_bits: r.qrom_work_bits(),
        qrom_terms: r.qrom_work_terms(),
        qrom_error_bits_t64: r.qrom_error_bits(64),
        rounds: r.rounds,
        proof_bytes: r.proof_bytes,
        blind_cells: blind_cells_for(st0.step_vars, st0.num_queries),
    }
}

/// `[MODEL]` blinder-count comparison, per `log_cells`: `(L, s, q0, v2_blind, cfw_model)` with
/// `v2_blind = (q0 + 25) << s` (V2.0, Lemma V2.2 budget) and `cfw_model = (q0 << s) + 2`
/// (a scalar model of CFW 2026/391 Lemma 3.29 and §10.1: one random coefficient per symbol plus two
/// spare coordinates). Model numbers only; not a security claim.
pub fn blinder_model_table() -> Vec<(usize, usize, usize, usize, usize)> {
    (MIN_LOG_CELLS..=MAX_LOG_CELLS)
        .map(|l| {
            let st0 = schedule(l).unwrap().stages[0];
            let (s, q0) = (st0.step_vars, st0.num_queries);
            (l, s, q0, blind_cells_for(s, q0), (q0 << s) + 2)
        })
        .collect()
}

/// The `(rows, vars)` sizes of dregg-sig `print_v2_tables` (v2/bounds.rs:1080-1089).
pub const V27_SIZES: [(usize, usize); 8] = [
    (17, 82_000),
    (17, 1 << 17),
    (20, 1 << 20),
    (21, 1_088_721),
    (22, 1 << 22),
    (23, 1 << 23),
    (25, 1 << 25),
    (27, 1 << 27),
];

/// One row of `print_v2_tables` (v2/bounds.rs:1090-1105): `report(TurboShakeJohnson400, ..)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct V27Row {
    pub rows: usize,
    pub vars: usize,
    pub log_cells: usize,
    pub queries: Vec<usize>,
    pub mask_m: u128,
    pub rbr_bits: MilliBits,
    pub rbr_round: String,
    pub classical_work_bits: MilliBits,
    pub qrom_work_bits: MilliBits,
    pub qrom_terms: (MilliBits, MilliBits),
    pub qrom_error_bits_t64: MilliBits,
    pub proof_bytes: usize,
}

pub fn v27_row(rows: usize, vars: usize) -> V27Row {
    let r = report(Profile::TurboShakeJohnson400, size(rows, vars)).unwrap();
    V27Row {
        rows,
        vars,
        log_cells: r.log_cells,
        queries: r.stages.iter().map(|s| s.queries).collect(),
        mask_m: r.mask_m,
        rbr_bits: r.rbr_bits,
        rbr_round: format!("{:?}", r.rbr_round),
        classical_work_bits: r.classical_work_bits(),
        qrom_work_bits: r.qrom_work_bits(),
        qrom_terms: r.qrom_work_terms(),
        qrom_error_bits_t64: r.qrom_error_bits(64),
        proof_bytes: r.proof_bytes,
    }
}

/// `qrom_work_bits` / `classical_work_bits` as functions of `rbr_bits` alone (both depend only
/// on `rbr_bits` and the 400-bit digest; `rounds` enters only the `< 512` assertion), using the
/// L=21 report as carrier.
pub fn work_bits_at_rbr(rbr_bits: MilliBits) -> (MilliBits, MilliBits) {
    let s = schedule(21).unwrap();
    let mut r = report_with(
        Profile::CshakeJohnson400,
        size(21, 1 << 20),
        21,
        20,
        0,
        &s,
    )
    .unwrap();
    r.rbr_bits = rbr_bits;
    (r.qrom_work_bits(), r.classical_work_bits())
}

/// Extra conformance data beyond the per-size rows.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Extras {
    pub v27: Vec<V27Row>,
    /// `min_stage0_queries(L, 128_000)` for `L = 16..=28`.
    pub min_stage0: Vec<Option<usize>>,
}

fn fmt_opt(x: Option<usize>) -> String {
    x.map_or("null".to_string(), |v| v.to_string())
}

/// Deterministic conformance JSON.
pub fn conformance_json(rows: &[ConformanceRow], extras: &Extras) -> String {
    let (a21, b_cf21) = mask_line_bad_challenges(4, 15, 256);
    let (a28, b_cf28) = mask_line_bad_challenges(4, 22, 128);
    let (_, bits21) = mask_line(4, 15, 256);
    let (_, bits28) = mask_line(4, 22, 128);
    let (q264827, c264827) = work_bits_at_rbr(264_827);
    let mut j = String::new();
    j.push_str("{\n");
    j.push_str("  \"source\": \"dregg-sig working tree 2026-11-22, crates/agg/src/zk_hem/v2/bounds.rs report_with(CshakeJohnson400, size(L, 1<<(L-1)), L, L-1, 0, schedule(L)); [EXECUTED] by zkhem_v2_closure tests\",\n");
    j.push_str(&format!("  \"field_millibits\": {FIELD_MILLIBITS},\n"));
    j.push_str(&format!("  \"target\": {TARGET_LEVEL_MILLIBITS},\n"));
    j.push_str("  \"sizes\": [\n");
    for (i, r) in rows.iter().enumerate() {
        j.push_str(&format!(
            "    {{\"log_cells\": {}, \"stage0_queries\": {}, \"stage0_step_vars\": {}, \"stage0_agreement\": {}, \"rbr_bits\": {}, \"rbr_round\": \"{}\", \"mask_m\": {}, \"mask_bits\": {}, \"classical_work_bits\": {}, \"qrom_work_bits\": {}, \"qrom_terms\": [{}, {}], \"qrom_error_bits_t64\": {}, \"rounds\": {}, \"proof_bytes\": {}, \"blind_cells\": {}}}{}\n",
            r.log_cells,
            r.stage0_queries,
            r.stage0_step_vars,
            r.stage0_agreement,
            r.rbr_bits,
            r.rbr_round,
            r.mask_m,
            r.mask_bits,
            r.classical_work_bits,
            r.qrom_work_bits,
            r.qrom_terms.0,
            r.qrom_terms.1,
            r.qrom_error_bits_t64,
            r.rounds,
            r.proof_bytes,
            r.blind_cells,
            if i + 1 == rows.len() { "" } else { "," }
        ));
    }
    j.push_str("  ],\n");
    j.push_str(&format!("  \"mask_line_21\": {bits21},\n"));
    j.push_str(&format!("  \"mask_line_28\": {bits28},\n"));
    j.push_str(&format!(
        "  \"mask_line_detail\": {{\"21\": {{\"blowup\": 4, \"rem\": 15, \"m\": 256, \"threshold\": {a21}, \"b_cf\": {b_cf21}, \"bits\": {bits21}}}, \"28\": {{\"blowup\": 4, \"rem\": 22, \"m\": 128, \"threshold\": {a28}, \"b_cf\": {b_cf28}, \"bits\": {bits28}}}}},\n"
    ));
    j.push_str(&format!(
        "  \"work_bits_at_rbr_264827\": {{\"qrom\": {q264827}, \"classical\": {c264827}}},\n"
    ));
    j.push_str(&format!(
        "  \"min_stage0_queries\": [{}],\n",
        extras
            .min_stage0
            .iter()
            .map(|&x| fmt_opt(x))
            .collect::<Vec<_>>()
            .join(", ")
    ));
    j.push_str("  \"v27_rows\": [\n");
    for (i, r) in extras.v27.iter().enumerate() {
        j.push_str(&format!(
            "    {{\"rows\": {}, \"vars\": {}, \"log_cells\": {}, \"queries\": [{}], \"mask_m\": {}, \"rbr_bits\": {}, \"rbr_round\": \"{}\", \"classical_work_bits\": {}, \"qrom_work_bits\": {}, \"qrom_terms\": [{}, {}], \"qrom_error_bits_t64\": {}, \"proof_bytes\": {}}}{}\n",
            r.rows,
            r.vars,
            r.log_cells,
            r.queries
                .iter()
                .map(|q| q.to_string())
                .collect::<Vec<_>>()
                .join(", "),
            r.mask_m,
            r.rbr_bits,
            r.rbr_round,
            r.classical_work_bits,
            r.qrom_work_bits,
            r.qrom_terms.0,
            r.qrom_terms.1,
            r.qrom_error_bits_t64,
            r.proof_bytes,
            if i + 1 == extras.v27.len() { "" } else { "," }
        ));
    }
    j.push_str("  ],\n");
    j.push_str("  \"ranks\": {");
    let ranks = rank_experiments();
    for (i, (label, _, rank, _)) in ranks.iter().enumerate() {
        j.push_str(&format!(
            "\"{label}\": {rank}{}",
            if i + 1 == ranks.len() { "" } else { ", " }
        ));
    }
    j.push_str("},\n");
    j.push_str("  \"blinder_model\": {\"label\": \"MODEL: v2 = (q0+25)<<s (Lemma V2.2 budget); cfw = (q0<<s)+2 (CFW 2026/391 Lemma 3.29 and section 10.1 scalar model); not a security claim\", \"rows\": [");
    let table = blinder_model_table();
    for (i, (l, s, q0, v2, cfw)) in table.iter().enumerate() {
        j.push_str(&format!(
            "{{\"log_cells\": {l}, \"s\": {s}, \"q0\": {q0}, \"v2\": {v2}, \"cfw\": {cfw}}}{}",
            if i + 1 == table.len() { "" } else { ", " }
        ));
    }
    j.push_str("]}\n");
    j.push_str("}\n");
    j
}
