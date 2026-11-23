//! Differential tests: no-lookup vectors from dregg-sig
//! `crates/agg/src/zk_hem/v2/bounds.rs` tests (:806-997) reproduced on the standalone port,
//! plus F_{p^5} field / rank / mask_points_good checks and the recorded conformance JSON.
//!
//! Run: `CARGO_TARGET_DIR=/tmp/target-w11-zkhem cargo test --release -- --nocapture`

use std::thread;
use zkhem_v2_closure::*;

fn par_sizes<T: Send>(f: impl Fn(usize) -> T + Sync) -> Vec<T> {
    thread::scope(|sc| {
        let hs: Vec<_> = (MIN_LOG_CELLS..=MAX_LOG_CELLS)
            .map(|l| {
                let f = &f;
                sc.spawn(move || f(l))
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    })
}

// ---------------------------------------------------------------- shared ledger sanity

#[test]
fn logarithms_bracket_the_true_value() {
    // dregg-sig zk_hem/bounds.rs:566-580
    for (x, milli) in [
        (1u128, 0),
        (2, 1000),
        (3, 1584),
        (10, 3321),
        (1 << 100, 100_000),
    ] {
        assert!(log2_lo(x) <= milli + 1 && log2_lo(x) >= milli - 2, "{x}");
        assert!(log2_hi(x) >= milli && log2_hi(x) <= milli + 3, "{x}");
    }
    assert_eq!(log2_lo(823_543) / 10, 1965);
    assert_eq!(log2_lo(384) / 10, 858);
    assert!(log2_lo(320) < QROM_RBR_CONST && QROM_RBR_CONST <= log2_hi(320));
    assert!(log2_lo(6380) < QROM_MERKLE_CONST && QROM_MERKLE_CONST <= log2_hi(6380));
    // FIELD_MILLIBITS = floor(1000 log2(p^5 - 1)) - 1 (v2/bounds.rs:36-38), checked in f64:
    let exact = 5000.0 * (P as f64).log2();
    assert_eq!(exact.floor() as i64 - 1, FIELD_MILLIBITS, "{exact}");
}

#[test]
fn query_error_matches_the_hypergeometric_product() {
    // dregg-sig zk_hem/bounds.rs:587-592
    let bits = query_bits(16, 6, 3).unwrap();
    assert!(bits <= log2_lo(28) && bits >= log2_lo(28) - 3, "{bits}");
    assert_eq!(query_bits(16, 2, 3), None);
    assert_eq!(query_bits(16, 16, 3), Some(0));
}

// ---------------------------------------------------------------- v2 pinned tests

#[test]
fn stage0_queries_are_minimal() {
    // v2/bounds.rs:806-840
    let results = par_sizes(|log_cells| {
        let q = STAGE0_QUERIES[log_cells - MIN_LOG_CELLS];
        let found = min_stage0_queries(log_cells, TARGET_LEVEL_MILLIBITS);
        let mut violations = Vec::new();
        for fewer in 1..q {
            let s = schedule_with_stage0(log_cells, fewer).unwrap();
            let r = report_with(
                Profile::CshakeJohnson400,
                size(log_cells, 1 << (log_cells - 1)),
                log_cells,
                log_cells - 1,
                0,
                &s,
            )
            .unwrap();
            if r.qrom_sum_bits(24_000) >= 0 {
                if r.qrom_work_bits() >= TARGET_LEVEL_MILLIBITS {
                    violations.push(fewer);
                }
            } else if r.rbr_bits >= 128_000 {
                violations.push(fewer);
            }
        }
        (log_cells, q, found, violations)
    });
    for (log_cells, q, found, violations) in results {
        eprintln!("stage0 L={log_cells}: pinned {q}, recomputed {found:?}");
        assert_eq!(found, Some(q), "log_cells = {log_cells}");
        assert!(violations.is_empty(), "L={log_cells}: earlier cert at {violations:?}");
    }
    assert_eq!(
        STAGE0_QUERIES,
        [267, 267, 267, 267, 267, 267, 267, 267, 266, 266, 266, 266, 266]
    );
    assert_eq!(
        min_stage0_queries(MAX_LOG_CELLS + 1, TARGET_LEVEL_MILLIBITS),
        None
    );
}

#[test]
fn every_accepted_size_reaches_128_bits_classical_and_qrom() {
    // v2/bounds.rs:842-870
    let out = par_sizes(|log_cells| {
        let s = schedule(log_cells).unwrap();
        let st0 = s.stages[0];
        let blind = blind_cells_for(st0.step_vars, st0.num_queries);
        let n = usize::BITS as usize - 1;
        let align = 1 << VAR_ALIGN_MIN.max(log_cells - 8);
        let num_vars = ((1 << log_cells) - blind - mask_cells(n, log_cells)) / align * align;
        let shape = ShapeSize {
            log_rows: n,
            num_vars,
            num_public: num_vars - 16,
        };
        assert_eq!(Layout::new(shape).unwrap().log_cells, log_cells);
        let mut lines = Vec::new();
        for profile in Profile::ALL {
            let mut r = report(profile, shape).unwrap();
            assert!(r.qrom_work_bits() >= 128_000, "{log_cells}");
            assert!(r.classical_work_bits() >= 128_000, "{log_cells}");
            assert!(r.view_perfectly_simulated());
            assert_eq!(r.blind_cells, r.opened_symbols + LIMBS * r.mask_values);
            assert!(r.rounds < 512);
            assert!(r.rbr_bits <= 266_500);
            assert_eq!(r.qrom_work_terms().1, 129_112);
            lines.push((
                profile,
                r.rbr_bits,
                r.rbr_round,
                r.qrom_work_bits(),
                r.classical_work_bits(),
            ));
            r.blind_cells -= 1;
            assert!(!r.view_perfectly_simulated());
        }
        (log_cells, lines)
    });
    for (l, lines) in out {
        eprintln!("accepted L={l}: {lines:?}");
    }
}

#[test]
fn dkt26_thm512_and_beyond_johnson_prop510_rational_verification() {
    // v2/bounds.rs:872-908
    let (a21, b_cf21) = mask_line_bad_challenges(4, 15, 256);
    let n21 = 4u128 << 15;
    let k21 = (1u128 << 15) + 2;
    assert!((512 * a21).pow(2) >= 513u128.pow(2) * n21 * k21);
    assert!((512 * (a21 - 1)).pow(2) < 513u128.pow(2) * n21 * k21);
    assert_eq!(b_cf21, (513u128.pow(3) * n21 * n21).div_ceil(3 * (k21 - 1)));
    let (_, bits21) = mask_line(4, 15, 256);
    assert!((275_550..=275_580).contains(&bits21), "bits21={bits21}");
    let (_, bits28) = mask_line(4, 22, 128);
    assert!((271_540..=271_570).contains(&bits28), "bits28={bits28}");
    eprintln!("mask_line: a21={a21} b_cf21={b_cf21} bits21={bits21} bits28={bits28}");
    for (rem, eta_inv) in [(12usize, 1024u128), (15, 1024), (18, 1024), (22, 64)] {
        let (agree, mca, q_udr) = dkt26_beyond_johnson_first_order(4, rem, 6, eta_inv);
        let n = 4u128 << rem;
        let k = (1u128 << rem) + 2;
        assert!(agree * agree < k * n, "rem={rem}: {agree} not below Johnson");
        assert!(3 * eta_inv * agree >= eta_inv * (n + k) + 3 * n);
        assert!(3 * eta_inv * (agree - 1) < eta_inv * (n + k) + 3 * n);
        assert!(mca >= 265_010, "rem={rem}: mca={mca}");
        assert!(q_udr <= 220, "rem={rem}: q_udr={q_udr}");
        eprintln!("dkt26 beyond-Johnson rem={rem} eta_inv={eta_inv}: agree={agree} mca={mca} q={q_udr}");
    }
}

#[test]
fn layout_puts_everything_in_one_cube() {
    // v2/bounds.rs:926-943
    let l = Layout::new(size(21, 1_088_721)).unwrap();
    assert_eq!((l.log_cells, l.var_bits), (21, 21));
    assert!(l.var_cells >= 1_088_721 && l.var_cells % (1 << l.var_align) == 0);
    let st0 = l.schedule.stages[0];
    assert_eq!(l.blind_cells, (st0.num_queries + 25) << st0.step_vars);
    assert!(l.var_cells + mask_cells(21, 21) + l.blind_cells <= 1 << 21);
    let large = Layout::new(size(25, 1 << 25)).unwrap();
    assert_eq!(large.log_cells, 26);
    assert!(Layout::new(size(28, 1 << 28)).is_none());
    assert!(Layout::new(size(29, 1 << 29)).is_none());
    assert!(Layout::new(size(5, usize::MAX)).is_none());
    assert!(Layout::new(size(4, 1000)).is_none());
    assert!(Layout::new(size(5, 15)).is_none());
}

#[test]
fn directed_rounding_and_summed_crossovers() {
    // v2/bounds.rs:946-984
    // SECURITY.md V2.7. After division by the leading term, all offset terms
    // decrease with t. Bound q_V, q_V+k, and q_Pi individually by h.
    let (t, k, h) = (1u128 << 24, 511u128, 1u128 << 15);
    let digest = 1280 * t * (2*t + 1).pow(2) + 960 * t * (t + 1 + h).pow(2)
        + 300 * t.pow(3) + 480 * h.pow(2) * (t + h + 2) + 128 * h * 28;
    assert!(1000 * digest < 1001 * 6380 * t.pow(3));
    // For these rows eps = 2^(-rbr/1000) >= 2^-267. Charge the 2^-319
    // restoration remainder against the quadratic round term at this smaller eps.
    let field_ratio = 1u128 << (319 - 267);
    let round = 320 * (t + k + 1) * (t + k) * field_ratio + 4 * (t + k + 1) * k;
    assert!(1000 * round < 1001 * 320 * t.pow(2) * field_ratio);
    assert_eq!(QROM_ROUND_SLACK, 23);
    for e in 1..=127 {
        for x in [(1u128 << e) - 1, 1u128 << e, (1u128 << e) + 1] {
            let exact = 1000.0 * (x as f64).log2();
            assert!(log2_lo(x) as f64 <= exact + 1e-8, "lo({x})");
            assert!(log2_hi(x) as f64 + 1e-8 >= exact, "hi({x})");
        }
    }
    for d in 0..=80_000 {
        let exact = 1000.0 * (2.0f64.powf(-(d as f64) / 1000.0)).ln_1p() / core::f64::consts::LN_2;
        assert!(log2_one_plus(d) as f64 + 1e-9 >= exact, "d={d}");
        assert!(log2_one_plus(d) <= 1000);
    }
    let rows = par_sizes(|l| {
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
        let q = r.qrom_work_bits();
        let c = r.classical_work_bits();
        assert!(r.qrom_sum_bits(q) >= 0 && r.qrom_sum_bits(q + 1) < 0);
        assert!(r.classical_sum_bits(c) >= 0 && r.classical_sum_bits(c + 1) < 0);
        assert_eq!(c, 198_999, "l={l}");
        let x = q as f64 / 1000.0;
        let exact = 320.0
            * (2.0f64.powf(x) + r.rounds as f64 + 1.0)
            * (2.0f64.powf(x) + r.rounds as f64)
            * 2.0f64.powf(-(r.rbr_bits as f64) / 1000.0)
            + 6380.0 * 2.0f64.powf(3.0 * x - 400.0);
        assert!(exact <= 1.0, "l={l}: {exact}");
        (l, r.rbr_bits, r.rbr_round, q, c)
    });
    for row in rows {
        eprintln!("directed {row:?}");
    }
}

// Increasing-order oracle, independent of the work search and its single-term ceiling.
fn pass_intervals(f: impl Fn(MilliBits) -> MilliBits) -> Vec<(MilliBits, MilliBits)> {
    let mut runs = Vec::new();
    let mut start = None;
    for w in 0..=512_000 {
        if f(w) >= 0 {
            start.get_or_insert(w);
        } else if let Some(lo) = start.take() {
            runs.push((lo, w - 1));
        }
    }
    if let Some(lo) = start {
        runs.push((lo, 512_000));
    }
    runs
}

#[test]
fn exhaustive_work_search_with_rounding_reentries() {
    for l in MIN_LOG_CELLS..=MAX_LOG_CELLS {
        let r = report_with(Profile::CshakeJohnson400, size(l, 1 << (l - 1)), l, l - 1,
                            0, &schedule(l).unwrap()).unwrap();
        assert_eq!(pass_intervals(|w| r.qrom_sum_bits(w)), [(0, r.qrom_work_bits())]);
        assert_eq!(pass_intervals(|w| r.classical_sum_bits(w)), [(0, r.classical_work_bits())]);
    }
    let mut r = report(Profile::CshakeJohnson400, size(17, 82_000)).unwrap();
    r.rbr_bits = 267_508;
    assert_eq!(pass_intervals(|w| r.qrom_sum_bits(w)), [(0, 128_779), (128_799, 128_799)]);
    assert_eq!(r.qrom_work_bits(), 128_799);
    r.rbr_bits = 200_094;
    assert_eq!(pass_intervals(|w| r.classical_sum_bits(w)), [(0, 198_500), (198_531, 198_531)]);
    assert_eq!(r.classical_work_bits(), 198_531);
}

#[test]
fn tree_nonce_eliminates_fiber_count_birthday_loss_in_multiproof_hiding() {
    // v2/bounds.rs:986-997
    let r17 = report(Profile::CshakeJohnson400, size(17, 82_000)).unwrap();
    let r26 = report(Profile::CshakeJohnson400, size(25, 1 << 25)).unwrap();
    assert_eq!(r17.stages[0].fibers, 1 << 14);
    assert_eq!(r26.stages[0].fibers, 1 << 22);
    assert_eq!(r17.classical_hiding_bits(64, 0), 192_000);
    assert_eq!(r17.classical_hiding_bits(0, 64), 128_999);
    assert_eq!(r26.classical_hiding_bits(0, 64), 128_999);
}

// ---------------------------------------------------------------- field F_{p^5}

#[test]
fn quintic_field_is_well_formed() {
    // (a) 5 | p - 1, zeta5 = 3^((p-1)/5) != 1, pinned value (field5.rs:30-32)
    assert_eq!((P - 1) % 5, 0);
    let z = zeta5();
    assert_ne!(z, 1);
    assert_eq!(z, PINNED_FROBENIUS_ZETA5);
    assert_eq!(fpow(z, 5), 1);
    // X^p = zeta5 * X
    let x = Fp5([0, 1, 0, 0, 0]);
    assert_eq!(x.pow(P), Fp5([0, z, 0, 0, 0]));
    let mut rng = SplitMix(0xF1E1_D005);
    for _ in 0..32 {
        let a = rng.fp5();
        let b = rng.fp5();
        let c = rng.fp5();
        assert_eq!(a.mul(b), b.mul(a));
        assert_eq!(a.mul(b.mul(c)), a.mul(b).mul(c));
        assert_eq!(a.mul(b.add(c)), a.mul(b).add(a.mul(c)));
        if !a.is_zero() {
            assert_eq!(a.mul(a.inv()), Fp5::ONE);
        }
        for k in 0..5 {
            assert_eq!(a.frobenius_pow(k), a.frobenius_by_pow(k), "k={k}");
        }
        assert_eq!(a.frobenius_pow(5), a);
        assert_eq!(a.frobenius_pow(usize::MAX), a.frobenius_by_pow(usize::MAX % 5));
        assert_eq!(a.frobenius_pow(1).mul(b.frobenius_pow(1)), a.mul(b).frobenius_pow(1));
        // is_base iff fixed by Frobenius
        assert_eq!(a.is_base(), a.frobenius_pow(1) == a);
    }
    let base = Fp5::from_base(12345);
    assert!(base.is_base() && base.frobenius_by_pow(1) == base);
    // Fermat in F_{p^5}: a^(p^5 - 1) = 1
    let e = p5_minus_one();
    let a = rng.fp5_nonbase();
    assert_eq!(a.pow_big(&e), Fp5::ONE);
}

#[test]
fn two_power_structure_of_quintic_extension() {
    // (d) v2(p^5 - 1) = v2(p - 1) = 32, i.e. (p^5-1)/(p-1) is odd.
    let (v, odd) = big_split_two_adic(&p5_minus_one());
    assert_eq!(v, 32);
    assert_eq!((P - 1).trailing_zeros(), 32);
    let mut rng = SplitMix(0xD00D);
    for _ in 0..16 {
        let z = rng.fp5_nonbase();
        // z^(2^s) is never base for s = 1..=32 (squaring is a bijection on F_{p^5}^*/F_p^*).
        let mut acc = z;
        for s in 1..=32 {
            acc = acc.square();
            assert!(!acc.is_base(), "z^(2^{s}) became base");
        }
        // Projection onto the 2-Sylow subgroup lands in F_p: every 2^s-th root of unity of
        // F_{p^5} is a base-field element.
        let w = z.pow_big(&odd);
        assert!(w.is_base(), "2-Sylow component not base");
        let mut t = w;
        for _ in 0..32 {
            t = t.square();
        }
        assert_eq!(t, Fp5::ONE);
    }
}

// ---------------------------------------------------------------- ranks

#[test]
fn mask_point_rank_experiments() {
    // (b) + (c)
    for (label, s, rank, expected) in rank_experiments() {
        eprintln!("rank {label} (s={s}): {rank} expected {expected}");
        assert_eq!(rank, expected, "{label}");
    }
    let named: std::collections::BTreeMap<_, _> = rank_experiments()
        .into_iter()
        .map(|(l, _, r, _)| (l, r))
        .collect();
    assert_eq!(named["distinct"], 25);
    assert_eq!(named["conjugate"], 20);
    assert_eq!(named["conjugate_k2"], 20);
    assert_eq!(named["conjugate_k3"], 20);
    assert_eq!(named["conjugate_k4"], 20);
    assert_eq!(named["one_base"], 21);
    for k in 1..=4 {
        assert_eq!(named[&format!("insufficient_k{k}")], k);
    }
}

#[test]
fn mask_points_good_replica() {
    // (e) dregg-sig v2/pcs.rs:731-738
    let mut rng = SplitMix(0x600D);
    for s in 0..=6usize {
        for _ in 0..4 {
            let om: [Fp5; 5] = core::array::from_fn(|_| rng.fp5_nonbase());
            assert!(mask_points_good(&om, s), "random distinct orbits accepted, s={s}");
            let zs: Vec<Fp5> = om
                .iter()
                .map(|w| (0..s).fold(*w, |a, _| a.square()))
                .collect();
            if s <= 2 {
                assert_eq!(residue_rank(&zs, s), 25 << s);
            }
            // Conjugate pair rejected (Frobenius commutes with squaring).
            for k in 1..5 {
                let mut c = om;
                c[3] = om[1].frobenius_pow(k);
                assert!(!mask_points_good(&c, s), "conjugate k={k} s={s}");
                if s <= 1 && k == 1 {
                    let zc: Vec<Fp5> = c
                        .iter()
                        .map(|w| (0..s).fold(*w, |a, _| a.square()))
                        .collect();
                    assert_eq!(residue_rank(&zc, s), 20 << s);
                }
            }
            // Equal point rejected.
            let mut e = om;
            e[4] = om[0];
            assert!(!mask_points_good(&e, s));
            // Base point rejected.
            let mut b = om;
            b[2] = Fp5::from_base(7);
            assert!(!mask_points_good(&b, s));
            // A 2^s-th root of unity (base field) times omega collides after s squarings.
            if s >= 1 {
                let g = fpow(7, (P - 1) >> s); // order divides 2^s
                let mut r = om;
                r[1] = om[0].scale(g);
                assert!(!mask_points_good(&r, s), "root-of-unity twist s={s}");
            }
        }
    }
}

// ---------------------------------------------------------------- JSON + model table

#[test]
fn conformance_json_matches_recorded_vectors() {
    let rows = par_sizes(conformance_row);
    let v27: Vec<V27Row> = thread::scope(|sc| {
        let hs: Vec<_> = V27_SIZES
            .iter()
            .map(|&(r, v)| sc.spawn(move || v27_row(r, v)))
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let min_stage0 = par_sizes(|l| min_stage0_queries(l, TARGET_LEVEL_MILLIBITS));
    let extras = Extras { v27, min_stage0 };
    let a = conformance_json(&rows, &extras);
    // determinism: regenerate the per-size rows and re-render
    let b = conformance_json(&par_sizes(conformance_row), &extras);
    assert_eq!(a, b);
    assert_eq!(
        extras.min_stage0,
        STAGE0_QUERIES.iter().map(|&q| Some(q)).collect::<Vec<_>>()
    );
    // Lean-side pins (w11-zkhem-selvage #221)
    let (_, b_cf21) = mask_line_bad_challenges(4, 15, 256);
    assert_eq!(b_cf21, 23_593_235_614_501);
    assert_ne!(b_cf21, 23_595_299_139_184); // v2/bounds.rs:884 comment value
    assert_eq!(mask_line(4, 15, 256).1, 275_573);
    assert_eq!(mask_line(4, 22, 128).1, 271_565);
    assert_eq!(work_bits_at_rbr(264_827), (128_123, 198_999));
    for r in &extras.v27 {
        eprintln!("v27 {r:?}");
    }
    for r in &rows {
        assert_eq!(r.classical_work_bits, 198_999);
        assert_eq!(r.qrom_terms.1, 129_112);
        assert!(r.qrom_work_bits >= 128_000);
        assert_eq!(r.blind_cells, (r.stage0_queries + 25) << r.stage0_step_vars);
        eprintln!(
            "L={} q0={} rbr={} ({}) m={} mask={} qrom={} terms={:?} t64={} bytes={}",
            r.log_cells,
            r.stage0_queries,
            r.rbr_bits,
            r.rbr_round,
            r.mask_m,
            r.mask_bits,
            r.qrom_work_bits,
            r.qrom_terms,
            r.qrom_error_bits_t64,
            r.proof_bytes
        );
    }
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/zkhem_v2_conformance.json");
    assert_eq!(a, std::fs::read_to_string(path).unwrap());
}

#[test]
fn blinder_model_table_bench() {
    // (f) [MODEL] numbers + wall-clock of the report computation (std::time only).
    let t0 = std::time::Instant::now();
    let table = blinder_model_table();
    for (l, s, q0, v2, cfw) in &table {
        assert_eq!(*v2, (q0 + 25) << s);
        assert!(cfw < v2);
        eprintln!(
            "model L={l} s={s} q0={q0} v2_blind={v2} cfw_model={cfw} saving={} ({:.2}%)",
            v2 - cfw,
            100.0 * (v2 - cfw) as f64 / *v2 as f64
        );
    }
    let t = std::time::Instant::now();
    let _ = conformance_row(21);
    eprintln!(
        "bench: table {:?}, report_with(L=21) {:?}",
        t0.elapsed(),
        t.elapsed()
    );
}
