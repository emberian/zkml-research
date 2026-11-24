//! Real `--release` multithreaded (`rayon`) benchmark suite for `darkvfhe` (`N = 8192`):
//! Measures wall-clock latency (`ms`), prover/verifier throughput, memory (`MiB`), and committed
//! proof sizes across `d in {64, 256, 1024, 4096}` (`Eager` vs `HoistedB61` `Direct-20` &
//! `Exact-Garner-15` vs `Hoist(b, tau=64)` vs `vFHEML` Inference vs `Dark-vPIR V = 151,936`).

use darkstep::bfv::{Ct, OwnKey};
use darkvfhe::cert::{
    compute_statement_digest, ct2_handle, ct3_handle, evaluate_shared_a_at_fs,
    precompute_shared_grid, prove_hoisted_matvec, verify_hoisted_matvec,
    verify_hoisted_matvec_succinct_with_a_evals, ProveOptions, SuccinctAEvalsQuery, VerifyOptions,
};
use darkvfhe::digits::LiftMode;
use darkvfhe::logup_gkr::LogUpConfig;
use darkvfhe::rns_hoist::{HoistedEngine, RelinearizationKey, TemporalOuterAccumulator};
use darkvfhe::{process_memory_mib, HoistedParams};
use rayon::prelude::*;
use std::sync::Arc;
use std::time::Instant;

fn fhe_layout(d: usize, n: usize) -> (usize, usize, usize, usize) {
    let dc = d.min(64);
    let dr = d.min(n / 64);
    assert_eq!(d % dc, 0);
    assert_eq!(d % dr, 0);
    let r_blk = d / dr;
    let k_blk = d / dc;
    (dc, dr, r_blk, k_blk)
}

fn gen_cts_parallel(
    params: &HoistedParams,
    engine: &HoistedEngine,
    count: usize,
    seed_base: u64,
) -> Vec<Ct> {
    (0..count)
        .into_par_iter()
        .map(|idx| {
            let mut key = OwnKey::new(engine.rns_q.clone(), seed_base + idx as u64);
            let mut m = vec![0u64; params.n];
            for (j, slot) in m.iter_mut().take(64).enumerate() {
                *slot = ((idx * 7 + j * 3 + 1) as u64) % 13;
            }
            key.encrypt_exact(&m)
        })
        .collect()
}

fn main() {
    let t_total = Instant::now();
    let threads = rayon::current_num_threads();
    let params = Arc::new(HoistedParams::n8192());
    let engine = HoistedEngine::new(params.clone());

    println!("==========================================================================================================");
    println!("darkvfhe Native Multithreaded (`rayon`) HoistedB61 Benchmark Suite — N = 8192 (L=3 Qp + k=5 Bp = 8x61b)");
    println!(
        "Threads: {} | log2(Q) = {} bits | log2(Q*B) = {} bits | t = {}",
        threads,
        params.q_big.bits(),
        params.mqb_big.bits(),
        params.t
    );
    println!("==========================================================================================================\n");

    // --------------------------------------------------------------------------------------------------
    // SECTION 1: Forward Matvec (`R_blk x K_blk`) at N = 8192 across d in {64, 256, 1024, 4096}
    // Comparing: Eager FHE vs Hoisted FHE (cold & warm NTT) + Full HoistedB61 Prover & Verifier
    // --------------------------------------------------------------------------------------------------
    println!("### 1. Forward Block Matvec (`N = 8192`) — `Eager` vs `HoistedB61` (`Direct-20` & `Exact-Garner-15`)");
    println!(
        "{:>5} | {:>9} | {:>10} | {:>10} | {:>9} | {:>11} | {:>11} | {:>10} | {:>10} | {:>9}",
        "d",
        "Blocks",
        "Eager(ms)",
        "Hoist(ms)",
        "Warm(ms)",
        "Prv-D20(ms)",
        "Prv-EG15(ms)",
        "Vfy-Full",
        "Vfy-Succ",
        "RSS(MiB)"
    );
    println!("{}", "-".repeat(118));

    for &d in &[64usize, 256, 1024, 4096] {
        let (_, _, r_blk, k_blk) = fhe_layout(d, 8192);
        let num_blocks = r_blk * k_blk;

        let flat_a = gen_cts_parallel(&params, &engine, num_blocks, 10_000 + d as u64 * 10);
        let a_grid: Vec<Vec<Ct>> = (0..r_blk)
            .map(|r| flat_a[r * k_blk..(r + 1) * k_blk].to_vec())
            .collect();
        drop(flat_a);
        let b_vec = gen_cts_parallel(&params, &engine, k_blk, 90_000 + d as u64);

        // 1a. Eager per-block rescale + sum (cold):
        let t0 = Instant::now();
        let _eager_out = engine.eager_matvec(&a_grid, &b_vec);
        let eager_ms = t0.elapsed().as_secs_f64() * 1e3;

        // 1b. Hoisted sum-before-rescale (cold: includes base-extension + forward NTT of A and B):
        let t1 = Instant::now();
        let _hoist_out = engine.hoisted_matvec(&a_grid, &b_vec);
        let hoist_cold_ms = t1.elapsed().as_secs_f64() * 1e3;

        // 1c. Hoisted sum-before-rescale (warm weights A, fresh vector B — `vFHEML` / `Hoist(b, tau=64)`):
        let a_pre_exec = engine.precompute_grid(&a_grid, false);
        let t2 = Instant::now();
        let b_pre_exec = engine.precompute_vec(&b_vec, false);
        let _hoist_warm = engine.hoisted_matvec_precomputed(&a_pre_exec, &b_pre_exec);
        let hoist_warm_ms = t2.elapsed().as_secs_f64() * 1e3;
        drop(a_pre_exec);
        drop(b_pre_exec);

        let ha: Vec<Vec<[u8; 32]>> = a_grid
            .par_iter()
            .map(|r| r.iter().map(ct2_handle).collect())
            .collect();
        let hb: Vec<[u8; 32]> = b_vec.par_iter().map(ct2_handle).collect();

        // 1d. Precompute persistent weight lifts + NTT (`SharedGridLifts`), then benchmark online
        //     `Direct-20` and `Exact-Garner-15` Prover + Verifier (with full D1b LogUp-GKR!):
        let (a_pre_d20, shared_d20) = precompute_shared_grid(&engine, &a_grid, LiftMode::Direct20);
        let t_pd20 = Instant::now();
        let (out_d20, wit_d20) = prove_hoisted_matvec(
            &engine,
            &a_grid,
            &b_vec,
            Some((&a_pre_d20, &shared_d20)),
            ProveOptions {
                mode: LiftMode::Direct20,
                logup: Some(LogUpConfig::BatchedC3 { chunk_log2: 18 }),
                persistent_a: true,
            },
        )
        .expect("prove Direct20");
        let prove_d20_ms = t_pd20.elapsed().as_secs_f64() * 1e3;
        drop(a_pre_d20);

        let hout_d20: Vec<[u8; 32]> = out_d20.par_iter().map(ct3_handle).collect();
        let t_vfull = Instant::now();
        verify_hoisted_matvec(
            &params,
            &ha,
            &hb,
            &hout_d20,
            &a_grid,
            &b_vec,
            &out_d20,
            &wit_d20,
            Some(&shared_d20),
            VerifyOptions::default(),
        )
        .expect("verify Direct20 full");
        let vfy_full_ms = t_vfull.elapsed().as_secs_f64() * 1e3;

        // Measure succinct PCS-oracle verifier (online B/y/s/K evals + 8-prime R_blk x K_blk scalar matvec + D1b GKR!):
        let stmt_h = compute_statement_digest(&params, &ha, &hb, &hout_d20);
        let a_evals = evaluate_shared_a_at_fs(&params, &stmt_h, &wit_d20.witness_root, &shared_d20);
        let t_vsucc = Instant::now();
        verify_hoisted_matvec_succinct_with_a_evals(
            &params,
            &SuccinctAEvalsQuery {
                r_blk,
                k_blk,
                stmt_hash: &stmt_h,
                a_evals_per_prime: &a_evals,
                opened_b: &b_vec,
                out_cts: &out_d20,
            },
            &wit_d20,
        )
        .expect("succinct HoistedB61 + D1b verify");
        let vfy_succ_ms = t_vsucc.elapsed().as_secs_f64() * 1e3;
        drop(shared_d20);
        drop(wit_d20);

        let (a_pre_eg15, shared_eg15) =
            precompute_shared_grid(&engine, &a_grid, LiftMode::ExactGarner15);
        let t_peg15 = Instant::now();
        let (out_eg15, wit_eg15) = prove_hoisted_matvec(
            &engine,
            &a_grid,
            &b_vec,
            Some((&a_pre_eg15, &shared_eg15)),
            ProveOptions {
                mode: LiftMode::ExactGarner15,
                logup: Some(LogUpConfig::BatchedC3 { chunk_log2: 18 }),
                persistent_a: true,
            },
        )
        .expect("prove ExactGarner15");
        let prove_eg15_ms = t_peg15.elapsed().as_secs_f64() * 1e3;
        let hout_eg15: Vec<[u8; 32]> = out_eg15.par_iter().map(ct3_handle).collect();
        verify_hoisted_matvec(
            &params,
            &ha,
            &hb,
            &hout_eg15,
            &a_grid,
            &b_vec,
            &out_eg15,
            &wit_eg15,
            Some(&shared_eg15),
            VerifyOptions::default(),
        )
        .expect("verify ExactGarner15");

        let (_, peak_mib) = process_memory_mib();
        println!(
            "{:>5} | {:>4}->{:<3} | {:>10.2} | {:>10.2} | {:>9.2} | {:>11.2} | {:>11.2} | {:>8.2}ms | {:>8.3}ms | {:>9.1}",
            d,
            num_blocks,
            r_blk,
            eager_ms,
            hoist_cold_ms,
            hoist_warm_ms,
            prove_d20_ms,
            prove_eg15_ms,
            vfy_full_ms,
            vfy_succ_ms,
            peak_mib
        );
    }

    // --------------------------------------------------------------------------------------------------
    // SECTION 2: 1-Block (`R=1, K=1`, `N=8192`) Direct Speedup vs Python `vfhe_hoisted_b61_and_pir.py`
    // and Cold Weight-Lift + Prover Throughput (`Direct-20` & `Exact-Garner-15` + `c=3` vs `c=4` D1b)
    // --------------------------------------------------------------------------------------------------
    println!("\n### 2. Deployed `N = 8192` 1-Block Cold Prover/Verifier (Direct Comparison vs Python M2 Max Baseline)");
    {
        let ct_a = gen_cts_parallel(&params, &engine, 1, 500_000);
        let ct_b = gen_cts_parallel(&params, &engine, 1, 500_001);
        let a1 = vec![ct_a];
        let ha = vec![vec![ct2_handle(&a1[0][0])]];
        let hb = vec![ct2_handle(&ct_b[0])];

        for (label, mode, lu_cfg) in [
            (
                "Direct-20 + D1b(c=3, 2^18)",
                LiftMode::Direct20,
                LogUpConfig::BatchedC3 { chunk_log2: 18 },
            ),
            (
                "Exact-Garner-15 + D1b(c=3, 2^18)",
                LiftMode::ExactGarner15,
                LogUpConfig::BatchedC3 { chunk_log2: 18 },
            ),
            (
                "Exact-Garner-15 + D1b(c=4, mono)",
                LiftMode::ExactGarner15,
                LogUpConfig::MonolithicC4,
            ),
        ] {
            let tp = Instant::now();
            let (out1, wit1) = prove_hoisted_matvec(
                &engine,
                &a1,
                &ct_b,
                None,
                ProveOptions {
                    mode,
                    logup: Some(lu_cfg),
                    persistent_a: false,
                },
            )
            .unwrap();
            let p_ms = tp.elapsed().as_secs_f64() * 1e3;
            let hout = vec![ct3_handle(&out1[0])];

            let tv = Instant::now();
            verify_hoisted_matvec(
                &params,
                &ha,
                &hb,
                &hout,
                &a1,
                &ct_b,
                &out1,
                &wit1,
                None,
                VerifyOptions::default(),
            )
            .unwrap();
            let v_ms = tv.elapsed().as_secs_f64() * 1e3;

            let (lu_prf, _) = wit1.logup_proof.as_ref().unwrap();
            let (b_w20, b_61) = wit1.committed_bits(8192, true);
            println!(
                "  - {:34}: prove = {:>7.2} ms | verify = {:>6.2} ms | lookups = {:>9} | GKR proof = {:>6.2} KiB | cert = {:.2} Mbit (w=20) / {:.2} Mbit (digits61)",
                label,
                p_ms,
                v_ms,
                lu_prf.total_lookups,
                lu_prf.succinct_bytes() as f64 / 1024.0,
                b_w20 as f64 / 1e6,
                b_61 as f64 / 1e6,
            );
        }

        // Measure pure BEHZ rounding noise drop at N = 8192, K = 64 on zero-error ciphertexts:
        let key_z = OwnKey::new(engine.rns_q.clone(), 4242);
        let mut s_ntt = engine.rns_q.from_signed(&key_z.s);
        engine.rns_q.fwd(&mut s_ntt);
        let mut q_limbs5 = [0u64; 5];
        for (k, x) in engine.rns_q.q_big.to_u64_digits().into_iter().enumerate() {
            q_limbs5[k] = x;
        }
        let make_zero_ct = |seed: u64| -> Ct {
            let mut rng = pycompat::PyRandom::from_u64(seed);
            let mut a = engine.rns_q.zero();
            for i in 0..8192 {
                let v = rng.randbelow_arr::<5>(&q_limbs5);
                for k in 0..3 {
                    a[k * 8192 + i] = engine.rns_q.md[k].limbs5(&v);
                }
            }
            let mut a_ntt = a.clone();
            engine.rns_q.fwd(&mut a_ntt);
            let mut as_c = engine.rns_q.mul_pw(&a_ntt, &s_ntt);
            engine.rns_q.inv(&mut as_c);
            let mut c0 = engine.rns_q.zero();
            for k in 0..3 {
                let qk = engine.rns_q.qs[k];
                for i in 0..8192 {
                    c0[k * 8192 + i] = darkstep::arith::submod(0, as_c[k * 8192 + i], qk);
                }
            }
            Ct { c0, c1: a }
        };
        let az: Vec<Ct> = (0..64)
            .into_par_iter()
            .map(|c| make_zero_ct(10_000 + c))
            .collect();
        let bz: Vec<Ct> = (0..64)
            .into_par_iter()
            .map(|c| make_zero_ct(20_000 + c))
            .collect();
        let hz_out = engine.hoisted_matvec(std::slice::from_ref(&az), &bz);
        let ez_out = engine.eager_matvec(&[az], &bz);
        let zeros = vec![0u64; 8192];
        let nh = engine.phase_noise_inf(&key_z, &hz_out[0], &zeros);
        let ne = engine.phase_noise_inf(&key_z, &ez_out[0], &zeros);
        let nh_f = nh.to_u64_digits().first().copied().unwrap_or(1) as f64;
        let ne_f = ne.to_u64_digits().first().copied().unwrap_or(1) as f64;
        println!(
            "  - Zero-Error Rounding Noise @ N=8192, K=64: Eager = {} -> Hoisted = {} ({:.2}x smaller!)",
            ne,
            nh,
            ne_f / nh_f.max(1.0)
        );
    }

    // --------------------------------------------------------------------------------------------------
    // SECTION 3: End-to-End Regime Benchmarks at `d = 4096, N = 8192`:
    //   (A) `vFHEML` 2-Layer Encrypted Inference (`2 x (32x64)` hoisted matvecs, persistent `Enc(W)`)
    //   (B) `Hoist(b, tau=64)` Exact Dense SGD (`3` hoisted matvecs + amortized `tau=64` temporal outer
    //       accumulation + single BEHZ rescale + RNS-gadget relinearization)
    //   (C) `Dark-vPIR` (`V = 151,936, d = 4096`, `75,968 -> 32` cts = `32 x 2,374` blocks!)
    // --------------------------------------------------------------------------------------------------
    println!("\n### 3. Deployed System Regimes at `d = 4096, N = 8192` (`vFHEML`, `Hoist(b, tau=64)`, `Dark-vPIR V=151,936`)");
    {
        let (_, _, r_blk, k_blk) = fhe_layout(4096, 8192); // 32 x 64 = 2,048 blocks/layer
        let flat_w = gen_cts_parallel(&params, &engine, r_blk * k_blk, 700_000);
        let w_grid: Vec<Vec<Ct>> = (0..r_blk)
            .map(|r| flat_w[r * k_blk..(r + 1) * k_blk].to_vec())
            .collect();
        drop(flat_w);
        let x_vec = gen_cts_parallel(&params, &engine, k_blk, 800_000);
        let h_vec = gen_cts_parallel(&params, &engine, k_blk, 801_000);
        let d2_vec = gen_cts_parallel(&params, &engine, r_blk, 802_000);

        let t_offline = Instant::now();
        let (w_pre, w_shared) = precompute_shared_grid(&engine, &w_grid, LiftMode::Direct20);
        let offline_lift_ms = t_offline.elapsed().as_secs_f64() * 1e3;

        // (A) `vFHEML` 2-Layer Forward Inference (`W1 x` + `W2 h`, persistent weights):
        let t_vfheml = Instant::now();
        let (z1_cts, w_z1) = prove_hoisted_matvec(
            &engine,
            &w_grid,
            &x_vec,
            Some((&w_pre, &w_shared)),
            ProveOptions {
                mode: LiftMode::Direct20,
                logup: Some(LogUpConfig::BatchedC3 { chunk_log2: 18 }),
                persistent_a: true,
            },
        )
        .unwrap();
        let (z2_cts, w_z2) = prove_hoisted_matvec(
            &engine,
            &w_grid,
            &h_vec,
            Some((&w_pre, &w_shared)),
            ProveOptions {
                mode: LiftMode::Direct20,
                logup: Some(LogUpConfig::BatchedC3 { chunk_log2: 18 }),
                persistent_a: true,
            },
        )
        .unwrap();
        let vfheml_prove_ms = t_vfheml.elapsed().as_secs_f64() * 1e3;

        let hw: Vec<Vec<[u8; 32]>> = w_grid
            .par_iter()
            .map(|r| r.iter().map(ct2_handle).collect())
            .collect();
        let hx: Vec<[u8; 32]> = x_vec.par_iter().map(ct2_handle).collect();
        let hh: Vec<[u8; 32]> = h_vec.par_iter().map(ct2_handle).collect();
        let hz1: Vec<[u8; 32]> = z1_cts.par_iter().map(ct3_handle).collect();
        let hz2: Vec<[u8; 32]> = z2_cts.par_iter().map(ct3_handle).collect();

        let t_vfheml_vfy = Instant::now();
        verify_hoisted_matvec(
            &params,
            &hw,
            &hx,
            &hz1,
            &w_grid,
            &x_vec,
            &z1_cts,
            &w_z1,
            Some(&w_shared),
            VerifyOptions::default(),
        )
        .unwrap();
        verify_hoisted_matvec(
            &params,
            &hw,
            &hh,
            &hz2,
            &w_grid,
            &h_vec,
            &z2_cts,
            &w_z2,
            Some(&w_shared),
            VerifyOptions::default(),
        )
        .unwrap();
        let vfheml_vfy_ms = t_vfheml_vfy.elapsed().as_secs_f64() * 1e3;
        let (z1_b20, z1_b61) = w_z1.committed_bits(8192, false);
        let (z2_b20, z2_b61) = w_z2.committed_bits(8192, false);
        let gkr_kib = (w_z1.logup_proof.as_ref().unwrap().0.succinct_bytes()
            + w_z2.logup_proof.as_ref().unwrap().0.succinct_bytes()) as f64
            / 1024.0;
        println!(
            "  [A] `vFHEML` 2-Layer Inference (d=4096, 4096->64 hoisted cts, persistent W offline {:.1} ms):",
            offline_lift_ms
        );
        println!(
            "      Online Prove = {:.2} ms | Full Verify = {:.2} ms | Cert = {:.3} Gbit (w=20) / {:.3} Gbit (digits61) | D1b GKR = {:.1} KiB",
            vfheml_prove_ms,
            vfheml_vfy_ms,
            (z1_b20 + z2_b20) as f64 / 1e9,
            (z1_b61 + z2_b61) as f64 / 1e9,
            gkr_kib
        );

        // (B) `Hoist(b, tau=64)` Exact Dense SGD:
        // Transpose view of W2 (`64 x 32`) reusing the exact same precomputed `w_pre` & `w_shared`!
        let w_pre_t: Vec<Vec<_>> = (0..k_blk)
            .map(|c| (0..r_blk).map(|r| w_pre[r][c].clone()).collect())
            .collect();
        let w_shared_t = darkvfhe::cert::SharedGridLifts {
            mode: LiftMode::Direct20,
            lifts: (0..k_blk)
                .map(|c| (0..r_blk).map(|r| w_shared.lifts[r][c].clone()).collect())
                .collect(),
            pair_hashes: (0..k_blk)
                .map(|c| (0..r_blk).map(|r| w_shared.pair_hashes[r][c]).collect())
                .collect(),
        };
        let t_bwd = Instant::now();
        let (b_cts, w_b) = prove_hoisted_matvec(
            &engine,
            &(0..k_blk)
                .map(|c| (0..r_blk).map(|r| w_grid[r][c].clone()).collect())
                .collect::<Vec<_>>(),
            &d2_vec,
            Some((&w_pre_t, &w_shared_t)),
            ProveOptions {
                mode: LiftMode::Direct20,
                logup: Some(LogUpConfig::BatchedC3 { chunk_log2: 18 }),
                persistent_a: true,
            },
        )
        .unwrap();
        let bwd_prove_ms = t_bwd.elapsed().as_secs_f64() * 1e3;
        let _ = (b_cts, w_b);
        drop(w_pre_t);
        drop(w_shared_t);
        drop(w_pre);
        drop(w_shared);

        // Measure `TemporalOuterAccumulator` on `32 x 64 = 2,048` blocks:
        // 1 online step NTT outer accumulation + 1 epoch-end BEHZ rescale + RNS-gadget relinearization flush!
        let key_dummy = OwnKey::new(engine.rns_q.clone(), 999_999);
        let rlk = RelinearizationKey::generate(&params, &key_dummy.s, 888_888);
        let mut temp_acc = TemporalOuterAccumulator::new(&params, r_blk, k_blk);
        let t_step_acc = Instant::now();
        temp_acc.accumulate_step(&engine, &d2_vec, &h_vec);
        let outer_step_acc_ms = t_step_acc.elapsed().as_secs_f64() * 1e3;

        let t_flush = Instant::now();
        let _updated_w2 = temp_acc.flush_and_update(&engine, &w_grid, &rlk);
        let outer_flush_1layer_ms = t_flush.elapsed().as_secs_f64() * 1e3;

        // Amortized per-step wall-clock across `tau = 64` steps (2 outer layers `W1, W2` + 2 weight re-lifts / 64):
        let amortized_step_fhe_prove_ms = vfheml_prove_ms
            + bwd_prove_ms
            + 2.0 * outer_step_acc_ms
            + (2.0 * outer_flush_1layer_ms + 2.0 * offline_lift_ms) / 64.0;
        println!(
            "  [B] `Hoist(b, tau=64)` Exact Dense SGD (d=4096, 6144->128 matvec certs + tau=64 outer flush):"
        );
        println!(
            "      3-Matvec Online Prove = {:.2} ms | 1-Step Outer NTT Acc (2x2048 blks) = {:.2} ms | Epoch Flush+Relin (2x2048 blks) = {:.2} ms ({:.2} ms/step @ tau=64)",
            vfheml_prove_ms + bwd_prove_ms,
            2.0 * outer_step_acc_ms,
            2.0 * outer_flush_1layer_ms,
            (2.0 * outer_flush_1layer_ms) / 64.0
        );
        println!(
            "      Total Amortized Per-Step Host FHE+Prove Wall-Clock (@ tau=64) = {:.2} ms",
            amortized_step_fhe_prove_ms
        );
        drop(w_grid);

        // (C) `Dark-vPIR` (`V = 151,936, d = 4096, N = 8192`):
        // `K_pir = ceil(151936 / 64) = 2,374` query ciphertexts shared across `R_pir = 32` dim-groups (`75,968` blocks!).
        // Execute real `1 x 2,374` full hoisted row-group prover & verifier AND stream all `32` row-groups (`75,968` blocks)!
        let k_pir = 2374usize;
        let r_pir = 32usize;
        assert!(params.check_crt_nowrap(k_pir, params.default_max_y_bits(k_pir)));

        let q_pir_cts = gen_cts_parallel(&params, &engine, k_pir, 1_200_000);
        let e_row0_cts = gen_cts_parallel(&params, &engine, k_pir, 1_300_000);

        let (e_row0_pre, e_row0_shared) = precompute_shared_grid(
            &engine,
            std::slice::from_ref(&e_row0_cts),
            LiftMode::Direct20,
        );

        // Measure 1) Query precompute (`2,374` cts, paid ONCE across all 32 dim-groups!), and
        //         2) All `32` row-groups (`32 x 2,374 = 75,968` 8-limb NTT tensor blocks + 32 BEHZ rescales)!
        let t_pir_q = Instant::now();
        let q_pir_pre = engine.precompute_vec(&q_pir_cts, false);
        let pir_query_ntt_ms = t_pir_q.elapsed().as_secs_f64() * 1e3;

        let t_pir_stream = Instant::now();
        let mut pir_out_cts = Vec::with_capacity(r_pir);
        for _ in 0..r_pir {
            let mut row_out = engine.hoisted_matvec_precomputed(&e_row0_pre, &q_pir_pre);
            pir_out_cts.push(row_out.pop().unwrap());
        }
        let pir_75968_exec_ms = t_pir_stream.elapsed().as_secs_f64() * 1e3;
        drop(q_pir_pre);

        // Full Prover & Verifier on `1 x 2,374` row-group (which lifts ALL `2,374` query cts + proves `1` group;
        // remaining `31` groups reuse the exact same `B_lifts` and add only `31` `(y, s, K)` group witnesses!):
        let e1_grid = vec![e_row0_cts];
        let t_pir_prv1 = Instant::now();
        let (pir_out1, pir_wit1) = prove_hoisted_matvec(
            &engine,
            &e1_grid,
            &q_pir_cts,
            Some((&e_row0_pre, &e_row0_shared)),
            ProveOptions {
                mode: LiftMode::Direct20,
                logup: Some(LogUpConfig::BatchedC3 { chunk_log2: 18 }),
                persistent_a: true,
            },
        )
        .unwrap();
        let pir_prv_row0_ms = t_pir_prv1.elapsed().as_secs_f64() * 1e3;

        let he1: Vec<Vec<[u8; 32]>> = vec![e1_grid[0].par_iter().map(ct2_handle).collect()];
        let hq_pir: Vec<[u8; 32]> = q_pir_cts.par_iter().map(ct2_handle).collect();
        let ho_pir1 = vec![ct3_handle(&pir_out1[0])];
        let t_pir_vfy1 = Instant::now();
        verify_hoisted_matvec(
            &params,
            &he1,
            &hq_pir,
            &ho_pir1,
            &e1_grid,
            &q_pir_cts,
            &pir_out1,
            &pir_wit1,
            Some(&e_row0_shared),
            VerifyOptions::default(),
        )
        .unwrap();
        let pir_vfy_row0_ms = t_pir_vfy1.elapsed().as_secs_f64() * 1e3;

        let (_, peak_mib_end) = process_memory_mib();
        println!(
            "  [C] `Dark-vPIR` (V=151,936, d=4096, 75,968 -> 32 hoisted cts, fits k=5: 2^451 < 2^488):"
        );
        println!(
            "      Query NTT (2,374 cts) = {:.2} ms | Full 75,968-Block Hoisted FHE Matvec+Rescale = {:.2} ms ({:.1} blocks/s)",
            pir_query_ntt_ms,
            pir_75968_exec_ms,
            75_968.0 / (pir_75968_exec_ms / 1e3)
        );
        println!(
            "      Online Query Lift (2,374 cts) + Row-0 HoistedB61+D1b Prove = {:.2} ms | Verify = {:.2} ms | Peak RSS = {:.1} MiB",
            pir_prv_row0_ms,
            pir_vfy_row0_ms,
            peak_mib_end
        );
    }

    println!(
        "\nBenchmark suite completed cleanly in {:.2}s.",
        t_total.elapsed().as_secs_f64()
    );
}
