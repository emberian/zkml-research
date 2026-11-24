//! `--release` Benchmark CLI for Wave-6 (`darkvfhe`):
//! 1. **128-Bit Succinct Coset-NTT Matrix PCS (`HoistedSuccinctBundle`)** across `d in {64, 256, 1024, 4096}`,
//!    `N = 8192`: measures exact serialized `Vec<u8>` proof size (`KiB` / `MiB`), PCS commit time,
//!    PCS + `D1b` open time, total online prove time, and standalone zero-witness verifier time!
//! 2. **Real 3-Custodian Threshold-BFV + SPDZ Encrypted `Qwen3.8` `Gated DeltaNet` (`d_k = d_v = 128`,
//!    `N = 8192`) + `Dark-vPIR` Encrypted Embedding Resident** (`zero party holds sk`!): executes 4
//!    consecutive stateful turns, verifying bit-exact match (`max |diff| == 0`) against cleartext
//!    `Qwen3.8` `Gated DeltaNet` over `Z_t`!

use darkstep::bfv::{Ct, OwnKey};
use darkvfhe::cert::{
    commit_persistent_grid_pcs, ct2_handle, ct3_handle, prove_hoisted_succinct_bundle,
    verify_hoisted_succinct_bundle, HoistedSuccinctBundle,
};
use darkvfhe::dark_gdn::{
    cleartext_gdn_step_mod_t, DarkGdnInitSpec, DarkGdnResident, ThreeCustodianCluster,
};
use darkvfhe::digits::LiftMode;
use darkvfhe::logup_gkr::LogUpConfig;
use darkvfhe::rns_hoist::HoistedEngine;
use darkvfhe::succinct_pcs::PcsShape;
use darkvfhe::{process_memory_mib, HoistedParams};
use rayon::prelude::*;
use std::sync::Arc;
use std::time::Instant;

fn fhe_layout(d: usize, n: usize) -> (usize, usize, usize, usize) {
    let dc = d.min(64);
    let dr = d.min(n / 64);
    (dc, dr, d / dr, d / dc)
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
                *slot = ((idx * 11 + j * 5 + 3) as u64) % 17;
            }
            key.encrypt_exact(&m)
        })
        .collect()
}

fn main() {
    let t_start = Instant::now();
    let threads = rayon::current_num_threads();
    let params = Arc::new(HoistedParams::n8192());
    let engine = Arc::new(HoistedEngine::new(params.clone()));

    println!("==================================================================================================================");
    println!(
        "darkvfhe Wave-6 Benchmark: 128-Bit Succinct Coset-NTT Matrix PCS & 3-Custodian Encrypted Qwen3.8 GDN + Dark-vPIR"
    );
    println!(
        "Ring N = {} | Threads = {} | log2(Q) = {}b | log2(Q*B) = {}b | SPDZ prime t = {}",
        params.n,
        threads,
        params.q_big.bits(),
        params.mqb_big.bits(),
        params.t
    );
    println!("==================================================================================================================\n");

    // --------------------------------------------------------------------------------------------------
    // PART 1: Succinct 128-Bit Coset-NTT Matrix PCS (`HoistedSuccinctBundle`) Scaling @ N = 8192
    // --------------------------------------------------------------------------------------------------
    println!("### 1. Standalone 128-Bit Succinct PCS `HoistedSuccinctBundle` Scaling (`N = 8192`, Persistent `Enc(W)`)");
    println!(
        "{:>5} | {:>14} | {:>9} | {:>9} | {:>10} | {:>10} | {:>10} | {:>11} | {:>11} | {:>11}",
        "d",
        "Mode",
        "Blocks",
        "Shape",
        "Commit(ms)",
        "Open(ms)",
        "TotPrv(ms)",
        "Verify(ms)",
        "Proof(KiB)",
        "UD/Lig(bits)"
    );
    println!("{}", "-".repeat(126));

    for &d in &[64usize, 256, 1024, 4096] {
        let (_, _, r_blk, k_blk) = fhe_layout(d, 8192);
        let num_blocks = r_blk * k_blk;
        let flat_a = gen_cts_parallel(&params, &engine, num_blocks, 30_000 + d as u64 * 17);
        let a_grid: Vec<Vec<Ct>> = (0..r_blk)
            .map(|r| flat_a[r * k_blk..(r + 1) * k_blk].to_vec())
            .collect();
        drop(flat_a);
        let b_vec = gen_cts_parallel(&params, &engine, k_blk, 80_000 + d as u64);

        let ha: Vec<Vec<[u8; 32]>> = a_grid
            .par_iter()
            .map(|r| r.iter().map(ct2_handle).collect())
            .collect();
        let hb: Vec<[u8; 32]> = b_vec.par_iter().map(ct2_handle).collect();

        for mode in [LiftMode::Direct20, LiftMode::ExactGarner15] {
            let (a_pre, a_pcs) =
                commit_persistent_grid_pcs(&engine, &a_grid, mode).expect("commit persistent A");

            let t_prv = Instant::now();
            let (out_cts, bundle, commit_ms, open_ms) = prove_hoisted_succinct_bundle(
                &engine,
                &a_grid,
                &b_vec,
                Some((&a_pre, &a_pcs)),
                mode,
                LogUpConfig::MonolithicC4,
            )
            .expect("prove succinct bundle");
            let tot_prv_ms = t_prv.elapsed().as_secs_f64() * 1e3;

            let proof_bytes = bundle.to_bytes();
            let hout: Vec<[u8; 32]> = out_cts.par_iter().map(ct3_handle).collect();

            // Standalone verification from raw `proof_bytes: Vec<u8>` alone (`0` secret witness access!):
            let t_vfy = Instant::now();
            let decoded = HoistedSuccinctBundle::from_bytes(&proof_bytes, &params)
                .expect("deserialize succinct bundle");
            verify_hoisted_succinct_bundle(
                &params, &ha, &hb, &hout, None, &b_vec, &out_cts, &decoded,
            )
            .expect("standalone verify succinct bundle");
            let vfy_ms = t_vfy.elapsed().as_secs_f64() * 1e3;

            let sh = PcsShape::from_mr_mc(
                &params.fp[0],
                decoded.shape_mr as usize,
                decoded.shape_mc as usize,
                decoded.t_cols as usize,
                decoded.blow as usize,
            );
            let (ud_b, lig_b, _) = sh.soundness_bits();
            println!(
                "{:>5} | {:>14} | {:>4}->{:<3} | {:>3}x{:<5} | {:>10.2} | {:>10.2} | {:>10.2} | {:>9.2}ms | {:>10.2} | {:>5.1}/{:<5.1}",
                d,
                mode.as_str(),
                num_blocks,
                r_blk,
                1usize << decoded.shape_mr,
                1usize << decoded.shape_mc,
                commit_ms,
                open_ms,
                tot_prv_ms,
                vfy_ms,
                proof_bytes.len() as f64 / 1024.0,
                ud_b,
                lig_b
            );
            drop(a_pre);
            drop(a_pcs);
        }
    }

    // --------------------------------------------------------------------------------------------------
    // PART 2: Real 3-Custodian Threshold-BFV + SPDZ Encrypted `Qwen3.8` `Gated DeltaNet` + `Dark-vPIR`
    //         Stateful Multi-Turn Resident at Deployed `N = 8192`, `d_k = d_v = 128` (`Qwen3.8` Head!)
    // --------------------------------------------------------------------------------------------------
    println!("\n### 2. 3-Custodian Threshold-BFV + SPDZ Encrypted `Qwen3.8` `Gated DeltaNet` + `Dark-vPIR` Resident (`N = 8192`)");
    {
        let t_setup = Instant::now();
        let mut cluster =
            ThreeCustodianCluster::setup(params.clone(), engine.clone(), [0x5Au8; 32]);
        let setup_ms = t_setup.elapsed().as_secs_f64() * 1e3;
        println!(
            "  - 3-of-3 Threshold-BFV + SPDZ Ceremony (`0` party holds `sk`, smudge bound E = 2^{:.1}): {:.2} ms",
            (cluster.custodians[0].smudge_bound as f64).log2(),
            setup_ms
        );

        let vocab_size = 256usize; // 4 vocab-blocks of 64 tokens (`d_k = d_v = 128` real Qwen3.8 GDN head width!)
        let d_k = 128usize;
        let d_v = 128usize;
        let fp_t = &params.fp_t;
        let t_mod = params.t;

        let embed_table: Vec<Vec<u64>> = (0..vocab_size)
            .map(|tok| {
                (0..d_k)
                    .map(|i| ((tok * 13 + i * 7 + 1) as u64) % t_mod)
                    .collect()
            })
            .collect();
        let mut cleartext_state: Vec<Vec<u64>> = (0..d_k)
            .map(|i| {
                (0..d_v)
                    .map(|j| ((i * 3 + j * 5 + 2) as u64) % 19)
                    .collect()
            })
            .collect();

        let w_q: Vec<Vec<u64>> = (0..d_k)
            .map(|r| {
                (0..d_k)
                    .map(|c| {
                        if r == c {
                            2
                        } else if (r + c) % 17 == 0 {
                            1
                        } else {
                            0
                        }
                    })
                    .collect()
            })
            .collect();
        let w_k: Vec<Vec<u64>> = (0..d_k)
            .map(|r| {
                (0..d_k)
                    .map(|c| {
                        if r == c {
                            3
                        } else if (r + 2 * c) % 19 == 0 {
                            1
                        } else {
                            0
                        }
                    })
                    .collect()
            })
            .collect();
        let w_v: Vec<Vec<u64>> = (0..d_v)
            .map(|r| {
                (0..d_k)
                    .map(|c| {
                        if r == c {
                            5
                        } else if (2 * r + c) % 23 == 0 {
                            1
                        } else {
                            0
                        }
                    })
                    .collect()
            })
            .collect();

        let t_init = Instant::now();
        let mut resident = DarkGdnResident::initialize(
            &mut cluster,
            DarkGdnInitSpec {
                embed_table: &embed_table,
                state_0: &cleartext_state,
                w_q: w_q.clone(),
                w_k: w_k.clone(),
                w_v: w_v.clone(),
                mode: LiftMode::ExactGarner15,
                logup_cfg: LogUpConfig::MonolithicC4,
            },
        )
        .expect("initialize DarkGdnResident");
        println!(
            "  - Resident Genesis (`Enc_pk(E)` [{}x{}] + `Enc_pk(S_0^T)` [{}x{}] + 3-Custodian Offline PCS Range Verify): {:.2} ms",
            vocab_size,
            d_k,
            d_v,
            d_k,
            t_init.elapsed().as_secs_f64() * 1e3
        );

        let turns = [
            (17usize, 3u64, 2u64),
            (142usize, 5u64, 4u64),
            (255usize, 0u64, 7u64), // includes exact zero decay `alpha_t = 0`!
            (64usize, 9u64, 3u64),
        ];

        let matvec_mod_t = |w: &[Vec<u64>], x: &[u64]| -> Vec<u64> {
            w.iter().map(|row| fp_t.dot(row, x)).collect()
        };

        for (turn_idx, &(tok_id, alpha_t, beta_t)) in turns.iter().enumerate() {
            let (y_enc_dec, metrics) = resident
                .step_turn(&mut cluster, turn_idx, tok_id, alpha_t, beta_t)
                .expect("encrypted GDN + Dark-vPIR turn must succeed");

            // Cleartext sequential reference check over `Z_t`:
            let x_ref = &embed_table[tok_id];
            let q_ref = matvec_mod_t(&w_q, x_ref);
            let k_ref = matvec_mod_t(&w_k, x_ref);
            let v_ref = matvec_mod_t(&w_v, x_ref);
            let (y_ref, next_s) = cleartext_gdn_step_mod_t(
                fp_t,
                &cleartext_state,
                &q_ref,
                &k_ref,
                &v_ref,
                alpha_t,
                beta_t,
            );
            assert_eq!(
                y_enc_dec, y_ref,
                "Turn {turn_idx} encrypted GDN output mismatch vs cleartext!"
            );
            cleartext_state = next_s;

            println!(
                "  - Turn {} (tok={:>3}, alpha={}, beta={}): BIT-EXACT MATCH (`max|diff|=0`) | Host Prove = {:.1} ms | 3-Custodian Verify+E2S+SPDZ = {:.1} ms | State S2E+PCS = {:.1} ms | Proofs (PIR/mk/mq) = {:.1}/{:.1}/{:.1} KiB",
                turn_idx,
                tok_id,
                alpha_t,
                beta_t,
                metrics.host_prove_ms,
                metrics.custodian_verify_and_cross_ms,
                metrics.state_refresh_ms,
                metrics.pir_proof_bytes as f64 / 1024.0,
                metrics.gdn_mk_proof_bytes as f64 / 1024.0,
                metrics.gdn_mq_proof_bytes as f64 / 1024.0,
            );
        }

        let (_, peak_mib) = process_memory_mib();
        println!(
            "  - Totals across 4 turns: Beaver triples = {} | E2S crossings = {} | S2E crossings = {} | Peak RSS = {:.1} MiB",
            cluster.total_beaver_triples,
            cluster.total_e2s_crossings,
            cluster.total_s2e_crossings,
            peak_mib
        );
    }

    println!(
        "\nWave-6 benchmark completed cleanly in {:.2}s.",
        t_start.elapsed().as_secs_f64()
    );
}
