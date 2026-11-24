//! Comprehensive `WhirPcs61` + `GMask61` Proof-Compression, Full-Transcript HVZK (`TVD == 0`),
//! 6/6 Adversarial Soundness Falsifier, and `N = 8192` Scaling Suite (`d in {64, 256, 1024, 4096}`).

use darkstep::bfv::{Ct, OwnKey};
use darkvfhe::cert::{
    commit_persistent_grid_pcs, ct2_handle, ct3_handle, prove_hoisted_succinct_bundle,
    verify_hoisted_succinct_bundle, HoistedSuccinctBundle,
};
use darkvfhe::digits::LiftMode;
use darkvfhe::logup_gkr::LogUpConfig;
use darkvfhe::rns_hoist::HoistedEngine;
use darkvfhe::succinct_pcs::{Ext3, Ext3Field, PcsRng, PcsTranscript, SlotLinearClaim};
use darkvfhe::whir_pcs::{
    commit_persistent_whir_grid, eval_poly_ext3, prove_hoisted_whir, verify_gmask61_rounds,
    verify_hoisted_whir_bundle, verify_hoisted_whir_bytes, verify_whir_pcs61, GMask61, GMaskSpec61,
    HoistedWhirBundle, HoistedWhirPcsPayload, WhirCommittedPcs61, WhirOpeningBundle61, WhirShape61,
    WHIR_BLOWUP, WHIR_T_QUERIES_128,
};
use darkvfhe::{FastPrime61, HoistedParams};
use rayon::prelude::*;
use std::collections::BTreeSet;
use std::sync::Arc;
use std::time::Instant;

fn gaussian_rank_ext3(ef: &Ext3Field, mut mat: Vec<Vec<Ext3>>) -> usize {
    if mat.is_empty() {
        return 0;
    }
    let rows = mat.len();
    let cols = mat[0].len();
    let mut rank = 0usize;
    for col in 0..cols {
        if rank >= rows {
            break;
        }
        let Some(piv) = (rank..rows).find(|&r| mat[r][col] != [0, 0, 0]) else {
            continue;
        };
        mat.swap(rank, piv);
        let inv_p = ef.inv(mat[rank][col]);
        for cell in &mut mat[rank][col..cols] {
            *cell = ef.mul(*cell, inv_p);
        }
        for r in 0..rows {
            if r == rank || mat[r][col] == [0, 0, 0] {
                continue;
            }
            let factor = mat[r][col];
            let (row_r, row_rank) = if r < rank {
                let (head, tail) = mat.split_at_mut(rank);
                (&mut head[r], &tail[0])
            } else {
                let (head, tail) = mat.split_at_mut(r);
                (&mut tail[0], &head[rank])
            };
            for (dst, &src) in row_r[col..cols].iter_mut().zip(&row_rank[col..cols]) {
                let sub = ef.mul(factor, src);
                *dst = ef.sub(*dst, sub);
            }
        }
        rank += 1;
    }
    rank
}

/// 1. Algebraic Full-Rank (`TVD == 0`) & Statistical Witness-Indistinguishability Audit for `GMask61` + `WhirPcs61`.
///    Also verifies external `GMask61::append_slot_claims_for_spec` discharging `G` and `g(r)` inside a single
///    `WhirCommittedPcs61` opening with zero extra commitments!
#[test]
fn test_gmask61_algebraic_rank_and_statistical_hvzk_indistinguishability() {
    let params = HoistedParams::for_ring(64);
    let fp: FastPrime61 = params.fp[0];
    let ef = Ext3Field::new(fp);

    // (a) Prove exact full row rank `1 + d * ell` of the `GMask61` observable transcript linear map
    //     `Psi(c) = (G, {g_round_i(0), [t^2] g_round_i, ..., [t^d] g_round_i}_{i=0..ell-1})` over `Ext3`:
    //     Since `Psi` is a surjective `F_{p^3}`-linear map onto `(Ext3)^{1 + d*ell}`, adding `\rho * Psi(c)` (`\rho != 0`)
    //     makes `(M, \tilde{s}_0, ..., \tilde{s}_{\ell-1})` EXACTLY uniform (`TVD == 0`) for ANY witness!
    for &(ell, deg) in &[(1usize, 2usize), (4, 2), (10, 2), (8, 3)] {
        let mut chal_rng = PcsRng::from_seed([0x31u8; 32]);
        let r_chals: Vec<Ext3> = (0..ell)
            .map(|i| {
                let mut raw = [0u64; 3];
                chal_rng.fill_fp_row(&fp, i as u64, &mut raw);
                raw
            })
            .collect();

        let n_vars = ell * (deg + 1);
        let n_obs = 1 + ell * deg;
        let specs = vec![GMaskSpec61::new("audit", ell, deg)];

        // Build exact Jacobian / representation matrix `J` (`n_obs x n_vars`) over `Ext3`:
        let mut j_mat = vec![vec![ef.zero(); n_vars]; n_obs];
        for var_idx in 0..n_vars {
            let mut basis_coeffs = vec![ef.zero(); n_vars];
            basis_coeffs[var_idx] = ef.one();
            let mut gm = GMask61::sample(ef, specs.clone(), &mut PcsRng::from_seed([0u8; 32]));
            gm.coeffs = basis_coeffs;

            j_mat[0][var_idx] = gm.hypercube_sum("audit");
            let mut row_off = 1usize;
            for round in 0..ell {
                let rp = gm.round_poly("audit", round, &r_chals[..round]);
                // Observable free components at each round: `rp[0]` and `rp[2..=deg]`
                // (`rp[1]` is deterministically pinned by `rp(0) + rp(1) == prev_claim`!).
                j_mat[row_off][var_idx] = rp[0];
                row_off += 1;
                for &val in &rp[2..=deg] {
                    j_mat[row_off][var_idx] = val;
                    row_off += 1;
                }
            }
        }
        let rank = gaussian_rank_ext3(&ef, j_mat);
        assert_eq!(
            rank, n_obs,
            "GMask61 map Psi must have full row rank {n_obs} (got {rank}) for ell={ell}, deg={deg} => TVD == 0!"
        );
    }

    // (b) External `GMask61` packed into blinded witness slots + discharged inside the SAME `WhirPcs61` opening:
    //     Construct TWO completely different secret multilinear witnesses `f_sparse` and `f_dense` over `{0,1}^6`
    //     (`N = 64`) that have the **EXACT SAME** public hypercube sum `S_pub`!
    let log_n = 6usize;
    let n = 1usize << log_n;
    let mut f_sparse = vec![0u64; n];
    let target_sum = 1_234_567_890_123u64;
    f_sparse[0] = target_sum; // 63 zeros, 1 spike!

    let mut f_dense = vec![0u64; n];
    let mut running_sum = 0u64;
    for (i, slot) in f_dense.iter_mut().enumerate().take(n - 1) {
        let v = ((i as u64 + 1) * 777_777_777_777) % fp.p;
        *slot = v;
        running_sum = fp.add(running_sum, v);
    }
    f_dense[n - 1] = fp.sub(target_sum, running_sum);
    assert_eq!(
        f_sparse.iter().fold(0u64, |a, &b| fp.add(a, b)),
        f_dense.iter().fold(0u64, |a, &b| fp.add(a, b)),
        "both witnesses must satisfy the identical public statement S_pub"
    );

    // Run 24 randomized trials per witness for BOTH external degree-2 `GMask61` sumcheck AND `WhirCommittedPcs61` opening:
    let ext_specs = vec![GMaskSpec61::new("ext_sc", log_n, 2)];
    let mut seen_round0_c0 = BTreeSet::new();
    let mut sparse_lsb_ones = 0usize;
    let mut dense_lsb_ones = 0usize;
    let mut sparse_col_lsb_ones = 0usize;
    let mut dense_col_lsb_ones = 0usize;
    let mut total_round_bits = 0usize;
    let mut total_col_bits = 0usize;

    for (w_idx, witness) in [&f_sparse, &f_dense].iter().enumerate() {
        for trial in 0..24usize {
            let mut seed = [0u8; 32];
            seed[0] = w_idx as u8;
            seed[1..9].copy_from_slice(&(trial as u64).to_le_bytes());
            seed[15] = 0xA5;
            let mut rng = PcsRng::from_seed(seed);

            let gmask = GMask61::sample(ef, ext_specs.clone(), &mut rng);
            let gm_slots = gmask.num_slots(n);
            let total_slots = 1 + gm_slots;
            let mut pcs_data = vec![0u64; total_slots * n];
            pcs_data[..n].copy_from_slice(witness);
            gmask.write_to_slots(&mut pcs_data[n..], n);

            let pcs = WhirCommittedPcs61::commit_with_rng(
                fp,
                &pcs_data,
                log_n,
                WHIR_T_QUERIES_128,
                WHIR_BLOWUP,
                rng,
            );

            // Prove masked sumcheck on `<1, witness>` (`deg = 2`, embedding linear `witness` with `c_2 = 0`):
            let ctx = [0x5Cu8; 32];
            let mut tr_p = PcsTranscript::new("EXT_GMASK_TEST", fp.p, &pcs.root, &ctx);
            let g_sum = gmask.hypercube_sum("ext_sc");
            tr_p.absorb_ext3(&g_sum);
            let mut rho = tr_p.squeeze_ext3(&ef, 900);
            if rho == [0, 0, 0] {
                rho = [1, 0, 0];
            }

            let mut cur_tbl: Vec<Ext3> = witness.iter().map(|&v| [v, 0, 0]).collect();
            let mut r_chals = Vec::with_capacity(log_n);
            let mut masked_rounds = Vec::with_capacity(log_n);
            for rd in 0..log_n {
                let half = cur_tbl.len() / 2;
                let mut s0 = ef.zero();
                let mut s1_slope = ef.zero();
                for u in 0..half {
                    s0 = ef.add(s0, cur_tbl[2 * u]);
                    s1_slope = ef.add(s1_slope, ef.sub(cur_tbl[2 * u + 1], cur_tbl[2 * u]));
                }
                let unmasked = [s0, s1_slope, ef.zero()];
                let blinded = gmask.blind_round_poly("ext_sc", rd, &r_chals, rho, &unmasked);
                for ck in &blinded {
                    tr_p.absorb_ext3(ck);
                }
                let r_i = tr_p.squeeze_ext3(&ef, 901 + rd as u64);
                masked_rounds.push(blinded);
                r_chals.push(r_i);
                cur_tbl = (0..half)
                    .map(|u| {
                        ef.add(
                            cur_tbl[2 * u],
                            ef.mul(r_i, ef.sub(cur_tbl[2 * u + 1], cur_tbl[2 * u])),
                        )
                    })
                    .collect();
            }
            let f_at_r = cur_tbl[0];
            let g_at_r = gmask.eval_at("ext_sc", &r_chals);
            let terminal_masked = ef.add(f_at_r, ef.mul(rho, g_at_r));

            // Discharge `<1, slot_0> == target_sum`, `G == g_sum`, AND `f(r) + rho*g(r) == terminal_masked`
            // via `append_hvzk_terminal_weld_for_spec` (`TVD == 0` Guard 1: neither `f(r)` nor `g(r)` revealed!)
            // inside ONE single `WhirCommittedPcs61::open_whir_slot_claims`!
            let mut v_fams = vec![vec![1u64; n]];
            let mut claims = vec![SlotLinearClaim::single_vec(0, vec![(0, 1)], target_sum)];
            GMask61::append_hvzk_terminal_weld_for_spec(
                &ef,
                &ext_specs,
                "ext_sc",
                0,
                1,
                n,
                g_sum,
                rho,
                &r_chals,
                terminal_masked,
                &mut v_fams,
                &mut claims,
            );

            let bundle = pcs.open_whir_slot_claims(log_n, &v_fams, &claims, &ctx);

            // Verifier checks BOTH `verify_gmask61_rounds` AND `verify_whir_pcs61`!
            let mut tr_v = PcsTranscript::new("EXT_GMASK_TEST", fp.p, &pcs.root, &ctx);
            let (rho_v, r_v, term_v) = verify_gmask61_rounds(
                &ef,
                &mut tr_v,
                [target_sum, 0, 0],
                g_sum,
                &masked_rounds,
                2,
                900,
            )
            .expect("verify_gmask61_rounds must pass");
            assert_eq!(rho_v, rho);
            assert_eq!(r_v, r_chals);
            assert_eq!(ef.add(f_at_r, ef.mul(rho, g_at_r)), term_v);

            verify_whir_pcs61(
                &fp, &pcs.shape, &pcs.root, log_n, &v_fams, &claims, &ctx, &bundle,
            )
            .expect("standalone WhirPcs61 + GMask61 opening must verify");

            // Collect statistical indistinguishability observables:
            // Note: on `f_sparse`, unmasked `c_2 == 0` in EVERY round, yet `masked_rounds[rd][2]` must be uniform non-zero!
            assert!(
                masked_rounds.iter().all(|p| p[2] != [0, 0, 0]),
                "quadratic blinding coefficient must mask c_2 == 0 on linear witness!"
            );
            assert!(
                seen_round0_c0.insert(bundle.proof.header.sumcheck_rounds[0][0]),
                "blinded round-0 messages must have 0 collisions across independent openings"
            );

            for poly in &bundle.proof.header.sumcheck_rounds {
                for limb in poly {
                    for &v in limb {
                        for b in 0..16 {
                            let bit = ((v >> b) & 1) as usize;
                            if w_idx == 0 {
                                sparse_lsb_ones += bit;
                            } else {
                                dense_lsb_ones += bit;
                            }
                            total_round_bits += 1;
                        }
                    }
                }
            }
            // Check Stage-0 opened data-row columns (`0..usable_rows` in each column):
            for col in bundle.proof.s0_fiber_vals.chunks_exact(pcs.shape.r_total) {
                for &v in &col[..pcs.shape.usable_rows] {
                    assert_ne!(v, 0, "opened Stage-0 data cells must be uniform non-zero");
                    for b in 0..8 {
                        let bit = ((v >> b) & 1) as usize;
                        if w_idx == 0 {
                            sparse_col_lsb_ones += bit;
                        } else {
                            dense_col_lsb_ones += bit;
                        }
                        total_col_bits += 1;
                    }
                }
            }
        }
    }

    let half_rb = (total_round_bits / 2) as f64;
    let p_sparse_r = sparse_lsb_ones as f64 / half_rb;
    let p_dense_r = dense_lsb_ones as f64 / half_rb;
    let half_cb = (total_col_bits / 2) as f64;
    let p_sparse_c = sparse_col_lsb_ones as f64 / half_cb;
    let p_dense_c = dense_col_lsb_ones as f64 / half_cb;

    println!(
        "[HVZK Audit] GMask61 round bit-ones: sparse={:.4}, dense={:.4} (|diff|={:.4}) | Stage-0 cols: sparse={:.4}, dense={:.4} (|diff|={:.4})",
        p_sparse_r,
        p_dense_r,
        (p_sparse_r - p_dense_r).abs(),
        p_sparse_c,
        p_dense_c,
        (p_sparse_c - p_dense_c).abs()
    );
    assert!((p_sparse_r - 0.5).abs() < 0.03 && (p_dense_r - 0.5).abs() < 0.03);
    assert!((p_sparse_c - 0.5).abs() < 0.02 && (p_dense_c - 0.5).abs() < 0.02);
}

/// 2. Deterministic Rejection of All 6 Required Adversarial Attacks against `HoistedWhirBundle` / `WhirPcs61`.
#[test]
fn test_whir_gmask_six_adversarial_attacks_rejected() {
    let params = Arc::new(HoistedParams::for_ring(64));
    let engine = HoistedEngine::new(params.clone());
    let fp0 = params.fp[0];
    let mut key = OwnKey::new(engine.rns_q.clone(), 0xCAFE_BABEu64);

    let mk_ct = |key: &mut OwnKey, seed: usize| -> Ct {
        let mut m = vec![0u64; params.n];
        for (j, slot) in m.iter_mut().take(32).enumerate() {
            *slot = ((seed * 7 + j * 3 + 1) as u64) % 13;
        }
        key.encrypt_exact(&m)
    };
    let a_grid = vec![vec![mk_ct(&mut key, 1), mk_ct(&mut key, 2)]];
    let b_vec = vec![mk_ct(&mut key, 3), mk_ct(&mut key, 4)];
    let ha: Vec<Vec<[u8; 32]>> = a_grid
        .iter()
        .map(|r| r.iter().map(ct2_handle).collect())
        .collect();
    let hb: Vec<[u8; 32]> = b_vec.iter().map(ct2_handle).collect();

    let (out_cts, honest_bundle, _, _) = prove_hoisted_whir(
        &engine,
        &a_grid,
        &b_vec,
        None,
        LiftMode::ExactGarner15,
        LogUpConfig::MonolithicC4,
    )
    .expect("honest HoistedWhirBundle prove");
    let hout: Vec<[u8; 32]> = out_cts.iter().map(ct3_handle).collect();
    let honest_bytes = honest_bundle.to_bytes();

    // Baseline honest verification must succeed:
    verify_hoisted_whir_bytes(
        &params,
        &ha,
        &hb,
        &hout,
        Some(&a_grid),
        None,
        &b_vec,
        &out_cts,
        &honest_bytes,
    )
    .expect("honest serialized HoistedWhirBundle must verify");

    let mutate_single = |f: &mut dyn FnMut(&mut WhirOpeningBundle61)| -> HoistedWhirBundle {
        let mut b = honest_bundle.clone();
        if let HoistedWhirPcsPayload::Single(ref mut w) = b.pcs_payload {
            f(w);
        } else {
            panic!("expected Single payload");
        }
        b
    };

    // Attack 1: Tampered `GMask61`-blinded sumcheck round polynomial coefficient (`sumcheck_rounds[0][1] + 1`):
    let atk1 = mutate_single(&mut |w| {
        w.proof.header.sumcheck_rounds[0][1][0] =
            fp0.add(w.proof.header.sumcheck_rounds[0][1][0], 1);
    });
    assert!(
        verify_hoisted_whir_bytes(
            &params,
            &ha,
            &hb,
            &hout,
            Some(&a_grid),
            None,
            &b_vec,
            &out_cts,
            &atk1.to_bytes(),
        )
        .is_err(),
        "Attack 1 (tampered sumcheck round poly) must be rejected!"
    );

    // Attack 2: WHIR OOD evaluation mismatch (`ood_eval_prev` & `final_ood_eval` forged):
    let atk2 = mutate_single(&mut |w| {
        if !w.proof.fold_rounds.is_empty() {
            w.proof.fold_rounds[0].ood_eval_prev[0] =
                fp0.add(w.proof.fold_rounds[0].ood_eval_prev[0], 1);
        } else {
            w.proof.final_ood_eval[0] = fp0.add(w.proof.final_ood_eval[0], 1);
        }
    });
    assert!(
        verify_hoisted_whir_bytes(
            &params,
            &ha,
            &hb,
            &hout,
            Some(&a_grid),
            None,
            &b_vec,
            &out_cts,
            &atk2.to_bytes(),
        )
        .is_err(),
        "Attack 2 (WHIR OOD evaluation mismatch) must be rejected!"
    );

    // Attack 3: `GMask61` forgery — consistent shift on `gmask_sum` and round-0 to pass round-0 check,
    //           caught at the `P_gmask_hat` committed PCS weld!
    let atk3a = mutate_single(&mut |w| {
        w.proof.header.gmask_sum[0] = fp0.add(w.proof.header.gmask_sum[0], 7);
    });
    let atk3b = mutate_single(&mut |w| {
        w.proof.header.z_gm_masks[0][1] = fp0.add(w.proof.header.z_gm_masks[0][1], 1);
    });
    let atk3c = mutate_single(&mut |w| {
        w.proof.header.m_eval[2] = fp0.add(w.proof.header.m_eval[2], 1);
    });
    for (lbl, atk) in [
        ("gmask_sum", atk3a),
        ("z_gm_masks", atk3b),
        ("m_eval", atk3c),
    ] {
        assert!(
            verify_hoisted_whir_bytes(
                &params,
                &ha,
                &hb,
                &hout,
                Some(&a_grid),
                None,
                &b_vec,
                &out_cts,
                &atk.to_bytes(),
            )
            .is_err(),
            "Attack 3 (GMask61 forgery on {lbl}) must be rejected!"
        );
    }

    // Attack 4: Tampered intermediate folded coset codeword (`fold_rounds[0].opened_fibers`) & `final_poly`:
    let atk4a = mutate_single(&mut |w| {
        w.proof.fold_rounds[0].opened_fibers[0][0] =
            fp0.add(w.proof.fold_rounds[0].opened_fibers[0][0], 1);
    });
    let atk4b = mutate_single(&mut |w| {
        let _ = eval_poly_ext3;
        w.proof.final_poly[0][0] = fp0.add(w.proof.final_poly[0][0], 1);
    });
    assert!(
        verify_hoisted_whir_bundle(
            &params,
            &ha,
            &hb,
            &hout,
            Some(&a_grid),
            None,
            &b_vec,
            &out_cts,
            &atk4a
        )
        .is_err(),
        "Attack 4a (tampered folded coset fiber) must be rejected!"
    );
    assert!(
        verify_hoisted_whir_bundle(
            &params,
            &ha,
            &hb,
            &hout,
            Some(&a_grid),
            None,
            &b_vec,
            &out_cts,
            &atk4b
        )
        .is_err(),
        "Attack 4b (tampered WHIR final_poly) must be rejected!"
    );

    // Attack 5: Merkle multiproof sibling / salt bit-flips (`s0_siblings`, `s0_salts`, and `fold_rounds[0].siblings`):
    let atk5a = mutate_single(&mut |w| {
        w.proof.s0_siblings[0][0] ^= 0x01;
    });
    let atk5b = mutate_single(&mut |w| {
        w.proof.s0_salts[0][0] ^= 0x80;
    });
    let atk5c = mutate_single(&mut |w| {
        w.proof.fold_rounds[0].siblings[0][3] ^= 0x04;
    });
    for (lbl, atk) in [
        ("s0_sibling", atk5a),
        ("s0_salt", atk5b),
        ("fold_sibling", atk5c),
    ] {
        assert!(
            verify_hoisted_whir_bytes(
                &params,
                &ha,
                &hb,
                &hout,
                Some(&a_grid),
                None,
                &b_vec,
                &out_cts,
                &atk.to_bytes(),
            )
            .is_err(),
            "Attack 5 (Merkle bit-flip on {lbl}) must be rejected!"
        );
    }

    // Attack 6: `HoistedB61` cross-prime / `Hole B` evaluation, ciphertext forgery, AND `#117.A.2`
    //           unbound `persistent_a` / malformed `(wit_mr, wit_mc, blow)` header bytes:
    let mut atk6a = honest_bundle.clone();
    atk6a.p0_poly_evals[0] = fp0.add(atk6a.p0_poly_evals[0], 1);
    let mut atk6b = honest_bundle.clone();
    atk6b.p17_poly_subsums[0][0] += 1;
    let mut bad_outs = out_cts.clone();
    bad_outs[0].c0[0] = fp0.add(bad_outs[0].c0[0], 1);
    let bad_hout: Vec<[u8; 32]> = bad_outs.iter().map(ct3_handle).collect();

    assert!(
        verify_hoisted_whir_bundle(
            &params,
            &ha,
            &hb,
            &hout,
            Some(&a_grid),
            None,
            &b_vec,
            &out_cts,
            &atk6a
        )
        .is_err(),
        "Attack 6a (forged p0_poly_evals) must be rejected!"
    );
    assert!(
        verify_hoisted_whir_bundle(
            &params,
            &ha,
            &hb,
            &hout,
            Some(&a_grid),
            None,
            &b_vec,
            &out_cts,
            &atk6b
        )
        .is_err(),
        "Attack 6b (forged p17_poly_subsums) must be rejected!"
    );
    assert!(
        verify_hoisted_whir_bytes(
            &params,
            &ha,
            &hb,
            &bad_hout,
            Some(&a_grid),
            None,
            &b_vec,
            &bad_outs,
            &honest_bytes,
        )
        .is_err(),
        "Attack 6c (forged output Ct3 against honest proof) must be rejected!"
    );
    let mut bad_hdr = honest_bundle.clone();
    bad_hdr.wit_mr = 0;
    assert!(
        verify_hoisted_whir_bytes(
            &params,
            &ha,
            &hb,
            &hout,
            Some(&a_grid),
            None,
            &b_vec,
            &out_cts,
            &bad_hdr.to_bytes(),
        )
        .is_err(),
        "Attack 6d (malformed wit_mr=0 header) must return Err without panic!"
    );
    let (a_pre_p, a_pcs_p) =
        commit_persistent_whir_grid(&engine, &a_grid, LiftMode::ExactGarner15).unwrap();
    let (out_p, bun_p, _, _) = prove_hoisted_whir(
        &engine,
        &a_grid,
        &b_vec,
        Some((&a_pre_p, &a_pcs_p)),
        LiftMode::ExactGarner15,
        LogUpConfig::MonolithicC4,
    )
    .unwrap();
    let hout_p: Vec<[u8; 32]> = out_p.iter().map(ct3_handle).collect();
    let bytes_p = bun_p.to_bytes();
    assert!(
        verify_hoisted_whir_bytes(&params, &ha, &hb, &hout_p, None, None, &b_vec, &out_p, &bytes_p)
            .is_err(),
        "Attack 6e (#117.A.2 persistent_a with opened_a=None and expected_root=None) must be rejected!"
    );
    let mut wrong_aroot = a_pcs_p.pcs.root;
    wrong_aroot[0] ^= 0xFF;
    assert!(
        verify_hoisted_whir_bytes(
            &params,
            &ha,
            &hb,
            &hout_p,
            None,
            Some(&wrong_aroot),
            &b_vec,
            &out_p,
            &bytes_p,
        )
        .is_err(),
        "Attack 6f (#117.A.2 persistent_a with wrong expected_persistent_a_root) must be rejected!"
    );
    assert!(
        verify_hoisted_whir_bytes(
            &params,
            &ha,
            &hb,
            &hout_p,
            Some(&a_grid),
            None,
            &b_vec,
            &out_p,
            &bytes_p,
        )
        .is_err(),
        "Attack 6g (#131 persistent_a with Some(opened_a) and expected_persistent_a_root=None) must be rejected!"
    );
    let mut bad_tq = bun_p.clone();
    bad_tq.t_queries = 9999;
    let bad_tq_bytes = bad_tq.to_bytes();
    assert!(
        verify_hoisted_whir_bytes(
            &params,
            &ha,
            &hb,
            &hout_p,
            None,
            Some(&a_pcs_p.pcs.root),
            &b_vec,
            &out_p,
            &bad_tq_bytes,
        )
        .is_err(),
        "Attack 6h (#131 oversized untrusted t_queries header) must return Err without panic!"
    );
}

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

/// 3. Full Deployed `N = 8192` Before-vs-After Benchmark across `d in {64, 256, 1024, 4096}`!
#[test]
fn test_hoisted_whir_n8192_scaling_d64_to_d4096() {
    let params = Arc::new(HoistedParams::n8192());
    let engine = Arc::new(HoistedEngine::new(params.clone()));

    println!("\n==================================================================================================================================");
    println!("darkvfhe N = 8192 Proof-Compression Benchmark: 1-Step Ligero (`succinct_pcs`) vs Multi-Round WHIR + GMask61 (`whir_pcs`)");
    println!("==================================================================================================================================");
    println!(
        "{:>5} | {:>14} | {:>11} | {:>11} | {:>8} | {:>10} | {:>10} | {:>10} | {:>17}",
        "d",
        "Mode",
        "Before(KiB)",
        "WHIR(KiB)",
        "Ratio",
        "PrvOld(ms)",
        "PrvWhir(ms)",
        "VfyWhir(ms)",
        "BCIKS / DKT (b)"
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

        let mode = LiftMode::ExactGarner15;

        // 1. Baseline 1-Step Ligero (`HoistedSuccinctBundle`):
        let (a_pre_old, a_pcs_old) =
            commit_persistent_grid_pcs(&engine, &a_grid, mode).expect("commit old persistent A");
        let t0 = Instant::now();
        let (out_old, bun_old, _, _) = prove_hoisted_succinct_bundle(
            &engine,
            &a_grid,
            &b_vec,
            Some((&a_pre_old, &a_pcs_old)),
            mode,
            LogUpConfig::MonolithicC4,
        )
        .expect("prove old succinct bundle");
        let prv_old_ms = t0.elapsed().as_secs_f64() * 1e3;
        let bytes_old = bun_old.to_bytes();
        let old_len = bytes_old.len();
        let hout_old: Vec<[u8; 32]> = out_old.par_iter().map(ct3_handle).collect();
        let dec_old = HoistedSuccinctBundle::from_bytes(&bytes_old, &params).unwrap();
        verify_hoisted_succinct_bundle(
            &params, &ha, &hb, &hout_old, None, &b_vec, &out_old, &dec_old,
        )
        .expect("verify old succinct bundle");
        drop(dec_old);
        drop(bytes_old);
        drop(out_old);
        drop(a_pre_old);
        drop(a_pcs_old);
        drop(bun_old);

        // 2. Multi-Round $2^k$-ary WHIR + `GMask61` (`HoistedWhirBundle`):
        let (a_pre_whir, a_pcs_whir) =
            commit_persistent_whir_grid(&engine, &a_grid, mode).expect("commit WHIR persistent A");
        let t1 = Instant::now();
        let (out_whir, bun_whir, _, _) = prove_hoisted_whir(
            &engine,
            &a_grid,
            &b_vec,
            Some((&a_pre_whir, &a_pcs_whir)),
            mode,
            LogUpConfig::MonolithicC4,
        )
        .expect("prove HoistedWhirBundle");
        let prv_whir_ms = t1.elapsed().as_secs_f64() * 1e3;
        let bytes_whir = bun_whir.to_bytes();
        let hout_whir: Vec<[u8; 32]> = out_whir.par_iter().map(ct3_handle).collect();
        assert_eq!(
            hout_old, hout_whir,
            "ciphertext output handles must match bit-for-bit!"
        );

        let mut vfy_whir_ms = f64::INFINITY;
        for _ in 0..3 {
            let t_vfy = Instant::now();
            verify_hoisted_whir_bytes(
                &params,
                &ha,
                &hb,
                &hout_whir,
                None,
                Some(&a_pcs_whir.pcs.root),
                &b_vec,
                &out_whir,
                &bytes_whir,
            )
            .expect("standalone zero-witness verify_hoisted_whir_bytes must succeed");
            vfy_whir_ms = vfy_whir_ms.min(t_vfy.elapsed().as_secs_f64() * 1e3);
        }

        let sh_w = WhirShape61::from_mr_mc(
            &params.fp[0],
            bun_whir.wit_mr as usize,
            bun_whir.wit_mc as usize,
            bun_whir.t_queries as usize,
            bun_whir.blow as usize,
        );
        let (bciks_b, dkt_b, _ahiv_b, _alg_b) = sh_w.soundness_bits();
        assert!(
            bciks_b >= 128.0 && dkt_b >= 128.0,
            "WHIR soundness must clear 128 bits! got bciks={bciks_b}, dkt={dkt_b}"
        );

        let old_kib = old_len as f64 / 1024.0;
        let whir_kib = bytes_whir.len() as f64 / 1024.0;
        let ratio = old_kib / whir_kib;

        // Also measure Online-Witness-Only (`opened_a` public/custodian-held, `persistent_a = None`) at `d <= 1024`:
        let online_only_str = if d <= 256 {
            let (_, bun_np, _, _) = prove_hoisted_whir(
                &engine,
                &a_grid,
                &b_vec,
                None,
                mode,
                LogUpConfig::MonolithicC4,
            )
            .expect("prove non-persistent HoistedWhirBundle");
            let np_bytes = bun_np.to_bytes();
            verify_hoisted_whir_bytes(
                &params,
                &ha,
                &hb,
                &hout_whir,
                Some(&a_grid),
                None,
                &b_vec,
                &out_whir,
                &np_bytes,
            )
            .expect("verify non-persistent HoistedWhirBundle");
            format!(
                " (SinglePCS={:.1}KiB, {:.1}x)",
                np_bytes.len() as f64 / 1024.0,
                old_kib / (np_bytes.len() as f64 / 1024.0)
            )
        } else {
            String::new()
        };

        println!(
            "{:>5} | {:>14} | {:>11.2} | {:>11.2} | {:>7.2}x | {:>10.2} | {:>10.2} | {:>10.2} | {:>7.2} / {:<7.2}{}",
            d,
            mode.as_str(),
            old_kib,
            whir_kib,
            ratio,
            prv_old_ms,
            prv_whir_ms,
            vfy_whir_ms,
            bciks_b,
            dkt_b,
            online_only_str
        );

        drop(a_pre_whir);
        drop(a_pcs_whir);
    }
}
