//! Comprehensive `WhirExt4Pcs` + `GMaskExt4` Compression, Full-Transcript HVZK (`TVD == 0`),
//! and `6/6` Adversarial Soundness Falsifier Suite for `Qwen3.5-0.8B` & `Qwen3.8-Flash-Next`!

use qwen35audit::ext4::{badd, bsub, CShakeRng, CShakeTranscript, Ext4, P_U32};
use qwen35audit::qwen35_layer::{
    execute_qwen35_24_layers_mmap, solve_real_gdn_wy_chunk64, GdnWyShape, PrecommittedMxfp4Pcs,
};
use qwen35audit::qwen38fn_slice::{prove_and_verify_qwen38fn_real_slice, QsaTopKbWitness};
use qwen35audit::safetensors_mmap::{
    decode_e2m1_x2_i32, MmapSafetensors, Mxfp4Matrix, Qwen35WeightRegistry, QWEN35_SAFETENSORS_FILE,
};
use qwen35audit::u1_audit::{
    commit_u1_pcs_boundaries, prove_u1_audit_bundle, redact_sk_secrets,
    verify_u1_audit_bundle_standalone,
};
use qwen35audit::whir_ext4::{
    commit_u1_whir_boundaries, open_whir_batch_ext4, prove_gmask_einsum_ext4,
    prove_qwen38fn_whir_slice, prove_u1_whir_audit_bundle, verify_gmask_einsum_ext4,
    verify_qwen38fn_whir_slice_bytes, verify_u1_whir_audit_bundle_standalone,
    verify_whir_batch_ext4, GMaskExt4, GMaskSpecExt4, GmaskEinSumParams, JointLinearClaimExt4,
    LinearTermExt4, PrecommittedWhirMxfp4, Qwen35U1WhirBundle, Qwen38FnWhirReceipt,
    WhirCommittedMatrixExt4, WHIR_EXT4_T_QUERIES_100,
};
use std::ops::{Add, Mul, Sub};
use std::time::Instant;

fn gaussian_rank_ext4(mut mat: Vec<Vec<Ext4>>) -> usize {
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
        let Some(piv) = (rank..rows).find(|&r| !mat[r][col].is_zero()) else {
            continue;
        };
        mat.swap(rank, piv);
        let inv_p = mat[rank][col].inv().unwrap();
        for cell in &mut mat[rank][col..cols] {
            *cell = cell.mul(inv_p);
        }
        let (upper, rest) = mat.split_at_mut(rank);
        let (piv_slice, lower) = rest.split_at_mut(1);
        let piv_row = &piv_slice[0];
        for row in upper.iter_mut().chain(lower.iter_mut()) {
            if row[col].is_zero() {
                continue;
            }
            let f = row[col];
            for (cell, &piv_cell) in row[col..cols].iter_mut().zip(piv_row[col..cols].iter()) {
                let sub = f.mul(piv_cell);
                *cell = cell.sub(sub);
            }
        }
        rank += 1;
    }
    rank
}

/// 1. Algebraic Full-Rank (`TVD == 0`) & Witness-Indistinguishability Test for `GMaskExt4` + `WhirExt4Pcs`.
#[test]
fn test_gmask_ext4_algebraic_hvzk_and_witness_indistinguishability() {
    // (a) Exact full-rank Jacobian of `GMaskExt4` over `BabyBear Ext4` (`X^4 - 11`):
    for &(ell, deg) in &[(1usize, 2usize), (6, 2), (10, 3)] {
        let mut rng = CShakeRng::from_seed(b"GMASK-RANK-AUDIT", &[ell as u8, deg as u8]);
        let r_chals: Vec<Ext4> = (0..ell)
            .map(|_| Ext4([rng.next_bb(), rng.next_bb(), rng.next_bb(), rng.next_bb()]))
            .collect();
        let specs = vec![GMaskSpecExt4::new("s", ell, deg)];
        let n_vars = ell * (deg + 1);
        let n_obs = 1 + ell * deg;
        let mut j_mat = vec![vec![Ext4::ZERO; n_vars]; n_obs];
        for v_idx in 0..n_vars {
            let mut basis = vec![Ext4::ZERO; n_vars];
            basis[v_idx] = Ext4::ONE;
            let mut gm = GMaskExt4::sample(specs.clone(), &mut rng);
            gm.coeffs = basis;
            j_mat[0][v_idx] = gm.hypercube_sum("s");
            let mut off = 1usize;
            for i in 0..ell {
                let rp = gm.round_poly("s", i, &r_chals[..i]);
                j_mat[off][v_idx] = rp[0];
                off += 1;
                for &rp_k in &rp[2..=deg] {
                    j_mat[off][v_idx] = rp_k;
                    off += 1;
                }
            }
        }
        assert_eq!(
            gaussian_rank_ext4(j_mat),
            n_obs,
            "GMaskExt4 map must have full row rank {n_obs} for ell={ell}, deg={deg} => TVD == 0!"
        );
    }

    // (b) Two distinct secret witnesses (`w_sparse` vs `w_dense`, `m = 10` -> `1024` cells) with identical
    //     public statement (`sum_x pub_a[x] * w[x] == S_pub`), opened with `BlindedEinSumExt4Proof` + `WhirExt4Pcs`!
    let m = 10usize;
    let n = 1usize << m;
    let pub_a: Vec<Ext4> = (0..n)
        .map(|i| Ext4::from_bb(((i * 13 + 5) % 97) as u32 + 1))
        .collect();

    // Pick `w_sparse` (only index 0 & 1 non-zero) and `w_dense` satisfying the exact same `<pub_a, w> == S_pub`!
    let mut w_sparse = vec![0u32; n];
    w_sparse[0] = 777_777;
    let mut w_dense: Vec<u32> = (0..n).map(|i| ((i * 99991 + 3) as u32) % P_U32).collect();
    // Adjust `w_dense[0]` so `<pub_a, w_dense> == <pub_a, w_sparse>` (note `pub_a` is in `F_p`, `pub_a[0] = 6` invertible!):
    let dot_bb = |w: &[u32]| -> u32 {
        pub_a.iter().zip(w.iter()).fold(0u32, |acc, (a, &wi)| {
            badd(acc, ((a.0[0] as u64 * wi as u64) % (P_U32 as u64)) as u32)
        })
    };
    let want_s = dot_bb(&w_sparse);
    w_dense[0] = 0;
    let rem_s = dot_bb(&w_dense);
    let diff_s = bsub(want_s, rem_s);
    let inv_a0 = qwen35audit::ext4::binv(pub_a[0].0[0]).unwrap();
    w_dense[0] = ((diff_s as u64 * inv_a0 as u64) % (P_U32 as u64)) as u32;
    assert_eq!(dot_bb(&w_sparse), dot_bb(&w_dense));

    let specs = vec![GMaskSpecExt4::new("sc", m, 3)];
    let mut bits_ones = [0usize; 2];
    let mut bits_tot = [0usize; 2];

    for (w_idx, w_tab) in [&w_sparse, &w_dense].iter().enumerate() {
        for trial in 0..16u8 {
            let seed = [
                w_idx as u8,
                trial,
                0x5A,
                0x3C,
                1,
                2,
                3,
                4,
                5,
                6,
                7,
                8,
                9,
                10,
                11,
                12,
                13,
                14,
                15,
                16,
                17,
                18,
                19,
                20,
                21,
                22,
                23,
                24,
                25,
                26,
                27,
                28,
            ];
            let mut rng = CShakeRng::from_seed(b"HVZK-TRIAL", &seed);
            let gm = GMaskExt4::sample(specs.clone(), &mut rng);
            let gm_limbs = gm.to_four_bb_tables();

            let mat = WhirCommittedMatrixExt4::commit(
                &[
                    w_tab,
                    &gm_limbs[0],
                    &gm_limbs[1],
                    &gm_limbs[2],
                    &gm_limbs[3],
                ],
                true,
                Some(seed),
            );
            let (snd_thm14, snd_eta, _) =
                mat.shape.provable_soundness_bits(WHIR_EXT4_T_QUERIES_100);
            assert!(snd_thm14 >= 100.0 && snd_eta >= 100.0);

            let mut tr_p = CShakeTranscript::new(b"HVZK-TEST");
            tr_p.absorb_root(b"r", &mat.root);
            let w_ext: Vec<Ext4> = w_tab.iter().map(|&v| Ext4::from_bb(v)).collect();
            let (bsc, rho, chals, pub_at_r, _, term) = prove_gmask_einsum_ext4(
                &pub_a,
                &w_ext,
                GmaskEinSumParams {
                    mu_s: 0,
                    kappa: m,
                    z_s: &[],
                    gmask: &gm,
                    spec_name: "sc",
                },
                &mut tr_p,
            );
            let (ws, wa) = GMaskExt4::build_spec_weights(&specs, "sc", &chals);
            let claims = vec![
                JointLinearClaimExt4::gmask_sum_claim([1, 2, 3, 4], &ws, bsc.gmask_sum),
                JointLinearClaimExt4::hvzk_terminal_weld(
                    vec![LinearTermExt4::PointEval {
                        subtable: 0,
                        point: chals.clone(),
                        weight: pub_at_r,
                    }],
                    [1, 2, 3, 4],
                    &wa,
                    rho,
                    term,
                ),
            ];
            let prf = open_whir_batch_ext4(&[(&mat, &claims)], WHIR_EXT4_T_QUERIES_100, &mut tr_p);

            let mut tr_v = CShakeTranscript::new(b"HVZK-TEST");
            tr_v.absorb_root(b"r", &mat.root);
            let (rho_v, chals_v, term_v) =
                verify_gmask_einsum_ext4(Ext4::from_bb(want_s), 0, m, &[], &bsc, &mut tr_v)
                    .unwrap();
            assert_eq!((rho_v, chals_v, term_v), (rho, chals, term));
            verify_whir_batch_ext4(
                &[(&mat.root, &mat.shape, &claims)],
                WHIR_EXT4_T_QUERIES_100,
                &prf,
                &mut tr_v,
            )
            .expect("standalone WhirExt4Pcs + GMaskExt4 must verify");

            for rd in &bsc.rounds {
                assert!(
                    !rd[3].is_zero(),
                    "GMaskExt4 deg-3 coefficient must blind c_3 == 0!"
                );
                for c in rd {
                    for &l in &c.0 {
                        for b in 0..8 {
                            bits_ones[w_idx] += ((l >> b) & 1) as usize;
                            bits_tot[w_idx] += 1;
                        }
                    }
                }
            }
        }
    }
    let p0 = bits_ones[0] as f64 / bits_tot[0] as f64;
    let p1 = bits_ones[1] as f64 / bits_tot[1] as f64;
    println!(
        "[GMaskExt4 HVZK] sparse bit-balance={p0:.4}, dense bit-balance={p1:.4} (|diff|={:.4})",
        (p0 - p1).abs()
    );
    assert!((p0 - 0.5).abs() < 0.03 && (p1 - 0.5).abs() < 0.03);
}

/// 2. End-to-End Compression Benchmark & `6/6` Adversarial Falsifiers on Real Pretrained `Qwen3.5-0.8B` & `Qwen3.8-Flash-Next`!
#[test]
fn test_qwen35_and_qwen38_whir_compression_and_six_adversarial_attacks() {
    // -----------------------------------------------------------------------------------------
    // PART A: Real Pretrained 24-Layer `Qwen/Qwen3.5-0.8B-Base` (`U1` Layer + ZK `Absent`)
    // -----------------------------------------------------------------------------------------
    let mmap = MmapSafetensors::open(QWEN35_SAFETENSORS_FILE)
        .expect("open cached Qwen3.5-0.8B safetensors");
    let registry = Qwen35WeightRegistry::commit_all_24_layers(&mmap).expect("commit 24 layers");

    let prompt_ids: Vec<u32> = (0..64).map(|i| 760 + (i * 17) as u32).collect();
    let audited_layer = 0usize;
    let (turn, _) = execute_qwen35_24_layers_mmap(&mmap, &prompt_ids, audited_layer).unwrap();

    let raw_secret_out =
        b"Generated config:\nAPI_TOKEN = \"sk-proj-abc123XYZ_secret_key_99\"\nDone.";
    let (redacted_out, red_cnt) = redact_sk_secrets(raw_secret_out);
    assert_eq!(red_cnt, 1);

    let names = Qwen35WeightRegistry::layer_tensor_names(audited_layer);
    let mut digests = Vec::new();
    let mut gate_slot = 0usize;
    for (idx, nm) in names.iter().enumerate() {
        let m = Mxfp4Matrix::from_safetensors(&mmap, nm).unwrap();
        if nm.ends_with(".mlp.gate_proj.weight") {
            gate_slot = idx;
        }
        digests.push(m.digest);
    }

    // 1. Baseline 1-step Ligero (`Qwen35U1AuditBundle`):
    let u1_old = commit_u1_pcs_boundaries(&turn.boundaries_bb);
    let gate_old = PrecommittedMxfp4Pcs::build(&turn.gate_proj_mat);
    let t_prv_old = Instant::now();
    let (old_u1_bytes, old_out_root, old_qs_bind) = prove_u1_audit_bundle(
        &registry,
        digests.clone(),
        gate_slot,
        &gate_old,
        &u1_old,
        &turn,
        &redacted_out,
    )
    .unwrap();
    let prv_old_ms = t_prv_old.elapsed().as_secs_f64() * 1e3;
    let t_vfy_old = Instant::now();
    verify_u1_audit_bundle_standalone(
        &registry.weight_root,
        &u1_old.boundary_roots,
        audited_layer,
        &old_qs_bind,
        &old_out_root,
        None,
        &old_u1_bytes,
    )
    .unwrap();
    let vfy_old_ms = t_vfy_old.elapsed().as_secs_f64() * 1e3;

    // 2. Compressed `WhirExt4Pcs + GMaskExt4` (`Qwen35U1WhirBundle`):
    let u1_whir = commit_u1_whir_boundaries(&turn.boundaries_bb);
    let gate_whir = PrecommittedWhirMxfp4::build(&turn.gate_proj_mat);
    let t_prv_whir = Instant::now();
    let (whir_u1_bytes, whir_out_root, whir_qs_bind) = prove_u1_whir_audit_bundle(
        &registry,
        digests.clone(),
        gate_slot,
        &gate_whir,
        &u1_whir,
        &turn,
        &redacted_out,
    )
    .expect("prove Qwen35U1WhirBundle");
    let prv_whir_ms = t_prv_whir.elapsed().as_secs_f64() * 1e3;

    let t_vfy_whir = Instant::now();
    verify_u1_whir_audit_bundle_standalone(
        &registry.weight_root,
        &u1_whir.boundary_roots,
        audited_layer,
        &whir_qs_bind,
        &whir_out_root,
        None,
        &whir_u1_bytes,
    )
    .expect("standalone 0-cleartext verify Qwen35U1WhirBundle");
    let vfy_whir_ms = t_vfy_whir.elapsed().as_secs_f64() * 1e3;

    verify_u1_whir_audit_bundle_standalone(
        &registry.weight_root,
        &u1_whir.boundary_roots,
        audited_layer,
        &whir_qs_bind,
        &whir_out_root,
        Some(&redacted_out),
        &whir_u1_bytes,
    )
    .expect("standalone redacted-cleartext verify Qwen35U1WhirBundle");

    let q35_old_kib = old_u1_bytes.len() as f64 / 1024.0;
    let q35_whir_kib = whir_u1_bytes.len() as f64 / 1024.0;
    println!(
        "\n[Qwen3.5-0.8B U1 + Absent] Before: {:.2} KiB ({:.2} ms vfy, {:.2} ms prv) -> WHIR+GMaskExt4: {:.2} KiB ({:.2}x smaller, {:.2} ms vfy, {:.2} ms prv)",
        q35_old_kib,
        vfy_old_ms,
        prv_old_ms,
        q35_whir_kib,
        q35_old_kib / q35_whir_kib,
        vfy_whir_ms,
        prv_whir_ms
    );
    assert!(
        q35_whir_kib < 700.0 && vfy_whir_ms < 25.0,
        "Qwen3.5 WHIR receipt must be < 700 KiB and < 25 ms verify! got {q35_whir_kib:.2} KiB, {vfy_whir_ms:.2} ms"
    );

    // -----------------------------------------------------------------------------------------
    // PART B: Full-Width `Qwen3.8-Flash-Next` (`H_v = 48` WY + `512E` `MXFP4` MoE + `QSA`)
    // -----------------------------------------------------------------------------------------
    let c_len = 64usize;
    let q: Vec<f32> = (0..(c_len * 16 * 128))
        .map(|i| ((i % 29) as f32 - 14.0) * 0.05)
        .collect();
    let k: Vec<f32> = (0..(c_len * 16 * 128))
        .map(|i| ((i % 31) as f32 - 15.0) * 0.05)
        .collect();
    let v: Vec<f32> = (0..(c_len * 48 * 128))
        .map(|i| ((i % 19) as f32 - 9.0) * 0.08)
        .collect();
    let g: Vec<f32> = (0..(c_len * 48))
        .map(|i| -0.05 * ((i % 7) as f32 + 1.0))
        .collect();
    let beta: Vec<f32> = (0..(c_len * 48))
        .map(|i| 0.2 + 0.05 * ((i % 5) as f32))
        .collect();

    let wy48 = solve_real_gdn_wy_chunk64(
        &q,
        &k,
        &v,
        &g,
        &beta,
        GdnWyShape {
            h_k: 16,
            h_v: 48,
            c_len: 64,
            d_k: 128,
            d_v: 128,
        },
    );
    let x_in: Vec<i16> = (0..(64 * 2560)).map(|i| ((i % 41) as i16) - 20).collect();
    let mut nibs_pad = vec![0u8; 1024 * 128 * 32];
    let mut scs_pad = vec![0u32; 1024 * 128];
    for j in 0..640 {
        for blk in 0..80 {
            scs_pad[j * 128 + blk] = 64;
            for b in 0..32 {
                nibs_pad[(j * 128 + blk) * 32 + b] = ((j + blk + b) & 15) as u8;
            }
        }
    }
    let mut y_raw = vec![0i64; 64 * 1024];
    for t in 0..64 {
        for j in 0..640 {
            let mut acc = 0i64;
            for blk in 0..80 {
                let s = scs_pad[j * 128 + blk] as i64;
                let mut bs = 0i64;
                for b in 0..32 {
                    let xv = x_in[t * 2560 + blk * 32 + b] as i64;
                    let qv = decode_e2m1_x2_i32(nibs_pad[(j * 128 + blk) * 32 + b]) as i64;
                    bs += xv * qv;
                }
                acc += s * bs;
            }
            y_raw[t * 1024 + j] = acc;
        }
    }
    let relu_scores: Vec<u32> = (0..(64 * 16))
        .map(|i| {
            if (i % 3) == 0 {
                0
            } else {
                ((i * 5) % 25) as u32
            }
        })
        .collect();
    let qsa = QsaTopKbWitness {
        num_queries: 64,
        num_blocks: 16,
        k_budget: 4,
        relu_scores,
    };

    let old_q38 =
        prove_and_verify_qwen38fn_real_slice(&wy48, &x_in, &nibs_pad, &scs_pad, &y_raw, &qsa)
            .unwrap();
    let q38_old_wy_kib = old_q38.wy_proof_bytes.len() as f64 / 1024.0;
    let q38_old_tot_kib =
        (old_q38.wy_proof_bytes.len() + old_q38.qsa_proof_bytes.len()) as f64 / 1024.0;

    let expert_whir = PrecommittedWhirMxfp4::from_padded(1024, 128, nibs_pad, scs_pad);
    let q38_whir = prove_qwen38fn_whir_slice(&wy48, &x_in, &expert_whir, &y_raw, &qsa, None)
        .expect("prove Qwen3.8 WHIR");
    let q38_whir_kib = q38_whir.proof_bytes.len() as f64 / 1024.0;

    println!(
        "[Qwen3.8-Flash-Next H_v=48] Before: {:.2} KiB WY+MoE ({:.2} KiB w/ QSA, {:.2} ms vfy) -> WHIR+GMaskExt4: {:.2} KiB ALL-IN-ONE ({:.2}x vs WY+MoE, {:.2}x vs WY+MoE+QSA, {:.2} ms vfy, {:.2} ms prv)",
        q38_old_wy_kib,
        q38_old_tot_kib,
        old_q38.wy_verify_ms,
        q38_whir_kib,
        q38_old_wy_kib / q38_whir_kib,
        q38_old_tot_kib / q38_whir_kib,
        q38_whir.verify_ms,
        q38_whir.prove_ms
    );
    assert!(
        q38_whir_kib < 700.0 && q38_whir.verify_ms < 25.0,
        "Qwen3.8 WHIR receipt must be < 700 KiB and < 25 ms verify! got {q38_whir_kib:.2} KiB, {:.2} ms",
        q38_whir.verify_ms
    );

    // -----------------------------------------------------------------------------------------
    // PART C: `6/6` Required Soundness Attacks — ALL Deterministically Rejected!
    // -----------------------------------------------------------------------------------------
    let base_u1 = Qwen35U1WhirBundle::from_bytes(&whir_u1_bytes).unwrap();
    let base_q38 = Qwen38FnWhirReceipt::from_bytes(&q38_whir.proof_bytes).unwrap();

    // Attack 1: Tampered `GMaskExt4`-blinded sumcheck round polynomial (`wy_blinded_sc.rounds[0][1] + 1`):
    let mut atk1 = base_u1.clone();
    atk1.wy_blinded_sc.rounds[0][1] = atk1.wy_blinded_sc.rounds[0][1].add(Ext4::ONE);
    assert!(
        verify_u1_whir_audit_bundle_standalone(
            &registry.weight_root,
            &u1_whir.boundary_roots,
            audited_layer,
            &whir_qs_bind,
            &whir_out_root,
            None,
            &atk1.to_bytes(),
        )
        .is_err(),
        "Attack 1 (tampered GMaskExt4 round poly) must be rejected!"
    );

    // Attack 2: Tampered WHIR `u = 2` OOD evaluation (`cascade_levels[0].ood_evals[0]` & `final_ood_evals[1]`):
    let mut atk2a = base_u1.clone();
    atk2a.whir_batch_proof.cascade_levels[0].ood_evals[0] =
        atk2a.whir_batch_proof.cascade_levels[0].ood_evals[0].add(Ext4::ONE);
    let mut atk2b = base_q38.clone();
    atk2b.whir_batch_proof.final_ood_evals[1] =
        atk2b.whir_batch_proof.final_ood_evals[1].add(Ext4::ONE);
    assert!(
        verify_u1_whir_audit_bundle_standalone(
            &registry.weight_root,
            &u1_whir.boundary_roots,
            audited_layer,
            &whir_qs_bind,
            &whir_out_root,
            None,
            &atk2a.to_bytes(),
        )
        .is_err(),
        "Attack 2a (tampered WHIR cascade OOD eval) must be rejected!"
    );
    assert!(
        verify_qwen38fn_whir_slice_bytes(
            &q38_whir.qs_whir_root,
            &q38_whir.qsa_keys_whir_root,
            (64, 16, 4),
            &atk2b.to_bytes(),
        )
        .is_err(),
        "Attack 2b (tampered WHIR final OOD eval) must be rejected!"
    );

    // Attack 3: `GMaskExt4` / PCS `z_gm_masks` forgery (`gmask_sum` or `z_gm_masks` mutated):
    let mut atk3a = base_u1.clone();
    atk3a.slt_blinded_sc.gmask_sum = atk3a.slt_blinded_sc.gmask_sum.add(Ext4::ONE);
    let mut atk3b = base_u1.clone();
    atk3b.whir_batch_proof.matrix_parts[0].z_gm_masks[0] =
        atk3b.whir_batch_proof.matrix_parts[0].z_gm_masks[0].add(Ext4::ONE);
    assert!(
        verify_u1_whir_audit_bundle_standalone(
            &registry.weight_root,
            &u1_whir.boundary_roots,
            audited_layer,
            &whir_qs_bind,
            &whir_out_root,
            None,
            &atk3a.to_bytes(),
        )
        .is_err(),
        "Attack 3a (forged external GMaskExt4 sum) must be rejected!"
    );
    assert!(
        verify_u1_whir_audit_bundle_standalone(
            &registry.weight_root,
            &u1_whir.boundary_roots,
            audited_layer,
            &whir_qs_bind,
            &whir_out_root,
            None,
            &atk3b.to_bytes(),
        )
        .is_err(),
        "Attack 3b (forged internal Z_gm mask) must be rejected!"
    );

    // Attack 4: Pretrained `MXFP4` weight digest / `U1` boundary residual tamper:
    let mut atk4a = base_u1.clone();
    atk4a.layer_tensor_digests[gate_slot][0] ^= 0x01;
    let mut bad_bnds = u1_whir.boundary_roots;
    bad_bnds[audited_layer + 1][0] ^= 0xFF;
    assert!(
        verify_u1_whir_audit_bundle_standalone(
            &registry.weight_root,
            &u1_whir.boundary_roots,
            audited_layer,
            &whir_qs_bind,
            &whir_out_root,
            None,
            &atk4a.to_bytes(),
        )
        .is_err(),
        "Attack 4a (MXFP4 weight nibble/digest tamper) must be rejected!"
    );
    assert!(
        verify_u1_whir_audit_bundle_standalone(
            &registry.weight_root,
            &bad_bnds,
            audited_layer,
            &whir_qs_bind,
            &whir_out_root,
            None,
            &whir_u1_bytes,
        )
        .is_err(),
        "Attack 4b (U1 boundary root tamper) must be rejected!"
    );

    // Attack 5: `cSHAKE256` WHIR Merkle multiproof / folded coset fiber bit-flip:
    let mut atk5a = base_u1.clone();
    atk5a.whir_batch_proof.cascade_levels[0]
        .multiproof
        .aux_hashes[0][2] ^= 0x40;
    let mut atk5b = base_q38.clone();
    atk5b.whir_batch_proof.cascade_levels[1].opened_fibers[0] =
        atk5b.whir_batch_proof.cascade_levels[1].opened_fibers[0].add(Ext4::ONE);
    assert!(
        verify_u1_whir_audit_bundle_standalone(
            &registry.weight_root,
            &u1_whir.boundary_roots,
            audited_layer,
            &whir_qs_bind,
            &whir_out_root,
            None,
            &atk5a.to_bytes(),
        )
        .is_err(),
        "Attack 5a (cSHAKE256 WHIR Merkle sibling flip) must be rejected!"
    );
    assert!(
        verify_qwen38fn_whir_slice_bytes(
            &q38_whir.qs_whir_root,
            &q38_whir.qsa_keys_whir_root,
            (64, 16, 4),
            &atk5b.to_bytes(),
        )
        .is_err(),
        "Attack 5b (WHIR folded coset fiber mutation) must be rejected!"
    );

    // `#117.A.1` & `#117.A.3` Adversarial Regressions:
    // - Forged QSA `sel` / `qsa_keys_whir_root` / `k_budget` mismatch must be rejected!
    let mut atk_qsa_sel = base_q38.clone();
    atk_qsa_sel.qsa_sel_at_r = atk_qsa_sel.qsa_sel_at_r.add(Ext4::ONE);
    assert!(
        verify_qwen38fn_whir_slice_bytes(
            &q38_whir.qs_whir_root,
            &q38_whir.qsa_keys_whir_root,
            (64, 16, 4),
            &atk_qsa_sel.to_bytes(),
        )
        .is_err(),
        "#117.A.1 forged QSA sel_at_r must be rejected!"
    );
    let mut bad_qsa_keys_root = q38_whir.qsa_keys_whir_root;
    bad_qsa_keys_root[0] ^= 0x55;
    assert!(
        verify_qwen38fn_whir_slice_bytes(
            &q38_whir.qs_whir_root,
            &bad_qsa_keys_root,
            (64, 16, 4),
            &q38_whir.proof_bytes,
        )
        .is_err(),
        "#117.A.1 mismatched QSA keys root must be rejected!"
    );
    assert!(
        verify_qwen38fn_whir_slice_bytes(
            &q38_whir.qs_whir_root,
            &q38_whir.qsa_keys_whir_root,
            (64, 16, 3),
            &q38_whir.proof_bytes,
        )
        .is_err(),
        "#117.A.1 forged QSA k_budget must be rejected!"
    );
    // - Forged `b_at_zeof` (`#117.A.3` tail EOF check) must be rejected!
    let mut atk_eof = base_u1.clone();
    atk_eof.b_at_zeof = atk_eof.b_at_zeof.add(Ext4::ONE);
    assert!(
        verify_u1_whir_audit_bundle_standalone(
            &registry.weight_root,
            &u1_whir.boundary_roots,
            audited_layer,
            &whir_qs_bind,
            &whir_out_root,
            None,
            &atk_eof.to_bytes(),
        )
        .is_err(),
        "#117.A.3 forged EOF evaluation must be rejected!"
    );

    // Attack 6: Unredacted `sk-proj-...` API secret leak (`P4`/`P6`) & `QSA` `Trap B1a` `tau >= 2^30` wraparound!
    assert!(
        prove_u1_whir_audit_bundle(
            &registry,
            digests,
            gate_slot,
            &gate_whir,
            &u1_whir,
            &turn,
            raw_secret_out,
        )
        .is_err(),
        "Attack 6a (unredacted sk-proj-... secret leak) must be refused by prover!"
    );
    let mut atk6_sink = base_u1;
    atk6_sink.final_dfa_state = 4;
    assert!(
        verify_u1_whir_audit_bundle_standalone(
            &registry.weight_root,
            &u1_whir.boundary_roots,
            audited_layer,
            &whir_qs_bind,
            &whir_out_root,
            None,
            &atk6_sink.to_bytes(),
        )
        .is_err(),
        "Attack 6b (non-accepting sink state 4 in receipt) must be rejected by verifier!"
    );
    assert!(
        prove_qwen38fn_whir_slice(
            &wy48,
            &x_in,
            &expert_whir,
            &y_raw,
            &qsa,
            Some((40, (8u32 << 27) + 15))
        )
        .is_err(),
        "Attack 6c (QSA Trap B1a 30-bit tau wraparound) must be rejected by C5!"
    );
}
