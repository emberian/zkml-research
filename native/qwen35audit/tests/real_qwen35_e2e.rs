//! End-to-End Integration & Planted Soundness Falsifier Tests over Real Pretrained
//! `Qwen/Qwen3.5-0.8B-Base` (`model.safetensors-00001-of-00001.safetensors`) & `Qwen3.8-Flash-Next` (`H_v = 48`).

use qwen35audit::ext4::{CShakeTranscript, Ext4, P_U32};
use qwen35audit::gruen_ext4::{prove_strict_lower_tri_ext4, verify_strict_lower_tri_ext4};
use qwen35audit::qwen35_layer::{
    execute_qwen35_24_layers_mmap, solve_real_gdn_wy_chunk64, GdnWyShape, PrecommittedMxfp4Pcs,
};
use qwen35audit::qwen38fn_slice::{
    prove_and_verify_qwen38fn_real_slice, prove_qsa_top_kb_ext4, verify_qsa_top_kb_ext4,
    QsaTopKbWitness,
};
use qwen35audit::safetensors_mmap::{
    MmapSafetensors, Mxfp4Matrix, Qwen35WeightRegistry, QWEN35_SAFETENSORS_FILE, WY_SCALE,
};
use qwen35audit::u1_audit::{
    broken_whole_word_complement_sk, commit_u1_pcs_boundaries, prove_padded_absence_zk,
    prove_u1_audit_bundle, redact_sk_secrets, verify_padded_absence_zk,
    verify_u1_audit_bundle_standalone, Qwen35U1AuditBundle,
};
use std::ops::Add;

#[test]
fn test_real_qwen35_pretrained_e2e_u1_audit_and_all_planted_attacks() {
    let mmap =
        MmapSafetensors::open(QWEN35_SAFETENSORS_FILE).expect("open cached Qwen3.5 safetensors");
    assert_eq!(mmap.tensors.len(), 488);

    let registry = Qwen35WeightRegistry::commit_all_24_layers(&mmap).expect("commit 24 layers");
    assert_eq!(registry.total_tensors_committed, 18 * 8 + 6 * 7);

    let prompt_ids: Vec<u32> = (0..64).map(|i| 760 + (i * 17) as u32).collect();
    let audited_layer = 0usize; // Real Layer 0 (`Gated DeltaNet + SwiGLU`)
    let (turn, final_h) =
        execute_qwen35_24_layers_mmap(&mmap, &prompt_ids, audited_layer).expect("24L forward");
    assert_eq!(final_h.len(), 64 * 1024);
    assert!(final_h.iter().all(|x| x.is_finite()));

    let u1_online = commit_u1_pcs_boundaries(&turn.boundaries_bb);

    let raw_secret_out =
        b"Generated config:\nAPI_TOKEN = \"sk-proj-abc123XYZ_secret_key_99\"\nDone.";
    let (redacted_out, red_cnt) = redact_sk_secrets(raw_secret_out);
    assert_eq!(red_cnt, 1);
    assert!(!String::from_utf8_lossy(&redacted_out).contains("sk-proj-"));
    // Verify P4 whole-word complement trap (`"xPx"` false acceptance):
    assert!(broken_whole_word_complement_sk(raw_secret_out));

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
    let gate_pcs = PrecommittedMxfp4Pcs::build(&turn.gate_proj_mat);

    let (proof_bytes, out_root, qs_binding) = prove_u1_audit_bundle(
        &registry,
        digests,
        gate_slot,
        &gate_pcs,
        &u1_online,
        &turn,
        &redacted_out,
    )
    .expect("prove U1 bundle");

    // Standalone verification WITH zero cleartext (`None`) and WITH redacted cleartext (`Some`)!
    verify_u1_audit_bundle_standalone(
        &registry.weight_root,
        &u1_online.boundary_roots,
        audited_layer,
        &qs_binding,
        &out_root,
        None,
        &proof_bytes,
    )
    .expect("standalone 0-cleartext ZK audit verify");

    verify_u1_audit_bundle_standalone(
        &registry.weight_root,
        &u1_online.boundary_roots,
        audited_layer,
        &qs_binding,
        &out_root,
        Some(&redacted_out),
        &proof_bytes,
    )
    .expect("standalone redacted-cleartext audit verify");

    let base_bundle = Qwen35U1AuditBundle::from_bytes(&proof_bytes).unwrap();

    // --- Planted Attack 1: Swapping 1 pretrained MXFP4 weight nibble ---
    let mut b1 = base_bundle.clone();
    b1.layer_proof.layer_tensor_digests[gate_slot][0] ^= 0x01;
    assert!(verify_u1_audit_bundle_standalone(
        &registry.weight_root,
        &u1_online.boundary_roots,
        audited_layer,
        &qs_binding,
        &out_root,
        None,
        &b1.to_bytes(),
    )
    .is_err());

    // --- Planted Attack 2a: Mutating 1 GDN WY `UW` cell claim ---
    let mut b2 = base_bundle.clone();
    b2.layer_proof.wy_gruen_proof.terminal_openings.1 = b2
        .layer_proof
        .wy_gruen_proof
        .terminal_openings
        .1
        .add(Ext4::ONE);
    assert!(verify_u1_audit_bundle_standalone(
        &registry.weight_root,
        &u1_online.boundary_roots,
        audited_layer,
        &qs_binding,
        &out_root,
        None,
        &b2.to_bytes(),
    )
    .is_err());

    // --- Planted Attack 2b (`Hole B` on WY): Mutating `UW[0] += 1` & compensating `R_rem[0] += M_wy` ---
    let mut forged_turn = Qwen35TurnExecutionClone::from_turn(&turn);
    forged_turn.wy.uw_lsb_hik[0] = (forged_turn.wy.uw_lsb_hik[0] + 1) % P_U32;
    forged_turn.wy.rem_lsb_hik[0] += WY_SCALE as u32; // >= 4096 -> caught by D1b range check!
    assert!(
        qwen35audit::gruen_ext4::compute_d1b_multiplicities(&forged_turn.wy.rem_lsb_hik, 12)
            .is_err()
    );

    // --- Planted Attack 2c (`A1b` non-strict-lower `L[0,0,0] = P - 1`): caught by SLT zerocheck! ---
    let mut bad_l = turn.wy_witness.l_lsb_hij.clone();
    bad_l[0] = P_U32 - 1;
    let mut p_tr = CShakeTranscript::new(b"a1b");
    let (bad_slt_pf, _) = prove_strict_lower_tri_ext4(&bad_l, 4, 6, &mut p_tr);
    let mut v_tr = CShakeTranscript::new(b"a1b");
    assert!(verify_strict_lower_tri_ext4(4, 6, &bad_slt_pf, &mut v_tr).is_err());

    // --- Planted Attack 3: Mutating 1 boundary activation (`boundary_roots[1]`) ---
    let mut bad_bnds = u1_online.boundary_roots;
    bad_bnds[audited_layer + 1][0] ^= 0xFF;
    assert!(verify_u1_audit_bundle_standalone(
        &registry.weight_root,
        &bad_bnds,
        audited_layer,
        &qs_binding,
        &out_root,
        None,
        &proof_bytes,
    )
    .is_err());

    // --- Planted Attack 4: Forging PCS Merkle multiproof sibling hash ---
    let mut b4 = base_bundle.clone();
    b4.layer_proof.q_pcs_proof.multiproof.aux_hashes[0][3] ^= 0x42;
    assert!(verify_u1_audit_bundle_standalone(
        &registry.weight_root,
        &u1_online.boundary_roots,
        audited_layer,
        &qs_binding,
        &out_root,
        None,
        &b4.to_bytes(),
    )
    .is_err());

    // --- Planted Attack 5: Leaking unredacted `sk-...` secret (prover & verifier both reject, incl. forged ZK state) ---
    let mut abs_tr = CShakeTranscript::new(b"leak");
    assert!(prove_padded_absence_zk(raw_secret_out, &mut abs_tr).is_err());
    let mut b5 = base_bundle;
    b5.absence_receipt.final_state = 4; // sink state!
    let mut v_abs = CShakeTranscript::new(b"QW35-U1-ABSENCE-V1");
    assert!(verify_padded_absence_zk(&out_root, None, &b5.absence_receipt, &mut v_abs).is_err());
}

struct Qwen35TurnExecutionClone {
    wy: qwen35audit::qwen35_layer::RealGdnWyWitness,
}
impl Qwen35TurnExecutionClone {
    fn from_turn(t: &qwen35audit::qwen35_layer::Qwen35TurnExecution) -> Self {
        Self {
            wy: t.wy_witness.clone(),
        }
    }
}

#[test]
fn test_qwen38_flash_next_hv48_wy_moe_and_qsa_c3_c5_traps() {
    // Full-dimension `Qwen3.8-Flash-Next` (`H_k = 16, H_v = 48 -> 64, C = 64, d_k = d_v = 128`) + QSA `ReLU == 0` ties!
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
                    let qv = qwen35audit::safetensors_mmap::decode_e2m1_x2_i32(
                        nibs_pad[(j * 128 + blk) * 32 + b],
                    ) as i64;
                    bs += xv * qv;
                }
                acc += s * bs;
            }
            y_raw[t * 1024 + j] = acc;
        }
    }

    // QSA witness WITH ubiquitous `ReLU == 0` score ties (`Trap B1b` completeness test!)
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

    let bundle =
        prove_and_verify_qwen38fn_real_slice(&wy48, &x_in, &nibs_pad, &scs_pad, &y_raw, &qsa)
            .expect("Qwen3.8-Flash-Next H_v=48 WY + MoE + QSA verify");
    verify_qsa_top_kb_ext4(&bundle.qsa_proof_bytes).expect("standalone QSA verify");

    // Verify `Trap B1a` (`tau = 8 * 2^27 + 15` 30-bit wraparound) is deterministically rejected by `C5`!
    assert!(prove_qsa_top_kb_ext4(&qsa, Some((40, (8u32 << 27) + 15))).is_err());
}
