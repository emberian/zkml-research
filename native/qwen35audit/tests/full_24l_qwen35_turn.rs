#![deny(warnings)]
//! End-to-end `--release` benchmark, `f32` reference top-1 logit/token parity check, and exhaustive
//! 8-way adversarial layer-tamper falsifier suite for `Full24LayerQwen35Receipt` across ALL 24 layers
//! (`18` Gated-DeltaNet + `6` Full-Attention GQA + `24` SwiGLU MLPs + `48` Layer RMSNorms +
//! `embed_tokens` + `final_norm` + `248,320`-vocab tied `lm_head` argmax) of `Qwen/Qwen3.5-0.8B-Base`.

use qwen35audit::agent_runner::QwenBpeTokenizer;
use qwen35audit::ext4::{Ext4, P_U32};
use qwen35audit::full_model_24l_audit::{
    execute_f32_reference_24l, prove_full_24l_qwen35_turn_from_prompt,
    prove_tampered_full_24l_qwen35_turn, verify_full_24l_qwen35_receipt, Full24LayerQwen35Receipt,
    Full24LayerTamperKind, PrecomputedModelWeights24L, FULL_24L_SEQ_LEN,
};
use qwen35audit::safetensors_mmap::{QWEN35_SAFETENSORS_FILE, QWEN35_TOKENIZER_FILE};
use std::time::Instant;

const REAL_16_TOKEN_PROMPT: &str =
    "The largest planet in our solar system is Jupiter, and the capital of France is";

#[test]
fn test_full_24l_qwen35_end_to_end_turn_and_all_8_falsifiers() {
    let tokenizer =
        QwenBpeTokenizer::from_file(QWEN35_TOKENIZER_FILE).expect("load Qwen3.5 tokenizer.json");
    let prompt_ids = tokenizer.encode(REAL_16_TOKEN_PROMPT);
    assert_eq!(
        prompt_ids.len(),
        FULL_24L_SEQ_LEN,
        "expected exactly 16 real BPE tokens, got {:?}",
        prompt_ids
    );
    let mut prompt_arr = [0u32; FULL_24L_SEQ_LEN];
    prompt_arr.copy_from_slice(&prompt_ids);

    // 1. Reference 24-layer `f32` forward pass on real HuggingFace `Qwen/Qwen3.5-0.8B-Base` weights:
    let t_f32 = Instant::now();
    let f32_ref =
        execute_f32_reference_24l(QWEN35_SAFETENSORS_FILE, &prompt_arr).expect("f32 24L forward");
    let f32_ms = t_f32.elapsed().as_secs_f64() * 1000.0;
    let f32_decoded = tokenizer.decode_lossy(&[f32_ref.top1_token_id]);

    // 2. Offline/cached `WeightModelRoot24L` commitment across all 267 checkpoint tensors:
    let t_setup = Instant::now();
    let weights = PrecomputedModelWeights24L::build_default()
        .expect("build 24-layer WeightModelRoot24L from safetensors");
    let setup_ms = t_setup.elapsed().as_secs_f64() * 1000.0;

    // 3. Online 24-layer batched `WhirExt4Pcs + GMaskExt4` proving:
    let t_prove = Instant::now();
    let receipt =
        prove_full_24l_qwen35_turn_from_prompt(&weights, &tokenizer, REAL_16_TOKEN_PROMPT)
            .expect("prove full 24-layer Qwen3.5 turn");
    let prove_ms = t_prove.elapsed().as_secs_f64() * 1000.0;

    let wire_bytes = receipt.to_bytes();
    let wire_kib = (wire_bytes.len() as f64) / 1024.0;
    let decoded_receipt =
        Full24LayerQwen35Receipt::from_bytes(&wire_bytes).expect("deserialize receipt");
    assert_eq!(decoded_receipt, receipt);

    // 4. Standalone verification (`< 150 ms` target!):
    // Warm once + measure standalone verification from deserialized `decoded_receipt`:
    verify_full_24l_qwen35_receipt(&weights.model_root, &prompt_arr, &decoded_receipt)
        .expect("standalone full 24L verification");
    let n_runs = 5usize;
    let t_ver = Instant::now();
    for _ in 0..n_runs {
        verify_full_24l_qwen35_receipt(&weights.model_root, &prompt_arr, &decoded_receipt)
            .expect("standalone full 24L verification repeat");
    }
    let verify_ms = (t_ver.elapsed().as_secs_f64() * 1000.0) / (n_runs as f64);

    let int_decoded = tokenizer.decode_lossy(&[receipt.emitted_next_token_id]);
    println!(
        "\n=== Full 24-Layer Qwen3.5-0.8B-Base Batched WhirExt4Pcs + GMaskExt4 Receipt ===\n\
         prompt ({} BPE tokens): {:?} -> {:?}\n\
         f32 24L reference:      top1 = {} ({:?}, logit = {:.4}) [{:.2} ms]\n\
         proved 24L integer:     top1 = {} ({:?}, scaled_logit = {:.4})\n\
         WeightModelRoot24L:     setup = {:.2} ms (max_row_l1 = {}, max_conv_l1 = {}, max_gain = {}, qk_gain = {}, scalar = {})\n\
         24L online prove:       {:.2} ms\n\
         24L standalone verify:  {:.2} ms (budget < 150.0 ms)\n\
         wire receipt size:      {} B ({:.2} KiB)",
        prompt_arr.len(),
        REAL_16_TOKEN_PROMPT,
        prompt_arr,
        f32_ref.top1_token_id,
        f32_decoded,
        f32_ref.top1_logit,
        f32_ms,
        receipt.emitted_next_token_id,
        int_decoded,
        (receipt.claimed_max_logit as f64) / 256.0,
        setup_ms,
        weights.model_root.max_row_l1,
        weights.model_root.max_conv_l1,
        weights.model_root.max_gain_abs,
        weights.model_root.max_gdn_qk_gain,
        weights.model_root.max_scalar_abs,
        prove_ms,
        verify_ms,
        wire_bytes.len(),
        wire_kib,
    );

    // Assert exact top-1 token parity vs 24-layer `f32` reference forward pass:
    assert_eq!(
        receipt.emitted_next_token_id, f32_ref.top1_token_id,
        "24-layer proved top-1 token {} ({:?}) != f32 reference {} ({:?})",
        receipt.emitted_next_token_id, int_decoded, f32_ref.top1_token_id, f32_decoded
    );
    if cfg!(not(debug_assertions)) {
        assert!(
            verify_ms < 150.0,
            "standalone verify_ms {:.2} exceeded 150 ms budget",
            verify_ms
        );
    }

    // Post-audit typed/wire invariant guards (`gpt-6.2-astra` `M3` + `L1`):
    {
        let mut malleated = decoded_receipt.clone();
        malleated.online_whir_proof.final_lockstep_sc = vec![[Ext4::ONE, Ext4::ZERO, Ext4::ZERO]];
        let err = verify_full_24l_qwen35_receipt(&weights.model_root, &prompt_arr, &malleated)
            .expect_err("non-zero reserved final_lockstep_sc must be rejected");
        assert!(err.contains("final_lockstep_sc"), "unexpected error: {err}");

        let mut non_canon = decoded_receipt.clone();
        non_canon.linear_point_evals[0].0[0] = P_U32;
        let err_nc = verify_full_24l_qwen35_receipt(&weights.model_root, &prompt_arr, &non_canon)
            .expect_err("non-canonical Ext4 limb must be rejected");
        assert!(
            err_nc.contains("non-canonical"),
            "unexpected error: {err_nc}"
        );
    }

    // 5. Exhaustive 10-Way Adversarial Layer-Tamper Falsifier Suite (freshly committed & re-proved, pinning exact rejection boundary!):
    let all_tampers: [(Full24LayerTamperKind, &str); 10] = [
        (
            Full24LayerTamperKind::EmbedTokensHIn0,
            "PublicWeight row sumcheck round 0 failed",
        ),
        (
            Full24LayerTamperKind::Layer0GdnWyUwy,
            "BlindedEinSumExt4Proof round 0 failed",
        ),
        (
            Full24LayerTamperKind::Layer3GqaQkRopeSoftmax,
            "BlindedEinSumExt4Proof round 0 failed",
        ),
        (
            Full24LayerTamperKind::Layer11GqaOProj,
            "BlindedEinSumExt4Proof round 0 failed",
        ),
        (
            Full24LayerTamperKind::Layer14SwiGluSiluDownProj,
            "BlindedEinSumExt4Proof round 0 failed",
        ),
        (
            Full24LayerTamperKind::Layer14SwiGluMul,
            "BlindedEinSumExt4Proof round 0 failed",
        ),
        (
            Full24LayerTamperKind::Layer14SwiGluSiluLut,
            "D1b tuple terminal layer check failed",
        ),
        (
            Full24LayerTamperKind::CrossLayerSpliceL7ToL8,
            "WHIR matrix 2 row sumcheck round 0 failed",
        ),
        (
            Full24LayerTamperKind::Layer22RmsNormScale,
            "BlindedEinSumExt4Proof round 0 failed",
        ),
        (
            Full24LayerTamperKind::FinalLmHeadArgmaxToken,
            "lm_head greedy argmax dominance equation failed",
        ),
    ];

    for (idx, &(kind, expected_err)) in all_tampers.iter().enumerate() {
        let forged = prove_tampered_full_24l_qwen35_turn(&weights, &prompt_arr, kind)
            .unwrap_or_else(|e| panic!("adversarial receipt generation failed on {kind:?}: {e}"));
        let forged_bytes = forged.to_bytes();
        let forged_dec = Full24LayerQwen35Receipt::from_bytes(&forged_bytes)
            .expect("forged wire receipt must deserialize cleanly");
        let err = verify_full_24l_qwen35_receipt(&weights.model_root, &prompt_arr, &forged_dec)
            .expect_err(&format!(
                "MANDATORY FALSIFIER #{} ({:?}) WAS ACCEPTED!",
                idx + 1,
                kind
            ));
        assert!(
            err.contains(expected_err),
            "FALSIFIER #{} ({:?}) rejected at wrong boundary: got {:?}, expected substring {:?}",
            idx + 1,
            kind,
            err,
            expected_err
        );
        println!(
            "  [falsifier #{}/{} REJECTED] {:?} -> {}",
            idx + 1,
            all_tampers.len(),
            kind,
            err
        );
    }
}
