//! Real pretrained `Qwen3.5-0.8B` (`24L: 18 GDN + 6 GQA`) & `Qwen3.8-Flash-Next-FP8` (`4L` HTTP-Range slice:
//! `3 GDN [H_v=48, d=128, C=64] + 1 QSA + 4-branch GR + 512E Top-10+1 MoE + 51.2B SplitMix64 PLE`)
//! `U1` commit-then-audit prover & standalone succinct `BabyBear Ext4` (`X^4 - 11`, `cSHAKE256`) verifier.

pub mod agent_runner;
pub mod bpe_bridge;
pub mod continual_memory;
pub mod dregg180_hem_bridge;
pub mod ext4;
pub mod full_model_24l_audit;
pub mod gruen_ext4;
pub mod pcs_ext4;
pub mod py_bundle;
pub mod qwen35_layer;
pub mod qwen38fn_slice;
pub mod safetensors_mmap;
pub mod spec_prefill;
pub mod streaming_gdn_carry;
pub mod u1_audit;
pub mod unified_turn_weld;
pub mod whir_ext4;
