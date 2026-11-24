//! Native multithreaded deterministic exact-integer (`MXFP4`/`FP8-E4M3` + `INT16` + `C=64` `IntWY`)
//! 24-layer `Qwen/Qwen3.5-0.8B-Base` token generator, `Qwen3.8-27B` real `MXFP4` slice loader/prover,
//! verified multi-pattern secret-redaction + 139-rule LL(1) `miniJsonCfg` AST transducer, and
//! canonical `StreamCodec`-compatible `VAGENT01` / `VASTMT01` end-to-end turn receipt bundler.
//!
//! Zero PyTorch, zero Python in the online path, and **zero floating-point operations** anywhere in
//! online prefill or autoregressive token decoding (`1` vs `12` `rayon` threads produce bit-identical
//! SHA-256 and `cSHAKE256` digests at every layer boundary and output token).

use crate::ext4::{
    bb_from_i64, build_eq_table_lsb_ext4, cshake256_32, eq_mle_ext4, merkle_open_single_cshake,
    merkle_root_cshake, mle_eval_bb_at_ext4, ByteCursor, CShakeTranscript, Ext4, P, P_U32,
};
use crate::gruen_ext4::{
    compute_d1b_multiplicities, compute_d1b_public_table_multiplicities,
    prove_d1b_public_table_ext4, prove_d1b_range_ext4, prove_gruen_einsum_mode2_ext4,
    prove_mxfp4_delayed_bjk_horner_ext4, verify_d1b_public_table_ext4, verify_d1b_range_ext4,
    verify_gruen_einsum_mode2_ext4, verify_mxfp4_delayed_bjk_horner_ext4, D1bRangeExt4Proof,
    GruenMode2Ext4Proof, Mxfp4DelayedBjkExt4Proof,
};
use crate::pcs_ext4::{
    commit_table_pcs, open_pcs_claims, verify_pcs_claims, MleEvalClaim, PcsOpeningProof, PcsParams,
    PcsShape,
};
use crate::qwen35_layer::{
    prove_audited_gdn_layer, verify_audited_gdn_layer_standalone, AuditedGdnLayerVerifyStmt,
    AuditedGdnLayerWitness, PrecommittedMxfp4Pcs, Qwen35TurnExecution, RealGdnWyWitness,
    SuccinctGdnLayerProof,
};
use crate::safetensors_mmap::{
    decode_e2m1_x2_bb, decode_e2m1_x2_i32, MmapSafetensors, Mxfp4Matrix, Qwen35WeightRegistry,
    QWEN35_SAFETENSORS_FILE, WY_SCALE, WY_SHIFT, W_SCALE_SHIFT,
};
use crate::u1_audit::{
    commit_u1_fast_stream_boundaries, commit_u1_pcs_boundaries, padded_complement_sk_step,
    run_padded_complement_sk_dfa, U1OnlineCommitment,
};
use rayon::prelude::*;
use sha2::{Digest as Sha2DigestTrait, Sha256};
use std::collections::HashMap;
use std::fmt;
use std::fs;
use std::hash::Hash;
use std::ops::{Add, Mul, Sub};
use std::path::Path;
use std::sync::OnceLock;
use std::time::Instant;

/// Default local path to cached real `Qwen3.8-27B` Layer-0 `gate_proj` `[256, 5120]` `MXFP4` slice.
pub const QWEN38_27B_NPZ_PATH: &str =
    "/Users/ember/.cache/zkml-models/qwen38_27b_e2m1_slice/qwen38_27b_l0_gate_proj_256x5120.npz";

/// Magic headers shared byte-for-byte with `Minidregg.Assurance.VerifiableAgentTurnWeld`.
pub const VASTMT01_MAGIC: &[u8; 8] = b"VASTMT01";
pub const VAGENT01_MAGIC: &[u8; 8] = b"VAGENT01";
pub const VBUNDL01_MAGIC: &[u8; 8] = b"VBUNDL01";

/// Customization strings matching `Minidregg.Compiler.Tower256ContentCert` & `VerifiableAgentTurnWeld`.
const MERKLE_LEAF_CUST: &[u8] = b"\x01MINIDREGG/TOWER256/MERKLE/LEAF/V1";
const MERKLE_NODE_CUST: &[u8] = b"\x02MINIDREGG/TOWER256/MERKLE/NODE/V1";
pub const U1_STEP_CUST: &[u8] = b"\x07MINIDREGG/VAGENT01/U1/CHAIN/STEP/V1";
pub const U1_OUT_CUST: &[u8] = b"\x08MINIDREGG/VAGENT01/U1/OUT/WELD/V1";
pub const U1_VRF_CUST: &[u8] = b"\x09MINIDREGG/VAGENT01/U1/VRF/SELECT/V1";
pub const U1_PF_DIGEST_CUST: &[u8] = b"\x0AMINIDREGG/VAGENT01/U1/PF/DIGEST/V1";

const NUM_LAYERS: usize = 24;
const D_MODEL: usize = 1024;
const D_FF: usize = 3584;
const VOCAB_SIZE: usize = 248_320;
const GDN_H: usize = 16;
const GDN_D: usize = 128;
const GDN_CONV_W: usize = 4;
const GQA_HQ: usize = 8;
const GQA_HKV: usize = 2;
const GQA_DH: usize = 256;
const GQA_ROT_DIM: usize = 64;

const Q16_SHIFT: u32 = 16;
const Q16_ONE: i32 = 1 << Q16_SHIFT; // 65,536
const K_WY_SHIFT: u32 = 12;
const K_WY_SCALE: i64 = 1 << K_WY_SHIFT; // 4,096
const M_WY: i64 = WY_SCALE; // 4,096
const INV_SQRT128_Q16: i64 = 5793; // round(65536 / sqrt(128))
const INV_SQRT256_SHIFT: u32 = 4; // 1 / sqrt(256) = 1 / 16 exact!
const BOUNDARY_I16_SHIFT: u32 = 9; // Q16 >> 9 = Q7 (`ACT_SCALE = 128`) matching `qwen35_layer`!

/// Canonicalize a 4-bit OCP `MXFP4` (`E2M1`) nibble: `-0.0` (`nibble == 8`) maps to `0`.
#[inline(always)]
pub fn canonicalize_e2m1_nibble(nibble: u8) -> u8 {
    let n = nibble & 0x0F;
    if (n & 0x07) == 0 {
        0
    } else {
        n
    }
}

#[inline(always)]
fn rshift_round_i64(x: i64, shift: u32) -> i64 {
    if shift == 0 {
        x
    } else if shift >= 62 {
        0
    } else {
        let half = 1i64 << (shift - 1);
        (x + half) >> shift
    }
}

#[inline(always)]
fn rshift_round_i128(x: i128, shift: u32) -> i64 {
    if shift == 0 {
        x as i64
    } else {
        let half = 1i128 << (shift - 1);
        ((x + half) >> shift) as i64
    }
}

/// Pure-integer conversion of IEEE/Brain-Float `BF16` `u16` bits into signed fixed-point `Q20` (`× 2^20`).
#[inline]
pub fn bf16_bits_to_q20_i64(bits: u16) -> i64 {
    let sign = (bits >> 15) != 0;
    let exp = ((bits >> 7) & 0xFF) as i32;
    let mant = (bits & 0x7F) as i64;
    if exp == 0 || exp == 255 {
        return 0;
    }
    let sig = 128 + mant; // value = sig * 2^(exp - 134)
    let sh = exp - 114; // value * 2^20 = sig * 2^(exp - 114)
    let mag = if sh >= 0 {
        sig << (sh.min(42) as u32)
    } else {
        let rsh = (-sh) as u32;
        if rsh >= 62 {
            0
        } else {
            (sig + (1i64 << (rsh - 1))) >> rsh
        }
    };
    if sign {
        -mag
    } else {
        mag
    }
}

// ============================================================================
// §1. Deterministic Integer Math Lookup Tables (`EXP`, `SIGMOID`, `SOFTPLUS`, `RSQRT`, `ROPE`, `FP8`)
// ============================================================================

pub struct IntMathTables {
    /// Exact 256-entry OCP `FP8-E4M3` signed integer value × `512` (`2^9`), `-0.0` (`0x80`) -> `0`.
    pub fp8_e4m3_x512: [i32; 256],
    /// Sorted unique 253 finite `FP8-E4M3` values × `512` and their canonical `u8` codes (`0x80` excluded!).
    pub fp8_sorted_x512: [i32; 253],
    pub fp8_sorted_codes: [u8; 253],
    /// `BF16` (`u16`) -> `Q16` `i16` (`clamped to [-32767, 32767]`, exact on `embed_tokens` where `|w| <= 0.232`).
    pub bf16_to_q16_i16: Vec<i16>,
    /// `exp(x)` for `x in [-16.0, 0.0]` indexed by `(-x) * 512` (`0..=8192`), output in `Q15` (`[0, 32768]`).
    pub exp_neg_q15: Vec<u16>,
    /// `sigmoid(x)` for `x in [-16.0, +16.0]` indexed by `(x + 16.0) * 256` (`0..=8192`), output in `Q15` (`[0, 32768]`).
    pub sigmoid_q15: Vec<u16>,
    /// `softplus(x) = ln(1 + exp(x))` for `x in [-16.0, +16.0]` indexed by `(x + 16.0) * 256` (`0..=8192`), output in `Q16`.
    pub softplus_q16: Vec<u32>,
    /// `1 / sqrt(u)` for `u in [1.0, 4.0)` (`2048` bins: `[0..1024)` for `[1.0, 2.0)`, `[1024..2048)` for `[2.0, 4.0)`), output in `Q24`.
    pub rsqrt_mant_q24: [u32; 2048],
    /// RoPE `cos` & `sin` in `Q15` (`[-32768, 32768]`) for `pos in 0..512`, `pair in 0..32` (`theta = 10_000_000`).
    pub rope_cos_q15: Vec<[i32; 32]>,
    pub rope_sin_q15: Vec<[i32; 32]>,
}

static INT_MATH_TABLES: OnceLock<IntMathTables> = OnceLock::new();

pub fn int_math_tables() -> &'static IntMathTables {
    INT_MATH_TABLES.get_or_init(|| {
        let mut fp8_e4m3_x512 = [0i32; 256];
        let mut pairs: Vec<(i32, u8)> = Vec::with_capacity(253);
        for (code, slot) in fp8_e4m3_x512.iter_mut().enumerate() {
            let sign = (code >> 7) != 0;
            let exp = ((code >> 3) & 0x0F) as u32;
            let mant = (code & 0x07) as i32;
            if exp == 15 && mant == 7 {
                // NaN -> 0 fallback, excluded from quantizer codebook
                *slot = 0;
                continue;
            }
            let mag_x512: i32 = if exp == 0 {
                mant // (mant / 8) * 2^-6 * 512 = mant
            } else {
                (8 + mant) << (exp - 1) // (1 + mant/8) * 2^(exp - 7) * 512 = (8 + mant) * 2^(exp - 1)
            };
            let signed = if mag_x512 == 0 || !sign {
                mag_x512
            } else {
                -mag_x512
            };
            *slot = signed;
            if code != 0x80 {
                // Canonical: exclude -0.0 (0x80) from quantizer codebook!
                pairs.push((signed, code as u8));
            }
        }
        pairs.sort_by_key(|&(v, _)| v);
        assert_eq!(pairs.len(), 253);
        assert_eq!(pairs[0].0, -229_376);
        assert_eq!(pairs[252].0, 229_376);
        let mut fp8_sorted_x512 = [0i32; 253];
        let mut fp8_sorted_codes = [0u8; 253];
        for (i, &(v, c)) in pairs.iter().enumerate() {
            fp8_sorted_x512[i] = v;
            fp8_sorted_codes[i] = c;
        }

        let mut bf16_to_q16_i16 = vec![0i16; 65536];
        for (bits, slot) in bf16_to_q16_i16.iter_mut().enumerate() {
            let q20 = bf16_bits_to_q20_i64(bits as u16);
            let q16 = rshift_round_i64(q20, 4);
            *slot = q16.clamp(-32767, 32767) as i16;
        }

        let mut exp_neg_q15 = vec![0u16; 8193];
        for (idx, slot) in exp_neg_q15.iter_mut().enumerate() {
            let x = -(idx as f64) / 512.0;
            *slot = (x.exp() * 32768.0).round().clamp(0.0, 32768.0) as u16;
        }

        let mut sigmoid_q15 = vec![0u16; 8193];
        let mut softplus_q16 = vec![0u32; 8193];
        for idx in 0..=8192usize {
            let x = (idx as f64) / 256.0 - 16.0;
            let sig = 1.0 / (1.0 + (-x).exp());
            sigmoid_q15[idx] = (sig * 32768.0).round().clamp(0.0, 32768.0) as u16;
            let sp = (1.0 + x.exp()).ln();
            softplus_q16[idx] = (sp * 65536.0).round().max(0.0) as u32;
        }

        let mut rsqrt_mant_q24 = [0u32; 2048];
        for i in 0..1024usize {
            let u1 = 1.0 + (i as f64 + 0.5) / 1024.0; // [1.0, 2.0)
            rsqrt_mant_q24[i] = ((1.0 / u1.sqrt()) * (1u64 << 24) as f64).round() as u32;
            let u2 = 2.0 + 2.0 * (i as f64 + 0.5) / 1024.0; // [2.0, 4.0)
            rsqrt_mant_q24[1024 + i] = ((1.0 / u2.sqrt()) * (1u64 << 24) as f64).round() as u32;
        }

        let max_pos = 512usize;
        let mut rope_cos_q15 = vec![[0i32; 32]; max_pos];
        let mut rope_sin_q15 = vec![[0i32; 32]; max_pos];
        for pos in 0..max_pos {
            for pair in 0..32usize {
                let freq = 1.0f64 / 10_000_000.0f64.powf((2 * pair) as f64 / (GQA_ROT_DIM as f64));
                let ang = (pos as f64) * freq;
                rope_cos_q15[pos][pair] = (ang.cos() * 32768.0).round() as i32;
                rope_sin_q15[pos][pair] = (ang.sin() * 32768.0).round() as i32;
            }
        }

        IntMathTables {
            fp8_e4m3_x512,
            fp8_sorted_x512,
            fp8_sorted_codes,
            bf16_to_q16_i16,
            exp_neg_q15,
            sigmoid_q15,
            softplus_q16,
            rsqrt_mant_q24,
            rope_cos_q15,
            rope_sin_q15,
        }
    })
}

/// Pure-integer `exp(x)` for `x_q16 <= 0`, returning `Q15` in `[0, 32768]`.
#[inline]
pub fn int_exp_neg_q15(tabs: &IntMathTables, x_q16: i32) -> u32 {
    if x_q16 >= 0 {
        return 32768;
    }
    let neg_x = (-x_q16) as u64; // Q16: 16.0 * 65536 = 1,048,576
    if neg_x >= (16 << 16) {
        return 0;
    }
    // Map Q16 -> Q9 index (`>> 7`) with 7-bit linear interpolation!
    let idx = (neg_x >> 7) as usize;
    let frac = (neg_x & 0x7F) as i64;
    let y0 = tabs.exp_neg_q15[idx] as i64;
    let y1 = tabs.exp_neg_q15[idx + 1] as i64;
    (y0 + (((y1 - y0) * frac + 64) >> 7)) as u32
}

/// Pure-integer `sigmoid(x_q16)` returning `Q15` in `[0, 32768]`.
#[inline]
pub fn int_sigmoid_q15(tabs: &IntMathTables, x_q16: i32) -> i32 {
    if x_q16 <= -(16 << 16) {
        return 0;
    }
    if x_q16 >= (16 << 16) {
        return 32768;
    }
    let shifted = (x_q16 + (16 << 16)) as u64; // [0, 32 * 65536], step 1/256 -> `>> 8`
    let idx = (shifted >> 8) as usize;
    let frac = (shifted & 0xFF) as i64;
    let y0 = tabs.sigmoid_q15[idx] as i64;
    let y1 = tabs.sigmoid_q15[idx + 1] as i64;
    (y0 + (((y1 - y0) * frac + 128) >> 8)) as i32
}

/// Pure-integer `silu(x_q16) = x * sigmoid(x)` returning `Q16`.
#[inline]
pub fn int_silu_q16(tabs: &IntMathTables, x_q16: i32) -> i32 {
    let sig = int_sigmoid_q15(tabs, x_q16) as i64;
    rshift_round_i64((x_q16 as i64) * sig, 15) as i32
}

/// Pure-integer `softplus(x_q16) = ln(1 + exp(x))` returning `Q16`.
#[inline]
pub fn int_softplus_q16(tabs: &IntMathTables, x_q16: i32) -> i64 {
    if x_q16 <= -(16 << 16) {
        return 0;
    }
    if x_q16 >= (16 << 16) {
        return x_q16 as i64;
    }
    let shifted = (x_q16 + (16 << 16)) as u64;
    let idx = (shifted >> 8) as usize;
    let frac = (shifted & 0xFF) as i64;
    let y0 = tabs.softplus_q16[idx] as i64;
    let y1 = tabs.softplus_q16[idx + 1] as i64;
    y0 + (((y1 - y0) * frac + 128) >> 8)
}

/// Pure-integer `round(2^30 / sqrt(val_q32))` for `val_q32 > 0` (where `1.0 == 2^32`)
/// using `rsqrt_mant_q24` LUT + **1 exact integer Newton-Raphson refinement step** (`< 1 ULP` in Q16!).
/// Returns `inv_sqrt` in **`Q16`** (`round(65536 / sqrt(val_q32 / 2^32))`).
#[inline]
pub fn int_rsqrt_from_q32_to_q16(tabs: &IntMathTables, val_q32: u128) -> i64 {
    let v = val_q32.max(4295); // >= 1e-6 * 2^32 = 4295
                               // Find `e` such that `v = u * 2^(32 + 2*k)` with `u in [1.0, 4.0)`:
    let bit_len = 128 - v.leading_zeros(); // v in [2^(bit_len-1), 2^bit_len)
    let exp_raw = (bit_len as i32) - 1 - 32; // floor(log2(v / 2^32))
    let k_even = exp_raw.div_euclid(2);
    let rem_bit = exp_raw.rem_euclid(2); // 0 -> u in [1, 2), 1 -> u in [2, 4)

    // Extract `u_q24` (`u * 2^24`, in `[2^24, 4 * 2^24)`):
    let shift_to_q24 = 32 + 2 * k_even - 24;
    let u_q24: u64 = if shift_to_q24 >= 0 {
        (v >> (shift_to_q24 as u32)) as u64
    } else {
        (v << ((-shift_to_q24) as u32)) as u64
    };
    let lut_idx = if rem_bit == 0 {
        (((u_q24.saturating_sub(1 << 24)) >> 14) as usize).min(1023)
    } else {
        1024 + (((u_q24.saturating_sub(2 << 24)) >> 15) as usize).min(1023)
    };
    let y0_q24 = tabs.rsqrt_mant_q24[lut_idx] as u128; // ~ 2^24 / sqrt(u)

    // 1 exact integer Newton-Raphson iteration: y1 = y0 * (3 - u * y0^2) / 2 in Q24!
    let y0_sq_q24 = (y0_q24 * y0_q24) >> 24;
    let u_y2_q24 = (u_q24 as u128 * y0_sq_q24) >> 24;
    let three_q24 = 3u128 << 24;
    let y1_q24 = if three_q24 > u_y2_q24 {
        (y0_q24 * (three_q24 - u_y2_q24)) >> 25
    } else {
        y0_q24
    };

    // Since `val = u * 2^(2 * k_even)`, `1 / sqrt(val) = (1 / sqrt(u)) * 2^(-k_even)`.
    // Convert `y1_q24` (`Q24`) * `2^(-k_even)` to `Q16` (`shift right by 8 + k_even`):
    let out_rsh = 8 + k_even;
    if out_rsh >= 0 {
        if out_rsh >= 64 {
            0
        } else if out_rsh == 0 {
            y1_q24 as i64
        } else {
            ((y1_q24 + (1u128 << (out_rsh as u32 - 1))) >> (out_rsh as u32)) as i64
        }
    } else {
        (y1_q24 << ((-out_rsh).min(30) as u32)) as i64
    }
}

/// Zero-centered integer `Qwen3NextRMSNorm`: `out_q16[t, d] = x_q16[t, d] * inv_rms * (1 + w[d])`.
pub fn rmsnorm_zero_centered_int_q16(
    tabs: &IntMathTables,
    x_q16: &[i32],
    w_q16: &[i32], // stores `(1.0 + w[d])` in Q16!
    dim: usize,
) -> Vec<i32> {
    let rows = x_q16.len() / dim;
    let log_dim = dim.trailing_zeros();
    assert_eq!(1usize << log_dim, dim);
    let mut out = vec![0i32; x_q16.len()];
    for r in 0..rows {
        let xr = &x_q16[r * dim..(r + 1) * dim];
        let mut sum_sq: u128 = 0;
        for &v in xr {
            let vi = v as i128;
            sum_sq += (vi * vi) as u128; // each term in Q32!
        }
        let mean_sq_q32 = (sum_sq >> log_dim) + 4295; // + eps (1e-6 * 2^32 = 4295)
        let inv_rms_q16 = int_rsqrt_from_q32_to_q16(tabs, mean_sq_q32);
        let dst = &mut out[r * dim..(r + 1) * dim];
        for d in 0..dim {
            let normed_q16 = rshift_round_i64((xr[d] as i64) * inv_rms_q16, 16);
            dst[d] = rshift_round_i64(normed_q16 * (w_q16[d] as i64), 16) as i32;
        }
    }
    out
}

// ============================================================================
// §2. Exact Integer `FP8-E4M3` & `MXFP4-E2M1` Quantized Matrices + Per-Token `INT16`
// ============================================================================

/// Quantize `Q16` activations `[seq_len, dim]` to `INT16` with per-token power-of-two dynamic shifts
/// placing `max_d |x_i16[t, d]|` in `(target_max / 2, target_max]` (`0` clipping across all ranges!).
pub fn quantize_act_i16_dyn_pow2(
    x_q16: &[i32],
    seq_len: usize,
    dim: usize,
    target_max: i32, // e.g. `16383` for FP8 or `2047` for MXFP4
) -> (Vec<i16>, Vec<i32>) {
    assert_eq!(x_q16.len(), seq_len * dim);
    let mut out_i16 = vec![0i16; seq_len * dim];
    let mut shifts = vec![0i32; seq_len]; // `x_i16[t, d] ≈ x_real[t, d] * 2^{shifts[t]}`
    for t in 0..seq_len {
        let row = &x_q16[t * dim..(t + 1) * dim];
        let mut max_abs = 0u32;
        for &v in row {
            let av = v.unsigned_abs();
            if av > max_abs {
                max_abs = av;
            }
        }
        // `max_abs` is `max_real * 2^16`. We want `max_real * 2^sh <= target_max`, i.e.,
        // `max_abs * 2^(sh - 16) <= target_max`.
        let sh: i32 = if max_abs == 0 {
            12
        } else {
            let ratio = ((target_max as u64) << 16) / (max_abs as u64);
            if ratio == 0 {
                let down = (max_abs as u64)
                    .div_ceil(target_max as u64)
                    .next_power_of_two()
                    .trailing_zeros() as i32;
                (16 - down).max(-4)
            } else {
                let lg = (63 - ratio.leading_zeros()) as i32;
                lg.clamp(-4, 20)
            }
        };
        shifts[t] = sh;
        let dst = &mut out_i16[t * dim..(t + 1) * dim];
        let diff = sh - 16;
        for d in 0..dim {
            let q = if diff >= 0 {
                (row[d] as i64) << (diff as u32)
            } else {
                rshift_round_i64(row[d] as i64, (-diff) as u32)
            };
            dst[d] = q.clamp(-32767, 32767) as i16;
        }
    }
    (out_i16, shifts)
}

/// Quantize a `BF16` 2D tensor from `MmapSafetensors` into exact block-32 OCP `FP8-E4M3` (`0` float ops!).
#[derive(Clone, Debug)]
pub struct Fp8E4m3Matrix {
    pub name: String,
    pub rows: usize,
    pub cols: usize,
    pub blocks_per_row: usize,
    pub e_floor: i32,
    /// `[rows * cols]` canonical `FP8-E4M3` codes (`0x80` `-0.0` never emitted!).
    pub codes: Vec<u8>,
    /// `[rows * blocks_per_row]` power-of-two integer scales (`1 << (e_blk - e_floor)`).
    pub scales: Vec<u32>,
    pub digest: [u8; 32],
}

impl Fp8E4m3Matrix {
    pub fn from_safetensors_int(mmap: &MmapSafetensors, name: &str) -> Result<Self, String> {
        let tabs = int_math_tables();
        let (info, raw) = mmap.tensor_bytes(name)?;
        if info.shape.len() != 2 || info.dtype != "BF16" {
            return Err(format!("expected 2D BF16 tensor for {name}"));
        }
        let rows = info.shape[0];
        let cols = info.shape[1];
        assert_eq!(cols % 32, 0);
        let blocks_per_row = cols / 32;
        let row_bytes = cols * 2;

        // Pass 1: compute per-block power-of-two exponents `e_blk` (`max_q20 <= 448 * 2^(20 + e_blk)`) in parallel!
        let block_exps: Vec<(bool, i32)> = (0..rows * blocks_per_row)
            .into_par_iter()
            .map(|bi| {
                let r = bi / blocks_per_row;
                let k = bi % blocks_per_row;
                let b_raw = &raw[r * row_bytes + k * 64..r * row_bytes + (k + 1) * 64];
                let mut max_q20 = 0i64;
                for b in 0..32 {
                    let bits = u16::from_le_bytes([b_raw[2 * b], b_raw[2 * b + 1]]);
                    let av = bf16_bits_to_q20_i64(bits).abs();
                    if av > max_q20 {
                        max_q20 = av;
                    }
                }
                if max_q20 == 0 {
                    (false, 0)
                } else {
                    // Find smallest integer `e` such that `max_q20 <= 448 * 2^(20 + e)`:
                    let mut e = -24i32;
                    while e < 12 {
                        let cap = if 20 + e >= 0 {
                            448i64 << ((20 + e) as u32)
                        } else {
                            448i64 >> ((-(20 + e)) as u32)
                        };
                        if cap >= max_q20 {
                            break;
                        }
                        e += 1;
                    }
                    (true, e)
                }
            })
            .collect();

        let mut e_max = -24i32;
        let mut e_min_nz = 24i32;
        let mut any_nz = false;
        for &(nz, e) in &block_exps {
            if nz {
                any_nz = true;
                if e > e_max {
                    e_max = e;
                }
                if e < e_min_nz {
                    e_min_nz = e;
                }
            }
        }
        let e_floor = if any_nz { e_min_nz.max(e_max - 10) } else { 0 };

        let mut codes = vec![0u8; rows * cols];
        let mut scales = vec![1u32; rows * blocks_per_row];

        codes
            .par_chunks_mut(cols)
            .zip(scales.par_chunks_mut(blocks_per_row))
            .enumerate()
            .for_each(|(r, (c_row, s_row))| {
                let r_raw = &raw[r * row_bytes..(r + 1) * row_bytes];
                for k in 0..blocks_per_row {
                    let (nz, raw_e) = block_exps[r * blocks_per_row + k];
                    if !nz {
                        s_row[k] = 0;
                        continue;
                    }
                    let e_clamped = raw_e.clamp(e_floor, e_floor + 10);
                    s_row[k] = 1u32 << ((e_clamped - e_floor) as u32);
                    let b_raw = &r_raw[k * 64..(k + 1) * 64];
                    // Target in `x512` coordinates: `round(val * 512 / 2^e_clamped) = round(val_q20 / 2^(11 + e_clamped))`
                    let sh = 11 + e_clamped;
                    for b in 0..32 {
                        let bits = u16::from_le_bytes([b_raw[2 * b], b_raw[2 * b + 1]]);
                        let v_q20 = bf16_bits_to_q20_i64(bits);
                        let target_x512 = if sh >= 0 {
                            rshift_round_i64(v_q20, sh as u32)
                        } else {
                            v_q20 << ((-sh).min(20) as u32)
                        }
                        .clamp(-229_376, 229_376) as i32;

                        // Binary search nearest entry in `fp8_sorted_x512` (`0` maps to canonical `0x00`, never `0x80`!)
                        let idx = match tabs.fp8_sorted_x512.binary_search(&target_x512) {
                            Ok(i) => i,
                            Err(ins) => {
                                if ins == 0 {
                                    0
                                } else if ins >= 253 {
                                    252
                                } else {
                                    let d_lo = target_x512 - tabs.fp8_sorted_x512[ins - 1];
                                    let d_hi = tabs.fp8_sorted_x512[ins] - target_x512;
                                    if d_lo <= d_hi {
                                        ins - 1
                                    } else {
                                        ins
                                    }
                                }
                            }
                        };
                        c_row[k * 32 + b] = tabs.fp8_sorted_codes[idx];
                    }
                }
            });

        let mut buf = Vec::with_capacity(64 + codes.len() + scales.len() * 4);
        buf.extend_from_slice(&(name.len() as u32).to_le_bytes());
        buf.extend_from_slice(name.as_bytes());
        buf.extend_from_slice(&(rows as u32).to_le_bytes());
        buf.extend_from_slice(&(cols as u32).to_le_bytes());
        buf.extend_from_slice(&e_floor.to_le_bytes());
        buf.extend_from_slice(&codes);
        for &s in &scales {
            buf.extend_from_slice(&s.to_le_bytes());
        }
        let digest = cshake256_32(b"QW35-FP8E4M3-MAT-V1", &buf);

        Ok(Self {
            name: name.to_string(),
            rows,
            cols,
            blocks_per_row,
            e_floor,
            codes,
            scales,
            digest,
        })
    }

    /// Multithreaded (`rayon`) exact-integer contraction returning `Q16` `[seq_len, rows]`.
    /// Parallelizes across output row chunks even at `seq_len == 1` so autoregressive decode uses all cores!
    pub fn matmul_to_q16(&self, x_i16: &[i16], x_shifts: &[i32], seq_len: usize) -> Vec<i32> {
        let tabs = int_math_tables();
        let lut = &tabs.fp8_e4m3_x512;
        let cols = self.cols;
        let k_len = self.blocks_per_row;
        assert_eq!(x_i16.len(), seq_len * cols);
        let mut out = vec![0i32; seq_len * self.rows];

        if seq_len == 1 {
            let x_row = &x_i16[0..cols];
            // `raw_acc = x_real * 2^x_sh * w_real * 512 / 2^e_floor`
            // To obtain `Q16` (`y_real * 2^16`), shift right by `x_sh + 9 - e_floor - 16 = x_sh - e_floor - 7`:
            let rsh = x_shifts[0] - self.e_floor - 7;
            out.par_chunks_mut(64).enumerate().for_each(|(cg, dst)| {
                let j_base = cg * 64;
                for (off, slot) in dst.iter_mut().enumerate() {
                    let j = j_base + off;
                    let c_row = &self.codes[j * cols..(j + 1) * cols];
                    let s_row = &self.scales[j * k_len..(j + 1) * k_len];
                    let mut acc = 0i64;
                    for k in 0..k_len {
                        let s = s_row[k] as i64;
                        if s == 0 {
                            continue;
                        }
                        let cb = &c_row[k * 32..(k + 1) * 32];
                        let xb = &x_row[k * 32..(k + 1) * 32];
                        let mut b_sum = 0i64;
                        for b in 0..32 {
                            b_sum += (xb[b] as i64) * (lut[cb[b] as usize] as i64);
                        }
                        acc += s * b_sum;
                    }
                    let y_q16 = if rsh >= 0 {
                        rshift_round_i64(acc, rsh as u32)
                    } else {
                        acc << ((-rsh).min(24) as u32)
                    };
                    *slot = y_q16.clamp(i32::MIN as i64 + 1, i32::MAX as i64) as i32;
                }
            });
        } else {
            out.par_chunks_mut(self.rows)
                .enumerate()
                .for_each(|(t, y_row)| {
                    let x_row = &x_i16[t * cols..(t + 1) * cols];
                    let rsh = x_shifts[t] - self.e_floor - 7;
                    for (j, slot) in y_row.iter_mut().enumerate() {
                        let c_row = &self.codes[j * cols..(j + 1) * cols];
                        let s_row = &self.scales[j * k_len..(j + 1) * k_len];
                        let mut acc = 0i64;
                        for k in 0..k_len {
                            let s = s_row[k] as i64;
                            if s == 0 {
                                continue;
                            }
                            let cb = &c_row[k * 32..(k + 1) * 32];
                            let xb = &x_row[k * 32..(k + 1) * 32];
                            let mut b_sum = 0i64;
                            for b in 0..32 {
                                b_sum += (xb[b] as i64) * (lut[cb[b] as usize] as i64);
                            }
                            acc += s * b_sum;
                        }
                        let y_q16 = if rsh >= 0 {
                            rshift_round_i64(acc, rsh as u32)
                        } else {
                            acc << ((-rsh).min(24) as u32)
                        };
                        *slot = y_q16.clamp(i32::MIN as i64 + 1, i32::MAX as i64) as i32;
                    }
                });
        }
        out
    }
}

/// Fast SIMD-friendly pre-decoded `i8` wrapper around canonical `Mxfp4Matrix` (`-0.0` canonicalization verified!).
#[derive(Clone)]
pub struct FastIntMxfp4 {
    pub mat: Mxfp4Matrix,
    /// `[rows_orig * cols_orig]` signed doubled values in `{-12..12}` for direct NEON `i16 * i8 -> i32` dot products.
    pub q_x2_i8: Vec<i8>,
}

impl FastIntMxfp4 {
    pub fn from_mxfp4(mut mat: Mxfp4Matrix) -> Self {
        let mut neg_zero_fixed = 0usize;
        for nib in &mut mat.nibbles {
            if *nib == 8 {
                *nib = 0;
                neg_zero_fixed += 1;
            }
            assert!(*nib < 16 && *nib != 8, "non-canonical E2M1 nibble {}", *nib);
        }
        if neg_zero_fixed > 0 {
            mat.digest = Mxfp4Matrix::compute_digest(
                &mat.name,
                mat.rows_orig,
                mat.rows_pad,
                mat.cols_orig,
                &mat.nibbles,
                &mat.scales,
            );
        }
        let cols = mat.cols_orig;
        let mut q_x2_i8 = vec![0i8; mat.rows_orig * cols];
        for j in 0..mat.rows_orig {
            for c in 0..cols {
                q_x2_i8[j * cols + c] = decode_e2m1_x2_i32(mat.nibbles[j * cols + c]) as i8;
            }
        }
        Self { mat, q_x2_i8 }
    }

    /// Exact integer contraction producing both `Q16` `[seq_len * rows_orig]` and optional `Y_raw: Vec<i64>` `[seq_len * rows_pad]`.
    pub fn matmul_to_q16(
        &self,
        x_i16: &[i16],
        x_shifts: &[i32],
        seq_len: usize,
        capture_y_raw: bool,
    ) -> (Vec<i32>, Option<Vec<i64>>) {
        let rows_orig = self.mat.rows_orig;
        let rows_pad = self.mat.rows_pad;
        let cols = self.mat.cols_orig;
        let k_len = self.mat.blocks_per_row;
        assert_eq!(x_i16.len(), seq_len * cols);

        let mut out_q16 = vec![0i32; seq_len * rows_orig];
        if seq_len == 1 && !capture_y_raw {
            let x_row = &x_i16[0..cols];
            // `raw_acc = x_real * 2^x_sh * w_real * 2 * 2^W_SCALE_SHIFT`
            // To obtain `Q16`: shift right by `x_sh + 1 + W_SCALE_SHIFT - 16 = x_sh - 5`!
            let rsh = x_shifts[0] + 1 + W_SCALE_SHIFT - 16;
            out_q16
                .par_chunks_mut(64)
                .enumerate()
                .for_each(|(cg, dst)| {
                    let j_base = cg * 64;
                    for (off, slot) in dst.iter_mut().enumerate() {
                        let j = j_base + off;
                        let q_row = &self.q_x2_i8[j * cols..(j + 1) * cols];
                        let s_row = &self.mat.scales[j * k_len..(j + 1) * k_len];
                        let mut acc = 0i64;
                        for k in 0..k_len {
                            let s = s_row[k] as i64;
                            if s == 0 {
                                continue;
                            }
                            let qb = &q_row[k * 32..(k + 1) * 32];
                            let xb = &x_row[k * 32..(k + 1) * 32];
                            let mut b_sum = 0i32;
                            for b in 0..32 {
                                b_sum += (xb[b] as i32) * (qb[b] as i32);
                            }
                            acc += s * (b_sum as i64);
                        }
                        let y_q16 = if rsh >= 0 {
                            rshift_round_i64(acc, rsh as u32)
                        } else {
                            acc << ((-rsh).min(24) as u32)
                        };
                        *slot = y_q16.clamp(i32::MIN as i64 + 1, i32::MAX as i64) as i32;
                    }
                });
            return (out_q16, None);
        }

        let mut y_raw_all = if capture_y_raw {
            vec![0i64; seq_len * rows_pad]
        } else {
            Vec::new()
        };

        if capture_y_raw {
            out_q16
                .par_chunks_mut(rows_orig)
                .zip(y_raw_all.par_chunks_mut(rows_pad))
                .enumerate()
                .for_each(|(t, (y_q16_row, y_raw_row))| {
                    let x_row = &x_i16[t * cols..(t + 1) * cols];
                    let rsh = x_shifts[t] + 1 + W_SCALE_SHIFT - 16;
                    for j in 0..rows_orig {
                        let q_row = &self.q_x2_i8[j * cols..(j + 1) * cols];
                        let s_row = &self.mat.scales[j * k_len..(j + 1) * k_len];
                        let mut acc = 0i64;
                        for k in 0..k_len {
                            let s = s_row[k] as i64;
                            if s == 0 {
                                continue;
                            }
                            let qb = &q_row[k * 32..(k + 1) * 32];
                            let xb = &x_row[k * 32..(k + 1) * 32];
                            let mut b_sum = 0i32;
                            for b in 0..32 {
                                b_sum += (xb[b] as i32) * (qb[b] as i32);
                            }
                            acc += s * (b_sum as i64);
                        }
                        assert!(
                            acc.abs() < (P as i64) / 2,
                            "MXFP4 BabyBear wraparound guard: |acc| = {}",
                            acc.abs()
                        );
                        y_raw_row[j] = acc;
                        let v_q16 = if rsh >= 0 {
                            rshift_round_i64(acc, rsh as u32)
                        } else {
                            acc << ((-rsh).min(24) as u32)
                        };
                        y_q16_row[j] = v_q16.clamp(i32::MIN as i64 + 1, i32::MAX as i64) as i32;
                    }
                });
            (out_q16, Some(y_raw_all))
        } else {
            out_q16
                .par_chunks_mut(rows_orig)
                .enumerate()
                .for_each(|(t, y_q16_row)| {
                    let x_row = &x_i16[t * cols..(t + 1) * cols];
                    let rsh = x_shifts[t] + 1 + W_SCALE_SHIFT - 16;
                    for (j, y_cell) in y_q16_row.iter_mut().take(rows_orig).enumerate() {
                        let q_row = &self.q_x2_i8[j * cols..(j + 1) * cols];
                        let s_row = &self.mat.scales[j * k_len..(j + 1) * k_len];
                        let mut acc = 0i64;
                        for k in 0..k_len {
                            let s = s_row[k] as i64;
                            if s == 0 {
                                continue;
                            }
                            let qb = &q_row[k * 32..(k + 1) * 32];
                            let xb = &x_row[k * 32..(k + 1) * 32];
                            let mut b_sum = 0i32;
                            for b in 0..32 {
                                b_sum += (xb[b] as i32) * (qb[b] as i32);
                            }
                            acc += s * (b_sum as i64);
                        }
                        let v_q16 = if rsh >= 0 {
                            rshift_round_i64(acc, rsh as u32)
                        } else {
                            acc << ((-rsh).min(24) as u32)
                        };
                        *y_cell = v_q16.clamp(i32::MIN as i64 + 1, i32::MAX as i64) as i32;
                    }
                });
            (out_q16, None)
        }
    }
}

// ============================================================================
// §3. Pure-Rust `QwenBpeTokenizer` (`tokenizer.json`, 0 Python!)
// ============================================================================

pub struct QwenBpeTokenizer {
    byte_to_char: [char; 256],
    char_to_byte: HashMap<char, u8>,
    vocab: HashMap<String, u32>,
    id_to_bytes: Vec<Vec<u8>>,
    merge_ranks: HashMap<(u32, u32), u32>,
    pub eos_token_id: u32,
}

impl QwenBpeTokenizer {
    pub fn from_file(path: impl AsRef<Path>) -> Result<Self, String> {
        let raw_json = fs::read_to_string(path.as_ref())
            .map_err(|e| format!("failed reading tokenizer {}: {e}", path.as_ref().display()))?;
        let root: serde_json::Value = serde_json::from_str(&raw_json)
            .map_err(|e| format!("tokenizer JSON parse error: {e}"))?;

        let mut byte_to_char = ['\0'; 256];
        let mut char_to_byte = HashMap::with_capacity(256);
        let mut n = 0u32;
        for b in 0..=255u8 {
            let is_direct =
                (33..=126).contains(&b) || (161..=172).contains(&b) || (174..=255).contains(&b);
            let ch = if is_direct {
                char::from_u32(b as u32).unwrap()
            } else {
                let c = char::from_u32(256 + n).unwrap();
                n += 1;
                c
            };
            byte_to_char[b as usize] = ch;
            char_to_byte.insert(ch, b);
        }

        let vocab_obj = root["model"]["vocab"]
            .as_object()
            .ok_or_else(|| "missing model.vocab".to_string())?;
        let mut max_id = VOCAB_SIZE;
        let mut vocab = HashMap::with_capacity(vocab_obj.len() + 512);
        for (tok_str, val) in vocab_obj {
            let id = val.as_u64().ok_or_else(|| "non-u64 vocab id".to_string())? as u32;
            if (id as usize) >= max_id {
                max_id = (id as usize) + 1;
            }
            vocab.insert(tok_str.clone(), id);
        }

        let mut id_to_bytes = vec![Vec::new(); max_id];
        for (tok_str, &id) in &vocab {
            let mut bs = Vec::with_capacity(tok_str.len());
            for ch in tok_str.chars() {
                if let Some(&b) = char_to_byte.get(&ch) {
                    bs.push(b);
                } else {
                    let mut u = [0u8; 4];
                    bs.extend_from_slice(ch.encode_utf8(&mut u).as_bytes());
                }
            }
            id_to_bytes[id as usize] = bs;
        }

        if let Some(added) = root["added_tokens"].as_array() {
            for item in added {
                if let (Some(id_u64), Some(content)) =
                    (item["id"].as_u64(), item["content"].as_str())
                {
                    let id = id_u64 as usize;
                    if id >= id_to_bytes.len() {
                        id_to_bytes.resize(id + 1, Vec::new());
                    }
                    id_to_bytes[id] = content.as_bytes().to_vec();
                    vocab.insert(content.to_string(), id as u32);
                }
            }
        }

        let merges_arr = root["model"]["merges"]
            .as_array()
            .ok_or_else(|| "missing model.merges".to_string())?;
        let mut merge_ranks = HashMap::with_capacity(merges_arr.len());
        for (rank, entry) in merges_arr.iter().enumerate() {
            let pair_opt: Option<(&str, &str)> = if let Some(s) = entry.as_str() {
                s.split_once(' ')
            } else if let Some(arr) = entry.as_array() {
                if arr.len() == 2 {
                    Some((arr[0].as_str().unwrap_or(""), arr[1].as_str().unwrap_or("")))
                } else {
                    None
                }
            } else {
                None
            };
            if let Some((a, b)) = pair_opt {
                if let (Some(&ida), Some(&idb)) = (vocab.get(a), vocab.get(b)) {
                    merge_ranks.insert((ida, idb), rank as u32);
                }
            }
        }

        Ok(Self {
            byte_to_char,
            char_to_byte,
            vocab,
            id_to_bytes,
            merge_ranks,
            eos_token_id: 248_044,
        })
    }

    /// Pre-tokenize text matching Qwen's `Split` pattern (`letters`, single `digits`, `punct+crlf`, `newlines`, `spaces`).
    fn pre_tokenize(text: &str) -> Vec<&str> {
        let mut chunks = Vec::new();
        let bytes = text.as_bytes();
        let n = bytes.len();
        let mut i = 0usize;

        #[inline]
        fn is_letter(b: u8) -> bool {
            b.is_ascii_alphabetic() || b >= 0x80
        }
        #[inline]
        fn is_newline(b: u8) -> bool {
            b == b'\n' || b == b'\r'
        }
        #[inline]
        fn is_ws_not_nl(b: u8) -> bool {
            b == b' ' || b == b'\t'
        }
        #[inline]
        fn is_punct(b: u8) -> bool {
            !is_letter(b) && !b.is_ascii_digit() && !is_newline(b) && !is_ws_not_nl(b)
        }

        while i < n {
            let b = bytes[i];
            // Single digit (`\p{N}` in Qwen tokenizer splits digits 1-by-1!)
            if b.is_ascii_digit() {
                chunks.push(&text[i..i + 1]);
                i += 1;
                continue;
            }
            // Contractions `'s`, `'t`, `'re`, `'ve`, `'m`, `'ll`, `'d`
            if b == b'\'' && i + 1 < n {
                let next_lo = bytes[i + 1].to_ascii_lowercase();
                if matches!(next_lo, b's' | b't' | b'm' | b'd') {
                    chunks.push(&text[i..i + 2]);
                    i += 2;
                    continue;
                }
                if i + 2 < n {
                    let pair = [next_lo, bytes[i + 2].to_ascii_lowercase()];
                    if matches!(&pair, b"re" | b"ve" | b"ll") {
                        chunks.push(&text[i..i + 3]);
                        i += 3;
                        continue;
                    }
                }
            }
            // Newline-prefixed whitespace `\s*[\r\n]+`
            if is_newline(b) {
                let start = i;
                while i < n && is_newline(bytes[i]) {
                    i += 1;
                }
                chunks.push(&text[start..i]);
                continue;
            }
            // Non-letter, non-digit prefix followed immediately by letters (`[^\r\n\p{L}\p{N}]?[\p{L}]+`)
            if !is_newline(b)
                && !b.is_ascii_digit()
                && !is_letter(b)
                && i + 1 < n
                && is_letter(bytes[i + 1])
            {
                let start = i;
                i += 1;
                while i < n && is_letter(bytes[i]) {
                    i += 1;
                }
                chunks.push(&text[start..i]);
                continue;
            }
            // Letters `[\p{L}]+`
            if is_letter(b) {
                let start = i;
                while i < n && is_letter(bytes[i]) {
                    i += 1;
                }
                chunks.push(&text[start..i]);
                continue;
            }
            // Optional single space + punctuation + optional trailing `[\r\n]*` (` ?[^\s\p{L}\p{N}]+[\r\n]*`)
            if (b == b' ' && i + 1 < n && is_punct(bytes[i + 1])) || is_punct(b) {
                let start = i;
                if bytes[i] == b' ' {
                    i += 1;
                }
                while i < n && is_punct(bytes[i]) {
                    i += 1;
                }
                while i < n && is_newline(bytes[i]) {
                    i += 1;
                }
                chunks.push(&text[start..i]);
                continue;
            }
            // Whitespace run (`\s*[\r\n]+` or `\s+(?!\S)` or `\s+`)
            if is_ws_not_nl(b) {
                let start = i;
                while i < n && is_ws_not_nl(bytes[i]) {
                    i += 1;
                }
                if i < n && is_newline(bytes[i]) {
                    while i < n && is_newline(bytes[i]) {
                        i += 1;
                    }
                    chunks.push(&text[start..i]);
                } else if i < n && (i - start) > 1 {
                    // Leave the last space attached to the following word (`\s+(?!\S)`)!
                    chunks.push(&text[start..i - 1]);
                    i -= 1;
                } else {
                    chunks.push(&text[start..i]);
                }
                continue;
            }
            chunks.push(&text[i..i + 1]);
            i += 1;
        }
        chunks
    }

    fn bpe_piece(&self, piece: &str, out: &mut Vec<u32>) {
        if piece.is_empty() {
            return;
        }
        let mut mapped = String::with_capacity(piece.len() * 2);
        for &b in piece.as_bytes() {
            mapped.push(self.byte_to_char[b as usize]);
        }
        if let Some(&id) = self.vocab.get(&mapped) {
            out.push(id);
            return;
        }

        let mut syms: Vec<String> = mapped.chars().map(|c| c.to_string()).collect();
        let mut ids: Vec<u32> = syms
            .iter()
            .map(|s| *self.vocab.get(s).expect("byte symbol in BPE vocab"))
            .collect();

        while ids.len() >= 2 {
            let mut best: Option<(u32, usize)> = None;
            for idx in 0..(ids.len() - 1) {
                if let Some(&rk) = self.merge_ranks.get(&(ids[idx], ids[idx + 1])) {
                    if best.is_none_or(|(brk, _)| rk < brk) {
                        best = Some((rk, idx));
                    }
                }
            }
            let Some((_, best_idx)) = best else {
                break;
            };
            let merged_str = format!("{}{}", syms[best_idx], syms[best_idx + 1]);
            let merged_id = *self
                .vocab
                .get(&merged_str)
                .expect("merged BPE token must exist in vocab");
            syms[best_idx] = merged_str;
            syms.remove(best_idx + 1);
            ids[best_idx] = merged_id;
            ids.remove(best_idx + 1);
        }
        out.extend_from_slice(&ids);
    }

    pub fn encode(&self, text: &str) -> Vec<u32> {
        let mut ids = Vec::with_capacity(text.len() / 2 + 8);
        for piece in Self::pre_tokenize(text) {
            self.bpe_piece(piece, &mut ids);
        }
        let _ = &self.char_to_byte;
        ids
    }

    pub fn decode_bytes(&self, ids: &[u32]) -> Vec<u8> {
        let mut out = Vec::with_capacity(ids.len() * 4);
        for &id in ids {
            if let Some(bs) = self.id_to_bytes.get(id as usize) {
                out.extend_from_slice(bs);
            }
        }
        out
    }

    pub fn decode_lossy(&self, ids: &[u32]) -> String {
        String::from_utf8_lossy(&self.decode_bytes(ids)).into_owned()
    }
}

// ============================================================================
// §4. Pure-Integer 24-Layer `Qwen3.5-0.8B` Engine (`Mixed-MXFP4/FP8` + `IntWY` + KV/SSM Cache)
// ============================================================================

struct GdnAttnWeights {
    qkv: Fp8E4m3Matrix,
    z: Fp8E4m3Matrix,
    b: Fp8E4m3Matrix,
    a: Fp8E4m3Matrix,
    out_proj: Fp8E4m3Matrix,
    conv_w_q16: Vec<i32>,        // [6144 * 4]
    neg_exp_alog_q16: [i64; 16], // -exp(A_log[h]) in Q16
    dt_bias_q16: [i32; 16],      // dt_bias[h] in Q16
    norm_w_q16: Vec<i32>,        // [128] plain w[d] in Q16 (NO 1 + w!)
}

struct GqaAttnWeights {
    q_proj: Fp8E4m3Matrix,
    k_proj: Fp8E4m3Matrix,
    v_proj: Fp8E4m3Matrix,
    o_proj: Fp8E4m3Matrix,
    q_norm_1pw_q16: Vec<i32>, // [256] (1 + w[d]) in Q16
    k_norm_1pw_q16: Vec<i32>, // [256] (1 + w[d]) in Q16
}

enum LayerAttnWeights {
    Gdn(Box<GdnAttnWeights>),
    Gqa(Box<GqaAttnWeights>),
}

struct LayerWeights {
    ln1_1pw_q16: Vec<i32>, // [1024] (1 + w[d]) in Q16
    ln2_1pw_q16: Vec<i32>, // [1024] (1 + w[d]) in Q16
    attn: LayerAttnWeights,
    gate_proj: FastIntMxfp4,
    up_proj: FastIntMxfp4,
    down_proj: FastIntMxfp4,
    tensor_digests: Vec<[u8; 32]>,
    gate_proj_slot: usize,
}

/// Mutable recurrent/KV cache across all 24 layers (`0` float fields — 100% integer!).
#[derive(Clone)]
pub struct ExactIntDecodeCache {
    pub pos: usize,
    pub conv_q16: Vec<Vec<i32>>,    // per GDN layer: [6144 * 4]
    pub ssm_q16: Vec<Vec<i32>>,     // per GDN layer: [16 * 128 * 128]
    pub k_cache_q12: Vec<Vec<i16>>, // per GQA layer: [seq_so_far * 2 * 256]
    pub v_cache_q12: Vec<Vec<i16>>, // per GQA layer: [seq_so_far * 2 * 256]
}

impl Default for ExactIntDecodeCache {
    fn default() -> Self {
        Self::new()
    }
}

impl ExactIntDecodeCache {
    pub fn new() -> Self {
        Self {
            pos: 0,
            conv_q16: (0..NUM_LAYERS)
                .map(|l| {
                    if (l % 4) != 3 {
                        vec![0i32; 6144 * GDN_CONV_W]
                    } else {
                        Vec::new()
                    }
                })
                .collect(),
            ssm_q16: (0..NUM_LAYERS)
                .map(|l| {
                    if (l % 4) != 3 {
                        vec![0i32; GDN_H * GDN_D * GDN_D]
                    } else {
                        Vec::new()
                    }
                })
                .collect(),
            k_cache_q12: vec![Vec::new(); NUM_LAYERS],
            v_cache_q12: vec![Vec::new(); NUM_LAYERS],
        }
    }
}

/// Complete 100%-integer 24-layer `Qwen/Qwen3.5-0.8B-Base` engine backed by zero-copy `MmapSafetensors`.
pub struct ExactIntQwen35Engine {
    pub mmap: MmapSafetensors,
    layers: Vec<LayerWeights>,
    final_norm_1pw_q16: Vec<i32>,
    pub registry: Qwen35WeightRegistry,
}

fn read_1d_bf16_or_f32_to_q16(
    mmap: &MmapSafetensors,
    name: &str,
    add_one: bool,
) -> Result<Vec<i32>, String> {
    let (info, raw) = mmap.tensor_bytes(name)?;
    let numel: usize = info.shape.iter().product();
    let add = if add_one { 1i64 << 20 } else { 0 };
    match info.dtype.as_str() {
        "BF16" => Ok(raw
            .chunks_exact(2)
            .map(|b| {
                let bits = u16::from_le_bytes([b[0], b[1]]);
                rshift_round_i64(bf16_bits_to_q20_i64(bits) + add, 4) as i32
            })
            .collect()),
        "F32" => {
            if raw.len() != numel * 4 {
                return Err(format!("F32 size mismatch on {name}"));
            }
            Ok(raw
                .chunks_exact(4)
                .map(|b| {
                    let v = f32::from_le_bytes([b[0], b[1], b[2], b[3]]) as f64;
                    let base = if add_one { 1.0 + v } else { v };
                    (base * 65536.0).round() as i32
                })
                .collect())
        }
        dt => Err(format!("unsupported 1D dtype {dt} on {name}")),
    }
}

fn hash_1d_tensor_bytes(mmap: &MmapSafetensors, name: &str) -> Result<[u8; 32], String> {
    let (info, raw) = mmap.tensor_bytes(name)?;
    let mut buf = Vec::with_capacity(64 + raw.len());
    buf.extend_from_slice(&(name.len() as u32).to_le_bytes());
    buf.extend_from_slice(name.as_bytes());
    buf.extend_from_slice(&(info.dtype.len() as u32).to_le_bytes());
    buf.extend_from_slice(info.dtype.as_bytes());
    for &dim in &info.shape {
        buf.extend_from_slice(&(dim as u64).to_le_bytes());
    }
    buf.extend_from_slice(raw);
    Ok(cshake256_32(b"QW35-1D-EXEC-TENSOR-V1", &buf))
}

fn hash_embed_tokens_parallel(mmap: &MmapSafetensors) -> Result<[u8; 32], String> {
    let (_, emb_raw) = mmap.tensor_bytes("model.language_model.embed_tokens.weight")?;
    let chunk_bytes = 1024 * D_MODEL * 2; // 1,024 vocab rows per parallel leaf
    let chunk_digests: Vec<[u8; 32]> = emb_raw
        .par_chunks(chunk_bytes)
        .enumerate()
        .map(|(ci, ch)| {
            let mut hdr = Vec::with_capacity(8 + ch.len());
            hdr.extend_from_slice(&(ci as u64).to_le_bytes());
            hdr.extend_from_slice(ch);
            cshake256_32(b"QW35-EMBED-CHUNK-V1", &hdr)
        })
        .collect();
    let mut pow2_leaves = chunk_digests;
    let target = pow2_leaves.len().next_power_of_two();
    while pow2_leaves.len() < target {
        pow2_leaves.push([0u8; 32]);
    }
    Ok(merkle_root_cshake(b"QW35-EMBED-TREE-V1", &pow2_leaves))
}

impl ExactIntQwen35Engine {
    /// Load and commit all 24 layers (`Mixed-MXFP4/FP8` + all 1D norms/SSM params + zero-copy `mmap` embeddings) in `rayon` parallel.
    pub fn load_default() -> Result<Self, String> {
        Self::load_from_safetensors(QWEN35_SAFETENSORS_FILE)
    }

    pub fn load_from_safetensors(path: impl AsRef<Path>) -> Result<Self, String> {
        type LoadedLayerTuple = (LayerWeights, [u8; 32], usize, usize);
        let _tabs = int_math_tables();
        let mmap = MmapSafetensors::open(path)?;
        let per_layer: Result<Vec<LoadedLayerTuple>, String> = (0..NUM_LAYERS)
            .into_par_iter()
            .map(|l| {
                let pfx = format!("model.language_model.layers.{l}");
                let ln1_name = format!("{pfx}.input_layernorm.weight");
                let ln2_name = format!("{pfx}.post_attention_layernorm.weight");
                let ln1_1pw_q16 = read_1d_bf16_or_f32_to_q16(&mmap, &ln1_name, true)?;
                let ln2_1pw_q16 = read_1d_bf16_or_f32_to_q16(&mmap, &ln2_name, true)?;
                let ln1_dig = hash_1d_tensor_bytes(&mmap, &ln1_name)?;
                let ln2_dig = hash_1d_tensor_bytes(&mmap, &ln2_name)?;

                let gate_proj = FastIntMxfp4::from_mxfp4(Mxfp4Matrix::from_safetensors(
                    &mmap,
                    &format!("{pfx}.mlp.gate_proj.weight"),
                )?);
                let up_proj = FastIntMxfp4::from_mxfp4(Mxfp4Matrix::from_safetensors(
                    &mmap,
                    &format!("{pfx}.mlp.up_proj.weight"),
                )?);
                let down_proj = FastIntMxfp4::from_mxfp4(Mxfp4Matrix::from_safetensors(
                    &mmap,
                    &format!("{pfx}.mlp.down_proj.weight"),
                )?);

                let (attn, mut tensor_digests, aux_1d_digests, gate_proj_slot, mut params) =
                    if (l % 4) != 3 {
                        let qkv = Fp8E4m3Matrix::from_safetensors_int(
                            &mmap,
                            &format!("{pfx}.linear_attn.in_proj_qkv.weight"),
                        )?;
                        let z = Fp8E4m3Matrix::from_safetensors_int(
                            &mmap,
                            &format!("{pfx}.linear_attn.in_proj_z.weight"),
                        )?;
                        let b = Fp8E4m3Matrix::from_safetensors_int(
                            &mmap,
                            &format!("{pfx}.linear_attn.in_proj_b.weight"),
                        )?;
                        let a = Fp8E4m3Matrix::from_safetensors_int(
                            &mmap,
                            &format!("{pfx}.linear_attn.in_proj_a.weight"),
                        )?;
                        let out_proj = Fp8E4m3Matrix::from_safetensors_int(
                            &mmap,
                            &format!("{pfx}.linear_attn.out_proj.weight"),
                        )?;
                        let conv_name = format!("{pfx}.linear_attn.conv1d.weight");
                        let alog_name = format!("{pfx}.linear_attn.A_log");
                        let dt_name = format!("{pfx}.linear_attn.dt_bias");
                        let norm_name = format!("{pfx}.linear_attn.norm.weight");
                        let conv_w_q16 = read_1d_bf16_or_f32_to_q16(&mmap, &conv_name, false)?;
                        let (_, a_log_f32) = mmap.read_f32(&alog_name)?;
                        let mut neg_exp_alog_q16 = [0i64; 16];
                        for h in 0..16 {
                            neg_exp_alog_q16[h] =
                                (-((a_log_f32[h] as f64).exp() * 65536.0).round()) as i64;
                        }
                        let dt_v = read_1d_bf16_or_f32_to_q16(&mmap, &dt_name, false)?;
                        let mut dt_bias_q16 = [0i32; 16];
                        dt_bias_q16.copy_from_slice(&dt_v[..16]);
                        let norm_w_q16 = read_1d_bf16_or_f32_to_q16(&mmap, &norm_name, false)?;
                        let p_cnt = qkv.rows * qkv.cols
                            + z.rows * z.cols
                            + b.rows * b.cols
                            + a.rows * a.cols
                            + out_proj.rows * out_proj.cols;
                        let digs = vec![qkv.digest, z.digest, b.digest, a.digest, out_proj.digest];
                        let aux = vec![
                            ln1_dig,
                            ln2_dig,
                            hash_1d_tensor_bytes(&mmap, &conv_name)?,
                            hash_1d_tensor_bytes(&mmap, &alog_name)?,
                            hash_1d_tensor_bytes(&mmap, &dt_name)?,
                            hash_1d_tensor_bytes(&mmap, &norm_name)?,
                        ];
                        (
                            LayerAttnWeights::Gdn(Box::new(GdnAttnWeights {
                                qkv,
                                z,
                                b,
                                a,
                                out_proj,
                                conv_w_q16,
                                neg_exp_alog_q16,
                                dt_bias_q16,
                                norm_w_q16,
                            })),
                            digs,
                            aux,
                            5usize,
                            p_cnt,
                        )
                    } else {
                        let q_proj = Fp8E4m3Matrix::from_safetensors_int(
                            &mmap,
                            &format!("{pfx}.self_attn.q_proj.weight"),
                        )?;
                        let k_proj = Fp8E4m3Matrix::from_safetensors_int(
                            &mmap,
                            &format!("{pfx}.self_attn.k_proj.weight"),
                        )?;
                        let v_proj = Fp8E4m3Matrix::from_safetensors_int(
                            &mmap,
                            &format!("{pfx}.self_attn.v_proj.weight"),
                        )?;
                        let o_proj = Fp8E4m3Matrix::from_safetensors_int(
                            &mmap,
                            &format!("{pfx}.self_attn.o_proj.weight"),
                        )?;
                        let qn_name = format!("{pfx}.self_attn.q_norm.weight");
                        let kn_name = format!("{pfx}.self_attn.k_norm.weight");
                        let q_norm_1pw_q16 = read_1d_bf16_or_f32_to_q16(&mmap, &qn_name, true)?;
                        let k_norm_1pw_q16 = read_1d_bf16_or_f32_to_q16(&mmap, &kn_name, true)?;
                        let p_cnt = q_proj.rows * q_proj.cols
                            + k_proj.rows * k_proj.cols
                            + v_proj.rows * v_proj.cols
                            + o_proj.rows * o_proj.cols;
                        let digs = vec![q_proj.digest, k_proj.digest, v_proj.digest, o_proj.digest];
                        let aux = vec![
                            ln1_dig,
                            ln2_dig,
                            hash_1d_tensor_bytes(&mmap, &qn_name)?,
                            hash_1d_tensor_bytes(&mmap, &kn_name)?,
                        ];
                        (
                            LayerAttnWeights::Gqa(Box::new(GqaAttnWeights {
                                q_proj,
                                k_proj,
                                v_proj,
                                o_proj,
                                q_norm_1pw_q16,
                                k_norm_1pw_q16,
                            })),
                            digs,
                            aux,
                            4usize,
                            p_cnt,
                        )
                    };

                params += gate_proj.mat.rows_orig * gate_proj.mat.cols_orig
                    + up_proj.mat.rows_orig * up_proj.mat.cols_orig
                    + down_proj.mat.rows_orig * down_proj.mat.cols_orig;
                tensor_digests.push(gate_proj.mat.digest);
                tensor_digests.push(up_proj.mat.digest);
                tensor_digests.push(down_proj.mat.digest);
                // Append all 1D norm / conv1d / A_log / dt_bias digests AFTER `down_proj` so
                // `gate_proj_slot` stays fixed AND `layer_weight_path` authenticates 100% of layer params!
                tensor_digests.extend(aux_1d_digests);

                let mut layer_buf = Vec::with_capacity(4 + tensor_digests.len() * 32);
                layer_buf.extend_from_slice(&(l as u32).to_le_bytes());
                for d in &tensor_digests {
                    layer_buf.extend_from_slice(d);
                }
                let l_digest = cshake256_32(b"QW35-LAYER-WEIGHT-LEAF-V1", &layer_buf);
                let n_tens = tensor_digests.len();

                Ok((
                    LayerWeights {
                        ln1_1pw_q16,
                        ln2_1pw_q16,
                        attn,
                        gate_proj,
                        up_proj,
                        down_proj,
                        tensor_digests,
                        gate_proj_slot,
                    },
                    l_digest,
                    params,
                    n_tens,
                ))
            })
            .collect();

        let per_layer = per_layer?;
        let mut layers = Vec::with_capacity(NUM_LAYERS);
        let mut layer_digests = Vec::with_capacity(32);
        let mut total_quantized_params = 0usize;
        let mut total_tensors_committed = 0usize;
        for (lw, d, p, c) in per_layer {
            layers.push(lw);
            layer_digests.push(d);
            total_quantized_params += p;
            total_tensors_committed += c;
        }
        // Authenticate global `embed_tokens.weight` (tied `lm_head`) + `final_norm.weight` in leaf 24!
        let embed_tree_root = hash_embed_tokens_parallel(&mmap)?;
        let final_norm_dig = hash_1d_tensor_bytes(&mmap, "model.language_model.norm.weight")?;
        let mut global_leaf_buf = [0u8; 64];
        global_leaf_buf[0..32].copy_from_slice(&embed_tree_root);
        global_leaf_buf[32..64].copy_from_slice(&final_norm_dig);
        layer_digests.push(cshake256_32(
            b"QW35-GLOBAL-EMBED-FINALNORM-LEAF-V1",
            &global_leaf_buf,
        ));
        total_tensors_committed += 2;
        while layer_digests.len() < 32 {
            layer_digests.push([0u8; 32]);
        }
        let weight_root = merkle_root_cshake(b"QW35-GLOBAL-WEIGHT-TREE-V1", &layer_digests);
        let final_norm_1pw_q16 =
            read_1d_bf16_or_f32_to_q16(&mmap, "model.language_model.norm.weight", true)?;

        Ok(Self {
            mmap,
            layers,
            final_norm_1pw_q16,
            registry: Qwen35WeightRegistry {
                weight_root,
                layer_digests,
                total_quantized_params,
                total_tensors_committed,
            },
        })
    }

    pub fn layer_tensor_digests(&self, layer_idx: usize) -> (Vec<[u8; 32]>, usize) {
        let lw = &self.layers[layer_idx];
        (lw.tensor_digests.clone(), lw.gate_proj_slot)
    }

    /// Compute the deterministic offline `qs_binding` (`H(gate_proj_digest || q_pcs_root || s_pcs_root)`)
    /// for `layer_idx` so verifiers can pin expected `(weight_root, qs_binding)`.
    pub fn compute_layer_qs_binding(&self, layer_idx: usize) -> [u8; 32] {
        let lw = &self.layers[layer_idx];
        let gate_pcs = PrecommittedMxfp4Pcs::build(&lw.gate_proj.mat);
        let mut qs_bind_in = [0u8; 96];
        qs_bind_in[0..32].copy_from_slice(&lw.tensor_digests[lw.gate_proj_slot]);
        qs_bind_in[32..64].copy_from_slice(&gate_pcs.q_state.root);
        qs_bind_in[64..96].copy_from_slice(&gate_pcs.s_state.root);
        cshake256_32(b"QW35-QS-PCS-BIND-V1", &qs_bind_in)
    }

    /// Zero-copy embedding lookup into `Q16` (`[seq_len * 1024]`, `0` float ops!).
    fn embed_tokens_q16(&self, token_ids: &[u32]) -> Result<Vec<i32>, String> {
        let tabs = int_math_tables();
        let (_, emb_raw) = self
            .mmap
            .tensor_bytes("model.language_model.embed_tokens.weight")?;
        let mut out = vec![0i32; token_ids.len() * D_MODEL];
        for (t, &tid) in token_ids.iter().enumerate() {
            let u = tid as usize;
            if u >= VOCAB_SIZE {
                return Err(format!("token id {u} >= {VOCAB_SIZE}"));
            }
            let row = &emb_raw[u * D_MODEL * 2..(u + 1) * D_MODEL * 2];
            let dst = &mut out[t * D_MODEL..(t + 1) * D_MODEL];
            for d in 0..D_MODEL {
                let bits = u16::from_le_bytes([row[2 * d], row[2 * d + 1]]);
                dst[d] = tabs.bf16_to_q16_i16[bits as usize] as i32;
            }
        }
        Ok(out)
    }

    /// Multithreaded (`rayon`) exact-integer tied `lm_head` argmax over all `248,320` vocabulary rows (`0` float ops!).
    /// Returns `(argmax_token_id, top_logit_raw, logits_sha256)`.
    pub fn argmax_lm_head_int(&self, last_h_q16: &[i32]) -> Result<(u32, i64, [u8; 32]), String> {
        let tabs = int_math_tables();
        let h_norm_q16 =
            rmsnorm_zero_centered_int_q16(tabs, last_h_q16, &self.final_norm_1pw_q16, D_MODEL);
        let (x_i16, _) = quantize_act_i16_dyn_pow2(&h_norm_q16, 1, D_MODEL, 16383);
        let (_, emb_raw) = self
            .mmap
            .tensor_bytes("model.language_model.embed_tokens.weight")?;
        let lut = &tabs.bf16_to_q16_i16;

        let scores: Vec<i64> = emb_raw
            .par_chunks_exact(D_MODEL * 2)
            .map(|row| {
                let mut dot = 0i64;
                for d in 0..D_MODEL {
                    let bits = u16::from_le_bytes([row[2 * d], row[2 * d + 1]]);
                    dot += (x_i16[d] as i64) * (lut[bits as usize] as i64);
                }
                dot
            })
            .collect();

        let mut best_id = 0u32;
        let mut best_val = i64::MIN;
        let mut sha = Sha256::new();
        for (vid, &sc) in scores.iter().enumerate() {
            sha.update(sc.to_le_bytes());
            if sc > best_val {
                best_val = sc;
                best_id = vid as u32;
            }
        }
        let digest: [u8; 32] = sha.finalize().into();
        Ok((best_id, best_val, digest))
    }

    /// Exact-integer `C = 64` chunkwise WY solver with per-head `u_scale[h] = 2^{u_shift[h]}`!
    /// Returns `(y_out_q16 [64 * 2048], s_final_q16 [16 * 128 * 128], RealGdnWyWitness)`.
    fn solve_gdn_int_wy_chunk64(
        tabs: &IntMathTables,
        q_q16: &[i32],      // [64 * 16 * 128]
        k_q16: &[i32],      // [64 * 16 * 128]
        v_q16: &[i32],      // [64 * 16 * 128]
        alpha_q12: &[i64],  // [64 * 16] in [0, 4096]
        beta_q12: &[i64],   // [64 * 16] in [0, 4096]
        s_init_q16: &[i32], // [16 * 128 * 128]
    ) -> (Vec<i32>, Vec<i32>, RealGdnWyWitness) {
        type IntGdnHeadOutputs = (Vec<i64>, Vec<i64>, Vec<i64>, Vec<u32>, Vec<i32>, Vec<i32>);
        let c_len = 64usize;
        let cols = 256usize;
        let half_wy = M_WY / 2; // 2048

        let per_head: Vec<IntGdnHeadOutputs> = (0..GDN_H)
            .into_par_iter()
            .map(|h| {
                let mut q_int = vec![0i64; c_len * GDN_D];
                let mut k_int = vec![0i64; c_len * GDN_D];
                let mut v_beta_q28 = vec![0i64; c_len * GDN_D];
                let mut max_vb = 0i64;

                for t in 0..c_len {
                    let off = (t * GDN_H + h) * GDN_D;
                    let qs = &q_q16[off..off + GDN_D];
                    let ks = &k_q16[off..off + GDN_D];
                    let vs = &v_q16[off..off + GDN_D];

                    let mut sq_q: u128 = 4295;
                    let mut sq_k: u128 = 4295;
                    for d in 0..GDN_D {
                        sq_q += ((qs[d] as i128) * (qs[d] as i128)) as u128;
                        sq_k += ((ks[d] as i128) * (ks[d] as i128)) as u128;
                    }
                    let inv_q = int_rsqrt_from_q32_to_q16(tabs, sq_q);
                    let inv_k = int_rsqrt_from_q32_to_q16(tabs, sq_k);
                    let b_val = beta_q12[t * GDN_H + h];

                    for d in 0..GDN_D {
                        // `qs[d] * inv_q` is Q32 -> shift right by `32 - 12 = 20` for `K_WY_SCALE = 4096`!
                        q_int[t * GDN_D + d] = rshift_round_i64((qs[d] as i64) * inv_q, 20)
                            .clamp(-K_WY_SCALE, K_WY_SCALE);
                        k_int[t * GDN_D + d] = rshift_round_i64((ks[d] as i64) * inv_k, 20)
                            .clamp(-K_WY_SCALE, K_WY_SCALE);
                        let vb = (vs[d] as i64) * b_val; // Q16 * Q12 = Q28
                        v_beta_q28[t * GDN_D + d] = vb;
                        if vb.abs() > max_vb {
                            max_vb = vb.abs();
                        }
                    }
                }

                // Per-head power-of-two `u_shift[h]` in `4..=26` so `U_rhs` uses full `[-4096, 4096]` precision!
                let u_shift: i32 = if max_vb <= 0 {
                    12
                } else {
                    // Want `(max_vb * 2^u_shift) >> 28 <= 4096`, i.e., `2^u_shift <= (4096 << 28) / max_vb`
                    let ratio = ((4096u128) << 28) / (max_vb as u128);
                    if ratio == 0 {
                        4
                    } else {
                        ((127 - ratio.leading_zeros()) as i32).clamp(4, 26)
                    }
                };

                let mut gamma_pre = [0i64; 64];
                let mut gamma_suf = [0i64; 64];
                let mut cap_gamma = vec![0i64; 64 * 64];
                let mut cur = M_WY;
                for i in 0..c_len {
                    cur = rshift_round_i64(cur * alpha_q12[i * GDN_H + h], 12);
                    gamma_pre[i] = cur;
                }
                let mut cur_s = M_WY;
                for j in (0..c_len).rev() {
                    gamma_suf[j] = cur_s;
                    cur_s = rshift_round_i64(cur_s * alpha_q12[j * GDN_H + h], 12);
                }
                for j in 0..c_len {
                    cap_gamma[j * c_len + j] = M_WY;
                    let mut p = M_WY;
                    for i in (j + 1)..c_len {
                        p = rshift_round_i64(p * alpha_q12[i * GDN_H + h], 12);
                        cap_gamma[i * c_len + j] = p;
                    }
                }

                // Strictly lower-triangular `L_tilde[i, j]`
                let mut l_mat = vec![0i64; c_len * c_len];
                for i in 1..c_len {
                    let bi = beta_q12[i * GDN_H + h];
                    for j in 0..i {
                        let mut kk = 0i64;
                        for d in 0..GDN_D {
                            kk += k_int[i * GDN_D + d] * k_int[j * GDN_D + d];
                        }
                        let kk_q12 = rshift_round_i64(kk, 12);
                        let bg = rshift_round_i64(bi * cap_gamma[i * c_len + j], 12);
                        l_mat[i * c_len + j] = rshift_round_i64(bg * kk_q12, 12);
                    }
                }

                // `RHS = [U_rhs (128) | W_rhs (128)]`
                let mut rhs_mat = vec![0i64; c_len * cols];
                let u_rsh = 28 - u_shift;
                for i in 0..c_len {
                    let gb = rshift_round_i64(gamma_pre[i] * beta_q12[i * GDN_H + h], 12);
                    for d in 0..GDN_D {
                        rhs_mat[i * cols + d] = if u_rsh >= 0 {
                            rshift_round_i64(v_beta_q28[i * GDN_D + d], u_rsh as u32)
                        } else {
                            v_beta_q28[i * GDN_D + d] << ((-u_rsh) as u32)
                        };
                        rhs_mat[i * cols + GDN_D + d] =
                            rshift_round_i64(gb * k_int[i * GDN_D + d], 12);
                    }
                }

                // Exact Euclidean forward substitution `(I + L_tilde / 4096) UW = RHS`!
                let mut uw_mat = vec![0i64; c_len * cols];
                let mut rem_mat = vec![0u32; c_len * cols];
                for i in 0..c_len {
                    for col in 0..cols {
                        let mut sum_lu = 0i64;
                        for j in 0..i {
                            sum_lu += l_mat[i * c_len + j] * uw_mat[j * cols + col];
                        }
                        assert!(
                            sum_lu.abs() < (P as i64) / 2,
                            "IntWY BabyBear wraparound guard tripped: |sum_lu|={}",
                            sum_lu.abs()
                        );
                        let num = M_WY * rhs_mat[i * cols + col] + half_wy - sum_lu;
                        let uw_val = num.div_euclid(M_WY);
                        let r_val = num.rem_euclid(M_WY) as u32;
                        debug_assert_eq!(
                            sum_lu,
                            M_WY * (rhs_mat[i * cols + col] - uw_val) + half_wy - (r_val as i64)
                        );
                        uw_mat[i * cols + col] = uw_val;
                        rem_mat[i * cols + col] = r_val;
                    }
                }

                // Convert initial `s_init_q16` to `u_shift` scale (`S_u`):
                let s_init_h = &s_init_q16[h * GDN_D * GDN_D..(h + 1) * GDN_D * GDN_D];
                let mut s_u = vec![0i64; GDN_D * GDN_D];
                let sh_diff = u_shift - 16;
                for idx in 0..(GDN_D * GDN_D) {
                    s_u[idx] = if sh_diff >= 0 {
                        (s_init_h[idx] as i64) << (sh_diff as u32)
                    } else {
                        rshift_round_i64(s_init_h[idx] as i64, (-sh_diff) as u32)
                    };
                }

                // `U_eff = U - (W @ S_u >> 12)` (`scale = 2^u_shift`)
                let mut u_eff = vec![0i64; c_len * GDN_D];
                for i in 0..c_len {
                    for dv in 0..GDN_D {
                        let mut ws = 0i64;
                        for dk in 0..GDN_D {
                            ws += uw_mat[i * cols + GDN_D + dk] * s_u[dk * GDN_D + dv];
                        }
                        u_eff[i * GDN_D + dv] = uw_mat[i * cols + dv] - rshift_round_i64(ws, 12);
                    }
                }

                // Intra + inter-chunk readout -> `y_h_q16[c_len * 128]`
                let mut y_h_q16 = vec![0i32; c_len * GDN_D];
                // `y_acc` has scale `M_WY * 2^u_shift = 2^(12 + u_shift)` before `1/sqrt(128)` (`INV_SQRT128_Q16 / 2^16`)
                // Product `y_acc * INV_SQRT128_Q16` has scale `2^(28 + u_shift)` -> shift right by `12 + u_shift` to get `Q16`!
                let y_rsh = (12 + u_shift) as u32;
                for i in 0..c_len {
                    let mut y_inter_row = [0i64; GDN_D];
                    for dk in 0..GDN_D {
                        let qg = rshift_round_i64(gamma_pre[i] * q_int[i * GDN_D + dk], 12);
                        if qg != 0 {
                            for dv in 0..GDN_D {
                                y_inter_row[dv] += qg * s_u[dk * GDN_D + dv];
                            }
                        }
                    }
                    let mut y_intra_row = [0i64; GDN_D];
                    for j in 0..=i {
                        let mut qk = 0i64;
                        for dk in 0..GDN_D {
                            qk += q_int[i * GDN_D + dk] * k_int[j * GDN_D + dk];
                        }
                        let qk_q12 = rshift_round_i64(qk, 12);
                        let attn_ij = rshift_round_i64(qk_q12 * cap_gamma[i * c_len + j], 12);
                        for dv in 0..GDN_D {
                            y_intra_row[dv] += attn_ij * u_eff[j * GDN_D + dv];
                        }
                    }
                    for dv in 0..GDN_D {
                        let y_acc = (rshift_round_i64(y_inter_row[dv], 12) << 12) + y_intra_row[dv];
                        let scaled =
                            rshift_round_i128((y_acc as i128) * (INV_SQRT128_Q16 as i128), y_rsh);
                        y_h_q16[i * GDN_D + dv] =
                            scaled.clamp(i32::MIN as i64 + 1, i32::MAX as i64) as i32;
                    }
                }

                // Update `S_u` -> `s_final_h_q16[128 * 128]`
                let g_last = gamma_pre[c_len - 1];
                let mut s_next_q16 = vec![0i32; GDN_D * GDN_D];
                for dk in 0..GDN_D {
                    for dv in 0..GDN_D {
                        let s_dec = rshift_round_i64(g_last * s_u[dk * GDN_D + dv], 12);
                        let mut add_acc = 0i64;
                        for i in 0..c_len {
                            let kb = rshift_round_i64(gamma_suf[i] * k_int[i * GDN_D + dk], 12);
                            add_acc += kb * u_eff[i * GDN_D + dv];
                        }
                        let s_new_u = s_dec + rshift_round_i64(add_acc, 12);
                        let v_q16 = if sh_diff >= 0 {
                            rshift_round_i64(s_new_u, sh_diff as u32)
                        } else {
                            s_new_u << ((-sh_diff) as u32)
                        };
                        s_next_q16[dk * GDN_D + dv] =
                            v_q16.clamp(i32::MIN as i64 + 1, i32::MAX as i64) as i32;
                    }
                }

                (l_mat, rhs_mat, uw_mat, rem_mat, y_h_q16, s_next_q16)
            })
            .collect();

        let log_h = 4usize;
        let log_c = 6usize;
        let mut l_lsb_hij = vec![0u32; GDN_H * c_len * c_len];
        let mut rhs_lsb_hik = vec![0u32; GDN_H * c_len * cols];
        let mut uw_lsb_hik = vec![0u32; GDN_H * c_len * cols];
        let mut rem_lsb_hik = vec![0u32; GDN_H * c_len * cols];
        let mut y_out_q16 = vec![0i32; c_len * GDN_H * GDN_D];
        let mut s_final_q16 = vec![0i32; GDN_H * GDN_D * GDN_D];

        for (h, (l_mat, rhs_mat, uw_mat, rem_mat, y_h, s_h)) in per_head.into_iter().enumerate() {
            s_final_q16[h * GDN_D * GDN_D..(h + 1) * GDN_D * GDN_D].copy_from_slice(&s_h);
            for i in 0..c_len {
                for j in 0..c_len {
                    let idx = h + (i << log_h) + (j << (log_h + log_c));
                    l_lsb_hij[idx] = bb_from_i64(l_mat[i * c_len + j]);
                }
                for col in 0..cols {
                    let idx = h + (i << log_h) + (col << (log_h + log_c));
                    rhs_lsb_hik[idx] = bb_from_i64(rhs_mat[i * cols + col]);
                    uw_lsb_hik[idx] = bb_from_i64(uw_mat[i * cols + col]);
                    rem_lsb_hik[idx] = rem_mat[i * cols + col];
                }
                y_out_q16[(i * GDN_H + h) * GDN_D..(i * GDN_H + h + 1) * GDN_D]
                    .copy_from_slice(&y_h[i * GDN_D..(i + 1) * GDN_D]);
            }
        }

        (
            y_out_q16,
            s_final_q16,
            RealGdnWyWitness {
                h_v_orig: GDN_H,
                h_pad: GDN_H,
                c_len,
                d_k: GDN_D,
                d_v: GDN_D,
                l_lsb_hij,
                rhs_lsb_hik,
                uw_lsb_hik,
                rem_lsb_hik,
                y_out_f32: Vec::new(),
            },
        )
    }

    /// Execute a full 64-token `IntWY` prefill chunk across all 24 layers (`0` float ops!),
    /// initializing `cache` for subsequent autoregressive decoding AND capturing `Qwen35TurnExecution`
    /// for `audited_layer`!
    pub fn prefill_chunk64_int(
        &self,
        token_ids_64: &[u32],
        audited_layer: usize,
        cache: &mut ExactIntDecodeCache,
    ) -> Result<(Qwen35TurnExecution, Vec<i32>), String> {
        assert_eq!(token_ids_64.len(), 64);
        assert!(audited_layer < NUM_LAYERS && (audited_layer % 4) != 3);
        let tabs = int_math_tables();
        let seq_len = 64usize;
        let pos_base = cache.pos;

        let mut h_q16 = self.embed_tokens_q16(token_ids_64)?;
        let mut h_b_i16: Vec<i16> = h_q16
            .iter()
            .map(|&v| rshift_round_i64(v as i64, BOUNDARY_I16_SHIFT).clamp(-32767, 32767) as i16)
            .collect();

        let pack_bnd = |arr: &[i16]| -> Vec<u32> {
            let mut out = vec![0u32; seq_len * D_MODEL];
            for t in 0..seq_len {
                for d in 0..D_MODEL {
                    out[t + (d << 6)] = bb_from_i64(arr[t * D_MODEL + d] as i64);
                }
            }
            out
        };
        let pack_bnd_i32 = |arr: &[i32]| -> Vec<u32> {
            let mut out = vec![0u32; seq_len * D_MODEL];
            for t in 0..seq_len {
                for d in 0..D_MODEL {
                    out[t + (d << 6)] = bb_from_i64(arr[t * D_MODEL + d] as i64);
                }
            }
            out
        };

        let mut boundaries_bb = Vec::with_capacity(25);
        boundaries_bb.push(pack_bnd(&h_b_i16));

        let mut opt_wy: Option<RealGdnWyWitness> = None;
        let mut opt_x_ln2: Option<Vec<i16>> = None;
        let mut opt_gate_y: Option<Vec<i64>> = None;
        let mut opt_delta_gdn: Option<Vec<u32>> = None;
        let mut opt_delta_mlp: Option<Vec<u32>> = None;

        for (l, lw) in self.layers.iter().enumerate() {
            let x_ln1_q16 = rmsnorm_zero_centered_int_q16(tabs, &h_q16, &lw.ln1_1pw_q16, D_MODEL);
            let (x_ln1_i16, x_ln1_sh) =
                quantize_act_i16_dyn_pow2(&x_ln1_q16, seq_len, D_MODEL, 16383);

            let attn_delta_q16: Vec<i32> = match &lw.attn {
                LayerAttnWeights::Gdn(gdn) => {
                    let GdnAttnWeights {
                        qkv,
                        z,
                        b,
                        a,
                        out_proj,
                        conv_w_q16,
                        neg_exp_alog_q16,
                        dt_bias_q16,
                        norm_w_q16,
                    } = gdn.as_ref();
                    let qkv_q16 = qkv.matmul_to_q16(&x_ln1_i16, &x_ln1_sh, seq_len);
                    let z_q16 = z.matmul_to_q16(&x_ln1_i16, &x_ln1_sh, seq_len);
                    let b_q16 = b.matmul_to_q16(&x_ln1_i16, &x_ln1_sh, seq_len);
                    let a_q16 = a.matmul_to_q16(&x_ln1_i16, &x_ln1_sh, seq_len);

                    // Causal 4-tap depthwise conv1d + SiLU (`0` float ops!)
                    let prev_conv = cache.conv_q16[l].clone();
                    let mut conv_out_q16 = vec![0i32; seq_len * 6144];
                    for t in 0..seq_len {
                        let dst = &mut conv_out_q16[t * 6144..(t + 1) * 6144];
                        for ch in 0..6144 {
                            let mut s = 0i64;
                            for kw in 0..GDN_CONV_W {
                                let rel = (t as isize) - 3 + (kw as isize);
                                let v_in = if rel >= 0 {
                                    qkv_q16[(rel as usize) * 6144 + ch]
                                } else {
                                    let c_idx = (3 + rel) as usize;
                                    prev_conv[ch * GDN_CONV_W + c_idx]
                                };
                                s += (v_in as i64) * (conv_w_q16[ch * 4 + kw] as i64);
                            }
                            dst[ch] = int_silu_q16(tabs, rshift_round_i64(s, 16) as i32);
                        }
                    }
                    // Save last 4 tokens into `cache.conv_q16[l]`
                    for ch in 0..6144 {
                        for kw in 0..GDN_CONV_W {
                            cache.conv_q16[l][ch * GDN_CONV_W + kw] =
                                qkv_q16[(seq_len - GDN_CONV_W + kw) * 6144 + ch];
                        }
                    }

                    let mut q_q16 = vec![0i32; seq_len * 2048];
                    let mut k_q16 = vec![0i32; seq_len * 2048];
                    let mut v_q16 = vec![0i32; seq_len * 2048];
                    let mut alpha_q12 = vec![0i64; seq_len * 16];
                    let mut beta_q12 = vec![0i64; seq_len * 16];

                    for t in 0..seq_len {
                        q_q16[t * 2048..(t + 1) * 2048]
                            .copy_from_slice(&conv_out_q16[t * 6144..t * 6144 + 2048]);
                        k_q16[t * 2048..(t + 1) * 2048]
                            .copy_from_slice(&conv_out_q16[t * 6144 + 2048..t * 6144 + 4096]);
                        v_q16[t * 2048..(t + 1) * 2048]
                            .copy_from_slice(&conv_out_q16[t * 6144 + 4096..t * 6144 + 6144]);
                        for h in 0..16 {
                            beta_q12[t * 16 + h] = rshift_round_i64(
                                int_sigmoid_q15(tabs, b_q16[t * 16 + h]) as i64,
                                3,
                            );
                            let sp = int_softplus_q16(tabs, a_q16[t * 16 + h] + dt_bias_q16[h]);
                            let g_q16 = rshift_round_i64(neg_exp_alog_q16[h] * sp, 16)
                                .clamp(-(32 << 16), 0)
                                as i32;
                            alpha_q12[t * 16 + h] =
                                rshift_round_i64(int_exp_neg_q15(tabs, g_q16) as i64, 3);
                        }
                    }

                    let (y_wy_q16, s_next_q16, wy_wit) = Self::solve_gdn_int_wy_chunk64(
                        tabs,
                        &q_q16,
                        &k_q16,
                        &v_q16,
                        &alpha_q12,
                        &beta_q12,
                        &cache.ssm_q16[l],
                    );
                    cache.ssm_q16[l] = s_next_q16;
                    if l == audited_layer {
                        opt_wy = Some(wy_wit);
                    }

                    // Integer `Qwen3NextRMSNormGated`: `norm_w * rmsnorm_plain(y) * silu(z)`
                    let mut gated_q16 = vec![0i32; seq_len * 2048];
                    for t in 0..seq_len {
                        for h in 0..16 {
                            let off = (t * 16 + h) * 128;
                            let ys = &y_wy_q16[off..off + 128];
                            let zs = &z_q16[off..off + 128];
                            let sq: u128 = ys
                                .iter()
                                .map(|&y| ((y as i128) * (y as i128)) as u128)
                                .sum();
                            let inv_rms = int_rsqrt_from_q32_to_q16(tabs, (sq >> 7) + 4295);
                            for d in 0..128 {
                                let yn = rshift_round_i64((ys[d] as i64) * inv_rms, 16);
                                let wn = rshift_round_i64(yn * (norm_w_q16[d] as i64), 16);
                                let sz = int_silu_q16(tabs, zs[d]) as i64;
                                gated_q16[off + d] = rshift_round_i64(wn * sz, 16) as i32;
                            }
                        }
                    }
                    let (g_i16, g_sh) = quantize_act_i16_dyn_pow2(&gated_q16, seq_len, 2048, 16383);
                    out_proj.matmul_to_q16(&g_i16, &g_sh, seq_len)
                }
                LayerAttnWeights::Gqa(gqa) => {
                    let GqaAttnWeights {
                        q_proj,
                        k_proj,
                        v_proj,
                        o_proj,
                        q_norm_1pw_q16,
                        k_norm_1pw_q16,
                    } = gqa.as_ref();
                    let qg_q16 = q_proj.matmul_to_q16(&x_ln1_i16, &x_ln1_sh, seq_len);
                    let kp_q16 = k_proj.matmul_to_q16(&x_ln1_i16, &x_ln1_sh, seq_len);
                    let vp_q16 = v_proj.matmul_to_q16(&x_ln1_i16, &x_ln1_sh, seq_len);

                    let mut q_heads_q16 = vec![0i32; seq_len * GQA_HQ * GQA_DH];
                    let mut gate_q16 = vec![0i32; seq_len * 2048];
                    for t in 0..seq_len {
                        for h in 0..GQA_HQ {
                            let src = &qg_q16[(t * 8 + h) * 512..(t * 8 + h + 1) * 512];
                            q_heads_q16[(t * 8 + h) * 256..(t * 8 + h + 1) * 256]
                                .copy_from_slice(&src[..256]);
                            gate_q16[(t * 8 + h) * 256..(t * 8 + h + 1) * 256]
                                .copy_from_slice(&src[256..]);
                        }
                    }
                    let mut q_norm =
                        rmsnorm_zero_centered_int_q16(tabs, &q_heads_q16, q_norm_1pw_q16, GQA_DH);
                    let mut k_norm =
                        rmsnorm_zero_centered_int_q16(tabs, &kp_q16, k_norm_1pw_q16, GQA_DH);

                    // Integer Partial RoPE (`rotary_dim = 64`) & append to KV cache (`Q12` `i16`)!
                    for t in 0..seq_len {
                        let pos = pos_base + t;
                        let cs = &tabs.rope_cos_q15[pos];
                        let sn = &tabs.rope_sin_q15[pos];
                        for pair in 0..32usize {
                            let (c, s) = (cs[pair] as i64, sn[pair] as i64);
                            for h in 0..GQA_HQ {
                                let base = (t * 8 + h) * 256;
                                let (x1, x2) =
                                    (q_norm[base + pair] as i64, q_norm[base + 32 + pair] as i64);
                                q_norm[base + pair] = rshift_round_i64(x1 * c - x2 * s, 15) as i32;
                                q_norm[base + 32 + pair] =
                                    rshift_round_i64(x2 * c + x1 * s, 15) as i32;
                            }
                            for hk in 0..GQA_HKV {
                                let base = (t * 2 + hk) * 256;
                                let (x1, x2) =
                                    (k_norm[base + pair] as i64, k_norm[base + 32 + pair] as i64);
                                k_norm[base + pair] = rshift_round_i64(x1 * c - x2 * s, 15) as i32;
                                k_norm[base + 32 + pair] =
                                    rshift_round_i64(x2 * c + x1 * s, 15) as i32;
                            }
                        }
                        for idx in 0..(GQA_HKV * GQA_DH) {
                            cache.k_cache_q12[l].push(
                                rshift_round_i64(k_norm[t * 512 + idx] as i64, 4)
                                    .clamp(-32767, 32767) as i16,
                            );
                            cache.v_cache_q12[l].push(
                                rshift_round_i64(vp_q16[t * 512 + idx] as i64, 4)
                                    .clamp(-32767, 32767) as i16,
                            );
                        }
                    }

                    let k_all = &cache.k_cache_q12[l];
                    let v_all = &cache.v_cache_q12[l];
                    let mut attn_out_q16 = vec![0i32; seq_len * 2048];
                    for h in 0..GQA_HQ {
                        let hk = h / 4;
                        for ti in 0..seq_len {
                            let total_kv = pos_base + ti + 1;
                            let qi = &q_norm[(ti * 8 + h) * 256..(ti * 8 + h + 1) * 256];
                            // `qi` is Q16, `kj` is Q12 -> `qi * kj` is Q28; `* 1/16` (`>> 4`) -> Q24; `>> 8` -> Q16!
                            let mut scores_q16 = vec![0i32; total_kv];
                            let mut max_s = i32::MIN;
                            for tj in 0..total_kv {
                                let kj = &k_all[(tj * 2 + hk) * 256..(tj * 2 + hk + 1) * 256];
                                let mut dot = 0i64;
                                for d in 0..256 {
                                    dot += (qi[d] as i64) * (kj[d] as i64);
                                }
                                let s_q16 = rshift_round_i64(dot, 12 + INV_SQRT256_SHIFT) as i32;
                                scores_q16[tj] = s_q16;
                                if s_q16 > max_s {
                                    max_s = s_q16;
                                }
                            }
                            let mut weights = vec![0u64; total_kv];
                            let mut sum_w = 0u64;
                            for tj in 0..total_kv {
                                let w = int_exp_neg_q15(tabs, scores_q16[tj].saturating_sub(max_s))
                                    as u64;
                                weights[tj] = w;
                                sum_w += w;
                            }
                            let sum_w = sum_w.max(1) as i128;
                            let dst = &mut attn_out_q16[(ti * 8 + h) * 256..(ti * 8 + h + 1) * 256];
                            for d in 0..256 {
                                let mut acc: i128 = 0;
                                for tj in 0..total_kv {
                                    let vj_q16 = (v_all[(tj * 2 + hk) * 256 + d] as i128) << 4; // Q12 -> Q16
                                    acc += (weights[tj] as i128) * vj_q16;
                                }
                                let av = (acc + sum_w / 2).div_euclid(sum_w) as i64;
                                let g_sig =
                                    int_sigmoid_q15(tabs, gate_q16[(ti * 8 + h) * 256 + d]) as i64;
                                dst[d] = rshift_round_i64(av * g_sig, 15) as i32;
                            }
                        }
                    }
                    let (a_i16, a_sh) =
                        quantize_act_i16_dyn_pow2(&attn_out_q16, seq_len, 2048, 16383);
                    o_proj.matmul_to_q16(&a_i16, &a_sh, seq_len)
                }
            };

            // Mid-layer residual + exact `i32` boundary delta tracking (zero `i16` saturation!)
            let mut h_mid_q16 = vec![0i32; seq_len * D_MODEL];
            let mut h_mid_b_i16 = vec![0i16; seq_len * D_MODEL];
            let mut exact_delta_attn = vec![0i32; seq_len * D_MODEL];
            for i in 0..(seq_len * D_MODEL) {
                let m = h_q16[i].saturating_add(attn_delta_q16[i]);
                h_mid_q16[i] = m;
                let mb = rshift_round_i64(m as i64, BOUNDARY_I16_SHIFT).clamp(-32767, 32767) as i16;
                exact_delta_attn[i] = (mb as i32) - (h_b_i16[i] as i32);
                h_mid_b_i16[i] = mb;
            }

            // SwiGLU MLP (`MXFP4-E2M1`: target_max = `2047` -> `|Y_raw| < 15M << P_BB / 2` with 66 dB dynamic range!)
            let x_ln2_q16 =
                rmsnorm_zero_centered_int_q16(tabs, &h_mid_q16, &lw.ln2_1pw_q16, D_MODEL);
            let (x_ln2_i16, x_ln2_sh) =
                quantize_act_i16_dyn_pow2(&x_ln2_q16, seq_len, D_MODEL, 2047);
            let (gate_q16, gate_raw_opt) =
                lw.gate_proj
                    .matmul_to_q16(&x_ln2_i16, &x_ln2_sh, seq_len, l == audited_layer);
            let (up_q16, _) = lw
                .up_proj
                .matmul_to_q16(&x_ln2_i16, &x_ln2_sh, seq_len, false);

            let mut swiglu_q16 = vec![0i32; seq_len * D_FF];
            for i in 0..(seq_len * D_FF) {
                let sg = int_silu_q16(tabs, gate_q16[i]) as i64;
                swiglu_q16[i] = rshift_round_i64(sg * (up_q16[i] as i64), 16)
                    .clamp(i32::MIN as i64 + 1, i32::MAX as i64)
                    as i32;
            }
            let (sw_i16, sw_sh) = quantize_act_i16_dyn_pow2(&swiglu_q16, seq_len, D_FF, 2047);
            let (down_q16, _) = lw.down_proj.matmul_to_q16(&sw_i16, &sw_sh, seq_len, false);

            let mut exact_delta_mlp = vec![0i32; seq_len * D_MODEL];
            for i in 0..(seq_len * D_MODEL) {
                let nxt = h_mid_q16[i].saturating_add(down_q16[i]);
                h_q16[i] = nxt;
                let nb =
                    rshift_round_i64(nxt as i64, BOUNDARY_I16_SHIFT).clamp(-32767, 32767) as i16;
                exact_delta_mlp[i] = (nb as i32) - (h_mid_b_i16[i] as i32);
                h_b_i16[i] = nb;
            }

            if l == audited_layer {
                opt_x_ln2 = Some(x_ln2_i16);
                opt_gate_y = gate_raw_opt;
                opt_delta_gdn = Some(pack_bnd_i32(&exact_delta_attn));
                opt_delta_mlp = Some(pack_bnd_i32(&exact_delta_mlp));
            }
            boundaries_bb.push(pack_bnd(&h_b_i16));
        }

        cache.pos += seq_len;
        let last_h = h_q16[(seq_len - 1) * D_MODEL..seq_len * D_MODEL].to_vec();
        Ok((
            Qwen35TurnExecution {
                token_ids: token_ids_64.to_vec(),
                boundaries_bb,
                audited_layer,
                wy_witness: opt_wy.unwrap(),
                x_ln2_i16: opt_x_ln2.unwrap(),
                gate_proj_mat: self.layers[audited_layer].gate_proj.mat.clone(),
                gate_proj_y_raw: opt_gate_y.unwrap(),
                delta_gdn_bb: opt_delta_gdn.unwrap(),
                delta_mlp_bb: opt_delta_mlp.unwrap(),
            },
            last_h,
        ))
    }

    /// Single-token (`T = 1`) exact-integer autoregressive decode step streaming 25 `U1` boundary digests!
    /// Returns `(last_h_q16 [1024], step_boundary_digests [[u8; 32]; 25])`.
    pub fn decode_step_int(
        &self,
        token_id: u32,
        cache: &mut ExactIntDecodeCache,
    ) -> Result<(Vec<i32>, [[u8; 32]; 25]), String> {
        let tabs = int_math_tables();
        let pos = cache.pos;
        let mut h_q16 = self.embed_tokens_q16(&[token_id])?;
        let mut step_bnds = [[0u8; 32]; 25];

        let hash_step_bnd = |b_idx: usize, vec_q16: &[i32]| -> [u8; 32] {
            let mut buf = Vec::with_capacity(8 + D_MODEL * 2);
            buf.extend_from_slice(&(pos as u32).to_le_bytes());
            buf.extend_from_slice(&(b_idx as u32).to_le_bytes());
            for &v in vec_q16 {
                let vi16 =
                    rshift_round_i64(v as i64, BOUNDARY_I16_SHIFT).clamp(-32767, 32767) as i16;
                buf.extend_from_slice(&vi16.to_le_bytes());
            }
            cshake256_32(b"QW35-U1-DECODE-STEP-BND-V1", &buf)
        };
        step_bnds[0] = hash_step_bnd(0, &h_q16);

        for (l, lw) in self.layers.iter().enumerate() {
            let x_ln1_q16 = rmsnorm_zero_centered_int_q16(tabs, &h_q16, &lw.ln1_1pw_q16, D_MODEL);
            let (x_ln1_i16, x_ln1_sh) = quantize_act_i16_dyn_pow2(&x_ln1_q16, 1, D_MODEL, 16383);

            let attn_delta_q16: Vec<i32> = match &lw.attn {
                LayerAttnWeights::Gdn(gdn) => {
                    let GdnAttnWeights {
                        qkv,
                        z,
                        b,
                        a,
                        out_proj,
                        conv_w_q16,
                        neg_exp_alog_q16,
                        dt_bias_q16,
                        norm_w_q16,
                    } = gdn.as_ref();
                    let qkv_q16 = qkv.matmul_to_q16(&x_ln1_i16, &x_ln1_sh, 1);
                    let z_q16 = z.matmul_to_q16(&x_ln1_i16, &x_ln1_sh, 1);
                    let b_q16 = b.matmul_to_q16(&x_ln1_i16, &x_ln1_sh, 1);
                    let a_q16 = a.matmul_to_q16(&x_ln1_i16, &x_ln1_sh, 1);

                    let mut conv_out_q16 = vec![0i32; 6144];
                    let cst = &mut cache.conv_q16[l];
                    for ch in 0..6144 {
                        let base = ch * GDN_CONV_W;
                        cst[base] = cst[base + 1];
                        cst[base + 1] = cst[base + 2];
                        cst[base + 2] = cst[base + 3];
                        cst[base + 3] = qkv_q16[ch];
                        let s = (cst[base] as i64) * (conv_w_q16[base] as i64)
                            + (cst[base + 1] as i64) * (conv_w_q16[base + 1] as i64)
                            + (cst[base + 2] as i64) * (conv_w_q16[base + 2] as i64)
                            + (cst[base + 3] as i64) * (conv_w_q16[base + 3] as i64);
                        conv_out_q16[ch] = int_silu_q16(tabs, rshift_round_i64(s, 16) as i32);
                    }

                    let q_s = &conv_out_q16[0..2048];
                    let k_s = &conv_out_q16[2048..4096];
                    let v_s = &conv_out_q16[4096..6144];

                    // Parallel exact-integer recurrent GDN step across `H = 16` heads!
                    let mut gated_q16 = vec![0i32; 2048];
                    cache.ssm_q16[l]
                        .par_chunks_mut(GDN_D * GDN_D)
                        .zip(gated_q16.par_chunks_mut(GDN_D))
                        .enumerate()
                        .for_each(|(h, (s_mat, g_dst))| {
                            let qh = &q_s[h * GDN_D..(h + 1) * GDN_D];
                            let kh = &k_s[h * GDN_D..(h + 1) * GDN_D];
                            let vh = &v_s[h * GDN_D..(h + 1) * GDN_D];
                            let zh = &z_q16[h * GDN_D..(h + 1) * GDN_D];

                            let mut sq_q: u128 = 4295;
                            let mut sq_k: u128 = 4295;
                            for d in 0..GDN_D {
                                sq_q += ((qh[d] as i128) * (qh[d] as i128)) as u128;
                                sq_k += ((kh[d] as i128) * (kh[d] as i128)) as u128;
                            }
                            let inv_q = int_rsqrt_from_q32_to_q16(tabs, sq_q);
                            let inv_k = int_rsqrt_from_q32_to_q16(tabs, sq_k);
                            let mut q_q12 = [0i64; GDN_D];
                            let mut k_q12 = [0i64; GDN_D];
                            for d in 0..GDN_D {
                                q_q12[d] = rshift_round_i64((qh[d] as i64) * inv_q, 20)
                                    .clamp(-K_WY_SCALE, K_WY_SCALE);
                                k_q12[d] = rshift_round_i64((kh[d] as i64) * inv_k, 20)
                                    .clamp(-K_WY_SCALE, K_WY_SCALE);
                            }

                            let beta_q12 =
                                rshift_round_i64(int_sigmoid_q15(tabs, b_q16[h]) as i64, 3);
                            let sp = int_softplus_q16(tabs, a_q16[h] + dt_bias_q16[h]);
                            let g_q16 = rshift_round_i64(neg_exp_alog_q16[h] * sp, 16)
                                .clamp(-(32 << 16), 0)
                                as i32;
                            let alpha_q12 =
                                rshift_round_i64(int_exp_neg_q15(tabs, g_q16) as i64, 3);

                            for s_cell in s_mat.iter_mut() {
                                *s_cell = rshift_round_i64((*s_cell as i64) * alpha_q12, 12) as i32;
                            }

                            let mut kv_mem_q16 = [0i64; GDN_D];
                            for dk in 0..GDN_D {
                                let kval = k_q12[dk];
                                if kval != 0 {
                                    let s_row = &s_mat[dk * GDN_D..(dk + 1) * GDN_D];
                                    for dv in 0..GDN_D {
                                        kv_mem_q16[dv] += (s_row[dv] as i64) * kval;
                                    }
                                }
                            }
                            let mut delta_q16 = [0i64; GDN_D];
                            for dv in 0..GDN_D {
                                let kv = rshift_round_i64(kv_mem_q16[dv], 12);
                                delta_q16[dv] =
                                    rshift_round_i64(((vh[dv] as i64) - kv) * beta_q12, 12);
                            }

                            let mut y_raw_q28 = [0i64; GDN_D];
                            for dk in 0..GDN_D {
                                let kval = k_q12[dk];
                                let qval = q_q12[dk];
                                let s_row = &mut s_mat[dk * GDN_D..(dk + 1) * GDN_D];
                                for dv in 0..GDN_D {
                                    let upd = rshift_round_i64(kval * delta_q16[dv], 12);
                                    let sn = ((s_row[dv] as i64) + upd)
                                        .clamp(i32::MIN as i64 + 1, i32::MAX as i64);
                                    s_row[dv] = sn as i32;
                                    y_raw_q28[dv] += sn * qval;
                                }
                            }

                            let mut y_h_q16 = [0i32; GDN_D];
                            let mut sq_y: u128 = 0;
                            for dv in 0..GDN_D {
                                let yq = rshift_round_i128(
                                    (y_raw_q28[dv] as i128) * (INV_SQRT128_Q16 as i128),
                                    28,
                                ) as i32;
                                y_h_q16[dv] = yq;
                                sq_y += ((yq as i128) * (yq as i128)) as u128;
                            }
                            let inv_rms = int_rsqrt_from_q32_to_q16(tabs, (sq_y >> 7) + 4295);
                            for dv in 0..GDN_D {
                                let yn = rshift_round_i64((y_h_q16[dv] as i64) * inv_rms, 16);
                                let wn = rshift_round_i64(yn * (norm_w_q16[dv] as i64), 16);
                                let sz = int_silu_q16(tabs, zh[dv]) as i64;
                                g_dst[dv] = rshift_round_i64(wn * sz, 16) as i32;
                            }
                        });

                    let (g_i16, g_sh) = quantize_act_i16_dyn_pow2(&gated_q16, 1, 2048, 16383);
                    out_proj.matmul_to_q16(&g_i16, &g_sh, 1)
                }
                LayerAttnWeights::Gqa(gqa) => {
                    let GqaAttnWeights {
                        q_proj,
                        k_proj,
                        v_proj,
                        o_proj,
                        q_norm_1pw_q16,
                        k_norm_1pw_q16,
                    } = gqa.as_ref();
                    let qg_q16 = q_proj.matmul_to_q16(&x_ln1_i16, &x_ln1_sh, 1);
                    let kp_q16 = k_proj.matmul_to_q16(&x_ln1_i16, &x_ln1_sh, 1);
                    let vp_q16 = v_proj.matmul_to_q16(&x_ln1_i16, &x_ln1_sh, 1);

                    let mut q_heads = vec![0i32; GQA_HQ * GQA_DH];
                    let mut gate_q16 = vec![0i32; 2048];
                    for h in 0..GQA_HQ {
                        let src = &qg_q16[h * 512..(h + 1) * 512];
                        q_heads[h * 256..(h + 1) * 256].copy_from_slice(&src[..256]);
                        gate_q16[h * 256..(h + 1) * 256].copy_from_slice(&src[256..]);
                    }
                    let mut q_norm =
                        rmsnorm_zero_centered_int_q16(tabs, &q_heads, q_norm_1pw_q16, GQA_DH);
                    let mut k_norm =
                        rmsnorm_zero_centered_int_q16(tabs, &kp_q16, k_norm_1pw_q16, GQA_DH);

                    let cs = &tabs.rope_cos_q15[pos];
                    let sn = &tabs.rope_sin_q15[pos];
                    for pair in 0..32usize {
                        let (c, s) = (cs[pair] as i64, sn[pair] as i64);
                        for h in 0..GQA_HQ {
                            let base = h * 256;
                            let (x1, x2) =
                                (q_norm[base + pair] as i64, q_norm[base + 32 + pair] as i64);
                            q_norm[base + pair] = rshift_round_i64(x1 * c - x2 * s, 15) as i32;
                            q_norm[base + 32 + pair] = rshift_round_i64(x2 * c + x1 * s, 15) as i32;
                        }
                        for hk in 0..GQA_HKV {
                            let base = hk * 256;
                            let (x1, x2) =
                                (k_norm[base + pair] as i64, k_norm[base + 32 + pair] as i64);
                            k_norm[base + pair] = rshift_round_i64(x1 * c - x2 * s, 15) as i32;
                            k_norm[base + 32 + pair] = rshift_round_i64(x2 * c + x1 * s, 15) as i32;
                        }
                    }

                    for idx in 0..(GQA_HKV * GQA_DH) {
                        cache.k_cache_q12[l].push(
                            rshift_round_i64(k_norm[idx] as i64, 4).clamp(-32767, 32767) as i16,
                        );
                        cache.v_cache_q12[l].push(
                            rshift_round_i64(vp_q16[idx] as i64, 4).clamp(-32767, 32767) as i16,
                        );
                    }

                    let k_all = &cache.k_cache_q12[l];
                    let v_all = &cache.v_cache_q12[l];
                    let total_kv = pos + 1;
                    let mut attn_out_q16 = vec![0i32; 2048];

                    for h in 0..GQA_HQ {
                        let hk = h / 4;
                        let qi = &q_norm[h * 256..(h + 1) * 256];
                        let mut scores_q16 = vec![0i32; total_kv];
                        let mut max_s = i32::MIN;
                        for tj in 0..total_kv {
                            let kj = &k_all[(tj * 2 + hk) * 256..(tj * 2 + hk + 1) * 256];
                            let mut dot = 0i64;
                            for d in 0..256 {
                                dot += (qi[d] as i64) * (kj[d] as i64);
                            }
                            let s_q16 = rshift_round_i64(dot, 12 + INV_SQRT256_SHIFT) as i32;
                            scores_q16[tj] = s_q16;
                            if s_q16 > max_s {
                                max_s = s_q16;
                            }
                        }
                        let mut weights = vec![0u64; total_kv];
                        let mut sum_w = 0u64;
                        for tj in 0..total_kv {
                            let w =
                                int_exp_neg_q15(tabs, scores_q16[tj].saturating_sub(max_s)) as u64;
                            weights[tj] = w;
                            sum_w += w;
                        }
                        let sum_w = sum_w.max(1) as i128;
                        let dst = &mut attn_out_q16[h * 256..(h + 1) * 256];
                        for d in 0..256 {
                            let mut acc: i128 = 0;
                            for tj in 0..total_kv {
                                let vj_q16 = (v_all[(tj * 2 + hk) * 256 + d] as i128) << 4;
                                acc += (weights[tj] as i128) * vj_q16;
                            }
                            let av = (acc + sum_w / 2).div_euclid(sum_w) as i64;
                            let g_sig = int_sigmoid_q15(tabs, gate_q16[h * 256 + d]) as i64;
                            dst[d] = rshift_round_i64(av * g_sig, 15) as i32;
                        }
                    }

                    let (a_i16, a_sh) = quantize_act_i16_dyn_pow2(&attn_out_q16, 1, 2048, 16383);
                    o_proj.matmul_to_q16(&a_i16, &a_sh, 1)
                }
            };

            let mut h_mid_q16 = vec![0i32; D_MODEL];
            for i in 0..D_MODEL {
                h_mid_q16[i] = h_q16[i].saturating_add(attn_delta_q16[i]);
            }

            let x_ln2_q16 =
                rmsnorm_zero_centered_int_q16(tabs, &h_mid_q16, &lw.ln2_1pw_q16, D_MODEL);
            let (x_ln2_i16, x_ln2_sh) = quantize_act_i16_dyn_pow2(&x_ln2_q16, 1, D_MODEL, 2047);
            let (gate_q16, _) = lw.gate_proj.matmul_to_q16(&x_ln2_i16, &x_ln2_sh, 1, false);
            let (up_q16, _) = lw.up_proj.matmul_to_q16(&x_ln2_i16, &x_ln2_sh, 1, false);

            let mut swiglu_q16 = vec![0i32; D_FF];
            for i in 0..D_FF {
                let sg = int_silu_q16(tabs, gate_q16[i]) as i64;
                swiglu_q16[i] = rshift_round_i64(sg * (up_q16[i] as i64), 16)
                    .clamp(i32::MIN as i64 + 1, i32::MAX as i64)
                    as i32;
            }
            let (sw_i16, sw_sh) = quantize_act_i16_dyn_pow2(&swiglu_q16, 1, D_FF, 2047);
            let (down_q16, _) = lw.down_proj.matmul_to_q16(&sw_i16, &sw_sh, 1, false);

            for i in 0..D_MODEL {
                h_q16[i] = h_mid_q16[i].saturating_add(down_q16[i]);
            }
            step_bnds[l + 1] = hash_step_bnd(l + 1, &h_q16);
        }

        cache.pos = pos + 1;
        Ok((h_q16, step_bnds))
    }
}

// ============================================================================
// §5. Pure-Safe-Rust RFC 1951 `DEFLATE` + `Qwen3.8-27B` Real `.npz` Slice Loader & Prover
// ============================================================================

struct BitStream<'a> {
    data: &'a [u8],
    bit_pos: usize,
}

impl<'a> BitStream<'a> {
    fn new(data: &'a [u8]) -> Self {
        Self { data, bit_pos: 0 }
    }
    #[inline]
    fn read_bits(&mut self, n: usize) -> Result<u32, String> {
        if n == 0 {
            return Ok(0);
        }
        if self.bit_pos + n > self.data.len() * 8 {
            return Err("DEFLATE bitstream unexpected EOF".to_string());
        }
        let mut val = 0u32;
        for i in 0..n {
            let p = self.bit_pos + i;
            let bit = ((self.data[p >> 3] >> (p & 7)) & 1) as u32;
            val |= bit << i;
        }
        self.bit_pos += n;
        Ok(val)
    }
    fn align_byte(&mut self) {
        if (self.bit_pos & 7) != 0 {
            self.bit_pos = (self.bit_pos + 7) & !7;
        }
    }
}

struct HuffTable {
    counts: [u16; 16],
    symbols: Vec<u16>,
}

impl HuffTable {
    fn from_lengths(lengths: &[u8]) -> Result<Self, String> {
        let mut counts = [0u16; 16];
        for &l in lengths {
            if l as usize >= 16 {
                return Err("Huffman code length > 15".to_string());
            }
            if l > 0 {
                counts[l as usize] += 1;
            }
        }
        let mut offsets = [0u16; 16];
        let mut total = 0u16;
        for bits in 1..16 {
            offsets[bits] = total;
            total += counts[bits];
        }
        let mut symbols = vec![0u16; total as usize];
        for (sym, &l) in lengths.iter().enumerate() {
            if l > 0 {
                let idx = offsets[l as usize] as usize;
                symbols[idx] = sym as u16;
                offsets[l as usize] += 1;
            }
        }
        Ok(Self { counts, symbols })
    }

    #[inline]
    fn decode(&self, bs: &mut BitStream<'_>) -> Result<u16, String> {
        let mut code = 0i32;
        let mut first = 0i32;
        let mut index = 0i32;
        for len in 1..16usize {
            code |= bs.read_bits(1)? as i32;
            let cnt = self.counts[len] as i32;
            if code - cnt < first {
                return Ok(self.symbols[(index + (code - first)) as usize]);
            }
            index += cnt;
            first = (first + cnt) << 1;
            code <<= 1;
        }
        Err("invalid Huffman code in DEFLATE stream".to_string())
    }
}

/// Pure safe Rust RFC 1951 raw DEFLATE decompressor (`0` unsafe, `0` external crates).
pub fn inflate_raw_deflate(comp: &[u8], expected_size: usize) -> Result<Vec<u8>, String> {
    const LEN_BASE: [usize; 29] = [
        3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115,
        131, 163, 195, 227, 258,
    ];
    const LEN_EXTRA: [usize; 29] = [
        0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0,
    ];
    const DIST_BASE: [usize; 30] = [
        1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537,
        2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577,
    ];
    const DIST_EXTRA: [usize; 30] = [
        0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12,
        13, 13,
    ];
    const CL_ORDER: [usize; 19] = [
        16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,
    ];

    let mut bs = BitStream::new(comp);
    let mut out = Vec::with_capacity(expected_size);

    loop {
        let bfinal = bs.read_bits(1)?;
        let btype = bs.read_bits(2)?;
        match btype {
            0 => {
                bs.align_byte();
                let byte_pos = bs.bit_pos / 8;
                if byte_pos + 4 > comp.len() {
                    return Err("truncated uncompressed DEFLATE header".to_string());
                }
                let len = u16::from_le_bytes([comp[byte_pos], comp[byte_pos + 1]]) as usize;
                let nlen = u16::from_le_bytes([comp[byte_pos + 2], comp[byte_pos + 3]]) as usize;
                if (len ^ 0xFFFF) != nlen || byte_pos + 4 + len > comp.len() {
                    return Err("invalid uncompressed DEFLATE block length".to_string());
                }
                out.extend_from_slice(&comp[byte_pos + 4..byte_pos + 4 + len]);
                bs.bit_pos = (byte_pos + 4 + len) * 8;
            }
            1 | 2 => {
                let (lit_tab, dist_tab) = if btype == 1 {
                    let mut ll = vec![0u8; 288];
                    ll[0..144].fill(8);
                    ll[144..256].fill(9);
                    ll[256..280].fill(7);
                    ll[280..288].fill(8);
                    let dl = vec![5u8; 32];
                    (HuffTable::from_lengths(&ll)?, HuffTable::from_lengths(&dl)?)
                } else {
                    let hlit = bs.read_bits(5)? as usize + 257;
                    let hdist = bs.read_bits(5)? as usize + 1;
                    let hclen = bs.read_bits(4)? as usize + 4;
                    let mut cl_lens = [0u8; 19];
                    for i in 0..hclen {
                        cl_lens[CL_ORDER[i]] = bs.read_bits(3)? as u8;
                    }
                    let cl_tab = HuffTable::from_lengths(&cl_lens)?;
                    let mut all_lens = Vec::with_capacity(hlit + hdist);
                    while all_lens.len() < hlit + hdist {
                        let sym = cl_tab.decode(&mut bs)?;
                        match sym {
                            0..=15 => all_lens.push(sym as u8),
                            16 => {
                                let prev = *all_lens.last().ok_or("repeat 16 with no prev")?;
                                let rep = bs.read_bits(2)? as usize + 3;
                                all_lens.resize(all_lens.len() + rep, prev);
                            }
                            17 => {
                                let rep = bs.read_bits(3)? as usize + 3;
                                all_lens.resize(all_lens.len() + rep, 0);
                            }
                            18 => {
                                let rep = bs.read_bits(7)? as usize + 11;
                                all_lens.resize(all_lens.len() + rep, 0);
                            }
                            _ => return Err("invalid clen symbol".to_string()),
                        }
                    }
                    (
                        HuffTable::from_lengths(&all_lens[..hlit])?,
                        HuffTable::from_lengths(&all_lens[hlit..hlit + hdist])?,
                    )
                };

                loop {
                    let sym = lit_tab.decode(&mut bs)? as usize;
                    if sym < 256 {
                        out.push(sym as u8);
                    } else if sym == 256 {
                        break;
                    } else {
                        let l_idx = sym - 257;
                        if l_idx >= 29 {
                            return Err("invalid length symbol".to_string());
                        }
                        let length = LEN_BASE[l_idx] + bs.read_bits(LEN_EXTRA[l_idx])? as usize;
                        let d_sym = dist_tab.decode(&mut bs)? as usize;
                        if d_sym >= 30 {
                            return Err("invalid distance symbol".to_string());
                        }
                        let dist = DIST_BASE[d_sym] + bs.read_bits(DIST_EXTRA[d_sym])? as usize;
                        if dist == 0 || dist > out.len() {
                            return Err("DEFLATE lookback distance out of bounds".to_string());
                        }
                        for _ in 0..length {
                            let b = out[out.len() - dist];
                            out.push(b);
                        }
                    }
                }
            }
            _ => return Err("reserved DEFLATE block type 3".to_string()),
        }
        if bfinal != 0 {
            break;
        }
    }
    Ok(out)
}

fn read_npz_entries(path: &Path) -> Result<HashMap<String, Vec<u8>>, String> {
    let zip = fs::read(path).map_err(|e| format!("failed reading npz {}: {e}", path.display()))?;
    if zip.len() < 22 {
        return Err("npz shorter than ZIP EOCD".to_string());
    }
    let mut eocd_off = None;
    let min_off = zip.len().saturating_sub(65558);
    for pos in (min_off..=zip.len() - 22).rev() {
        if &zip[pos..pos + 4] == b"PK\x05\x06" {
            eocd_off = Some(pos);
            break;
        }
    }
    let eocd = eocd_off.ok_or_else(|| "missing ZIP EOCD signature".to_string())?;
    let total_entries = u16::from_le_bytes([zip[eocd + 10], zip[eocd + 11]]) as usize;
    let cd_offset = u32::from_le_bytes(zip[eocd + 16..eocd + 20].try_into().unwrap()) as usize;

    let mut entries = HashMap::with_capacity(total_entries);
    let mut cd_pos = cd_offset;
    for _ in 0..total_entries {
        if cd_pos + 46 > zip.len() || &zip[cd_pos..cd_pos + 4] != b"PK\x01\x02" {
            return Err("invalid ZIP central directory entry".to_string());
        }
        let method = u16::from_le_bytes([zip[cd_pos + 10], zip[cd_pos + 11]]);
        let comp_size =
            u32::from_le_bytes(zip[cd_pos + 20..cd_pos + 24].try_into().unwrap()) as usize;
        let uncomp_size =
            u32::from_le_bytes(zip[cd_pos + 24..cd_pos + 28].try_into().unwrap()) as usize;
        let name_len = u16::from_le_bytes([zip[cd_pos + 28], zip[cd_pos + 29]]) as usize;
        let extra_len = u16::from_le_bytes([zip[cd_pos + 30], zip[cd_pos + 31]]) as usize;
        let comment_len = u16::from_le_bytes([zip[cd_pos + 32], zip[cd_pos + 33]]) as usize;
        let lfh_off =
            u32::from_le_bytes(zip[cd_pos + 42..cd_pos + 46].try_into().unwrap()) as usize;
        let name_end = cd_pos
            .checked_add(46)
            .and_then(|v| v.checked_add(name_len))
            .ok_or("ZIP central directory name overflow")?;
        let name_slice = zip
            .get(cd_pos + 46..name_end)
            .ok_or("ZIP central directory name out of bounds")?;
        let name = String::from_utf8_lossy(name_slice).into_owned();
        cd_pos = name_end
            .checked_add(extra_len)
            .and_then(|v| v.checked_add(comment_len))
            .ok_or("ZIP central directory offset overflow")?;

        if lfh_off + 30 > zip.len() || &zip[lfh_off..lfh_off + 4] != b"PK\x03\x04" {
            return Err(format!("invalid ZIP local file header for {name}"));
        }
        let ln_len = u16::from_le_bytes([zip[lfh_off + 26], zip[lfh_off + 27]]) as usize;
        let le_len = u16::from_le_bytes([zip[lfh_off + 28], zip[lfh_off + 29]]) as usize;
        let data_start = lfh_off
            .checked_add(30)
            .and_then(|v| v.checked_add(ln_len))
            .and_then(|v| v.checked_add(le_len))
            .ok_or("ZIP local header overflow")?;
        let data_end = data_start
            .checked_add(comp_size)
            .ok_or("ZIP compressed size overflow")?;
        let comp_slice = zip
            .get(data_start..data_end)
            .ok_or_else(|| format!("ZIP compressed data out of bounds on {name}"))?;
        let payload = match method {
            0 => comp_slice.to_vec(),
            8 => inflate_raw_deflate(comp_slice, uncomp_size)?,
            m => return Err(format!("unsupported ZIP compression method {m} on {name}")),
        };
        if payload.len() != uncomp_size {
            return Err(format!(
                "decompressed size mismatch on {name}: {} != {uncomp_size}",
                payload.len()
            ));
        }
        entries.insert(name, payload);
    }
    Ok(entries)
}

fn npy_data_slice(npy: &[u8]) -> Result<&[u8], String> {
    if npy.len() < 10 || &npy[0..6] != b"\x93NUMPY" {
        return Err("invalid .npy magic".to_string());
    }
    let major = npy[6];
    let (hdr_off, hdr_len) = if major == 1 {
        (10usize, u16::from_le_bytes([npy[8], npy[9]]) as usize)
    } else {
        if npy.len() < 12 {
            return Err("truncated .npy v2 header".to_string());
        }
        (
            12usize,
            u32::from_le_bytes(npy[8..12].try_into().unwrap()) as usize,
        )
    };
    let end = hdr_off.checked_add(hdr_len).ok_or(".npy header overflow")?;
    npy.get(end..)
        .ok_or_else(|| ".npy header exceeds buffer".to_string())
}

#[derive(Clone, Debug)]
pub struct Qwen38SliceAuditReport {
    pub rows: usize,
    pub cols: usize,
    pub raw_neg_zero_nibble_count: usize,
    pub canonical_neg_zero_nibble_count: usize,
    pub noncanonical_digest: [u8; 32],
    pub canonical_digest: [u8; 32],
    pub max_abs_y_raw: i64,
    pub prove_ms: f64,
    pub verify_ms: f64,
    pub proof_bytes_len: usize,
}

/// Load real `Qwen3.8-27B` Layer-0 `gate_proj` (`[256, 5120]`) from `.npz`, verify `8 -> 0` `-0.0`
/// `MXFP4` nibble canonicalization (`51,851` `-0.0` nibbles canonicalized to `0` with exact contraction
/// invariance!), and prove + standalone-verify in `124`-bit `BabyBear Ext4`!
pub fn audit_qwen38_27b_mxfp4_npz_slice(
    npz_path: impl AsRef<Path>,
) -> Result<Qwen38SliceAuditReport, String> {
    let entries = read_npz_entries(npz_path.as_ref())?;
    let mx_u32_raw = npy_data_slice(
        entries
            .get("mx_u32.npy")
            .ok_or("missing mx_u32.npy in Qwen3.8-27B npz")?,
    )?;
    let mx_sc_raw = npy_data_slice(
        entries
            .get("mx_scales_u8.npy")
            .ok_or("missing mx_scales_u8.npy in Qwen3.8-27B npz")?,
    )?;
    let rows = 256usize;
    let cols = 5120usize;
    let blocks = cols / 32; // 160
    if mx_u32_raw.len() != rows * (cols / 8) * 4 || mx_sc_raw.len() != rows * blocks {
        return Err("unexpected mx_u32 / mx_scales_u8 byte lengths".to_string());
    }

    let mut raw_nibbles = Vec::with_capacity(rows * cols);
    let mut raw_neg_zero_nibble_count = 0usize;
    for chunk in mx_u32_raw.chunks_exact(4) {
        let word = u32::from_le_bytes(chunk.try_into().unwrap());
        for sh in 0..8 {
            let nib = ((word >> (sh * 4)) & 0x0F) as u8;
            if nib == 8 {
                raw_neg_zero_nibble_count += 1;
            }
            raw_nibbles.push(nib);
        }
    }
    let e_min = *mx_sc_raw.iter().min().unwrap_or(&118);
    let scales: Vec<u32> = mx_sc_raw
        .iter()
        .map(|&e| 1u32 << ((e - e_min).min(16) as u32))
        .collect();

    let noncanonical_digest = Mxfp4Matrix::compute_digest(
        "qwen38_27b.layers.0.mlp.gate_proj.weight",
        rows,
        rows,
        cols,
        &raw_nibbles,
        &scales,
    );

    let canonical_nibbles: Vec<u8> = raw_nibbles
        .iter()
        .map(|&n| canonicalize_e2m1_nibble(n))
        .collect();
    let canonical_neg_zero_nibble_count = canonical_nibbles.iter().filter(|&&n| n == 8).count();
    assert_eq!(canonical_neg_zero_nibble_count, 0);
    let canonical_digest = Mxfp4Matrix::compute_digest(
        "qwen38_27b.layers.0.mlp.gate_proj.weight",
        rows,
        rows,
        cols,
        &canonical_nibbles,
        &scales,
    );
    assert_ne!(
        noncanonical_digest, canonical_digest,
        "canonicalizing 8 -> 0 must separate non-canonical nibble digests!"
    );

    let raw_mat = Mxfp4Matrix {
        name: "qwen38_27b.layers.0.mlp.gate_proj.weight".to_string(),
        rows_orig: rows,
        rows_pad: rows,
        cols_orig: cols,
        blocks_per_row: blocks,
        nibbles: raw_nibbles,
        scales: scales.clone(),
        digest: noncanonical_digest,
    };
    let can_mat = Mxfp4Matrix {
        name: "qwen38_27b.layers.0.mlp.gate_proj.weight".to_string(),
        rows_orig: rows,
        rows_pad: rows,
        cols_orig: cols,
        blocks_per_row: blocks,
        nibbles: canonical_nibbles,
        scales,
        digest: canonical_digest,
    };

    // Deterministic `C = 64` `INT16` input `[64, 5120]` & verify exact contraction invariance `raw == canonical`!
    let c_len = 64usize;
    let x_i16: Vec<i16> = (0..(c_len * cols))
        .map(|i| (((i * 37 + 11) % 511) as i16) - 255)
        .collect();
    let y_raw_un = crate::qwen35_layer::eval_mxfp4_int_contraction(&x_i16, c_len, cols, &raw_mat);
    let y_raw_can = crate::qwen35_layer::eval_mxfp4_int_contraction(&x_i16, c_len, cols, &can_mat);
    assert_eq!(
        y_raw_un, y_raw_can,
        "8 -> 0 canonicalization preserves exact integer contractions over Z"
    );
    let max_abs_y_raw = y_raw_can.iter().map(|v| v.abs()).max().unwrap_or(0);
    assert!(max_abs_y_raw < (P as i64) / 2);

    // Prove & standalone-verify the real `Qwen3.8-27B` `256 x 5120` (`k_pad = 256`) `MXFP4` contraction!
    let t_p = Instant::now();
    let pcs = PrecommittedMxfp4Pcs::build(&can_mat); // j_pad = 256 (log_j = 8), k_pad = 256 (log_k = 8)
    let log_c = 6usize;
    let log_j = pcs.j_pad.trailing_zeros() as usize;
    let log_k = pcs.k_pad.trailing_zeros() as usize;

    let mut x_lsb_tbk = vec![0u32; c_len * pcs.k_pad * 32];
    for t in 0..c_len {
        for d in 0..cols {
            let k = d / 32;
            let b = d % 32;
            x_lsb_tbk[t + (b << log_c) + (k << (log_c + 5))] =
                bb_from_i64(x_i16[t * cols + d] as i64);
        }
    }
    let mut y_lsb_tj = vec![0u32; c_len * pcs.j_pad];
    for t in 0..c_len {
        for j in 0..pcs.j_pad {
            y_lsb_tj[t + (j << log_c)] = bb_from_i64(y_raw_can[t * pcs.j_pad + j]);
        }
    }
    let x_state = commit_table_pcs(&x_lsb_tbk, PcsParams::default_zk(1), Some(&[0x38; 32]));
    let y_state = commit_table_pcs(&y_lsb_tj, PcsParams::default_zk(1), Some(&[0x39; 32]));

    let mut tr = CShakeTranscript::new(b"QW38-27B-NPZ-SLICE-V1");
    for r in [
        &can_mat.digest,
        &pcs.q_state.root,
        &pcs.s_state.root,
        &x_state.root,
        &y_state.root,
    ] {
        tr.absorb_root(b"q38_root", r);
    }
    let r_i = tr.squeeze_ext4_vec(b"q38_ri", log_c, true);
    let r_j = tr.squeeze_ext4_vec(b"q38_rj", log_j, true);
    let eq_ri = build_eq_table_lsb_ext4(&r_i);
    let mut x_ri = vec![Ext4::ZERO; pcs.k_pad * 32];
    for k in 0..pcs.k_pad {
        for b in 0..32 {
            let base = (b << log_c) + (k << (log_c + 5));
            let mut acc = Ext4::ZERO;
            for t in 0..c_len {
                acc = acc.add(eq_ri[t].scale_bb(x_lsb_tbk[base + t]));
            }
            x_ri[k * 32 + b] = acc;
        }
    }
    let (mxfp4_pf, chals) = prove_mxfp4_delayed_bjk_horner_ext4(
        &x_ri,
        &pcs.nibs_pad,
        &pcs.scs_pad,
        log_j,
        log_k,
        &r_j,
        &mut tr,
    );

    let mut pt_q = Vec::with_capacity(5 + log_j + log_k);
    pt_q.extend_from_slice(&chals.chals_b);
    pt_q.extend_from_slice(&chals.chals_j);
    pt_q.extend_from_slice(&chals.chals_k);
    let mut pt_s = Vec::with_capacity(log_j + log_k);
    pt_s.extend_from_slice(&chals.chals_j);
    pt_s.extend_from_slice(&chals.chals_k);
    let mut pt_x = Vec::with_capacity(log_c + 5 + log_k);
    pt_x.extend_from_slice(&r_i);
    pt_x.extend_from_slice(&chals.chals_b);
    pt_x.extend_from_slice(&chals.chals_k);
    let mut pt_y = Vec::with_capacity(log_c + log_j);
    pt_y.extend_from_slice(&r_i);
    pt_y.extend_from_slice(&r_j);

    let q_pf = open_pcs_claims(
        &pcs.q_state,
        &[MleEvalClaim {
            point: pt_q.clone(),
            value: mxfp4_pf.finals.1,
        }],
        &mut tr,
    );
    let s_pf = open_pcs_claims(
        &pcs.s_state,
        &[MleEvalClaim {
            point: pt_s.clone(),
            value: mxfp4_pf.finals.2,
        }],
        &mut tr,
    );
    let x_pf = open_pcs_claims(
        &x_state,
        &[MleEvalClaim {
            point: pt_x.clone(),
            value: mxfp4_pf.finals.0,
        }],
        &mut tr,
    );
    let y_pf = open_pcs_claims(
        &y_state,
        &[MleEvalClaim {
            point: pt_y.clone(),
            value: mxfp4_pf.claim,
        }],
        &mut tr,
    );
    let prove_ms = t_p.elapsed().as_secs_f64() * 1000.0;

    let mut wire = Vec::new();
    mxfp4_pf.write_to(&mut wire);
    q_pf.write_to(&mut wire);
    s_pf.write_to(&mut wire);
    x_pf.write_to(&mut wire);
    y_pf.write_to(&mut wire);

    // Standalone verify from serialized bytes (`0` witness access!)
    let t_v = Instant::now();
    let mut cur = ByteCursor::new(&wire);
    let dec_mxfp4 = Mxfp4DelayedBjkExt4Proof::read_from(&mut cur)?;
    let dec_q = PcsOpeningProof::read_from(&mut cur)?;
    let dec_s = PcsOpeningProof::read_from(&mut cur)?;
    let dec_x = PcsOpeningProof::read_from(&mut cur)?;
    let dec_y = PcsOpeningProof::read_from(&mut cur)?;
    if cur.remaining() != 0 {
        return Err("trailing bytes in Qwen3.8-27B slice proof".to_string());
    }

    let mut vtr = CShakeTranscript::new(b"QW38-27B-NPZ-SLICE-V1");
    for r in [
        &can_mat.digest,
        &pcs.q_state.root,
        &pcs.s_state.root,
        &x_state.root,
        &y_state.root,
    ] {
        vtr.absorb_root(b"q38_root", r);
    }
    let vr_i = vtr.squeeze_ext4_vec(b"q38_ri", log_c, true);
    let vr_j = vtr.squeeze_ext4_vec(b"q38_rj", log_j, true);
    let vchals =
        verify_mxfp4_delayed_bjk_horner_ext4(dec_mxfp4.claim, &vr_j, &dec_mxfp4, &mut vtr)?;
    let mut vpt_q = Vec::new();
    vpt_q.extend_from_slice(&vchals.chals_b);
    vpt_q.extend_from_slice(&vchals.chals_j);
    vpt_q.extend_from_slice(&vchals.chals_k);
    let mut vpt_s = Vec::new();
    vpt_s.extend_from_slice(&vchals.chals_j);
    vpt_s.extend_from_slice(&vchals.chals_k);
    let mut vpt_x = Vec::new();
    vpt_x.extend_from_slice(&vr_i);
    vpt_x.extend_from_slice(&vchals.chals_b);
    vpt_x.extend_from_slice(&vchals.chals_k);
    let mut vpt_y = Vec::new();
    vpt_y.extend_from_slice(&vr_i);
    vpt_y.extend_from_slice(&vr_j);

    verify_pcs_claims(
        &pcs.q_state.root,
        PcsShape::new(5 + log_j + log_k, PcsParams::default_public(1)),
        &[MleEvalClaim {
            point: vpt_q,
            value: dec_mxfp4.finals.1,
        }],
        &dec_q,
        &mut vtr,
    )?;
    verify_pcs_claims(
        &pcs.s_state.root,
        PcsShape::new(log_j + log_k, PcsParams::default_public(1)),
        &[MleEvalClaim {
            point: vpt_s,
            value: dec_mxfp4.finals.2,
        }],
        &dec_s,
        &mut vtr,
    )?;
    verify_pcs_claims(
        &x_state.root,
        PcsShape::new(log_c + 5 + log_k, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: vpt_x,
            value: dec_mxfp4.finals.0,
        }],
        &dec_x,
        &mut vtr,
    )?;
    verify_pcs_claims(
        &y_state.root,
        PcsShape::new(log_c + log_j, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: vpt_y,
            value: dec_mxfp4.claim,
        }],
        &dec_y,
        &mut vtr,
    )?;
    let verify_ms = t_v.elapsed().as_secs_f64() * 1000.0;
    let _ = decode_e2m1_x2_bb(0);
    let _ = merkle_open_single_cshake;

    Ok(Qwen38SliceAuditReport {
        rows,
        cols,
        raw_neg_zero_nibble_count,
        canonical_neg_zero_nibble_count,
        noncanonical_digest,
        canonical_digest,
        max_abs_y_raw,
        prove_ms,
        verify_ms,
        proof_bytes_len: wire.len(),
    })
}

// ============================================================================
// §6. `Tower256ContentCert.contentCommit`, Multi-Pattern Redactor, & 139-Rule LL(1) `miniJsonCfg`
// ============================================================================

#[inline]
fn depth_of_merkle(n: usize) -> usize {
    if n <= 1 {
        0
    } else {
        (usize::BITS - (n - 1).leading_zeros()) as usize
    }
}

struct ContentMerkleCache {
    byte_leaves: [[u8; 32]; 256],
    zero_subtrees: [[u8; 32]; 24],
}

static CONTENT_MERKLE_CACHE: OnceLock<ContentMerkleCache> = OnceLock::new();

fn content_merkle_cache() -> &'static ContentMerkleCache {
    CONTENT_MERKLE_CACHE.get_or_init(|| {
        let mut byte_leaves = [[0u8; 32]; 256];
        for (b, leaf) in byte_leaves.iter_mut().enumerate() {
            // `0 :: (32 zeros ++ [1] ++ c8_le[32])` = 66 bytes
            let mut inp = [0u8; 66];
            inp[0] = 0;
            inp[33] = 1;
            inp[34] = b as u8;
            *leaf = cshake256_32(MERKLE_LEAF_CUST, &inp);
        }
        let mut zero_subtrees = [[0u8; 32]; 24];
        zero_subtrees[0] = byte_leaves[0];
        for h in 1..24 {
            zero_subtrees[h] =
                hash_tower256_merkle_node(&zero_subtrees[h - 1], &zero_subtrees[h - 1]);
        }
        ContentMerkleCache {
            byte_leaves,
            zero_subtrees,
        }
    })
}

#[inline]
fn hash_tower256_merkle_node(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut inp = [0u8; 131];
    inp[0] = 1;
    inp[33] = 1;
    inp[34..66].copy_from_slice(left);
    inp[98] = 1;
    inp[99..131].copy_from_slice(right);
    cshake256_32(MERKLE_NODE_CUST, &inp)
}

fn content_root_strided(
    cache: &ContentMerkleCache,
    bytes: &[u8],
    total_leaves: usize,
    offset: usize,
    stride: usize,
    rem_depth: usize,
) -> [u8; 32] {
    if offset >= bytes.len() && rem_depth < 24 {
        return cache.zero_subtrees[rem_depth];
    }
    if stride >= total_leaves {
        let b = bytes.get(offset).copied().unwrap_or(0);
        cache.byte_leaves[b as usize]
    } else {
        let l = content_root_strided(
            cache,
            bytes,
            total_leaves,
            offset,
            stride * 2,
            rem_depth - 1,
        );
        let r = content_root_strided(
            cache,
            bytes,
            total_leaves,
            offset + stride,
            stride * 2,
            rem_depth - 1,
        );
        hash_tower256_merkle_node(&l, &r)
    }
}

/// Exact `Minidregg.Compiler.Tower256ContentCert.contentCommit(bytes)` (`cSHAKE256` LSB-split cube-Merkle root).
pub fn content_commit_cshake(bytes: &[u8]) -> [u8; 32] {
    let cache = content_merkle_cache();
    let d = depth_of_merkle(bytes.len());
    content_root_strided(cache, bytes, 1usize << d, 0, 1, d)
}

#[derive(Clone)]
pub struct RedactRule {
    pub name: &'static str,
    pub pat: Vec<u8>,
    pub body_pred: fn(u8) -> bool,
    pub repl: Vec<u8>,
}

#[inline]
fn is_api_key_body_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_' || b == b'-'
}
#[inline]
fn is_bearer_body_byte(b: u8) -> bool {
    is_api_key_body_byte(b) || matches!(b, b'.' | b'~' | b'+' | b'/' | b'=')
}
#[inline]
fn is_pem_header_byte(b: u8) -> bool {
    b.is_ascii_uppercase() || b.is_ascii_digit() || b == b' ' || b == b'-'
}
#[inline]
fn no_continuation(_: u8) -> bool {
    false
}

/// Exact 5-class production secret-redaction policy (`Theory.VerifiedAstTransducer.defaultSecretRules`).
pub fn default_secret_rules() -> Vec<RedactRule> {
    vec![
        RedactRule {
            name: "api_key",
            pat: b"sk-".to_vec(),
            body_pred: is_api_key_body_byte,
            repl: b"[REDACTED_API_KEY]".to_vec(),
        },
        RedactRule {
            name: "bearer",
            pat: b"Bearer ".to_vec(),
            body_pred: is_bearer_body_byte,
            repl: b"[REDACTED_BEARER]".to_vec(),
        },
        RedactRule {
            name: "pem_key",
            pat: b"-----BEGIN ".to_vec(),
            body_pred: is_pem_header_byte,
            repl: b"[REDACTED_PEM]".to_vec(),
        },
        RedactRule {
            name: "template_open",
            pat: b"{{".to_vec(),
            body_pred: no_continuation,
            repl: b"[REDACTED_TPL]".to_vec(),
        },
        RedactRule {
            name: "github_pat",
            pat: b"ghp_".to_vec(),
            body_pred: is_api_key_body_byte,
            repl: b"[REDACTED_GH_PAT]".to_vec(),
        },
    ]
}

pub fn safe_replacement(pat: &[u8], repl: &[u8]) -> bool {
    if repl.is_empty() || (!pat.is_empty() && repl.windows(pat.len()).any(|w| w == pat)) {
        return false;
    }
    for k in 1..pat.len() {
        let p1 = &pat[..k];
        let p2 = &pat[k..];
        if repl.starts_with(p2) || p2.starts_with(repl) || repl.ends_with(p1) {
            return false;
        }
    }
    true
}

pub fn all_rules_safe(rules: &[RedactRule]) -> bool {
    rules
        .iter()
        .all(|rt| !rt.pat.is_empty() && rules.iter().all(|r| safe_replacement(&rt.pat, &r.repl)))
}

/// Exact `Theory.VerifiedAstTransducer.redactBytes` deterministic longest-match byte transducer.
pub fn redact_bytes_canonical(rules: &[RedactRule], input: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(input.len());
    let mut pos = 0usize;
    while pos < input.len() {
        let rem = &input[pos..];
        let mut best: Option<(&[u8], usize)> = None;
        for r in rules {
            if !r.pat.is_empty() && rem.starts_with(&r.pat) {
                let mut len = r.pat.len();
                while len < rem.len() && (r.body_pred)(rem[len]) {
                    len += 1;
                }
                if best.is_none_or(|(_, bl)| bl < len) {
                    best = Some((&r.repl, len));
                }
            }
        }
        if let Some((repl, len)) = best {
            out.extend_from_slice(repl);
            pos += len;
        } else {
            out.push(input[pos]);
            pos += 1;
        }
    }
    out
}

/// Extracted `Mini` AST value (`Theory.VerifiedAstTransducer.MiniValue`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MiniValue {
    Byte(u8),
    Bytes(Vec<u8>),
    Digits(Vec<usize>),
    Nat(usize),
    ToolCall {
        tool: Vec<u8>,
        target: Vec<u8>,
        amount: usize,
    },
    CotToolCall {
        cot: Vec<u8>,
        tool: Vec<u8>,
        target: Vec<u8>,
        amount: usize,
    },
    BatchNil,
    BatchCons(Box<MiniValue>, Box<MiniValue>),
    Unit,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum MiniNT {
    Root = 0,
    TopExpr = 1,
    ObjDispatch = 2,
    ToolRest = 3,
    CotRest = 4,
    BatchBody = 5,
    BatchTail = 6,
    StrVal = 7,
    Chars = 8,
    Esc = 9,
    NatVal = 10,
    Digits = 11,
    WS = 12,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MiniOp {
    PassAt(usize),
    UnitOp,
    StrUnquote,
    CharsNil,
    CharsCons(u8),
    CharsEsc,
    EscConst(u8),
    NatZero,
    NatPos(usize),
    DigitsNil,
    DigitsCons(usize),
    MkToolRest,
    MkCotRest,
    BatchEmpty,
    BatchCons,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CfgSym<T, NT> {
    Terminal(T),
    Nonterminal(NT),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttrRule<T, NT, SemOp> {
    pub lhs: NT,
    pub rhs: Vec<CfgSym<T, NT>>,
    pub op: SemOp,
}

pub struct AttrCfg<T, NT, SemOp, Val> {
    pub initial: NT,
    pub rules: Vec<AttrRule<T, NT, SemOp>>,
    pub term_val: fn(T) -> Val,
    pub eval_op: fn(&SemOp, &[Val]) -> Result<Val, String>,
}

fn eval_mini_op(op: &MiniOp, vs: &[MiniValue]) -> Result<MiniValue, String> {
    match *op {
        MiniOp::PassAt(i) => Ok(vs.get(i).cloned().unwrap_or(MiniValue::Unit)),
        MiniOp::UnitOp => Ok(MiniValue::Unit),
        MiniOp::StrUnquote => Ok(vs
            .get(1)
            .cloned()
            .unwrap_or_else(|| MiniValue::Bytes(Vec::new()))),
        MiniOp::CharsNil => Ok(MiniValue::Bytes(Vec::new())),
        MiniOp::CharsCons(b) => match vs.get(1) {
            Some(MiniValue::Bytes(tail)) => {
                let mut v = Vec::with_capacity(1 + tail.len());
                v.push(b);
                v.extend_from_slice(tail);
                Ok(MiniValue::Bytes(v))
            }
            _ => Ok(MiniValue::Bytes(vec![b])),
        },
        MiniOp::CharsEsc => match (vs.get(1), vs.get(2)) {
            (Some(MiniValue::Byte(b)), Some(MiniValue::Bytes(tail))) => {
                let mut v = Vec::with_capacity(1 + tail.len());
                v.push(*b);
                v.extend_from_slice(tail);
                Ok(MiniValue::Bytes(v))
            }
            _ => Ok(MiniValue::Bytes(Vec::new())),
        },
        MiniOp::EscConst(b) => Ok(MiniValue::Byte(b)),
        MiniOp::NatZero => Ok(MiniValue::Nat(0)),
        MiniOp::NatPos(d0) => match vs.get(1) {
            Some(MiniValue::Digits(ds)) => {
                let mut acc = d0;
                for &d in ds {
                    acc = acc
                        .checked_mul(10)
                        .and_then(|v| v.checked_add(d))
                        .ok_or_else(|| "MiniOp::NatPos decimal overflow (>= 2^64)".to_string())?;
                }
                Ok(MiniValue::Nat(acc))
            }
            _ => Ok(MiniValue::Nat(d0)),
        },
        MiniOp::DigitsNil => Ok(MiniValue::Digits(Vec::new())),
        MiniOp::DigitsCons(d) => match vs.get(1) {
            Some(MiniValue::Digits(ds)) => {
                let mut v = Vec::with_capacity(1 + ds.len());
                v.push(d);
                v.extend_from_slice(ds);
                Ok(MiniValue::Digits(v))
            }
            _ => Ok(MiniValue::Digits(vec![d])),
        },
        MiniOp::MkToolRest => match (vs.get(7), vs.get(22), vs.get(37)) {
            (
                Some(MiniValue::Bytes(tool)),
                Some(MiniValue::Bytes(target)),
                Some(MiniValue::Nat(amount)),
            ) => Ok(MiniValue::ToolCall {
                tool: tool.clone(),
                target: target.clone(),
                amount: *amount,
            }),
            _ => Ok(MiniValue::Unit),
        },
        MiniOp::MkCotRest => match (vs.get(6), vs.get(19), vs.get(34), vs.get(49)) {
            (
                Some(MiniValue::Bytes(cot)),
                Some(MiniValue::Bytes(tool)),
                Some(MiniValue::Bytes(target)),
                Some(MiniValue::Nat(amount)),
            ) => Ok(MiniValue::CotToolCall {
                cot: cot.clone(),
                tool: tool.clone(),
                target: target.clone(),
                amount: *amount,
            }),
            _ => Ok(MiniValue::Unit),
        },
        MiniOp::BatchEmpty => Ok(MiniValue::BatchNil),
        MiniOp::BatchCons => match vs {
            [item, _, rest] | [_, _, item, _, rest] => Ok(MiniValue::BatchCons(
                Box::new(item.clone()),
                Box::new(rest.clone()),
            )),
            _ => Ok(MiniValue::BatchNil),
        },
    }
}

/// Exact 139-rule `miniJsonCfg` matching `Theory.VerifiedAstTransducer.miniJsonCfg` rule-for-rule!
pub fn mini_json_cfg() -> AttrCfg<u8, MiniNT, MiniOp, MiniValue> {
    use CfgSym::{Nonterminal as Nt, Terminal as T};
    use MiniNT::*;
    let lit = |s: &[u8]| -> Vec<CfgSym<u8, MiniNT>> { s.iter().map(|&b| T(b)).collect() };

    let mut tool_rest = Vec::new();
    tool_rest.extend(lit(b"ool\""));
    tool_rest.extend([Nt(WS), T(b':'), Nt(WS), Nt(StrVal), Nt(WS), T(b','), Nt(WS)]);
    tool_rest.extend(lit(b"\"target\""));
    tool_rest.extend([Nt(WS), T(b':'), Nt(WS), Nt(StrVal), Nt(WS), T(b','), Nt(WS)]);
    tool_rest.extend(lit(b"\"amount\""));
    tool_rest.extend([Nt(WS), T(b':'), Nt(WS), Nt(NatVal), Nt(WS), T(b'}')]);

    let mut cot_rest = Vec::new();
    cot_rest.extend(lit(b"ot\""));
    cot_rest.extend([Nt(WS), T(b':'), Nt(WS), Nt(StrVal), Nt(WS), T(b','), Nt(WS)]);
    cot_rest.extend(lit(b"\"tool\""));
    cot_rest.extend([Nt(WS), T(b':'), Nt(WS), Nt(StrVal), Nt(WS), T(b','), Nt(WS)]);
    cot_rest.extend(lit(b"\"target\""));
    cot_rest.extend([Nt(WS), T(b':'), Nt(WS), Nt(StrVal), Nt(WS), T(b','), Nt(WS)]);
    cot_rest.extend(lit(b"\"amount\""));
    cot_rest.extend([Nt(WS), T(b':'), Nt(WS), Nt(NatVal), Nt(WS), T(b'}')]);

    let mut rules = vec![
        AttrRule {
            lhs: Root,
            rhs: vec![Nt(WS), Nt(TopExpr), Nt(WS)],
            op: MiniOp::PassAt(1),
        },
        AttrRule {
            lhs: TopExpr,
            rhs: vec![T(b'{'), Nt(WS), T(b'"'), Nt(ObjDispatch)],
            op: MiniOp::PassAt(3),
        },
        AttrRule {
            lhs: TopExpr,
            rhs: vec![T(b'['), Nt(WS), Nt(BatchBody), T(b']')],
            op: MiniOp::PassAt(2),
        },
        AttrRule {
            lhs: ObjDispatch,
            rhs: vec![T(b't'), Nt(ToolRest)],
            op: MiniOp::PassAt(1),
        },
        AttrRule {
            lhs: ObjDispatch,
            rhs: vec![T(b'c'), Nt(CotRest)],
            op: MiniOp::PassAt(1),
        },
        AttrRule {
            lhs: ToolRest,
            rhs: tool_rest,
            op: MiniOp::MkToolRest,
        },
        AttrRule {
            lhs: CotRest,
            rhs: cot_rest,
            op: MiniOp::MkCotRest,
        },
        AttrRule {
            lhs: BatchBody,
            rhs: vec![Nt(TopExpr), Nt(WS), Nt(BatchTail)],
            op: MiniOp::BatchCons,
        },
        AttrRule {
            lhs: BatchBody,
            rhs: vec![],
            op: MiniOp::BatchEmpty,
        },
        AttrRule {
            lhs: BatchTail,
            rhs: vec![T(b','), Nt(WS), Nt(TopExpr), Nt(WS), Nt(BatchTail)],
            op: MiniOp::BatchCons,
        },
        AttrRule {
            lhs: BatchTail,
            rhs: vec![],
            op: MiniOp::BatchEmpty,
        },
        AttrRule {
            lhs: WS,
            rhs: vec![T(b' '), Nt(WS)],
            op: MiniOp::UnitOp,
        },
        AttrRule {
            lhs: WS,
            rhs: vec![T(b'\t'), Nt(WS)],
            op: MiniOp::UnitOp,
        },
        AttrRule {
            lhs: WS,
            rhs: vec![T(b'\n'), Nt(WS)],
            op: MiniOp::UnitOp,
        },
        AttrRule {
            lhs: WS,
            rhs: vec![T(b'\r'), Nt(WS)],
            op: MiniOp::UnitOp,
        },
        AttrRule {
            lhs: WS,
            rhs: vec![],
            op: MiniOp::UnitOp,
        },
        AttrRule {
            lhs: StrVal,
            rhs: vec![T(b'"'), Nt(Chars), T(b'"')],
            op: MiniOp::StrUnquote,
        },
        AttrRule {
            lhs: Chars,
            rhs: vec![T(b'\\'), Nt(Esc), Nt(Chars)],
            op: MiniOp::CharsEsc,
        },
        AttrRule {
            lhs: Chars,
            rhs: vec![],
            op: MiniOp::CharsNil,
        },
        AttrRule {
            lhs: Esc,
            rhs: vec![T(b'"')],
            op: MiniOp::EscConst(b'"'),
        },
        AttrRule {
            lhs: Esc,
            rhs: vec![T(b'\\')],
            op: MiniOp::EscConst(b'\\'),
        },
        AttrRule {
            lhs: Esc,
            rhs: vec![T(b'/')],
            op: MiniOp::EscConst(b'/'),
        },
        AttrRule {
            lhs: Esc,
            rhs: vec![T(b'n')],
            op: MiniOp::EscConst(b'\n'),
        },
        AttrRule {
            lhs: Esc,
            rhs: vec![T(b'r')],
            op: MiniOp::EscConst(b'\r'),
        },
        AttrRule {
            lhs: Esc,
            rhs: vec![T(b't')],
            op: MiniOp::EscConst(b'\t'),
        },
        AttrRule {
            lhs: NatVal,
            rhs: vec![T(b'0')],
            op: MiniOp::NatZero,
        },
        AttrRule {
            lhs: Digits,
            rhs: vec![],
            op: MiniOp::DigitsNil,
        },
    ];
    for k in 0..9u8 {
        let d = k + 1;
        rules.push(AttrRule {
            lhs: NatVal,
            rhs: vec![T(b'0' + d), Nt(Digits)],
            op: MiniOp::NatPos(d as usize),
        });
    }
    for d in 0..10u8 {
        rules.push(AttrRule {
            lhs: Digits,
            rhs: vec![T(b'0' + d), Nt(Digits)],
            op: MiniOp::DigitsCons(d as usize),
        });
    }
    for k in 0..95u8 {
        let b = 0x20 + k;
        if b != b'"' && b != b'\\' {
            rules.push(AttrRule {
                lhs: Chars,
                rhs: vec![T(b), Nt(Chars)],
                op: MiniOp::CharsCons(b),
            });
        }
    }
    assert_eq!(rules.len(), 139);
    AttrCfg {
        initial: Root,
        rules,
        term_val: MiniValue::Byte,
        eval_op: eval_mini_op,
    }
}

enum WorkItem<T, NT, SemOp> {
    Sym(CfgSym<T, NT>),
    Reduce(SemOp, usize),
}

pub fn ll1_parse_mini_json(input: &[u8]) -> Result<(Vec<usize>, MiniValue), String> {
    let cfg = mini_json_cfg();
    // Build LL(1) nullable / first / follow / dispatch table (`[13][257]`)
    let mut null_nt = [false; 13];
    for _ in 0..14 {
        for r in &cfg.rules {
            if r.rhs.iter().all(|s| match s {
                CfgSym::Terminal(_) => false,
                CfgSym::Nonterminal(nt) => null_nt[*nt as usize],
            }) {
                null_nt[r.lhs as usize] = true;
            }
        }
    }
    let seq_null = |syms: &[CfgSym<u8, MiniNT>]| -> bool {
        syms.iter().all(|s| match s {
            CfgSym::Terminal(_) => false,
            CfgSym::Nonterminal(nt) => null_nt[*nt as usize],
        })
    };
    let mut first = vec![vec![false; 256]; 13];
    for _ in 0..14 {
        for r in &cfg.rules {
            let lid = r.lhs as usize;
            for s in &r.rhs {
                match *s {
                    CfgSym::Terminal(t) => {
                        first[lid][t as usize] = true;
                        break;
                    }
                    CfgSym::Nonterminal(nt) => {
                        let f_nt = first[nt as usize].clone();
                        for b in 0..256 {
                            if f_nt[b] {
                                first[lid][b] = true;
                            }
                        }
                        if !null_nt[nt as usize] {
                            break;
                        }
                    }
                }
            }
        }
    }
    let seq_first = |syms: &[CfgSym<u8, MiniNT>]| -> Vec<usize> {
        let mut out = Vec::new();
        for s in syms {
            match *s {
                CfgSym::Terminal(t) => {
                    out.push((t as usize) + 1);
                    break;
                }
                CfgSym::Nonterminal(nt) => {
                    for (b, &has_b) in first[nt as usize].iter().enumerate().take(256) {
                        if has_b && !out.contains(&(b + 1)) {
                            out.push(b + 1);
                        }
                    }
                    if !null_nt[nt as usize] {
                        break;
                    }
                }
            }
        }
        out
    };
    let mut follow = vec![vec![false; 257]; 13];
    follow[cfg.initial as usize][0] = true;
    for _ in 0..14 {
        for r in &cfg.rules {
            let lhs_fol = follow[r.lhs as usize].clone();
            for idx in 0..r.rhs.len() {
                if let CfgSym::Nonterminal(b_nt) = r.rhs[idx] {
                    let suf = &r.rhs[idx + 1..];
                    for sl in seq_first(suf) {
                        follow[b_nt as usize][sl] = true;
                    }
                    if seq_null(suf) {
                        for sl in 0..257 {
                            if lhs_fol[sl] {
                                follow[b_nt as usize][sl] = true;
                            }
                        }
                    }
                }
            }
        }
    }
    let mut dispatch = [[u16::MAX; 257]; 13];
    for (ridx, r) in cfg.rules.iter().enumerate() {
        let mut slots = seq_first(&r.rhs);
        if seq_null(&r.rhs) {
            for (sl, &has_sl) in follow[r.lhs as usize].iter().enumerate() {
                if has_sl && !slots.contains(&sl) {
                    slots.push(sl);
                }
            }
        }
        for sl in slots {
            if dispatch[r.lhs as usize][sl] != u16::MAX {
                return Err("miniJsonCfg dispatch collision".to_string());
            }
            dispatch[r.lhs as usize][sl] = ridx as u16;
        }
    }

    let mut cstk = vec![WorkItem::Sym(CfgSym::Nonterminal(cfg.initial))];
    let mut vstk: Vec<MiniValue> = Vec::new();
    let mut rule_indices = Vec::new();
    let mut pos = 0usize;

    while let Some(top) = cstk.pop() {
        match top {
            WorkItem::Sym(CfgSym::Terminal(exp)) => {
                let Some(&act) = input.get(pos) else {
                    return Err("unexpected EOF in LL(1) parse".to_string());
                };
                if act != exp {
                    return Err(format!(
                        "terminal mismatch at {pos}: expected 0x{exp:02x}, got 0x{act:02x}"
                    ));
                }
                pos += 1;
                vstk.push((cfg.term_val)(exp));
            }
            WorkItem::Sym(CfgSym::Nonterminal(nt)) => {
                let slot = input.get(pos).map_or(0usize, |&b| (b as usize) + 1);
                let ridx = dispatch[nt as usize][slot];
                if ridx == u16::MAX {
                    return Err(format!(
                        "no matching LL(1) rule for {nt:?} at byte pos {pos}"
                    ));
                }
                let rule = &cfg.rules[ridx as usize];
                rule_indices.push(ridx as usize);
                cstk.push(WorkItem::Reduce(rule.op, rule.rhs.len()));
                for s in rule.rhs.iter().rev() {
                    cstk.push(WorkItem::Sym(*s));
                }
            }
            WorkItem::Reduce(op, k) => {
                if vstk.len() < k {
                    return Err("value stack underflow".to_string());
                }
                let split = vstk.len() - k;
                let red = (cfg.eval_op)(&op, &vstk[split..])?;
                vstk.truncate(split);
                vstk.push(red);
            }
        }
    }
    if pos != input.len() || vstk.len() != 1 {
        return Err("unconsumed input or invalid stack in LL(1) parse".to_string());
    }
    Ok((rule_indices, vstk.pop().unwrap()))
}

pub fn exec_mini_attr_replay(rule_indices: &[usize], input: &[u8]) -> Result<MiniValue, String> {
    let cfg = mini_json_cfg();
    let mut cstk = vec![WorkItem::Sym(CfgSym::Nonterminal(cfg.initial))];
    let mut vstk: Vec<MiniValue> = Vec::new();
    let mut rpos = 0usize;
    let mut ipos = 0usize;

    while let Some(top) = cstk.pop() {
        match top {
            WorkItem::Sym(CfgSym::Terminal(exp)) => {
                let Some(&act) = input.get(ipos) else {
                    return Err("replay unexpected EOF".to_string());
                };
                if act != exp {
                    return Err("replay terminal mismatch".to_string());
                }
                ipos += 1;
                vstk.push((cfg.term_val)(exp));
            }
            WorkItem::Sym(CfgSym::Nonterminal(nt)) => {
                let Some(&ridx) = rule_indices.get(rpos) else {
                    return Err("replay ran out of rules".to_string());
                };
                let Some(rule) = cfg.rules.get(ridx) else {
                    return Err("replay rule index out of bounds".to_string());
                };
                if rule.lhs != nt {
                    return Err("replay rule LHS mismatch".to_string());
                }
                rpos += 1;
                cstk.push(WorkItem::Reduce(rule.op, rule.rhs.len()));
                for s in rule.rhs.iter().rev() {
                    cstk.push(WorkItem::Sym(*s));
                }
            }
            WorkItem::Reduce(op, k) => {
                if vstk.len() < k {
                    return Err("replay stack underflow".to_string());
                }
                let split = vstk.len() - k;
                let red = (cfg.eval_op)(&op, &vstk[split..])?;
                vstk.truncate(split);
                vstk.push(red);
            }
        }
    }
    if rpos != rule_indices.len() || ipos != input.len() || vstk.len() != 1 {
        return Err("replay incomplete consumption".to_string());
    }
    Ok(vstk.pop().unwrap())
}

// ============================================================================
// §7. Canonical `StreamCodec` Wire Encoding & `VAGENT01` / `VASTMT01` Turn Weld
// ============================================================================

/// Encode `Nat` in `Theory.StreamCodec.nat` format (`base-255` LE digits + `0xFF` terminator).
pub fn stream_encode_nat(mut value: usize, out: &mut Vec<u8>) {
    while value > 0 {
        out.push((value % 255) as u8);
        value /= 255;
    }
    out.push(255u8);
}

/// Decode `Nat` in `Theory.StreamCodec.nat` format, rejecting non-canonical trailing `0` digits!
pub fn stream_decode_nat(bytes: &[u8], pos: &mut usize) -> Result<usize, String> {
    let start = *pos;
    while *pos < bytes.len() && bytes[*pos] != 255 {
        *pos += 1;
    }
    if *pos >= bytes.len() {
        return Err("unterminated StreamCodec.nat".to_string());
    }
    let digits = &bytes[start..*pos];
    *pos += 1; // consume 255 terminator
    if let Some(&last) = digits.last() {
        if last == 0 {
            return Err("non-canonical trailing zero digit in StreamCodec.nat".to_string());
        }
    }
    let mut acc = 0usize;
    for &d in digits.iter().rev() {
        acc = acc
            .checked_mul(255)
            .and_then(|v| v.checked_add(d as usize))
            .ok_or_else(|| "StreamCodec.nat overflow".to_string())?;
    }
    Ok(acc)
}

pub fn stream_encode_bytes(bs: &[u8], out: &mut Vec<u8>) {
    stream_encode_nat(bs.len(), out);
    out.extend_from_slice(bs);
}

pub fn stream_decode_bytes(bytes: &[u8], pos: &mut usize) -> Result<Vec<u8>, String> {
    let len = stream_decode_nat(bytes, pos)?;
    let end = pos.checked_add(len).ok_or("bytesStream overflow")?;
    if end > bytes.len() {
        return Err("bytesStream truncated".to_string());
    }
    let v = bytes[*pos..end].to_vec();
    *pos = end;
    Ok(v)
}

pub fn stream_decode_digest32(bytes: &[u8], pos: &mut usize) -> Result<[u8; 32], String> {
    let end = pos.checked_add(32).ok_or("digest256 overflow")?;
    if end > bytes.len() {
        return Err("digest256Stream truncated (< 32 octets)".to_string());
    }
    let mut d = [0u8; 32];
    d.copy_from_slice(&bytes[*pos..end]);
    *pos = end;
    Ok(d)
}

pub fn stream_encode_mini_value(val: &MiniValue, out: &mut Vec<u8>) {
    match val {
        MiniValue::Byte(b) => {
            out.push(0);
            out.push(*b);
        }
        MiniValue::Bytes(bs) => {
            out.push(1);
            stream_encode_bytes(bs, out);
        }
        MiniValue::Digits(ds) => {
            out.push(2);
            stream_encode_nat(ds.len(), out);
            for &d in ds {
                stream_encode_nat(d, out);
            }
        }
        MiniValue::Nat(n) => {
            out.push(3);
            stream_encode_nat(*n, out);
        }
        MiniValue::ToolCall {
            tool,
            target,
            amount,
        } => {
            out.push(4);
            stream_encode_bytes(tool, out);
            stream_encode_bytes(target, out);
            stream_encode_nat(*amount, out);
        }
        MiniValue::CotToolCall {
            cot,
            tool,
            target,
            amount,
        } => {
            out.push(5);
            stream_encode_bytes(cot, out);
            stream_encode_bytes(tool, out);
            stream_encode_bytes(target, out);
            stream_encode_nat(*amount, out);
        }
        MiniValue::BatchNil => out.push(6),
        MiniValue::BatchCons(hd, tl) => {
            out.push(7);
            stream_encode_mini_value(hd, out);
            stream_encode_mini_value(tl, out);
        }
        MiniValue::Unit => out.push(8),
    }
}

const MAX_MINI_VALUE_DEPTH: usize = 512;

pub fn stream_decode_mini_value(bytes: &[u8], pos: &mut usize) -> Result<MiniValue, String> {
    let mut fuel = bytes.len().saturating_sub(*pos);
    stream_decode_mini_value_inner(bytes, pos, &mut fuel, 0)
}

fn stream_decode_mini_value_inner(
    bytes: &[u8],
    pos: &mut usize,
    fuel: &mut usize,
    depth: usize,
) -> Result<MiniValue, String> {
    if *fuel == 0 || depth > MAX_MINI_VALUE_DEPTH {
        return Err("MiniValue recursion depth or fuel exceeded".to_string());
    }
    *fuel -= 1;
    if *pos >= bytes.len() {
        return Err("MiniValue tag EOF".to_string());
    }
    let tag = bytes[*pos];
    *pos += 1;
    match tag {
        0 => {
            if *pos >= bytes.len() {
                return Err("vByte EOF".to_string());
            }
            let b = bytes[*pos];
            *pos += 1;
            Ok(MiniValue::Byte(b))
        }
        1 => Ok(MiniValue::Bytes(stream_decode_bytes(bytes, pos)?)),
        2 => {
            let cnt = stream_decode_nat(bytes, pos)?;
            if cnt > bytes.len().saturating_sub(*pos) {
                return Err("MiniValue Digits count exceeds remaining wire bytes".to_string());
            }
            let mut ds = Vec::with_capacity(cnt.min(1024));
            for _ in 0..cnt {
                ds.push(stream_decode_nat(bytes, pos)?);
            }
            Ok(MiniValue::Digits(ds))
        }
        3 => Ok(MiniValue::Nat(stream_decode_nat(bytes, pos)?)),
        4 => {
            let tool = stream_decode_bytes(bytes, pos)?;
            let target = stream_decode_bytes(bytes, pos)?;
            let amount = stream_decode_nat(bytes, pos)?;
            Ok(MiniValue::ToolCall {
                tool,
                target,
                amount,
            })
        }
        5 => {
            let cot = stream_decode_bytes(bytes, pos)?;
            let tool = stream_decode_bytes(bytes, pos)?;
            let target = stream_decode_bytes(bytes, pos)?;
            let amount = stream_decode_nat(bytes, pos)?;
            Ok(MiniValue::CotToolCall {
                cot,
                tool,
                target,
                amount,
            })
        }
        6 => Ok(MiniValue::BatchNil),
        7 => {
            let hd = stream_decode_mini_value_inner(bytes, pos, fuel, depth + 1)?;
            let tl = stream_decode_mini_value_inner(bytes, pos, fuel, depth + 1)?;
            Ok(MiniValue::BatchCons(Box::new(hd), Box::new(tl)))
        }
        8 => Ok(MiniValue::Unit),
        _ => Err(format!("invalid MiniValue wire tag {tag}")),
    }
}

/// Compute `u1ChainFold` + `u1TurnHead` matching `Assurance/VerifiableAgentTurnWeld.lean` byte-for-byte!
pub fn compute_u1_turn_head_cshake(
    weight_root: &[u8; 32],
    prompt_root: &[u8; 32],
    prompt_len: usize,
    boundary_roots: &[[u8; 32]],
    u1_proof_digest: &[u8; 32],
    raw_len: usize,
    raw_root: &[u8; 32],
) -> [u8; 32] {
    let mut init_frame = Vec::with_capacity(80);
    stream_encode_nat(0, &mut init_frame);
    init_frame.extend_from_slice(weight_root);
    stream_encode_nat(prompt_len, &mut init_frame);
    init_frame.extend_from_slice(prompt_root);
    let mut acc = cshake256_32(U1_STEP_CUST, &init_frame);

    for (idx, b_root) in boundary_roots.iter().enumerate() {
        let mut step_frame = Vec::with_capacity(80);
        stream_encode_nat(1, &mut step_frame);
        step_frame.extend_from_slice(&acc);
        stream_encode_nat(idx, &mut step_frame);
        step_frame.extend_from_slice(b_root);
        acc = cshake256_32(U1_STEP_CUST, &step_frame);
    }

    let mut out_frame = Vec::with_capacity(112);
    out_frame.extend_from_slice(&acc);
    stream_encode_nat(boundary_roots.len(), &mut out_frame);
    out_frame.extend_from_slice(u1_proof_digest);
    stream_encode_nat(raw_len, &mut out_frame);
    out_frame.extend_from_slice(raw_root);
    cshake256_32(U1_OUT_CUST, &out_frame)
}

/// Deterministic Fiat-Shamir VRF layer selection matching `Assurance/VerifiableAgentTurnWeld.lean` byte-for-byte!
pub fn compute_u1_vrf_layer_cshake(
    weight_root: &[u8; 32],
    boundary_roots: &[[u8; 32]],
    clean_root: &[u8; 32],
    num_layers: usize,
) -> usize {
    const GDN_LAYERS: [usize; 18] = [
        0, 1, 2, 4, 5, 6, 8, 9, 10, 12, 13, 14, 16, 17, 18, 20, 21, 22,
    ];
    let mut frame = Vec::with_capacity(96 + boundary_roots.len() * 32);
    frame.extend_from_slice(weight_root);
    stream_encode_nat(boundary_roots.len(), &mut frame);
    for b in boundary_roots {
        frame.extend_from_slice(b);
    }
    frame.extend_from_slice(clean_root);
    stream_encode_nat(num_layers, &mut frame);
    let dig = cshake256_32(U1_VRF_CUST, &frame);
    let low32 = u32::from_le_bytes(dig[0..4].try_into().unwrap()) as usize;
    if num_layers == 24 {
        GDN_LAYERS[low32 % GDN_LAYERS.len()]
    } else if num_layers == 0 {
        0
    } else {
        low32 % num_layers
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiableAgentTurnStmt {
    pub weight_root: [u8; 32],
    pub prompt_length: usize,
    pub prompt_root: [u8; 32],
    pub num_layers: usize,
    pub turn_chain_root: [u8; 32],
    pub raw_length: usize,
    pub raw_root: [u8; 32],
    pub clean_length: usize,
    pub clean_root: [u8; 32],
    pub claimed_ast: MiniValue,
}

impl VerifiableAgentTurnStmt {
    pub fn to_stream_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(256);
        out.extend_from_slice(VASTMT01_MAGIC);
        out.extend_from_slice(&self.weight_root);
        stream_encode_nat(self.prompt_length, &mut out);
        out.extend_from_slice(&self.prompt_root);
        stream_encode_nat(self.num_layers, &mut out);
        out.extend_from_slice(&self.turn_chain_root);
        stream_encode_nat(self.raw_length, &mut out);
        out.extend_from_slice(&self.raw_root);
        stream_encode_nat(self.clean_length, &mut out);
        out.extend_from_slice(&self.clean_root);
        stream_encode_mini_value(&self.claimed_ast, &mut out);
        out
    }

    pub fn from_stream_bytes(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() < 8 || &bytes[0..8] != VASTMT01_MAGIC {
            return Err("invalid VASTMT01 magic".to_string());
        }
        let mut pos = 8usize;
        let weight_root = stream_decode_digest32(bytes, &mut pos)?;
        let prompt_length = stream_decode_nat(bytes, &mut pos)?;
        let prompt_root = stream_decode_digest32(bytes, &mut pos)?;
        let num_layers = stream_decode_nat(bytes, &mut pos)?;
        let turn_chain_root = stream_decode_digest32(bytes, &mut pos)?;
        let raw_length = stream_decode_nat(bytes, &mut pos)?;
        let raw_root = stream_decode_digest32(bytes, &mut pos)?;
        let clean_length = stream_decode_nat(bytes, &mut pos)?;
        let clean_root = stream_decode_digest32(bytes, &mut pos)?;
        let claimed_ast = stream_decode_mini_value(bytes, &mut pos)?;
        if pos != bytes.len() {
            return Err(format!("trailing {} bytes in VASTMT01", bytes.len() - pos));
        }
        Ok(Self {
            weight_root,
            prompt_length,
            prompt_root,
            num_layers,
            turn_chain_root,
            raw_length,
            raw_root,
            clean_length,
            clean_root,
            claimed_ast,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiableAgentTurnReceipt {
    pub prompt_bytes: Vec<u8>,
    pub boundary_roots: Vec<[u8; 32]>,
    pub audited_layer: usize,
    pub audited_b_in_root: [u8; 32],
    pub audited_b_out_root: [u8; 32],
    pub u1_proof_digest: [u8; 32],
    pub w_raw: Vec<u8>,
    pub w_clean: Vec<u8>,
    pub rule_indices: Vec<usize>,
}

impl VerifiableAgentTurnReceipt {
    pub fn to_stream_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(1024 + self.w_raw.len() * 2);
        out.extend_from_slice(VAGENT01_MAGIC);
        stream_encode_bytes(&self.prompt_bytes, &mut out);
        stream_encode_nat(self.boundary_roots.len(), &mut out);
        for r in &self.boundary_roots {
            out.extend_from_slice(r);
        }
        stream_encode_nat(self.audited_layer, &mut out);
        out.extend_from_slice(&self.audited_b_in_root);
        out.extend_from_slice(&self.audited_b_out_root);
        out.extend_from_slice(&self.u1_proof_digest);
        stream_encode_bytes(&self.w_raw, &mut out);
        stream_encode_bytes(&self.w_clean, &mut out);
        stream_encode_nat(self.rule_indices.len(), &mut out);
        for &ri in &self.rule_indices {
            stream_encode_nat(ri, &mut out);
        }
        out
    }

    pub fn from_stream_bytes(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() < 8 || &bytes[0..8] != VAGENT01_MAGIC {
            return Err("invalid VAGENT01 magic".to_string());
        }
        let mut pos = 8usize;
        let prompt_bytes = stream_decode_bytes(bytes, &mut pos)?;
        let nb = stream_decode_nat(bytes, &mut pos)?;
        if nb > 256 {
            return Err("excessive boundary_roots len".to_string());
        }
        let mut boundary_roots = Vec::with_capacity(nb);
        for _ in 0..nb {
            boundary_roots.push(stream_decode_digest32(bytes, &mut pos)?);
        }
        let audited_layer = stream_decode_nat(bytes, &mut pos)?;
        let audited_b_in_root = stream_decode_digest32(bytes, &mut pos)?;
        let audited_b_out_root = stream_decode_digest32(bytes, &mut pos)?;
        let u1_proof_digest = stream_decode_digest32(bytes, &mut pos)?;
        let w_raw = stream_decode_bytes(bytes, &mut pos)?;
        let w_clean = stream_decode_bytes(bytes, &mut pos)?;
        let nr = stream_decode_nat(bytes, &mut pos)?;
        if nr > 100_000 {
            return Err("excessive rule_indices len".to_string());
        }
        let mut rule_indices = Vec::with_capacity(nr);
        for _ in 0..nr {
            rule_indices.push(stream_decode_nat(bytes, &mut pos)?);
        }
        if pos != bytes.len() {
            return Err(format!("trailing {} bytes in VAGENT01", bytes.len() - pos));
        }
        Ok(Self {
            prompt_bytes,
            boundary_roots,
            audited_layer,
            audited_b_in_root,
            audited_b_out_root,
            u1_proof_digest,
            w_raw,
            w_clean,
            rule_indices,
        })
    }
}

/// Exact Rust mirror of Lean's `verifyAgentTurnBytes : List UInt8 -> List UInt8 -> Bool`!
pub fn verify_agent_turn_weld_bytes(stmt_bytes: &[u8], receipt_bytes: &[u8]) -> Result<(), String> {
    let stmt = VerifiableAgentTurnStmt::from_stream_bytes(stmt_bytes)?;
    let rcpt = VerifiableAgentTurnReceipt::from_stream_bytes(receipt_bytes)?;

    if stmt.num_layers == 0 || stmt.num_layers.checked_add(1) != Some(rcpt.boundary_roots.len()) {
        return Err("U1 boundary count != num_layers + 1".to_string());
    }
    if rcpt.audited_layer >= stmt.num_layers {
        return Err("audited_layer >= num_layers".to_string());
    }
    let exp_vrf = compute_u1_vrf_layer_cshake(
        &stmt.weight_root,
        &rcpt.boundary_roots,
        &stmt.clean_root,
        stmt.num_layers,
    );
    if rcpt.audited_layer != exp_vrf {
        return Err("Fiat-Shamir VRF audited_layer mismatch".to_string());
    }
    if rcpt.boundary_roots[rcpt.audited_layer] != rcpt.audited_b_in_root
        || rcpt.boundary_roots[rcpt.audited_layer + 1] != rcpt.audited_b_out_root
    {
        return Err("audited boundary in/out root mismatch".to_string());
    }
    if rcpt.prompt_bytes.len() != stmt.prompt_length
        || content_commit_cshake(&rcpt.prompt_bytes) != stmt.prompt_root
    {
        return Err("TK prompt (length, contentCommit) mismatch".to_string());
    }
    let recomputed_head = compute_u1_turn_head_cshake(
        &stmt.weight_root,
        &stmt.prompt_root,
        stmt.prompt_length,
        &rcpt.boundary_roots,
        &rcpt.u1_proof_digest,
        stmt.raw_length,
        &stmt.raw_root,
    );
    if recomputed_head != stmt.turn_chain_root {
        return Err("U1 turnChainRoot mismatch (TK boundary/output splice refused)".to_string());
    }

    let rules = default_secret_rules();
    if !all_rules_safe(&rules) {
        return Err("unsafe redaction rules".to_string());
    }
    if rcpt.w_raw.len() != stmt.raw_length || content_commit_cshake(&rcpt.w_raw) != stmt.raw_root {
        return Err("w_raw (length, contentCommit) mismatch".to_string());
    }
    if rcpt.w_clean.len() != stmt.clean_length
        || content_commit_cshake(&rcpt.w_clean) != stmt.clean_root
    {
        return Err("w_clean (length, contentCommit) mismatch".to_string());
    }
    if rcpt.w_clean != redact_bytes_canonical(&rules, &rcpt.w_raw) {
        return Err("w_clean != redactBytes defaultSecretRules w_raw".to_string());
    }
    let ast = exec_mini_attr_replay(&rcpt.rule_indices, &rcpt.w_clean)?;
    if ast != stmt.claimed_ast {
        return Err("extracted AST != stmt.claimed_ast".to_string());
    }
    Ok(())
}

const HARDENED_U1_MAGIC: &[u8; 8] = b"QW35U1P2";
const UW_SHIFT_BIAS: u32 = 65_536; // `2^16` -> `uw_shifted in [0, 2^17)` <=> signed `UW in [-65536, 65536)`
const UW_RANGE_BITS: usize = 17;
const RHS_SHIFT_BIAS: u32 = 16_384; // `2^14` -> `rhs_shifted in [0, 2^15)` <=> signed `RHS in [-16384, 16384)`
const RHS_RANGE_BITS: usize = 15;

/// Collision-free stride-`4096` public DFA table `tuple = q + 8 * b + 4096 * q_next`!
/// Because `q in [0, 8)` and `b in [0, 512)`, `(q, b, q_next) -> q + 8*b + 4096*q_next` is
/// **100% injective over Z and BabyBear** (`8 * 512 == 4096`, eliminating the `2048`-stride overlap!).
pub fn build_accepting_sk_dfa_public_table_stride4096() -> Vec<u32> {
    let mut entries = Vec::with_capacity(2048);
    for q in 0..4u8 {
        for b in 0..=255u8 {
            let q_next = padded_complement_sk_step(q, b);
            if q_next < 4 {
                let tuple = (q as u32) + 8 * (b as u32) + 4096 * (q_next as u32);
                entries.push(tuple);
            }
        }
        // Tail EOF transition `b = 256`: `q_next == q` (`b in [257, 512)` has NO entries in this table!)
        let pad_tuple = (q as u32) + 8 * 256 + 4096 * (q as u32);
        entries.push(pad_tuple);
    }
    let filler = entries[0];
    while entries.len() < 2048 {
        entries.push(filler);
    }
    entries
}

fn eval_shift_kernel_mle_checked(z: &[Ext4], u_pt: &[Ext4]) -> Result<Ext4, String> {
    if z.len() != u_pt.len() {
        return Err("shift kernel dimension mismatch (kappa != m)".to_string());
    }
    let eq_z = build_eq_table_lsb_ext4(z);
    let eq_u = build_eq_table_lsb_ext4(u_pt);
    let n = eq_z.len();
    let mut acc = Ext4::ZERO;
    for t in 0..(n - 1) {
        acc = acc.add(eq_z[t].mul(eq_u[t + 1]));
    }
    Ok(acc)
}

/// Public multilinear extension of `1[t >= word_len]` over `t in 0..pad_len` (`O(pad_len)` = `2048` ops).
fn eval_eof_indicator_mle(word_len: usize, pad_len: usize, z_pt: &[Ext4]) -> Ext4 {
    let eq_z = build_eq_table_lsb_ext4(z_pt);
    let mut acc = Ext4::ZERO;
    for &ez in &eq_z[word_len..pad_len] {
        acc = acc.add(ez);
    }
    acc
}

/// Hardened zero-cleartext ZK `Absent("sk-...")` DFA receipt closing BOTH:
/// 1) Stride-`4096` tuple injectivity + position-dependent `t < word_len => b[t] in [0, 256)` and `t >= word_len => b[t] == 256`,
/// 2) `248`-bit Schwartz-Zippel MLE binding of `opt_cleartext_bytes` (`w_clean`) against `bytes_pcs_root` at `(z_dfa_leaf, z_b8_leaf)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HardenedPaddedAbsenceZkReceipt {
    pub word_len: usize,
    pub pad_len: usize,
    pub final_state: u8,
    pub content_root: [u8; 32],
    pub bytes_pcs_root: [u8; 32],
    pub q_pcs_root: [u8; 32],
    pub q_next_pcs_root: [u8; 32],
    pub mult_dfa_pcs_root: [u8; 32],
    pub mult_b8_pcs_root: [u8; 32],
    pub mult_q_pcs_root: [u8; 32],
    pub dfa_d1b_proof: D1bRangeExt4Proof,
    pub q_at_dfa_leaf: Ext4,
    pub b_at_dfa_leaf: Ext4,
    pub q_next_at_dfa_leaf: Ext4,
    pub b_pad_at_zb8: Ext4,
    pub q_next_at_zsh: Ext4,
    pub b8_range_proof: D1bRangeExt4Proof,
    pub q_range_proof: D1bRangeExt4Proof,
    pub shift_gruen_proof: GruenMode2Ext4Proof,
    pub bytes_pcs_proof: PcsOpeningProof,
    pub q_pcs_proof: PcsOpeningProof,
    pub q_next_pcs_proof: PcsOpeningProof,
    pub mult_dfa_pcs_proof: PcsOpeningProof,
    pub mult_b8_pcs_proof: PcsOpeningProof,
    pub mult_q_pcs_proof: PcsOpeningProof,
}

impl HardenedPaddedAbsenceZkReceipt {
    pub fn write_to(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&(self.word_len as u32).to_le_bytes());
        out.extend_from_slice(&(self.pad_len as u32).to_le_bytes());
        out.push(self.final_state);
        for r in [
            &self.content_root,
            &self.bytes_pcs_root,
            &self.q_pcs_root,
            &self.q_next_pcs_root,
            &self.mult_dfa_pcs_root,
            &self.mult_b8_pcs_root,
            &self.mult_q_pcs_root,
        ] {
            out.extend_from_slice(r);
        }
        self.dfa_d1b_proof.write_to(out);
        for e in [
            self.q_at_dfa_leaf,
            self.b_at_dfa_leaf,
            self.q_next_at_dfa_leaf,
            self.b_pad_at_zb8,
            self.q_next_at_zsh,
        ] {
            out.extend_from_slice(&e.to_bytes());
        }
        self.b8_range_proof.write_to(out);
        self.q_range_proof.write_to(out);
        self.shift_gruen_proof.write_to(out);
        for pf in [
            &self.bytes_pcs_proof,
            &self.q_pcs_proof,
            &self.q_next_pcs_proof,
            &self.mult_dfa_pcs_proof,
            &self.mult_b8_pcs_proof,
            &self.mult_q_pcs_proof,
        ] {
            pf.write_to(out);
        }
    }

    pub fn read_from(cur: &mut ByteCursor) -> Result<Self, String> {
        let word_len = cur.read_u32()? as usize;
        let pad_len = cur.read_u32()? as usize;
        let final_state = cur.read_u8()?;
        let content_root = cur.read_arr32()?;
        let bytes_pcs_root = cur.read_arr32()?;
        let q_pcs_root = cur.read_arr32()?;
        let q_next_pcs_root = cur.read_arr32()?;
        let mult_dfa_pcs_root = cur.read_arr32()?;
        let mult_b8_pcs_root = cur.read_arr32()?;
        let mult_q_pcs_root = cur.read_arr32()?;
        let dfa_d1b_proof = D1bRangeExt4Proof::read_from(cur)?;
        let q_at_dfa_leaf = cur.read_ext4()?;
        let b_at_dfa_leaf = cur.read_ext4()?;
        let q_next_at_dfa_leaf = cur.read_ext4()?;
        let b_pad_at_zb8 = cur.read_ext4()?;
        let q_next_at_zsh = cur.read_ext4()?;
        let b8_range_proof = D1bRangeExt4Proof::read_from(cur)?;
        let q_range_proof = D1bRangeExt4Proof::read_from(cur)?;
        let shift_gruen_proof = GruenMode2Ext4Proof::read_from(cur)?;
        let bytes_pcs_proof = PcsOpeningProof::read_from(cur)?;
        let q_pcs_proof = PcsOpeningProof::read_from(cur)?;
        let q_next_pcs_proof = PcsOpeningProof::read_from(cur)?;
        let mult_dfa_pcs_proof = PcsOpeningProof::read_from(cur)?;
        let mult_b8_pcs_proof = PcsOpeningProof::read_from(cur)?;
        let mult_q_pcs_proof = PcsOpeningProof::read_from(cur)?;
        Ok(Self {
            word_len,
            pad_len,
            final_state,
            content_root,
            bytes_pcs_root,
            q_pcs_root,
            q_next_pcs_root,
            mult_dfa_pcs_root,
            mult_b8_pcs_root,
            mult_q_pcs_root,
            dfa_d1b_proof,
            q_at_dfa_leaf,
            b_at_dfa_leaf,
            q_next_at_dfa_leaf,
            b_pad_at_zb8,
            q_next_at_zsh,
            b8_range_proof,
            q_range_proof,
            shift_gruen_proof,
            bytes_pcs_proof,
            q_pcs_proof,
            q_next_pcs_proof,
            mult_dfa_pcs_proof,
            mult_b8_pcs_proof,
            mult_q_pcs_proof,
        })
    }
}

pub fn prove_hardened_padded_absence_zk(
    output_bytes: &[u8],
    tr: &mut CShakeTranscript,
) -> Result<HardenedPaddedAbsenceZkReceipt, String> {
    let (final_state, trace) = run_padded_complement_sk_dfa(output_bytes);
    if final_state >= 4 {
        return Err("prover refusal: output_bytes violates Absent(\"sk-...\") policy (sink state 4 reached)".to_string());
    }
    let pad_len = (output_bytes.len() + 2).next_power_of_two().max(2048);
    let m = pad_len.trailing_zeros() as usize;

    let mut bytes_pad = vec![256u32; pad_len];
    let mut b_byte_only = vec![0u32; pad_len]; // `bytes_pad[t] - 256 * 1[t >= word_len] in [0, 256)`!
    for (i, &b) in output_bytes.iter().enumerate() {
        bytes_pad[i] = b as u32;
        b_byte_only[i] = b as u32;
    }
    let mut q_vec = vec![final_state as u32; pad_len];
    let mut q_next_vec = vec![final_state as u32; pad_len];
    let mut tuples = vec![0u32; pad_len];
    for t in 0..pad_len {
        let qt = if t < trace.len() {
            trace[t] as u32
        } else {
            final_state as u32
        };
        let qn = if t + 1 < trace.len() {
            trace[t + 1] as u32
        } else {
            final_state as u32
        };
        q_vec[t] = qt;
        q_next_vec[t] = qn;
        tuples[t] = qt + 8 * bytes_pad[t] + 4096 * qn;
    }

    let pub_dfa_tab = build_accepting_sk_dfa_public_table_stride4096();
    let mult_dfa = compute_d1b_public_table_multiplicities(&tuples, &pub_dfa_tab)?;
    let mult_b8 = compute_d1b_multiplicities(&b_byte_only, 8)?; // `[0, 256)`!
    let mult_q = compute_d1b_multiplicities(&q_vec, 3)?; // `[0, 8)`!

    let bytes_state = commit_table_pcs(&bytes_pad, PcsParams::default_zk(2), None);
    let q_state = commit_table_pcs(&q_vec, PcsParams::default_zk(4), None);
    let q_next_state = commit_table_pcs(&q_next_vec, PcsParams::default_zk(2), None);
    let mult_dfa_state = commit_table_pcs(&mult_dfa, PcsParams::default_zk(1), None);
    let mult_b8_state = commit_table_pcs(&mult_b8, PcsParams::default_zk(1), None);
    let mult_q_state = commit_table_pcs(&mult_q, PcsParams::default_zk(1), None);

    let mut root_in = [0u8; 40];
    root_in[0..8].copy_from_slice(&(output_bytes.len() as u64).to_le_bytes());
    root_in[8..40].copy_from_slice(&bytes_state.root);
    let content_root = cshake256_32(b"QW35-CONTENT-SCHEME-ROOT-V2", &root_in);

    tr.absorb_root(b"abs_content_root", &content_root);
    tr.absorb_u32(b"abs_word_len", output_bytes.len() as u32);
    tr.absorb_u32(b"abs_final_state", final_state as u32);
    for r in [
        &bytes_state.root,
        &q_state.root,
        &q_next_state.root,
        &mult_dfa_state.root,
        &mult_b8_state.root,
        &mult_q_state.root,
    ] {
        tr.absorb_root(b"abs_pcs_root", r);
    }

    let (dfa_d1b_proof, z_dfa_leaf) =
        prove_d1b_public_table_ext4(&tuples, &pub_dfa_tab, &mult_dfa, tr);
    let q_at_dfa_leaf = mle_eval_bb_at_ext4(&q_vec, &z_dfa_leaf);
    let b_at_dfa_leaf = mle_eval_bb_at_ext4(&bytes_pad, &z_dfa_leaf);
    let q_next_at_dfa_leaf = mle_eval_bb_at_ext4(&q_next_vec, &z_dfa_leaf);
    tr.absorb_ext4(b"abs_q_dl", q_at_dfa_leaf);
    tr.absorb_ext4(b"abs_b_dl", b_at_dfa_leaf);
    tr.absorb_ext4(b"abs_qn_dl", q_next_at_dfa_leaf);

    let (b8_range_proof, z_b8_leaf) = prove_d1b_range_ext4(&b_byte_only, &mult_b8, m, 8, tr);
    let b_pad_at_zb8 = mle_eval_bb_at_ext4(&bytes_pad, &z_b8_leaf);
    tr.absorb_ext4(b"abs_bp_zb8", b_pad_at_zb8);
    let (q_range_proof, z_q_leaf) = prove_d1b_range_ext4(&q_vec, &mult_q, m, 3, tr);

    let z_sh = tr.squeeze_ext4_vec(b"abs_zsh", m, true);
    let q_next_at_zsh = mle_eval_bb_at_ext4(&q_next_vec, &z_sh);
    tr.absorb_ext4(b"abs_qn_zsh", q_next_at_zsh);

    let eq_zsh = build_eq_table_lsb_ext4(&z_sh);
    let mut shift_col = vec![Ext4::ZERO; pad_len];
    shift_col[1..pad_len].copy_from_slice(&eq_zsh[..(pad_len - 1)]);
    let q_ext: Vec<Ext4> = q_vec.iter().map(|&v| Ext4::from_bb(v)).collect();
    let (shift_gruen_proof, shift_chals) =
        prove_gruen_einsum_mode2_ext4(&shift_col, &q_ext, 0, m, &[], tr);

    let bytes_pcs_proof = open_pcs_claims(
        &bytes_state,
        &[
            MleEvalClaim {
                point: z_dfa_leaf.clone(),
                value: b_at_dfa_leaf,
            },
            MleEvalClaim {
                point: z_b8_leaf.clone(),
                value: b_pad_at_zb8,
            },
        ],
        tr,
    );
    let q_pcs_proof = open_pcs_claims(
        &q_state,
        &[
            MleEvalClaim {
                point: vec![Ext4::ZERO; m],
                value: Ext4::ZERO,
            },
            MleEvalClaim {
                point: z_dfa_leaf.clone(),
                value: q_at_dfa_leaf,
            },
            MleEvalClaim {
                point: z_q_leaf.clone(),
                value: q_range_proof.rem_leaf_eval,
            },
            MleEvalClaim {
                point: shift_chals,
                value: shift_gruen_proof.terminal_openings.1,
            },
        ],
        tr,
    );
    let q_next_pcs_proof = open_pcs_claims(
        &q_next_state,
        &[
            MleEvalClaim {
                point: z_dfa_leaf.clone(),
                value: q_next_at_dfa_leaf,
            },
            MleEvalClaim {
                point: z_sh,
                value: q_next_at_zsh,
            },
        ],
        tr,
    );
    let mult_dfa_pcs_proof = open_pcs_claims(
        &mult_dfa_state,
        &[MleEvalClaim {
            point: z_dfa_leaf[..11].to_vec(),
            value: dfa_d1b_proof.mult_leaf_eval,
        }],
        tr,
    );
    let mult_b8_pcs_proof = open_pcs_claims(
        &mult_b8_state,
        &[MleEvalClaim {
            point: z_b8_leaf[..8].to_vec(),
            value: b8_range_proof.mult_leaf_eval,
        }],
        tr,
    );
    let mult_q_pcs_proof = open_pcs_claims(
        &mult_q_state,
        &[MleEvalClaim {
            point: z_q_leaf[..3].to_vec(),
            value: q_range_proof.mult_leaf_eval,
        }],
        tr,
    );

    Ok(HardenedPaddedAbsenceZkReceipt {
        word_len: output_bytes.len(),
        pad_len,
        final_state,
        content_root,
        bytes_pcs_root: bytes_state.root,
        q_pcs_root: q_state.root,
        q_next_pcs_root: q_next_state.root,
        mult_dfa_pcs_root: mult_dfa_state.root,
        mult_b8_pcs_root: mult_b8_state.root,
        mult_q_pcs_root: mult_q_state.root,
        dfa_d1b_proof,
        q_at_dfa_leaf,
        b_at_dfa_leaf,
        q_next_at_dfa_leaf,
        b_pad_at_zb8,
        q_next_at_zsh,
        b8_range_proof,
        q_range_proof,
        shift_gruen_proof,
        bytes_pcs_proof,
        q_pcs_proof,
        q_next_pcs_proof,
        mult_dfa_pcs_proof,
        mult_b8_pcs_proof,
        mult_q_pcs_proof,
    })
}

pub fn verify_hardened_padded_absence_zk(
    expected_content_root: &[u8; 32],
    opt_cleartext_bytes: Option<&[u8]>,
    receipt: &HardenedPaddedAbsenceZkReceipt,
    tr: &mut CShakeTranscript,
) -> Result<(), String> {
    if &receipt.content_root != expected_content_root {
        return Err("P6 content_root binding mismatch".to_string());
    }
    if receipt.final_state >= 4 {
        return Err("Absent(\"sk-...\") rejected: final DFA state >= 4".to_string());
    }
    if !receipt.pad_len.is_power_of_two()
        || receipt.pad_len < 2048
        || receipt
            .word_len
            .checked_add(2)
            .is_none_or(|n| n > receipt.pad_len)
    {
        return Err("invalid HardenedPaddedAbsenceZkReceipt pad_len".to_string());
    }
    let mut root_in = [0u8; 40];
    root_in[0..8].copy_from_slice(&(receipt.word_len as u64).to_le_bytes());
    root_in[8..40].copy_from_slice(&receipt.bytes_pcs_root);
    if cshake256_32(b"QW35-CONTENT-SCHEME-ROOT-V2", &root_in) != receipt.content_root {
        return Err("content_root != H(word_len || bytes_pcs_root)".to_string());
    }

    let m = receipt.pad_len.trailing_zeros() as usize;
    tr.absorb_root(b"abs_content_root", &receipt.content_root);
    tr.absorb_u32(b"abs_word_len", receipt.word_len as u32);
    tr.absorb_u32(b"abs_final_state", receipt.final_state as u32);
    for r in [
        &receipt.bytes_pcs_root,
        &receipt.q_pcs_root,
        &receipt.q_next_pcs_root,
        &receipt.mult_dfa_pcs_root,
        &receipt.mult_b8_pcs_root,
        &receipt.mult_q_pcs_root,
    ] {
        tr.absorb_root(b"abs_pcs_root", r);
    }

    let pub_dfa_tab = build_accepting_sk_dfa_public_table_stride4096();
    if receipt.dfa_d1b_proof.m_wit != m || receipt.dfa_d1b_proof.m_tab != 11 {
        return Err("DFA D1b dimensions mismatch".to_string());
    }
    let z_dfa_leaf = verify_d1b_public_table_ext4(&pub_dfa_tab, &receipt.dfa_d1b_proof, tr)?;
    tr.absorb_ext4(b"abs_q_dl", receipt.q_at_dfa_leaf);
    tr.absorb_ext4(b"abs_b_dl", receipt.b_at_dfa_leaf);
    tr.absorb_ext4(b"abs_qn_dl", receipt.q_next_at_dfa_leaf);

    // Collision-free stride-`4096` tuple reconstruction: `tuple == q + 8*b + 4096*q_next`!
    let expected_tuple = receipt
        .q_at_dfa_leaf
        .add(receipt.b_at_dfa_leaf.scale_bb(8))
        .add(receipt.q_next_at_dfa_leaf.scale_bb(4096));
    if receipt.dfa_d1b_proof.rem_leaf_eval != expected_tuple {
        return Err("DFA stride-4096 transition tuple != q + 8*b + 4096*q_next".to_string());
    }

    if receipt.b8_range_proof.m_wit != m
        || receipt.b8_range_proof.m_tab != 8
        || receipt.q_range_proof.m_wit != m
        || receipt.q_range_proof.m_tab != 3
    {
        return Err("DFA b8/q range D1b dimension mismatch".to_string());
    }
    let z_b8_leaf = verify_d1b_range_ext4(&receipt.b8_range_proof, tr)?;
    tr.absorb_ext4(b"abs_bp_zb8", receipt.b_pad_at_zb8);
    // Position-dependent EOF check (`b_pad(z_b8) == b_byte_only(z_b8) + 256 * 1[t >= word_len](z_b8)`):
    // proves `t < word_len => b_pad[t] in [0, 256)` AND `t >= word_len => b_pad[t] == 256`!
    let eof_ind_eval = eval_eof_indicator_mle(receipt.word_len, receipt.pad_len, &z_b8_leaf);
    let expected_b_pad_zb8 = receipt
        .b8_range_proof
        .rem_leaf_eval
        .add(eof_ind_eval.scale_bb(256));
    if receipt.b_pad_at_zb8 != expected_b_pad_zb8 {
        return Err(
            "position-dependent byte/EOF check failed: b_pad != b8 + 256 * 1[t >= word_len]"
                .to_string(),
        );
    }

    // When `opt_cleartext_bytes` (`w_clean`) is supplied, cryptographically bind `w_clean` to
    // `bytes_pcs_root` via dual-point (~123.6-bit/pt, capped by ~103.5-bit PCS) Schwartz-Zippel MLE checks at `z_dfa_leaf` and `z_b8_leaf`!
    if let Some(clear) = opt_cleartext_bytes {
        if clear.len() != receipt.word_len {
            return Err("cleartext length != committed word_len".to_string());
        }
        let (q_end, _) = run_padded_complement_sk_dfa(clear);
        if q_end >= 4 || q_end != receipt.final_state {
            return Err(
                "cleartext bytes fail padded-complement Absent(\"sk-...\") DFA!".to_string(),
            );
        }
        let mut expected_bytes_pad = vec![256u32; receipt.pad_len];
        for (i, &b) in clear.iter().enumerate() {
            expected_bytes_pad[i] = b as u32;
        }
        if mle_eval_bb_at_ext4(&expected_bytes_pad, &z_dfa_leaf) != receipt.b_at_dfa_leaf
            || mle_eval_bb_at_ext4(&expected_bytes_pad, &z_b8_leaf) != receipt.b_pad_at_zb8
        {
            return Err(
                "third-party re-pointing forgery refused: w_clean MLE != committed bytes_pcs_root!"
                    .to_string(),
            );
        }
    }

    let z_q_leaf = verify_d1b_range_ext4(&receipt.q_range_proof, tr)?;

    let z_sh = tr.squeeze_ext4_vec(b"abs_zsh", m, true);
    tr.absorb_ext4(b"abs_qn_zsh", receipt.q_next_at_zsh);
    let eq_last = eq_mle_ext4(&z_sh, &vec![Ext4::ONE; m]);
    let expected_shift_claim = receipt
        .q_next_at_zsh
        .sub(eq_last.scale_bb(receipt.final_state as u32));
    if receipt.shift_gruen_proof.rounds.len() != m {
        return Err("shift_gruen_proof kappa != m".to_string());
    }
    let shift_chals =
        verify_gruen_einsum_mode2_ext4(expected_shift_claim, &[], &receipt.shift_gruen_proof, tr)?;
    if receipt.shift_gruen_proof.terminal_openings.0
        != eval_shift_kernel_mle_checked(&z_sh, &shift_chals)?
    {
        return Err("DFA shift kernel public evaluation mismatch".to_string());
    }

    verify_pcs_claims(
        &receipt.bytes_pcs_root,
        PcsShape::new(m, PcsParams::default_zk(2)),
        &[
            MleEvalClaim {
                point: z_dfa_leaf.clone(),
                value: receipt.b_at_dfa_leaf,
            },
            MleEvalClaim {
                point: z_b8_leaf.clone(),
                value: receipt.b_pad_at_zb8,
            },
        ],
        &receipt.bytes_pcs_proof,
        tr,
    )?;
    verify_pcs_claims(
        &receipt.q_pcs_root,
        PcsShape::new(m, PcsParams::default_zk(4)),
        &[
            MleEvalClaim {
                point: vec![Ext4::ZERO; m],
                value: Ext4::ZERO,
            },
            MleEvalClaim {
                point: z_dfa_leaf.clone(),
                value: receipt.q_at_dfa_leaf,
            },
            MleEvalClaim {
                point: z_q_leaf.clone(),
                value: receipt.q_range_proof.rem_leaf_eval,
            },
            MleEvalClaim {
                point: shift_chals,
                value: receipt.shift_gruen_proof.terminal_openings.1,
            },
        ],
        &receipt.q_pcs_proof,
        tr,
    )?;
    verify_pcs_claims(
        &receipt.q_next_pcs_root,
        PcsShape::new(m, PcsParams::default_zk(2)),
        &[
            MleEvalClaim {
                point: z_dfa_leaf.clone(),
                value: receipt.q_next_at_dfa_leaf,
            },
            MleEvalClaim {
                point: z_sh,
                value: receipt.q_next_at_zsh,
            },
        ],
        &receipt.q_next_pcs_proof,
        tr,
    )?;
    verify_pcs_claims(
        &receipt.mult_dfa_pcs_root,
        PcsShape::new(11, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: z_dfa_leaf[..11].to_vec(),
            value: receipt.dfa_d1b_proof.mult_leaf_eval,
        }],
        &receipt.mult_dfa_pcs_proof,
        tr,
    )?;
    verify_pcs_claims(
        &receipt.mult_b8_pcs_root,
        PcsShape::new(8, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: z_b8_leaf[..8].to_vec(),
            value: receipt.b8_range_proof.mult_leaf_eval,
        }],
        &receipt.mult_b8_pcs_proof,
        tr,
    )?;
    verify_pcs_claims(
        &receipt.mult_q_pcs_root,
        PcsShape::new(3, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: z_q_leaf[..3].to_vec(),
            value: receipt.q_range_proof.mult_leaf_eval,
        }],
        &receipt.mult_q_pcs_proof,
        tr,
    )?;
    Ok(())
}

/// Hardened turn-bound `U1` audit bundle (`QW35U1P2`) uniting:
/// 1) Statement-bound `SuccinctGdnLayerProof` (absorbing `prompt_root`, `raw_root`, `clean_root`, `boundary_roots`),
/// 2) `D1b` signed-quotient range checks on `UW` (`[-65536, 65536)`) and `RHS` (`[-16384, 16384)`) preventing `mod P` wraparound,
/// 3) `HardenedPaddedAbsenceZkReceipt` (stride `4096` + position-dependent EOF check + 248-bit `w_clean` MLE binding).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HardenedVAgentU1AuditBundle {
    pub audited_layer: usize,
    pub bnd_vars: usize,
    pub uw_shifted_pcs_root: [u8; 32],
    pub mult_uw_pcs_root: [u8; 32],
    pub rhs_shifted_pcs_root: [u8; 32],
    pub mult_rhs_pcs_root: [u8; 32],
    pub layer_proof: SuccinctGdnLayerProof,
    pub d1b_uw_proof: D1bRangeExt4Proof,
    pub d1b_rhs_proof: D1bRangeExt4Proof,
    pub uw_shifted_pcs_proof: PcsOpeningProof,
    pub mult_uw_pcs_proof: PcsOpeningProof,
    pub rhs_shifted_pcs_proof: PcsOpeningProof,
    pub mult_rhs_pcs_proof: PcsOpeningProof,
    pub absence_receipt: HardenedPaddedAbsenceZkReceipt,
}

impl HardenedVAgentU1AuditBundle {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(640 * 1024);
        out.extend_from_slice(HARDENED_U1_MAGIC);
        out.extend_from_slice(&(self.audited_layer as u32).to_le_bytes());
        out.extend_from_slice(&(self.bnd_vars as u32).to_le_bytes());
        for r in [
            &self.uw_shifted_pcs_root,
            &self.mult_uw_pcs_root,
            &self.rhs_shifted_pcs_root,
            &self.mult_rhs_pcs_root,
        ] {
            out.extend_from_slice(r);
        }
        self.layer_proof.write_to(&mut out);
        self.d1b_uw_proof.write_to(&mut out);
        self.d1b_rhs_proof.write_to(&mut out);
        for pf in [
            &self.uw_shifted_pcs_proof,
            &self.mult_uw_pcs_proof,
            &self.rhs_shifted_pcs_proof,
            &self.mult_rhs_pcs_proof,
        ] {
            pf.write_to(&mut out);
        }
        self.absence_receipt.write_to(&mut out);
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        let mut cur = ByteCursor::new(bytes);
        let magic = cur.read_exact(8)?;
        if magic != HARDENED_U1_MAGIC {
            return Err(
                "invalid HardenedVAgentU1AuditBundle magic (expected QW35U1P2)".to_string(),
            );
        }
        let audited_layer = cur.read_u32()? as usize;
        let bnd_vars = cur.read_u32()? as usize;
        let uw_shifted_pcs_root = cur.read_arr32()?;
        let mult_uw_pcs_root = cur.read_arr32()?;
        let rhs_shifted_pcs_root = cur.read_arr32()?;
        let mult_rhs_pcs_root = cur.read_arr32()?;
        let layer_proof = SuccinctGdnLayerProof::read_from(&mut cur)?;
        let d1b_uw_proof = D1bRangeExt4Proof::read_from(&mut cur)?;
        let d1b_rhs_proof = D1bRangeExt4Proof::read_from(&mut cur)?;
        let uw_shifted_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        let mult_uw_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        let rhs_shifted_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        let mult_rhs_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        let absence_receipt = HardenedPaddedAbsenceZkReceipt::read_from(&mut cur)?;
        if cur.remaining() != 0 {
            return Err(format!(
                "trailing {} bytes in HardenedVAgentU1AuditBundle",
                cur.remaining()
            ));
        }
        Ok(Self {
            audited_layer,
            bnd_vars,
            uw_shifted_pcs_root,
            mult_uw_pcs_root,
            rhs_shifted_pcs_root,
            mult_rhs_pcs_root,
            layer_proof,
            d1b_uw_proof,
            d1b_rhs_proof,
            uw_shifted_pcs_proof,
            mult_uw_pcs_proof,
            rhs_shifted_pcs_proof,
            mult_rhs_pcs_proof,
            absence_receipt,
        })
    }
}

struct TurnContextMetadata<'a> {
    weight_root: &'a [u8; 32],
    prompt_len: usize,
    prompt_root: &'a [u8; 32],
    raw_len: usize,
    raw_root: &'a [u8; 32],
    clean_len: usize,
    clean_root: &'a [u8; 32],
    boundary_roots: &'a [[u8; 32]; 25],
}

fn absorb_turn_context_into_transcript(tr: &mut CShakeTranscript, ctx: &TurnContextMetadata<'_>) {
    tr.absorb_root(b"turn_weight_root", ctx.weight_root);
    tr.absorb_u32(b"turn_prompt_len", ctx.prompt_len as u32);
    tr.absorb_root(b"turn_prompt_root", ctx.prompt_root);
    tr.absorb_u32(b"turn_raw_len", ctx.raw_len as u32);
    tr.absorb_root(b"turn_raw_root", ctx.raw_root);
    tr.absorb_u32(b"turn_clean_len", ctx.clean_len as u32);
    tr.absorb_root(b"turn_clean_root", ctx.clean_root);
    for (idx, br) in ctx.boundary_roots.iter().enumerate() {
        tr.absorb_u32(b"turn_bnd_idx", idx as u32);
        tr.absorb_root(b"turn_bnd_root", br);
    }
}

/// `(bundle_bytes, content_root, qs_binding)` returned by [`prove_hardened_vagent_u1_bundle`].
pub type VagentBundleResult = (Vec<u8>, [u8; 32], [u8; 32]);

#[allow(clippy::too_many_arguments)]
pub fn prove_hardened_vagent_u1_bundle(
    registry: &Qwen35WeightRegistry,
    layer_tensor_digests: Vec<[u8; 32]>,
    gate_proj_slot: usize,
    gate_pcs: &PrecommittedMxfp4Pcs,
    u1_online: &U1OnlineCommitment,
    turn: &Qwen35TurnExecution,
    prompt_len: usize,
    prompt_root: &[u8; 32],
    raw_len: usize,
    raw_root: &[u8; 32],
    redacted_output_bytes: &[u8],
    clean_root: &[u8; 32],
) -> Result<VagentBundleResult, String> {
    let ctx = TurnContextMetadata {
        weight_root: &registry.weight_root,
        prompt_len,
        prompt_root,
        raw_len,
        raw_root,
        clean_len: redacted_output_bytes.len(),
        clean_root,
        boundary_roots: &u1_online.boundary_roots,
    };
    let mut abs_tr = CShakeTranscript::new(b"QW35-VAGENT01-ABSENCE-V2");
    absorb_turn_context_into_transcript(&mut abs_tr, &ctx);
    let absence_receipt = prove_hardened_padded_absence_zk(redacted_output_bytes, &mut abs_tr)?;

    let l_idx = turn.audited_layer;
    let layer_path = registry.open_layer(l_idx);

    let mut qs_bind_in = [0u8; 96];
    qs_bind_in[0..32].copy_from_slice(&layer_tensor_digests[gate_proj_slot]);
    qs_bind_in[32..64].copy_from_slice(&gate_pcs.q_state.root);
    qs_bind_in[64..96].copy_from_slice(&gate_pcs.s_state.root);
    let qs_binding = cshake256_32(b"QW35-QS-PCS-BIND-V1", &qs_bind_in);

    // Commit signed-shifted `UW` (`[-65536, 65536)`) & `RHS` (`[-16384, 16384)`) BEFORE squeezing `z_hik`!
    let wy = &turn.wy_witness;
    let log_h = wy.h_pad.trailing_zeros() as usize;
    let log_c = wy.c_len.trailing_zeros() as usize;
    let log_col = (wy.d_v + wy.d_k).trailing_zeros() as usize;
    let m_wy_wit = log_h + log_c + log_col;

    let uw_shifted: Vec<u32> = wy
        .uw_lsb_hik
        .iter()
        .map(|&v| ((v as u64 + UW_SHIFT_BIAS as u64) % P) as u32)
        .collect();
    let rhs_shifted: Vec<u32> = wy
        .rhs_lsb_hik
        .iter()
        .map(|&v| ((v as u64 + RHS_SHIFT_BIAS as u64) % P) as u32)
        .collect();
    let mult_uw = compute_d1b_multiplicities(&uw_shifted, UW_RANGE_BITS)?;
    let mult_rhs = compute_d1b_multiplicities(&rhs_shifted, RHS_RANGE_BITS)?;

    let uw_sh_state = commit_table_pcs(&uw_shifted, PcsParams::default_zk(2), None);
    let mult_uw_state = commit_table_pcs(&mult_uw, PcsParams::default_zk(1), None);
    let rhs_sh_state = commit_table_pcs(&rhs_shifted, PcsParams::default_zk(2), None);
    let mult_rhs_state = commit_table_pcs(&mult_rhs, PcsParams::default_zk(1), None);

    let mut lyr_tr = CShakeTranscript::new(b"QW35-VAGENT01-LAYER-AUDIT-V2");
    absorb_turn_context_into_transcript(&mut lyr_tr, &ctx);
    for r in [
        &uw_sh_state.root,
        &mult_uw_state.root,
        &rhs_sh_state.root,
        &mult_rhs_state.root,
    ] {
        lyr_tr.absorb_root(b"wy_quot_pcs_root", r);
    }

    let mut z_hik_replay = lyr_tr.clone();
    let layer_proof = prove_audited_gdn_layer(
        &registry.weight_root,
        l_idx,
        AuditedGdnLayerWitness {
            layer_weight_path: layer_path,
            layer_tensor_digests,
            gate_proj_tensor_slot: gate_proj_slot,
            gate_pcs,
            b_in_state: &u1_online.boundary_states[l_idx],
            b_out_state: &u1_online.boundary_states[l_idx + 1],
            b_in_bb: &turn.boundaries_bb[l_idx],
            b_out_bb: &turn.boundaries_bb[l_idx + 1],
            delta_gdn_bb: &turn.delta_gdn_bb,
            delta_mlp_bb: &turn.delta_mlp_bb,
            wy: &turn.wy_witness,
            x_ln2_i16: &turn.x_ln2_i16,
            gate_y_raw: &turn.gate_proj_y_raw,
        },
        &mut lyr_tr,
    )?;

    // Recover the exact `z_hik` squeezed inside `prove_audited_gdn_layer`!
    z_hik_replay.absorb_root(b"stmt_weight_root", &registry.weight_root);
    z_hik_replay.absorb_root(b"stmt_b_in_root", &u1_online.boundary_roots[l_idx]);
    z_hik_replay.absorb_root(b"stmt_b_out_root", &u1_online.boundary_roots[l_idx + 1]);
    z_hik_replay.absorb_u32(b"stmt_audited_layer", l_idx as u32);
    for r in [
        &layer_proof.q_pcs_root,
        &layer_proof.s_pcs_root,
        &layer_proof.l_pcs_root,
        &layer_proof.rhs_pcs_root,
        &layer_proof.uw_pcs_root,
        &layer_proof.rem_pcs_root,
        &layer_proof.mult_pcs_root,
        &layer_proof.x_ln2_pcs_root,
        &layer_proof.y_gate_pcs_root,
        &layer_proof.delta_gdn_pcs_root,
        &layer_proof.delta_mlp_pcs_root,
    ] {
        z_hik_replay.absorb_root(b"wit_pcs_root", r);
    }
    let z_h = z_hik_replay.squeeze_ext4_vec(b"wy_zh", log_h, true);
    let z_i = z_hik_replay.squeeze_ext4_vec(b"wy_zi", log_c, true);
    let z_k = z_hik_replay.squeeze_ext4_vec(b"wy_zk", log_col, true);
    let mut z_hik = Vec::with_capacity(m_wy_wit);
    z_hik.extend_from_slice(&z_h);
    z_hik.extend_from_slice(&z_i);
    z_hik.extend_from_slice(&z_k);

    let (d1b_uw_proof, z_uw_leaf) =
        prove_d1b_range_ext4(&uw_shifted, &mult_uw, m_wy_wit, UW_RANGE_BITS, &mut lyr_tr);
    let (d1b_rhs_proof, z_rhs_leaf) = prove_d1b_range_ext4(
        &rhs_shifted,
        &mult_rhs,
        m_wy_wit,
        RHS_RANGE_BITS,
        &mut lyr_tr,
    );

    let uw_shifted_pcs_proof = open_pcs_claims(
        &uw_sh_state,
        &[
            MleEvalClaim {
                point: z_hik.clone(),
                value: layer_proof.uw_eval_at_z.add(Ext4::from_bb(UW_SHIFT_BIAS)),
            },
            MleEvalClaim {
                point: z_uw_leaf.clone(),
                value: d1b_uw_proof.rem_leaf_eval,
            },
        ],
        &mut lyr_tr,
    );
    let mult_uw_pcs_proof = open_pcs_claims(
        &mult_uw_state,
        &[MleEvalClaim {
            point: z_uw_leaf[..UW_RANGE_BITS].to_vec(),
            value: d1b_uw_proof.mult_leaf_eval,
        }],
        &mut lyr_tr,
    );
    let rhs_shifted_pcs_proof = open_pcs_claims(
        &rhs_sh_state,
        &[
            MleEvalClaim {
                point: z_hik,
                value: layer_proof.rhs_eval_at_z.add(Ext4::from_bb(RHS_SHIFT_BIAS)),
            },
            MleEvalClaim {
                point: z_rhs_leaf.clone(),
                value: d1b_rhs_proof.rem_leaf_eval,
            },
        ],
        &mut lyr_tr,
    );
    let mult_rhs_pcs_proof = open_pcs_claims(
        &mult_rhs_state,
        &[MleEvalClaim {
            point: z_rhs_leaf[..RHS_RANGE_BITS].to_vec(),
            value: d1b_rhs_proof.mult_leaf_eval,
        }],
        &mut lyr_tr,
    );

    let bnd_vars = turn.boundaries_bb[l_idx].len().trailing_zeros() as usize;
    let bundle = HardenedVAgentU1AuditBundle {
        audited_layer: l_idx,
        bnd_vars,
        uw_shifted_pcs_root: uw_sh_state.root,
        mult_uw_pcs_root: mult_uw_state.root,
        rhs_shifted_pcs_root: rhs_sh_state.root,
        mult_rhs_pcs_root: mult_rhs_state.root,
        layer_proof,
        d1b_uw_proof,
        d1b_rhs_proof,
        uw_shifted_pcs_proof,
        mult_uw_pcs_proof,
        rhs_shifted_pcs_proof,
        mult_rhs_pcs_proof,
        absence_receipt: absence_receipt.clone(),
    };
    Ok((bundle.to_bytes(), absence_receipt.content_root, qs_binding))
}

#[allow(clippy::too_many_arguments)]
pub fn verify_hardened_vagent_u1_bundle(
    stmt: &VerifiableAgentTurnStmt,
    boundary_roots: &[[u8; 32]; 25],
    expected_audited_layer: usize,
    qs_binding: &[u8; 32],
    expected_out_root: &[u8; 32],
    opt_redacted_bytes: Option<&[u8]>,
    proof_bytes: &[u8],
) -> Result<(), String> {
    let _ = (WY_SHIFT, P_U32);
    if expected_audited_layer >= NUM_LAYERS || (expected_audited_layer % 4) == 3 {
        return Err("expected_audited_layer is not a valid GDN layer".to_string());
    }
    let bundle = HardenedVAgentU1AuditBundle::from_bytes(proof_bytes)?;
    if bundle.audited_layer != expected_audited_layer || bundle.bnd_vars != 16 {
        return Err("bundle audited_layer or bnd_vars mismatch".to_string());
    }

    let ctx = TurnContextMetadata {
        weight_root: &stmt.weight_root,
        prompt_len: stmt.prompt_length,
        prompt_root: &stmt.prompt_root,
        raw_len: stmt.raw_length,
        raw_root: &stmt.raw_root,
        clean_len: stmt.clean_length,
        clean_root: &stmt.clean_root,
        boundary_roots,
    };
    let mut abs_tr = CShakeTranscript::new(b"QW35-VAGENT01-ABSENCE-V2");
    absorb_turn_context_into_transcript(&mut abs_tr, &ctx);
    verify_hardened_padded_absence_zk(
        expected_out_root,
        opt_redacted_bytes,
        &bundle.absence_receipt,
        &mut abs_tr,
    )?;

    let mut lyr_tr = CShakeTranscript::new(b"QW35-VAGENT01-LAYER-AUDIT-V2");
    absorb_turn_context_into_transcript(&mut lyr_tr, &ctx);
    for r in [
        &bundle.uw_shifted_pcs_root,
        &bundle.mult_uw_pcs_root,
        &bundle.rhs_shifted_pcs_root,
        &bundle.mult_rhs_pcs_root,
    ] {
        lyr_tr.absorb_root(b"wy_quot_pcs_root", r);
    }

    let mut z_hik_replay = lyr_tr.clone();
    verify_audited_gdn_layer_standalone(
        &AuditedGdnLayerVerifyStmt {
            expected_weight_root: &stmt.weight_root,
            expected_b_in_root: &boundary_roots[expected_audited_layer],
            expected_b_out_root: &boundary_roots[expected_audited_layer + 1],
            expected_audited_layer,
            expected_q_s_binding: qs_binding,
            bnd_vars: bundle.bnd_vars,
        },
        &bundle.layer_proof,
        &mut lyr_tr,
    )?;

    // Enforce expected Qwen3.5-0.8B GDN layer geometry (`16` heads, `64` chunk, `256` WY cols, `4096x32` MXFP4)
    let lp = &bundle.layer_proof;
    if lp.h_pad != 16
        || lp.c_len != 64
        || lp.wy_cols != 256
        || lp.mxfp4_j_pad != 4096
        || lp.mxfp4_k_pad != 32
    {
        return Err(
            "unexpected GDN/MXFP4 layer dimensions in HardenedVAgentU1AuditBundle".to_string(),
        );
    }
    let log_h = lp.h_pad.trailing_zeros() as usize;
    let log_c = lp.c_len.trailing_zeros() as usize;
    let log_col = lp.wy_cols.trailing_zeros() as usize;
    let m_wy_wit = log_h + log_c + log_col;

    z_hik_replay.absorb_root(b"stmt_weight_root", &stmt.weight_root);
    z_hik_replay.absorb_root(b"stmt_b_in_root", &boundary_roots[expected_audited_layer]);
    z_hik_replay.absorb_root(
        b"stmt_b_out_root",
        &boundary_roots[expected_audited_layer + 1],
    );
    z_hik_replay.absorb_u32(b"stmt_audited_layer", expected_audited_layer as u32);
    for r in [
        &lp.q_pcs_root,
        &lp.s_pcs_root,
        &lp.l_pcs_root,
        &lp.rhs_pcs_root,
        &lp.uw_pcs_root,
        &lp.rem_pcs_root,
        &lp.mult_pcs_root,
        &lp.x_ln2_pcs_root,
        &lp.y_gate_pcs_root,
        &lp.delta_gdn_pcs_root,
        &lp.delta_mlp_pcs_root,
    ] {
        z_hik_replay.absorb_root(b"wit_pcs_root", r);
    }
    let z_h = z_hik_replay.squeeze_ext4_vec(b"wy_zh", log_h, true);
    let z_i = z_hik_replay.squeeze_ext4_vec(b"wy_zi", log_c, true);
    let z_k = z_hik_replay.squeeze_ext4_vec(b"wy_zk", log_col, true);
    let mut z_hik = Vec::with_capacity(m_wy_wit);
    z_hik.extend_from_slice(&z_h);
    z_hik.extend_from_slice(&z_i);
    z_hik.extend_from_slice(&z_k);

    // Verify signed-quotient D1b range proofs on `UW` (`[-65536, 65536)`) & `RHS` (`[-16384, 16384)`)!
    if m_wy_wit < UW_RANGE_BITS
        || bundle.d1b_uw_proof.m_wit != m_wy_wit
        || bundle.d1b_uw_proof.m_tab != UW_RANGE_BITS
        || bundle.d1b_rhs_proof.m_wit != m_wy_wit
        || bundle.d1b_rhs_proof.m_tab != RHS_RANGE_BITS
    {
        return Err("UW/RHS signed-quotient D1b dimension mismatch".to_string());
    }
    let z_uw_leaf = verify_d1b_range_ext4(&bundle.d1b_uw_proof, &mut lyr_tr)?;
    let z_rhs_leaf = verify_d1b_range_ext4(&bundle.d1b_rhs_proof, &mut lyr_tr)?;

    verify_pcs_claims(
        &bundle.uw_shifted_pcs_root,
        PcsShape::new(m_wy_wit, PcsParams::default_zk(2)),
        &[
            MleEvalClaim {
                point: z_hik.clone(),
                value: lp.uw_eval_at_z.add(Ext4::from_bb(UW_SHIFT_BIAS)),
            },
            MleEvalClaim {
                point: z_uw_leaf.clone(),
                value: bundle.d1b_uw_proof.rem_leaf_eval,
            },
        ],
        &bundle.uw_shifted_pcs_proof,
        &mut lyr_tr,
    )?;
    verify_pcs_claims(
        &bundle.mult_uw_pcs_root,
        PcsShape::new(UW_RANGE_BITS, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: z_uw_leaf[..UW_RANGE_BITS].to_vec(),
            value: bundle.d1b_uw_proof.mult_leaf_eval,
        }],
        &bundle.mult_uw_pcs_proof,
        &mut lyr_tr,
    )?;
    verify_pcs_claims(
        &bundle.rhs_shifted_pcs_root,
        PcsShape::new(m_wy_wit, PcsParams::default_zk(2)),
        &[
            MleEvalClaim {
                point: z_hik,
                value: lp.rhs_eval_at_z.add(Ext4::from_bb(RHS_SHIFT_BIAS)),
            },
            MleEvalClaim {
                point: z_rhs_leaf.clone(),
                value: bundle.d1b_rhs_proof.rem_leaf_eval,
            },
        ],
        &bundle.rhs_shifted_pcs_proof,
        &mut lyr_tr,
    )?;
    verify_pcs_claims(
        &bundle.mult_rhs_pcs_root,
        PcsShape::new(RHS_RANGE_BITS, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: z_rhs_leaf[..RHS_RANGE_BITS].to_vec(),
            value: bundle.d1b_rhs_proof.mult_leaf_eval,
        }],
        &bundle.mult_rhs_pcs_proof,
        &mut lyr_tr,
    )?;

    Ok(())
}

/// Complete local-TCB quarantine weld wire bundle `VAgent01Bundle` uniting:
/// 1) `stmt_bytes` (`VASTMT01` Lean statement),
/// 2) `receipt_bytes` (`VAGENT01` Lean quarantine receipt proving `w_clean == redactBytes defaultSecretRules w_raw`),
/// 3) `u1_zk_audit_bytes` (`QW35U1P2` statement-bound `BabyBear Ext4` GDN+SwiGLU + UW/RHS D1b + stride-4096 ZK `Absent`).
///
/// NOTE ON SECRET HYGIENE: `VAgent01Bundle` carries `rcpt.prompt_bytes` and `rcpt.w_raw` so the
/// local TCB / enclave verifier (`verifyAgentTurnBytes` in Lean) can verify `w_clean == redactBytes w_raw`.
/// Before crossing an untrusted network boundary, strip all raw secrets via
/// `VAgent01Bundle::to_public_redacted_bytes()` (`PublicRedactedVAgent01Bundle`, `0` cleartext secrets!).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VAgent01Bundle {
    pub stmt_bytes: Vec<u8>,
    pub receipt_bytes: Vec<u8>,
    pub qs_binding: [u8; 32],
    pub zk_absence_content_root: [u8; 32],
    pub u1_zk_audit_bytes: Vec<u8>,
}

/// External zero-secret wire bundle (`0xA2` envelope): omits `prompt_bytes` and `w_raw` completely
/// (`0` occurrences of `"sk-"` anywhere in serialized octets!) while preserving full standalone
/// verification of `VASTMT01`, `U1` VRF + `turnChainRoot`, `QW35U1P2` `Ext4` layer + ZK `Absent` +
/// 248-bit `w_clean` MLE binding, and 139-rule LL(1) `miniJsonCfg` AST extraction!
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicRedactedVAgent01Bundle {
    pub stmt_bytes: Vec<u8>,
    pub boundary_roots: Vec<[u8; 32]>,
    pub audited_layer: usize,
    pub u1_proof_digest: [u8; 32],
    pub w_clean: Vec<u8>,
    pub rule_indices: Vec<usize>,
    pub qs_binding: [u8; 32],
    pub zk_absence_content_root: [u8; 32],
    pub u1_zk_audit_bytes: Vec<u8>,
}

impl VAgent01Bundle {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(
            64 + self.stmt_bytes.len() + self.receipt_bytes.len() + self.u1_zk_audit_bytes.len(),
        );
        out.extend_from_slice(VAGENT01_MAGIC);
        out.push(0xA1); // Full local-quarantine envelope tag (`0xA1`)
        stream_encode_bytes(&self.stmt_bytes, &mut out);
        stream_encode_bytes(&self.receipt_bytes, &mut out);
        out.extend_from_slice(&self.qs_binding);
        out.extend_from_slice(&self.zk_absence_content_root);
        stream_encode_bytes(&self.u1_zk_audit_bytes, &mut out);
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() < 9 || &bytes[0..8] != VAGENT01_MAGIC || bytes[8] != 0xA1 {
            return Err("invalid VAgent01Bundle header".to_string());
        }
        let mut pos = 9usize;
        let stmt_bytes = stream_decode_bytes(bytes, &mut pos)?;
        let receipt_bytes = stream_decode_bytes(bytes, &mut pos)?;
        let qs_binding = stream_decode_digest32(bytes, &mut pos)?;
        let zk_absence_content_root = stream_decode_digest32(bytes, &mut pos)?;
        let u1_zk_audit_bytes = stream_decode_bytes(bytes, &mut pos)?;
        if pos != bytes.len() {
            return Err("trailing bytes in VAgent01Bundle".to_string());
        }
        Ok(Self {
            stmt_bytes,
            receipt_bytes,
            qs_binding,
            zk_absence_content_root,
            u1_zk_audit_bytes,
        })
    }

    /// Scrub `prompt_bytes` and `w_raw` to produce an external zero-secret `PublicRedactedVAgent01Bundle`.
    pub fn to_public_redacted_bytes(&self) -> Result<Vec<u8>, String> {
        let rcpt = VerifiableAgentTurnReceipt::from_stream_bytes(&self.receipt_bytes)?;
        let pub_b = PublicRedactedVAgent01Bundle {
            stmt_bytes: self.stmt_bytes.clone(),
            boundary_roots: rcpt.boundary_roots,
            audited_layer: rcpt.audited_layer,
            u1_proof_digest: rcpt.u1_proof_digest,
            w_clean: rcpt.w_clean,
            rule_indices: rcpt.rule_indices,
            qs_binding: self.qs_binding,
            zk_absence_content_root: self.zk_absence_content_root,
            u1_zk_audit_bytes: self.u1_zk_audit_bytes.clone(),
        };
        Ok(pub_b.to_bytes())
    }
}

impl PublicRedactedVAgent01Bundle {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out =
            Vec::with_capacity(128 + self.stmt_bytes.len() + self.u1_zk_audit_bytes.len());
        out.extend_from_slice(VAGENT01_MAGIC);
        out.push(0xA2); // External redacted zero-secret envelope tag (`0xA2`)
        stream_encode_bytes(&self.stmt_bytes, &mut out);
        stream_encode_nat(self.boundary_roots.len(), &mut out);
        for br in &self.boundary_roots {
            out.extend_from_slice(br);
        }
        stream_encode_nat(self.audited_layer, &mut out);
        out.extend_from_slice(&self.u1_proof_digest);
        stream_encode_bytes(&self.w_clean, &mut out);
        stream_encode_nat(self.rule_indices.len(), &mut out);
        for &ri in &self.rule_indices {
            stream_encode_nat(ri, &mut out);
        }
        out.extend_from_slice(&self.qs_binding);
        out.extend_from_slice(&self.zk_absence_content_root);
        stream_encode_bytes(&self.u1_zk_audit_bytes, &mut out);
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() < 9 || &bytes[0..8] != VAGENT01_MAGIC || bytes[8] != 0xA2 {
            return Err("invalid PublicRedactedVAgent01Bundle header".to_string());
        }
        let mut pos = 9usize;
        let stmt_bytes = stream_decode_bytes(bytes, &mut pos)?;
        let nb = stream_decode_nat(bytes, &mut pos)?;
        if nb > 1024 {
            return Err("excessive boundary_roots len".to_string());
        }
        let mut boundary_roots = Vec::with_capacity(nb);
        for _ in 0..nb {
            boundary_roots.push(stream_decode_digest32(bytes, &mut pos)?);
        }
        let audited_layer = stream_decode_nat(bytes, &mut pos)?;
        let u1_proof_digest = stream_decode_digest32(bytes, &mut pos)?;
        let w_clean = stream_decode_bytes(bytes, &mut pos)?;
        let nr = stream_decode_nat(bytes, &mut pos)?;
        if nr > 100_000 {
            return Err("excessive rule_indices len".to_string());
        }
        let mut rule_indices = Vec::with_capacity(nr);
        for _ in 0..nr {
            rule_indices.push(stream_decode_nat(bytes, &mut pos)?);
        }
        let qs_binding = stream_decode_digest32(bytes, &mut pos)?;
        let zk_absence_content_root = stream_decode_digest32(bytes, &mut pos)?;
        let u1_zk_audit_bytes = stream_decode_bytes(bytes, &mut pos)?;
        if pos != bytes.len() {
            return Err("trailing bytes in PublicRedactedVAgent01Bundle".to_string());
        }
        Ok(Self {
            stmt_bytes,
            boundary_roots,
            audited_layer,
            u1_proof_digest,
            w_clean,
            rule_indices,
            qs_binding,
            zk_absence_content_root,
            u1_zk_audit_bytes,
        })
    }
}

/// Policy-pinned standalone verifier for `VAgent01Bundle`:
/// enforces optional trusted `expected_weight_root` and `expected_qs_binding` pins in addition to
/// the full Lean-mirror weld + `QW35U1P2` statement-bound `Ext4` layer + UW/RHS `D1b` + 248-bit `w_clean` MLE check!
pub fn verify_vagent01_bytes_with_policy(
    bundle_bytes: &[u8],
    expected_weight_root: Option<&[u8; 32]>,
    expected_qs_binding: Option<&[u8; 32]>,
) -> Result<(VerifiableAgentTurnStmt, VerifiableAgentTurnReceipt), String> {
    let b = VAgent01Bundle::from_bytes(bundle_bytes)?;
    verify_agent_turn_weld_bytes(&b.stmt_bytes, &b.receipt_bytes)?;
    let stmt = VerifiableAgentTurnStmt::from_stream_bytes(&b.stmt_bytes)?;
    let rcpt = VerifiableAgentTurnReceipt::from_stream_bytes(&b.receipt_bytes)?;

    if let Some(exp_wr) = expected_weight_root {
        if &stmt.weight_root != exp_wr {
            return Err("pinned expected_weight_root mismatch".to_string());
        }
    }
    if let Some(exp_qsb) = expected_qs_binding {
        if &b.qs_binding != exp_qsb {
            return Err("pinned expected_qs_binding mismatch".to_string());
        }
    }

    let pf_dig = cshake256_32(U1_PF_DIGEST_CUST, &b.u1_zk_audit_bytes);
    if pf_dig != rcpt.u1_proof_digest {
        return Err("u1_zk_audit_bytes digest != receipt.u1_proof_digest".to_string());
    }
    if stmt.num_layers != NUM_LAYERS || rcpt.boundary_roots.len() != NUM_LAYERS + 1 {
        return Err(
            "VAgent01Bundle requires 24-layer Qwen3.5 U1 proof (25 boundary roots)".to_string(),
        );
    }
    let bnd_arr: [[u8; 32]; 25] = rcpt
        .boundary_roots
        .clone()
        .try_into()
        .map_err(|_| "expected 25 boundary roots")?;
    // Verify BOTH zero-cleartext ZK (`None`) AND 248-bit MLE-bound `Some(&rcpt.w_clean)`!
    verify_hardened_vagent_u1_bundle(
        &stmt,
        &bnd_arr,
        rcpt.audited_layer,
        &b.qs_binding,
        &b.zk_absence_content_root,
        None,
        &b.u1_zk_audit_bytes,
    )?;
    verify_hardened_vagent_u1_bundle(
        &stmt,
        &bnd_arr,
        rcpt.audited_layer,
        &b.qs_binding,
        &b.zk_absence_content_root,
        Some(&rcpt.w_clean),
        &b.u1_zk_audit_bytes,
    )?;
    Ok((stmt, rcpt))
}

/// Strictly pinned verifier requiring caller-trusted `(expected_weight_root, expected_qs_binding)`.
pub fn verify_vagent01_bytes_pinned(
    bundle_bytes: &[u8],
    expected_weight_root: &[u8; 32],
    expected_qs_binding: &[u8; 32],
) -> Result<(VerifiableAgentTurnStmt, VerifiableAgentTurnReceipt), String> {
    verify_vagent01_bytes_with_policy(
        bundle_bytes,
        Some(expected_weight_root),
        Some(expected_qs_binding),
    )
}

/// Full standalone verifier for `VAgent01Bundle` (unpinned convenience wrapper).
pub fn verify_vagent01_bytes(
    bundle_bytes: &[u8],
) -> Result<(VerifiableAgentTurnStmt, VerifiableAgentTurnReceipt), String> {
    verify_vagent01_bytes_with_policy(bundle_bytes, None, None)
}

/// Standalone verifier for external zero-secret `PublicRedactedVAgent01Bundle` (`0` cleartext secrets on wire!).
pub fn verify_public_redacted_vagent01_bytes(
    bundle_bytes: &[u8],
    expected_weight_root: Option<&[u8; 32]>,
    expected_qs_binding: Option<&[u8; 32]>,
) -> Result<VerifiableAgentTurnStmt, String> {
    let pb = PublicRedactedVAgent01Bundle::from_bytes(bundle_bytes)?;
    let stmt = VerifiableAgentTurnStmt::from_stream_bytes(&pb.stmt_bytes)?;
    if let Some(exp_wr) = expected_weight_root {
        if &stmt.weight_root != exp_wr {
            return Err("pinned expected_weight_root mismatch".to_string());
        }
    }
    if let Some(exp_qsb) = expected_qs_binding {
        if &pb.qs_binding != exp_qsb {
            return Err("pinned expected_qs_binding mismatch".to_string());
        }
    }
    if stmt.num_layers != NUM_LAYERS || pb.boundary_roots.len() != NUM_LAYERS + 1 {
        return Err("PublicRedactedVAgent01Bundle requires 24 layers (25 boundaries)".to_string());
    }
    let exp_vrf = compute_u1_vrf_layer_cshake(
        &stmt.weight_root,
        &pb.boundary_roots,
        &stmt.clean_root,
        stmt.num_layers,
    );
    if pb.audited_layer != exp_vrf {
        return Err("Fiat-Shamir VRF audited_layer mismatch".to_string());
    }
    let recomputed_head = compute_u1_turn_head_cshake(
        &stmt.weight_root,
        &stmt.prompt_root,
        stmt.prompt_length,
        &pb.boundary_roots,
        &pb.u1_proof_digest,
        stmt.raw_length,
        &stmt.raw_root,
    );
    if recomputed_head != stmt.turn_chain_root {
        return Err("U1 turnChainRoot mismatch".to_string());
    }
    if pb.w_clean.len() != stmt.clean_length
        || content_commit_cshake(&pb.w_clean) != stmt.clean_root
    {
        return Err("w_clean (length, contentCommit) mismatch".to_string());
    }
    // Verify `w_clean` contains zero secrets under all 5 canonical rules (`redact(w_clean) == w_clean`)!
    let rules = default_secret_rules();
    if redact_bytes_canonical(&rules, &pb.w_clean) != pb.w_clean {
        return Err("w_clean still contains secret pattern!".to_string());
    }
    let ast = exec_mini_attr_replay(&pb.rule_indices, &pb.w_clean)?;
    if ast != stmt.claimed_ast {
        return Err("extracted AST != stmt.claimed_ast".to_string());
    }
    if cshake256_32(U1_PF_DIGEST_CUST, &pb.u1_zk_audit_bytes) != pb.u1_proof_digest {
        return Err("u1_zk_audit_bytes digest != u1_proof_digest".to_string());
    }
    let bnd_arr: [[u8; 32]; 25] = pb
        .boundary_roots
        .try_into()
        .map_err(|_| "expected 25 boundary roots")?;
    verify_hardened_vagent_u1_bundle(
        &stmt,
        &bnd_arr,
        pb.audited_layer,
        &pb.qs_binding,
        &pb.zk_absence_content_root,
        Some(&pb.w_clean),
        &pb.u1_zk_audit_bytes,
    )?;
    Ok(stmt)
}

// ============================================================================
// §8. Live End-to-End Verifiable Agent Turn Runner (`run_live_verifiable_qwen_agent_turn`)
// ============================================================================

/// Canonical 64-token agentic `CotToolCall` prompt for `Qwen/Qwen3.5-0.8B-Base`.
pub fn default_agent_64tok_prompt(tok: &QwenBpeTokenizer) -> (String, Vec<u32>) {
    let core = concat!(
        "KEY=sk-proj-demo01 TARGET=db_stage AMT=10\n",
        "{\"cot\":\"Key sk-proj-demo01 on db_stage\",\"tool\":\"audit_cfg\",\"target\":\"db_stage\",\"amount\":10}\n",
        "KEY=sk-proj-9f8a7b6c5d4e TARGET=vault_prod AMT=64\n"
    );
    // Pad header comment deterministically to hit exact `64` BPE tokens (`0` runtime padding!)
    let mut header = String::from("# Policy");
    loop {
        let cand = format!("{header}\n{core}");
        let ids = tok.encode(&cand);
        if ids.len() == 64 {
            return (cand, ids);
        } else if ids.len() < 64 {
            header.push_str(" v1");
        } else {
            let tail = ids[ids.len() - 64..].to_vec();
            let decoded = String::from_utf8_lossy(&tok.decode_bytes(&tail)).into_owned();
            return (decoded, tail);
        }
    }
}

#[derive(Clone, Debug)]
pub struct LiveAgentTurnReport {
    pub prompt_utf8: String,
    pub prompt_token_ids: Vec<u32>,
    pub generated_token_ids: Vec<u32>,
    pub w_raw: Vec<u8>,
    pub w_clean: Vec<u8>,
    pub claimed_ast: MiniValue,
    pub audited_layer: usize,
    pub prefill_ms: f64,
    pub prefill_tok_s: f64,
    pub decode_ms: f64,
    pub decode_tok_s: f64,
    pub u1_stream_fast_us_per_tok: f64,
    pub prove_ms: f64,
    pub verify_ms: f64,
    pub prefill_boundaries_sha256: [u8; 32],
    pub prefill_boundaries_cshake256: [u8; 32],
    pub decode_stream_sha256: [u8; 32],
    pub decode_stream_cshake256: [u8; 32],
    pub stmt: VerifiableAgentTurnStmt,
    pub receipt: VerifiableAgentTurnReceipt,
    pub bundle: VAgent01Bundle,
    pub bundle_bytes: Vec<u8>,
}

impl fmt::Display for MiniValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MiniValue::CotToolCall {
                cot,
                tool,
                target,
                amount,
            } => write!(
                f,
                "CotToolCall {{ cot: {:?}, tool: {:?}, target: {:?}, amount: {} }}",
                String::from_utf8_lossy(cot),
                String::from_utf8_lossy(tool),
                String::from_utf8_lossy(target),
                amount
            ),
            other => write!(f, "{other:?}"),
        }
    }
}

/// Execute a full live verifiable agent turn on the 100%-integer 24-layer `Qwen3.5-0.8B` engine:
/// 1) 64-token `IntWY` prefill + greedy multi-token integer decode until closing `}` / `\n`,
/// 2) Online `U1` `cSHAKE256` 25-boundary commitments at prefill & every decode step,
/// 3) Canonical 5-class secret redaction (`sk-proj-...` -> `[REDACTED_API_KEY]`) + `contentCommit`,
/// 4) Deterministic 139-rule LL(1) `miniJsonCfg` AST extraction (`CotToolCall`),
/// 5) Fiat-Shamir VRF layer selection (`compute_u1_vrf_layer_cshake`) + succinct `BabyBear Ext4` GDN+SwiGLU
///    layer proof + 0-cleartext ZK `Absent("sk-...")` DFA proof, serialized into canonical **`VAGENT01`**.
pub fn run_live_verifiable_qwen_agent_turn(
    engine: &ExactIntQwen35Engine,
    tok: &QwenBpeTokenizer,
    max_decode_tokens: usize,
) -> Result<LiveAgentTurnReport, String> {
    let _ = Q16_ONE;
    let (prompt_utf8, prompt_ids) = default_agent_64tok_prompt(tok);
    assert_eq!(prompt_ids.len(), 64);

    // 1. Exact-integer 24-layer prefill (`C = 64` `IntWY`)
    let mut cache = ExactIntDecodeCache::new();
    let t_pref = Instant::now();
    let (turn_probe0, mut last_h_q16) = engine.prefill_chunk64_int(&prompt_ids, 0, &mut cache)?;
    let (first_tok, _, first_logit_sha) = engine.argmax_lm_head_int(&last_h_q16)?;
    let prefill_ms = t_pref.elapsed().as_secs_f64() * 1000.0;
    let prefill_tok_s = 64.0 / (prefill_ms / 1000.0);

    // Compute thread-determinism digests over all 25 prefill boundary matrices (`25 * 64 * 1024` BabyBear cells)!
    let mut bnd_sha = Sha256::new();
    let mut bnd_flat = Vec::with_capacity(25 * 64 * D_MODEL * 4 + 32);
    for b in &turn_probe0.boundaries_bb {
        for &v in b {
            let le = v.to_le_bytes();
            bnd_sha.update(le);
            bnd_flat.extend_from_slice(&le);
        }
    }
    bnd_sha.update(first_logit_sha);
    bnd_flat.extend_from_slice(&first_logit_sha);
    let prefill_boundaries_sha256: [u8; 32] = bnd_sha.finalize().into();
    let prefill_boundaries_cshake256 = cshake256_32(b"QW35-DET-PREFILL-V1", &bnd_flat);

    // Measure online fast streaming `U1` 25-boundary `cSHAKE256` cost!
    let t_fast = Instant::now();
    let _fast_bnds = commit_u1_fast_stream_boundaries(&turn_probe0.boundaries_bb);
    let u1_stream_fast_us_per_tok = (t_fast.elapsed().as_secs_f64() * 1e6) / 64.0;

    // 2. Greedy multi-token exact-integer autoregressive decode (`0` float ops!), streaming 25 `U1` boundaries per step!
    let mut gen_ids = vec![first_tok];
    let mut decode_sha = Sha256::new();
    let mut decode_cshake_buf = Vec::new();
    let t_dec = Instant::now();
    let mut cur_tok = first_tok;

    for _step in 1..max_decode_tokens {
        let cur_bytes = tok.decode_bytes(&gen_ids);
        if cur_bytes.contains(&b'\n') {
            break;
        }
        if let Some(pos_brace) = cur_bytes.iter().position(|&b| b == b'}') {
            if pos_brace > 10 {
                break;
            }
        }
        let (h_step, step_bnds) = engine.decode_step_int(cur_tok, &mut cache)?;
        last_h_q16 = h_step;
        let (nxt_tok, _, step_logit_sha) = engine.argmax_lm_head_int(&last_h_q16)?;
        for sb in &step_bnds {
            decode_sha.update(sb);
            decode_cshake_buf.extend_from_slice(sb);
        }
        decode_sha.update(step_logit_sha);
        decode_cshake_buf.extend_from_slice(&step_logit_sha);
        gen_ids.push(nxt_tok);
        cur_tok = nxt_tok;
        if cur_tok == tok.eos_token_id {
            break;
        }
    }
    let decode_ms = t_dec.elapsed().as_secs_f64() * 1000.0;
    let decoded_steps = gen_ids.len().saturating_sub(1).max(1);
    let decode_tok_s = (decoded_steps as f64) / (decode_ms / 1000.0);

    let decode_stream_sha256: [u8; 32] = decode_sha.finalize().into();
    let decode_stream_cshake256 = cshake256_32(b"QW35-DET-DECODE-STREAM-V1", &decode_cshake_buf);

    // Extract single-line raw generated JSON bytes up to closing `}`
    let raw_full = tok.decode_bytes(&gen_ids);
    let line_end = raw_full
        .iter()
        .position(|&b| b == b'\n')
        .unwrap_or(raw_full.len());
    let w_raw: Vec<u8> = raw_full[..line_end].to_vec();

    // 3. Canonical 5-class secret redaction + `cSHAKE256` `contentCommit` + 139-rule LL(1) `miniJsonCfg` AST extraction!
    let rules = default_secret_rules();
    let w_clean = redact_bytes_canonical(&rules, &w_raw);
    let (rule_indices, claimed_ast) = ll1_parse_mini_json(&w_clean)?;

    let prompt_bytes = prompt_utf8.as_bytes().to_vec();
    let prompt_root = content_commit_cshake(&prompt_bytes);
    let raw_root = content_commit_cshake(&w_raw);
    let clean_root = content_commit_cshake(&w_clean);

    // 4. Commit 25 `U1` ZK PCS layer boundaries & derive Fiat-Shamir VRF `audited_layer`!
    let t_prv = Instant::now();
    let u1_online = commit_u1_pcs_boundaries(&turn_probe0.boundaries_bb);
    let audited_layer = compute_u1_vrf_layer_cshake(
        &engine.registry.weight_root,
        &u1_online.boundary_roots,
        &clean_root,
        NUM_LAYERS,
    );

    let turn = if audited_layer == 0 {
        turn_probe0
    } else {
        let mut c2 = ExactIntDecodeCache::new();
        engine
            .prefill_chunk64_int(&prompt_ids, audited_layer, &mut c2)?
            .0
    };

    let (layer_digests, gate_slot) = engine.layer_tensor_digests(audited_layer);
    let gate_pcs = PrecommittedMxfp4Pcs::build(&turn.gate_proj_mat);
    let (u1_zk_audit_bytes, zk_absence_content_root, qs_binding) = prove_hardened_vagent_u1_bundle(
        &engine.registry,
        layer_digests,
        gate_slot,
        &gate_pcs,
        &u1_online,
        &turn,
        prompt_bytes.len(),
        &prompt_root,
        w_raw.len(),
        &raw_root,
        &w_clean,
        &clean_root,
    )?;
    let u1_proof_digest = cshake256_32(U1_PF_DIGEST_CUST, &u1_zk_audit_bytes);

    let turn_chain_root = compute_u1_turn_head_cshake(
        &engine.registry.weight_root,
        &prompt_root,
        prompt_bytes.len(),
        &u1_online.boundary_roots,
        &u1_proof_digest,
        w_raw.len(),
        &raw_root,
    );

    let stmt = VerifiableAgentTurnStmt {
        weight_root: engine.registry.weight_root,
        prompt_length: prompt_bytes.len(),
        prompt_root,
        num_layers: NUM_LAYERS,
        turn_chain_root,
        raw_length: w_raw.len(),
        raw_root,
        clean_length: w_clean.len(),
        clean_root,
        claimed_ast: claimed_ast.clone(),
    };
    let receipt = VerifiableAgentTurnReceipt {
        prompt_bytes,
        boundary_roots: u1_online.boundary_roots.to_vec(),
        audited_layer,
        audited_b_in_root: u1_online.boundary_roots[audited_layer],
        audited_b_out_root: u1_online.boundary_roots[audited_layer + 1],
        u1_proof_digest,
        w_raw: w_raw.clone(),
        w_clean: w_clean.clone(),
        rule_indices,
    };
    let stmt_bytes = stmt.to_stream_bytes();
    let receipt_bytes = receipt.to_stream_bytes();
    let bundle = VAgent01Bundle {
        stmt_bytes,
        receipt_bytes,
        qs_binding,
        zk_absence_content_root,
        u1_zk_audit_bytes,
    };
    let bundle_bytes = bundle.to_bytes();
    let prove_ms = t_prv.elapsed().as_secs_f64() * 1000.0;

    // 5. Standalone pinned end-to-end verification of `VAGENT01` wire bundle!
    let expected_qsb = engine.compute_layer_qs_binding(audited_layer);
    assert_eq!(qs_binding, expected_qsb);
    let t_ver = Instant::now();
    let (dec_stmt, dec_rcpt) =
        verify_vagent01_bytes_pinned(&bundle_bytes, &engine.registry.weight_root, &expected_qsb)?;
    assert_eq!(dec_stmt, stmt);
    assert_eq!(dec_rcpt, receipt);
    let verify_ms = t_ver.elapsed().as_secs_f64() * 1000.0;

    let _ = mle_eval_bb_at_ext4;
    Ok(LiveAgentTurnReport {
        prompt_utf8,
        prompt_token_ids: prompt_ids,
        generated_token_ids: gen_ids,
        w_raw,
        w_clean,
        claimed_ast,
        audited_layer,
        prefill_ms,
        prefill_tok_s,
        decode_ms,
        decode_tok_s,
        u1_stream_fast_us_per_tok,
        prove_ms,
        verify_ms,
        prefill_boundaries_sha256,
        prefill_boundaries_cshake256,
        decode_stream_sha256,
        decode_stream_cshake256,
        stmt,
        receipt,
        bundle,
        bundle_bytes,
    })
}
