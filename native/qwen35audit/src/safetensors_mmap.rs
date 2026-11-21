//! Zero-copy `libc::mmap` reader for HuggingFace `safetensors` shards (`BF16` / `F32`)
//! and deterministic OCP `MXFP4` (`E2M1`, block-32) offline `cSHAKE256` Merkle commitment
//! directly over the cached `Qwen/Qwen3.5-0.8B-Base` checkpoint (`0` copies, `0` downloads).

use crate::ext4::{cshake256_32, merkle_root_cshake, merkle_open_single_cshake, MerkleSinglePath, P};
use rayon::prelude::*;
use serde::Deserialize;
use std::collections::BTreeMap;
use std::fs::File;
use std::os::unix::io::AsRawFd;
use std::path::Path;
use std::ptr;

/// Default local read-only HuggingFace snapshot path for `Qwen/Qwen3.5-0.8B-Base`.
pub const QWEN35_SNAPSHOT_DIR: &str =
    "/Users/ember/.cache/huggingface/hub/models--Qwen--Qwen3.5-0.8B-Base/snapshots/dc7cdfe2ee4154fa7e30f5b51ca41bfa40174e68";
pub const QWEN35_SAFETENSORS_FILE: &str =
    "/Users/ember/.cache/huggingface/hub/models--Qwen--Qwen3.5-0.8B-Base/snapshots/dc7cdfe2ee4154fa7e30f5b51ca41bfa40174e68/model.safetensors-00001-of-00001.safetensors";
pub const QWEN35_TOKENIZER_FILE: &str =
    "/Users/ember/.cache/huggingface/hub/models--Qwen--Qwen3.5-0.8B-Base/snapshots/dc7cdfe2ee4154fa7e30f5b51ca41bfa40174e68/tokenizer.json";

/// Fixed-point integer shifts chosen so real `Qwen3.5-0.8B` `3584`-wide contractions stay `< 5e6 << P_BB / 4`
/// (`0` BabyBear wraparound across all 24 layers).
pub const ACT_SHIFT: u32 = 7;
pub const ACT_SCALE: i32 = 1 << ACT_SHIFT; // 128 (`[-256.0, 255.99]` fits in `i16` with zero outlier clipping)
pub const W_SCALE_SHIFT: i32 = 10;
pub const W_SCALE_BASE: f32 = (1u32 << W_SCALE_SHIFT) as f32; // 1024 (`val = (e2m1_x2 / 2) * (S / 1024)`)
pub const WY_SHIFT: u32 = 12;
pub const WY_SCALE: i64 = 1 << WY_SHIFT; // 4096

/// Doubled OCP `MXFP4` (`E2M1`) magnitudes indexed by `nibble & 7`:
/// `{0, 0.5, 1.0, 1.5, 2.0, 3.0, 4.0, 6.0} * 2 = {0, 1, 2, 3, 4, 6, 8, 12}`.
pub const E2M1_X2_MAGS: [u32; 8] = [0, 1, 2, 3, 4, 6, 8, 12];

/// Parsed metadata for a single tensor in the `safetensors` JSON header.
#[derive(Debug, Clone, Deserialize)]
pub struct TensorInfo {
    pub dtype: String,
    pub shape: Vec<usize>,
    data_offsets: [usize; 2],
}

impl TensorInfo {
    #[inline]
    pub fn data_offsets(&self) -> [usize; 2] {
        self.data_offsets
    }
}

/// Zero-copy `libc::mmap` handle over a `safetensors` shard.
pub struct MmapSafetensors {
    ptr: *const u8,
    len: usize,
    data_start: usize,
    pub header_len: usize,
    pub tensors: BTreeMap<String, TensorInfo>,
}

unsafe impl Send for MmapSafetensors {}
unsafe impl Sync for MmapSafetensors {}

impl Drop for MmapSafetensors {
    fn drop(&mut self) {
        if !self.ptr.is_null() && self.len > 0 {
            unsafe {
                libc::munmap(self.ptr as *mut libc::c_void, self.len);
            }
        }
    }
}

struct RawMmapGuard {
    ptr: *mut libc::c_void,
    len: usize,
}

impl Drop for RawMmapGuard {
    fn drop(&mut self) {
        if !self.ptr.is_null() && self.len > 0 {
            unsafe {
                libc::munmap(self.ptr, self.len);
            }
        }
    }
}

impl MmapSafetensors {
    /// Memory-map a `safetensors` file read-only (`PROT_READ`, `MAP_PRIVATE`) and parse its header.
    pub fn open(path: impl AsRef<Path>) -> Result<Self, String> {
        let file = File::open(path.as_ref())
            .map_err(|e| format!("failed to open safetensors {}: {e}", path.as_ref().display()))?;
        let len_u64 = file
            .metadata()
            .map_err(|e| format!("metadata failed: {e}"))?
            .len();
        let len = usize::try_from(len_u64)
            .map_err(|_| "safetensors file exceeds usize::MAX".to_string())?;
        if len < 8 || len > isize::MAX as usize {
            return Err("invalid safetensors file length".to_string());
        }
        let ptr = unsafe {
            libc::mmap(
                ptr::null_mut(),
                len,
                libc::PROT_READ,
                libc::MAP_PRIVATE,
                file.as_raw_fd(),
                0,
            )
        };
        if ptr == libc::MAP_FAILED {
            return Err("libc::mmap failed".to_string());
        }
        let mut guard = RawMmapGuard { ptr, len };
        let ptr_u8 = ptr as *const u8;
        let bytes = unsafe { std::slice::from_raw_parts(ptr_u8, len) };
        let header_len_u64 = u64::from_le_bytes(bytes[0..8].try_into().unwrap());
        let header_len = usize::try_from(header_len_u64)
            .map_err(|_| "header_len exceeds usize::MAX".to_string())?;
        let data_start = 8usize
            .checked_add(header_len)
            .ok_or_else(|| "header_len overflow".to_string())?;
        if data_start > len {
            return Err("header_len exceeds file size".to_string());
        }

        let raw_map: BTreeMap<String, serde_json::Value> =
            serde_json::from_slice(&bytes[8..data_start])
                .map_err(|e| format!("header JSON parse error: {e}"))?;
        let mut tensors = BTreeMap::new();
        for (k, v) in raw_map {
            if k == "__metadata__" {
                continue;
            }
            let info: TensorInfo = serde_json::from_value(v)
                .map_err(|e| format!("invalid tensor entry {k}: {e}"))?;
            let end_abs = data_start
                .checked_add(info.data_offsets[1])
                .ok_or_else(|| format!("offset overflow for tensor {k}"))?;
            if info.data_offsets[0] > info.data_offsets[1] || end_abs > len {
                return Err(format!("out-of-bounds offsets for tensor {k}"));
            }
            tensors.insert(k, info);
        }

        // Disarm guard now that ownership transfers to `Self`.
        guard.ptr = ptr::null_mut();
        guard.len = 0;
        Ok(Self {
            ptr: ptr_u8,
            len,
            data_start,
            header_len,
            tensors,
        })
    }

    /// Zero-copy raw byte slice for `name`.
    #[inline]
    pub fn tensor_bytes(&self, name: &str) -> Result<(&TensorInfo, &[u8]), String> {
        let info = self
            .tensors
            .get(name)
            .ok_or_else(|| format!("missing tensor {name}"))?;
        let start = self
            .data_start
            .checked_add(info.data_offsets[0])
            .ok_or_else(|| format!("start offset overflow for tensor {name}"))?;
        let end = self
            .data_start
            .checked_add(info.data_offsets[1])
            .ok_or_else(|| format!("end offset overflow for tensor {name}"))?;
        if start > end || end > self.len {
            return Err(format!("out-of-bounds slice for tensor {name}"));
        }
        let all_bytes = unsafe { std::slice::from_raw_parts(self.ptr, self.len) };
        Ok((info, &all_bytes[start..end]))
    }

    /// Convert a `BF16` or `F32` tensor into `Vec<f32>` directly from the mmap slice.
    pub fn read_f32(&self, name: &str) -> Result<(Vec<usize>, Vec<f32>), String> {
        let (info, raw) = self.tensor_bytes(name)?;
        let numel: usize = info.shape.iter().product();
        match info.dtype.as_str() {
            "BF16" => {
                if raw.len() != numel * 2 {
                    return Err(format!("BF16 byte length mismatch on {name}"));
                }
                let out: Vec<f32> = raw
                    .chunks_exact(2)
                    .map(|b| {
                        let bits = u16::from_le_bytes([b[0], b[1]]);
                        f32::from_bits((bits as u32) << 16)
                    })
                    .collect();
                Ok((info.shape.clone(), out))
            }
            "F32" => {
                if raw.len() != numel * 4 {
                    return Err(format!("F32 byte length mismatch on {name}"));
                }
                let out: Vec<f32> = raw
                    .chunks_exact(4)
                    .map(|b| f32::from_le_bytes([b[0], b[1], b[2], b[3]]))
                    .collect();
                Ok((info.shape.clone(), out))
            }
            other => Err(format!("unsupported dtype {other} on {name}")),
        }
    }
}

/// Decode a canonical 4-bit OCP `E2M1` nibble (`0..15`, bit 3 = sign, bits `0..2` = magnitude)
/// into its signed doubled integer in `{-12, -8, -6, -4, -3, -2, -1, 0, 1, 2, 3, 4, 6, 8, 12}`.
#[inline]
pub fn decode_e2m1_x2_i32(nibble: u8) -> i32 {
    let mag = E2M1_X2_MAGS[(nibble & 7) as usize] as i32;
    if mag == 0 || (nibble & 8) == 0 {
        mag
    } else {
        -mag
    }
}

/// Decode a canonical 4-bit OCP `E2M1` nibble into canonical BabyBear `[0, P)`.
#[inline]
pub fn decode_e2m1_x2_bb(nibble: u8) -> u32 {
    let mag = E2M1_X2_MAGS[(nibble & 7) as usize];
    if mag == 0 || (nibble & 8) == 0 {
        mag
    } else {
        (P as u32) - mag
    }
}

/// Quantize a single normalized float `v / scale_pow2` (`|u| <= 6.0`) to canonical 4-bit E2M1 nibble
/// (`-0` canonicalized to `0`).
#[inline]
pub fn quantize_scalar_e2m1_nibble(u: f32) -> u8 {
    let ax2 = u.abs() * 2.0; // compare against doubled magnitudes `[0, 1, 2, 3, 4, 6, 8, 12]`
    let mag_idx: u8 = if ax2 < 0.5 {
        0
    } else if ax2 < 1.5 {
        1
    } else if ax2 < 2.5 {
        2
    } else if ax2 < 3.5 {
        3
    } else if ax2 < 5.0 {
        4
    } else if ax2 < 7.0 {
        5
    } else if ax2 < 10.0 {
        6
    } else {
        7
    };
    if mag_idx == 0 {
        0
    } else if u < 0.0 {
        8 | mag_idx
    } else {
        mag_idx
    }
}

/// Quantized OCP `MXFP4` (`E2M1`, block-32) matrix ready for 0-mul Horner proving & `cSHAKE256` commitment.
#[derive(Debug, Clone)]
pub struct Mxfp4Matrix {
    pub name: String,
    pub rows_orig: usize,
    pub rows_pad: usize,
    pub cols_orig: usize,
    pub blocks_per_row: usize,
    /// `[rows_pad * blocks_per_row * 32]` canonical nibbles in `0..16` (`0` on padded rows).
    pub nibbles: Vec<u8>,
    /// `[rows_pad * blocks_per_row]` non-negative integer block scales in BabyBear (`< 2^20`).
    pub scales: Vec<u32>,
    /// `cSHAKE256` digest of `(rows_orig, rows_pad, cols_orig, packed_nibbles, scales_le)`.
    pub digest: [u8; 32],
}

impl Mxfp4Matrix {
    /// Quantize a 2D `BF16` tensor directly from `MmapSafetensors` in `rayon` parallel over rows,
    /// padding `rows_orig` up to `rows_orig.next_power_of_two()` with zero rows for hypercube MLE indexing.
    pub fn from_safetensors(mmap: &MmapSafetensors, name: &str) -> Result<Self, String> {
        let (info, raw) = mmap.tensor_bytes(name)?;
        if info.shape.len() != 2 || info.dtype != "BF16" {
            return Err(format!(
                "expected 2D BF16 tensor for {name}, got {:?} {}",
                info.shape, info.dtype
            ));
        }
        let rows_orig = info.shape[0];
        let cols_orig = info.shape[1];
        if cols_orig % 32 != 0 {
            return Err(format!("cols_orig {cols_orig} not divisible by 32 on {name}"));
        }
        let rows_pad = rows_orig.next_power_of_two();
        let blocks_per_row = cols_orig / 32;
        let row_bytes = cols_orig * 2;

        let mut nibbles = vec![0u8; rows_pad * cols_orig];
        let mut scales = vec![0u32; rows_pad * blocks_per_row];

        nibbles[..rows_orig * cols_orig]
            .par_chunks_mut(cols_orig)
            .zip(scales[..rows_orig * blocks_per_row].par_chunks_mut(blocks_per_row))
            .enumerate()
            .for_each(|(r, (nib_row, sc_row))| {
                let r_raw = &raw[r * row_bytes..(r + 1) * row_bytes];
                for blk in 0..blocks_per_row {
                    let b_raw = &r_raw[blk * 64..(blk + 1) * 64];
                    let mut vals = [0.0f32; 32];
                    let mut max_abs = 0.0f32;
                    for b in 0..32 {
                        let bits = u16::from_le_bytes([b_raw[2 * b], b_raw[2 * b + 1]]);
                        let v = f32::from_bits((bits as u32) << 16);
                        vals[b] = v;
                        let av = v.abs();
                        if av > max_abs {
                            max_abs = av;
                        }
                    }
                    if max_abs == 0.0 {
                        sc_row[blk] = 0;
                        for b in 0..32 {
                            nib_row[blk * 32 + b] = 0;
                        }
                    } else {
                        let exp_i = (max_abs / 6.0).log2().ceil() as i32;
                        let exp_clamped = exp_i.clamp(-W_SCALE_SHIFT, 8);
                        let scale_int = 1u32 << ((exp_clamped + W_SCALE_SHIFT) as u32);
                        let scale_f32 = (scale_int as f32) / W_SCALE_BASE;
                        sc_row[blk] = scale_int;
                        for b in 0..32 {
                            nib_row[blk * 32 + b] = quantize_scalar_e2m1_nibble(vals[b] / scale_f32);
                        }
                    }
                }
            });

        let digest = Self::compute_digest(name, rows_orig, rows_pad, cols_orig, &nibbles, &scales);
        Ok(Self {
            name: name.to_string(),
            rows_orig,
            rows_pad,
            cols_orig,
            blocks_per_row,
            nibbles,
            scales,
            digest,
        })
    }

    pub fn compute_digest(
        name: &str,
        rows_orig: usize,
        rows_pad: usize,
        cols_orig: usize,
        nibbles: &[u8],
        scales: &[u32],
    ) -> [u8; 32] {
        let mut buf = Vec::with_capacity(64 + nibbles.len() / 2 + scales.len() * 4);
        buf.extend_from_slice(&(name.len() as u32).to_le_bytes());
        buf.extend_from_slice(name.as_bytes());
        buf.extend_from_slice(&(rows_orig as u32).to_le_bytes());
        buf.extend_from_slice(&(rows_pad as u32).to_le_bytes());
        buf.extend_from_slice(&(cols_orig as u32).to_le_bytes());
        for pair in nibbles.chunks_exact(2) {
            buf.push((pair[0] & 0x0F) | ((pair[1] & 0x0F) << 4));
        }
        for &s in scales {
            buf.extend_from_slice(&s.to_le_bytes());
        }
        cshake256_32(b"QW35-MXFP4-MAT-V1", &buf)
    }

    /// Expand canonical E2M1 nibbles into canonical BabyBear elements `[rows_pad * cols_orig]`
    /// (`j` at low bits `0..log_j`, `k` at middle bits `log_j..log_j+log_k`, `b` at high bits — or
    /// `(j * blocks_per_row + k) * 32 + b` matching `prove_mxfp4_delayed_bjk_horner_ext4`).
    pub fn to_bb_table_lsb_bjk(&self) -> Vec<u32> {
        // Layout matching `prove_mxfp4_delayed_bjk_horner_ext4`:
        // After `b` (`5` bits), `j` (`log_j` bits), `k` (`log_k` bits), MLE `Q̂(c_b, c_j, c_k)` has
        // `b` at bits `0..5`, `j` at bits `5..5+log_j`, `k` at bits `5+log_j..5+log_j+log_k`!
        let j_len = self.rows_pad;
        let k_len = self.blocks_per_row;
        let mut out = vec![0u32; j_len * k_len * 32];
        for j in 0..j_len {
            for k in 0..k_len {
                let src = (j * k_len + k) * 32;
                let dst_jk = (k * j_len + j) * 32;
                for b in 0..32 {
                    out[dst_jk + b] = decode_e2m1_x2_bb(self.nibbles[src + b]);
                }
            }
        }
        out
    }

    /// Layout `S` as `k * rows_pad + j` (`j` at low bits `0..log_j`, `k` at high bits `log_j..log_j+log_k`),
    /// matching `Ŝ(c_j, c_k)` at the end of `prove_mxfp4_delayed_bjk_horner_ext4`.
    pub fn scales_table_lsb_jk(&self) -> Vec<u32> {
        let j_len = self.rows_pad;
        let k_len = self.blocks_per_row;
        let mut out = vec![0u32; j_len * k_len];
        for j in 0..j_len {
            for k in 0..k_len {
                out[k * j_len + j] = self.scales[j * k_len + k];
            }
        }
        out
    }
}

/// Offline `cSHAKE256` Merkle weight registry across all 24 layers of `Qwen/Qwen3.5-0.8B-Base`.
#[derive(Debug, Clone)]
pub struct Qwen35WeightRegistry {
    /// 32-leaf (`24` real layers padded to `32`) `cSHAKE256` Merkle root binding all 24 layers' `MXFP4` weights.
    pub weight_root: [u8; 32],
    pub layer_digests: Vec<[u8; 32]>,
    pub total_quantized_params: usize,
    pub total_tensors_committed: usize,
}

impl Qwen35WeightRegistry {
    /// Returns the canonical tensor names for layer `layer_idx` (`0..24`).
    pub fn layer_tensor_names(layer_idx: usize) -> Vec<String> {
        let pfx = format!("model.language_model.layers.{layer_idx}");
        let is_full_attn = (layer_idx % 4) == 3;
        if is_full_attn {
            vec![
                format!("{pfx}.self_attn.q_proj.weight"),
                format!("{pfx}.self_attn.k_proj.weight"),
                format!("{pfx}.self_attn.v_proj.weight"),
                format!("{pfx}.self_attn.o_proj.weight"),
                format!("{pfx}.mlp.gate_proj.weight"),
                format!("{pfx}.mlp.up_proj.weight"),
                format!("{pfx}.mlp.down_proj.weight"),
            ]
        } else {
            vec![
                format!("{pfx}.linear_attn.in_proj_qkv.weight"),
                format!("{pfx}.linear_attn.in_proj_z.weight"),
                format!("{pfx}.linear_attn.in_proj_b.weight"),
                format!("{pfx}.linear_attn.in_proj_a.weight"),
                format!("{pfx}.linear_attn.out_proj.weight"),
                format!("{pfx}.mlp.gate_proj.weight"),
                format!("{pfx}.mlp.up_proj.weight"),
                format!("{pfx}.mlp.down_proj.weight"),
            ]
        }
    }

    /// Quantize & `cSHAKE256`-Merkle-commit all 24 pretrained text layers directly from `MmapSafetensors`
    /// in parallel across `rayon` worker threads.
    pub fn commit_all_24_layers(mmap: &MmapSafetensors) -> Result<Self, String> {
        let per_layer: Result<Vec<([u8; 32], usize, usize)>, String> = (0..24usize)
            .into_par_iter()
            .map(|l| {
                let names = Self::layer_tensor_names(l);
                let mut layer_buf = Vec::with_capacity(4 + names.len() * 32);
                layer_buf.extend_from_slice(&(l as u32).to_le_bytes());
                let mut params = 0usize;
                for name in &names {
                    let mat = Mxfp4Matrix::from_safetensors(mmap, name)?;
                    params += mat.rows_orig * mat.cols_orig;
                    layer_buf.extend_from_slice(&mat.digest);
                }
                let l_digest = cshake256_32(b"QW35-LAYER-WEIGHT-LEAF-V1", &layer_buf);
                Ok((l_digest, params, names.len()))
            })
            .collect();

        let per_layer = per_layer?;
        let mut layer_digests = Vec::with_capacity(32);
        let mut total_quantized_params = 0usize;
        let mut total_tensors_committed = 0usize;
        for (d, p, c) in per_layer {
            layer_digests.push(d);
            total_quantized_params += p;
            total_tensors_committed += c;
        }
        while layer_digests.len() < 32 {
            layer_digests.push([0u8; 32]);
        }
        let weight_root = merkle_root_cshake(b"QW35-GLOBAL-WEIGHT-TREE-V1", &layer_digests);
        Ok(Self {
            weight_root,
            layer_digests,
            total_quantized_params,
            total_tensors_committed,
        })
    }

    /// Produce a 5-sibling `cSHAKE256` authentication path opening `layer_idx` against `weight_root`.
    pub fn open_layer(&self, layer_idx: usize) -> MerkleSinglePath {
        merkle_open_single_cshake(b"QW35-GLOBAL-WEIGHT-TREE-V1", &self.layer_digests, layer_idx)
    }
}
