#!/usr/bin/env python3
"""
real_qwen35_gdn_eval.py — Real Pretrained `Qwen/Qwen3.5-0.8B-Base` (18 Gated DeltaNet + 6 GQA)
Offline Evaluation, Quantization Fidelity Audit (`FP8-E4M3`, `Mixed-MXFP4`, `Pure-MXFP4` +
Division-Free Integer `C=64` Chunkwise WY), and Compact Deterministic Binary Bundle Export.

2026-11-21 — `qwen35-neon-eval` (helper to `@real-qwen35-zk-audit` on `real_systems_wave_2026_11_21`).

======================================================================================
BINARY EXPORT FORMAT (`--export <path>`, deterministic little-endian, < 25 MB)
======================================================================================
All multi-byte integers are little-endian (`<`). Strings are raw UTF-8 with a `u32` byte
length prefix and NO trailing NUL byte and NO implicit padding.

Offset 0:
  1. Magic & Header (64 bytes total):
     - [0..8]    magic              : [u8; 8] = b"QW35AUD1"
     - [8..12]   version            : u32     = 1
     - [12..16]  c_len              : u32     = 64   (chunk/sequence length)
     - [16..20]  d_model            : u32     = 1024 (hidden size)
     - [20..24]  h_v                : u32     = 16   (GDN value/key heads)
     - [24..28]  d_k                : u32     = 128  (GDN key head dim)
     - [28..32]  d_v                : u32     = 128  (GDN value head dim)
     - [32..36]  d_ff               : u32     = 3584 (SwiGLU intermediate size)
     - [36..40]  audited_layer_idx  : u32     = 0    (GDN Layer 0)
     - [40..44]  m_wy               : u32     = 4096 (WY fixed-point denominator)
     - [44..48]  act_scale_hidden   : u32     = 512  (scale for H_boundaries)
     - [48..52]  act_scale_ln1      : u32     = 512  (scale for X_ln1)
     - [52..56]  act_scale_gdn_y    : u32     = 2048 (scale for X_gdn_y)
     - [56..60]  act_scale_ln2      : u32     = 512  (scale for X_ln2)
     - [60..64]  num_mxfp4_mats     : u32     = 3    (in_proj_z, out_proj, mlp.gate_proj)

  2. Prompt & Real P5 Completion (variable length):
     - prompt_token_ids : u32[64]              (256 bytes)
     - gen_len          : u32                  (4 bytes)
     - gen_bytes        : u8[gen_len]          (UTF-8 completion on P5 containing real "sk-proj-...")

  3. All 25 Layer Boundary Hidden States (3,276,800 bytes = 3.125 MiB):
     - H_boundaries     : i16[25, 64, 1024]    (L0 input .. L24 final output, scale = act_scale_hidden)

  4. Audited GDN Layer 0 Division-Free C=64 WY Integer Witness (2,883,584 bytes = 2.75 MiB):
     - L_tilde          : i32[16, 64, 64]      (262,144 B; strictly lower-triangular: L[h,i,j]=0 for j>=i)
     - RHS              : i32[16, 64, 256]     (1,048,576 B; [U_rhs (128) | W_rhs (128)])
     - UW               : i32[16, 64, 256]     (1,048,576 B; [U (128) | W (128)])
     - R_rem            : u16[16, 64, 256]     (524,288 B; 0 <= R_rem < 4096)
     Exact integer identity verified over Z for all 16 * 64 * 256 = 262,144 entries:
       sum_{j=0}^{63} L_tilde[h, i, j] * UW[h, j, c]
         == M_wy * (RHS[h, i, c] - UW[h, i, c]) + (M_wy // 2) - R_rem[h, i, c]
     with max |LHS| < P_BB // 2 (P_BB = 2013265921).

  5. Audited Layer 0 Real INT16 Input Activations (524,288 bytes = 0.50 MiB):
     - X_ln1            : i16[64, 1024]        (131,072 B; input_selector = 0, scale = act_scale_ln1)
     - X_gdn_y          : i16[64, 2048]        (262,144 B; input_selector = 1, scale = act_scale_gdn_y)
     - X_ln2            : i16[64, 1024]        (131,072 B; input_selector = 2, scale = act_scale_ln2)

  6. Audited Layer 0 OCP MXFP4 E2M1 Matrix Records (`num_mxfp4_mats = 3`, ~12.5 MiB total):
     Each record is packed back-to-back:
     - name_len         : u32
     - name_utf8        : u8[name_len]         ("linear_attn.in_proj_z", "linear_attn.out_proj", "mlp.gate_proj")
     - input_selector   : u32                  (0 = X_ln1, 1 = X_gdn_y, 2 = X_ln2)
     - orig_rows        : u32                  (2048, 1024, 3584)
     - J_pad            : u32                  (2048, 1024, 4096; power-of-2 with zero-padded tail rows)
     - in_dim           : u32                  (1024, 2048, 1024; power-of-2)
     - K_blocks         : u32                  (in_dim // 32: 32, 64, 32)
     - e_floor          : i32                  (base power-of-2 exponent: W_deq = decode_e2m1_x2(Q) * S * 2^(e_floor - 1))
     - Q_nibbles        : u8[J_pad, K_blocks, 32]   (values in 0..15; -0 canonicalized to 0)
     - S_scales         : u32[J_pad, K_blocks]      (power-of-2 integer scales >= 1)
     - Y_raw            : i64[64, J_pad]            (exact integer contraction, max |Y_raw| < P_BB // 2)

     OCP MXFP4 E2M1 nibble decoding table (`decode_e2m1_x2(nib)` for `nib in 0..15`):
       [0, 1, 2, 3, 4, 6, 8, 12, 0, -1, -2, -3, -4, -6, -8, -12]
       (bit 3 = sign, bits 2..1 = exp, bit 0 = mantissa; nibble 8 (-0) is never emitted).
     Exact integer identity verified over Z for every (i, j):
       Y_raw[i, j] == sum_{k=0}^{K_blocks-1} sum_{b=0}^{31} X[i, k*32 + b] * decode_e2m1_x2(Q[j, k, b]) * S[j, k].

Total bundle size: ~19.8 MB (< 25 MB).

Usage:
  /Users/ember/.cache/uv/environments-v2/22c912b003d45dd8/62b316b52f48579c/bin/python \\
      research/real_systems_wave_2026_11_21/experiments/real_qwen35_gdn_eval.py \\
      --export /tmp/qwen35_real_layer_turn.bin
"""

from __future__ import annotations

import sys

_UV_TORCH_ARCHIVE = "/Users/ember/.cache/uv/archive-v0/6M8GPysv1WhaxV-r"
if _UV_TORCH_ARCHIVE not in sys.path:
    sys.path.insert(0, _UV_TORCH_ARCHIVE)

import argparse
import json
import math
import os
import struct
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import numpy as np
import torch
import torch.nn.functional as F
from safetensors import safe_open
from tokenizers import Tokenizer


# ======================================================================================
# 0. Constants & Exact OCP Codebooks
# ======================================================================================
MODEL_SNAPSHOT = Path(
    "/Users/ember/.cache/huggingface/hub/"
    "models--Qwen--Qwen3.5-0.8B-Base/snapshots/"
    "dc7cdfe2ee4154fa7e30f5b51ca41bfa40174e68"
)
SAFETENSORS_PATH = MODEL_SNAPSHOT / "model.safetensors-00001-of-00001.safetensors"
CONFIG_PATH = MODEL_SNAPSHOT / "config.json"
TOKENIZER_PATH = MODEL_SNAPSHOT / "tokenizer.json"

P_BB = (1 << 31) - (1 << 27) + 1  # BabyBear prime = 2,013,265,921
P_BB_HALF = P_BB // 2             # 1,006,632,960

NUM_LAYERS = 24
D_MODEL = 1024
D_FF = 3584
VOCAB_SIZE = 248320
RMS_EPS = 1e-6

# GDN (18 layers: (l + 1) % 4 != 0)
GDN_H = 16
GDN_D = 128
GDN_CONV_W = 4

# GQA (6 layers: (l + 1) % 4 == 0 -> {3, 7, 11, 15, 19, 23})
GQA_HQ = 8
GQA_HKV = 2
GQA_DH = 256
GQA_ROT_DIM = 64
ROPE_THETA = 10_000_000.0

# Fixed-point scales
M_WY = 4096
WY_SHIFT = 12
K_WY_SHIFT = 12     # K_SCALE = 4096 for L2-normalized q, k in [-1, 1]
K_WY_SCALE = 1 << K_WY_SHIFT
ACT_SCALE = 512     # Fixed INT16 export scale for H_boundaries, X_ln1, X_ln2
ACT_SCALE_GDN_Y = 2048  # Fixed INT16 export scale for X_gdn_y (max ~2.6 -> fits easily in i16)
INT16_MIN, INT16_MAX = -32768, 32767

# OCP MXFP4 E2M1 exact 16-entry nibble decode table (x2 integer values)
# Bit layout: bit3=sign, bit2..1=exp, bit0=mantissa; nibble 8 (-0) canonicalized to 0.
E2M1_NIBBLE_TO_X2 = np.array(
    [0, 1, 2, 3, 4, 6, 8, 12, 0, -1, -2, -3, -4, -6, -8, -12], dtype=np.int64
)
# Valid canonical nibbles (15 entries, excluding 8 = -0) sorted by value:
_E2M1_SORTED_NIBS = np.array(
    [15, 14, 13, 12, 11, 10, 9, 0, 1, 2, 3, 4, 5, 6, 7], dtype=np.uint8
)
_E2M1_SORTED_X2 = E2M1_NIBBLE_TO_X2[_E2M1_SORTED_NIBS].astype(np.float32)  # [-12..12]
# Midpoints between consecutive E2M1_x2 values for O(1) bucketize quantization:
_E2M1_MIDPOINTS_X2 = 0.5 * (_E2M1_SORTED_X2[:-1] + _E2M1_SORTED_X2[1:])


def _build_fp8_e4m3_grid() -> np.ndarray:
    """Exact 253-value OCP FP8 E4M3 finite value grid (126 pos + 0 + 126 neg; max = 448.0, min subnormal = 2^-9)."""
    pos = [0.0]
    # Subnormals: e = 0 -> (m / 8) * 2^-6 for m = 1..7 (7 values)
    for m in range(1, 8):
        pos.append((m / 8.0) * (2.0 ** -6))
    # Normals: exp_bits = 1..15, bias = 7 -> e in -6..8; NaN is exp=15, m=7 (excluded) (14*8 + 7 = 119 values)
    for exp_bits in range(1, 16):
        e = exp_bits - 7
        m_max = 7 if exp_bits == 15 else 8
        for m in range(m_max):
            pos.append((1.0 + m / 8.0) * (2.0 ** e))
    vals = sorted(set([-v for v in pos if v > 0.0] + pos))
    assert len(vals) == 253 and vals[-1] == 448.0, f"Unexpected FP8 grid: len={len(vals)}, max={vals[-1]}"
    return np.array(vals, dtype=np.float32)


FP8_E4M3_GRID = _build_fp8_e4m3_grid()
FP8_E4M3_MIDPOINTS = 0.5 * (FP8_E4M3_GRID[:-1] + FP8_E4M3_GRID[1:])


# ======================================================================================
# 1. Exact OCP Block-32 Quantizers & INT16 Activation Quantizer
# ======================================================================================
def quantize_fp8_e4m3_block32_deq(w: torch.Tensor, block_size: int = 32) -> torch.Tensor:
    """
    OCP MXFP8-E4M3 (block-32 shared UE8M0 power-of-two scale) quantization -> FP32 dequantized tensor.
    Every element is snapped to the exact 255-level FP8 E4M3 grid scaled by a power-of-two block scale.
    """
    orig_shape = w.shape
    wf = w.detach().float().cpu()
    J, D = wf.shape
    assert D % block_size == 0, f"in_dim {D} not divisible by {block_size}"
    K = D // block_size
    blocks = wf.view(J, K, block_size)
    bmax = blocks.abs().amax(dim=-1, keepdim=True)  # (J, K, 1)
    # Power-of-two UE8M0 scale so max(|block|) / scale <= 448.0
    exp = torch.ceil(torch.log2(torch.clamp(bmax, min=1e-30) / 448.0))
    scale = torch.pow(2.0, exp)
    scale = torch.where(bmax > 0, scale, torch.ones_like(scale))
    scaled = blocks / scale
    mids = torch.from_numpy(FP8_E4M3_MIDPOINTS)
    grid = torch.from_numpy(FP8_E4M3_GRID)
    idx = torch.bucketize(scaled.contiguous(), mids)
    q_vals = grid[idx]
    return (q_vals * scale).view(orig_shape)


@dataclass
class MXFP4MatrixPack:
    """Exact integer OCP MXFP4 (E2M1 + UE8M0 block-32 scale) representation."""
    orig_rows: int
    J_pad: int
    in_dim: int
    K_blocks: int
    e_floor: int
    q_nibbles: np.ndarray   # uint8 [J_pad, K_blocks, 32], values in 0..15 (-0 -> 0)
    s_scales: np.ndarray    # uint32 [J_pad, K_blocks], power-of-2 >= 1

    def dequantize_fp32(self) -> torch.Tensor:
        q_x2 = E2M1_NIBBLE_TO_X2[self.q_nibbles]  # int64 [J_pad, K, 32]
        w_int = q_x2 * self.s_scales.astype(np.int64)[:, :, None]
        w_f = w_int.astype(np.float32) * (2.0 ** (self.e_floor - 1))
        return torch.from_numpy(w_f.reshape(self.J_pad, self.in_dim)[: self.orig_rows])


def quantize_mxfp4_e2m1_block32(
    w: torch.Tensor,
    block_size: int = 32,
    pad_rows_pow2: bool = False,
    max_exp_span: int = 7,
) -> MXFP4MatrixPack:
    """
    Quantize a 2D weight matrix `[orig_rows, in_dim]` to exact OCP MXFP4 E2M1 block-32 format:
      W_deq[j, k*32 + b] = decode_e2m1_x2(Q[j, k, b]) * S[j, k] * 2^(e_floor - 1)
    where:
      - Q[j, k, b] in {0..15} with -0 (nibble 8) canonicalized to 0,
      - S[j, k] = 2^(e[j,k] - e_floor) in {1, 2, ..., 2^max_exp_span} (u32 power of 2).
    """
    wf = w.detach().float().cpu().numpy()
    orig_rows, in_dim = wf.shape
    assert in_dim % block_size == 0, f"in_dim {in_dim} not divisible by {block_size}"
    if pad_rows_pow2:
        J_pad = 1 << (orig_rows - 1).bit_length()
        if J_pad > orig_rows:
            wf_pad = np.zeros((J_pad, in_dim), dtype=np.float32)
            wf_pad[:orig_rows] = wf
            wf = wf_pad
    else:
        J_pad = orig_rows

    K = in_dim // block_size
    blocks = wf.reshape(J_pad, K, block_size)
    bmax = np.max(np.abs(blocks), axis=-1)  # (J_pad, K)

    nz = bmax > 0.0
    if np.any(nz):
        raw_exp = np.ceil(np.log2(np.maximum(bmax, 1e-30) / 6.0)).astype(np.int64)
        e_max = int(np.max(raw_exp[nz]))
        e_min_nz = int(np.min(raw_exp[nz]))
        e_floor = max(e_min_nz, e_max - max_exp_span)
        exp_clamped = np.where(nz, np.clip(raw_exp, e_floor, e_max), e_floor)
    else:
        e_floor = 0
        exp_clamped = np.zeros((J_pad, K), dtype=np.int64)

    s_scales = (1 << (exp_clamped - e_floor)).astype(np.uint32)  # power-of-2 >= 1
    # Target in x2 coordinates: blocks / (S * 2^(e_floor - 1))
    denom = s_scales.astype(np.float32)[:, :, None] * float(2.0 ** (e_floor - 1))
    targets_x2 = blocks / denom
    # Nearest neighbor in canonical E2M1 x2 grid (zero maps to nibble 0, never 8)
    idx = np.searchsorted(_E2M1_MIDPOINTS_X2, targets_x2)
    q_nibbles = _E2M1_SORTED_NIBS[idx].astype(np.uint8)
    # Zero out padded tail rows explicitly (nibble 0, scale 1)
    if J_pad > orig_rows:
        q_nibbles[orig_rows:] = 0
        s_scales[orig_rows:] = 1
    assert not np.any(q_nibbles == 8), "Non-canonical -0 nibble emitted!"

    return MXFP4MatrixPack(
        orig_rows=orig_rows,
        J_pad=J_pad,
        in_dim=in_dim,
        K_blocks=K,
        e_floor=e_floor,
        q_nibbles=q_nibbles,
        s_scales=s_scales,
    )


def quantize_act_int16(
    x: torch.Tensor,
    fixed_scale: int = ACT_SCALE,
    clip_counter: Optional[List[int]] = None,
) -> Tuple[torch.Tensor, torch.Tensor]:
    """
    Quantize activations to exact INT16 (`[-32767, 32767]`) using per-token power-of-two
    dynamic scaling (`scale_t = 2^e_t` placing `max(|x_t|) * scale_t` in `(16383.5, 32767]`).
    This uses the full 15-bit signed integer range on BOTH large norms (max ~25) and small
    intermediate tensors (like SwiGLU mid_mlp rms ~0.04 or GDN gated output rms ~0.11) with
    ZERO clipping and power-of-two dyadic scales.
    Returns `(x_deq_fp32, x_i16_int64)` on same device as `x`.
    """
    _ = fixed_scale  # kept in signature for caller compatibility
    xf = x.float()
    max_per_tok = xf.abs().amax(dim=-1, keepdim=True)  # (..., 1)
    safe_max = torch.clamp(max_per_tok, min=1e-12)
    exp_t = torch.clamp(torch.floor(torch.log2(32767.0 / safe_max)), min=-8.0, max=20.0)
    dyn_scale = torch.where(max_per_tok > 0.0, torch.pow(2.0, exp_t), torch.ones_like(exp_t))
    q = torch.round(xf * dyn_scale)
    q_clamped = torch.clamp(q, INT16_MIN, INT16_MAX)
    if clip_counter is not None:
        clip_counter[0] += int((q != q_clamped).sum().item())
    return q_clamped / dyn_scale, q_clamped.to(torch.int64)


def quantize_to_i16_fixed(x: torch.Tensor, scale: int) -> np.ndarray:
    """Deterministic round-to-nearest INT16 quantization at exact fixed scale, asserting zero clipping."""
    arr = np.rint(x.detach().float().cpu().numpy() * float(scale)).astype(np.int64)
    max_abs = int(np.max(np.abs(arr)))
    assert max_abs <= INT16_MAX, f"INT16 overflow at scale={scale}: max_abs={max_abs}"
    return arr.astype(np.int16)


# ======================================================================================
# 2. Core Qwen3.5 Ops (Norms, RoPE, FP32 Recurrent & Chunkwise GDN, Exact Int64 WY GDN)
# ======================================================================================
def rmsnorm_zero_centered(x: torch.Tensor, w: torch.Tensor, eps: float = RMS_EPS) -> torch.Tensor:
    """Zero-centered `Qwen3NextRMSNorm`: `rmsnorm_plain(x) * (1.0 + w)`."""
    xf = x.float()
    normed = xf * torch.rsqrt(xf.pow(2).mean(dim=-1, keepdim=True) + eps)
    return (normed * (1.0 + w.float())).to(x.dtype)


def rmsnorm_gated(
    y: torch.Tensor, z: torch.Tensor, w: torch.Tensor, eps: float = RMS_EPS
) -> torch.Tensor:
    """Gated `Qwen3NextRMSNormGated`: `w * rmsnorm_plain(y) * silu(z)` (NO `1.0 +`!)."""
    yf = y.float()
    normed = yf * torch.rsqrt(yf.pow(2).mean(dim=-1, keepdim=True) + eps)
    return (w.float() * normed * F.silu(z.float())).to(y.dtype)


def l2norm(x: torch.Tensor, eps: float = RMS_EPS) -> torch.Tensor:
    return x * torch.rsqrt((x * x).sum(dim=-1, keepdim=True) + eps)


def rotate_half(x: torch.Tensor) -> torch.Tensor:
    h = x.shape[-1] // 2
    return torch.cat((-x[..., h:], x[..., :h]), dim=-1)


def build_rope_cache(max_len: int, device: torch.device) -> Tuple[torch.Tensor, torch.Tensor]:
    inv_freq = 1.0 / (
        ROPE_THETA ** (torch.arange(0, GQA_ROT_DIM, 2, dtype=torch.float32, device=device) / float(GQA_ROT_DIM))
    )
    pos = torch.arange(max_len, dtype=torch.float32, device=device)
    freqs = torch.outer(pos, inv_freq)
    emb = torch.cat([freqs, freqs], dim=-1)  # (max_len, 64)
    return emb.cos(), emb.sin()


def apply_partial_rope(
    q: torch.Tensor,
    k: torch.Tensor,
    cos: torch.Tensor,
    sin: torch.Tensor,
    pos_offset: int = 0,
) -> Tuple[torch.Tensor, torch.Tensor]:
    """Partial RoPE (`rotary_dim = 64` of `256`); for 1D text, 3D mrope `[p,p,p]` equals 1D RoPE."""
    T = q.shape[2]
    c = cos[pos_offset : pos_offset + T][None, None, :, :].to(q.dtype)
    s = sin[pos_offset : pos_offset + T][None, None, :, :].to(q.dtype)
    q_rot, q_pass = q[..., :GQA_ROT_DIM], q[..., GQA_ROT_DIM:]
    k_rot, k_pass = k[..., :GQA_ROT_DIM], k[..., GQA_ROT_DIM:]
    q_out = torch.cat([(q_rot * c) + (rotate_half(q_rot) * s), q_pass], dim=-1)
    k_out = torch.cat([(k_rot * c) + (rotate_half(k_rot) * s), k_pass], dim=-1)
    return q_out, k_out


def gdn_recurrent_fp32(
    q: torch.Tensor,
    k: torch.Tensor,
    v: torch.Tensor,
    g: torch.Tensor,
    beta: torch.Tensor,
    state: Optional[torch.Tensor] = None,
) -> Tuple[torch.Tensor, torch.Tensor]:
    """Exact sequential Gated DeltaNet recurrence in FP32."""
    B, T, H, D = q.shape
    qf = l2norm(q.float()) * (D ** -0.5)
    kf = l2norm(k.float())
    vf = v.float()
    gf = g.float()
    bf = beta.float()
    S = (
        torch.zeros(B, H, D, D, dtype=torch.float32, device=q.device)
        if state is None
        else state.float().clone()
    )
    Y = torch.zeros(B, T, H, D, dtype=torch.float32, device=q.device)
    for t in range(T):
        decay = gf[:, t].exp()[:, :, None, None]
        S = S * decay
        kt = kf[:, t]
        vt = vf[:, t]
        bt = bf[:, t][:, :, None]
        kv_mem = (S * kt[:, :, :, None]).sum(dim=-2)
        delta = (vt - kv_mem) * bt
        S = S + kt[:, :, :, None] * delta[:, :, None, :]
        Y[:, t] = (S * qf[:, t, :, :, None]).sum(dim=-2)
    return Y, S


def gdn_chunkwise_wy_fp32(
    q: torch.Tensor,
    k: torch.Tensor,
    v: torch.Tensor,
    g: torch.Tensor,
    beta: torch.Tensor,
    chunk_size: int = 64,
    state: Optional[torch.Tensor] = None,
) -> Tuple[torch.Tensor, torch.Tensor]:
    """Exact FP32 chunkwise WY (`C=64`) Gated DeltaNet `(I + L)[U | W] = RHS`."""
    B, T, H, D = q.shape
    qf = (l2norm(q.float()) * (D ** -0.5)).transpose(1, 2)
    kf = l2norm(k.float()).transpose(1, 2)
    vf = v.float().transpose(1, 2)
    gf = g.float().transpose(1, 2)
    bf = beta.float().transpose(1, 2)
    pad = (chunk_size - T % chunk_size) % chunk_size
    if pad:
        qf = F.pad(qf, (0, 0, 0, pad))
        kf = F.pad(kf, (0, 0, 0, pad))
        vf = F.pad(vf, (0, 0, 0, pad))
        gf = F.pad(gf, (0, pad))
        bf = F.pad(bf, (0, pad))
    nc = (T + pad) // chunk_size
    qf = qf.reshape(B, H, nc, chunk_size, D)
    kf = kf.reshape(B, H, nc, chunk_size, D)
    vf = vf.reshape(B, H, nc, chunk_size, D)
    gf = gf.reshape(B, H, nc, chunk_size)
    bf = bf.reshape(B, H, nc, chunk_size)

    g_cum = gf.cumsum(dim=-1)
    decay_mask = (g_cum.unsqueeze(-1) - g_cum.unsqueeze(-2)).tril().exp().tril()
    v_beta = vf * bf.unsqueeze(-1)
    k_beta = kf * bf.unsqueeze(-1)
    mask0 = torch.triu(torch.ones(chunk_size, chunk_size, dtype=torch.bool, device=q.device), diagonal=0)
    L = ((k_beta @ kf.transpose(-1, -2)) * decay_mask).masked_fill(mask0, 0.0)

    rhs_u = v_beta
    rhs_w = k_beta * g_cum.exp().unsqueeze(-1)
    U = torch.zeros_like(rhs_u)
    W = torch.zeros_like(rhs_w)
    for i in range(chunk_size):
        if i == 0:
            U[..., 0, :] = rhs_u[..., 0, :]
            W[..., 0, :] = rhs_w[..., 0, :]
        else:
            U[..., i, :] = rhs_u[..., i, :] - (L[..., i : i + 1, :i] @ U[..., :i, :]).squeeze(-2)
            W[..., i, :] = rhs_w[..., i, :] - (L[..., i : i + 1, :i] @ W[..., :i, :]).squeeze(-2)

    S = (
        torch.zeros(B, H, D, D, dtype=torch.float32, device=q.device)
        if state is None
        else state.float().clone()
    )
    out = torch.zeros_like(vf)
    mask1 = torch.triu(torch.ones(chunk_size, chunk_size, dtype=torch.bool, device=q.device), diagonal=1)
    for ci in range(nc):
        qi, ki = qf[:, :, ci], kf[:, :, ci]
        ui, wi = U[:, :, ci], W[:, :, ci]
        v_new = ui - wi @ S
        attn = (qi @ ki.transpose(-1, -2) * decay_mask[:, :, ci]).masked_fill(mask1, 0.0)
        y_inter = (qi * g_cum[:, :, ci, :, None].exp()) @ S
        out[:, :, ci] = y_inter + attn @ v_new
        S = (
            S * g_cum[:, :, ci, -1, None, None].exp()
            + (ki * (g_cum[:, :, ci, -1, None] - g_cum[:, :, ci]).exp().unsqueeze(-1)).transpose(-1, -2) @ v_new
        )
    y_out = out.reshape(B, H, -1, D)[:, :, :T].transpose(1, 2).contiguous()
    return y_out, S


def _rshift_round_np(x: np.ndarray, shift: int) -> np.ndarray:
    """Deterministic round-half-up arithmetic right shift `floor((x + 2^(s-1)) / 2^s)`."""
    if shift == 0:
        return x
    half = np.int64(1 << (shift - 1))
    return (x + half) >> shift


@dataclass
class IntegerWYWitness:
    L_tilde: np.ndarray  # int32 [16, 64, 64] strictly lower-triangular
    RHS: np.ndarray      # int32 [16, 64, 256]
    UW: np.ndarray       # int32 [16, 64, 256]
    R_rem: np.ndarray    # uint16 [16, 64, 256] in [0, 4095]
    max_abs_lhs: int
    identity_errors: int


def gdn_chunkwise_wy_int64(
    q: torch.Tensor,
    k: torch.Tensor,
    v: torch.Tensor,
    g: torch.Tensor,
    beta: torch.Tensor,
    chunk_size: int = 64,
    state_fp32: Optional[torch.Tensor] = None,
    record_witness: bool = False,
) -> Tuple[torch.Tensor, torch.Tensor, Dict[str, Any]]:
    """
    Division-free exact integer `C=64` chunkwise WY (`M_wy = 4096`) for real Qwen3.5 GDN layers.
    Solves `(I + L_tilde / M_wy) UW = RHS` over `Z` with exact Euclidean remainder `0 <= R_rem < M_wy`:
      sum_{j<i} L_tilde[h, i, j] * UW[h, j, c]
        == M_wy * (RHS[h, i, c] - UW[h, i, c]) + (M_wy // 2) - R_rem[h, i, c]
    Verifies ZERO identity errors over `Z` and `max |LHS| < P_BB // 2` on every chunk!
    """
    orig_device = q.device
    B, T, H, D = q.shape
    assert B == 1 and H == GDN_H and D == GDN_D

    # L2-normalize q, k and convert to exact integer fixed-point coordinates
    q_n = l2norm(q.float())[0].detach().cpu().numpy()     # (T, H, D), ||q_n||_2 = 1
    k_n = l2norm(k.float())[0].detach().cpu().numpy()     # (T, H, D), ||k_n||_2 = 1
    v_f = v.float()[0].detach().cpu().numpy()             # (T, H, D)
    alpha_f = g.float().exp()[0].detach().cpu().numpy()   # (T, H) in (0, 1]
    beta_f = beta.float()[0].detach().cpu().numpy()       # (T, H) in (0, 1)

    # Pad to multiple of chunk_size (for T=64 -> pad=0, nc=1)
    pad = (chunk_size - T % chunk_size) % chunk_size
    if pad:
        q_n = np.pad(q_n, ((0, pad), (0, 0), (0, 0)))
        k_n = np.pad(k_n, ((0, pad), (0, 0), (0, 0)))
        v_f = np.pad(v_f, ((0, pad), (0, 0), (0, 0)))
        alpha_f = np.pad(alpha_f, ((0, pad), (0, 0)), constant_values=1.0)
        beta_f = np.pad(beta_f, ((0, pad), (0, 0)), constant_values=0.0)
    T_pad = T + pad
    nc = T_pad // chunk_size

    q_int = np.rint(q_n * K_WY_SCALE).astype(np.int64)              # [-4096, 4096]
    k_int = np.rint(k_n * K_WY_SCALE).astype(np.int64)              # [-4096, 4096]
    alpha_int = np.clip(np.rint(alpha_f * M_WY).astype(np.int64), 0, M_WY)
    beta_int = np.clip(np.rint(beta_f * M_WY).astype(np.int64), 0, M_WY)

    # Per-head power-of-two scaling on `beta * v` so low-beta heads (where beta ~ 1e-3
    # before RMSNormGated) retain full 12-bit integer precision inside U_rhs without
    # underflowing to 0/1/2! Linearity of `(I + L/M) U = U_rhs` preserves exact WY over Z.
    v_beta_f = v_f * beta_f[:, :, None]                             # (T_pad, H, D)
    u_head_max = np.max(np.abs(v_beta_f), axis=(0, 2))              # (H,)
    u_shifts = np.zeros(H, dtype=np.int64)
    for h in range(H):
        if u_head_max[h] > 1e-12:
            sh = int(math.floor(math.log2(4096.0 / float(u_head_max[h]))))
            u_shifts[h] = max(4, min(26, sh))
        else:
            u_shifts[h] = 12
    u_scales = np.power(2.0, u_shifts.astype(np.float64))           # (H,) exact powers of 2
    u_rhs_all = np.rint(v_beta_f * u_scales[None, :, None]).astype(np.int64)  # (T_pad, H, D) in [-4096, 4096]

    S_state = (
        np.zeros((H, D, D), dtype=np.int64)
        if state_fp32 is None
        else np.rint(
            state_fp32[0].detach().float().cpu().numpy() * u_scales[:, None, None]
        ).astype(np.int64)
    )
    Y_out_acc = np.zeros((T_pad, H, D), dtype=np.int64)             # scale = M_WY * u_scales[h]

    half_wy = np.int64(M_WY // 2)
    tril_strict = np.tril(np.ones((chunk_size, chunk_size), dtype=np.int64), k=-1)
    tril_incl = np.tril(np.ones((chunk_size, chunk_size), dtype=np.int64), k=0)
    kk_shift = 2 * K_WY_SHIFT - WY_SHIFT  # 24 - 12 = 12

    max_abs_lhs_all = 0
    total_id_errs = 0
    total_entries = 0
    max_rem_seen = 0
    min_rem_seen = M_WY
    first_witness: Optional[IntegerWYWitness] = None

    for ci in range(nc):
        sl = slice(ci * chunk_size, (ci + 1) * chunk_size)
        Qc = np.transpose(q_int[sl], (1, 0, 2))      # (H, C, D)
        Kc = np.transpose(k_int[sl], (1, 0, 2))      # (H, C, D)
        U_rhs = np.transpose(u_rhs_all[sl], (1, 0, 2))  # (H, C, D)
        ac = alpha_int[sl].T                         # (H, C)
        bc = beta_int[sl].T                          # (H, C)

        # Division-free pairwise cumulative decay products (vectorized over all H=16 heads)
        gamma_pre = np.zeros((H, chunk_size), dtype=np.int64)
        gamma_suf = np.zeros((H, chunk_size), dtype=np.int64)
        Gamma = np.zeros((H, chunk_size, chunk_size), dtype=np.int64)

        cur = np.full(H, M_WY, dtype=np.int64)
        for i in range(chunk_size):
            cur = _rshift_round_np(cur * ac[:, i], WY_SHIFT)
            gamma_pre[:, i] = cur

        cur_s = np.full(H, M_WY, dtype=np.int64)
        for j in range(chunk_size - 1, -1, -1):
            gamma_suf[:, j] = cur_s
            cur_s = _rshift_round_np(cur_s * ac[:, j], WY_SHIFT)

        for j in range(chunk_size):
            Gamma[:, j, j] = M_WY
            p = np.full(H, M_WY, dtype=np.int64)
            for i in range(j + 1, chunk_size):
                p = _rshift_round_np(p * ac[:, i], WY_SHIFT)
                Gamma[:, i, j] = p

        # Strictly lower-triangular L_tilde[h, i, j] (scale M_wy = 4096)
        kk = _rshift_round_np(np.matmul(Kc, np.swapaxes(Kc, -1, -2)), kk_shift)  # (H, C, C)
        bg = _rshift_round_np(bc[:, :, None] * Gamma, WY_SHIFT)                  # (H, C, C)
        L_tilde = _rshift_round_np(bg * kk, WY_SHIFT) * tril_strict[None, :, :]  # (H, C, C)

        # RHS = [U_rhs (D) | W_rhs (D)] of shape (H, C, 2*D = 256)
        gb = _rshift_round_np(gamma_pre * bc, WY_SHIFT)
        W_rhs = _rshift_round_np(gb[:, :, None] * Kc, WY_SHIFT)
        RHS = np.concatenate([U_rhs, W_rhs], axis=-1)  # (H, C, 256)

        # Forward substitution over Z with exact Euclidean remainder 0 <= R_rem < M_wy
        UW = np.zeros_like(RHS)
        R_rem = np.zeros_like(RHS)
        for i in range(chunk_size):
            if i == 0:
                dot_row = np.zeros((H, 2 * D), dtype=np.int64)
            else:
                dot_row = np.matmul(L_tilde[:, i : i + 1, :i], UW[:, :i, :])[:, 0, :]
            num = M_WY * RHS[:, i, :] + half_wy - dot_row
            UW[:, i, :] = num // M_WY
            R_rem[:, i, :] = num - M_WY * UW[:, i, :]

        # Verify exact WY identity over Z for EVERY entry in the chunk
        lhs_mat = np.matmul(L_tilde, UW)  # (H, C, 256) exact int64
        rhs_chk = M_WY * (RHS - UW) + half_wy - R_rem
        errs = int(np.count_nonzero(lhs_mat != rhs_chk))
        max_lhs_chunk = int(np.max(np.abs(lhs_mat)))
        max_rhs_chk = int(np.max(np.abs(rhs_chk)))
        assert errs == 0, f"WY identity failed with {errs} errors!"
        assert np.all((R_rem >= 0) & (R_rem < M_WY)), "WY remainder out of [0, M_wy)!"
        assert max_lhs_chunk < P_BB_HALF, f"BabyBear overflow: max|LHS|={max_lhs_chunk} >= {P_BB_HALF}"

        max_abs_lhs_all = max(max_abs_lhs_all, max_lhs_chunk, max_rhs_chk)
        total_id_errs += errs
        total_entries += int(lhs_mat.size)
        max_rem_seen = max(max_rem_seen, int(np.max(R_rem)))
        min_rem_seen = min(min_rem_seen, int(np.min(R_rem)))

        if record_witness and first_witness is None:
            first_witness = IntegerWYWitness(
                L_tilde=L_tilde.astype(np.int32),
                RHS=RHS.astype(np.int32),
                UW=UW.astype(np.int32),
                R_rem=R_rem.astype(np.uint16),
                max_abs_lhs=max_lhs_chunk,
                identity_errors=errs,
            )

        # Inter-chunk & intra-chunk output computation in exact integer arithmetic
        U_mat = UW[:, :, :D]  # (H, C, D), scale u_scales[h]
        W_mat = UW[:, :, D:]  # (H, C, D), scale K_WY_SCALE
        ws = _rshift_round_np(np.matmul(W_mat, S_state), K_WY_SHIFT)
        U_eff = U_mat - ws    # (H, C, D), scale u_scales[h]

        q_gam = _rshift_round_np(gamma_pre[:, :, None] * Qc, WY_SHIFT)
        y_inter = _rshift_round_np(np.matmul(q_gam, S_state), K_WY_SHIFT)  # scale u_scales[h]
        qk = _rshift_round_np(np.matmul(Qc, np.swapaxes(Kc, -1, -2)), kk_shift)
        qk_causal = _rshift_round_np(qk * (Gamma * tril_incl[None, :, :]), WY_SHIFT)
        # Keep unshifted M_WY * u_scales[h] integer accumulator to preserve full precision before RMSNormGated
        y_intra_acc = np.matmul(qk_causal, U_eff)
        Y_out_acc[sl] = np.transpose((y_inter << WY_SHIFT) + y_intra_acc, (1, 0, 2))

        # Update inter-chunk recurrent state S_state (scale u_scales[h])
        k_bar = _rshift_round_np(gamma_suf[:, :, None] * Kc, WY_SHIFT)
        s_decay = _rshift_round_np(gamma_pre[:, chunk_size - 1, None, None] * S_state, WY_SHIFT)
        s_add = _rshift_round_np(np.matmul(np.swapaxes(k_bar, -1, -2), U_eff), K_WY_SHIFT)
        S_state = s_decay + s_add

    # Rescale back to float32 (exact power-of-two per-head scale * 128^-0.5)
    inv_y = (D ** -0.5) / (float(M_WY) * u_scales[None, :, None])
    y_fp32 = torch.from_numpy((Y_out_acc[:T].astype(np.float64) * inv_y).astype(np.float32)[None, ...]).to(orig_device)
    s_fp32 = torch.from_numpy((S_state.astype(np.float64) / u_scales[:, None, None]).astype(np.float32)[None, ...]).to(orig_device)

    stats = {
        "max_abs_lhs": max_abs_lhs_all,
        "identity_errors": total_id_errs,
        "entries_checked": total_entries,
        "min_rem": min_rem_seen,
        "max_rem": max_rem_seen,
        "u_shifts_min_max": [int(np.min(u_shifts)), int(np.max(u_shifts))],
        "witness": first_witness,
    }
    return y_fp32, s_fp32, stats


# ======================================================================================
# 3. Real Qwen3.5-0.8B Engine (FP32, BF16, FP8+IntWY, Mixed-MXFP4+IntWY, Pure-MXFP4+IntWY)
# ======================================================================================
def census_safetensors() -> Dict[str, Any]:
    """Exact census of all 488 tensors in `Qwen/Qwen3.5-0.8B-Base`."""
    counts = {"text": [0, 0], "vision": [0, 0], "mtp": [0, 0]}
    linear_2d_all = []
    linear_2d_mlp = []
    linear_2d_attn_gdn = []
    with safe_open(str(SAFETENSORS_PATH), framework="pt", device="cpu") as f:
        keys = list(f.keys())
        for k in keys:
            sh = f.get_slice(k).get_shape()
            n = 1
            for d in sh:
                n *= d
            if k.startswith("model.language_model."):
                counts["text"][0] += 1
                counts["text"][1] += n
                if k.startswith("model.language_model.layers.") and len(sh) == 2 and k.endswith(".weight"):
                    linear_2d_all.append(k)
                    if ".mlp." in k:
                        linear_2d_mlp.append(k)
                    else:
                        linear_2d_attn_gdn.append(k)
            elif k.startswith("model.visual."):
                counts["vision"][0] += 1
                counts["vision"][1] += n
            elif k.startswith("mtp."):
                counts["mtp"][0] += 1
                counts["mtp"][1] += n
            else:
                raise ValueError(f"Unexpected tensor prefix: {k}")
    total_tensors = sum(v[0] for v in counts.values())
    total_params = sum(v[1] for v in counts.values())
    assert total_tensors == 488, f"Expected 488 tensors, got {total_tensors}"
    return {
        "total_tensors": total_tensors,
        "total_params": total_params,
        "text_tensors": counts["text"][0],
        "text_params": counts["text"][1],
        "vision_tensors": counts["vision"][0],
        "vision_params": counts["vision"][1],
        "mtp_tensors": counts["mtp"][0],
        "mtp_params": counts["mtp"][1],
        "text_linear_2d_total": len(linear_2d_all),
        "text_mlp_2d": len(linear_2d_mlp),
        "text_attn_gdn_2d": len(linear_2d_attn_gdn),
    }


def load_text_weights() -> Dict[str, torch.Tensor]:
    """Load the 320 `model.language_model.*` tensors into CPU memory (read-only)."""
    weights: Dict[str, torch.Tensor] = {}
    with safe_open(str(SAFETENSORS_PATH), framework="pt", device="cpu") as f:
        for k in f.keys():
            if k.startswith("model.language_model."):
                weights[k[len("model.language_model.") :]] = f.get_tensor(k)
    assert len(weights) == 320
    return weights


def build_quantized_weight_bank(
    base_weights: Dict[str, torch.Tensor],
    mode: str,
    device: torch.device,
) -> Dict[str, torch.Tensor]:
    """
    Build weight dictionary on `device` for one of the 5 modes:
      - "fp32"
      - "bf16"
      - "fp8_intwy"        : OCP block-32 FP8 E4M3 on all 186 linear/MLP matrices
      - "mixed_mxfp4_intwy": OCP block-32 MXFP4 E2M1 on all 72 MLP matrices, FP8 E4M3 on all 114 Attn/GDN matrices
      - "pure_mxfp4_intwy" : OCP block-32 MXFP4 E2M1 on ALL 186 linear/MLP matrices
    """
    target_dtype = torch.bfloat16 if mode == "bf16" else torch.float32
    bank: Dict[str, torch.Tensor] = {}
    for k, w in base_weights.items():
        is_layer_2d = k.startswith("layers.") and w.ndim == 2 and k.endswith(".weight")
        if not is_layer_2d:
            # Keep A_log, norm weights, conv1d, embed_tokens in native/target dtype
            if k.endswith("A_log") or k.endswith("linear_attn.norm.weight"):
                bank[k] = w.float().to(device)
            else:
                bank[k] = w.to(target_dtype).to(device)
            continue

        if mode in ("fp32", "bf16"):
            bank[k] = w.to(target_dtype).to(device)
        elif mode == "fp8_intwy":
            bank[k] = quantize_fp8_e4m3_block32_deq(w).to(device)
        elif mode == "mixed_mxfp4_intwy":
            if ".mlp." in k:
                bank[k] = quantize_mxfp4_e2m1_block32(w).dequantize_fp32().to(device)
            else:
                bank[k] = quantize_fp8_e4m3_block32_deq(w).to(device)
        elif mode == "pure_mxfp4_intwy":
            bank[k] = quantize_mxfp4_e2m1_block32(w).dequantize_fp32().to(device)
        else:
            raise ValueError(f"Unknown mode: {mode}")
    return bank


class Qwen35Runner:
    """Runs prefill (full sequence) and cached autoregressive decoding for any precision mode."""

    def __init__(
        self,
        weights: Dict[str, torch.Tensor],
        mode: str,
        device: torch.device,
        max_pos: int = 256,
    ) -> None:
        self.w = weights
        self.mode = mode
        self.device = device
        self.quant_act = mode in ("fp8_intwy", "mixed_mxfp4_intwy", "pure_mxfp4_intwy")
        self.use_int_wy = self.quant_act
        self.cos, self.sin = build_rope_cache(max_pos, device)

    def _linear(self, x: torch.Tensor, weight_key: str, clip_ctr: Optional[List[int]] = None) -> torch.Tensor:
        if self.quant_act:
            x_q, _ = quantize_act_int16(x, ACT_SCALE, clip_ctr)
            return F.linear(x_q, self.w[weight_key])
        return F.linear(x, self.w[weight_key])

    @torch.no_grad()
    def forward_prefill(
        self,
        token_ids: List[int],
        capture_layer0_audit: bool = False,
        return_cache: bool = False,
    ) -> Dict[str, Any]:
        """
        Full-sequence prefill over `token_ids` (`T` tokens).
        Returns logits `[T, VOCAB_SIZE]`, all 25 boundary hidden states `[25, T, 1024]`,
        WY verification stats across all 18 GDN layers, and optional Layer 0 audit bundle + decode cache.
        """
        idx_t = torch.tensor(token_ids, dtype=torch.long, device=self.device)
        x = self.w["embed_tokens.weight"][idx_t].unsqueeze(0)  # [1, T, 1024]
        T = x.shape[1]

        boundaries: List[torch.Tensor] = [x[0].float().cpu()]  # boundary 0 = L0 input
        clip_ctr = [0]
        wy_max_lhs = 0
        wy_total_errs = 0
        wy_total_entries = 0
        wy_min_rem = M_WY
        wy_max_rem = 0
        l0_audit: Dict[str, Any] = {}

        cache = (
            {"conv": [None] * NUM_LAYERS, "ssm": [None] * NUM_LAYERS, "k": [None] * NUM_LAYERS, "v": [None] * NUM_LAYERS, "pos": T}
            if return_cache
            else None
        )

        cmask = torch.triu(
            torch.full((T, T), float("-inf"), dtype=torch.float32, device=self.device), diagonal=1
        )

        for l in range(NUM_LAYERS):
            p = f"layers.{l}."
            h = rmsnorm_zero_centered(x, self.w[p + "input_layernorm.weight"])

            if (l + 1) % 4 != 0:
                # --- Gated DeltaNet layer ---
                if capture_layer0_audit and l == 0:
                    l0_audit["X_ln1_fp32"] = h[0].float().cpu()

                qkv = self._linear(h, p + "linear_attn.in_proj_qkv.weight", clip_ctr)
                qkv_t = qkv.transpose(1, 2)  # [1, 6144, T]
                if cache is not None:
                    if T >= GDN_CONV_W:
                        cache["conv"][l] = qkv_t[:, :, -GDN_CONV_W:].clone()
                    else:
                        cache["conv"][l] = F.pad(qkv_t, (GDN_CONV_W - T, 0))
                qkv_c = F.conv1d(
                    F.pad(qkv_t, (GDN_CONV_W - 1, 0)),
                    self.w[p + "linear_attn.conv1d.weight"],
                    groups=6144,
                )
                qkv_c = F.silu(qkv_c.float()).to(x.dtype).transpose(1, 2)
                q, k, v = torch.split(qkv_c, [2048, 2048, 2048], dim=-1)
                q = q.view(1, T, GDN_H, GDN_D)
                k = k.view(1, T, GDN_H, GDN_D)
                v = v.view(1, T, GDN_H, GDN_D)

                z = self._linear(h, p + "linear_attn.in_proj_z.weight", clip_ctr).view(1, T, GDN_H, GDN_D)
                b = self._linear(h, p + "linear_attn.in_proj_b.weight", clip_ctr)
                a = self._linear(h, p + "linear_attn.in_proj_a.weight", clip_ctr)

                beta = torch.sigmoid(b.float())
                g = -self.w[p + "linear_attn.A_log"].float().exp() * F.softplus(
                    a.float() + self.w[p + "linear_attn.dt_bias"].float()
                )

                if self.use_int_wy:
                    y_core, s_final, wy_st = gdn_chunkwise_wy_int64(
                        q, k, v, g, beta, chunk_size=64, record_witness=(capture_layer0_audit and l == 0)
                    )
                    wy_max_lhs = max(wy_max_lhs, wy_st["max_abs_lhs"])
                    wy_total_errs += wy_st["identity_errors"]
                    wy_total_entries += wy_st["entries_checked"]
                    wy_min_rem = min(wy_min_rem, wy_st["min_rem"])
                    wy_max_rem = max(wy_max_rem, wy_st["max_rem"])
                    if capture_layer0_audit and l == 0:
                        l0_audit["wy_witness"] = wy_st["witness"]
                else:
                    y_core, s_final = gdn_chunkwise_wy_fp32(q, k, v, g, beta, chunk_size=64)

                if cache is not None:
                    cache["ssm"][l] = s_final

                y_gated = rmsnorm_gated(
                    y_core.to(x.dtype), z, self.w[p + "linear_attn.norm.weight"]
                ).reshape(1, T, 2048)

                if capture_layer0_audit and l == 0:
                    l0_audit["X_gdn_y_fp32"] = y_gated[0].float().cpu()

                attn_out = self._linear(y_gated, p + "linear_attn.out_proj.weight", clip_ctr)
            else:
                # --- GQA Full-Attention layer ---
                qg = self._linear(h, p + "self_attn.q_proj.weight", clip_ctr).view(1, T, GQA_HQ, GQA_DH * 2)
                q, gate = torch.chunk(qg, 2, dim=-1)
                gate = gate.reshape(1, T, GQA_HQ * GQA_DH)
                q = rmsnorm_zero_centered(q, self.w[p + "self_attn.q_norm.weight"]).transpose(1, 2)
                k = rmsnorm_zero_centered(
                    self._linear(h, p + "self_attn.k_proj.weight", clip_ctr).view(1, T, GQA_HKV, GQA_DH),
                    self.w[p + "self_attn.k_norm.weight"],
                ).transpose(1, 2)
                v = self._linear(h, p + "self_attn.v_proj.weight", clip_ctr).view(1, T, GQA_HKV, GQA_DH).transpose(1, 2)

                q, k = apply_partial_rope(q, k, self.cos, self.sin, pos_offset=0)
                if cache is not None:
                    cache["k"][l] = k
                    cache["v"][l] = v

                k_rep = k.repeat_interleave(GQA_HQ // GQA_HKV, dim=1)
                v_rep = v.repeat_interleave(GQA_HQ // GQA_HKV, dim=1)
                scores = (q.float() @ k_rep.float().transpose(-1, -2)) * (GQA_DH ** -0.5) + cmask
                probs = F.softmax(scores, dim=-1).to(v_rep.dtype)
                a_out = (probs @ v_rep).transpose(1, 2).contiguous().reshape(1, T, GQA_HQ * GQA_DH)
                a_out = (a_out.float() * torch.sigmoid(gate.float())).to(x.dtype)
                attn_out = self._linear(a_out, p + "self_attn.o_proj.weight", clip_ctr)

            x = x + attn_out
            h2 = rmsnorm_zero_centered(x, self.w[p + "post_attention_layernorm.weight"])
            if capture_layer0_audit and l == 0:
                l0_audit["X_ln2_fp32"] = h2[0].float().cpu()

            g_mlp = self._linear(h2, p + "mlp.gate_proj.weight", clip_ctr)
            u_mlp = self._linear(h2, p + "mlp.up_proj.weight", clip_ctr)
            mid_mlp = (F.silu(g_mlp.float()) * u_mlp.float()).to(x.dtype)
            mlp_out = self._linear(mid_mlp, p + "mlp.down_proj.weight", clip_ctr)
            x = x + mlp_out
            boundaries.append(x[0].float().cpu())

        x_norm = rmsnorm_zero_centered(x, self.w["norm.weight"])
        logits = F.linear(x_norm.float(), self.w["embed_tokens.weight"].float())[0].cpu()  # [T, VOCAB]

        return {
            "logits": logits,
            "boundaries": torch.stack(boundaries, dim=0),  # [25, T, 1024]
            "clip_count": clip_ctr[0],
            "wy_stats": {
                "max_abs_lhs": wy_max_lhs,
                "identity_errors": wy_total_errs,
                "entries_checked": wy_total_entries,
                "min_rem": wy_min_rem if wy_total_entries else 0,
                "max_rem": wy_max_rem,
            },
            "l0_audit": l0_audit,
            "cache": cache,
        }

    @torch.no_grad()
    def decode_step(self, next_token_id: int, cache: Dict[str, Any]) -> torch.Tensor:
        """Single-token cached autoregressive step (`T=1`)."""
        pos = cache["pos"]
        idx_t = torch.tensor([next_token_id], dtype=torch.long, device=self.device)
        x = self.w["embed_tokens.weight"][idx_t].unsqueeze(0)  # [1, 1, 1024]

        for l in range(NUM_LAYERS):
            p = f"layers.{l}."
            h = rmsnorm_zero_centered(x, self.w[p + "input_layernorm.weight"])

            if (l + 1) % 4 != 0:
                qkv = self._linear(h, p + "linear_attn.in_proj_qkv.weight")  # [1, 1, 6144]
                qkv_t = qkv.transpose(1, 2)  # [1, 6144, 1]
                # Shift 4-tap causal conv state
                conv_st = torch.cat([cache["conv"][l][:, :, 1:], qkv_t], dim=-1)  # [1, 6144, 4]
                cache["conv"][l] = conv_st
                conv_w = self.w[p + "linear_attn.conv1d.weight"].squeeze(1)  # [6144, 4]
                qkv_c = F.silu((conv_st * conv_w.unsqueeze(0)).sum(dim=-1).float()).to(x.dtype).unsqueeze(1)
                q, k, v = torch.split(qkv_c, [2048, 2048, 2048], dim=-1)
                q = q.view(1, 1, GDN_H, GDN_D)
                k = k.view(1, 1, GDN_H, GDN_D)
                v = v.view(1, 1, GDN_H, GDN_D)

                z = self._linear(h, p + "linear_attn.in_proj_z.weight").view(1, 1, GDN_H, GDN_D)
                b = self._linear(h, p + "linear_attn.in_proj_b.weight")
                a = self._linear(h, p + "linear_attn.in_proj_a.weight")
                beta = torch.sigmoid(b.float())
                g = -self.w[p + "linear_attn.A_log"].float().exp() * F.softplus(
                    a.float() + self.w[p + "linear_attn.dt_bias"].float()
                )
                y_core, s_new = gdn_recurrent_fp32(q, k, v, g, beta, state=cache["ssm"][l])
                cache["ssm"][l] = s_new
                y_gated = rmsnorm_gated(
                    y_core.to(x.dtype), z, self.w[p + "linear_attn.norm.weight"]
                ).reshape(1, 1, 2048)
                attn_out = self._linear(y_gated, p + "linear_attn.out_proj.weight")
            else:
                qg = self._linear(h, p + "self_attn.q_proj.weight").view(1, 1, GQA_HQ, GQA_DH * 2)
                q, gate = torch.chunk(qg, 2, dim=-1)
                gate = gate.reshape(1, 1, GQA_HQ * GQA_DH)
                q = rmsnorm_zero_centered(q, self.w[p + "self_attn.q_norm.weight"]).transpose(1, 2)
                k = rmsnorm_zero_centered(
                    self._linear(h, p + "self_attn.k_proj.weight").view(1, 1, GQA_HKV, GQA_DH),
                    self.w[p + "self_attn.k_norm.weight"],
                ).transpose(1, 2)
                v = self._linear(h, p + "self_attn.v_proj.weight").view(1, 1, GQA_HKV, GQA_DH).transpose(1, 2)
                q, k = apply_partial_rope(q, k, self.cos, self.sin, pos_offset=pos)

                k = torch.cat([cache["k"][l], k], dim=2)
                v = torch.cat([cache["v"][l], v], dim=2)
                cache["k"][l] = k
                cache["v"][l] = v

                k_rep = k.repeat_interleave(GQA_HQ // GQA_HKV, dim=1)
                v_rep = v.repeat_interleave(GQA_HQ // GQA_HKV, dim=1)
                scores = (q.float() @ k_rep.float().transpose(-1, -2)) * (GQA_DH ** -0.5)
                probs = F.softmax(scores, dim=-1).to(v_rep.dtype)
                a_out = (probs @ v_rep).transpose(1, 2).contiguous().reshape(1, 1, GQA_HQ * GQA_DH)
                a_out = (a_out.float() * torch.sigmoid(gate.float())).to(x.dtype)
                attn_out = self._linear(a_out, p + "self_attn.o_proj.weight")

            x = x + attn_out
            h2 = rmsnorm_zero_centered(x, self.w[p + "post_attention_layernorm.weight"])
            g_mlp = self._linear(h2, p + "mlp.gate_proj.weight")
            u_mlp = self._linear(h2, p + "mlp.up_proj.weight")
            mid_mlp = (F.silu(g_mlp.float()) * u_mlp.float()).to(x.dtype)
            x = x + self._linear(mid_mlp, p + "mlp.down_proj.weight")

        cache["pos"] = pos + 1
        x_norm = rmsnorm_zero_centered(x, self.w["norm.weight"])
        return F.linear(x_norm.float(), self.w["embed_tokens.weight"].float())[0, 0].cpu()

    @torch.no_grad()
    def generate_greedy(self, tok: Tokenizer, prompt: str, max_new_tokens: int = 32) -> Tuple[List[int], str]:
        ids = tok.encode(prompt).ids
        res = self.forward_prefill(ids, return_cache=True)
        cache = res["cache"]
        next_id = int(torch.argmax(res["logits"][-1]).item())
        gen_ids = [next_id]
        for _ in range(max_new_tokens - 1):
            logits_step = self.decode_step(next_id, cache)
            next_id = int(torch.argmax(logits_step).item())
            gen_ids.append(next_id)
        return gen_ids, tok.decode(gen_ids)


# ======================================================================================
# 4. Real Prompts (5 Generation Prompts + 5 Exact T=64 Evaluation Sequences)
# ======================================================================================
GEN_PROMPTS: List[Tuple[str, str]] = [
    ("P1_English", "The capital of France is"),
    ("P2_Math", "To solve the quadratic equation x^2 - 5x + 6 = 0, we factor"),
    (
        "P3_Python",
        "def binary_search(arr: list[int], target: int) -> int:\n    lo, hi = 0, len(arr) - 1\n",
    ),
    ("P4_Rust", "pub fn merkle_root(leaves: &[[u8; 32]]) -> [u8; 32] {\n"),
    (
        "P5_Secret",
        "Config backup:\nOPENAI_API_KEY=sk-proj-9f8a7b6c5d4e3f2a1b0c9d8e\n Mirroring config:\nOPENAI_API_KEY=",
    ),
]

EVAL_CORPUS_TEXTS: List[Tuple[str, str]] = [
    (
        "S1_English",
        (
            "The capital of France is Paris, a global center for art, fashion, gastronomy, and culture. "
            "Its nineteenth-century cityscape is crisscrossed by wide boulevards and the River Seine. "
            "Beyond landmarks such as the Eiffel Tower and the Gothic Notre-Dame cathedral, the city "
            "is celebrated for its cafe culture, scientific academies, and historic libraries."
        ),
    ),
    (
        "S2_Math",
        (
            "To solve the quadratic equation x^2 - 5x + 6 = 0, we factor the left-hand side into "
            "(x - 2)(x - 3) = 0, yielding roots x = 2 and x = 3. More generally, by completing the "
            "square on a*x^2 + b*x + c = 0, the discriminant Delta = b^2 - 4*a*c determines whether "
            "the polynomial admits two real roots, a repeated root, or complex conjugates."
        ),
    ),
    (
        "S3_Python",
        (
            "def binary_search(arr: list[int], target: int) -> int:\n"
            "    lo, hi = 0, len(arr) - 1\n"
            "    while lo <= hi:\n"
            "        mid = lo + (hi - lo) // 2\n"
            "        if arr[mid] == target:\n"
            "            return mid\n"
            "        elif arr[mid] < target:\n"
            "            lo = mid + 1\n"
            "        else:\n"
            "            hi = mid - 1\n"
            "    return -1\n"
        ),
    ),
    (
        "S4_Rust",
        (
            "pub fn merkle_root(leaves: &[[u8; 32]]) -> [u8; 32] {\n"
            "    if leaves.is_empty() {\n"
            "        return [0u8; 32];\n"
            "    }\n"
            "    let mut level: Vec<[u8; 32]> = leaves.to_vec();\n"
            "    while level.len() > 1 {\n"
            "        let mut next = Vec::with_capacity((level.len() + 1) / 2);\n"
            "        for pair in level.chunks(2) {\n"
            "            let right = if pair.len() == 2 { pair[1] } else { pair[0] };\n"
            "            next.push(hash_pair(&pair[0], &right));\n"
            "        }\n"
            "        level = next;\n"
            "    }\n"
            "    level[0]\n"
            "}\n"
        ),
    ),
    (
        "S5_ConfigSecret",
        (
            "# Production environment snapshot for telemetry relay\n"
            "SERVICE_ENV=production\n"
            "REGION=us-west-2\n"
            "LOG_LEVEL=info\n"
            "Config backup:\n"
            "OPENAI_API_KEY=sk-proj-9f8a7b6c5d4e3f2a1b0c9d8e\n"
            "DATABASE_HOST=db.internal.local\n"
            "Mirroring config:\n"
            "OPENAI_API_KEY="
        ),
    ),
]


def prepare_t64_sequences(tok: Tokenizer) -> List[Tuple[str, List[int]]]:
    """Produce 5 exact T=64 real token sequences (total 320 token positions / 315 targets)."""
    out: List[Tuple[str, List[int]]] = []
    for name, text in EVAL_CORPUS_TEXTS:
        ids = tok.encode(text).ids
        if len(ids) < 64:
            # Pad by repeating a clean prefix comment if ever short
            while len(ids) < 64:
                ids = tok.encode("# backup\n" + text).ids
                text = "# backup\n" + text
        if name == "S5_ConfigSecret":
            # Take the LAST 64 tokens so the sequence ends exactly at "OPENAI_API_KEY="
            ids = ids[-64:]
        else:
            ids = ids[:64]
        assert len(ids) == 64, f"{name} has len {len(ids)}"
        out.append((name, ids))
    return out


# ======================================================================================
# 5. Metrics Computation
# ======================================================================================
def compute_layer_fidelity(b_ref: torch.Tensor, b_q: torch.Tensor) -> Tuple[List[float], List[float]]:
    """
    Compare boundary hidden states `[N_seq, 25, 64, 1024]` at layer outputs L0..L23 (indices 1..24).
    Returns per-layer `(cos_sim[24], snr_db[24])`.
    """
    cos_list: List[float] = []
    snr_list: List[float] = []
    for l in range(NUM_LAYERS):
        r = b_ref[:, l + 1].reshape(-1, D_MODEL).double()
        q = b_q[:, l + 1].reshape(-1, D_MODEL).double()
        # Mean token-level cosine similarity
        cos = F.cosine_similarity(r, q, dim=-1).mean().item()
        sig = (r * r).sum().item()
        err = ((r - q) ** 2).sum().item()
        snr = 10.0 * math.log10((sig + 1e-18) / (err + 1e-18))
        cos_list.append(cos)
        snr_list.append(snr)
    return cos_list, snr_list


def compute_logit_metrics(
    logits_ref: torch.Tensor,  # [N_seq, 64, V]
    logits_q: torch.Tensor,    # [N_seq, 64, V]
    token_seqs: List[List[int]],
) -> Dict[str, float]:
    """
    Compute exact KL(P_ref || P_q), Top-1 agreement %, Top-1-in-Top-5 %, Top-5 overlap %,
    and real-token Cross-Entropy NLL & Perplexity across all sequences.
    """
    N, T, V = logits_ref.shape
    lr = logits_ref.reshape(-1, V).float()
    lq = logits_q.reshape(-1, V).float()

    log_pr = F.log_softmax(lr, dim=-1)
    log_pq = F.log_softmax(lq, dim=-1)
    pr = log_pr.exp()
    kl_per_pos = (pr * (log_pr - log_pq)).sum(dim=-1).clamp(min=0.0)

    top5_ref = torch.topk(lr, 5, dim=-1).indices  # [N*T, 5]
    top5_q = torch.topk(lq, 5, dim=-1).indices    # [N*T, 5]
    top1_ref = top5_ref[:, 0]
    top1_q = top5_q[:, 0]

    top1_agree = float((top1_q == top1_ref).float().mean().item() * 100.0)
    top1_in_ref_top5 = float((top1_q.unsqueeze(-1) == top5_ref).any(dim=-1).float().mean().item() * 100.0)
    # Set overlap of top-5 indices per position
    top5_matches = (top5_q.unsqueeze(-1) == top5_ref.unsqueeze(-2)).any(dim=-1).float().mean().item() * 100.0

    # Real next-token NLL / Perplexity on positions 0..62 predicting tokens 1..63
    targets = torch.tensor([seq[1:] for seq in token_seqs], dtype=torch.long)  # [N, 63]
    pred_logits = logits_q[:, :-1, :].float()  # [N, 63, V]
    nll = float(F.cross_entropy(pred_logits.reshape(-1, V), targets.reshape(-1)).item())
    ppl = float(math.exp(nll))

    return {
        "kl_mean_nats": float(kl_per_pos.mean().item()),
        "kl_median_nats": float(kl_per_pos.median().item()),
        "kl_max_nats": float(kl_per_pos.max().item()),
        "top1_agree_pct": top1_agree,
        "top1_in_top5_pct": top1_in_ref_top5,
        "top5_overlap_pct": top5_matches,
        "nll_nats": nll,
        "perplexity": ppl,
    }


# ======================================================================================
# 6. Binary Bundle Export (`--export <path>`) & Exact Round-Trip Verification
# ======================================================================================
def export_audit_bundle(
    export_path: Path,
    prompt_ids: List[int],
    p5_gen_bytes: bytes,
    boundaries_fp32: torch.Tensor,  # [25, 64, 1024]
    l0_audit: Dict[str, Any],
    base_weights: Dict[str, torch.Tensor],
) -> Dict[str, Any]:
    """
    Write deterministic little-endian binary bundle (`magic = b"QW35AUD1"`, `version = 1u32`)
    containing real T=64 hidden boundaries, P5 generated `sk-proj-...` bytes, Layer 0 exact
    division-free C=64 WY integer witnesses, and Layer 0 real OCP MXFP4 E2M1 delayed-bind
    matrix contraction bundles (`in_proj_z`, `out_proj`, `mlp.gate_proj`).
    """
    assert len(prompt_ids) == 64
    assert boundaries_fp32.shape == (25, 64, D_MODEL)

    # Quantize 25 boundary matrices and Layer 0 inputs to exact INT16
    h_bound_i16 = quantize_to_i16_fixed(boundaries_fp32, ACT_SCALE)                  # [25, 64, 1024]
    x_ln1_i16 = quantize_to_i16_fixed(l0_audit["X_ln1_fp32"], ACT_SCALE)             # [64, 1024]
    x_gdn_y_i16 = quantize_to_i16_fixed(l0_audit["X_gdn_y_fp32"], ACT_SCALE_GDN_Y)   # [64, 2048]
    x_ln2_i16 = quantize_to_i16_fixed(l0_audit["X_ln2_fp32"], ACT_SCALE)             # [64, 1024]
    x_inputs = [x_ln1_i16, x_gdn_y_i16, x_ln2_i16]
    x_input_scales = [ACT_SCALE, ACT_SCALE_GDN_Y, ACT_SCALE]

    wy_wit: IntegerWYWitness = l0_audit["wy_witness"]
    assert wy_wit.identity_errors == 0
    assert wy_wit.L_tilde.shape == (GDN_H, 64, 64)
    assert wy_wit.RHS.shape == (GDN_H, 64, 256)
    assert wy_wit.UW.shape == (GDN_H, 64, 256)
    assert wy_wit.R_rem.shape == (GDN_H, 64, 256)

    # Build 3 real Layer 0 OCP MXFP4 E2M1 matrix contraction bundles
    mat_specs = [
        ("linear_attn.in_proj_z", "layers.0.linear_attn.in_proj_z.weight", 0, False),
        ("linear_attn.out_proj", "layers.0.linear_attn.out_proj.weight", 1, False),
        ("mlp.gate_proj", "layers.0.mlp.gate_proj.weight", 2, True),  # 3584 -> 4096 zero-padded!
    ]
    mat_records = []
    mat_summaries = []
    for name, wkey, in_sel, pad_pow2 in mat_specs:
        pack = quantize_mxfp4_e2m1_block32(
            base_weights[wkey], block_size=32, pad_rows_pow2=pad_pow2, max_exp_span=7
        )
        X_mat = x_inputs[in_sel].astype(np.int64)  # [64, in_dim]
        # Exact unscaled integer contraction over Z:
        # Y_raw[i, j] = sum_{k, b} X[i, k*32 + b] * decode_e2m1_x2(Q[j, k, b]) * S[j, k]
        w_eff_int = (
            E2M1_NIBBLE_TO_X2[pack.q_nibbles] * pack.s_scales.astype(np.int64)[:, :, None]
        ).reshape(pack.J_pad, pack.in_dim)
        Y_raw = np.matmul(X_mat, w_eff_int.T).astype(np.int64)  # [64, J_pad]
        max_abs_y = int(np.max(np.abs(Y_raw)))
        assert max_abs_y < P_BB_HALF, f"{name} BabyBear overflow: max|Y_raw|={max_abs_y} >= {P_BB_HALF}"
        if pack.J_pad > pack.orig_rows:
            assert np.all(Y_raw[:, pack.orig_rows :] == 0), "Nonzero padded tail row!"

        # Cross-check float agreement against PyTorch F.linear(X_deq, W_deq)
        in_sc = float(x_input_scales[in_sel])
        y_from_raw = Y_raw[:, : pack.orig_rows].astype(np.float64) * (2.0 ** (pack.e_floor - 1)) / in_sc
        y_torch = F.linear(
            torch.from_numpy(X_mat.astype(np.float32) / in_sc),
            pack.dequantize_fp32(),
        ).numpy().astype(np.float64)
        max_fp_diff = float(np.max(np.abs(y_from_raw - y_torch)))
        assert max_fp_diff < 1e-4, f"{name} float mismatch: {max_fp_diff}"

        mat_records.append((name, in_sel, pack, Y_raw))
        mat_summaries.append(
            {
                "name": name,
                "orig_rows": pack.orig_rows,
                "J_pad": pack.J_pad,
                "in_dim": pack.in_dim,
                "K_blocks": pack.K_blocks,
                "e_floor": pack.e_floor,
                "max_scale": int(np.max(pack.s_scales)),
                "max_abs_y_raw": max_abs_y,
                "p_bb_half_margin": round(P_BB_HALF / max(max_abs_y, 1), 2),
                "max_fp_diff": max_fp_diff,
            }
        )

    # Write deterministic binary file
    export_path.parent.mkdir(parents=True, exist_ok=True)
    with open(export_path, "wb") as f:
        # 1. Magic + 14 u32 header fields = 64 bytes
        f.write(b"QW35AUD1")
        f.write(
            struct.pack(
                "<14I",
                1,              # version
                64,             # c_len
                D_MODEL,        # d_model = 1024
                GDN_H,          # h_v = 16
                GDN_D,          # d_k = 128
                GDN_D,          # d_v = 128
                D_FF,           # d_ff = 3584
                0,              # audited_layer_idx = 0
                M_WY,           # m_wy = 4096
                ACT_SCALE,      # act_scale_hidden = 512
                ACT_SCALE,      # act_scale_ln1 = 512
                ACT_SCALE_GDN_Y,  # act_scale_gdn_y = 2048
                ACT_SCALE,      # act_scale_ln2 = 512
                len(mat_records),
            )
        )
        # 2. Prompt tokens + P5 completion bytes
        f.write(np.asarray(prompt_ids, dtype="<u4").tobytes())
        f.write(struct.pack("<I", len(p5_gen_bytes)))
        f.write(p5_gen_bytes)
        # 3. 25 boundary hidden states
        f.write(np.ascontiguousarray(h_bound_i16, dtype="<i2").tobytes())
        # 4. Layer 0 WY integer witness
        f.write(np.ascontiguousarray(wy_wit.L_tilde, dtype="<i4").tobytes())
        f.write(np.ascontiguousarray(wy_wit.RHS, dtype="<i4").tobytes())
        f.write(np.ascontiguousarray(wy_wit.UW, dtype="<i4").tobytes())
        f.write(np.ascontiguousarray(wy_wit.R_rem, dtype="<u2").tobytes())
        # 5. Layer 0 INT16 input activations
        f.write(np.ascontiguousarray(x_ln1_i16, dtype="<i2").tobytes())
        f.write(np.ascontiguousarray(x_gdn_y_i16, dtype="<i2").tobytes())
        f.write(np.ascontiguousarray(x_ln2_i16, dtype="<i2").tobytes())
        # 6. 3 MXFP4 matrix records
        for name, in_sel, pack, Y_raw in mat_records:
            nb = name.encode("utf-8")
            f.write(struct.pack("<I", len(nb)))
            f.write(nb)
            f.write(
                struct.pack(
                    "<5Ii",
                    in_sel,
                    pack.orig_rows,
                    pack.J_pad,
                    pack.in_dim,
                    pack.K_blocks,
                    pack.e_floor,
                )
            )
            f.write(np.ascontiguousarray(pack.q_nibbles, dtype=np.uint8).tobytes())
            f.write(np.ascontiguousarray(pack.s_scales, dtype="<u4").tobytes())
            f.write(np.ascontiguousarray(Y_raw, dtype="<i8").tobytes())

    size_bytes = export_path.stat().st_size
    assert size_bytes < 25 * 1024 * 1024, f"Export size {size_bytes} exceeds 25 MB!"
    return {
        "path": str(export_path),
        "size_bytes": size_bytes,
        "size_mb": round(size_bytes / (1024.0 * 1024.0), 3),
        "wy_max_abs_lhs": wy_wit.max_abs_lhs,
        "wy_identity_errors": wy_wit.identity_errors,
        "matrices": mat_summaries,
    }


def verify_export_bundle_roundtrip(export_path: Path) -> Dict[str, Any]:
    """Read back the binary bundle from disk and verify EVERY byte, WY equation, and MXFP4 contraction."""
    data = export_path.read_bytes()
    off = 0

    def take(n: int) -> bytes:
        nonlocal off
        chunk = data[off : off + n]
        assert len(chunk) == n, f"Unexpected EOF at {off} (wanted {n})"
        off += n
        return chunk

    magic = take(8)
    assert magic == b"QW35AUD1", f"Bad magic: {magic!r}"
    hdr = struct.unpack("<14I", take(56))
    (
        ver, c_len, d_model, h_v, d_k, d_v, d_ff, audited_l,
        m_wy, s_hid, s_ln1, s_gy, s_ln2, num_mats,
    ) = hdr
    assert (ver, c_len, d_model, h_v, d_k, d_v, d_ff, audited_l, m_wy) == (
        1, 64, 1024, 16, 128, 128, 3584, 0, 4096
    )

    prompt_ids = np.frombuffer(take(c_len * 4), dtype="<u4")
    gen_len = struct.unpack("<I", take(4))[0]
    gen_str = take(gen_len).decode("utf-8", errors="replace")
    assert "sk-proj-" in gen_str, f"Generated bytes missing sk-proj-: {gen_str!r}"

    h_bound = np.frombuffer(take(25 * c_len * d_model * 2), dtype="<i2").reshape(25, c_len, d_model)
    L_tilde = np.frombuffer(take(h_v * c_len * c_len * 4), dtype="<i4").reshape(h_v, c_len, c_len).astype(np.int64)
    RHS = np.frombuffer(take(h_v * c_len * (d_v + d_k) * 4), dtype="<i4").reshape(h_v, c_len, d_v + d_k).astype(np.int64)
    UW = np.frombuffer(take(h_v * c_len * (d_v + d_k) * 4), dtype="<i4").reshape(h_v, c_len, d_v + d_k).astype(np.int64)
    R_rem = np.frombuffer(take(h_v * c_len * (d_v + d_k) * 2), dtype="<u2").reshape(h_v, c_len, d_v + d_k).astype(np.int64)

    # Verify strict lower triangularity & exact WY identity over Z
    triu_mask = np.triu(np.ones((c_len, c_len), dtype=bool), k=0)
    assert np.all(L_tilde[:, triu_mask] == 0), "L_tilde is not strictly lower-triangular!"
    assert np.all((R_rem >= 0) & (R_rem < m_wy)), "R_rem out of [0, M_wy)"
    lhs = np.matmul(L_tilde, UW)
    rhs = m_wy * (RHS - UW) + (m_wy // 2) - R_rem
    assert np.array_equal(lhs, rhs), "Round-trip WY identity failed!"
    assert int(np.max(np.abs(lhs))) < P_BB_HALF, "Round-trip WY exceeds P_BB // 2!"

    x_ln1 = np.frombuffer(take(c_len * d_model * 2), dtype="<i2").reshape(c_len, d_model).astype(np.int64)
    x_gy = np.frombuffer(take(c_len * (h_v * d_v) * 2), dtype="<i2").reshape(c_len, h_v * d_v).astype(np.int64)
    x_ln2 = np.frombuffer(take(c_len * d_model * 2), dtype="<i2").reshape(c_len, d_model).astype(np.int64)
    xs = [x_ln1, x_gy, x_ln2]

    checked_mats = []
    for _ in range(num_mats):
        nlen = struct.unpack("<I", take(4))[0]
        mname = take(nlen).decode("utf-8")
        in_sel, orig_r, J_pad, in_dim, K_blks, e_floor = struct.unpack("<5Ii", take(24))
        Q = np.frombuffer(take(J_pad * K_blks * 32), dtype=np.uint8).reshape(J_pad, K_blks, 32)
        S = np.frombuffer(take(J_pad * K_blks * 4), dtype="<u4").reshape(J_pad, K_blks).astype(np.int64)
        Y = np.frombuffer(take(c_len * J_pad * 8), dtype="<i8").reshape(c_len, J_pad)
        assert np.all(Q < 16) and not np.any(Q == 8), f"Invalid nibble in {mname}"
        W_eff = (E2M1_NIBBLE_TO_X2[Q] * S[:, :, None]).reshape(J_pad, in_dim)
        Y_recomp = np.matmul(xs[in_sel], W_eff.T)
        assert np.array_equal(Y, Y_recomp), f"Round-trip MXFP4 contraction mismatch for {mname}!"
        assert int(np.max(np.abs(Y))) < P_BB_HALF, f"Round-trip Y_raw overflow for {mname}!"
        checked_mats.append(mname)

    assert off == len(data), f"Trailing unparsed bytes: {len(data) - off}"
    return {
        "verified": True,
        "bytes_parsed": off,
        "prompt_len": int(prompt_ids.shape[0]),
        "gen_excerpt": gen_str,
        "h_bound_shape": list(h_bound.shape),
        "wy_entries_verified": int(lhs.size),
        "wy_max_abs_lhs": int(np.max(np.abs(lhs))),
        "mxfp4_mats_verified": checked_mats,
    }


# ======================================================================================
# 7. Real HTTP-Range 4-Layer Slice & Shipped 4-Bit Audit (`Qwen/Qwen3.8-Flash-Next-FP8`)
# ======================================================================================
def run_qwen38fn_range_audit(export_path: Optional[str] = None) -> Dict[str, Any]:
    """
    Pulls exact byte ranges (< 400 MB Non-Expert/PLE + routed MoE slices instead of 180 GB)
    via HTTP `Range` from:
      - `Qwen/Qwen3.8-Flash-Next-FP8` (`embed_tokens` queried rows + `L0..L3` = `3 GDN + 1 QSA`
        + `8 GR` + `512E Top-10+1` MoE + `51.20B` Layer-2 SplitMix64 16-prime PLE),
      - `nvidia/Qwen3.8-Flash-Next-FP4-Local` (`NVFP4-CSF` + `MXFP8`),
      - `mlx-community/Qwen3.8-Flash-Next-4bit` (`affine-4bit` group-32),
    executes the upstream `modeling_qwen4_exp.py` 4-layer forward pass + integer `H_v=48`
    `C=64` WY witness + 7-bucket 0-mul E2M1 Horner expert witness + `L3` QSA `ReLU` indexer
    audit, and optionally writes `QW38FNS1` binary bundle (`< 35 MB`).
    """
    import concurrent.futures
    import shutil
    import urllib.request
    from collections import defaultdict

    cache_dir = "/tmp/qwen38fn_range_cache"
    fp8_repo = "https://huggingface.co/Qwen/Qwen3.8-Flash-Next-FP8/resolve/main"
    nvfp4_repo = "https://huggingface.co/nvidia/Qwen3.8-Flash-Next-FP4-Local/resolve/main"
    mlx_repo = "https://huggingface.co/mlx-community/Qwen3.8-Flash-Next-4bit/resolve/main"
    eos_id = 248044
    hidden_q38 = 2560
    hc_count = 4
    mask64 = (1 << 64) - 1
    splitmix_gamma = 0x9E3779B97F4A7C15
    splitmix_m1 = 0xBF58476D1CE4E5B9
    splitmix_m2 = 0x94D049BB133111EB
    prime_1 = 10007

    e2m1_float_lut = torch.tensor(
        [0.0, 0.5, 1.0, 1.5, 2.0, 3.0, 4.0, 6.0, -0.0, -0.5, -1.0, -1.5, -2.0, -3.0, -4.0, -6.0],
        dtype=torch.float32,
    )
    e2m1_2x_int_lut = torch.tensor(
        [0, 1, 2, 3, 4, 6, 8, 12, 0, -1, -2, -3, -4, -6, -8, -12],
        dtype=torch.int64,
    )
    e2m1_pos_mags = torch.tensor([0.0, 0.5, 1.0, 1.5, 2.0, 3.0, 4.0, 6.0], dtype=torch.float32)

    def _decode_raw(buf: bytearray, dtype: str, shape: List[int]) -> torch.Tensor:
        if dtype == "BF16":
            return torch.frombuffer(buf, dtype=torch.bfloat16).reshape(shape).float().clone()
        if dtype == "F16":
            return torch.frombuffer(buf, dtype=torch.float16).reshape(shape).float().clone()
        if dtype == "F32":
            return torch.frombuffer(buf, dtype=torch.float32).reshape(shape).clone()
        if dtype == "F8_E4M3":
            return torch.frombuffer(buf, dtype=torch.uint8).view(torch.float8_e4m3fn).reshape(shape).float().clone()
        if dtype == "U8":
            return torch.frombuffer(buf, dtype=torch.uint8).reshape(shape).clone()
        if dtype == "U32":
            return torch.frombuffer(buf, dtype=torch.uint32).reshape(shape).clone()
        if dtype == "I64":
            return torch.frombuffer(buf, dtype=torch.int64).reshape(shape).clone()
        if dtype == "I32":
            return torch.frombuffer(buf, dtype=torch.int32).reshape(shape).clone()
        raise ValueError(f"Unsupported dtype: {dtype}")

    class _RangeFetcher:
        def __init__(self, max_workers: int = 8):
            self.max_workers = max_workers
            self.bytes_by_tag: Dict[str, int] = defaultdict(int)
            self.reqs_by_tag: Dict[str, int] = defaultdict(int)
            self.header_cache: Dict[str, Tuple[int, Dict[str, Any]]] = {}

        def fetch_bytes(self, url: str, start: Optional[int] = None, end: Optional[int] = None, tag: str = "misc") -> bytes:
            headers = {"User-Agent": "qwen35audit-range-slice/1.0"}
            if start is not None and end is not None:
                headers["Range"] = f"bytes={start}-{end}"
            last_err = None
            for attempt in range(4):
                try:
                    req = urllib.request.Request(url, headers=headers)
                    with urllib.request.urlopen(req, timeout=45) as resp:
                        data = resp.read()
                    self.bytes_by_tag[tag] += len(data)
                    self.reqs_by_tag[tag] += 1
                    return data
                except Exception as e:
                    last_err = e
                    time.sleep(0.4 * (attempt + 1))
            raise RuntimeError(f"Failed fetching {url} [{start}-{end}]: {last_err}")

        def fetch_json(self, url: str, tag: str = "meta") -> Dict[str, Any]:
            return json.loads(self.fetch_bytes(url, tag=tag).decode("utf-8"))

        def get_st_header(self, url: str, tag: str = "headers") -> Tuple[int, Dict[str, Any]]:
            if url in self.header_cache:
                return self.header_cache[url]
            head = self.fetch_bytes(url, 0, 524287, tag=tag)
            hlen = struct.unpack("<Q", head[:8])[0]
            if 8 + hlen <= len(head):
                hdr_bytes = head[8 : 8 + hlen]
            else:
                rest = self.fetch_bytes(url, len(head), 8 + hlen - 1, tag=tag)
                hdr_bytes = head[8:] + rest
            res = (8 + hlen, json.loads(hdr_bytes.decode("utf-8")))
            self.header_cache[url] = res
            return res

        def fetch_tensors_coalesced(
            self,
            requests_list: List[Tuple[str, str, Optional[int], Optional[int]]],
            tag: str = "weights",
            gap_merge_bytes: int = 131072,
            max_span_bytes: int = 24 * 1024 * 1024,
        ) -> Dict[Tuple[str, str, Optional[int], Optional[int]], torch.Tensor]:
            urls = [u for u in dict.fromkeys(r[0] for r in requests_list) if u not in self.header_cache]
            if urls:
                with concurrent.futures.ThreadPoolExecutor(max_workers=self.max_workers) as ex:
                    list(ex.map(lambda u: self.get_st_header(u, tag="headers"), urls))
            by_url: Dict[str, List[Any]] = defaultdict(list)
            dt_map = {"BF16": 2, "F16": 2, "F32": 4, "F8_E4M3": 1, "U8": 1, "U32": 4, "I64": 8, "I32": 4}
            for req_key in requests_list:
                url, tname, r0, r1 = req_key
                base, hdr = self.get_st_header(url)
                meta = hdr[tname]
                s_off, e_off = meta["data_offsets"]
                dtype = meta["dtype"]
                shape = list(meta["shape"])
                dt_sz = dt_map[dtype]
                if r0 is not None and r1 is not None:
                    row_stride = int(math.prod(shape[1:])) * dt_sz
                    b0 = base + s_off + r0 * row_stride
                    b1 = base + s_off + r1 * row_stride - 1
                    out_shape = [r1 - r0] + shape[1:]
                else:
                    b0, b1, out_shape = base + s_off, base + e_off - 1, shape
                by_url[url].append((b0, b1, req_key, dtype, out_shape))

            chunks = []
            for url, items in by_url.items():
                items.sort(key=lambda x: x[0])
                cur_b0, cur_b1, cur_items = items[0][0], items[0][1], [items[0]]
                for it in items[1:]:
                    b0, b1 = it[0], it[1]
                    if b0 <= cur_b1 + 1 + gap_merge_bytes and (max(cur_b1, b1) - cur_b0 + 1) <= max_span_bytes:
                        cur_b1 = max(cur_b1, b1)
                        cur_items.append(it)
                    else:
                        chunks.append((url, cur_b0, cur_b1, cur_items))
                        cur_b0, cur_b1, cur_items = b0, b1, [it]
                chunks.append((url, cur_b0, cur_b1, cur_items))

            results: Dict[Tuple[str, str, Optional[int], Optional[int]], torch.Tensor] = {}

            def _do_chunk(ch: Any) -> List[Tuple[Any, torch.Tensor]]:
                url, cb0, cb1, items = ch
                raw = self.fetch_bytes(url, cb0, cb1, tag=tag)
                mv = memoryview(raw)
                return [
                    (rk, _decode_raw(bytearray(mv[b0 - cb0 : b1 - cb0 + 1]), dt, osh))
                    for b0, b1, rk, dt, osh in items
                ]

            with concurrent.futures.ThreadPoolExecutor(max_workers=self.max_workers) as ex:
                for chunk_res in ex.map(_do_chunk, chunks):
                    for rk, t in chunk_res:
                        results[rk] = t
            return results

    def _rms_norm(x: torch.Tensor, weight: torch.Tensor, group_size: Optional[int] = None) -> torch.Tensor:
        orig_shape = x.shape
        xf = x.float()
        if group_size is not None:
            xf = xf.reshape(*orig_shape[:-1], -1, group_size)
        out = xf * torch.rsqrt(xf.pow(2).mean(-1, keepdim=True) + RMS_EPS)
        if group_size is not None:
            out = out.flatten(-2)
        return out * (1.0 + weight.float())

    def _rms_norm_gated(x: torch.Tensor, gate: torch.Tensor, weight: torch.Tensor) -> torch.Tensor:
        xf = x.float()
        out = xf * torch.rsqrt(xf.pow(2).mean(-1, keepdim=True) + RMS_EPS) * weight.float()
        return out * torch.sigmoid(gate.float())

    def _l2norm(x: torch.Tensor) -> torch.Tensor:
        return x * torch.rsqrt((x * x).sum(dim=-1, keepdim=True) + 1e-6)

    def _apply_rope(q: torch.Tensor, cos: torch.Tensor, sin: torch.Tensor, unsqueeze_dim: int = 1) -> torch.Tensor:
        cos_u = cos.unsqueeze(unsqueeze_dim)
        sin_u = sin.unsqueeze(unsqueeze_dim)
        rdim = cos_u.shape[-1]
        q_r, q_n = q[..., :rdim], q[..., rdim:]
        q1, q2 = q_r[..., : rdim // 2], q_r[..., rdim // 2 :]
        q_r = (q_r * cos_u) + (torch.cat((-q2, q1), dim=-1) * sin_u)
        return torch.cat([q_r, q_n], dim=-1)

    def _cos_and_snr(ref: torch.Tensor, est: torch.Tensor) -> Dict[str, float]:
        r = ref.float().flatten()
        e = est.float().flatten()
        cos = float(F.cosine_similarity(r, e, dim=0).item())
        mse = float(((r - e) ** 2).mean().item())
        sig = float((r ** 2).mean().item())
        snr = float(10.0 * math.log10(sig / max(mse, 1e-30)))
        return {"cos_sim": round(cos, 6), "snr_db": round(snr, 3), "max_abs_err": round(float((r - e).abs().max().item()), 6)}

    def _quant_mxfp4_b32(w: torch.Tensor) -> Tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        M, K = w.shape
        wf = w.float().reshape(M, K // 32, 32)
        amax = wf.abs().amax(dim=-1)
        exps = torch.ceil(torch.log2(amax.clamp_min(2.0 ** -30) / 6.0)).to(torch.int32)
        zero_blk = amax == 0.0
        if zero_blk.any():
            min_nz = int(exps[~zero_blk].min().item()) if (~zero_blk).any() else -16
            exps = torch.where(zero_blk, torch.full_like(exps, min_nz), exps)
        scales = torch.pow(2.0, exps.float())
        normed = wf / scales.unsqueeze(-1)
        signs = (normed < 0).to(torch.uint8)
        idx = (normed.abs().unsqueeze(-1) - e2m1_pos_mags.view(1, 1, 1, 8)).abs().argmin(dim=-1).to(torch.uint8)
        nibs = torch.where(idx == 0, torch.zeros_like(idx), (signs << 3) | idx)
        return (e2m1_float_lut[nibs.long()] * scales.unsqueeze(-1)).reshape(M, K), nibs.reshape(M, K), exps

    def _splitmix64(val: int) -> int:
        val = (val + splitmix_gamma) & mask64
        val = ((val ^ (val >> 30)) * splitmix_m1) & mask64
        val = ((val ^ (val >> 27)) * splitmix_m2) & mask64
        return (val ^ (val >> 31)) & mask64

    def _is_prime(v: int) -> bool:
        if v < 2 or (v % 2 == 0 and v != 2):
            return False
        return all(v % d != 0 for d in range(3, math.isqrt(v) + 1, 2))

    t0 = time.time()
    os.makedirs(cache_dir, exist_ok=True)
    fetcher = _RangeFetcher(max_workers=8)
    report: Dict[str, Any] = {}

    try:
        fp8_idx = fetcher.fetch_json(f"{fp8_repo}/model.safetensors.index.json", tag="index")["weight_map"]
        fp8_tok_cfg = fetcher.fetch_json(f"{fp8_repo}/tokenizer_config.json", tag="meta")
        nv_idx = fetcher.fetch_json(f"{nvfp4_repo}/model.safetensors.index.json", tag="index")["weight_map"]
        mlx_idx = fetcher.fetch_json(f"{mlx_repo}/model.safetensors.index.json", tag="index")["weight_map"]

        tok = Tokenizer.from_file(str(TOKENIZER_PATH))
        ids_a = tok.encode("Zero-knowledge proof verification for gated delta recurrence and sparse attention. ").ids
        ids_b = tok.encode("Zero-knowledge proof verification for gated delta recurrence and block quantization. ").ids
        prompt_ids_list = ((ids_a + ids_b) * 4)[:31] + [eos_id] + ((ids_b + ids_a) * 4)[:32]
        input_ids = torch.tensor([prompt_ids_list], dtype=torch.int64)
        report["prompt"] = {
            "seq_len": 64,
            "eos_positions": [31],
            "unique_tokens": len(set(prompt_ids_list)),
            "cached_vocab_size": tok.get_vocab_size(),
            "fp8_eos_token": fp8_tok_cfg.get("eos_token"),
        }

        # Shipped 4-bit L0 comparison
        comp_reqs: List[Tuple[str, str, Optional[int], Optional[int]]] = []
        for proj in ("gate_proj", "up_proj", "down_proj"):
            kp = f"model.language_model.layers.0.mlp.experts.0.{proj}"
            comp_reqs += [(f"{fp8_repo}/{fp8_idx[f'{kp}.weight']}", f"{kp}.weight", None, None),
                          (f"{fp8_repo}/{fp8_idx[f'{kp}.weight_scale_inv']}", f"{kp}.weight_scale_inv", None, None)]
            for sfx in ("weight", "weight_scale.nvfp4_csf_fixed", "weight_scale.nvfp4_csf_exceptions", "weight_scale_2"):
                comp_reqs.append((f"{nvfp4_repo}/{nv_idx[f'{kp}.{sfx}']}", f"{kp}.{sfx}", None, None))
            for sfx in ("weight", "scales", "biases"):
                mk = f"language_model.model.layers.0.mlp.switch_mlp.{proj}.{sfx}"
                comp_reqs.append((f"{mlx_repo}/{mlx_idx[mk]}", mk, 0, 1))
        for proj in ("in_proj_qkv", "out_proj"):
            kp = f"model.language_model.layers.0.linear_attn.{proj}"
            comp_reqs += [(f"{nvfp4_repo}/{nv_idx[f'{kp}.weight']}", f"{kp}.weight", None, None),
                          (f"{nvfp4_repo}/{nv_idx[f'{kp}.weight_scale']}", f"{kp}.weight_scale", None, None)]
            for sfx in ("weight", "scales", "biases"):
                mk = f"language_model.model.layers.0.linear_attn.{proj}.{sfx}"
                comp_reqs.append((f"{mlx_repo}/{mlx_idx[mk]}", mk, None, None))
        comp_t = fetcher.fetch_tensors_coalesced(comp_reqs, tag="4bit_compare")

        # Non-expert L0..L3 + queried embed_tokens + 1,024 PLE rows
        emb_key = "model.language_model.embed_tokens.weight"
        emb_url = f"{fp8_repo}/{fp8_idx[emb_key]}"
        unique_tids = sorted(set(prompt_ids_list))
        non_exp_reqs: List[Tuple[str, str, Optional[int], Optional[int]]] = [
            (emb_url, emb_key, tid, tid + 1) for tid in unique_tids
        ]
        for l_i in range(4):
            for k in sorted(fp8_idx.keys()):
                if k.startswith(f"model.language_model.layers.{l_i}.") and ".experts." not in k and "ngram_embedding.shard_" not in k:
                    non_exp_reqs.append((f"{fp8_repo}/{fp8_idx[k]}", k, None, None))

        half_bound = max(1, (((1 << 63) - 1) // VOCAB_SIZE) // 2)
        base_seed = 1234 + prime_1 * 0
        derived_mults = torch.tensor(
            [2 * (_splitmix64((base_seed + splitmix_gamma * (idx + 1)) & mask64) % half_bound) + 1 for idx in range(3)],
            dtype=torch.int64,
        )
        primes_list: List[int] = []
        p_cand = 20000000 - 1
        while len(primes_list) < 16:
            p_cand += 1
            if _is_prime(p_cand):
                primes_list.append(p_cand)
        derived_sizes = torch.tensor(primes_list, dtype=torch.int64)
        derived_offsets = torch.tensor([sum(primes_list[:h]) for h in range(16)], dtype=torch.int64)

        def _shift_eos(t_ids: torch.Tensor, shift: int) -> torch.Tensor:
            if shift == 0:
                return t_ids
            bs, sl = t_ids.shape
            pos = torch.arange(sl, dtype=torch.int64)
            eos_pos = torch.where(t_ids == eos_id, pos, torch.tensor(-1, dtype=torch.int64))
            prev_inc = torch.cummax(eos_pos, dim=1).values
            prev_eos = torch.cat([torch.full((bs, 1), -1, dtype=torch.int64), prev_inc[:, :-1]], dim=1)
            pos_seg = pos.unsqueeze(0) - (prev_eos + 1)
            src_pos = pos - shift
            shifted = t_ids.gather(dim=1, index=src_pos.clamp_min(0).unsqueeze(0).expand(bs, -1))
            return torch.where((pos_seg >= shift) & (src_pos.unsqueeze(0) >= 0), shifted, torch.full_like(shifted, eos_id))

        hist = torch.cat([torch.full((1, 2), eos_id, dtype=torch.int64), input_ids], dim=-1)
        sh_hist = [_shift_eos(hist, s) for s in range(3)]
        ple_blocks = []
        for ng in (2, 3):
            s_i, e_i = (ng - 2) * 8, (ng - 1) * 8
            mixed = sh_hist[0] * derived_mults[0]
            for p_i in range(1, ng):
                mixed = torch.bitwise_xor(mixed, sh_hist[p_i] * derived_mults[p_i])
            ple_blocks.append(torch.remainder(mixed.unsqueeze(-1), derived_sizes[s_i:e_i].view(1, 1, -1)) + derived_offsets[s_i:e_i].view(1, 1, -1))
        ngram_ids = torch.cat(ple_blocks, dim=-1)[:, -64:]

        shard_rows = 2500012
        ple_shard_map = {
            int(k.split("shard_")[1].split(".")[0]): (f"{fp8_repo}/{v}", k)
            for k, v in fp8_idx.items()
            if "ngram_embedding.shard_" in k
        }
        unique_ple_rows = sorted(set(int(x) for x in ngram_ids.flatten().tolist()))
        ple_row_reqs = [
            (ple_shard_map[r_idx // shard_rows][0], ple_shard_map[r_idx // shard_rows][1], r_idx % shard_rows, (r_idx % shard_rows) + 1)
            for r_idx in unique_ple_rows
        ]
        nonexp_t = fetcher.fetch_tensors_coalesced(non_exp_reqs, tag="l0_l3_nonexp")
        ple_t = fetcher.fetch_tensors_coalesced(ple_row_reqs, tag="ple_1024_rows", gap_merge_bytes=4096)
        get_w = lambda k: nonexp_t[(f"{fp8_repo}/{fp8_idx[k]}", k, None, None)]

        assert torch.equal(derived_mults, get_w("model.language_model.layers.1.ple.ple_embedding.layer_multipliers"))
        assert torch.equal(derived_sizes, get_w("model.language_model.layers.1.ple.ple_embedding.ngram_heads_vocab_sizes"))
        ple_w_scale = float(get_w("model.language_model.layers.1.ple.ple_embedding.ngram_embedding.weight_scale").item())
        report["ple_verification"] = {
            "layer_multipliers": derived_mults.tolist(),
            "primes_16": derived_sizes.tolist(),
            "unique_ple_rows_fetched": len(unique_ple_rows),
            "ple_weight_scale": ple_w_scale,
        }

        def _decode_nvfp4_csf(nv_w: torch.Tensor, nv_fix: torch.Tensor, nv_exc: torch.Tensor, nv_s2: float, sh: Tuple[int, int]) -> torch.Tensor:
            M, K = sh
            bases = nv_fix[:, :16].to(torch.int32)
            pk = nv_fix[:, 16:]
            nibs = torch.stack([(pk & 0xF).to(torch.int32), ((pk >> 4) & 0xF).to(torch.int32)], dim=-1).reshape(M // 16, 16, K // 16)
            sc_u8 = (bases.unsqueeze(-1) + nibs).reshape(-1)
            ex64 = nv_exc.to(torch.int64)
            sc_u8[ex64 & 0xFFFFFF] = ((ex64 >> 24) & 0xFF).to(torch.int32)
            sc_f = sc_u8.to(torch.uint8).view(torch.float8_e4m3fn).float().reshape(M, K // 16)
            w_e = torch.stack([e2m1_float_lut[(nv_w & 0xF).long()], e2m1_float_lut[((nv_w >> 4) & 0xF).long()]], dim=-1).reshape(M, K)
            return w_e * (sc_f * nv_s2).repeat_interleave(16, dim=1)

        def _decode_mlx4(w_u32: torch.Tensor, sc: torch.Tensor, bi: torch.Tensor) -> torch.Tensor:
            u = w_u32.to(torch.int64)
            nibs = torch.stack([(u >> (4 * i)) & 0xF for i in range(8)], dim=-1).reshape(w_u32.shape[0], -1).float()
            return nibs * sc.repeat_interleave(32, dim=1) + bi.repeat_interleave(32, dim=1)

        shipped_4bit: Dict[str, Any] = {}
        for proj, sh_out in [("gate_proj", (640, 2560)), ("up_proj", (640, 2560)), ("down_proj", (2560, 640))]:
            kp = f"model.language_model.layers.0.mlp.experts.0.{proj}"
            wf = comp_t[(f"{fp8_repo}/{fp8_idx[f'{kp}.weight']}", f"{kp}.weight", None, None)] * comp_t[
                (f"{fp8_repo}/{fp8_idx[f'{kp}.weight_scale_inv']}", f"{kp}.weight_scale_inv", None, None)
            ].repeat_interleave(128, dim=0).repeat_interleave(128, dim=1)
            wnv = _decode_nvfp4_csf(
                comp_t[(f"{nvfp4_repo}/{nv_idx[f'{kp}.weight']}", f"{kp}.weight", None, None)],
                comp_t[(f"{nvfp4_repo}/{nv_idx[f'{kp}.weight_scale.nvfp4_csf_fixed']}", f"{kp}.weight_scale.nvfp4_csf_fixed", None, None)],
                comp_t[(f"{nvfp4_repo}/{nv_idx[f'{kp}.weight_scale.nvfp4_csf_exceptions']}", f"{kp}.weight_scale.nvfp4_csf_exceptions", None, None)],
                float(comp_t[(f"{nvfp4_repo}/{nv_idx[f'{kp}.weight_scale_2']}", f"{kp}.weight_scale_2", None, None)].item()),
                sh_out,
            )
            mkp = f"language_model.model.layers.0.mlp.switch_mlp.{proj}"
            wmlx = _decode_mlx4(
                comp_t[(f"{mlx_repo}/{mlx_idx[f'{mkp}.weight']}", f"{mkp}.weight", 0, 1)][0],
                comp_t[(f"{mlx_repo}/{mlx_idx[f'{mkp}.scales']}", f"{mkp}.scales", 0, 1)][0],
                comp_t[(f"{mlx_repo}/{mlx_idx[f'{mkp}.biases']}", f"{mkp}.biases", 0, 1)][0],
            )
            wmx, _, _ = _quant_mxfp4_b32(wf)
            shipped_4bit[f"L0_expert0_{proj}"] = {
                "nvfp4_csf_vs_fp8": _cos_and_snr(wf, wnv),
                "mlx_4bit_g32_vs_fp8": _cos_and_snr(wf, wmlx),
                "our_mxfp4_b32_vs_fp8": _cos_and_snr(wf, wmx),
            }
        report["shipped_4bit_comparisons"] = shipped_4bit
        del comp_t

        # 4-layer execution (L0..L3)
        emb_rows = {tid: nonexp_t[(emb_url, emb_key, tid, tid + 1)][0] for tid in unique_tids}
        h_ref = torch.stack([emb_rows[tid] for tid in prompt_ids_list], dim=0).unsqueeze(0).repeat(1, 1, hc_count)
        inv_freq = 1.0 / (10000000.0 ** (torch.arange(0, 64, 2, dtype=torch.float32) / 64.0))
        freqs = torch.outer(torch.arange(64, dtype=torch.float32), inv_freq)
        emb_r = torch.cat((freqs, freqs), dim=-1)
        cos_r, sin_r = emb_r.cos().unsqueeze(0), emb_r.sin().unsqueeze(0)

        def _gr(h_in: torch.Tensor, pfx: str) -> Tuple[torch.Tensor, torch.Tensor, Dict[str, Any]]:
            hn = _rms_norm(h_in, get_w(f"{pfx}.hc_norm.weight"), group_size=hidden_q38)
            mx = F.silu(F.linear(hn, get_w(f"{pfx}.input_mix_weight_down.weight")) / hc_count)
            mx = torch.sigmoid(F.linear(mx, get_w(f"{pfx}.input_mix_weight_up.weight"))).unflatten(-1, (hc_count, hidden_q38))
            mixed = (mx * hn.unflatten(-1, (hc_count, hidden_q38))).mean(dim=-2)
            inj = 2.0 * torch.sigmoid(F.linear(hn, get_w(f"{pfx}.block_inject_weight.weight")) / hc_count)
            return mixed, inj, {
                "stream_abs_max": round(float(h_in.abs().max().item()), 4),
                "branch_l2": [round(float(h_in.unflatten(-1, (hc_count, hidden_q38))[..., b, :].norm(dim=-1).mean().item()), 4) for b in range(hc_count)],
            }

        l0_wy_wit: Optional[Dict[str, Any]] = None
        l0_exp_wit: Optional[Dict[str, Any]] = None
        l0_eid, l0_tok = 0, 0
        l3_scores_i32 = torch.zeros((64, 16), dtype=torch.int32)
        l3_dots_i32 = torch.zeros((64, 16, 4), dtype=torch.int32)
        l3_valid_u8 = torch.zeros((64, 16), dtype=torch.uint8)
        layer_reps: Dict[str, Any] = {}

        for l_i in range(4):
            lr: Dict[str, Any] = {}
            if l_i == 1:
                sc_mul = ple_w_scale if ple_w_scale <= 1.0 else (1.0 / ple_w_scale)
                rvecs = {
                    r_idx: ple_t[(ple_shard_map[r_idx // shard_rows][0], ple_shard_map[r_idx // shard_rows][1], r_idx % shard_rows, (r_idx % shard_rows) + 1)][0] * sc_mul
                    for r_idx in unique_ple_rows
                }
                embs = torch.stack([torch.cat([rvecs[int(ngram_ids[0, t_i, h_i].item())] for h_i in range(16)], dim=-1) for t_i in range(64)], dim=0).unsqueeze(0)
                pp = "model.language_model.layers.1.ple"
                kn = _rms_norm(F.linear(embs, get_w(f"{pp}.key_proj.weight")), get_w(f"{pp}.norm_key.weight"), group_size=hidden_q38).unflatten(-1, (hc_count, hidden_q38))
                val = F.linear(embs, get_w(f"{pp}.value_proj.weight"))
                qn = _rms_norm(h_ref, get_w(f"{pp}.norm_query.weight"), group_size=hidden_q38).unflatten(-1, (hc_count, hidden_q38))
                gt = (kn * qn).sum(dim=-1, keepdim=True) / math.sqrt(hidden_q38)
                gt = gt.abs().clamp_min(1e-6).sqrt() * gt.sign()
                gv = (torch.sigmoid(gt) * val.unsqueeze(-2)).flatten(-2)
                gvn = _rms_norm(gv, get_w(f"{pp}.norm_conv.weight"), group_size=hidden_q38)
                sconv = F.silu(F.conv1d(F.pad(gvn.transpose(1, 2), (9, 0)), get_w(f"{pp}.conv1d.weight"), dilation=3, groups=10240)).transpose(1, 2)
                h_ref = h_ref + gv + sconv

            x_a, inj_a, lr["gr_attn"] = _gr(h_ref, f"model.language_model.layers.{l_i}.attn_hyper_connection")
            if l_i < 3:
                pa = f"model.language_model.layers.{l_i}.linear_attn"
                mqkv = F.silu(F.conv1d(F.linear(x_a, get_w(f"{pa}.in_proj_qkv.weight")).transpose(1, 2), get_w(f"{pa}.conv1d.weight"), padding=3, groups=10240)[:, :, :64]).transpose(1, 2)
                q, k, v = torch.split(mqkv, [2048, 2048, 6144], dim=-1)
                q = _l2norm(q.reshape(1, 64, 16, 128).repeat_interleave(3, dim=2).transpose(1, 2)) * (128.0 ** -0.5)
                k = _l2norm(k.reshape(1, 64, 16, 128).repeat_interleave(3, dim=2).transpose(1, 2))
                v = v.reshape(1, 64, 48, 128).transpose(1, 2)
                z = F.linear(x_a, get_w(f"{pa}.in_proj_z.weight")).reshape(1, 64, 48, 128)
                b = torch.sigmoid(F.linear(x_a, get_w(f"{pa}.in_proj_b.weight"))).transpose(1, 2)
                g = (-get_w(f"{pa}.A_log").float().exp() * F.softplus(F.linear(x_a, get_w(f"{pa}.in_proj_a.weight")).float() + get_w(f"{pa}.dt_bias").float())).transpose(1, 2)
                cdec = g.cumsum(dim=-1)
                pdec = (cdec.unsqueeze(-1) - cdec.unsqueeze(-2)).masked_fill(torch.ones(64, 64, dtype=torch.bool).triu(1), float("-inf")).exp()
                kb = k * b.unsqueeze(-1)
                vb = v * b.unsqueeze(-1)
                ut = (kb @ k.transpose(-1, -2)) * pdec
                ia = (q @ k.transpose(-1, -2)) * pdec
                dkb = kb * cdec.exp().unsqueeze(-1)
                u_sol = torch.linalg.solve_triangular(ut, vb, upper=False, unitriangular=True)
                w_sol = torch.linalg.solve_triangular(ut, dkb, upper=False, unitriangular=True)
                core = _rms_norm_gated((ia @ u_sol).transpose(1, 2).reshape(-1, 128), z.reshape(-1, 128), get_w(f"{pa}.norm.weight"))
                out_a = F.linear(core.reshape(1, 64, 6144), get_w(f"{pa}.out_proj.weight"))
                if l_i == 0:
                    L_f = ut[0].tril(-1)
                    RHS_f = torch.cat([vb[0], dkb[0]], dim=-1)
                    UW_ref = torch.cat([u_sol[0], w_sol[0]], dim=-1)
                    s_rhs = float(2 ** min(16, max(8, int(math.floor(math.log2(32768.0 / max(float(RHS_f.abs().max()), float(UW_ref.abs().max()), 1e-6)))))))
                    L_t = torch.where(torch.ones(64, 64, dtype=torch.bool).tril(-1).unsqueeze(0), torch.round(L_f * 4096.0).to(torch.int64), torch.zeros((48, 64, 64), dtype=torch.int64))
                    RHS_i = torch.round(RHS_f * s_rhs).to(torch.int64)
                    UW_i = torch.zeros_like(RHS_i)
                    R_rem = torch.zeros_like(RHS_i)
                    for r_i in range(64):
                        acc = torch.zeros(48, 256, dtype=torch.int64) if r_i == 0 else torch.einsum("hj,hjc->hc", L_t[:, r_i, :r_i], UW_i[:, :r_i, :])
                        q_d = torch.div(acc + 2047, 4096, rounding_mode="floor")
                        UW_i[:, r_i, :] = RHS_i[:, r_i, :] - q_d
                        R_rem[:, r_i, :] = 4096 * q_d + 2048 - acc
                    assert torch.equal(torch.einsum("hij,hjc->hic", L_t, UW_i), 4096 * (RHS_i - UW_i) + 2048 - R_rem)
                    l0_wy_wit = {"L_tilde": L_t.to(torch.int32), "RHS": RHS_i.to(torch.int32), "UW": UW_i.to(torch.int32), "R_rem": R_rem.to(torch.uint16), "S_rhs": s_rhs, "M_wy": 4096}
                    lr["gdn_wy_uw_fidelity"] = _cos_and_snr(UW_ref, UW_i.float() / s_rhs)
            else:
                ps = f"model.language_model.layers.{l_i}.self_attn"
                iq, ik = torch.split(F.linear(x_a, get_w(f"{ps}.indexer.index_qk_proj.weight")), [512, 128], dim=-1)
                iq = _apply_rope(_rms_norm(iq.reshape(1, 64, 4, 128), get_w(f"{ps}.indexer.q_layernorm.weight")), cos_r, sin_r, unsqueeze_dim=2)
                bk = _rms_norm(ik.reshape(16, 4, 128).mean(dim=1), get_w(f"{ps}.indexer.k_layernorm.weight"))
                sts = torch.arange(0, 64, 4, dtype=torch.int64)
                bk = _apply_rope(bk.unsqueeze(1), cos_r[0].index_select(0, sts), sin_r[0].index_select(0, sts), unsqueeze_dim=1).squeeze(1)
                rdots = torch.einsum("qhd,bd->qbh", iq[0].float(), bk.float())
                bscores = F.relu(rdots).sum(dim=-1) / math.sqrt(128.0)
                vmask = torch.zeros((64, 16), dtype=torch.bool)
                for q_i in range(64):
                    if (q_i + 1) // 4 > 0:
                        vmask[q_i, : (q_i + 1) // 4] = True
                l3_dots_i32 = torch.round(rdots * 1024.0).to(torch.int32)
                l3_scores_i32 = torch.clamp_min(l3_dots_i32, 0).sum(dim=-1)
                l3_valid_u8 = vmask.to(torch.uint8)
                lr["qsa_indexer"] = {
                    "per_head_le_zero_rate": round(float((rdots[vmask] <= 0.0).float().mean().item()), 6),
                    "all4_zero_block_rate": round(float((bscores[vmask] == 0.0).float().mean().item()), 6),
                }
                q_s, gt_s = torch.chunk(F.linear(x_a, get_w(f"{ps}.q_proj.weight")).reshape(1, 64, 24, 512), 2, dim=-1)
                q_s = _apply_rope(_rms_norm(q_s, get_w(f"{ps}.q_norm.weight")).transpose(1, 2), cos_r, sin_r, unsqueeze_dim=1)
                k_s = _apply_rope(_rms_norm(F.linear(x_a, get_w(f"{ps}.k_proj.weight")).reshape(1, 64, 2, 256), get_w(f"{ps}.k_norm.weight")).transpose(1, 2), cos_r, sin_r, unsqueeze_dim=1)
                v_s = F.linear(x_a, get_w(f"{ps}.v_proj.weight")).reshape(1, 64, 2, 256).transpose(1, 2)
                aw = (torch.matmul(q_s, k_s.repeat_interleave(12, dim=1).transpose(-1, -2)) * (256.0 ** -0.5)).masked_fill(torch.ones(64, 64, dtype=torch.bool).triu(1), float("-inf"))
                ao = torch.matmul(F.softmax(aw, dim=-1), v_s.repeat_interleave(12, dim=1)).transpose(1, 2).reshape(1, 64, 6144) * torch.sigmoid(gt_s.reshape(1, 64, 6144))
                out_a = F.linear(ao, get_w(f"{ps}.o_proj.weight"))

            h_ref = h_ref + (out_a.unsqueeze(-2) * inj_a.unsqueeze(-1)).flatten(-2)
            x_m, inj_m, lr["gr_mlp"] = _gr(h_ref, f"model.language_model.layers.{l_i}.mlp_hyper_connection")
            pm = f"model.language_model.layers.{l_i}.mlp"
            r_vals, r_idxs = torch.topk(F.softmax(F.linear(x_m.reshape(-1, hidden_q38), get_w(f"{pm}.gate.weight")).float(), dim=-1), 10, dim=-1)
            r_vals = r_vals / r_vals.sum(dim=-1, keepdim=True)
            uniq_e = sorted(set(int(e) for e in r_idxs.flatten().tolist()))
            exp_reqs = []
            for eid in uniq_e:
                for prj in ("gate_proj", "up_proj", "down_proj"):
                    exp_reqs += [(f"{fp8_repo}/{fp8_idx[f'{pm}.experts.{eid}.{prj}.weight']}", f"{pm}.experts.{eid}.{prj}.weight", None, None),
                                 (f"{fp8_repo}/{fp8_idx[f'{pm}.experts.{eid}.{prj}.weight_scale_inv']}", f"{pm}.experts.{eid}.{prj}.weight_scale_inv", None, None)]
            exp_t = fetcher.fetch_tensors_coalesced(exp_reqs, tag=f"L{l_i}_experts")
            x2 = x_m.reshape(-1, hidden_q38)
            mo = torch.zeros_like(x2)
            l0_gate_map: Dict[int, torch.Tensor] = {}
            for eid in uniq_e:
                ed: Dict[str, torch.Tensor] = {}
                for prj in ("gate_proj", "up_proj", "down_proj"):
                    ed[prj] = exp_t[(f"{fp8_repo}/{fp8_idx[f'{pm}.experts.{eid}.{prj}.weight']}", f"{pm}.experts.{eid}.{prj}.weight", None, None)] * exp_t[
                        (f"{fp8_repo}/{fp8_idx[f'{pm}.experts.{eid}.{prj}.weight_scale_inv']}", f"{pm}.experts.{eid}.{prj}.weight_scale_inv", None, None)
                    ].repeat_interleave(128, dim=0).repeat_interleave(128, dim=1)
                if l_i == 0:
                    l0_gate_map[eid] = ed["gate_proj"]
                ti, ki = torch.where(r_idxs == eid)
                xs = x2[ti]
                mo.index_add_(0, ti, F.linear(F.silu(F.linear(xs, ed["gate_proj"])) * F.linear(xs, ed["up_proj"]), ed["down_proj"]) * r_vals[ti, ki].unsqueeze(-1))
            sh_o = F.linear(F.silu(F.linear(x2, get_w(f"{pm}.shared_expert.gate_proj.weight"))) * F.linear(x2, get_w(f"{pm}.shared_expert.up_proj.weight")), get_w(f"{pm}.shared_expert.down_proj.weight"))
            mo = (mo + torch.sigmoid(F.linear(x2, get_w(f"{pm}.shared_expert_gate.weight"))) * sh_o).reshape_as(x_m)
            if l_i == 0:
                cnts: Dict[int, int] = defaultdict(int)
                for ti in range(64):
                    cnts[int(r_idxs[ti, 0].item())] += 1
                l0_eid = max(cnts.items(), key=lambda kv: kv[1])[0]
                l0_tok = next(ti for ti in range(64) if int(r_idxs[ti, 0].item()) == l0_eid)
                wf_g = l0_gate_map[l0_eid]
                _, nibs_o, exps_o = _quant_mxfp4_b32(wf_g)
                qn_pad = torch.zeros((1024, 4096), dtype=torch.uint8)
                qn_pad[:640, :2560] = nibs_o
                mn_e, mx_e = int(exps_o.min().item()), int(exps_o.max().item())
                if mx_e - mn_e > 24:
                    mn_e = mx_e - 24
                    exps_o = exps_o.clamp_min(mn_e)
                sc_pad = torch.zeros((1024, 128), dtype=torch.int64)
                sc_pad[:640, :80] = torch.bitwise_left_shift(torch.ones_like(exps_o, dtype=torch.int64), (exps_o - mn_e).to(torch.int64))
                x_act = x_m[0, l0_tok]
                x_sc = float(2 ** int(math.floor(math.log2(16384.0 / max(float(x_act.abs().max()), 1e-6)))))
                xin_pad = torch.zeros(4096, dtype=torch.int64)
                xin_pad[:2560] = torch.round(x_act.float() * x_sc).clamp(-32767, 32767).to(torch.int64)
                y_raw = ((e2m1_2x_int_lut[qn_pad.long()].reshape(1024, 128, 32) * xin_pad.reshape(1, 128, 32)).sum(dim=-1) * sc_pad).sum(dim=-1)
                l0_exp_wit = {"X_in": xin_pad.to(torch.int16), "Q_nibbles": qn_pad, "S_scales": sc_pad.to(torch.uint32), "Y_raw": y_raw, "min_exp": mn_e, "x_scale": x_sc}
            h_ref = h_ref + (mo.unsqueeze(-2) * inj_m.unsqueeze(-1)).flatten(-2)
            lr["unique_routed_experts"] = len(uniq_e)
            layer_reps[f"L{l_i}"] = lr

        report["layers"] = layer_reps
        if export_path is not None and l0_wy_wit is not None and l0_exp_wit is not None:
            hdr_b = struct.pack(
                "<8sIIIIIfIIIIIIIifIIII44s",
                b"QW38FNS1", 1, 48, 64, 256, 4096, float(l0_wy_wit["S_rhs"]),
                1024, 4096, 640, 2560, 32, int(l0_eid), int(l0_tok),
                int(l0_exp_wit["min_exp"]), float(l0_exp_wit["x_scale"]),
                64, 16, 4, 1024, b"\x00" * 44,
            )
            arrs = [
                l0_wy_wit["L_tilde"].numpy().astype("<i4"),
                l0_wy_wit["RHS"].numpy().astype("<i4"),
                l0_wy_wit["UW"].numpy().astype("<i4"),
                l0_wy_wit["R_rem"].numpy().astype("<u2"),
                l0_exp_wit["X_in"].numpy().astype("<i2"),
                l0_exp_wit["Q_nibbles"].numpy().astype("<u1"),
                l0_exp_wit["S_scales"].numpy().astype("<u4"),
                l0_exp_wit["Y_raw"].numpy().astype("<i8"),
                l3_scores_i32.numpy().astype("<i4"),
                l3_dots_i32.numpy().astype("<i4"),
                l3_valid_u8.numpy().astype("<u1"),
            ]
            with open(export_path, "wb") as fb:
                fb.write(hdr_b)
                for a in arrs:
                    fb.write(a.tobytes(order="C"))
            report["export_qwen38fn"] = {"path": export_path, "bytes": os.path.getsize(export_path)}
        report["network_mb"] = round(sum(fetcher.bytes_by_tag.values()) / (1024 * 1024), 2)
        report["elapsed_sec"] = round(time.time() - t0, 2)
    finally:
        shutil.rmtree(cache_dir, ignore_errors=True)
    return report


# ======================================================================================
# 8. Main Evaluation Pipeline
# ======================================================================================
def main() -> None:
    parser = argparse.ArgumentParser(description="Real Qwen3.5-0.8B Offline Audit + Qwen3.8-Flash-Next HTTP-Range Slice")
    parser.add_argument("--export", type=str, default=None, help="Optional binary audit bundle path (< 25 MB)")
    parser.add_argument("--device", type=str, default="auto", choices=["auto", "mps", "cpu"])
    parser.add_argument("--gen-tokens", type=int, default=32, help="Greedy new tokens per prompt (>= 24)")
    parser.add_argument("--qwen38fn-range", action="store_true", help="Also run HTTP-Range 4-layer Qwen3.8-Flash-Next-FP8 + NVFP4/MLX-4bit slice audit")
    parser.add_argument("--qwen38fn-only", action="store_true", help="Run ONLY the HTTP-Range 4-layer Qwen3.8-Flash-Next-FP8 slice audit")
    parser.add_argument("--export-qwen38fn", type=str, default=None, help="Optional QW38FNS1 binary bundle path (< 35 MB)")
    args = parser.parse_args()

    if args.qwen38fn_only:
        q38_only = run_qwen38fn_range_audit(export_path=args.export_qwen38fn)
        print(json.dumps(q38_only, indent=2))
        return

    t_start = time.time()
    if args.device == "auto":
        device = torch.device("mps" if torch.backends.mps.is_available() else "cpu")
    else:
        device = torch.device(args.device)

    print("=" * 92)
    print("REAL PRETRAINED Qwen/Qwen3.5-0.8B-Base (18 GDN + 6 GQA) — OFFLINE FIDELITY & AUDIT")
    print(f"Python {sys.version.split()[0]} | PyTorch {torch.__version__} | Device: {device} | MPS avail: {torch.backends.mps.is_available()}")
    print("=" * 92)

    # 1. Exact Tensor Census
    census = census_safetensors()
    print("\n[1] TENSOR CENSUS (Qwen/Qwen3.5-0.8B-Base safetensors):")
    print(f"  Total   : {census['total_tensors']:4d} tensors | {census['total_params']:13,d} params")
    print(f"  Text LM : {census['text_tensors']:4d} tensors | {census['text_params']:13,d} params "
          f"(24 layers: 18 GDN + 6 GQA; {census['text_linear_2d_total']} 2D linear/MLP mats = "
          f"{census['text_mlp_2d']} MLP + {census['text_attn_gdn_2d']} Attn/GDN)")
    print(f"  Vision  : {census['vision_tensors']:4d} tensors | {census['vision_params']:13,d} params")
    print(f"  MTP     : {census['mtp_tensors']:4d} tensors | {census['mtp_params']:13,d} params")

    tok = Tokenizer.from_file(str(TOKENIZER_PATH))
    base_weights = load_text_weights()
    t64_seqs = prepare_t64_sequences(tok)

    # 2. Verify FP32 Recurrent vs C=64 Chunkwise WY on Real Layer 0 Activations (T=64)
    print("\n[2] ARCHITECTURE EQUIVALENCE VERIFICATION (FP32 Recurrent vs C=64 Chunkwise WY + Cache):")
    fp32_bank = build_quantized_weight_bank(base_weights, "fp32", device)
    fp32_runner = Qwen35Runner(fp32_bank, "fp32", device)
    with torch.no_grad():
        seq0_ids = t64_seqs[0][1]
        x0 = fp32_bank["embed_tokens.weight"][torch.tensor(seq0_ids, device=device)].unsqueeze(0)
        h0 = rmsnorm_zero_centered(x0, fp32_bank["layers.0.input_layernorm.weight"])
        qkv0 = F.linear(h0, fp32_bank["layers.0.linear_attn.in_proj_qkv.weight"]).transpose(1, 2)
        qkv0 = F.silu(
            F.conv1d(F.pad(qkv0, (GDN_CONV_W - 1, 0)), fp32_bank["layers.0.linear_attn.conv1d.weight"], groups=6144)
        ).transpose(1, 2)
        q0, k0, v0 = [t.view(1, 64, GDN_H, GDN_D) for t in torch.split(qkv0, [2048, 2048, 2048], dim=-1)]
        b0 = F.linear(h0, fp32_bank["layers.0.linear_attn.in_proj_b.weight"])
        a0 = F.linear(h0, fp32_bank["layers.0.linear_attn.in_proj_a.weight"])
        beta0 = torch.sigmoid(b0.float())
        g0 = -fp32_bank["layers.0.linear_attn.A_log"].float().exp() * F.softplus(
            a0.float() + fp32_bank["layers.0.linear_attn.dt_bias"].float()
        )
        y_rec, s_rec = gdn_recurrent_fp32(q0, k0, v0, g0, beta0)
        y_chk, s_chk = gdn_chunkwise_wy_fp32(q0, k0, v0, g0, beta0, chunk_size=64)
        diff_y = float((y_rec - y_chk).abs().max().item())
        diff_s = float((s_rec - s_chk).abs().max().item())
        assert diff_y < 1e-5 and diff_s < 1e-5, f"Recurrent vs Chunk WY mismatch: y={diff_y}, s={diff_s}"

        # Verify cached decode step matches full-sequence prefill on 16-token prefix
        pref_full = fp32_runner.forward_prefill(seq0_ids[:16], return_cache=False)["logits"][-1]
        pref_15 = fp32_runner.forward_prefill(seq0_ids[:15], return_cache=True)
        step_16 = fp32_runner.decode_step(seq0_ids[15], pref_15["cache"])
        cache_diff = float((pref_full - step_16).abs().max().item())
        assert cache_diff < 1e-3, f"Cached decode mismatch: {cache_diff}"
    print(f"  L0 GDN FP32 recurrent vs C=64 WY max |dY| = {diff_y:.3e} (< 1e-5 PASS), max |dS| = {diff_s:.3e}")
    print(f"  24-layer cached decode vs full prefill max |dLogit| = {cache_diff:.3e} (< 1e-3 PASS)")

    # 3. Evaluate all 5 precision modes across 5 T=64 real sequences (320 positions / 315 targets)
    modes = [
        ("fp32", "FP32 (Reference)"),
        ("bf16", "BF16 (Native Pretrained)"),
        ("fp8_intwy", "FP8-E4M3 (All 186) + INT16 + IntWY(C=64)"),
        ("mixed_mxfp4_intwy", "Mixed MXFP4(72 MLP) + FP8(114 Attn/GDN) + INT16 + IntWY"),
        ("pure_mxfp4_intwy", "Pure MXFP4-E2M1 (All 186 Linear+MLP) + INT16 + IntWY"),
    ]
    all_logits: Dict[str, torch.Tensor] = {}
    all_bounds: Dict[str, torch.Tensor] = {}
    mode_wy_stats: Dict[str, Dict[str, Any]] = {}
    mode_clips: Dict[str, int] = {}
    gen_outputs: Dict[str, Dict[str, str]] = {}
    export_audit_payload: Optional[Dict[str, Any]] = None

    print(f"\n[3] RUNNING 5 PRECISION MODES ON 5 x T=64 REAL SEQUENCES (320 POSITIONS) + {args.gen_tokens}-TOKEN GENERATION:")
    for mode_key, mode_label in modes:
        t_m = time.time()
        bank = fp32_bank if mode_key == "fp32" else build_quantized_weight_bank(base_weights, mode_key, device)
        runner = fp32_runner if mode_key == "fp32" else Qwen35Runner(bank, mode_key, device)

        seq_logits = []
        seq_bounds = []
        wy_agg = {"max_abs_lhs": 0, "identity_errors": 0, "entries_checked": 0, "min_rem": M_WY, "max_rem": 0}
        clips_agg = 0

        for seq_name, ids in t64_seqs:
            capture_l0 = (mode_key == "mixed_mxfp4_intwy" and seq_name == "S5_ConfigSecret")
            res = runner.forward_prefill(ids, capture_layer0_audit=capture_l0, return_cache=False)
            seq_logits.append(res["logits"])
            seq_bounds.append(res["boundaries"])
            clips_agg += res["clip_count"]
            ws = res["wy_stats"]
            wy_agg["max_abs_lhs"] = max(wy_agg["max_abs_lhs"], ws["max_abs_lhs"])
            wy_agg["identity_errors"] += ws["identity_errors"]
            wy_agg["entries_checked"] += ws["entries_checked"]
            if ws["entries_checked"] > 0:
                wy_agg["min_rem"] = min(wy_agg["min_rem"], ws["min_rem"])
                wy_agg["max_rem"] = max(wy_agg["max_rem"], ws["max_rem"])
            if capture_l0:
                export_audit_payload = {
                    "prompt_ids": ids,
                    "boundaries_fp32": res["boundaries"],
                    "l0_audit": res["l0_audit"],
                }

        all_logits[mode_key] = torch.stack(seq_logits, dim=0)  # [5, 64, V]
        all_bounds[mode_key] = torch.stack(seq_bounds, dim=0)  # [5, 25, 64, 1024]
        mode_wy_stats[mode_key] = wy_agg
        mode_clips[mode_key] = clips_agg

        # Greedy multi-token generation on the 5 diverse prompts (skip duplicate FP32 to keep concise, run BF16 + all 3 quant)
        if mode_key != "fp32":
            gen_outputs[mode_key] = {}
            for pname, ptext in GEN_PROMPTS:
                _, gtxt = runner.generate_greedy(tok, ptext, max_new_tokens=args.gen_tokens)
                gen_outputs[mode_key][pname] = gtxt

        dt = time.time() - t_m
        wy_str = (
            f"WY errs={wy_agg['identity_errors']}/{wy_agg['entries_checked']:,}, "
            f"max|LHS|={wy_agg['max_abs_lhs']:,} ({P_BB_HALF / max(wy_agg['max_abs_lhs'], 1):.1f}x < P_BB/2), "
            f"Rem in [{wy_agg['min_rem']},{wy_agg['max_rem']}], INT16 clips={clips_agg}"
            if wy_agg["entries_checked"] > 0
            else "FP32/BF16 baseline"
        )
        print(f"  - {mode_label:<57s} ({dt:4.1f}s) | {wy_str}")

        if mode_key != "fp32":
            del bank, runner
            if device.type == "mps":
                torch.mps.empty_cache()

    # 4. Print Coherent Multi-Token Generation Table (5 prompts x BF16 / FP8 / Mixed-MXFP4 / Pure-MXFP4)
    print(f"\n[4] GREEDY MULTI-TOKEN GENERATION ({args.gen_tokens} NEW TOKENS ACROSS 5 DIVERSE REAL PROMPTS):")
    for pname, ptext in GEN_PROMPTS:
        print(f"\n  Prompt [{pname}]: {ptext!r}")
        for mkey, mshort in [
            ("bf16", "BF16       "),
            ("fp8_intwy", "FP8+IntWY  "),
            ("mixed_mxfp4_intwy", "Mix-MXFP4  "),
            ("pure_mxfp4_intwy", "Pure-MXFP4 "),
        ]:
            out_clean = gen_outputs[mkey][pname].replace("\n", "\\n")
            print(f"    {mshort} -> {out_clean!r}")

    # Verify P5 actually echoed the secret API key prefix under BF16 & quantized modes
    p5_bf16 = gen_outputs["bf16"]["P5_Secret"]
    assert "sk-proj-" in p5_bf16, f"P5 BF16 did not emit sk-proj-: {p5_bf16!r}"

    # 5. Quantitative Fidelity Summary (248,320-vocab logits + Per-Layer L0..L23 CosSim & SNR)
    token_seqs = [ids for _, ids in t64_seqs]
    metrics_vs_bf16: Dict[str, Dict[str, float]] = {}
    metrics_vs_fp32: Dict[str, Dict[str, float]] = {}
    layer_fid_vs_bf16: Dict[str, Tuple[List[float], List[float]]] = {}
    layer_fid_vs_fp32: Dict[str, Tuple[List[float], List[float]]] = {}

    for mkey, _ in modes:
        metrics_vs_bf16[mkey] = compute_logit_metrics(all_logits["bf16"], all_logits[mkey], token_seqs)
        metrics_vs_fp32[mkey] = compute_logit_metrics(all_logits["fp32"], all_logits[mkey], token_seqs)
        layer_fid_vs_bf16[mkey] = compute_layer_fidelity(all_bounds["bf16"], all_bounds[mkey])
        layer_fid_vs_fp32[mkey] = compute_layer_fidelity(all_bounds["fp32"], all_bounds[mkey])

    print("\n[5] FINAL 248,320-VOCAB LOGIT & PERPLEXITY BENCHMARK (5 x T=64 = 320 POSITIONS, 315 TARGETS):")
    hdr = (
        f"  {'Mode':<22s} | {'NLL':>6s} | {'PPL':>6s} | "
        f"{'KL vs BF16':>10s} | {'KL vs FP32':>10s} | "
        f"{'Top1% (BF16)':>12s} | {'T1inT5%':>7s} | {'T5Ov%':>6s} | "
        f"{'L23 Cos':>8s} | {'L23 SNR':>8s}"
    )
    print(hdr)
    print("  " + "-" * (len(hdr) - 2))
    for mkey, _ in modes:
        mb = metrics_vs_bf16[mkey]
        mf = metrics_vs_fp32[mkey]
        l23_cos = layer_fid_vs_bf16[mkey][0][-1]
        l23_snr = layer_fid_vs_bf16[mkey][1][-1]
        snr_str = "   inf  " if mkey == "bf16" else f"{l23_snr:6.2f}dB"
        print(
            f"  {mkey:<22s} | {mb['nll_nats']:6.4f} | {mb['perplexity']:6.3f} | "
            f"{mb['kl_mean_nats']:10.5f} | {mf['kl_mean_nats']:10.5f} | "
            f"{mb['top1_agree_pct']:11.2f}% | {mb['top1_in_top5_pct']:6.2f}% | {mb['top5_overlap_pct']:5.2f}% | "
            f"{l23_cos:8.6f} | {snr_str}"
        )

    print("\n[6] PER-LAYER (L0..L23) HIDDEN-STATE FIDELITY VS BF16 REFERENCE (320 TOKEN VECTORS/LAYER):")
    print(
        f"  {'Layer':<8s} | {'Type':<4s} | "
        f"{'FP8+IntWY Cos / SNR':>21s} | {'Mix-MXFP4 Cos / SNR':>21s} | {'Pure-MXFP4 Cos / SNR':>21s}"
    )
    print("  " + "-" * 86)
    for l in range(NUM_LAYERS):
        ltype = "GQA" if (l + 1) % 4 == 0 else "GDN"
        c_fp8, s_fp8 = layer_fid_vs_bf16["fp8_intwy"][0][l], layer_fid_vs_bf16["fp8_intwy"][1][l]
        c_mix, s_mix = layer_fid_vs_bf16["mixed_mxfp4_intwy"][0][l], layer_fid_vs_bf16["mixed_mxfp4_intwy"][1][l]
        c_pur, s_pur = layer_fid_vs_bf16["pure_mxfp4_intwy"][0][l], layer_fid_vs_bf16["pure_mxfp4_intwy"][1][l]
        print(
            f"  L{l:<7d} | {ltype:<4s} | "
            f"{c_fp8:8.6f} / {s_fp8:6.2f} dB | {c_mix:8.6f} / {s_mix:6.2f} dB | {c_pur:8.6f} / {s_pur:6.2f} dB"
        )

    # 7. Optional Binary Bundle Export & Round-Trip Verification
    export_summary = None
    roundtrip_summary = None
    if args.export:
        assert export_audit_payload is not None
        exp_path = Path(args.export)
        p5_gen_bytes = gen_outputs["mixed_mxfp4_intwy"]["P5_Secret"].encode("utf-8")
        if b"sk-proj-" not in p5_gen_bytes:
            p5_gen_bytes = gen_outputs["bf16"]["P5_Secret"].encode("utf-8")
        export_summary = export_audit_bundle(
            export_path=exp_path,
            prompt_ids=export_audit_payload["prompt_ids"],
            p5_gen_bytes=p5_gen_bytes,
            boundaries_fp32=export_audit_payload["boundaries_fp32"],
            l0_audit=export_audit_payload["l0_audit"],
            base_weights=base_weights,
        )
        roundtrip_summary = verify_export_bundle_roundtrip(exp_path)
        print(f"\n[7] BINARY AUDIT BUNDLE EXPORTED & ROUND-TRIP VERIFIED:")
        print(f"  Path       : {export_summary['path']}")
        print(f"  Size       : {export_summary['size_bytes']:,} bytes ({export_summary['size_mb']:.3f} MiB < 25 MB PASS)")
        print(f"  L0 WY      : {roundtrip_summary['wy_entries_verified']:,} entries, 0 errors over Z, "
              f"max|LHS| = {roundtrip_summary['wy_max_abs_lhs']:,} "
              f"({P_BB_HALF / max(roundtrip_summary['wy_max_abs_lhs'], 1):.1f}x < P_BB/2)")
        print(f"  P5 Gen     : {roundtrip_summary['gen_excerpt']!r}")
        for m in export_summary["matrices"]:
            print(
                f"  L0 MXFP4   : {m['name']:<22s} [{m['orig_rows']}->{m['J_pad']} x {m['in_dim']}] "
                f"e_floor={m['e_floor']} max_S={m['max_scale']:3d} "
                f"max|Y_raw|={m['max_abs_y_raw']:10,d} ({m['p_bb_half_margin']:6.1f}x < P_BB/2) "
                f"fp_diff={m['max_fp_diff']:.2e}"
            )

    q38_range_summary = None
    if args.qwen38fn_range:
        print("\n[7b] RUNNING HTTP-RANGE 4-LAYER Qwen/Qwen3.8-Flash-Next-FP8 + NVFP4/MLX-4BIT SLICE AUDIT:")
        q38_range_summary = run_qwen38fn_range_audit(export_path=args.export_qwen38fn)
        print(f"  Completed Qwen3.8-Flash-Next 4-layer slice in {q38_range_summary['elapsed_sec']}s ({q38_range_summary['network_mb']} MiB fetched).")

    summary_json = {
        "census": census,
        "arch_checks": {
            "l0_rec_vs_chunk_wy_max_dy": diff_y,
            "l0_rec_vs_chunk_wy_max_ds": diff_s,
            "cached_decode_vs_prefill_max_dlogit": cache_diff,
        },
        "wy_stats": mode_wy_stats,
        "int16_clips": mode_clips,
        "metrics_vs_bf16": metrics_vs_bf16,
        "metrics_vs_fp32": metrics_vs_fp32,
        "export": export_summary,
        "roundtrip": roundtrip_summary,
        "qwen38fn_range": q38_range_summary,
        "elapsed_sec": round(time.time() - t_start, 2),
    }
    print("\n[8] JSON SUMMARY:")
    print(json.dumps(summary_json, indent=2))
    print(f"\nALL CHECKS PASSED in {summary_json['elapsed_sec']}s.")


if __name__ == "__main__":
    main()
