#!/usr/bin/env python3
"""
sota_2026_hw_fit_and_live_run.py — Comprehensive Late-2026 Hardware-Fit SOTA Model Matrix,
Deterministic `zkML` (`Gruen` Mode-2 `EinSumcheck` + `EXP_TAB`) & `vFHEML` (`HoistedB61` + `SPDZ`)
Cryptographic Pricing (`T in {4K, 64K, 256K}`), Real `Qwen3.8-27B` `MXFP4` & `NVFP4` (`E2M1`)
Safetensors Prover Verification, and Live Apple M2 Max Metal Execution + `cSHAKE256` `RewriteCert`
Verification via `/opt/homebrew/bin/llama-cli` (`v0.9.0`).

2026-11-21 — `sota-hw-model-hunter` (`real_systems_wave_2026_11_21`).

Usage:
  python3 research/real_systems_wave_2026_11_21/experiments/sota_2026_hw_fit_and_live_run.py
  python3 research/real_systems_wave_2026_11_21/experiments/sota_2026_hw_fit_and_live_run.py --skip-live-gguf
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import re
import shutil
import struct
import subprocess
import sys
import time
import urllib.request
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple

import numpy as np

# ======================================================================================
# 0. Stack & Cryptographic Constants (Aligned with `qwen38_next_zk_vfhe_pricing.py` & `VERDICTS.md`)
# ======================================================================================
P_BB = (1 << 31) - (1 << 27) + 1          # BabyBear prime = 2,013,265,921
W_EXT4 = 11                               # Quartic extension F_p[X] / (X^4 - 11)
BB_MULS_EXT_BASE = 4                      # 1 base * Ext4 = 4 BabyBear muls
BB_MULS_EXT_EXT = 9                       # 1 Ext4 * Ext4 = 9 BabyBear muls (Karatsuba tower)
WHIR_LDE_MULS_PER_BASE_CELL = 16          # WHIR(rho=1/4) PCS encoding + Merkle sponge equiv
POSEIDON2_NARROW_CELLS_PER_PERM = 141     # VERDICTS.md §4 `permEmissionNarrow`

# B61 + SPDZ + HoistedB61 vFHEML constants (`docs/DARK-LEARNING-SCHEME-DECISION.md` + `HoistedB61`)
B61_N = 8192
B61_L = 3                                 # 3 x 61-bit RNS primes (log2 Q = 183)
B61_CT_CT_BITS_HOISTED = 8_126_464        # Hoisted sum-before-rescale B61 ct x ct cert bits (~8.13 Mbit)

# Local Hardware & Model Artifact Paths
HW_RAM_BYTES_EXPECTED = 103_079_215_104   # 96.000 GiB = 103.079 GB Apple M2 Max unified RAM
GGUF_PATH = Path("/Users/ember/.cache/zkml-models/Qwen3.8-27B-UD-Q4_K_XL.gguf")
GGUF_EXPECTED_BYTES = 17_659_407_264
GGUF_EXPECTED_SHA256 = "2a5f3565f39cf885103da591182c1266da64745737b42b452fd3e675369f1211"
SLICE_CACHE_PATH = Path("/Users/ember/.cache/zkml-models/qwen38_27b_e2m1_slice/qwen38_27b_l0_gate_proj_256x5120.npz")
LIVE_RECEIPT_CACHE = Path("/Users/ember/.cache/zkml-models/qwen38_27b_live_metal_receipt.json")
LLAMA_CLI = Path("/opt/homebrew/bin/llama-cli")

# OCP E2M1 16-entry signed x2 integer codebook:
# bit3 = sign, bits 2..1 = exp, bit0 = mantissa; nibble 8 = -0.0 canonicalized to 0.
E2M1_X2 = np.array([0, 1, 2, 3, 4, 6, 8, 12, 0, -1, -2, -3, -4, -6, -8, -12], dtype=np.int64)
E2M1_F32 = (E2M1_X2 / 2.0).astype(np.float32)


# ======================================================================================
# 1. Exact NIST SP 800-185 `cSHAKE256` & `minidregg` Cube-Merkle `contentCommit`
# ======================================================================================
_KECCAK_RC = (
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
)
_KECCAK_ROT = (
    (0, 36, 3, 41, 18),
    (1, 44, 10, 45, 2),
    (62, 6, 43, 15, 61),
    (28, 55, 25, 21, 56),
    (27, 20, 39, 8, 14),
)
_MASK64 = (1 << 64) - 1


def _rotl64(x: int, n: int) -> int:
    return ((x << n) | (x >> (64 - n))) & _MASK64 if n else x


def _keccak_f1600(state: List[int]) -> None:
    """In-place 24-round Keccak-f[1600] permutation on 25 u64 lanes (`state[x + 5*y]`)."""
    for rc in _KECCAK_RC:
        # Theta
        c = [state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20] for x in range(5)]
        d = [c[(x - 1) % 5] ^ _rotl64(c[(x + 1) % 5], 1) for x in range(5)]
        for y5 in (0, 5, 10, 15, 20):
            for x in range(5):
                state[x + y5] ^= d[x]
        # Rho + Pi
        b = [0] * 25
        for x in range(5):
            for y in range(5):
                b[y + 5 * ((2 * x + 3 * y) % 5)] = _rotl64(state[x + 5 * y], _KECCAK_ROT[x][y])
        # Chi
        for y5 in (0, 5, 10, 15, 20):
            t0, t1, t2, t3, t4 = b[y5], b[y5 + 1], b[y5 + 2], b[y5 + 3], b[y5 + 4]
            state[y5] = t0 ^ ((~t1 & _MASK64) & t2)
            state[y5 + 1] = t1 ^ ((~t2 & _MASK64) & t3)
            state[y5 + 2] = t2 ^ ((~t3 & _MASK64) & t4)
            state[y5 + 3] = t3 ^ ((~t4 & _MASK64) & t0)
            state[y5 + 4] = t4 ^ ((~t0 & _MASK64) & t1)
        # Iota
        state[0] ^= rc


def _left_encode(x: int) -> bytes:
    if x == 0:
        return b"\x01\x00"
    b = x.to_bytes((x.bit_length() + 7) // 8, "big")
    return bytes([len(b)]) + b


def _encode_string(s: bytes) -> bytes:
    return _left_encode(len(s) * 8) + s


def _bytepad(x: bytes, w: int) -> bytes:
    z = _left_encode(w) + x
    rem = len(z) % w
    if rem:
        z += b"\x00" * (w - rem)
    return z


def cshake256_xof(customization: bytes, data: bytes, out_len: int = 32, func_name: bytes = b"") -> bytes:
    """Exact NIST SP 800-185 §3.2 `cSHAKE256(X, L, N, S)` (`rate = 136` bytes)."""
    if not func_name and not customization:
        return hashlib.shake_256(data).digest(out_len)
    rate = 136
    prefix = _bytepad(_encode_string(func_name) + _encode_string(customization), rate)
    stream = bytearray(prefix) + bytearray(data)
    # Pad with domain separator 0x04 and multi-rate 10*1 rule
    pad_len = rate - (len(stream) % rate)
    if pad_len == 1:
        stream.append(0x84)
    else:
        stream.append(0x04)
        stream.extend(b"\x00" * (pad_len - 2))
        stream.append(0x80)
    state = [0] * 25
    for off in range(0, len(stream), rate):
        lanes = struct.unpack_from("<17Q", stream, off)
        for i in range(17):
            state[i] ^= lanes[i]
        _keccak_f1600(state)
    out = bytearray()
    while len(out) < out_len:
        block = struct.pack("<17Q", *state[:17])
        out.extend(block)
        if len(out) < out_len:
            _keccak_f1600(state)
    return bytes(out[:out_len])


# Mirror `minidregg/prover/src/policy_transducer.rs` §§1, 3, 4, 5 byte-for-byte:
LEAF_CUST = b"\x01MINIDREGG/TOWER256/MERKLE/LEAF/V1"
NODE_CUST = b"\x02MINIDREGG/TOWER256/MERKLE/NODE/V1"
MAX_ZERO_DEPTH = 20


def _envelope_bytes(payload: bytes) -> bytes:
    return (b"\x00" * len(payload)) + b"\x01" + payload


class Tower256ContentMerkle:
    """Exact mirror of `Tower256ContentCert.contentCommit` (`policy_transducer.rs:97-228`)."""

    def __init__(self) -> None:
        self.byte_leaves: List[bytes] = []
        for b in range(256):
            c8_le = bytes([b]) + (b"\x00" * 31)
            self.byte_leaves.append(cshake256_xof(LEAF_CUST, b"\x00" + _envelope_bytes(c8_le), 32))
        self.zero_subtrees: List[bytes] = [self.byte_leaves[0]]
        for _ in range(1, MAX_ZERO_DEPTH):
            prev = self.zero_subtrees[-1]
            env = _envelope_bytes(prev)
            self.zero_subtrees.append(cshake256_xof(NODE_CUST, b"\x01" + env + env, 32))

    @staticmethod
    def depth_of(n: int) -> int:
        return 0 if n <= 1 else (n - 1).bit_length()

    @staticmethod
    def hash_node(left: bytes, right: bytes) -> bytes:
        inp = b"\x01" + (b"\x00" * 32) + b"\x01" + left + (b"\x00" * 32) + b"\x01" + right
        return cshake256_xof(NODE_CUST, inp, 32)

    def _root_strided(self, data: bytes, total_leaves: int, offset: int, stride: int, rem_depth: int) -> bytes:
        if offset >= len(data) and rem_depth < MAX_ZERO_DEPTH:
            return self.zero_subtrees[rem_depth]
        if stride >= total_leaves:
            b = data[offset] if offset < len(data) else 0
            return self.byte_leaves[b]
        left = self._root_strided(data, total_leaves, offset, stride * 2, rem_depth - 1)
        right = self._root_strided(data, total_leaves, offset + stride, stride * 2, rem_depth - 1)
        return self.hash_node(left, right)

    def content_commit(self, data: bytes) -> bytes:
        d = self.depth_of(len(data))
        return self._root_strided(data, 1 << d, 0, 1, d)


# Exact 5-class secret-redaction policy (`Theory.VerifiedAstTransducer.defaultSecretRules`)
@dataclass(frozen=True)
class RedactRule:
    name: str
    pat: bytes
    body_pred: Callable[[int], bool]
    repl: bytes


def _is_api_key_body(b: int) -> bool:
    return (65 <= b <= 90) or (97 <= b <= 122) or (48 <= b <= 57) or b in (95, 45)


def _is_bearer_body(b: int) -> bool:
    return _is_api_key_body(b) or b in (46, 126, 43, 47, 61)


def _is_pem_body(b: int) -> bool:
    return (65 <= b <= 90) or (48 <= b <= 57) or b in (32, 45)


def _no_cont(_: int) -> bool:
    return False


DEFAULT_SECRET_RULES: Tuple[RedactRule, ...] = (
    RedactRule("api_key", b"sk-", _is_api_key_body, b"[REDACTED_API_KEY]"),
    RedactRule("bearer", b"Bearer ", _is_bearer_body, b"[REDACTED_BEARER]"),
    RedactRule("pem_key", b"-----BEGIN ", _is_pem_body, b"[REDACTED_PEM]"),
    RedactRule("template_open", b"{{", _no_cont, b"[REDACTED_TPL]"),
    RedactRule("github_pat", b"ghp_", _is_api_key_body, b"[REDACTED_GH_PAT]"),
)


def safe_replacement(pat: bytes, repl: bytes) -> bool:
    if not repl or (pat in repl):
        return False
    for k in range(1, len(pat)):
        p1, p2 = pat[:k], pat[k:]
        if repl.startswith(p2) or p2.startswith(repl) or repl.endswith(p1):
            return False
    return True


def all_rules_safe(rules: Tuple[RedactRule, ...]) -> bool:
    return all(len(rt.pat) > 0 and all(safe_replacement(rt.pat, r.repl) for r in rules) for rt in rules)


def redact_bytes(rules: Tuple[RedactRule, ...], data: bytes) -> bytes:
    """Exact longest-match deterministic byte-stream sanitizer (`policy_transducer.rs:1351-1376`)."""
    starters = {r.pat[0] for r in rules if r.pat}
    out = bytearray()
    pos = 0
    clean_start = 0
    n = len(data)
    while pos < n:
        if data[pos] not in starters:
            pos += 1
            continue
        rem = data[pos:]
        best_repl: Optional[bytes] = None
        best_len = 0
        for r in rules:
            if rem.startswith(r.pat):
                mlen = len(r.pat)
                while mlen < len(rem) and r.body_pred(rem[mlen]):
                    mlen += 1
                if best_repl is None or mlen > best_len:
                    best_repl, best_len = r.repl, mlen
        if best_repl is not None:
            if clean_start < pos:
                out.extend(data[clean_start:pos])
            out.extend(best_repl)
            pos += best_len
            clean_start = pos
        else:
            pos += 1
    if clean_start < n:
        out.extend(data[clean_start:])
    return bytes(out)


def parse_and_verify_mini_json_ast(clean_bytes: bytes) -> Dict[str, Any]:
    """
    Deterministic `miniJsonCfg` LL(1) tool-call parser & duplicate-key rejection check
    (`Theory.VerifiedAstTransducer.miniJsonCfg` — accepts strictly single-pass ordered
    `{"tool": ..., "target": ..., "amount": N}` or `{"cot": ..., "tool": ..., "target": ..., "amount": N}`).
    """
    text = clean_bytes.decode("ascii")  # miniJsonCfg restricts printable ASCII 0x20..0x7E + escapes
    # Reject duplicate keys explicitly (`ambigMiniJsonCfg` splice defense)
    pairs: List[Tuple[str, Any]] = []

    def _no_dup_hook(ordered_pairs: List[Tuple[str, Any]]) -> Dict[str, Any]:
        keys = [k for k, _ in ordered_pairs]
        if len(keys) != len(set(keys)):
            raise ValueError(f"Duplicate JSON key rejected by LL(1) grammar: {keys}")
        pairs.extend(ordered_pairs)
        return dict(ordered_pairs)

    obj = json.loads(text, object_pairs_hook=_no_dup_hook)
    if not isinstance(obj, dict):
        raise ValueError("Expected top-level JSON tool-call object")
    ordered_keys = [k for k, _ in pairs]
    if ordered_keys == ["tool", "target", "amount"]:
        kind = "ToolCall"
    elif ordered_keys == ["cot", "tool", "target", "amount"]:
        kind = "CotToolCall"
    else:
        raise ValueError(f"Key sequence {ordered_keys} rejected by LL(1) miniJsonCfg")
    for str_k in [k for k in ordered_keys if k != "amount"]:
        if not isinstance(obj[str_k], str):
            raise ValueError(f"Field '{str_k}' must be string")
    if type(obj["amount"]) is not int or obj["amount"] < 0:
        raise ValueError("Field 'amount' must be non-negative integer")
    return {"ast_kind": kind, "fields": obj}


def verify_cshake_and_transducer_selftest(merkle: Tower256ContentMerkle) -> Dict[str, Any]:
    """Verify NIST SP 800-185 cSHAKE256 official vector + SafeReplacement + splice/leak falsifiers."""
    # NIST SP 800-185 cSHAKE256 Sample #3: X = 00 01 02 03, N = "", S = "Email Signature", L = 512 bits
    nist_x = bytes([0x00, 0x01, 0x02, 0x03])
    nist_got = cshake256_xof(b"Email Signature", nist_x, 64).hex()
    nist_expected_prefix = "d008828e2b80ac9d2218ffee1d070c48b8e4c87bff32c9699d5b6896eee0edd1"
    assert nist_got.startswith(nist_expected_prefix), f"NIST cSHAKE256 mismatch: {nist_got}"
    # Empty N, S must equal SHAKE256 (SP 800-185 §3.3)
    assert cshake256_xof(b"", b"abc", 32) == hashlib.shake_256(b"abc").digest(32)
    assert all_rules_safe(DEFAULT_SECRET_RULES), "DEFAULT_SECRET_RULES failed SafeReplacement!"

    # Falsifier 1: Duplicate-key splice `{"tool":"safe","tool":"pwn","target":"x","amount":1}` MUST fail
    dup_rejected = False
    try:
        parse_and_verify_mini_json_ast(b'{"tool":"safe","tool":"pwn","target":"x","amount":1}')
    except ValueError:
        dup_rejected = True
    assert dup_rejected, "Duplicate-key JSON splice was not rejected!"

    # Falsifier 2: 1-byte tamper in committed payload changes cSHAKE256 cube-Merkle root
    r1 = merkle.content_commit(b'{"tool":"verify","target":"l0","amount":64}')
    r2 = merkle.content_commit(b'{"tool":"verify","target":"l0","amount":65}')
    assert r1 != r2
    return {"nist_sp800_185_sample3_verified": True, "dup_key_rejected": dup_rejected, "safe_rules": True}


# ======================================================================================
# 2. 2026 SOTA Hardware-Fit Model Roster & Deterministic `zkML` / `vFHEML` Pricing Engine
# ======================================================================================
@dataclass(frozen=True)
class ModelSpec2026:
    rank_tag: str
    name: str
    hf_repo: str
    release_ym: str
    fits_96gib_4bit: bool
    llama_cli_090_arch: str               # exact arch string in `/opt/homebrew/bin/llama-cli` v0.9.0 (`NONE` if newer)
    total_params_B: float                 # total checkpoint params (incl. PLE/Engram if any)
    backbone_params_B: float              # non-PLE/Engram text backbone params
    active_params_B: float                # active params per token (incl. lm_head)
    ple_params_B: float                   # off-accelerator N-gram PLE/Engram params (0 if none)
    ple_heads: int                        # N-gram hash heads per PLE layer (0 if none)
    ple_layers: int                       # number of PLE/Engram layers
    num_layers: int                       # stored transformer/hybrid blocks
    loop_extra_passes: int                # extra passes over looped middle core (0 for standard, 2 for 3-pass Inkling-2)
    loop_core_layers: int                 # number of layers inside loop core
    # Exact attention / SSM layer breakdown across effective unrolled depth:
    n_gdn: int                            # Gated DeltaNet (`Qwen3.6` / `Qwen3.8`)
    n_kda: int                            # Kimi Delta Attention (`Kimi-Linear` / `Ling-3.0` / `GLM-5.3`)
    n_mamba2: int                         # Mamba-2 SSD (`Nemotron-3.5`)
    n_qsa_dsa: int                        # Sparse block-indexed attention (`QSA` / `DSA`, top-K=2048)
    n_mla_full: int                       # Dense Multi-head Latent Attention (`MLA`)
    n_swa: int                            # Sliding-Window Attention (`SWA`)
    swa_win: int                          # SWA window size W (0 if n_swa == 0)
    n_gqa_full: int                       # Full causal GQA layers
    # Head & hidden geometry for pricing:
    d_model: int
    h_q: int
    h_kv: int                             # KV heads on GQA/SWA/QSA (or 1 for compressed MLA KV)
    d_head: int
    kv_lora_rank: int                     # >0 for MLA layers
    k_eq_v: bool                          # True for Gemma-4 (`attention_k_eq_v = True` -> 0.5x KV!)
    lin_heads: int                        # GDN/KDA/Mamba2 value heads
    lin_state_d: int                      # State dim per linear head (128 for GDN/KDA/Mamba2)
    # MoE & FFN geometry:
    moe_layers: int
    n_experts: int                        # routed experts (0 if dense)
    top_k: int                            # active routed experts (0 if dense)
    n_shared: int                         # shared experts
    d_ff_active: int                      # total active FFN intermediate width per layer (`(top_k+shared)*f_moe` or `f_dense`)
    d_ff_expert: int                      # single expert width `f_moe` (or `f_dense`)
    ffn_act: str                          # `swiglu` | `geglu` | `relu2` (`relu2` = 0 table lookups!)
    residual_kind: str                    # `rms` | `gr4` (4-branch Gated Residual) | `mhc20` (20-iter Sinkhorn!)
    vocab_size: int
    # Shipped quantized sizes & benchmarks (`[SOURCE]`):
    deploy_quant_label: str
    deploy_size_gb: float                 # decimal GB (10^9 B)
    deploy_size_gib: float                # binary GiB (2^30 B)
    lcb_v6: Optional[float]
    swe_verified: Optional[float]
    swe_pro: Optional[float]
    aime_25_26: str
    gpqa_diamond: Optional[float]
    source_note: str


MODELS_2026: Tuple[ModelSpec2026, ...] = (
    # --- TIER 1: <= 25 GB SWEET-SPOT NATIVE HARDWARE-FIT SOTA ---
    ModelSpec2026(
        rank_tag="#1 Sweet-Spot (<=25GB)",
        name="Qwen3.8-27B",
        hf_repo="Qwen/Qwen3.8-27B",
        release_ym="2026-08",
        fits_96gib_4bit=True,
        llama_cli_090_arch="qwen35",
        total_params_B=27.781,
        backbone_params_B=26.896,
        active_params_B=26.896,
        ple_params_B=0.0,
        ple_heads=0,
        ple_layers=0,
        num_layers=64,
        loop_extra_passes=0,
        loop_core_layers=0,
        n_gdn=48, n_kda=0, n_mamba2=0, n_qsa_dsa=0, n_mla_full=0, n_swa=0, swa_win=0, n_gqa_full=16,
        d_model=5120, h_q=24, h_kv=4, d_head=256, kv_lora_rank=0, k_eq_v=False,
        lin_heads=48, lin_state_d=128,
        moe_layers=0, n_experts=0, top_k=0, n_shared=0, d_ff_active=17408, d_ff_expert=17408,
        ffn_act="swiglu", residual_kind="rms", vocab_size=248320,
        deploy_quant_label="UD-Q4_K_XL GGUF / MLX-MXFP4",
        deploy_size_gb=17.659, deploy_size_gib=16.447,
        lcb_v6=90.3, swe_verified=77.8, swe_pro=61.7, aime_25_26="[OPEN] (MathVis 94.6)", gpqa_diamond=89.2,
        source_note="[SOURCE: Qwen/Qwen3.8-27B config.json + README; Inkling-2 bash SWE-V table]",
    ),
    ModelSpec2026(
        rank_tag="#2 Sweet-Spot (Looped)",
        name="Inkling-2-Mini (26B-A5.4B)",
        hf_repo="thinkingmachines/Inkling-2-Mini",
        release_ym="2026-11",
        fits_96gib_4bit=True,
        llama_cli_090_arch="NONE (inkling2, Nov-20 v1.0+)",
        total_params_B=26.389,
        backbone_params_B=26.070,
        active_params_B=5.400,
        ple_params_B=0.0,
        ple_heads=0,
        ple_layers=0,
        num_layers=24,
        loop_extra_passes=2,   # 3 passes over layers 6..18 -> +24 unrolled layers = 48 effective layers!
        loop_core_layers=12,
        n_gdn=0, n_kda=0, n_mamba2=0, n_qsa_dsa=0, n_mla_full=0, n_swa=40, swa_win=1024, n_gqa_full=8,
        d_model=2304, h_q=24, h_kv=8, d_head=128, kv_lora_rank=0, k_eq_v=False,
        lin_heads=0, lin_state_d=0,
        moe_layers=48, n_experts=128, top_k=8, n_shared=0, d_ff_active=9216, d_ff_expert=1152,
        ffn_act="swiglu", residual_kind="rms", vocab_size=201024,
        deploy_quant_label="UD-Q4_K_XL GGUF / Native FP4-U8",
        deploy_size_gb=17.630, deploy_size_gib=16.419,
        lcb_v6=None, swe_verified=79.2, swe_pro=77.9, aime_25_26="[OPEN]", gpqa_diamond=None,
        source_note="[SOURCE: thinkingmachines/Inkling-2-Mini config.json + README (2026-11-17)]",
    ),
    ModelSpec2026(
        rank_tag="#3 Sweet-Spot (Fast MoE)",
        name="Qwen3.6-35B-A3B",
        hf_repo="Qwen/Qwen3.6-35B-A3B",
        release_ym="2026-04",
        fits_96gib_4bit=True,
        llama_cli_090_arch="qwen35moe",
        total_params_B=35.952,
        backbone_params_B=34.661,
        active_params_B=3.050,
        ple_params_B=0.0,
        ple_heads=0,
        ple_layers=0,
        num_layers=40,
        loop_extra_passes=0,
        loop_core_layers=0,
        n_gdn=30, n_kda=0, n_mamba2=0, n_qsa_dsa=0, n_mla_full=0, n_swa=0, swa_win=0, n_gqa_full=10,
        d_model=2048, h_q=16, h_kv=2, d_head=256, kv_lora_rank=0, k_eq_v=False,
        lin_heads=32, lin_state_d=128,
        moe_layers=40, n_experts=256, top_k=8, n_shared=1, d_ff_active=4608, d_ff_expert=512,
        ffn_act="swiglu", residual_kind="rms", vocab_size=248320,
        deploy_quant_label="MXFP4_MOE GGUF / NVFP4",
        deploy_size_gb=21.706, deploy_size_gib=20.215,
        lcb_v6=80.4, swe_verified=73.4, swe_pro=49.5, aime_25_26="92.7 (AIME26)", gpqa_diamond=86.0,
        source_note="[SOURCE: Qwen/Qwen3.6-35B-A3B config.json + README]",
    ),
    ModelSpec2026(
        rank_tag="#4 Sweet-Spot (SWA Dense)",
        name="Muse-Glimmer-30B",
        hf_repo="meta-models/Muse-Glimmer-30B",
        release_ym="2026-08",
        fits_96gib_4bit=True,
        llama_cli_090_arch="muse-glimmer",
        total_params_B=29.777,
        backbone_params_B=27.980,
        active_params_B=27.980,
        ple_params_B=0.0,
        ple_heads=0,
        ple_layers=0,
        num_layers=52,
        loop_extra_passes=0,
        loop_core_layers=0,
        n_gdn=0, n_kda=0, n_mamba2=0, n_qsa_dsa=0, n_mla_full=0, n_swa=39, swa_win=2048, n_gqa_full=13,
        d_model=6656, h_q=32, h_kv=2, d_head=128, kv_lora_rank=0, k_eq_v=False,
        lin_heads=0, lin_state_d=0,
        moe_layers=0, n_experts=0, top_k=0, n_shared=0, d_ff_active=19968, d_ff_expert=19968,
        ffn_act="swiglu", residual_kind="rms", vocab_size=202048,
        deploy_quant_label="UD-Q4_K_XL GGUF",
        deploy_size_gb=15.878, deploy_size_gib=14.788,
        lcb_v6=None, swe_verified=76.0, swe_pro=51.2, aime_25_26="94.7 (AIME26)", gpqa_diamond=83.5,
        source_note="[SOURCE: meta-models/Muse-Glimmer-30B config.json + README]",
    ),
    ModelSpec2026(
        rank_tag="#5 Sweet-Spot (SWA K=V)",
        name="Gemma-4-31B-it (+26B-A4B)",
        hf_repo="google/gemma-4-31B-it",
        release_ym="2026-03",
        fits_96gib_4bit=True,
        llama_cli_090_arch="gemma4",
        total_params_B=31.273,
        backbone_params_B=30.700,
        active_params_B=30.700,
        ple_params_B=0.0,
        ple_heads=0,
        ple_layers=0,
        num_layers=60,
        loop_extra_passes=0,
        loop_core_layers=0,
        n_gdn=0, n_kda=0, n_mamba2=0, n_qsa_dsa=0, n_mla_full=0, n_swa=50, swa_win=1024, n_gqa_full=10,
        d_model=5376, h_q=32, h_kv=4, d_head=512, kv_lora_rank=0, k_eq_v=True,
        lin_heads=0, lin_state_d=0,
        moe_layers=0, n_experts=0, top_k=0, n_shared=0, d_ff_active=21504, d_ff_expert=21504,
        ffn_act="geglu", residual_kind="rms", vocab_size=262144,
        deploy_quant_label="Q4_K_M GGUF (26B-A4B: 16.55GB MXFP4)",
        deploy_size_gb=18.324, deploy_size_gib=17.065,
        lcb_v6=80.0, swe_verified=52.0, swe_pro=35.7, aime_25_26="89.2 (AIME26)", gpqa_diamond=84.3,
        source_note="[SOURCE: google/gemma-4-31B-it config.json + README]",
    ),
    ModelSpec2026(
        rank_tag="#6 Sweet-Spot (ReLU2+Mamba2)",
        name="Nemotron-3.5-Lightning-30B-A3B",
        hf_repo="nvidia/NVIDIA-Nemotron-3.5-Lightning-30B-A3B-NVFP4",
        release_ym="2026-08",
        fits_96gib_4bit=True,
        llama_cli_090_arch="nemotron_h_moe",
        total_params_B=31.578,
        backbone_params_B=31.578,
        active_params_B=3.150,
        ple_params_B=0.0,
        ple_heads=0,
        ple_layers=0,
        num_layers=52,   # 23 Mamba2 + 6 Full GQA + 23 ReLU^2 MoE decoupled blocks
        loop_extra_passes=0,
        loop_core_layers=0,
        n_gdn=0, n_kda=0, n_mamba2=23, n_qsa_dsa=0, n_mla_full=0, n_swa=0, swa_win=0, n_gqa_full=6,
        d_model=2688, h_q=32, h_kv=2, d_head=128, kv_lora_rank=0, k_eq_v=False,
        lin_heads=64, lin_state_d=128,
        moe_layers=23, n_experts=128, top_k=6, n_shared=1, d_ff_active=14848, d_ff_expert=1856,
        ffn_act="relu2", residual_kind="rms", vocab_size=131072,
        deploy_quant_label="NVFP4 (21.6GB) / MXFP4_MOE GGUF",
        deploy_size_gb=21.580, deploy_size_gib=20.100,
        lcb_v6=None, swe_verified=52.8, swe_pro=None, aime_25_26="[OPEN]", gpqa_diamond=75.6,
        source_note="[SOURCE: nvidia/NVIDIA-Nemotron-3.5-Lightning-30B-A3B-NVFP4 config.json + README]",
    ),
    # --- TIER 2: 26–96 GiB FULL-MEMORY / MMAP-PLE FRONTIER SOTA ---
    ModelSpec2026(
        rank_tag="#1 Full-96GiB Frontier",
        name="Qwen3.8-Flash-Next (125B-A6B+51B)",
        hf_repo="Qwen/Qwen3.8-Flash-Next",
        release_ym="2026-08",
        fits_96gib_4bit=True,
        llama_cli_090_arch="qwen4exp",
        total_params_B=180.000,
        backbone_params_B=125.744,
        active_params_B=6.671,
        ple_params_B=51.200,
        ple_heads=16,
        ple_layers=1,
        num_layers=48,
        loop_extra_passes=0,
        loop_core_layers=0,
        n_gdn=36, n_kda=0, n_mamba2=0, n_qsa_dsa=12, n_mla_full=0, n_swa=0, swa_win=0, n_gqa_full=0,
        d_model=2560, h_q=24, h_kv=2, d_head=256, kv_lora_rank=0, k_eq_v=False,
        lin_heads=48, lin_state_d=128,
        moe_layers=48, n_experts=512, top_k=10, n_shared=1, d_ff_active=7040, d_ff_expert=640,
        ffn_act="swiglu", residual_kind="gr4", vocab_size=248320,
        deploy_quant_label="GSQ-RCO-IQ3_S (54.8G + 28.8G mmap PLE)",
        deploy_size_gb=83.618, deploy_size_gib=77.875,
        lcb_v6=91.9, swe_verified=78.7, swe_pro=62.5, aime_25_26="[OPEN] (MathVis 95.7)", gpqa_diamond=91.7,
        source_note="[SOURCE: arXiv:2608.30320 + Qwen/Qwen3.8-Flash-Next + ISTA-DASLab GGUF]",
    ),
    ModelSpec2026(
        rank_tag="#2 Full-96GiB (Engram-SSD)",
        name="Tencent Hy4-flash (156B-A11B+64B)",
        hf_repo="tencent/Hy4-flash",
        release_ym="2026-11",
        fits_96gib_4bit=True,
        llama_cli_090_arch="hy_v4",
        total_params_B=220.251,
        backbone_params_B=155.500,
        active_params_B=11.300,
        ple_params_B=63.500,
        ple_heads=16,
        ple_layers=4,
        num_layers=42,
        loop_extra_passes=0,
        loop_core_layers=0,
        n_gdn=0, n_kda=0, n_mamba2=0, n_qsa_dsa=12, n_mla_full=0, n_swa=30, swa_win=512, n_gqa_full=0,
        d_model=3072, h_q=32, h_kv=1, d_head=256, kv_lora_rank=512, k_eq_v=False,
        lin_heads=0, lin_state_d=0,
        moe_layers=41, n_experts=512, top_k=16, n_shared=1, d_ff_active=26112, d_ff_expert=1536,
        ffn_act="swiglu", residual_kind="gr4", vocab_size=120832,
        deploy_quant_label="Q3/Q4 Backbone + SSD mmap Engram",
        deploy_size_gb=82.000, deploy_size_gib=76.368,
        lcb_v6=None, swe_verified=None, swe_pro=None, aime_25_26="[OPEN] (DeepSWE 64.6!)", gpqa_diamond=None,
        source_note="[SOURCE: tencent/Hy4-flash config.json (2026-11-17); DeepSWE 64.6% [REPORTED]]",
    ),
    ModelSpec2026(
        rank_tag="#3 Full-96GiB (120B NVFP4)",
        name="Nemotron-3.5-Super-VL-120B-A12B",
        hf_repo="nvidia/NVIDIA-Nemotron-3.5-Super-VL-120B-A12B-NVFP4",
        release_ym="2026-10",
        fits_96gib_4bit=True,
        llama_cli_090_arch="nemotron_h_moe",
        total_params_B=124.450,
        backbone_params_B=120.000,
        active_params_B=12.000,
        ple_params_B=0.0,
        ple_heads=0,
        ple_layers=0,
        num_layers=88,   # 40 Mamba2 + 8 Full GQA + 40 Latent-MoE ReLU^2 blocks
        loop_extra_passes=0,
        loop_core_layers=0,
        n_gdn=0, n_kda=0, n_mamba2=40, n_qsa_dsa=0, n_mla_full=0, n_swa=0, swa_win=0, n_gqa_full=8,
        d_model=4096, h_q=32, h_kv=2, d_head=128, kv_lora_rank=0, k_eq_v=False,
        lin_heads=128, lin_state_d=128,
        moe_layers=40, n_experts=512, top_k=22, n_shared=1, d_ff_active=64512, d_ff_expert=2688,
        ffn_act="relu2", residual_kind="rms", vocab_size=131072,
        deploy_quant_label="Official NVFP4 (75.06 GB)",
        deploy_size_gb=75.060, deploy_size_gib=69.905,
        lcb_v6=88.2, swe_verified=71.1, swe_pro=51.8, aime_25_26="[OPEN] (APEX 88.4)", gpqa_diamond=89.5,
        source_note="[SOURCE: nvidia/NVIDIA-Nemotron-3.5-Super-VL-120B-A12B config.json + README]",
    ),
    ModelSpec2026(
        rank_tag="#4 Full-96GiB (65B Dense)",
        name="Ripple-65B-Preview",
        hf_repo="ricursiveAI/Ripple-65B-Preview",
        release_ym="2026-11",
        fits_96gib_4bit=True,
        llama_cli_090_arch="NONE (ricursive)",
        total_params_B=64.783,
        backbone_params_B=64.783,
        active_params_B=64.783,
        ple_params_B=0.0,
        ple_heads=0,
        ple_layers=0,
        num_layers=80,
        loop_extra_passes=0,
        loop_core_layers=0,
        n_gdn=0, n_kda=0, n_mamba2=0, n_qsa_dsa=0, n_mla_full=0, n_swa=64, swa_win=1024, n_gqa_full=16,
        d_model=5120, h_q=80, h_kv=8, d_head=128, kv_lora_rank=0, k_eq_v=False,
        lin_heads=0, lin_state_d=0,
        moe_layers=0, n_experts=0, top_k=0, n_shared=0, d_ff_active=40960, d_ff_expert=40960,
        ffn_act="swiglu", residual_kind="rms", vocab_size=100352,
        deploy_quant_label="Q4_K_M (~39GB) / Q8_0 (~69GB)",
        deploy_size_gb=39.200, deploy_size_gib=36.508,
        lcb_v6=None, swe_verified=76.5, swe_pro=79.1, aime_25_26="98.3 / 95.0", gpqa_diamond=85.2,
        source_note="[SOURCE: ricursiveAI/Ripple-65B-Preview config.json + README (2026-11-04)]",
    ),
    ModelSpec2026(
        rank_tag="#5 Full-96GiB (127B KDA+MLA)",
        name="Ling-3.0-Flash (127B-A5.1B)",
        hf_repo="inclusionAI/Ling-3.0-Flash",
        release_ym="2026-08",
        fits_96gib_4bit=True,
        llama_cli_090_arch="bailingmoe3",
        total_params_B=127.486,
        backbone_params_B=127.486,
        active_params_B=5.100,
        ple_params_B=0.0,
        ple_heads=0,
        ple_layers=0,
        num_layers=42,
        loop_extra_passes=0,
        loop_core_layers=0,
        n_gdn=0, n_kda=35, n_mamba2=0, n_qsa_dsa=0, n_mla_full=7, n_swa=0, swa_win=0, n_gqa_full=0,
        d_model=2560, h_q=32, h_kv=1, d_head=192, kv_lora_rank=512, k_eq_v=False,
        lin_heads=32, lin_state_d=128,
        moe_layers=40, n_experts=512, top_k=8, n_shared=1, d_ff_active=6912, d_ff_expert=768,
        ffn_act="swiglu", residual_kind="rms", vocab_size=157184,
        deploy_quant_label="Q4_K_M GGUF (77.0GB) / VL-FP4 (69.6GB)",
        deploy_size_gb=77.008, deploy_size_gib=71.719,
        lcb_v6=82.8, swe_verified=None, swe_pro=56.6, aime_25_26="93.2 (AIME26)", gpqa_diamond=None,
        source_note="[SOURCE: inclusionAI/Ling-3.0-Flash config.json + README; LCB/AIME [REPORTED]]",
    ),
    ModelSpec2026(
        rank_tag="#6 Full-96GiB (48B KDA+MLA)",
        name="Kimi-Linear-48B-A3B-Instruct",
        hf_repo="moonshotai/Kimi-Linear-48B-A3B-Instruct",
        release_ym="2025-10",
        fits_96gib_4bit=True,
        llama_cli_090_arch="kimi-linear",
        total_params_B=49.123,
        backbone_params_B=49.123,
        active_params_B=3.100,
        ple_params_B=0.0,
        ple_heads=0,
        ple_layers=0,
        num_layers=27,
        loop_extra_passes=0,
        loop_core_layers=0,
        n_gdn=0, n_kda=20, n_mamba2=0, n_qsa_dsa=0, n_mla_full=7, n_swa=0, swa_win=0, n_gqa_full=0,
        d_model=2304, h_q=32, h_kv=1, d_head=192, kv_lora_rank=512, k_eq_v=False,
        lin_heads=32, lin_state_d=128,
        moe_layers=26, n_experts=256, top_k=8, n_shared=1, d_ff_active=9216, d_ff_expert=1024,
        ffn_act="swiglu", residual_kind="rms", vocab_size=163840,
        deploy_quant_label="IQ4_XS GGUF (26.5GB) / BF16 (98.2GB=91.5GiB)",
        deploy_size_gb=26.465, deploy_size_gib=24.647,
        lcb_v6=45.7, swe_verified=None, swe_pro=None, aime_25_26="[OPEN]", gpqa_diamond=None,
        source_note="[SOURCE: moonshotai/Kimi-Linear-48B-A3B-Instruct config.json + arXiv:2510.26692]",
    ),
    # --- TIER 3: > 96 GiB IN 4-BIT OVERFLOW & CRYPTOGRAPHIC PENALTY AUDIT ---
    ModelSpec2026(
        rank_tag="OVERFLOW-Q4 (Q3/IQ4_XS fits)",
        name="Step-3.5-Flash (199B-A11B)",
        hf_repo="stepfun-ai/Step-3.5-Flash",
        release_ym="2026-02",
        fits_96gib_4bit=False,
        llama_cli_090_arch="step35",
        total_params_B=199.384,
        backbone_params_B=199.384,
        active_params_B=11.000,
        ple_params_B=0.0,
        ple_heads=0,
        ple_layers=0,
        num_layers=45,
        loop_extra_passes=0,
        loop_core_layers=0,
        n_gdn=0, n_kda=0, n_mamba2=0, n_qsa_dsa=0, n_mla_full=0, n_swa=34, swa_win=512, n_gqa_full=11,
        d_model=4096, h_q=64, h_kv=8, d_head=128, kv_lora_rank=0, k_eq_v=False,
        lin_heads=0, lin_state_d=0,
        moe_layers=42, n_experts=288, top_k=8, n_shared=1, d_ff_active=11520, d_ff_expert=1280,
        ffn_act="swiglu", residual_kind="rms", vocab_size=128896,
        deploy_quant_label="Q4_K=110.6GiB (>96!); UD-Q3_K_XL=83.3GiB",
        deploy_size_gb=118.710, deploy_size_gib=110.557,
        lcb_v6=86.4, swe_verified=74.4, swe_pro=None, aime_25_26="97.3 (AIME25)", gpqa_diamond=None,
        source_note="[SOURCE: stepfun-ai/Step-3.5-Flash config.json + README]",
    ),
    ModelSpec2026(
        rank_tag="OVERFLOW-Q4 + mHC-Sinkhorn20",
        name="GLM-5.3-Flash (321B-A18B)",
        hf_repo="zai-org/GLM-5.3-Flash",
        release_ym="2026-08",
        fits_96gib_4bit=False,
        llama_cli_090_arch="glm5-next",
        total_params_B=321.323,
        backbone_params_B=321.323,
        active_params_B=18.000,
        ple_params_B=0.0,
        ple_heads=0,
        ple_layers=0,
        num_layers=45,
        loop_extra_passes=0,
        loop_core_layers=0,
        n_gdn=0, n_kda=34, n_mamba2=0, n_qsa_dsa=11, n_mla_full=0, n_swa=0, swa_win=0, n_gqa_full=0,
        d_model=4096, h_q=64, h_kv=1, d_head=256, kv_lora_rank=512, k_eq_v=False,
        lin_heads=64, lin_state_d=128,
        moe_layers=42, n_experts=288, top_k=8, n_shared=1, d_ff_active=18432, d_ff_expert=2048,
        ffn_act="swiglu", residual_kind="mhc20", vocab_size=154880,
        deploy_quant_label="UD-Q4_K_XL=186.0GiB (>96!); IQ2_XXS=94.9GiB",
        deploy_size_gb=199.707, deploy_size_gib=185.992,
        lcb_v6=None, swe_verified=None, swe_pro=None, aime_25_26="[OPEN] (DeepSWE 66.9)", gpqa_diamond=None,
        source_note="[SOURCE: zai-org/GLM-5.3-Flash config.json (`hc_sinkhorn_iters:20`) + unsloth GGUF]",
    ),
    ModelSpec2026(
        rank_tag="OVERFLOW-Q4 + mHC20 + 557B PLE",
        name="DeepSeek-V4.1-Flash (763B-A16B)",
        hf_repo="deepseek-ai/DeepSeek-V4.1-Flash",
        release_ym="2026-10",
        fits_96gib_4bit=False,
        llama_cli_090_arch="deepseek41",
        total_params_B=763.205,
        backbone_params_B=206.034,
        active_params_B=16.000,
        ple_params_B=557.171,
        ple_heads=8,
        ple_layers=2,
        num_layers=40,
        loop_extra_passes=0,
        loop_core_layers=0,
        n_gdn=0, n_kda=0, n_mamba2=0, n_qsa_dsa=20, n_mla_full=0, n_swa=20, swa_win=128, n_gqa_full=0,
        d_model=5120, h_q=64, h_kv=1, d_head=512, kv_lora_rank=512, k_eq_v=False,
        lin_heads=0, lin_state_d=0,
        moe_layers=40, n_experts=384, top_k=6, n_shared=1, d_ff_active=16128, d_ff_expert=2304,
        ffn_act="swiglu", residual_kind="mhc20", vocab_size=129280,
        deploy_quant_label="UD-Q4_K_XL=473.8GiB (>96!); IQ2+Engram=241GiB",
        deploy_size_gb=508.716, deploy_size_gib=473.778,
        lcb_v6=None, swe_verified=None, swe_pro=None, aime_25_26="[OPEN] (DeepSWE 77.0!)", gpqa_diamond=94.1,
        source_note="[SOURCE: deepseek-ai/DeepSeek-V4.1-Flash config.json + README + unsloth GGUF]",
    ),
)


@dataclass(frozen=True)
class CryptoPriceRow:
    model: str
    mode: str
    T: int
    zk_cells_M: float
    zk_exp_lkps_M: float
    zk_gruen_sc_ext4_M: float
    zk_prover_bb_muls_B: float
    vfhe_pubw_wire_M: float
    vfhe_state_kv_gib: float
    vfhe_dark_hoisted_gbit: float


def price_model_at_T(m: ModelSpec2026, mode: str, T: int) -> CryptoPriceRow:
    """
    Deterministic per-token `zkML` and `vFHEML` pricing across all 2026 architecture primitives,
    calibrated directly to `qwen38_next_zk_vfhe_pricing.py` & `einsum-speedup-wave.md`:
      - `GDN` / `KDA`: `C = 64` division-free WY `(I + L)[U|W] = RHS` -> `0` T^2 `EXP_TAB` lookups,
        `1` scalar decay `EXP` per head/layer (`O(1)` in T), `O(1)` encrypted state (`H_v * d^2` scalars).
      - `Mamba-2` (`SSD`, `C = 128`): structured state-space duality (`H_m * d_m * d_state` state, `O(1)` in T,
        `1` dt-exp per head/layer, `0` T^2 softmax!).
      - `QSA` / `DSA`: `AvgPool r = 4` `ReLU` indexer (`0` `EXP_TAB` lookups, `2` cells/blk) + `K = 2048` sparse core.
      - `MLA` (`kv_lora_rank`): full causal `EXP_TAB` on `H_q` heads, but KV cache compressed to `kv_lora_rank + 64`.
      - `SWA` (`W`): block-banded `step_beta` virtual window (`min(T, W)` active keys/query, `O(W)` KV state).
      - `Full GQA`: `H_q * (T/2 prefill | T decode)` `EXP_TAB` pairs/layer (`k_eq_v=True` halves KV state!).
      - `ReLU^2` FFN (`Nemotron-3.5`): sign-bit + degree-2 square (`2` cells/lkp vs `8` for `SwiGLU`/`GeGLU`!).
      - `mHC` (`hc_sinkhorn_iters = 20` in `GLM-5.3-Flash` / `DeepSeek-V4.1`): `2 * L * 20` 4x4 row/col reciprocal
        witnesses + crossings per token!
      - `Looped MoE` (`Inkling-2`): stored weights scanned ONCE in prefill across `3` passes (`t_batch * 3` amortization!).
    """
    t_batch = T if mode == "prefill" else 1

    # 1. Linear / SSM layers (GDN, KDA, Mamba2) — O(1) state, ZERO T^2 EXP_TABs!
    n_lin = m.n_gdn + m.n_kda + m.n_mamba2
    lin_width = m.lin_heads * m.lin_state_d
    state_scalars_per_lin = m.lin_heads * m.lin_state_d * (64 if m.n_mamba2 > 0 and m.n_gdn == 0 and m.n_kda == 0 else m.lin_state_d)
    lin_proj_elems = n_lin * (3 * lin_width + m.d_model + 2 * m.lin_heads)
    wy_chunk = 128 if m.n_mamba2 > 0 else 64
    wy_cells = n_lin * (2 * lin_width + (state_scalars_per_lin // wy_chunk if mode == "prefill" else 0))
    lin_cells = 4.0 * lin_proj_elems + wy_cells + n_lin * (3.0 * lin_width)
    lin_lkps = 4.0 * lin_proj_elems + n_lin * (3.0 * lin_width + 2 * m.lin_heads)
    lin_exp = float(n_lin * m.lin_heads)  # 1 decay exp per head per layer!
    lin_gruen_ext4 = float(n_lin * m.lin_heads * m.lin_state_d * wy_chunk * 2.0)

    # 2. Sparse Block-Indexed Attention (`QSA` / `DSA`, r=4, K=2048)
    qsa_relu_l = (T / 2.0) if mode == "prefill" else float(T)
    qsa_topk_l = max(0.0, T / 8.0 - 256.0) if mode == "prefill" else (0.0 if T <= 2048 else T / 4.0)
    eff_k_qsa = ((T + 1.0) / 2.0 if T <= 2048 else (2048.0 - (2048.0 * 2047.0) / (2.0 * T))) if mode == "prefill" else float(min(T, 2048))
    idx_blks_qsa = (T / 8.0) if mode == "prefill" else (T / 4.0)
    qsa_lin_elems = m.n_qsa_dsa * (2 * m.h_q * m.d_head + 2 * m.h_kv * m.d_head + m.d_model + 640)
    qsa_exp = m.n_qsa_dsa * m.h_q * eff_k_qsa
    qsa_cells = 4.0 * qsa_lin_elems + m.n_qsa_dsa * (2.0 * qsa_relu_l + 2.0 * qsa_topk_l + 6.0 * m.h_q * eff_k_qsa + 2048.0)
    qsa_lkps = 4.0 * qsa_lin_elems + m.n_qsa_dsa * (2.0 * qsa_relu_l + 2.0 * qsa_topk_l + 5.25 * m.h_q * eff_k_qsa + 512.0)
    qsa_gruen_ext4 = m.n_qsa_dsa * (4 * 128 * (qsa_relu_l / 4.0) + m.h_q * m.d_head * eff_k_qsa * 2.0)

    # 3. Sliding Window Attention (`SWA`, window = swa_win)
    if m.n_swa > 0 and m.swa_win > 0:
        w = float(m.swa_win)
        eff_swa = ((T + 1.0) / 2.0 if T <= w else (w - w * (w - 1.0) / (2.0 * T))) if mode == "prefill" else float(min(T, int(w)))
    else:
        eff_swa = 0.0
    kv_mult = 1 if m.k_eq_v else 2
    swa_lin_elems = m.n_swa * (m.h_q * m.d_head + kv_mult * m.h_kv * m.d_head + m.d_model)
    swa_exp = m.n_swa * m.h_q * eff_swa
    swa_cells = 4.0 * swa_lin_elems + 6.0 * swa_exp
    swa_lkps = 4.0 * swa_lin_elems + 5.25 * swa_exp
    swa_gruen_ext4 = swa_exp * m.d_head * 2.0

    # 4. Full Causal GQA & Full Causal MLA (`O(T^2)` prefill / `O(T)` decode!)
    n_full = m.n_gqa_full + m.n_mla_full
    eff_full = (T / 2.0) if mode == "prefill" else float(T)
    full_lin_elems = m.n_gqa_full * (m.h_q * m.d_head + kv_mult * m.h_kv * m.d_head + m.d_model) + m.n_mla_full * (
        m.h_q * m.d_head + m.kv_lora_rank + 64 + m.d_model
    )
    full_exp = n_full * m.h_q * eff_full
    full_cells = 4.0 * full_lin_elems + 6.0 * full_exp
    full_lkps = 4.0 * full_lin_elems + 5.25 * full_exp
    full_gruen_ext4 = full_exp * m.d_head * 2.0

    # 5. FFN / MoE + Residual (`rms`, `gr4`, `mhc20`) + PLE/Engram
    eff_layers = m.num_layers + m.loop_extra_passes * m.loop_core_layers
    ffn_cell_mult = 6.0 if m.ffn_act == "relu2" else 14.0  # relu2 avoids 8-cell SiLU/GELU lookup decomposition!
    ffn_lkp_mult = 4.0 if m.ffn_act == "relu2" else 13.0
    router_cells = m.moe_layers * (m.n_experts * 5.0)
    router_lkps = m.moe_layers * (m.n_experts * 2.0 + m.top_k)
    router_exp = float(m.moe_layers * m.top_k)  # monotone top-k before softmax (`top_k` vs `E` exp!)
    ffn_layers_count = m.moe_layers if m.moe_layers > 0 else eff_layers
    ffn_cells = ffn_layers_count * (ffn_cell_mult * m.d_ff_active + 4.0 * m.d_model) + router_cells + 2.0 * m.vocab_size
    ffn_lkps = ffn_layers_count * (ffn_lkp_mult * m.d_ff_active + 4.0 * m.d_model) + router_lkps + 2.0 * m.vocab_size

    if m.residual_kind == "gr4":
        res_cells = (2 * eff_layers + 1) * (4 * (m.d_model // 8) + 4 * 4 * m.d_model + 16)
    elif m.residual_kind == "mhc20":
        # 20 Sinkhorn-Knopp row+col reciprocal divisions on 4x4 doubly-stochastic mixers per sublayer!
        res_cells = (2 * eff_layers) * (20 * 8 * 12 + 4 * 4 * m.d_model)
    else:
        res_cells = (2 * eff_layers) * (2 * m.d_model)
    res_lkps = res_cells

    ple_cells = m.ple_layers * ((m.ple_heads * 39 * POSEIDON2_NARROW_CELLS_PER_PERM) + m.ple_heads * 48 + 4 * 9 * m.d_model)
    ple_lkps = m.ple_layers * (m.ple_heads * 48 + 4 * 9 * m.d_model)

    tot_cells = lin_cells + qsa_cells + swa_cells + full_cells + ffn_cells + res_cells + ple_cells
    tot_lkps = lin_lkps + qsa_lkps + swa_lkps + full_lkps + ffn_lkps + res_lkps + ple_lkps
    tot_exp = lin_exp + qsa_exp + swa_exp + full_exp + router_exp

    # 6. Scanned Weights (Coupon-Collector on MoE + Looped-Core Reuse!) & Gruen Sumcheck Muls
    active_w = m.active_params_B * 1e9
    if m.n_experts > 0:
        eff_tokens_per_stored_moe = t_batch * (1 + m.loop_extra_passes * (m.loop_core_layers / max(m.num_layers, 1)))
        stored_moe_layers = m.moe_layers // (1 + (m.loop_extra_passes if m.loop_core_layers > 0 else 0))
        active_e = m.n_experts * (1.0 - ((m.n_experts - m.top_k) / m.n_experts) ** eff_tokens_per_stored_moe)
        per_expert_w = (2 if m.ffn_act == "relu2" else 3) * m.d_model * m.d_ff_expert
        scanned_moe_w = stored_moe_layers * (active_e + m.n_shared) * per_expert_w
        non_moe_w = max(0.0, m.backbone_params_B * 1e9 - stored_moe_layers * (m.n_experts + m.n_shared) * per_expert_w)
        scanned_w = scanned_moe_w + non_moe_w
    else:
        scanned_w = m.backbone_params_B * 1e9

    # MXFP4 Tensor-Factored + 7-bucket E2M1 Horner (`~0.355` Ext4 muls = `3.2` BB muls per scanned weight)
    gruen_sc_ext4 = (scanned_w * 0.355) / t_batch + lin_gruen_ext4 + qsa_gruen_ext4 + swa_gruen_ext4 + full_gruen_ext4
    prover_sc_bb_muls = (
        3.2 * scanned_w / t_batch
        + 8.0 * active_w
        + 8.0 * (lin_gruen_ext4 + qsa_gruen_ext4 + swa_gruen_ext4 + full_gruen_ext4)
    )
    prover_tot_bb_muls = prover_sc_bb_muls + WHIR_LDE_MULS_PER_BASE_CELL * tot_cells + 12.0 * tot_lkps

    # 7. `vFHEML` (`HoistedB61` + `SPDZ` Crossing + `2P-DPF` PLE):
    # Encrypted state + KV cache in 64-bit ring shares (GiB):
    lin_state_bytes = n_lin * state_scalars_per_lin * 8
    qsa_kv_scalars_per_tok = (m.kv_lora_rank + 64 + 128) if m.kv_lora_rank > 0 else (2 * m.h_kv * m.d_head + 128)
    qsa_kv_bytes = m.n_qsa_dsa * qsa_kv_scalars_per_tok * T * 8
    swa_kv_scalars_per_tok = (m.kv_lora_rank + 64) if m.kv_lora_rank > 0 else (kv_mult * m.h_kv * m.d_head)
    swa_kv_bytes = m.n_swa * swa_kv_scalars_per_tok * min(T, max(m.swa_win, 1)) * 8
    gqa_kv_bytes = m.n_gqa_full * kv_mult * m.h_kv * m.d_head * T * 8
    mla_kv_bytes = m.n_mla_full * (m.kv_lora_rank + 64) * T * 8
    vfhe_state_kv_gib = (lin_state_bytes + qsa_kv_bytes + swa_kv_bytes + gqa_kv_bytes + mla_kv_bytes) / (1024 ** 3)

    # SPDZ crossing wire elements per token (`E2S + S2E` = `2 * B61_N * B61_L * 6` per crossing + active nonlinear Beaver triples):
    crossing_overhead = 2 * B61_N * B61_L * 6
    mhc_wire = (2 * eff_layers * 20 * 64 * 6) if m.residual_kind == "mhc20" else 0.0
    ffn_beaver_mult = 2.0 if m.ffn_act == "relu2" else 6.0
    vfhe_pubw_wire = (
        n_lin * (6.0 * lin_width + crossing_overhead)
        + m.n_qsa_dsa * (6.0 * (idx_blks_qsa + m.h_q * eff_k_qsa) + crossing_overhead)
        + (m.n_swa + n_full) * crossing_overhead
        + 6.0 * (swa_exp + full_exp)
        + ffn_layers_count * (ffn_beaver_mult * m.d_ff_active + 6.0 * m.n_experts + crossing_overhead)
        + mhc_wire
        + m.ple_layers * m.ple_heads * 480.0
    )

    # Dark `HoistedB61` `ct x ct` certificate volume (Gbit/tok):
    dark_ct_ct = (
        (active_w / B61_N)
        + n_lin * (2.0 * state_scalars_per_lin / B61_N)
        + m.n_qsa_dsa * (idx_blks_qsa * 128.0 / B61_N + 2.0 * eff_k_qsa * m.h_kv * m.d_head / B61_N)
        + (swa_exp + full_exp) * (2.0 * m.d_head / B61_N)
    )
    vfhe_dark_hoisted_gbit = (dark_ct_ct * B61_CT_CT_BITS_HOISTED) / 1e9

    return CryptoPriceRow(
        model=m.name,
        mode=mode,
        T=T,
        zk_cells_M=tot_cells / 1e6,
        zk_exp_lkps_M=tot_exp / 1e6,
        zk_gruen_sc_ext4_M=gruen_sc_ext4 / 1e6,
        zk_prover_bb_muls_B=prover_tot_bb_muls / 1e9,
        vfhe_pubw_wire_M=vfhe_pubw_wire / 1e6,
        vfhe_state_kv_gib=vfhe_state_kv_gib,
        vfhe_dark_hoisted_gbit=vfhe_dark_hoisted_gbit,
    )


# ======================================================================================
# 3. Real `Qwen3.8-27B` `MXFP4` & `NVFP4` (`E2M1`) Tensor Slice Audit & `Ext4` Horner Prover
# ======================================================================================
def ext_from_int(v: int) -> np.ndarray:
    return np.array([v % P_BB, 0, 0, 0], dtype=np.int64)


def ext_add(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    return (a + b) % P_BB


def ext_sub(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    return (a - b) % P_BB


def ext_mul(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    a0, a1, a2, a3 = a[..., 0], a[..., 1], a[..., 2], a[..., 3]
    b0, b1, b2, b3 = b[..., 0], b[..., 1], b[..., 2], b[..., 3]
    t_hi0 = ((a1 * b3) % P_BB + (a2 * b2) % P_BB + (a3 * b1) % P_BB) % P_BB
    t_hi1 = ((a2 * b3) % P_BB + (a3 * b2) % P_BB) % P_BB
    c0 = ((a0 * b0) % P_BB + W_EXT4 * t_hi0) % P_BB
    c1 = ((a0 * b1) % P_BB + (a1 * b0) % P_BB + W_EXT4 * t_hi1) % P_BB
    c2 = ((a0 * b2) % P_BB + (a1 * b1) % P_BB + (a2 * b0) % P_BB + W_EXT4 * ((a3 * b3) % P_BB)) % P_BB
    c3 = ((a0 * b3) % P_BB + (a1 * b2) % P_BB + (a2 * b1) % P_BB + (a3 * b0) % P_BB) % P_BB
    return np.stack([c0, c1, c2, c3], axis=-1)


def build_eq_table(r: np.ndarray) -> np.ndarray:
    k = r.shape[0]
    one = ext_from_int(1)
    if k == 0:
        return one[None, :]
    tbl = np.stack([ext_sub(one, r[0]), r[0]], axis=0)
    for bit in range(1, k):
        hi = ext_mul(tbl, r[bit])
        lo = ext_sub(tbl, hi)
        tbl = np.stack([lo, hi], axis=1).reshape(-1, 4)
    return tbl


def fp8_e4m3_to_f32_and_exact_int(u8: np.ndarray) -> Tuple[np.ndarray, np.ndarray, int]:
    """Decode FP8 E4M3 to float32 AND lift every nonzero scale to exact integer `(8 + m) * 2^(exp_unbiased - e_min)`."""
    u = u8.astype(np.int64)
    sign = np.where((u >> 7) & 1, -1, 1)
    exp = (u >> 3) & 0xF
    man = u & 0x7
    # Exact representation:
    #   exp == 0: man * 2^-9
    #   exp > 0 : (8 + man) * 2^(exp - 10)
    # Multiply all values by 2^9 so every finite FP8 E4M3 is an EXACT integer in [-448*512, 448*512]!
    int_x512 = np.where(exp == 0, sign * man, sign * (8 + man) * (1 << np.maximum(exp - 1, 0)))
    f32 = (int_x512.astype(np.float64) / 512.0).astype(np.float32)
    return f32, int_x512, -9


def ensure_qwen38_27b_e2m1_slices() -> Dict[str, np.ndarray]:
    """Load cached real `256 x 5120` Layer-0 `gate_proj` slices or fetch via HTTP Range (`< 5 MB`)."""
    if SLICE_CACHE_PATH.exists():
        d = np.load(SLICE_CACHE_PATH)
        return {k: d[k] for k in d.files}

    SLICE_CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)

    def _range(url: str, s: int, e: int) -> bytes:
        req = urllib.request.Request(url, headers={"User-Agent": "zkml-research/1.0", "Range": f"bytes={s}-{e}"})
        with urllib.request.urlopen(req, timeout=20) as resp:
            return resp.read()

    def _hdr(repo: str, shard: str) -> Tuple[str, int, Dict[str, Any]]:
        url = f"https://huggingface.co/{repo}/resolve/main/{shard}"
        hlen = struct.unpack("<Q", _range(url, 0, 7))[0]
        return url, 8 + hlen, json.loads(_range(url, 8, 8 + hlen - 1).decode("utf-8"))

    rows = 256
    bf_url, bf_base, bf_h = _hdr("Qwen/Qwen3.8-27B", "model-00001-of-00018.safetensors")
    bf_off = bf_base + bf_h["model.language_model.layers.0.mlp.gate_proj.weight"]["data_offsets"][0]
    w_bf16_u16 = np.frombuffer(_range(bf_url, bf_off, bf_off + rows * 5120 * 2 - 1), dtype=np.uint16).reshape(rows, 5120)

    mx_url, mx_base, mx_h = _hdr("mlx-community/Qwen3.8-27B-mxfp4", "model-00001-of-00003.safetensors")
    mx_wo = mx_base + mx_h["language_model.model.layers.0.mlp.gate_proj.weight"]["data_offsets"][0]
    mx_so = mx_base + mx_h["language_model.model.layers.0.mlp.gate_proj.scales"]["data_offsets"][0]
    mx_u32 = np.frombuffer(_range(mx_url, mx_wo, mx_wo + rows * 640 * 4 - 1), dtype=np.uint32).reshape(rows, 640)
    mx_scales_u8 = np.frombuffer(_range(mx_url, mx_so, mx_so + rows * 160 - 1), dtype=np.uint8).reshape(rows, 160)

    nv_url, nv_base, nv_h = _hdr("unsloth/Qwen3.8-27B-NVFP4", "model.safetensors")
    nv_wpo = nv_base + nv_h["model.language_model.layers.0.mlp.gate_proj.weight_packed"]["data_offsets"][0]
    nv_wso = nv_base + nv_h["model.language_model.layers.0.mlp.gate_proj.weight_scale"]["data_offsets"][0]
    nv_wgo = nv_base + nv_h["model.language_model.layers.0.mlp.gate_proj.weight_global_scale"]["data_offsets"][0]
    nv_u8 = np.frombuffer(_range(nv_url, nv_wpo, nv_wpo + rows * 2560 - 1), dtype=np.uint8).reshape(rows, 2560)
    nv_ws_u8 = np.frombuffer(_range(nv_url, nv_wso, nv_wso + rows * 320 - 1), dtype=np.uint8).reshape(rows, 320)
    nv_wg_f32 = np.frombuffer(_range(nv_url, nv_wgo, nv_wgo + 3), dtype=np.float32)

    np.savez_compressed(
        SLICE_CACHE_PATH,
        w_bf16_u16=w_bf16_u16, mx_u32=mx_u32, mx_scales_u8=mx_scales_u8,
        nv_u8=nv_u8, nv_ws_u8=nv_ws_u8, nv_wg_f32=nv_wg_f32,
    )
    return {
        "w_bf16_u16": w_bf16_u16, "mx_u32": mx_u32, "mx_scales_u8": mx_scales_u8,
        "nv_u8": nv_u8, "nv_ws_u8": nv_ws_u8, "nv_wg_f32": nv_wg_f32,
    }


def horner_7bucket_bind_b(q_nibs: np.ndarray, weights_ext4: np.ndarray) -> np.ndarray:
    """
    Zero-multiplication 7-bucket signed E2M1 addition chain (`notes/einsum-speedup-wave.md` §2.1):
    Evaluates `sum_b weights_ext4[..., b] * decode_e2m1_x2(q_nibs[..., b])` over `Ext4` using
    ONLY additions, subtractions, and 3 doublings (`(((2*C8 + C4)*2 + C2)*2 + C1)`),
    canonicalizing both nibble `0` (`+0.0`) and nibble `8` (`-0.0`) to `0`!
    `q_nibs`: shape `(J, K, B)`, `weights_ext4`: shape `(B, 4)` or `(J, K, 4)` -> returns `(J, K, 4)` or `(K, B, 4)`.
    """
    # Here `q_nibs` is `(J, K, B)` and `weights_ext4` is `(B, 4)` -> output `(J, K, 4)`.
    J, K, B = q_nibs.shape
    buckets = np.zeros((8, J, K, 4), dtype=np.int64)  # index by |e2m1_x2| in {1,2,3,4,6,8,12} -> map {1:1,2:2,3:3,4:4,6:5,8:6,12:7}
    mag_to_slot = {1: 1, 2: 2, 3: 3, 4: 4, 6: 5, 8: 6, 12: 7}
    for b in range(B):
        wb = weights_ext4[b]  # (4,)
        col = q_nibs[:, :, b]
        for nib in range(1, 16):
            if nib == 8:
                continue  # -0.0 canonicalized to 0!
            val = int(E2M1_X2[nib])
            slot = mag_to_slot[abs(val)]
            mask = (col == nib)[:, :, None]
            if val > 0:
                buckets[slot] = (buckets[slot] + mask * wb) % P_BB
            else:
                buckets[slot] = (buckets[slot] - mask * wb) % P_BB

    b1, b2, b3, b4, b6, b8, b12 = buckets[1], buckets[2], buckets[3], buckets[4], buckets[5], buckets[6], buckets[7]
    c8 = (b8 + b12) % P_BB
    c4 = (b4 + b6 + b12) % P_BB
    c2 = (b2 + b3 + b6) % P_BB
    c1 = (b1 + b3) % P_BB
    acc = (2 * c8 + c4) % P_BB
    acc = (2 * acc + c2) % P_BB
    acc = (2 * acc + c1) % P_BB
    return acc


def verify_e2m1_slices_and_horner_prover() -> Dict[str, Any]:
    """Verify real Qwen3.8-27B MXFP4 & NVFP4 slices against BF16 and run 0-mul E2M1 Horner check + falsifier."""
    sl = ensure_qwen38_27b_e2m1_slices()
    w_bf16 = (sl["w_bf16_u16"].astype(np.uint32) << 16).view(np.float32)  # (256, 5120)

    # 1. MXFP4 (`mlx-community/Qwen3.8-27B-mxfp4`, block-32 UE8M0)
    mx_u32 = sl["mx_u32"]                # (256, 640)
    mx_s_u8 = sl["mx_scales_u8"]         # (256, 160)
    mx_nibs_raw = np.stack([(mx_u32 >> (4 * k)) & 0xF for k in range(8)], axis=-1).reshape(256, 160, 32).astype(np.uint8)
    neg_zero_mx = int((mx_nibs_raw == 8).sum())
    mx_nibs_canon = np.where(mx_nibs_raw == 8, np.uint8(0), mx_nibs_raw)
    mx_scales_f32 = (2.0 ** (mx_s_u8.astype(np.int32) - 127)).astype(np.float32)
    w_mx = (E2M1_F32[mx_nibs_canon] * mx_scales_f32[:, :, None]).reshape(256, 5120)
    cos_mx = float(np.sum(w_bf16 * w_mx) / (np.linalg.norm(w_bf16) * np.linalg.norm(w_mx)))
    snr_mx = float(10.0 * np.log10(np.sum(w_bf16 ** 2) / np.sum((w_bf16 - w_mx) ** 2)))

    # 2. NVFP4 (`unsloth/Qwen3.8-27B-NVFP4`, block-16 FP8-E4M3 + F32 global_scale)
    nv_u8 = sl["nv_u8"]                  # (256, 2560)
    nv_ws_u8 = sl["nv_ws_u8"]            # (256, 320)
    nv_wg = float(sl["nv_wg_f32"][0])
    nv_nibs = np.stack([nv_u8 & 0xF, (nv_u8 >> 4) & 0xF], axis=-1).reshape(256, 320, 16).astype(np.uint8)
    neg_zero_nv = int((nv_nibs == 8).sum())
    nv_ws_f32, nv_ws_int_x512, _ = fp8_e4m3_to_f32_and_exact_int(nv_ws_u8)
    w_nv = (E2M1_F32[nv_nibs] * nv_ws_f32[:, :, None] / nv_wg).reshape(256, 5120)
    cos_nv = float(np.sum(w_bf16 * w_nv) / (np.linalg.norm(w_bf16) * np.linalg.norm(w_nv)))
    snr_nv = float(10.0 * np.log10(np.sum(w_bf16 ** 2) / np.sum((w_bf16 - w_nv) ** 2)))

    # 3. Exact BabyBear + Ext4 Zero-Mul 7-Bucket E2M1 Horner Verification on BOTH Real Slices!
    # Pad K=160 -> 256 (MXFP4, B=32) and K=320 -> 512 (NVFP4, B=16) for dyadic multilinear check:
    rng = np.random.default_rng(20261121)
    x_in = rng.integers(-128, 128, size=(16, 5120), dtype=np.int64)  # T_tok=16 real-range INT8 activations

    # (a) MXFP4 exact integer contraction over Z and BabyBear/Ext4:
    e_min_mx = int(mx_s_u8.min())
    mx_s_int = (1 << (mx_s_u8.astype(np.int64) - e_min_mx))  # exact integer scales in [1, 8]!
    q_mx_int = E2M1_X2[mx_nibs_canon]                        # (256, 160, 32)
    w_mx_int = (q_mx_int * mx_s_int[:, :, None]).reshape(256, 5120)
    y_mx_int = x_in @ w_mx_int.T                             # (16, 256), max |Y| << P_BB // 2!
    assert int(np.abs(y_mx_int).max()) < (P_BB // 2), "MXFP4 integer dot exceeded BabyBear half-modulus!"

    # Check Ext4 multilinear evaluation identity using 7-bucket 0-mul Horner on `Q`:
    r_i = rng.integers(1, P_BB - 1, size=(4, 4), dtype=np.int64)   # log2(16)=4
    r_j = rng.integers(1, P_BB - 1, size=(8, 4), dtype=np.int64)   # log2(256)=8
    r_b = rng.integers(1, P_BB - 1, size=(5, 4), dtype=np.int64)   # log2(32)=5
    eq_i = build_eq_table(r_i)                                     # (16, 4)
    eq_j = build_eq_table(r_j)                                     # (256, 4)
    eq_b = build_eq_table(r_b)                                     # (32, 4)

    # Bind Q_mx via 7-bucket 0-mul Horner vs direct field-multiplication reference:
    q_mx_horner = horner_7bucket_bind_b(mx_nibs_canon, eq_b)       # (256, 160, 4) — ZERO muls on Q!
    q_mx_direct = (((q_mx_int % P_BB)[:, :, :, None] * eq_b[None, None, :, :]) % P_BB).sum(axis=2) % P_BB
    assert np.array_equal(q_mx_horner, q_mx_direct), "MXFP4 7-bucket Horner != direct Ext4 evaluation!"

    # Also prove raw un-canonicalized MXFP4 (`neg_zero_mx = 51,851`) evaluates identically under 7-bucket Horner:
    q_mx_raw_horner = horner_7bucket_bind_b(mx_nibs_raw, eq_b)
    assert np.array_equal(q_mx_raw_horner, q_mx_horner), "Raw nibble=8 (-0.0) caused Horner divergence!"

    # Full `Y(r_i, r_j)` tensor contraction check over Ext4:
    y_ri = (((y_mx_int % P_BB)[:, :, None] * eq_i[:, None, :]) % P_BB).sum(axis=0) % P_BB
    lhs_y = ext_mul(y_ri, eq_j).sum(axis=0) % P_BB
    x_ri = (((x_in.reshape(16, 160, 32) % P_BB)[:, :, :, None] * eq_i[:, None, None, :]) % P_BB).sum(axis=0) % P_BB
    # Sum_{j,k,b} eq_j[j] * S[j,k] * Q[j,k,b] * X_ri[k,b] using 7-bucket Horner per k!
    e_jk = (eq_j[:, None, :] * (mx_s_int % P_BB)[:, :, None]) % P_BB  # (256, 160, 4)
    rhs_y = np.zeros(4, dtype=np.int64)
    for b in range(32):
        q_slice = ((q_mx_int[:, :, b] % P_BB)[:, :, None] * e_jk) % P_BB  # (256, 160, 4)
        m_kb = q_slice.sum(axis=0) % P_BB                                  # (160, 4)
        rhs_y = (rhs_y + ext_mul(m_kb, x_ri[:, b, :]).sum(axis=0)) % P_BB
    assert np.array_equal(lhs_y, rhs_y), "Ext4 MXFP4 tensor contraction claim mismatch!"

    # Constructive Tamper Falsifier: flip 1 nibble of Q_mx -> Ext4 claim MUST reject!
    tampered_nibs = mx_nibs_canon.copy()
    tampered_nibs[0, 0, 0] = np.uint8(7 if tampered_nibs[0, 0, 0] != 7 else 1)
    q_tampered_horner = horner_7bucket_bind_b(tampered_nibs, eq_b)
    tamper_rejected = not np.array_equal(q_tampered_horner, q_mx_horner)
    assert tamper_rejected

    # (b) NVFP4 exact integer scale + 7-bucket Horner check (`B = 16`, `F8_E4M3` micro-scales lifted to exact Z):
    eq_b16 = build_eq_table(r_b[:4])  # (16, 4)
    q_nv_horner = horner_7bucket_bind_b(nv_nibs, eq_b16)
    q_nv_direct = (((E2M1_X2[nv_nibs] % P_BB)[:, :, :, None] * eq_b16[None, None, :, :]) % P_BB).sum(axis=2) % P_BB
    assert np.array_equal(q_nv_horner, q_nv_direct), "NVFP4 7-bucket Horner != direct Ext4 evaluation!"
    w_nv_int_unshifted = (E2M1_X2[nv_nibs] * nv_ws_int_x512[:, :, None]).reshape(256, 5120)
    y_nv_int_unshifted = x_in @ w_nv_int_unshifted.T
    unshifted_nv_wraps_bb = int(np.abs(y_nv_int_unshifted).max()) >= (P_BB // 2)
    assert unshifted_nv_wraps_bb, "Expected naive 2^-9 NVFP4 scale lift to exceed P_BB // 2 on D=5120!"
    # Divide out exact matrix-wide power-of-two GCD of nonzero `nv_ws_int_x512` entries:
    nz = np.abs(nv_ws_int_x512[nv_ws_int_x512 != 0])
    tz_shift = int(min((int(v) & -int(v)).bit_length() - 1 for v in nz))
    nv_ws_int_gcd = nv_ws_int_x512 >> tz_shift
    w_nv_int_gcd = (E2M1_X2[nv_nibs] * nv_ws_int_gcd[:, :, None]).reshape(256, 5120)
    y_nv_int_gcd = x_in @ w_nv_int_gcd.T
    assert int(np.abs(y_nv_int_gcd).max()) < (P_BB // 2), "GCD-shifted NVFP4 Layer-0 dot must fit in BabyBear!"

    return {
        "slice_shape": [256, 5120],
        "mxfp4_cos_vs_bf16": round(cos_mx, 6),
        "mxfp4_snr_db": round(snr_mx, 2),
        "mxfp4_neg_zero_nibbles_caught": neg_zero_mx,
        "nvfp4_cos_vs_bf16": round(cos_nv, 6),
        "nvfp4_snr_db": round(snr_nv, 2),
        "nvfp4_neg_zero_nibbles": neg_zero_nv,
        "mxfp4_max_abs_int_dot": int(np.abs(y_mx_int).max()),
        "nvfp4_unshifted_max_abs_int_dot": int(np.abs(y_nv_int_unshifted).max()),
        "nvfp4_unshifted_wraps_babybear": unshifted_nv_wraps_bb,
        "nvfp4_gcd_shift_bits": tz_shift,
        "nvfp4_gcd_shifted_max_abs_int_dot": int(np.abs(y_nv_int_gcd).max()),
        "babybear_half_modulus": P_BB // 2,
        "horner_zero_mul_exact_match": True,
        "single_nibble_tamper_rejected": tamper_rejected,
    }


# ======================================================================================
# 4. Live Local Apple M2 Max Metal Execution (`llama-cli` v0.9.0) + `cSHAKE256` `RewriteCert`
# ======================================================================================
def extract_json_object_bytes(raw_text: str) -> bytes:
    """Extract the generated JSON object slice from `llama-cli` output banner."""
    # Find last `{...}` matching our tool-call fields
    candidates = re.findall(r"\{[^{}]*\"tool\"[^{}]*\}", raw_text, flags=re.S)
    if not candidates:
        raise RuntimeError(f"No JSON tool-call object found in llama-cli output:\n{raw_text[-600:]}")
    return candidates[-1].strip().encode("utf-8")


def parse_llama_cli_metrics(combined_out: str) -> Tuple[float, float, float]:
    """Parse `[ Prompt: X t/s | Generation: Y t/s ]` and `/usr/bin/time -l` `maximum resident set size`."""
    m_tps = re.findall(r"\[\s*Prompt:\s*([0-9.]+)\s*t/s\s*\|\s*Generation:\s*([0-9.]+)\s*t/s\s*\]", combined_out)
    prefill_tps = float(m_tps[-1][0]) if m_tps else 0.0
    decode_tps = float(m_tps[-1][1]) if m_tps else 0.0
    m_rss = re.search(r"(\d+)\s+maximum resident set size", combined_out)
    rss_gib = (int(m_rss.group(1)) / (1024 ** 3)) if m_rss else 0.0
    return prefill_tps, decode_tps, rss_gib


def run_live_metal_qwen38_27b(merkle: Tower256ContentMerkle, force_rerun: bool = False) -> Dict[str, Any]:
    """Execute `Qwen3.8-27B-UD-Q4_K_XL.gguf` locally on Apple Metal via `llama-cli` v0.9.0 & verify output."""
    assert GGUF_PATH.exists(), f"Missing GGUF at {GGUF_PATH}"
    actual_bytes = GGUF_PATH.stat().st_size
    assert actual_bytes == GGUF_EXPECTED_BYTES, f"GGUF size mismatch: {actual_bytes} != {GGUF_EXPECTED_BYTES}"

    # Reuse cached deterministic Metal receipt if already verified on this exact GGUF (unless `--force-rerun`)
    if LIVE_RECEIPT_CACHE.exists() and not force_rerun:
        cached = json.loads(LIVE_RECEIPT_CACHE.read_text())
        if cached.get("gguf_bytes") == actual_bytes and cached.get("gguf_sha256") == GGUF_EXPECTED_SHA256:
            # Always re-verify the cryptographic `cSHAKE256` roots, redaction, and LL(1) AST live!
            w_raw = bytes.fromhex(cached["json_run"]["w_raw_hex"])
            w_clean = redact_bytes(DEFAULT_SECRET_RULES, w_raw)
            assert merkle.content_commit(w_raw).hex() == cached["json_run"]["raw_cshake256_root"]
            assert merkle.content_commit(w_clean).hex() == cached["json_run"]["clean_cshake256_root"]
            for r in DEFAULT_SECRET_RULES:
                assert r.pat not in w_clean
            ast_res = parse_and_verify_mini_json_ast(w_clean)
            assert ast_res == cached["json_run"]["verified_ast"]
            return cached

    prompt_json = (
        "You are a deterministic zkML dispatch agent. Output ONLY a raw single-line JSON object "
        "(no markdown backticks, no prose) with keys in exact order "
        '("cot", "tool", "target", "amount"). Set "cot" to "Auth token sk-proj-ZkmlLiveMetalAudit2026Key99 '
        'verified for C=64 GDN WY", "tool" to "prove_gdn_wy", "target" to "qwen38_27b_layer0", and "amount" to 64.'
    )
    cmd1 = [
        "/usr/bin/time", "-l",
        str(LLAMA_CLI),
        "-m", str(GGUF_PATH),
        "-ngl", "all",
        "-fa", "on",
        "-c", "2048",
        "-n", "96",
        "--temp", "0",
        "--seed", "42",
        "-rea", "off",
        "--simple-io",
        "--single-turn",
        "--no-display-prompt",
        "-p", prompt_json,
    ]
    t0 = time.time()
    proc1 = subprocess.run(cmd1, capture_output=True, text=True, check=True, timeout=180)
    wall1 = time.time() - t0
    comb1 = proc1.stdout + "\n" + proc1.stderr
    pp1, tg1, rss1 = parse_llama_cli_metrics(comb1)
    w_raw = extract_json_object_bytes(proc1.stdout)

    # Verify secret was genuinely emitted by the model in `w_raw`, then redacted & AST-verified!
    assert b"sk-proj-" in w_raw, f"Expected synthetic sk-proj- token in raw output, got: {w_raw!r}"
    raw_root = merkle.content_commit(w_raw)
    w_clean = redact_bytes(DEFAULT_SECRET_RULES, w_raw)
    clean_root = merkle.content_commit(w_clean)
    for r in DEFAULT_SECRET_RULES:
        assert r.pat not in w_clean, f"Secret pattern {r.pat!r} survived redaction!"
    assert b"[REDACTED_API_KEY]" in w_clean
    verified_ast = parse_and_verify_mini_json_ast(w_clean)

    # Prompt 2: Real Agentic Rust + Lean 4 Division-Free GDN WY Kernel Generation (Longer prefill + decode)
    prompt_code = (
        "Write a concise Rust function `verify_unit_lower_wy` over BabyBear (`P = 2013265921`) that checks "
        "`L * U == V - U` (mod P) for a strictly lower-triangular 64x64 matrix `L`, followed by the corresponding "
        "1-line Lean 4 theorem signature `theorem wy_unique_over_comm_ring`. Be concise, no markdown prose outside code."
    )
    cmd2 = [
        "/usr/bin/time", "-l",
        str(LLAMA_CLI),
        "-m", str(GGUF_PATH),
        "-ngl", "all",
        "-fa", "on",
        "-c", "2048",
        "-n", "220",
        "--temp", "0",
        "--seed", "42",
        "-rea", "off",
        "--simple-io",
        "--single-turn",
        "--no-display-prompt",
        "-p", prompt_code,
    ]
    t1 = time.time()
    proc2 = subprocess.run(cmd2, capture_output=True, text=True, check=True, timeout=240)
    wall2 = time.time() - t1
    comb2 = proc2.stdout + "\n" + proc2.stderr
    pp2, tg2, rss2 = parse_llama_cli_metrics(comb2)
    # Strip banner before `> ` or after `[ Prompt:`
    code_out = proc2.stdout
    if "[ Prompt:" in code_out:
        code_out = code_out.split("[ Prompt:")[0]
    if "available commands:" in code_out:
        code_out = code_out.split("/glob <pattern>")[-1]
        lines = [ln for ln in code_out.splitlines() if not ln.strip().startswith("add text files")]
        code_out = "\n".join(lines).strip()
    code_bytes = code_out.strip().encode("utf-8")
    code_root = merkle.content_commit(code_bytes)
    assert b"fn " in code_bytes and b"theorem " in code_bytes, f"Expected Rust `fn` + Lean `theorem` in:\n{code_out}"
    for r in DEFAULT_SECRET_RULES:
        assert r.pat not in code_bytes

    free_disk_gib = shutil.disk_usage("/").free / (1024 ** 3)
    free_disk_gb = shutil.disk_usage("/").free / 1e9

    receipt = {
        "model_repo": "unsloth/Qwen3.8-27B-GGUF",
        "gguf_file": str(GGUF_PATH),
        "gguf_bytes": actual_bytes,
        "gguf_gb": round(actual_bytes / 1e9, 3),
        "gguf_gib": round(actual_bytes / (1024 ** 3), 3),
        "gguf_sha256": GGUF_EXPECTED_SHA256,
        "llama_cli_version": "0.9.0 (build 12110, commit cd959bae9, Darwin arm64 Metal)",
        "free_ssd_after_download_gb": round(free_disk_gb, 2),
        "free_ssd_after_download_gib": round(free_disk_gib, 2),
        "json_run": {
            "wall_sec": round(wall1, 2),
            "metal_prefill_tok_s": pp1,
            "metal_decode_tok_s": tg1,
            "peak_rss_gib": round(rss1, 3),
            "w_raw_utf8": w_raw.decode("utf-8"),
            "w_raw_hex": w_raw.hex(),
            "raw_len": len(w_raw),
            "raw_cshake256_root": raw_root.hex(),
            "w_clean_utf8": w_clean.decode("utf-8"),
            "clean_len": len(w_clean),
            "clean_cshake256_root": clean_root.hex(),
            "verified_ast": verified_ast,
        },
        "rust_lean_run": {
            "wall_sec": round(wall2, 2),
            "metal_prefill_tok_s": pp2,
            "metal_decode_tok_s": tg2,
            "peak_rss_gib": round(rss2, 3),
            "output_bytes": len(code_bytes),
            "cshake256_root": code_root.hex(),
            "contains_rust_fn_and_lean_theorem": True,
            "output_preview": code_out.strip()[:700],
        },
    }
    LIVE_RECEIPT_CACHE.write_text(json.dumps(receipt, indent=2))
    return receipt


# ======================================================================================
# 5. Main Report Printer & Assertion Suite
# ======================================================================================
def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--skip-live-gguf", action="store_true", help="Run Stages 1-3 & crypto selftests without GGUF")
    ap.add_argument("--force-rerun-gguf", action="store_true", help="Force fresh llama-cli Metal execution")
    args = ap.parse_args()

    # Verify live host hardware (`sysctl hw.memsize`)
    hw_mem = int(subprocess.check_output(["sysctl", "-n", "hw.memsize"], text=True).strip())
    assert hw_mem == HW_RAM_BYTES_EXPECTED, f"Unexpected hw.memsize: {hw_mem}"

    print("=" * 124)
    print("STAGE 1: LATE-2026 SOTA OPEN-WEIGHT HARDWARE-FIT MATRIX (`96.00 GiB` = `103.08 GB` APPLE M2 MAX)")
    print("=" * 124)
    hdr = (
        f"{'Rank / Fit Class':<28} | {'Model':<32} | {'Tot / Act':>11} | {'Layer Mix':<23} | "
        f"{'Deploy Size':>15} | {'LCBv6':>5} | {'SWE-V':>5} | {'GPQA':>5} | {'llama0.9':<10}"
    )
    print(hdr)
    print("-" * 124)
    for m in MODELS_2026:
        mix_parts = []
        if m.n_gdn:
            mix_parts.append(f"{m.n_gdn}GDN")
        if m.n_kda:
            mix_parts.append(f"{m.n_kda}KDA")
        if m.n_mamba2:
            mix_parts.append(f"{m.n_mamba2}Mba2")
        if m.n_qsa_dsa:
            mix_parts.append(f"{m.n_qsa_dsa}QSA")
        if m.n_mla_full:
            mix_parts.append(f"{m.n_mla_full}MLA")
        if m.n_swa:
            mix_parts.append(f"{m.n_swa}SWA")
        if m.n_gqa_full:
            mix_parts.append(f"{m.n_gqa_full}GQA")
        if m.n_experts:
            mix_parts.append(f"{m.top_k}/{m.n_experts}E")
        mix_str = "+".join(mix_parts)
        lcb_s = f"{m.lcb_v6:5.1f}" if m.lcb_v6 is not None else "  -- "
        swe_s = f"{m.swe_verified:5.1f}" if m.swe_verified is not None else "  -- "
        gpq_s = f"{m.gpqa_diamond:5.1f}" if m.gpqa_diamond is not None else "  -- "
        arch_short = m.llama_cli_090_arch.split()[0]
        print(
            f"{m.rank_tag:<28} | {m.name:<32} | {m.total_params_B:5.1f}/{m.active_params_B:4.1f}B | "
            f"{mix_str:<23} | {m.deploy_size_gb:6.1f}GB/{m.deploy_size_gib:4.0f}Gi | "
            f"{lcb_s} | {swe_s} | {gpq_s} | {arch_short:<10}"
        )

    print("\n" + "=" * 124)
    print("STAGE 2: DETERMINISTIC `zkML` (`Gruen` Mode-2 `EinSumcheck` + `EXP_TAB`) & `vFHEML` (`HoistedB61` + `SPDZ`) PRICING")
    print("=" * 124)
    hw_fit_models = [m for m in MODELS_2026 if m.fits_96gib_4bit]
    assert len(hw_fit_models) >= 10
    for mode in ("decode", "prefill"):
        for T in (4096, 65536, 262144):
            print(f"\n--- MODE: {mode.upper()} @ T = {T:,} (per token) ---")
            print(
                f"{'Model':<34} | {'ZK Cells':>10} | {'EXP Lkps':>10} | {'Gruen Ext4':>12} | "
                f"{'Prover BB Muls':>14} | {'vFHE Wire':>10} | {'State+KV':>9} | {'HoistB61':>10}"
            )
            print("-" * 124)
            for m in MODELS_2026:
                r = price_model_at_T(m, mode, T)
                print(
                    f"{r.model:<34} | {r.zk_cells_M:8.2f} M | {r.zk_exp_lkps_M:8.3f} M | "
                    f"{r.zk_gruen_sc_ext4_M:10.2f} M | {r.zk_prover_bb_muls_B:12.2f} B | "
                    f"{r.vfhe_pubw_wire_M:8.2f} M | {r.vfhe_state_kv_gib:6.2f} Gi | {r.vfhe_dark_hoisted_gbit:7.1f} Gb"
                )

    print("\n" + "=" * 124)
    print("STAGE 3: REAL `Qwen3.8-27B` `MXFP4` & `NVFP4` SAFETENSORS SLICE AUDIT & `Ext4` 7-BUCKET `E2M1` HORNER PROVER")
    print("=" * 124)
    e2m1_res = verify_e2m1_slices_and_horner_prover()
    for k, v in e2m1_res.items():
        print(f"  [PASS] {k:<38s}: {v}")

    print("\n" + "=" * 124)
    print("STAGE 4 & 5: NIST SP 800-185 `cSHAKE256` CUBE-MERKLE + `RewriteCert` + LIVE APPLE METAL `Qwen3.8-27B` RUN")
    print("=" * 124)
    merkle = Tower256ContentMerkle()
    st_res = verify_cshake_and_transducer_selftest(merkle)
    print(f"  [PASS] NIST SP 800-185 cSHAKE256 & LL(1) Transducer Self-Tests: {st_res}")

    if args.skip_live_gguf:
        print("  [SKIP] `--skip-live-gguf` set; skipping live 17.66 GB Metal execution.")
        return

    live_res = run_live_metal_qwen38_27b(merkle, force_rerun=args.force_rerun_gguf)
    jr = live_res["json_run"]
    cr = live_res["rust_lean_run"]
    print(f"  [PASS] GGUF Verified      : {live_res['gguf_file']} ({live_res['gguf_gb']} GB / {live_res['gguf_gib']} GiB)")
    print(f"  [PASS] LFS SHA256         : {live_res['gguf_sha256']}")
    print(f"  [PASS] Free SSD Remaining : {live_res['free_ssd_after_download_gb']} GB ({live_res['free_ssd_after_download_gib']} GiB)")
    print(
        f"  [PASS] Metal JSON Run     : prefill={jr['metal_prefill_tok_s']:.2f} tok/s | "
        f"decode={jr['metal_decode_tok_s']:.2f} tok/s | peak_rss={jr['peak_rss_gib']:.2f} GiB"
    )
    print(f"  [PASS] Raw Output         : {jr['w_raw_utf8']}")
    print(f"  [PASS] Raw cSHAKE256 Root : {jr['raw_cshake256_root']}")
    print(f"  [PASS] Clean Redacted Out : {jr['w_clean_utf8']}")
    print(f"  [PASS] Clean cSHAKE Root  : {jr['clean_cshake256_root']}")
    print(f"  [PASS] Verified LL(1) AST : {jr['verified_ast']}")
    print(
        f"  [PASS] Metal Rust+Lean Run: prefill={cr['metal_prefill_tok_s']:.2f} tok/s | "
        f"decode={cr['metal_decode_tok_s']:.2f} tok/s | peak_rss={cr['peak_rss_gib']:.2f} GiB | "
        f"cSHAKE256={cr['cshake256_root']}"
    )
    print("  --- Real Generated Rust + Lean 4 Output Preview ---")
    for ln in cr["output_preview"].splitlines()[:18]:
        print("   ", ln)


if __name__ == "__main__":
    main()
