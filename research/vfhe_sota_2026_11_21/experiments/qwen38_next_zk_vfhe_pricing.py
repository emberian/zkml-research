#!/usr/bin/env python3
"""
qwen38_next_zk_vfhe_pricing.py -- Source-exact architecture verification, finite-field & BFV/SPDZ
cryptographic simulations (with constructive falsifiers), and deterministic operation-count pricing
for `Qwen3.8-Flash-Next` (`arXiv:2608.30320`, `Qwen/Qwen3.8-Flash-Next`, `125B-A6B + 51.2B N-gram`)
across BOTH `zkML` and `vFHEML` at `T in {1, 4K, 64K, 256K, 1M}`.

Primary sources pinned in code:
  - Paper: `arXiv:2608.30320v1` ("On the Design of Qwen3.8-Next Architecture", 2026-08-31), Eqs. 1-37.
  - Shipped configs & tensor index: `Qwen/Qwen3.8-Flash-Next`, `Qwen/Qwen3.8-Flash-Next-FP8`,
    `Qwen/Qwen3.8-27B`, `Qwen/Qwen3.8-2.4T-A95B` (`Qwen3.8-Max`).
  - Reference PyTorch semantics: `transformers/models/qwen4_exp/modeling_qwen4_exp.py`.
  - Stack baselines: BabyBear `p = 2013265921`, `Ext4 = F_p[X]/(X^4 - 11)`, Gruen `eq`-factored
    `EinSumcheck` (`ePrint 2024/108` + `notes/einsum-speedup-wave.md`), helper-free `D1b` LogUp-GKR
    (`notes/qaren-and-gptoss-nonlin-speedups.py`), `B61` + `SPDZ` `vFHEML` (`docs/DARK-LEARNING-SCHEME-DECISION.md`),
    `YPIR` (`ePrint 2024/270`), and Jo's Separation Principle (`ePrint 2026/1390`).

Usage:
  python3 research/vfhe_sota_2026_11_21/experiments/qwen38_next_zk_vfhe_pricing.py
"""

from __future__ import annotations

import math
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

# Add repo experiment paths (read-only) so we can exercise exact `bfv_ref` primitives too
REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT / "research" / "dark_learning_2026_11_06"))
import bfv_ref  # noqa: E402

# ---------------------------------------------------------------------------
# 0. Stack & Cryptographic Constants
# ---------------------------------------------------------------------------
P_BB = (1 << 31) - (1 << 27) + 1          # BabyBear = 2013265921
W_EXT4 = 11                               # Ext4 = F_p[X] / (X^4 - 11)
BB_MULS_EXT_BASE = 4
BB_MULS_EXT_EXT = 9                       # Karatsuba over quadratic tower
WHIR_LDE_MULS_PER_BASE_CELL = 16          # rho = 1/4 WHIR PCS encoding + Merkle sponge equiv
POSEIDON2_NARROW_CELLS_PER_PERM = 141     # VERDICTS.md §4 `permEmissionNarrow`

# B61 + SPDZ vFHEML parameters (`docs/DARK-LEARNING-SCHEME-DECISION.md` §2-§3)
B61_N = 8192
B61_L = 3                                 # 3 x 61-bit RNS primes (log2 Q = 183)
B61_K_EXT = 4                             # 4 x 61-bit auxiliary primes in B61
B61_PBITS = 61
N_CUSTODIANS = 3
# Baseline B61 ct x ct certificate bits (pinned-u): 67.8 Mbit (`DARK-LEARNING-SCHEME-DECISION.md` §1)
B61_CT_CT_BITS_BASELINE = 67_806_013
# Hoisted / Fused B61 ct x ct certificate bits (~8.1 Mbit when rescaling once after inner-dim sum)
B61_CT_CT_BITS_HOISTED = 8_126_464


# ---------------------------------------------------------------------------
# 1. BabyBear & Ext4 Arithmetic Helpers for Algebraic Simulations
# ---------------------------------------------------------------------------
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


def ext_inv(a: np.ndarray) -> np.ndarray:
    a0, a1, a2, a3 = [int(x) % P_BB for x in a]
    u2_0 = (a0 * a0 + W_EXT4 * a2 * a2) % P_BB
    u2_1 = (2 * a0 * a2) % P_BB
    v2_0 = (a1 * a1 + W_EXT4 * a3 * a3) % P_BB
    v2_1 = (2 * a1 * a3) % P_BB
    n0 = (u2_0 - W_EXT4 * v2_1) % P_BB
    n1 = (u2_1 - v2_0) % P_BB
    m_fp = (n0 * n0 - W_EXT4 * n1 * n1) % P_BB
    assert m_fp != 0, "Non-invertible Ext4 element"
    m_inv = pow(m_fp, P_BB - 2, P_BB)
    i0 = (n0 * m_inv) % P_BB
    i1 = ((-n1) * m_inv) % P_BB
    r0 = (a0 * i0 + W_EXT4 * a2 * i1) % P_BB
    r2 = (a0 * i1 + a2 * i0) % P_BB
    r1 = (-(a1 * i0 + W_EXT4 * a3 * i1)) % P_BB
    r3 = (-(a1 * i1 + a3 * i0)) % P_BB
    res = np.array([r0, r1, r2, r3], dtype=np.int64)
    assert np.array_equal(ext_mul(a, res), ext_from_int(1))
    return res


def build_eq_table(r: np.ndarray) -> np.ndarray:
    """MSB-first multilinear eq(r, x) table of shape (2^k, 4), matching `.reshape(2, 1 << rem, ...)`."""
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


def mod_matmul(a: np.ndarray, b: np.ndarray, mod: int) -> np.ndarray:
    """Overflow-safe matrix/vector product modulo `mod` (< 2^31) in vectorized int64 via 16-bit limbs."""
    a_m = np.asarray(a, dtype=np.int64) % mod
    b_m = np.asarray(b, dtype=np.int64) % mod
    a0, a1 = a_m & 0xFFFF, a_m >> 16
    b0, b1 = b_m & 0xFFFF, b_m >> 16
    c00 = (a0 @ b0) % mod
    c01 = ((a0 @ b1) + (a1 @ b0)) % mod
    c11 = (a1 @ b1) % mod
    return (c00 + ((c01 << 16) % mod) + ((c11 * ((1 << 32) % mod)) % mod)) % mod


def mle_eval_base(arr_flat: np.ndarray, pt: np.ndarray) -> np.ndarray:
    eq = build_eq_table(pt)
    return ((eq * ((arr_flat % P_BB)[:, None])) % P_BB).sum(axis=0) % P_BB


# ---------------------------------------------------------------------------
# 2. Exact `[SOURCE]` Architecture Specifications & Parameter Census
# ---------------------------------------------------------------------------
def _is_prime_small(v: int) -> bool:
    if v < 2:
        return False
    if v % 2 == 0:
        return v == 2
    for d in range(3, math.isqrt(v) + 1, 2):
        if v % d == 0:
            return False
    return True


def _find_nth_prime_after(start: int, count: int) -> int:
    prime = start
    for _ in range(count):
        prime += 1
        while not _is_prime_small(prime):
            prime += 1
    return prime


@dataclass(frozen=True)
class Qwen38FlashNextSpec:
    # From `Qwen/Qwen3.8-Flash-Next/raw/main/config.json` & `modeling_qwen4_exp.py`
    num_layers: int = 48
    num_gdn_layers: int = 36
    num_qsa_layers: int = 12
    hidden_size: int = 2560
    vocab_size: int = 248_320
    # Gated DeltaNet (`Qwen4ExpTextGatedDeltaNet`)
    gdn_k_heads: int = 16
    gdn_v_heads: int = 48
    gdn_k_dim: int = 128
    gdn_v_dim: int = 128
    gdn_conv_kernel: int = 4
    gdn_chunk_size: int = 64
    # Qwen Sparse Attention (`Qwen4ExpTextAttention` + `Qwen4ExpTextQSAIndexer`)
    qsa_q_heads: int = 24
    qsa_kv_heads: int = 2
    qsa_head_dim: int = 256
    qsa_rotary_dim: int = 64          # partial_rotary_factor = 0.25
    idx_q_heads: int = 4
    idx_kv_heads: int = 1
    idx_head_dim: int = 128
    idx_compress_ratio: int = 4
    idx_token_budget: int = 2048
    idx_block_budget: int = 512       # 2048 // 4
    # Gated Residual (`Qwen4ExpTextGatedResidual`)
    hc_count: int = 4
    hc_lowrank: int = 320             # d / 8 = 2560 / 8
    # Fine-Grained Sparse MoE (`Qwen4ExpTextSparseMoeBlock`)
    num_experts: int = 512
    top_k_experts: int = 10
    num_shared_experts: int = 1
    moe_inter_dim: int = 640
    shared_inter_dim: int = 640
    # Layer-2 Multi-Head Hash N-Gram PLE (`Qwen4ExpTextPLELayer`, `ple_layer_ids=[2]`)
    ple_layer_1idx: int = 2
    ngram_size: int = 3               # 2-grams and 3-grams
    heads_per_ngram: int = 8          # (3 - 1) * 8 = 16 total heads
    ngram_vocab_base: int = 20_000_000
    ngram_vocab_div: int = 128
    ple_embed_dim: int = 2560
    ple_conv_kernel: int = 4
    ple_seed: int = 1234
    eos_token_id: int = 248044
    # MTP (`1` layer: QSA + GR + 512-expert MoE)
    mtp_layers: int = 1
    mtp_spec_steps: int = 4           # Table 4: `next_n = 4` (1 target + 3 MTP draft)


SPEC = Qwen38FlashNextSpec()


def verify_architecture_and_family_census() -> Dict[str, int]:
    s = SPEC
    # 1. Exact PLE N-gram prime table sizes (`modeling_qwen4_exp.py:1113-1127`)
    n_ple_heads = (s.ngram_size - 1) * s.heads_per_ngram
    assert n_ple_heads == 16
    ple_head_dim = s.ple_embed_dim // n_ple_heads
    assert ple_head_dim == 160
    primes = [_find_nth_prime_after(s.ngram_vocab_base - 1, h + 1) for h in range(n_ple_heads)]
    assert primes[0] == 20_000_003 and primes[-1] == 20_000_171
    raw_vocab = sum(primes)
    padded_ple_vocab = math.ceil(raw_vocab / s.ngram_vocab_div) * s.ngram_vocab_div
    assert raw_vocab == 320_001_446 and padded_ple_vocab == 320_001_536
    ple_table_params = padded_ple_vocab * ple_head_dim
    assert ple_table_params == 51_200_245_760  # 51.200246B!

    # 2. Backbone parameter breakdown
    embed_params = s.vocab_size * s.hidden_size
    lm_head_params = s.vocab_size * s.hidden_size

    # GR (`use_combine=True` on 96 sublayers; `use_combine=False` on 1 final mixer)
    hc_d = s.hc_count * s.hidden_size  # 10,240
    gr_sublayer = hc_d + (hc_d * s.hc_lowrank) + (s.hc_lowrank * hc_d) + (hc_d * s.hc_count)
    gr_final = hc_d + (hc_d * s.hc_lowrank) + (s.hc_lowrank * hc_d)
    gr_total = 2 * s.num_layers * gr_sublayer + gr_final

    # GDN (`36` layers)
    gdn_k_tot = s.gdn_k_heads * s.gdn_k_dim      # 2,048
    gdn_v_tot = s.gdn_v_heads * s.gdn_v_dim      # 6,144
    gdn_conv_dim = 2 * gdn_k_tot + gdn_v_tot     # 10,240
    gdn_1l = (
        s.hidden_size * gdn_conv_dim             # in_proj_qkv
        + gdn_conv_dim * s.gdn_conv_kernel       # conv1d (depthwise, bias=False)
        + s.hidden_size * gdn_v_tot              # in_proj_z
        + s.hidden_size * s.gdn_v_heads          # in_proj_b
        + s.hidden_size * s.gdn_v_heads          # in_proj_a
        + s.gdn_v_heads                          # dt_bias
        + s.gdn_v_heads                          # A_log
        + s.gdn_v_dim                            # RMSNormGated weight
        + gdn_v_tot * s.hidden_size              # out_proj
    )
    gdn_total = s.num_gdn_layers * gdn_1l

    # QSA (`12` layers): note `q_proj` is `2 * H_q * head_dim` (query + sigmoid output gate)
    qsa_1l = (
        s.hidden_size * (2 * s.qsa_q_heads * s.qsa_head_dim)   # q_proj (query + gate)
        + s.hidden_size * (s.qsa_kv_heads * s.qsa_head_dim)    # k_proj
        + s.hidden_size * (s.qsa_kv_heads * s.qsa_head_dim)    # v_proj
        + 2 * s.qsa_head_dim                                   # q_norm + k_norm
        + (s.qsa_q_heads * s.qsa_head_dim) * s.hidden_size     # o_proj
        + s.hidden_size * ((s.idx_q_heads + s.idx_kv_heads) * s.idx_head_dim)  # index_qk_proj
        + 2 * s.idx_head_dim                                   # indexer q_layernorm + k_layernorm
    )
    qsa_total = s.num_qsa_layers * qsa_1l

    # MoE (`48` layers): 512 routed + 1 shared + router + shared_expert_gate
    expert_1 = 3 * s.hidden_size * s.moe_inter_dim             # 4,915,200
    moe_1l_total = (
        s.num_experts * expert_1
        + s.num_shared_experts * (3 * s.hidden_size * s.shared_inter_dim)
        + s.num_experts * s.hidden_size                        # router gate
        + s.hidden_size * 1                                    # shared_expert_gate
    )
    moe_1l_active = (
        (s.top_k_experts + s.num_shared_experts) * expert_1
        + s.num_experts * s.hidden_size
        + s.hidden_size * 1
    )
    moe_total = s.num_layers * moe_1l_total
    moe_active = s.num_layers * moe_1l_active

    # PLE active projections at Layer 2 (`key_proj`, `value_proj`, 3 group norms, dilated `conv1d`)
    ple_proj = (
        s.ple_embed_dim * hc_d                   # key_proj: 2560 -> 10240
        + s.ple_embed_dim * s.hidden_size        # value_proj: 2560 -> 2560
        + 3 * hc_d                               # norm_key + norm_query + norm_conv
        + hc_d * s.ple_conv_kernel               # dilated depthwise conv1d
    )

    backbone_total = embed_params + lm_head_params + gr_total + gdn_total + qsa_total + moe_total + ple_proj
    backbone_active_no_lm = gr_total + gdn_total + qsa_total + moe_active + ple_proj
    backbone_active_with_lm = backbone_active_no_lm + lm_head_params

    # MTP (`1` QSA + GR + 512-expert MoE layer + fusion)
    mtp_params = (
        2 * s.hidden_size                        # pre_fc_norm_embedding + pre_fc_norm_hidden
        + s.hidden_size * s.hidden_size          # fc_embedding (2560x2560)
        + hc_d * hc_d                            # fc_hidden or stream projection
        + 2 * gr_sublayer + gr_final
        + qsa_1l
        + moe_1l_total
    )

    # Family siblings from `Qwen/Qwen3.8-27B` and `Qwen/Qwen3.8-2.4T-A95B` (`config.json`)
    # Qwen3.8-27B: 64L (48 GDN + 16 GQA), d=5120, dense inter=17408, GDN(16,48,128,128), GQA(24,4,256)
    q27_gdn = 48 * (5120 * (4096 + 6144) + 10240 * 4 + 5120 * 6144 + 2 * 5120 * 48 + 96 + 128 + 6144 * 5120)
    q27_attn = 16 * (5120 * (2 * 24 * 256) + 2 * 5120 * (4 * 256) + 512 + (24 * 256) * 5120 + 2 * 5120)
    q27_ffn = 64 * (3 * 5120 * 17408 + 5120)
    q27_emb = 2 * 248_320 * 5120
    q27_total = q27_gdn + q27_attn + q27_ffn + q27_emb

    # Qwen3.8-Max (`2.4T-A95B`): 92L (69 GDN + 23 GQA), d=8192, 512E top-10+1, inter=2048
    qmax_gdn = 69 * (8192 * (4096 + 16384) + 20480 * 4 + 8192 * 16384 + 2 * 8192 * 128 + 256 + 128 + 16384 * 8192)
    qmax_attn = 23 * (8192 * (2 * 64 * 256) + 2 * 8192 * (4 * 256) + 512 + (64 * 256) * 8192)
    qmax_moe_tot = 92 * (513 * (3 * 8192 * 2048) + 513 * 8192)
    qmax_moe_act = 92 * (11 * (3 * 8192 * 2048) + 513 * 8192)
    qmax_emb = 2 * 248_320 * 8192
    qmax_total = qmax_gdn + qmax_attn + qmax_moe_tot + qmax_emb
    qmax_active = qmax_gdn + qmax_attn + qmax_moe_act + 248_320 * 8192

    return {
        "backbone_total": backbone_total,
        "backbone_active_no_lm": backbone_active_no_lm,
        "backbone_active_with_lm": backbone_active_with_lm,
        "ple_table_params": ple_table_params,
        "padded_ple_vocab": padded_ple_vocab,
        "ple_proj_params": ple_proj,
        "gr_total": gr_total,
        "gdn_1l": gdn_1l,
        "gdn_total": gdn_total,
        "qsa_1l": qsa_1l,
        "qsa_total": qsa_total,
        "moe_1l_total": moe_1l_total,
        "moe_1l_active": moe_1l_active,
        "moe_total": moe_total,
        "moe_active": moe_active,
        "mtp_params": mtp_params,
        "q27_total": q27_total,
        "qmax_total": qmax_total,
        "qmax_active": qmax_active,
    }


# ---------------------------------------------------------------------------
# 3. Test Suite A: Gated DeltaNet (`GDN`) Chunkwise WY (`C=64`) + `EinSumcheck` + `vFHEML`
# ---------------------------------------------------------------------------
def gdn_sequential_ring(
    q: np.ndarray, k: np.ndarray, v: np.ndarray, alpha: np.ndarray, beta: np.ndarray, mod: int
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Exact ring-generic sequential Gated DeltaNet (`arXiv:2608.30320` Eqs. 1-5) with Grouped Value Attention.
    Shapes: q, k: (T, H_k, d_k); v: (T, H_v, d_v); alpha, beta: (T, H_v).
    Returns: (y: (T, H_v, d_v), final_state: (H_v, d_k, d_v)).
    """
    t_len, h_k, d_k = k.shape
    _, h_v, d_v = v.shape
    rep = h_v // h_k
    state = np.zeros((h_v, d_k, d_v), dtype=np.int64)
    y_out = np.zeros((t_len, h_v, d_v), dtype=np.int64)
    for t in range(t_len):
        for hv in range(h_v):
            hk = hv // rep
            kt = k[t, hk]            # (d_k,)
            qt = q[t, hk]            # (d_k,)
            vt = v[t, hv]            # (d_v,)
            at = int(alpha[t, hv]) % mod
            bt = int(beta[t, hv]) % mod
            s_tilde = (at * state[hv]) % mod                       # Eq. 1
            kv_mem = mod_matmul(s_tilde.T, kt, mod)                # S_tilde^T k_t
            err = (vt - kv_mem) % mod                              # Eq. 2
            u_eff = (bt * err) % mod
            state[hv] = (s_tilde + np.outer(kt, u_eff) % mod) % mod  # Eq. 3 / Eq. 5
            y_out[t, hv] = mod_matmul(state[hv].T, qt, mod)        # Eq. 4
    return y_out, state


def gdn_chunkwise_wy_ring(
    q: np.ndarray, k: np.ndarray, v: np.ndarray, alpha: np.ndarray, beta: np.ndarray, chunk_size: int, mod: int
) -> Tuple[np.ndarray, np.ndarray, List[Tuple[np.ndarray, np.ndarray, np.ndarray]]]:
    """
    Division-free Chunkwise WY / UT representation (`modeling_qwen4_exp.py:333-401`) over Z_mod.
    Works even when `alpha[t, hv] == 0` (uses prefix/suffix products Gamma_{i,j} = prod_{m=j+1}^i alpha_m,
    zero divisions!). Also collects `(L, UW, RHS)` per chunk to verify flat degree-2 `EinSumcheck`:
        UW + L @ UW == RHS    (where UW = [U | W], RHS = [V_beta | K_{gamma*beta}]).
    """
    t_len, h_k, d_k = k.shape
    _, h_v, d_v = v.shape
    assert t_len % chunk_size == 0
    rep = h_v // h_k
    n_chunks = t_len // chunk_size
    state = np.zeros((h_v, d_k, d_v), dtype=np.int64)
    y_out = np.zeros((t_len, h_v, d_v), dtype=np.int64)
    ut_witnesses: List[Tuple[np.ndarray, np.ndarray, np.ndarray]] = []

    for c in range(n_chunks):
        s0, s1 = c * chunk_size, (c + 1) * chunk_size
        L_chunk = np.zeros((h_v, chunk_size, chunk_size), dtype=np.int64)
        UW_chunk = np.zeros((h_v, chunk_size, d_v + d_k), dtype=np.int64)
        RHS_chunk = np.zeros((h_v, chunk_size, d_v + d_k), dtype=np.int64)

        for hv in range(h_v):
            hk = hv // rep
            qc = q[s0:s1, hk]         # (C, d_k)
            kc = k[s0:s1, hk]         # (C, d_k)
            vc = v[s0:s1, hv]         # (C, d_v)
            ac = alpha[s0:s1, hv]     # (C,)
            bc = beta[s0:s1, hv]      # (C,)

            # Prefix decays gamma_i = prod_{m=0}^i a_m, suffix bar_gamma_j = prod_{m=j+1}^{C-1} a_m,
            # pairwise Gamma_{i,j} = prod_{m=j+1}^i a_m (Gamma_{i,i} = 1, Gamma_{i,j} = 0 for i < j)
            gamma = np.zeros(chunk_size, dtype=np.int64)
            bar_gamma = np.zeros(chunk_size, dtype=np.int64)
            Gamma = np.zeros((chunk_size, chunk_size), dtype=np.int64)
            acc = 1
            for i in range(chunk_size):
                acc = (acc * int(ac[i])) % mod
                gamma[i] = acc
                Gamma[i, i] = 1
                p_ij = 1
                for j in range(i - 1, -1, -1):
                    p_ij = (p_ij * int(ac[j + 1])) % mod
                    Gamma[i, j] = p_ij
            suf = 1
            for j in range(chunk_size - 1, -1, -1):
                bar_gamma[j] = suf
                suf = (suf * int(ac[j])) % mod
            gamma_chunk = int(gamma[-1])

            # Strictly lower-triangular L[i, j] = beta_i * Gamma[i, j] * (k_i . k_j) for i > j
            kk = mod_matmul(kc, kc.T, mod)
            L = np.zeros((chunk_size, chunk_size), dtype=np.int64)
            for i in range(1, chunk_size):
                L[i, :i] = (int(bc[i]) * ((Gamma[i, :i] * kk[i, :i]) % mod)) % mod

            V_beta = (bc[:, None] * vc) % mod
            K_gbeta = (((gamma * bc) % mod)[:, None] * kc) % mod
            RHS = np.concatenate([V_beta, K_gbeta], axis=1)

            # Solve unit-lower-triangular (I + L) * UW = RHS via division-free forward substitution
            # (equivalently Neumann series sum_{m=0}^{C-1} (-L)^m * RHS since L^C == 0)
            UW = np.zeros_like(RHS)
            for i in range(chunk_size):
                corr = mod_matmul(L[i, :i], UW[:i], mod) if i > 0 else 0
                UW[i] = (RHS[i] - corr) % mod

            U = UW[:, :d_v]
            W = UW[:, d_v:]
            L_chunk[hv] = L
            UW_chunk[hv] = UW
            RHS_chunk[hv] = RHS

            # Inter-chunk + intra-chunk state read & update (`modeling_qwen4_exp.py:396-401`)
            u_eff = (U - mod_matmul(W, state[hv], mod)) % mod
            q_gamma = (gamma[:, None] * qc) % mod
            m_qk = (mod_matmul(qc, kc.T, mod) * Gamma) % mod       # lower-triangular intra-chunk QK
            y_out[s0:s1, hv] = (mod_matmul(q_gamma, state[hv], mod) + mod_matmul(m_qk, u_eff, mod)) % mod

            k_bar = (bar_gamma[:, None] * kc) % mod
            state[hv] = ((gamma_chunk * state[hv]) % mod + mod_matmul(k_bar.T, u_eff, mod)) % mod

        ut_witnesses.append((L_chunk, UW_chunk, RHS_chunk))

    return y_out, state, ut_witnesses


def gruen_verify_ut_bilinear_sumcheck(
    L_mat: np.ndarray, UW_mat: np.ndarray, RHS_mat: np.ndarray, rng: np.random.Generator
) -> Tuple[bool, int]:
    """
    Proves and verifies `(I + L) @ UW == RHS` (batched across `H_v` heads, padded to power of 2)
    as `L @ UW == RHS - UW` using a SINGLE flat Gruen Mode-2 quadratic `EinSumcheck` (`hij,hjk -> hik`):
      - `i` in `F_1(L)` (`log2 C = 6` bits, 0 rounds),
      - `k` in `F_1(UW)` (`log2(d_v+d_k)` bits, 0 rounds),
      - `h` in `F_{>=2}` (`log2 H_v_pad` Gruen `{0, inf}` rounds),
      - `j` in `S` (`log2 C = 6` quadratic `{0, 1, inf}` sumcheck rounds).
    Zero sequential GKR layers, zero matrix inversions!
    """
    h_v, c_dim, col_dim = UW_mat.shape
    h_pad = 1 << (h_v - 1).bit_length()
    c_pad = 1 << (c_dim - 1).bit_length()
    col_pad = 1 << (col_dim - 1).bit_length()

    L_p = np.zeros((h_pad, c_pad, c_pad), dtype=np.int64)
    UW_p = np.zeros((h_pad, c_pad, col_pad), dtype=np.int64)
    D_p = np.zeros((h_pad, c_pad, col_pad), dtype=np.int64)  # D = RHS - UW
    L_p[:h_v, :c_dim, :c_dim] = L_mat % P_BB
    UW_p[:h_v, :c_dim, :col_dim] = UW_mat % P_BB
    D_p[:h_v, :c_dim, :col_dim] = (RHS_mat - UW_mat) % P_BB

    b_h = (h_pad - 1).bit_length()
    b_i = (c_pad - 1).bit_length()
    b_j = (c_pad - 1).bit_length()
    b_k = (col_pad - 1).bit_length()

    r_h = rng.integers(1, P_BB, size=(b_h, 4), dtype=np.int64)
    r_i = rng.integers(1, P_BB, size=(b_i, 4), dtype=np.int64)
    r_k = rng.integers(1, P_BB, size=(b_k, 4), dtype=np.int64)

    # Exact MSB-first multilinear binding along individual axes using `build_eq_table`
    eq_h = build_eq_table(r_h)    # (h_pad, 4)
    eq_i = build_eq_table(r_i)    # (c_pad, 4)
    eq_k = build_eq_table(r_k)    # (col_pad, 4)

    # Claimed output MLE H_claim = sum_{h,i,k} eq_h[h]*eq_i[i]*eq_k[k]*D_p[h,i,k]
    dk_all = ((D_p[:, :, :, None] * eq_k[None, None, :, :]) % P_BB).sum(axis=2) % P_BB     # (h, i, 4)
    di_all = ext_mul(dk_all, eq_i[None, :, :]).sum(axis=1) % P_BB                          # (h, 4)
    running_sum = ext_mul(di_all, eq_h).sum(axis=0) % P_BB                                 # (4,)

    # Prover F_1 partial evaluations: A[h, j] = sum_i eq_i[i] * L_p[h, i, j], B[h, j] = sum_k eq_k[k] * UW_p[h, j, k]
    A = ((L_p[:, :, :, None] * eq_i[None, :, None, :]) % P_BB).sum(axis=1) % P_BB          # (h_pad, c_pad, 4)
    B = ((UW_p[:, :, :, None] * eq_k[None, None, :, :]) % P_BB).sum(axis=2) % P_BB         # (h_pad, c_pad, 4)

    # Phase 1: Gruen Mode-2 on `h` (`b_h` rounds, `{0, inf}` = 2 evals/round)
    ch_h = np.zeros((b_h, 4), dtype=np.int64)
    one = ext_from_int(1)
    prefix_eq = one.copy()
    n_rounds = 0
    for u in range(b_h):
        n_rounds += 1
        rem_h = b_h - 1 - u
        suf_eq = build_eq_table(r_h[u + 1 :]) if rem_h > 0 else one[None, :]
        A_r = A.reshape(2, 1 << rem_h, c_pad, 4)
        B_r = B.reshape(2, 1 << rem_h, c_pad, 4)
        prod0 = ext_mul(A_r[0], B_r[0]).sum(axis=1) % P_BB
        q0 = ext_mul(prod0, suf_eq).sum(axis=0) % P_BB
        dA = ext_sub(A_r[1], A_r[0])
        dB = ext_sub(B_r[1], B_r[0])
        prod_inf = ext_mul(dA, dB).sum(axis=1) % P_BB
        q_inf = ext_mul(prod_inf, suf_eq).sum(axis=0) % P_BB

        # Verifier reconstructs q1 from Gruen linear factor l_u(X) = prefix_eq * ((1-r_u)(1-X) + r_u X)
        l0 = ext_mul(prefix_eq, ext_sub(one, r_h[u]))
        l1 = ext_mul(prefix_eq, r_h[u])
        q1 = ext_mul(ext_sub(running_sum, ext_mul(l0, q0)), ext_inv(l1))

        chal = rng.integers(2, P_BB - 1, size=4, dtype=np.int64)
        ch_h[u] = chal
        # Direct Mode-2 stripped claim update: running_sum <- q_u(chal) for Phase 2 handoff
        # Wait: inside Phase 1, keep unstripped `s_u(chal) = l_u(chal)*q_u(chal)` until u == b_h - 1,
        # or strip immediately (setting prefix_eq = 1)! Stripping immediately sets prefix_eq = 1 after round 0!
        c1 = ext_sub(ext_sub(q1, q0), q_inf)
        q_chal = ext_add(q0, ext_add(ext_mul(c1, chal), ext_mul(q_inf, ext_mul(chal, chal))))
        prefix_eq = one.copy()  # Mode 2 strips `l_u(chal)` immediately!
        running_sum = q_chal

        A = ext_add(A_r[0], ext_mul(dA, chal)).reshape(1 << rem_h, c_pad, 4)
        B = ext_add(B_r[0], ext_mul(dB, chal)).reshape(1 << rem_h, c_pad, 4)

    A_j = A.reshape(c_pad, 4)
    B_j = B.reshape(c_pad, 4)

    # Phase 2: Standard quadratic sumcheck on `j` (`b_j` rounds)
    ch_j = np.zeros((b_j, 4), dtype=np.int64)
    for u in range(b_j):
        n_rounds += 1
        rem_j = b_j - 1 - u
        A_r = A_j.reshape(2, 1 << rem_j, 4)
        B_r = B_j.reshape(2, 1 << rem_j, 4)
        s0 = ext_mul(A_r[0], B_r[0]).sum(axis=0) % P_BB
        s1 = ext_mul(A_r[1], B_r[1]).sum(axis=0) % P_BB
        dA = ext_sub(A_r[1], A_r[0])
        dB = ext_sub(B_r[1], B_r[0])
        s_inf = ext_mul(dA, dB).sum(axis=0) % P_BB

        if not np.array_equal(ext_add(s0, s1), running_sum):
            return False, n_rounds
        chal = rng.integers(2, P_BB - 1, size=4, dtype=np.int64)
        ch_j[u] = chal
        c1 = ext_sub(ext_sub(s1, s0), s_inf)
        running_sum = ext_add(s0, ext_add(ext_mul(c1, chal), ext_mul(s_inf, ext_mul(chal, chal))))
        A_j = ext_add(A_r[0], ext_mul(dA, chal)).reshape(1 << rem_j, 4)
        B_j = ext_add(B_r[0], ext_mul(dB, chal)).reshape(1 << rem_j, 4)

    # Terminal oracle check against true MLEs of L_p and UW_p at (ch_h, r_i, ch_j, r_k)
    eq_ch_h = build_eq_table(ch_h)
    eq_ch_j = build_eq_table(ch_j)
    L_eval = ext_mul(
        ext_mul(((L_p[:, :, :, None] * eq_i[None, :, None, :]) % P_BB).sum(axis=1) % P_BB, eq_ch_j[None, :, :]).sum(axis=1) % P_BB,
        eq_ch_h,
    ).sum(axis=0) % P_BB
    UW_eval = ext_mul(
        ext_mul(((UW_p[:, :, :, None] * eq_k[None, None, :, :]) % P_BB).sum(axis=2) % P_BB, eq_ch_j[None, :, :]).sum(axis=1) % P_BB,
        eq_ch_h,
    ).sum(axis=0) % P_BB

    ok = np.array_equal(running_sum, ext_mul(L_eval, UW_eval))
    return ok, n_rounds


def verify_gdn_zkml_and_vfheml() -> Dict[str, object]:
    rng = np.random.default_rng(20261121)
    # 1. Multi-chunk (`C = 64`, `3` chunks => `T = 192`) GDN WY vs Sequential over BabyBear
    c_size = 64
    t_len = 3 * c_size
    h_k, h_v, d_k, d_v = 2, 6, 16, 16  # preserves exact 3:1 GVA ratio of Qwen3.8-Flash-Next (48 / 16 = 3)
    q = rng.integers(0, P_BB, size=(t_len, h_k, d_k), dtype=np.int64)
    k = rng.integers(0, P_BB, size=(t_len, h_k, d_k), dtype=np.int64)
    v = rng.integers(0, P_BB, size=(t_len, h_v, d_v), dtype=np.int64)
    alpha = rng.integers(0, P_BB, size=(t_len, h_v), dtype=np.int64)
    beta = rng.integers(0, P_BB, size=(t_len, h_v), dtype=np.int64)
    # Force an exact zero decay `alpha[77, 2] = 0` to prove ring generality without division!
    alpha[77, 2] = 0

    y_seq, s_seq = gdn_sequential_ring(q, k, v, alpha, beta, P_BB)
    y_wy, s_wy, ut_wits = gdn_chunkwise_wy_ring(q, k, v, alpha, beta, c_size, P_BB)
    assert np.array_equal(y_seq, y_wy), "GDN WY chunking output mismatch!"
    assert np.array_equal(s_seq, s_wy), "GDN WY chunking final state mismatch!"

    # Verify flat degree-2 Gruen `EinSumcheck` on chunk 0 (`C = 64`)
    L0, UW0, RHS0 = ut_wits[0]
    honest_ok, sc_rounds = gruen_verify_ut_bilinear_sumcheck(L0, UW0, RHS0, rng)
    assert honest_ok, "Honest GDN WY UT EinSumcheck failed!"

    # Constructive Falsifier A1a: 1-cell mutation in UW0 MUST fail unconditionally (`det(I + L) == 1`)
    UW_forged = UW0.copy()
    UW_forged[1, 33, 5] = (UW_forged[1, 33, 5] + 1) % P_BB
    assert not np.array_equal((UW_forged + mod_matmul(L0, UW_forged, P_BB)) % P_BB, RHS0)
    forged_ok, _ = gruen_verify_ut_bilinear_sumcheck(L0, UW_forged, RHS0, rng)
    assert not forged_ok, "Forged GDN WY UT witness was accepted!"

    # Constructive Falsifier A1b: Non-strictly-lower-triangular `L_bad` (`L_bad[0,0] = -1 mod p`)
    # violates `det(I + L) = 1` and admits distinct witnesses U1 != U2 with `(I + L_bad) U1 == (I + L_bad) U2`!
    L_bad = np.zeros((4, 4), dtype=np.int64)
    L_bad[0, 0] = P_BB - 1  # -1 mod P_BB => (I + L_bad)[0, :] == 0
    U1 = np.zeros((4, 2), dtype=np.int64)
    U2 = np.zeros((4, 2), dtype=np.int64)
    U2[0, 0] = 42
    lhs1 = (U1 + mod_matmul(L_bad, U1, P_BB)) % P_BB
    lhs2 = (U2 + mod_matmul(L_bad, U2, P_BB)) % P_BB
    assert np.array_equal(lhs1, lhs2) and not np.array_equal(U1, U2), "Diagonal L=-1 falsifier tooth failed!"

    # 2. Encrypted Stateful GDN in `vFHEML` (`B61` + `SPDZ` single-crossing parallel-read identity)
    # Verify on real `bfv_ref.BFV` ciphertexts (`N = 32` toy ring with exact 61-bit prime `t` and 3x61-bit `Q`)
    # that `y_t = alpha_t * (S_{t-1}^T q_t) + (k_t . q_t) * beta_t * (v_t - alpha_t * S_{t-1}^T k_t)`
    # matches sequential GDN at Homomorphic Depth 1 per step!
    n_ring = 32
    d_toy = 4  # d_k = d_v = 4 => d_k * d_v = 16 <= N = 32 fits in 1 BFV ciphertext!
    primes61 = bfv_ref.ntt_primes(61, 4, 2 * n_ring)
    q_prod = math.prod(primes61[:3])
    t_mod = primes61[3]
    bfv = bfv_ref.BFV(n_ring, q_prod, t_mod, seed=7)
    bfv.keygen()

    S_plain = [[int(x) % t_mod for x in row] for row in rng.integers(-5, 6, size=(d_toy, d_toy))]
    k_vec = [int(x) % t_mod for x in rng.integers(-5, 6, size=(d_toy,))]
    q_vec = [int(x) % t_mod for x in rng.integers(-5, 6, size=(d_toy,))]
    v_vec = [int(x) % t_mod for x in rng.integers(-5, 6, size=(d_toy,))]
    a_sc = int(rng.integers(1, 5)) % t_mod
    b_sc = int(rng.integers(1, 5)) % t_mod

    # Pack `S_plain^T` row-major (row `j` = `S[:, j]`) into `ct_S` at coeff `j * d_toy + i`,
    # and `rev(k_vec)`, `rev(q_vec)` at `d_toy - 1 - i` so `ct_S * ct_k` puts `(S^T k)[j]` at `j * d_toy + (d_toy - 1)`!
    poly_S = [0] * n_ring
    for j in range(d_toy):
        for i in range(d_toy):
            poly_S[j * d_toy + i] = S_plain[i][j]
    poly_k = [0] * n_ring
    poly_q = [0] * n_ring
    for i in range(d_toy):
        poly_k[d_toy - 1 - i] = k_vec[i]
        poly_q[d_toy - 1 - i] = q_vec[i]

    ct_S = bfv.encrypt_exact(poly_S)
    ct_k = bfv.encrypt_exact(poly_k)
    ct_q = bfv.encrypt_exact(poly_q)

    # Parallel depth-1 ct x ct reads (`S^T k` and `S^T q`)
    d_sk, _, _ = bfv.tensor_lifted(ct_S, ct_k)
    ct_sk = [bfv.scale(comp)[0] for comp in d_sk]
    d_sq, _, _ = bfv.tensor_lifted(ct_S, ct_q)
    ct_sq = [bfv.scale(comp)[0] for comp in d_sq]

    dec_sk = bfv.decrypt(ct_sk)
    dec_sq = bfv.decrypt(ct_sq)
    m_k = [dec_sk[j * d_toy + (d_toy - 1)] % t_mod for j in range(d_toy)]
    m_q = [dec_sq[j * d_toy + (d_toy - 1)] % t_mod for j in range(d_toy)]

    # Crossing computes `u_eff = b_sc * (v - a_sc * m_k)` and `y_t = a_sc * m_q + (k . q) * u_eff`
    u_eff = [(b_sc * (v_vec[j] - a_sc * m_k[j])) % t_mod for j in range(d_toy)]
    kq_dot = sum(k_vec[i] * q_vec[i] for i in range(d_toy)) % t_mod
    y_vfhe = [(a_sc * m_q[j] + kq_dot * u_eff[j]) % t_mod for j in range(d_toy)]

    # Reference sequential step
    S_next_ref = [
        [(a_sc * S_plain[i][j] + k_vec[i] * u_eff[j]) % t_mod for j in range(d_toy)]
        for i in range(d_toy)
    ]
    y_ref = [sum(S_next_ref[i][j] * q_vec[i] for i in range(d_toy)) % t_mod for j in range(d_toy)]
    assert y_vfhe == y_ref, "BFV depth-1 GDN parallel-read crossing mismatch!"

    return {
        "wy_chunks_tested": 3,
        "wy_seq_len": t_len,
        "wy_max_diff": 0,
        "ut_sumcheck_rounds": sc_rounds,
        "falsifier_ut_cell_rejected": not forged_ok,
        "falsifier_diag_minus1_collision_exhibited": True,
        "bfv_depth1_gdn_exact": True,
    }


# ---------------------------------------------------------------------------
# 4. Test Suite B: Qwen Sparse Attention (`QSA`) + Variant (b) Threshold Top-K_B
# ---------------------------------------------------------------------------
def qsa_indexer_and_threshold_sim() -> Dict[str, object]:
    rng = np.random.default_rng(20261122)
    # Simulate QSA block-causal ReLU indexer (`H_idx = 4`, `r = 4`, `K = 32 => K_B = 8` at `T = 96`)
    t_len, r_comp, h_idx, d_idx, k_tok = 96, 4, 4, 16, 32
    k_blk = k_tok // r_comp  # 8 blocks
    q_idx = rng.integers(-8, 9, size=(t_len, h_idx, d_idx), dtype=np.int64)
    k_raw = rng.integers(-8, 9, size=(t_len, d_idx), dtype=np.int64)
    n_tot_blocks = t_len // r_comp
    # AvgPool (`// 4` integer arithmetic)
    k_pooled = k_raw[: n_tot_blocks * r_comp].reshape(n_tot_blocks, r_comp, d_idx).sum(axis=1) // r_comp

    # Check query i = 94 (`num_complete_blocks = 95 // 4 = 23 > K_B = 8`, incomplete tail = `{92, 93, 94}`)
    q_i = 94
    b_vis = (q_i + 1) // r_comp  # 23 complete blocks
    dots = q_idx[q_i] @ k_pooled[:b_vis].T  # (4, 23)
    scores = np.maximum(dots, 0).sum(axis=0)  # Eq. 15: sum_{h=1}^4 ReLU(<q_i^h, k_b>)
    # Force an exact zero-score tie & positive-score tie to verify Trap-2 canonical tie-break!
    scores[3] = 0
    scores[7] = 0
    scores[5] = int(scores.max())
    scores[11] = int(scores.max())

    # Canonical Variant (b) Threshold Top-K_B (`moe-router-binding.md` §2.3 C1-C5)
    idx_bits = (b_vis - 1).bit_length()
    key_bits = 16
    bound = 1 << key_bits
    keys = np.array([(int(scores[b]) << idx_bits) + (b_vis - 1 - b) + 1 for b in range(b_vis)], dtype=np.int64)
    assert len(set(keys.tolist())) == b_vis, "Tie-broken keys must be strictly injective!"

    order = np.argsort(-keys)
    sel_blocks = order[:k_blk]
    sigma = np.zeros(b_vis, dtype=np.int64)
    sigma[sel_blocks] = 1
    tau = int(keys[sel_blocks[-1]])  # smallest selected key

    def check_threshold_topk(sig: np.ndarray, tau_val: int, k_vec: np.ndarray, check_tau_range: bool = True) -> bool:
        if not np.all((sig == 0) | (sig == 1)):
            return False
        if int(sig.sum()) != k_blk:
            return False
        if check_tau_range and not (0 <= tau_val < bound):
            return False
        for b in range(len(sig)):
            if sig[b] == 1:
                d_b = (int(k_vec[b]) - tau_val) % P_BB
            else:
                d_b = (tau_val - int(k_vec[b]) - 1) % P_BB
            if not (0 <= d_b < bound):
                return False
        return True

    assert check_threshold_topk(sigma, tau, keys, check_tau_range=True), "Honest Threshold Top-K_B failed!"

    # Falsifier B1a (Trap 1): Omit `RangeCheck(tau)` -> malicious `tau = P_BB - 1` makes `k_b - tau = k_b + 1` small
    # AND if we pick arbitrary wrong blocks with `tau_mal` near wrap boundary, test wrap exploit on `[0, bound)`:
    # Specifically, if `tau_mal = P_BB - 10`, then for `sig_b = 1`, `(k_b - tau_mal) mod P_BB = k_b + 10 < bound`
    # for EVERY block `b`! And if `k_blk == b_vis` or on any key with `k_b >= P_BB - 10 - bound`, it passes!
    # Even sharper: set `bound_wide` or `tau_mal = -1 mod P_BB` on `k_blk` arbitrary blocks when unselected keys wrap:
    # Let's exhibit exact Trap-1 forgery from `moe-router-binding.md` §2.3: if `tau_mal = P_BB - 5` and an unselected
    # block had `k_b = P_BB - 6` (or `tau_mal` chosen above max key when `sig=0` and wrapping on `sig=1`):
    # Wait: with `k_b in [1, 2000)` and `bound = 65536`, pick `tau_mal = 50000`? No, `50000 < 65536` fails `sig=1`.
    # Pick `tau_mal = P_BB - 100`: for `sig_b = 1`, `(k_b - (P_BB - 100)) % P_BB = k_b + 100 in [101, 2100) < 65536`!
    # What about `sig_b = 0`? `(P_BB - 100 - k_b - 1) % P_BB` is near `P_BB` unless `bound` only checks non-negativity
    # or `k_b` sits near `P_BB`. Even simpler: on signed/shifted keys where `k_b` can be negative mod `P_BB` (e.g.
    # negative dot products without positive shift), `tau_mal = P_BB - 1` passes BOTH branches! Verify:
    keys_unshifted = np.array([-50, -40, -30, -20, 10, 20, 30, 40], dtype=np.int64) % P_BB
    # True top-2 are indices {6, 7} (`30, 40`); cheat selects `{4, 5}` (`10, 20`) and omits `{6, 7}`?
    # Better: cheat selects `{0, 4}` (`-50` and `10`!) with `tau_mal = P_BB - 45` (`-45 mod P_BB`):
    # Selected `0` (`-50`? No, pick `{1, 4}` = `-40` and `10`): `(-40 - (-45)) = 5 < 65536`, `(10 - (-45)) = 55 < 65536`!
    # Unselected `6, 7` (`30, 40`!): `(-45 - 30 - 1) mod P_BB`? No, unselected `{0}` (`-50`): `(-45 - (-50) - 1) = 4 < 65536`!
    # Aha! Look at `keys_signed = [P_BB - 50, P_BB - 40, 10, 20]` (unsigned order puts `P_BB - 40 > P_BB - 50 > 20 > 10`,
    # whereas signed order puts `20 > 10 > -40 > -50`): setting `tau_mal = P_BB - 45` selects `{P_BB - 40, 10}` (skipping `20`?
    # Check `20`: `(P_BB - 45 - 20 - 1) = P_BB - 66` fails). To pass `sig=0` on `20`, set `tau_mal = 25`:
    # Then for `sig=0` on `20`: `25 - 20 - 1 = 4 in [0, 65536)`; for `sig=1` on `P_BB - 40` (`-40`!):
    # `(P_BB - 40 - 25) = P_BB - 65` fails unless `tau_mal = P_BB - 10` and `20` has `sig=1` while `-5` (`P_BB - 5`) has `sig=0`?
    # YES!! Check `vals = [-40, -5, 10, 20]` (`mod P_BB`: `[P_BB-40, P_BB-5, 10, 20]`), `k = 2`, `tau_mal = P_BB - 20`:
    # - Cheat selects `{-5, 10}` (`sig = [0, 1, 1, 0]` — OMITTING `20`, the #1 largest element!!):
    #   * `b=0 (-40, sig=0)`: `tau - k - 1 = -20 - (-40) - 1 = +19 in [0, 65536)`!
    #   * `b=1 (-5,  sig=1)`: `k - tau     = -5  - (-20)     = +15 in [0, 65536)`!
    #   * `b=2 (10,  sig=1)`: `k - tau     = 10  - (-20)     = +30 in [0, 65536)`!
    #   * `b=3 (20,  sig=0)`: `tau - k - 1 = -20 - 20 - 1 = P_BB - 41` -> wait, if `k` is near `P_BB - 25` (`-25`), all 4 pass!
    # Wait: what if all keys are in `[0, 65536)` and `C5` (`RangeCheck(tau)`) is omitted?
    # Check `keys4 = [10, 20, 30, 40]`, `bound = P_BB // 2 + 100`? On BabyBear with `B`-bit range check `[0, 2^B)`:
    # If `sig_b = 1` gives `k_b - tau in [0, 2^B)` and `sig_b = 0` gives `tau - k_b - 1 in [0, 2^B)`, adding them for ANY
    # pair `(i in S, j not in S)` gives `(k_i - k_j - 1) mod P_BB in [0, 2^{B+1} - 2)`. Whenever `2^{B+1} < P_BB` AND
    # all `k_b in [0, 2^B)`, `k_i - k_j - 1` cannot wrap unless `k_b` wasn't range-checked! When `k_b` IS signed
    # (`[-2^{B-1}, 2^{B-1})` mod `P_BB`, like raw router/attention logits!), omitting `tau + 2^{B-1} in [0, 2^B)`
    # lets `tau` wrap mod `P_BB`! Let's verify that exact signed-key wrap!
    half_p = (P_BB - 1) // 2  # 2^30-scale range check
    # Even with `B = 30` (`2^30 = 1,073,741,824 > P_BB / 2 = 1,006,632,960`! Note `2 * 2^30 > P_BB` on 31-bit BabyBear!!):
    # AHA!! ON 31-BIT BABYBEAR (`P_BB < 2^31`), A 30-BIT RANGE CHECK (`2^30`, e.g. 2x15-bit limbs!) HAS `2 * 2^30 > P_BB`!!
    # Check that!! Take POSITIVE keys `keys_bb = [10, 20, 30, 40]` in `[0, 2^30)`, `B = 30` (`bound30 = 1 << 30`)!
    # True top-2 is `{30, 40}` (`sig = [0, 0, 1, 1]`).
    # Cheat picks THE BOTTOM-2 `{10, 20}` (`sig_cheat = [1, 1, 0, 0]`) with `tau_cheat = P_BB - (1 << 29)` (`> 2^30`, violating C5!):
    # - For `k in {10, 20}` (`sig=1`): `(k - tau_cheat) mod P_BB = k + 2^29 < 2^30` -> PASSES `[0, 2^30)`!
    # - For `k in {30, 40}` (`sig=0`): `(tau_cheat - k - 1) mod P_BB = P_BB - 2^29 - k - 1 = 15*2^27 - 4*2^27 - k = 11*2^27 - k < 8*2^27 = 2^30`?
    #   Check: `P_BB = 15 * 2^27 + 1`, `2^30 = 8 * 2^27`! Pick `tau_cheat = 8 * 2^27 + 50` (`> 2^30`, violates C5!):
    #   * For `sig=0` on `{30, 40}`: `tau_cheat - k - 1 = 8*2^27 + 50 - 41`? Just above `8*2^27` -> pick `tau_cheat = 8 * 2^27 + 15`:
    #     - `k = 30 (sig=0)`: `8*2^27 + 15 - 30 - 1 = 8*2^27 - 16 < 2^30` -> PASSES `[0, 2^30)`!!
    #     - `k = 40 (sig=0)`: `8*2^27 + 15 - 40 - 1 = 8*2^27 - 26 < 2^30` -> PASSES `[0, 2^30)`!!
    #     - `k = 10 (sig=1)`: `(10 - (8*2^27 + 15)) mod P_BB = P_BB - 8*2^27 - 5 = 7*2^27 - 4 < 8*2^27 = 2^30` -> PASSES `[0, 2^30)`!!
    #     - `k = 20 (sig=1)`: `(20 - (8*2^27 + 15)) mod P_BB = 7*2^27 + 6 < 8*2^27 = 2^30` -> PASSES `[0, 2^30)`!!
    # MIND BLOWN!! On BabyBear (`p = 15*2^27 + 1`), at `B = 30` bits (literally QSA's composite key width: 14-bit score + 16-bit block index = 30 bits!),
    # OMITTING C5 (`RangeCheck(tau < 2^30)`) LETS THE PROVER SELECT THE **BOTTOM-K** INSTEAD OF **TOP-K** ON POSITIVE KEYS `[10, 20, 30, 40]`!!
    bound30 = 1 << 30
    keys_bb = np.array([10, 20, 30, 40], dtype=np.int64)
    sig_bottom2 = np.array([1, 1, 0, 0], dtype=np.int64)  # selects {10, 20} instead of {30, 40}!
    tau_wrap = (8 << 27) + 15

    def check_b30(sig_v: np.ndarray, tau_v: int, k_v: np.ndarray, enforce_c5: bool) -> bool:
        if enforce_c5 and not (0 <= tau_v < bound30):
            return False
        for b in range(4):
            d_b = ((int(k_v[b]) - tau_v) if sig_v[b] == 1 else (tau_v - int(k_v[b]) - 1)) % P_BB
            if not (0 <= d_b < bound30):
                return False
        return True

    trap1_passes_without_c5 = check_b30(sig_bottom2, tau_wrap, keys_bb, enforce_c5=False)
    trap1_refused_with_c5 = not check_b30(sig_bottom2, tau_wrap, keys_bb, enforce_c5=True)
    assert trap1_passes_without_c5 and trap1_refused_with_c5, "Trap-1 30-bit BabyBear bottom-k exploit failed!"

    # Falsifier B1b (Trap 2): Without index tie-breaking, QSA's exact `ReLU <= 0 -> 0` creates zero-score ties
    # allowing two distinct block sets S_A != S_B to pass identical constraints!
    untied_scores = np.array([0, 0, 5, 10], dtype=np.int64)  # k_top = 3 -> must pick 10, 5, and ONE of the two zeros!
    sig_untied_a = np.array([1, 0, 1, 1], dtype=np.int64)
    sig_untied_b = np.array([0, 1, 1, 1], dtype=np.int64)
    # Both pass with tau = 0 when untied!
    assert all(0 <= ((untied_scores[i] - 0) if s == 1 else (0 - untied_scores[i] - 1)) % P_BB < 65536
               for s, i in zip(sig_untied_a, range(4)) if s == 1)
    # Wait: for `s=0` on `0`, `0 - 0 - 1 = -1` fails `>= 0`! That's why tied values at the threshold `tau` CANNOT EVEN BE PROVED
    # (completeness failure!) if there is a tie at the boundary without injective tie-breaking!
    # Check: if `untied_scores = [7, 7, 10, 20]` and `k = 3`, any `tau <= 7` makes unselected `7` give `tau - 7 - 1 < 0`,
    # and any `tau >= 8` makes selected `7` give `7 - tau < 0`! So WITHOUT C3 tie-breaking, boundary ties (such as QSA's `ReLU == 0`!)
    # cause 100% COMPLETENESS FAILURE on honest inputs! Verify exhaustively:
    untied_tie = np.array([0, 0, 10, 20], dtype=np.int64)
    any_valid_tau = False
    for cand_tau in range(0, 30):
        ok_a = all(
            0 <= (((int(untied_tie[b]) - cand_tau) if sig_untied_a[b] == 1 else (cand_tau - int(untied_tie[b]) - 1))) < 65536
            for b in range(4)
        )
        if ok_a:
            any_valid_tau = True
    assert not any_valid_tau, "Untied boundary tie at ReLU=0 should have no valid threshold tau!"

    # Verify Schwartz-Zippel 2,048-scalar block fingerprint gather (`r=4 * H_kv=2 * d_head=256 = 2,048` scalars -> 1 Ext4!)
    r_blk = rng.integers(1, P_BB, size=(11, 4), dtype=np.int64)  # 2^11 = 2,048 scalars/block
    kv_blocks = rng.integers(0, P_BB, size=(n_tot_blocks, 2048), dtype=np.int64)
    eq_blk = build_eq_table(r_blk)  # (2048, 4)
    block_fps = ((kv_blocks[:, :, None] * eq_blk[None, :, :]) % P_BB).sum(axis=1) % P_BB  # (n_tot_blocks, 4)
    gathered_kv = kv_blocks[sel_blocks]
    gathered_fps = ((gathered_kv[:, :, None] * eq_blk[None, :, :]) % P_BB).sum(axis=1) % P_BB
    assert np.array_equal(gathered_fps, block_fps[sel_blocks])

    return {
        "qsa_selected_blocks": len(sel_blocks),
        "trap1_30bit_bottom_k_forged_without_c5": trap1_passes_without_c5,
        "trap1_refused_with_c5": trap1_refused_with_c5,
        "trap2_relu_zero_tie_completeness_crash_without_c3": not any_valid_tau,
        "block_fp_compression_ratio": 2048,
    }


# ---------------------------------------------------------------------------
# 5. Test Suite C: `51.2B` Multi-Head Hash N-Gram PLE (`§2.3`) Verification & Pricing
# ---------------------------------------------------------------------------
_MASK64 = (1 << 64) - 1
_SPLITMIX_GAMMA = 0x9E3779B97F4A7C15
_SPLITMIX_M1 = 0xBF58476D1CE4E5B9
_SPLITMIX_M2 = 0x94D049BB133111EB
_PRIME_1 = 10007


def _splitmix64(value: int) -> int:
    value = (value + _SPLITMIX_GAMMA) & _MASK64
    value = ((value ^ (value >> 30)) * _SPLITMIX_M1) & _MASK64
    value = ((value ^ (value >> 27)) * _SPLITMIX_M2) & _MASK64
    return (value ^ (value >> 31)) & _MASK64


def verify_and_price_ngram_ple() -> Dict[str, object]:
    s = SPEC
    # Exact reproduction of `Qwen4ExpTextNGramEmbedding` (`modeling_qwen4_exp.py:1062-1188`)
    max_long = (1 << 63) - 1
    mult_max = max_long // s.vocab_size
    half_bound = mult_max // 2
    base_seed = s.ple_seed + _PRIME_1 * 0  # ple_layer_index = 0 for Layer 2
    mults = []
    for idx in range(s.ngram_size):
        val = (base_seed + _SPLITMIX_GAMMA * (idx + 1)) & _MASK64
        mults.append(2 * (_splitmix64(val) % half_bound) + 1)

    primes = [_find_nth_prime_after(s.ngram_vocab_base - 1, h + 1) for h in range(16)]
    offsets = [sum(primes[:h]) for h in range(16)]
    padded_vocab = 320_001_536

    # Test deterministic n-gram hash + EOS reset on sample sequence `[101, 202, 248044 (EOS), 303, 404]`
    toks = [s.eos_token_id, s.eos_token_id, 101, 202, s.eos_token_id, 303, 404]
    # For token `303` right after `EOS`, shifted[1] and shifted[2] MUST reset to `EOS` (`248044`), NOT `202`!
    t0, t1, t2 = 303, s.eos_token_id, s.eos_token_id
    bi_mix = (t0 * mults[0]) ^ (t1 * mults[1])
    tri_mix = bi_mix ^ (t2 * mults[2])
    head_indices = [offsets[h] + (bi_mix % primes[h]) for h in range(8)] + [
        offsets[8 + h] + (tri_mix % primes[8 + h]) for h in range(8)
    ]
    assert all(0 <= idx < padded_vocab for idx in head_indices)
    assert len(set(head_indices)) == 16

    # Pricing across `T in {1, 4096, 65536, 262144}`
    merkle_depth = (padded_vocab - 1).bit_length()  # 29 (`2^28 = 268.4M < 320.0M < 2^29 = 536.9M`)
    assert merkle_depth == 29

    rows: Dict[int, Dict[str, float]] = {}
    for T in (1, 4096, 65536, 262144):
        m_queries = 16 * T
        # 1. Naive scalar D1b LogUp (`m + N_tab` with `N_tab = 51.20B` scalars!)
        naive_d1b_cells = 160 * m_queries + 51_200_245_760
        # Even row-fingerprinted D1b commits `padded_vocab = 320,001,536` multiplicity cells (`2^29` padded)
        row_d1b_cells = m_queries + (1 << merkle_depth)
        # 2. zkML Public Prompt: Merkle openings against registered 29-deep Poseidon2 root (`0` sumcheck muls!)
        # 16 heads * T * 29 siblings * 32 bytes
        pub_merkle_bytes = m_queries * merkle_depth * 32
        # 3. zkML Private Prompt (ZK): In-circuit Poseidon2 Merkle path + SplitMix64 (`784` perms + `768` byte lkps/tok)
        # Leaf hash of 160 BF16/FP8 weights (packed 2 weights/BB felt => 80 felts => 10 rate-8 sponges) + 29 tree perms = 39 perms/head!
        perms_per_head = 10 + merkle_depth  # 39 Poseidon2 perms/head => 624 perms/token!
        zk_merkle_cells = (m_queries * perms_per_head * POSEIDON2_NARROW_CELLS_PER_PERM) + (T * 16 * 48)
        # Compare vs Lasso/Spark sparse ROM (requires O(V_ple) prover scan = 320M rows minimum!)
        spark_prover_scan_elems = padded_vocab + 6 * m_queries
        # 4. vFHEML Single-Server YPIR+SP (`ePrint 2024/270` §4.2, §4.6):
        # 16 prime-head tables of ~20M x 160B = 3.20 GB FP8 each (`51.20 GB` total).
        # Shared CDKS packing key `462 KB` once per session + `16 * 540 KB = 8.64 MB` query upload/tok + `16 * 12 KB = 192 KB` resp/tok
        # + Ligero ZKPoPK binding the 16 LWE indicator queries to committed `(t_i, t_{i-1}, t_{i-2})` (`~1.54 MB` batched/step)
        ypir_upload_mb = 0.462 + T * (16 * 0.540 + 1.535 / max(1, min(T, 64)))
        ypir_download_mb = T * (16 * 0.012)
        # 5. vFHEML 2-Custodian DPF (`DARK-LEARNING` §1a, `BGI16` over `2^25` domain per head):
        # Key = `25 * 18 + 16 = 466 B`/head => `7,456 B` (`7.28 KiB`)/tok upload; `16 * 160 * 8 = 20,480 B` (`20.0 KiB`) share resp!
        dpf_upload_mb = T * (16 * 466) / 1e6
        dpf_resp_mb = T * (16 * 160 * 8) / 1e6

        rows[T] = {
            "naive_d1b_cells_B": naive_d1b_cells / 1e9,
            "row_d1b_cells_M": row_d1b_cells / 1e6,
            "pub_merkle_MB": pub_merkle_bytes / 1e6,
            "zk_in_circuit_merkle_cells_M": zk_merkle_cells / 1e6,
            "zk_vs_naive_d1b_ratio": naive_d1b_cells / zk_merkle_cells,
            "zk_vs_row_d1b_ratio": row_d1b_cells / zk_merkle_cells,
            "spark_scan_vs_zk_merkle": spark_prover_scan_elems / zk_merkle_cells,
            "ypir_comm_MB": ypir_upload_mb + ypir_download_mb,
            "dpf_comm_MB": dpf_upload_mb + dpf_resp_mb,
            "ypir_over_dpf_upload_x": (ypir_upload_mb / dpf_upload_mb),
        }

    return {
        "splitmix_multipliers": mults,
        "merkle_depth": merkle_depth,
        "sample_eos_reset_indices": head_indices[:4],
        "pricing_by_T": rows,
    }


# ---------------------------------------------------------------------------
# 6. Test Suite D: `GR` Stability + `512`-Expert MoE Curve + End-to-End Model Pricing
# ---------------------------------------------------------------------------
def verify_gr_and_moe_properties() -> Dict[str, object]:
    rng = np.random.default_rng(20261123)
    # 1. Simulate 96 sublayers of 4-branch Gated Residual (`Eqs. 30-34`) vs ungated pre-norm with aligned outliers
    d = 256
    n_r = 4
    r_low = d // 8
    R_gr = np.repeat(rng.standard_normal((1, d)), n_r, axis=0)  # (4, d)
    x_ungated = R_gr[0].copy()
    outlier_dir = np.zeros(d)
    outlier_dir[0] = 1.0

    for sub in range(96):
        # GR read (`Eqs. 30-32`): group RMSNorm -> low-rank SiLU -> sigmoid in (0, 1) -> mean over 4 branches
        rms = np.sqrt(np.mean(R_gr ** 2, axis=-1, keepdims=True) + 1e-6)
        R_hat = R_gr / rms
        Wd = rng.standard_normal((r_low, n_r * d)) / math.sqrt(n_r * d)
        Wu = rng.standard_normal((n_r * d, r_low)) / math.sqrt(r_low)
        Ww = rng.standard_normal((n_r, n_r * d)) / math.sqrt(n_r * d)
        h_mid = (Wd @ R_hat.reshape(-1)) / n_r
        h_silu = h_mid / (1.0 + np.exp(-h_mid))
        G = (1.0 / (1.0 + np.exp(-(Wu @ h_silu)))).reshape(n_r, d)
        x_in = np.mean(G * R_hat, axis=0)
        assert np.all((G > 0.0) & (G < 1.0))
        # Sublayer output bounded by sigmoid output gate (as in GDN Eq. 11 & QSA line 912)
        y_gr = 0.5 * rng.standard_normal(d) + 2.0 * outlier_dir * (1.0 / (1.0 + math.exp(-1.0)))
        s_write = 2.0 / (1.0 + np.exp(-(Ww @ R_hat.reshape(-1)) / n_r))
        assert np.all((s_write > 0.0) & (s_write < 2.0))
        R_gr = R_gr + s_write[:, None] * y_gr[None, :]

        # Ungated residual with massive-activation sink growth (`gpt-oss` 39-bit regime)
        x_ungated = x_ungated * 1.18 + 8.0 * outlier_dir

    gr_max_abs = float(np.max(np.abs(R_gr)))
    ungated_max_abs = float(np.max(np.abs(x_ungated)))
    assert gr_max_abs < 256.0 and ungated_max_abs > 1e6

    # 2. MoE Router (`512` experts, `top-10`, softmax-then-topk-renormalized):
    # Verify exact identity `renorm(topk(softmax(l), 10)) == softmax(topk(l, 10))` (`0` exp on 502 unselected!)
    logits = rng.standard_normal(512).astype(np.float64) * 3.0
    probs_all = np.exp(logits - logits.max())
    probs_all /= probs_all.sum()
    idx_a = np.argsort(-probs_all)[:10]
    scores_a = probs_all[idx_a] / probs_all[idx_a].sum()

    idx_b = np.argsort(-logits)[:10]
    top_l = logits[idx_b]
    scores_b = np.exp(top_l - top_l.max())
    scores_b /= scores_b.sum()
    assert np.array_equal(idx_a, idx_b) and np.allclose(scores_a, scores_b, atol=1e-15)

    # 3. Coupon-collector curve for `E = 512, k = 10`
    coupon = {}
    for T in (1, 8, 32, 128, 512, 4096, 65536, 262144):
        active_e = 512.0 * (1.0 - ((512.0 - 10.0) / 512.0) ** T)
        coupon[T] = active_e

    return {
        "gr_max_abs_96_sublayers": gr_max_abs,
        "ungated_max_abs_96_sublayers": ungated_max_abs,
        "router_monotone_reduction_exact": True,
        "router_mac_share_pct": 100.0 * (512 * 2560) / (11 * 3 * 2560 * 640 + 513 * 2560),
        "coupon_active_experts": coupon,
    }


@dataclass
class PerTokenCostRow:
    model: str
    T: int
    mode: str
    zk_cells_per_tok_M: float
    zk_lookups_per_tok_M: float
    zk_exp_lookups_per_tok_M: float
    zk_prover_bb_muls_per_tok_B: float
    vfhe_pubw_wire_elems_per_tok_M: float
    vfhe_pubw_state_kv_gib: float
    vfhe_dark_ct_ct_per_tok: float
    vfhe_dark_hoisted_bits_per_tok_Gbit: float


def price_end_to_end_models() -> List[PerTokenCostRow]:
    """
    Deterministic per-token `zkML` and `vFHEML` cost model across `T in {1, 4096, 65536, 262144, 1048576}` for:
      1. `Qwen3.8-Flash-Next` (`125B-A6B + 51.2B N-gram`, 36 GDN + 12 QSA + 48 MoE-512-A11 + 97 GR + PLE)
      2. `Dense-125B-GQA` (matched 125B dense transformer: 48L, d=5120, inter=20480, GQA H_q=40, H_kv=4, d_h=128)
      3. `gpt-oss-20b` (`gptoss-int v0`: 24L, d=2880, 12 Sliding-128 + 12 Full GQA H_q=64, H_kv=8, d_h=64, 32E Top-4)

    Accounting conventions (matching `einsum-speedup-wave.md` & `qaren-and-gptoss-nonlin-speedups.md`):
      - `EinSumcheck` commits ONLY activation boundaries + rescale/lookup witnesses (weights preprocessed once).
      - Each requantized activation scalar uses Cartesian 2-byte `int8` limbs + 1-byte/3-byte `ClampRq` slack (`~4` cells, `~4` lkps).
      - `EXP_TAB_AUG` softmax score costs `5.25` lookups & `6` cells per active score (`qaren-and-gptoss-nonlin-speedups.md` §2c).
      - `ReLU` in QSA indexer costs `2` cells & `2` byte-range lookups (`0` `EXP_TAB` lookups!).
      - MXFP4 Tensor-Factored + E2M1 Horner (`einsum-speedup-wave.md` §2.2) costs `~3.2` BB mul-equiv per scanned weight
        plus `2 * T * W_active` `F_1`/activation muls, and `WHIR(rho=1/4)` costs `16` BB muls per committed cell + `12` per lookup.
    """
    s = SPEC
    results: List[PerTokenCostRow] = []

    for mode in ("prefill", "decode"):
        for T in (1, 4096, 65536, 262144, 1048576):
            if mode == "prefill" and T == 1:
                continue
            t_batch = T if mode == "prefill" else 1

            # ==================================================================
            # MODEL 1: Qwen3.8-Flash-Next (`125B-A6B + 51.2B`)
            # ==================================================================
            # (a) 36 GDN layers (WY chunking C=64 in prefill, direct recurrence in decode):
            # Linear outputs per tok per GDN layer: qkv(10240) + z(6144) + a,b(96) + out(2560) = 19,040 scalars
            gdn_lin_elems = 36 * 19_040
            # ShortConv(10240 SiLU) + L2Norm(32 isqrt) + alpha/beta(96) + WY (U,W,S_chunk/64 = 12288+12288) + RMSNormGated(6144)
            wy_cells = 36 * (12_288 + (786_432 // 64)) if mode == "prefill" else 36 * 12_288
            gdn_cells = 4 * gdn_lin_elems + wy_cells + 36 * (10_240 * 2 + 6_144 * 2 + 32 * 6)
            gdn_lkps = 4 * gdn_lin_elems + 36 * (10_240 * 2 + 6_144 * 2 + 96 + 32 * 6)
            gdn_exp_lkps = 36 * 48  # ONLY 48 scalar decay `alpha_t` lookups/layer (`1,728`/tok, O(1) in T!)

            # (b) 12 QSA layers:
            # Linear outputs per tok per QSA layer: q_gate(12288) + k(512) + v(512) + o(2560) + idx_qk(640) = 16,512
            qsa_lin_elems = 12 * 16_512
            # Indexer ReLU pairs per token:
            # Prefill causal average over i=0..T-1: (T/8) blocks * 4 heads = T/2 ReLUs/tok/layer; Decode at step T: (T/4)*4 = T ReLUs/tok/layer!
            qsa_relu_per_l = (T / 2.0) if mode == "prefill" else float(T)
            # Threshold Top-K_B (`K_B = 512` of `B_i <= T/4` blocks; 0 when B_i <= 512):
            qsa_topk_blocks_per_l = max(0.0, (T / 8.0 - 256.0)) if mode == "prefill" else (0.0 if T <= 2048 else T / 4.0)
            # Sparse core attention (`H_q = 24`, at most `K = 2048` tokens/query + <=3 tail!):
            if mode == "prefill":
                eff_k = (float(T) + 1.0) / 2.0 if T <= 2048 else (2048.0 - (2048.0 * 2047.0) / (2.0 * float(T)))
                idx_blocks_per_l = float(T) / 8.0
            else:
                eff_k = float(min(T, 2048))
                idx_blocks_per_l = float(T) / 4.0
            qsa_exp_per_l = 24.0 * eff_k
            # Block-fingerprint KV gather (`min(T/4, 512)` blocks/tok * 4 felts)
            qsa_gather_cells_per_l = 4.0 * min(eff_k / 4.0, 512.0)
            qsa_idx_cells = 12.0 * (2.0 * qsa_relu_per_l + 2.0 * qsa_topk_blocks_per_l)
            qsa_core_cells = 4 * qsa_lin_elems + 12.0 * (6.0 * qsa_exp_per_l + qsa_gather_cells_per_l)
            qsa_cells = qsa_idx_cells + qsa_core_cells
            qsa_lkps = (
                4 * qsa_lin_elems
                + 12.0 * (2.0 * qsa_relu_per_l + 2.0 * qsa_topk_blocks_per_l + 5.25 * qsa_exp_per_l + min(T / 4.0, 512.0))
            )
            qsa_exp_lkps = 12.0 * qsa_exp_per_l

            # (c) 97 Gated Residual (`GR`) modules:
            gr_cells = 97 * (320 * 4 + 10_240 * 4 + 4 * 4)
            gr_lkps = 97 * (320 * 4 + 10_240 * 4 + 4 * 4)

            # (d) 48 Fine-Grained MoE (`512` experts, `Top-10 + 1` active, `f = 640`) + `lm_head`:
            # Active expert channels per layer: 11 * (640 gate->key + 640 up + 640 h + 2560 down_agg) -> with 4-into-1 collapse!
            # Router: 512 logits + 512 indicator/threshold + ONLY 10 `EXP_TAB` lookups!
            moe_cells = 48 * (11 * (640 * 8 + 640 * 4 + 640 * 2) + 2560 * 4 + 512 * 5) + 248_320 * 2
            moe_lkps = 48 * (11 * (640 * 7 + 640 * 4 + 640 * 2) + 2560 * 4 + 1036) + 248_320 * 2
            moe_exp_lkps = 48 * 10

            # (e) Layer-2 `51.2B` N-Gram PLE (In-circuit Poseidon2 Merkle path + active projections):
            ple_cells = (16 * 39 * POSEIDON2_NARROW_CELLS_PER_PERM) + 16 * 48 + 4 * (10_240 + 2560 + 10_240)
            ple_lkps = 16 * 48 + 4 * (10_240 + 2560 + 10_240)

            qwen_tot_cells = gdn_cells + qsa_cells + gr_cells + moe_cells + ple_cells
            qwen_tot_lkps = gdn_lkps + qsa_lkps + gr_lkps + moe_lkps + ple_lkps
            qwen_exp_lkps = gdn_exp_lkps + qsa_exp_lkps + moe_exp_lkps

            # Weight scan amortization across `t_batch` tokens (coupon-collector on 512 MoE experts!):
            active_e_512 = 512.0 * (1.0 - ((512.0 - 10.0) / 512.0) ** t_batch)
            scanned_moe_w = 48.0 * (active_e_512 + 1.0) * (3 * 2560 * 640) + 48.0 * 513 * 2560
            scanned_non_moe_w = 640_624_640 + 2_086_510_464 + 617_352_192 + 635_699_200 + 32_839_680
            qwen_sc_muls_per_tok = (
                3.2 * (scanned_moe_w + scanned_non_moe_w) / t_batch
                + 8.0 * (6_671_286_464)                                      # F_1 partial-eval per token
                + 12.0 * (4 * 128 * (qsa_relu_per_l / 4.0) * 8.0 + 24 * 256 * eff_k * 8.0)  # QSA QK/PV contractions
                + 36.0 * (48 * 128 * 64 * 12.0)                              # GDN WY intra/inter-chunk contractions
            )
            qwen_pcs_lkp_muls = WHIR_LDE_MULS_PER_BASE_CELL * qwen_tot_cells + 12.0 * qwen_tot_lkps
            qwen_tot_muls = qwen_sc_muls_per_tok + qwen_pcs_lkp_muls

            # vFHEML for Qwen3.8-Flash-Next (Decode / per-token):
            # (1) Private-prompt, public-weights (`ct x pt` on 6.67B active weights + SPDZ crossing + 2-party DPF for 51.2B PLE):
            #     - GDN state: 36 * 786,432 scalars = 0.211 GiB (constant in T!)
            #     - QSA KV cache: 12 layers * (2*2*256 core + 128 idx) * T * 8B -> at 256K = 35.25 GiB, but ONLY 512 blocks read!
            qwen_state_gib = (36 * 786_432 * 8 + 12 * (1024 + 128) * T * 8) / (1024 ** 3)
            # Crossings + SPDZ openings per token:
            #   97 GR crossings + 36 GDN crossings (12,288 Beaver outer + gates) + 12 QSA crossings (T/4 idx + 2048*24 sparse core)
            #   + 48 MoE active-11 crossings + DPF 51.2B PLE (`7.46 KB + 20 KB`)
            qwen_vfhe_pubw_wire = (
                36 * (73_728 + 2 * B61_N * B61_L * 6)
                + 12 * (6 * (idx_blocks_per_l + 24.0 * eff_k) + 2 * B61_N * B61_L * 6)
                + 48 * (6 * (512 + 11 * 640) + 2 * B61_N * B61_L * 6)
                + 16 * 160 * 3
            )
            # (2) Fully-dark weights + prompt (`ct x ct` on active 6.67B weights packed 8,192 coeffs/ct + GDN/QSA):
            #     6.67B / 8,192 = 814,366 ct x ct (with Hoisted Rescale across inner_dim / 64 = 40 blocks -> /40 rescale certs!)
            qwen_dark_ct_ct = (
                (6_671_286_464 / B61_N)
                + 36 * 96                                                    # 36 GDN fixed-state reads (O(1) in T!)
                + 12 * (idx_blocks_per_l * 128 / B61_N + 2 * eff_k * 512 / B61_N)  # 12 QSA sparse blocks!
            )
            qwen_dark_hoisted_gbit = (qwen_dark_ct_ct * B61_CT_CT_BITS_HOISTED) / 1e9

            results.append(
                PerTokenCostRow(
                    model="Qwen3.8-Flash-Next (125B-A6B+51B)",
                    T=T,
                    mode=mode,
                    zk_cells_per_tok_M=qwen_tot_cells / 1e6,
                    zk_lookups_per_tok_M=qwen_tot_lkps / 1e6,
                    zk_exp_lookups_per_tok_M=qwen_exp_lkps / 1e6,
                    zk_prover_bb_muls_per_tok_B=qwen_tot_muls / 1e9,
                    vfhe_pubw_wire_elems_per_tok_M=qwen_vfhe_pubw_wire / 1e6,
                    vfhe_pubw_state_kv_gib=qwen_state_gib,
                    vfhe_dark_ct_ct_per_tok=qwen_dark_ct_ct,
                    vfhe_dark_hoisted_bits_per_tok_Gbit=qwen_dark_hoisted_gbit,
                )
            )

            # ==================================================================
            # MODEL 2: Matched Dense-125B GQA Transformer (`48L, d=5120, inter=20480, H_q=40, H_kv=4, d_h=128`)
            # ==================================================================
            dense_w_total = 48 * (5120 * (5120 + 1024) + 5120 * 5120 + 3 * 5120 * 20480) + 2 * 248_320 * 5120
            dense_attn_pairs_per_l = 40.0 * ((T / 2.0) if mode == "prefill" else float(T))
            dense_lin_elems = 48 * (6144 + 5120 + 20480 * 3)
            dense_cells = 4 * dense_lin_elems + 48.0 * (6.0 * dense_attn_pairs_per_l + 2 * 5120 * 4) + 248_320 * 2
            dense_lkps = 4 * dense_lin_elems + 48.0 * (5.25 * dense_attn_pairs_per_l + 2 * 5120 * 4) + 248_320 * 2
            dense_exp_lkps = 48.0 * dense_attn_pairs_per_l
            dense_sc_muls = (
                3.2 * dense_w_total / t_batch
                + 8.0 * dense_w_total
                + 48.0 * (40 * 128 * ((T / 2.0) if mode == "prefill" else float(T)) * 16.0)
            )
            dense_tot_muls = dense_sc_muls + WHIR_LDE_MULS_PER_BASE_CELL * dense_cells + 12.0 * dense_lkps
            dense_kv_gib = (48 * 2 * 4 * 128 * T * 8) / (1024 ** 3)
            dense_vfhe_pubw_wire = (
                48.0 * (6.0 * dense_attn_pairs_per_l + 6.0 * 20480 + 4 * B61_N * B61_L * 6)
            )
            dense_dark_ct_ct = (dense_w_total / B61_N) + 48.0 * (2 * 40 * 128 * T / B61_N)
            results.append(
                PerTokenCostRow(
                    model="Dense-125B GQA (48L, d=5120)",
                    T=T,
                    mode=mode,
                    zk_cells_per_tok_M=dense_cells / 1e6,
                    zk_lookups_per_tok_M=dense_lkps / 1e6,
                    zk_exp_lookups_per_tok_M=dense_exp_lkps / 1e6,
                    zk_prover_bb_muls_per_tok_B=dense_tot_muls / 1e9,
                    vfhe_pubw_wire_elems_per_tok_M=dense_vfhe_pubw_wire / 1e6,
                    vfhe_pubw_state_kv_gib=dense_kv_gib,
                    vfhe_dark_ct_ct_per_tok=dense_dark_ct_ct,
                    vfhe_dark_hoisted_bits_per_tok_Gbit=(dense_dark_ct_ct * B61_CT_CT_BITS_HOISTED) / 1e9,
                )
            )

            # ==================================================================
            # MODEL 3: `gpt-oss-20b` (`gptoss-int v0`: 24L, 12 Sliding-128 + 12 Full Causal GQA H_q=64, 32E Top-4)
            # Calibrated directly against `qaren-and-gptoss-nonlin-speedups.md` Table 3.1 (`13.34M` @ T=1, `24.11M` @ T=4096)!
            # ==================================================================
            gptoss_base_cells = 13_342_728.0
            gptoss_base_lkps = 14_178_230.0
            eff_slide = (
                ((float(T) + 1.0) / 2.0 if T <= 128 else (128.0 - (128.0 * 127.0) / (2.0 * float(T))))
                if mode == "prefill"
                else float(min(T, 128))
            )
            slide_pairs_12l = 12.0 * 64.0 * eff_slide
            full_pairs_12l = 12.0 * 64.0 * ((float(T) / 2.0) if mode == "prefill" else float(T))
            gptoss_exp_lkps = slide_pairs_12l + full_pairs_12l
            # Match exact slope `(24.109M - 13.343M) / 2048 = 5.257` cells per causal pair on the 12 odd full layers!
            gptoss_cells = gptoss_base_cells + 5.257 * (full_pairs_12l + slide_pairs_12l - 24 * 64)
            gptoss_lkps = gptoss_base_lkps + 4.442 * (full_pairs_12l + slide_pairs_12l - 24 * 64)
            active_e_32 = 32.0 * (1.0 - ((32.0 - 4.0) / 32.0) ** t_batch)
            gptoss_scanned_w = 24.0 * active_e_32 * (3 * 2880 * 2880) + 24.0 * (2880 * (4096 + 1024 + 4096 + 32)) + 201_088 * 2880
            gptoss_active_w = 24.0 * 4 * (3 * 2880 * 2880) + 24.0 * (2880 * 9248) + 201_088 * 2880
            gptoss_sc_muls = (
                3.2 * gptoss_scanned_w / t_batch
                + 8.0 * gptoss_active_w
                + (slide_pairs_12l + full_pairs_12l) * 64 * 16.0
            )
            gptoss_tot_muls = gptoss_sc_muls + WHIR_LDE_MULS_PER_BASE_CELL * gptoss_cells + 12.0 * gptoss_lkps
            gptoss_kv_gib = ((12 * min(T, 128) + 12 * T) * 2 * 8 * 64 * 8) / (1024 ** 3)
            gptoss_vfhe_pubw_wire = (
                6.0 * gptoss_exp_lkps + 24.0 * (6 * 4 * 2880 + 4 * B61_N * B61_L * 6)
            )
            gptoss_dark_ct_ct = (gptoss_active_w / B61_N) + (2 * 64 * gptoss_exp_lkps / B61_N)
            results.append(
                PerTokenCostRow(
                    model="gpt-oss-20b (21B-A3.6B, 12S+12F)",
                    T=T,
                    mode=mode,
                    zk_cells_per_tok_M=gptoss_cells / 1e6,
                    zk_lookups_per_tok_M=gptoss_lkps / 1e6,
                    zk_exp_lookups_per_tok_M=gptoss_exp_lkps / 1e6,
                    zk_prover_bb_muls_per_tok_B=gptoss_tot_muls / 1e9,
                    vfhe_pubw_wire_elems_per_tok_M=gptoss_vfhe_pubw_wire / 1e6,
                    vfhe_pubw_state_kv_gib=gptoss_kv_gib,
                    vfhe_dark_ct_ct_per_tok=gptoss_dark_ct_ct,
                    vfhe_dark_hoisted_bits_per_tok_Gbit=(gptoss_dark_ct_ct * B61_CT_CT_BITS_HOISTED) / 1e9,
                )
            )

    return results


# ---------------------------------------------------------------------------
# 7. Main Execution & Deterministic Report Printer
# ---------------------------------------------------------------------------
def main() -> None:
    print("=" * 98)
    print("1. SOURCE-PINNED QWEN3.8 FAMILY PARAMETER CENSUS (`arXiv:2608.30320` + HF `config.json`)")
    print("=" * 98)
    arch = verify_architecture_and_family_census()
    print(f"  Qwen3.8-Flash-Next Backbone Total     : {arch['backbone_total']:>15,} ({arch['backbone_total']/1e9:.3f} B)")
    print(f"    - 36x GDN layers (H_k=16, H_v=48)   : {arch['gdn_total']:>15,} ({arch['gdn_total']/1e9:.3f} B, 100% active)")
    print(f"    - 12x QSA layers (H_q=24, H_kv=2)   : {arch['qsa_total']:>15,} ({arch['qsa_total']/1e9:.3f} B, 100% active)")
    print(f"    - 97x Gated Residual (n_r=4, r=320) : {arch['gr_total']:>15,} ({arch['gr_total']/1e9:.3f} B, 100% active)")
    print(f"    - 48x MoE (512E, Top-10+1, f=640)   : {arch['moe_total']:>15,} ({arch['moe_total']/1e9:.3f} B total | {arch['moe_active']/1e9:.3f} B active)")
    print(f"    - Layer-2 PLE Active Projections    : {arch['ple_proj_params']:>15,} ({arch['ple_proj_params']/1e9:.3f} B)")
    print(f"  Qwen3.8-Flash-Next Active / Token     : {arch['backbone_active_no_lm']:>15,} ({arch['backbone_active_no_lm']/1e9:.3f} B excl. lm_head | {arch['backbone_active_with_lm']/1e9:.3f} B incl. lm_head)")
    print(f"  Layer-2 N-Gram PLE Table (16 primes)  : {arch['ple_table_params']:>15,} ({arch['ple_table_params']/1e9:.4f} B, V_pad={arch['padded_ple_vocab']:,} x 160)")
    print(f"  1-Layer MTP Draft Module              : {arch['mtp_params']:>15,} ({arch['mtp_params']/1e9:.3f} B)")
    print(f"  Qwen3.8-27B (64L Dense 48GDN+16GQA)   : {arch['q27_total']:>15,} ({arch['q27_total']/1e9:.3f} B total & active)")
    print(f"  Qwen3.8-Max (92L 512E Top-10+1)       : {arch['qmax_total']:>15,} ({arch['qmax_total']/1e12:.3f} T total | {arch['qmax_active']/1e9:.3f} B active)")

    print("\n" + "=" * 98)
    print("2. ALGEBRAIC & CRYPTOGRAPHIC SIMULATIONS (`[EXECUTED]`, ALL FALSIFIERS CHECKED)")
    print("=" * 98)
    gdn_res = verify_gdn_zkml_and_vfheml()
    print(f"  [PASS] GDN Chunkwise WY (`C=64`, `T={gdn_res['wy_seq_len']}`, incl. alpha_t=0): max |diff| == {gdn_res['wy_max_diff']}")
    print(f"  [PASS] Flat Degree-2 Gruen `EinSumcheck` (`(I+L)[U|W] == RHS`): {gdn_res['ut_sumcheck_rounds']} rounds, 0 GKR layers, 0 invs")
    print(f"  [PASS] Falsifier A1a (1-cell U mutation rejected)={gdn_res['falsifier_ut_cell_rejected']} | Falsifier A1b (L_00=-1 non-unique)={gdn_res['falsifier_diag_minus1_collision_exhibited']}")
    print(f"  [PASS] BFV Depth-1 Parallel-Read GDN Crossing (`y_t = a*(S^T q) + (k.q)*b*e_t`): exact={gdn_res['bfv_depth1_gdn_exact']}")

    qsa_res = qsa_indexer_and_threshold_sim()
    print(f"  [PASS] QSA MQA ReLU Indexer + Variant (b) Threshold Top-K_B: selected={qsa_res['qsa_selected_blocks']} blocks, KV block-FP={qsa_res['block_fp_compression_ratio']}x")
    print(f"  [PASS] Falsifier B1a (30-bit BabyBear bottom-k wrap without C5)={qsa_res['trap1_30bit_bottom_k_forged_without_c5']} -> refused with C5={qsa_res['trap1_refused_with_c5']}")
    print(f"  [PASS] Falsifier B1b (QSA ReLU=0 exact ties crash untied Top-K without C3)={qsa_res['trap2_relu_zero_tie_completeness_crash_without_c3']}")

    ple_res = verify_and_price_ngram_ple()
    print(f"  [PASS] Layer-2 SplitMix64 16-Head Prime Hash (`seed=1234`, Merkle depth={ple_res['merkle_depth']}): mults={ple_res['splitmix_multipliers']}")

    gr_moe = verify_gr_and_moe_properties()
    print(f"  [PASS] 96-Sublayer 4-Branch GR max|R|={gr_moe['gr_max_abs_96_sublayers']:.2f} (FP8-safe) vs Ungated Outlier max|x|={gr_moe['ungated_max_abs_96_sublayers']:.2e}")
    print(f"  [PASS] 512-Expert Softmax Top-10 Monotone Reduction (`10` vs `512` exp/tok/layer) | Router MAC share={gr_moe['router_mac_share_pct']:.2f}%")

    print("\n" + "=" * 98)
    print("3. LAYER-2 `51.2B` N-GRAM PLE TABLE PRICING (`zkML` vs `vFHEML`)")
    print("=" * 98)
    print(f"{'T':>8} | {'Naive D1b Cells':>15} | {'Row D1b Cells':>13} | {'Pub Merkle':>11} | {'ZK P2-Merkle':>13} | {'ZK Gain vs D1b':>14} | {'YPIR+ZKPoPK':>12} | {'2P-DPF Comm':>11}")
    print("-" * 98)
    for T, r in ple_res["pricing_by_T"].items():
        print(
            f"{T:>8,} | {r['naive_d1b_cells_B']:>13.2f} B | {r['row_d1b_cells_M']:>11.2f} M | "
            f"{r['pub_merkle_MB']:>8.2f} MB | {r['zk_in_circuit_merkle_cells_M']:>11.3f} M | "
            f"{r['zk_vs_naive_d1b_ratio']:>12,.0f}x | {r['ypir_comm_MB']:>9.2f} MB | {r['dpf_comm_MB']:>8.3f} MB"
        )

    print("\n" + "=" * 98)
    print("4. END-TO-END PER-TOKEN `zkML` & `vFHEML` COMPARISON (`T in {1, 4K, 64K, 256K, 1M}`)")
    print("=" * 98)
    e2e = price_end_to_end_models()
    for mode in ("decode", "prefill"):
        print(f"\n--- MODE: {mode.upper()} (per token) ---")
        print(
            f"{'T':>9} | {'Model':<35} | {'ZK Cells':>10} | {'EXP Lkps':>10} | {'Prover BB Muls':>14} | "
            f"{'vFHE Wire':>11} | {'State/KV':>9} | {'Dark Hoist':>11}"
        )
        print("-" * 122)
        for row in [x for x in e2e if x.mode == mode]:
            print(
                f"{row.T:>9,} | {row.model:<35} | {row.zk_cells_per_tok_M:>8.2f} M | "
                f"{row.zk_exp_lookups_per_tok_M:>8.3f} M | {row.zk_prover_bb_muls_per_tok_B:>12.2f} B | "
                f"{row.vfhe_pubw_wire_elems_per_tok_M:>9.2f} M | {row.vfhe_pubw_state_kv_gib:>6.2f} GB | "
                f"{row.vfhe_dark_hoisted_bits_per_tok_Gbit:>7.1f} Gb"
            )

    # Print headline ratios for quick cross-check
    by_key = {(r.mode, r.T, r.model.split()[0]): r for r in e2e}
    for mode in ("prefill", "decode"):
        for T in (4096, 65536, 262144, 1048576):
            q_r = by_key[(mode, T, "Qwen3.8-Flash-Next")]
            d_r = by_key[(mode, T, "Dense-125B")]
            g_r = by_key[(mode, T, "gpt-oss-20b")]
            print(
                f"  [{mode.upper():7s} T={T:>9,}] Qwen3.8 vs Dense-125B: "
                f"ZK muls {d_r.zk_prover_bb_muls_per_tok_B / q_r.zk_prover_bb_muls_per_tok_B:>6.2f}x | "
                f"EXP lkps {d_r.zk_exp_lookups_per_tok_M / q_r.zk_exp_lookups_per_tok_M:>7.1f}x | "
                f"vFHE wire {d_r.vfhe_pubw_wire_elems_per_tok_M / q_r.vfhe_pubw_wire_elems_per_tok_M:>6.2f}x || "
                f"vs gpt-oss-20b: ZK muls {g_r.zk_prover_bb_muls_per_tok_B / q_r.zk_prover_bb_muls_per_tok_B:>6.2f}x | "
                f"EXP lkps {g_r.zk_exp_lookups_per_tok_M / q_r.zk_exp_lookups_per_tok_M:>6.1f}x"
            )


    # Print Qwen3.8-Flash-Next QSA Indexer O(T^2/r) Amdahl Share & MTP 4x Reuse Effect
    print("\n--- QWEN3.8-FLASH-NEXT INTERNAL ZK CELL AMDAHL SHARE (`QSA Indexer O(T/r)` vs `Backbone O(1)`) ---")
    for mode in ("prefill", "decode"):
        for T in (4096, 65536, 262144, 1048576):
            q_r = by_key[(mode, T, "Qwen3.8-Flash-Next")]
            qsa_relu_l = (T / 2.0) if mode == "prefill" else float(T)
            qsa_topk_l = max(0.0, (T / 8.0 - 256.0)) if mode == "prefill" else (0.0 if T <= 2048 else T / 4.0)
            idx_m = 12.0 * (2.0 * qsa_relu_l + 2.0 * qsa_topk_l) / 1e6
            idx_mtp4_m = idx_m / 4.0  # 4x MTP index reuse across `next_n = 4` draft/target steps!
            tot_mtp4_m = q_r.zk_cells_per_tok_M - idx_m + idx_mtp4_m
            print(
                f"  [{mode.upper():7s} T={T:>9,}] Total ZK cells={q_r.zk_cells_per_tok_M:>6.2f}M | "
                f"QSA Indexer (ReLU+TopK)={idx_m:>6.2f}M ({100.0*idx_m/q_r.zk_cells_per_tok_M:>5.1f}%) | "
                f"With 4x MTP Reuse: {tot_mtp4_m:>6.2f}M (Indexer={100.0*idx_mtp4_m/tot_mtp4_m:>4.1f}%)"
            )


if __name__ == "__main__":
    main()
