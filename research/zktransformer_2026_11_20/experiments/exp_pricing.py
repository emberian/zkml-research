#!/usr/bin/env python3
"""
exp_pricing.py -- Deterministic operation-count pricing of nonlinearity (exp) designs
across query volumes m in {2^12, 2^16, 2^20, 2^24, 2^28} and table bit-widths
b in {14, 15, 16, 20, 24} in our stack's exact units.

House rule (SLVG_THOUGHT.md II.2): Counts are the instrument; the clock is a guest.
Every constant carries provenance to primary source or our tree:
  - PROOF-SYSTEM-SPACE.md & notes/construction-search/space.py (BabyBear, WHIR, Ligerito, Shout, U10)
  - Assurance/AirSumcheckCubic.lean (degree-3 cubicForm_fraction_layer & cubicForm_hadamard)
  - Selvage/BinaryLookup.lean & DecomposableTable.lean (char-2 one-hot chi-tree & SOS product table)
  - zkTransformer src/dag/builder.rs::exp, src/dag/mod.rs, src/crypto/polycommit/{kzh3,sparse_kzh3}.rs
"""

import csv
import json
import math
import os
from typing import Dict, Any, List

HERE = os.path.dirname(os.path.abspath(__file__))

# ---------------------------------------------------------------------------
# 0. Stack & Field Constants (synced with notes/construction-search/space.py)
# ---------------------------------------------------------------------------
BABYBEAR_P = (1 << 31) - (1 << 27) + 1  # 2013265921 (31 bits)
BABYBEAR_BITS = 31

# Extension field multiplication cost in base-field scalar multiplications:
# BabyBear Ext4 = F_p[X]/(X^4 - 11):
#   - Ext4 x Base: 4 base muls
#   - Ext4 x Ext4: Karatsuba over quadratic tower / Toom uses 9-11 base muls; schoolbook binomial X^4-11
#     uses 16 muls + 3 mults-by-11. We track exact (base_muls, ext_base_muls, ext_ext_muls, ext_invs)
#     and convert to scalar base-mul equivalents using standard Karatsuba (9 for Ext4, 18 for Ext6)
#     AND schoolbook (16 for Ext4, 36 for Ext6) so neither convention can hide a conclusion.
EXT_CONFIG = {
    4: {"name": "Ext4", "deg": 4, "ext_mul_kar": 9, "ext_mul_sb": 16, "bits": 123.6},
    6: {"name": "Ext6", "deg": 6, "ext_mul_kar": 18, "ext_mul_sb": 36, "bits": 185.4},
}
# Batch inversion (Montgomery's trick) over F_ext: 3*(K - 1) F_ext muls + 1 F_ext inv (~35 F_ext muls)
BATCH_INV_EXT_MULS_PER_ELEM = 3
SINGLE_INV_EXT_MULS = 35

# PCS Prover per committed base cell (from space.py::pcs_prover, rate = 1/4 -> blowup = 4, width = 64):
# WHIR (multilinear, rho = 1/4) over BabyBear:
#   encode: (blow + 1) * log_h / 2 base muls; fold: 2 base muls/cell
#   hash (blake2s): 64 bytes = 16 BabyBear cells per compression -> blow * (1/16 + 2/64) = 4 * 3/32 = 0.375 hashes/cell
#   hash (poseidon2): rate 8 -> blow * (1/8 + 2/64) = 4 * 5/32 = 0.625 perms/cell (655 base muls/perm)
P2_MULS_PER_PERM = 655
BLAKE2S_INT32_OPS = 1200
BLAKE3_INT32_OPS = 860
KECCAK_INT32_OPS = 2400  # cSHAKE256 / Keccak-f[1600] software op proxy


def whir_pcs_per_cell(log_h: int, hash_kind: str = "blake2s") -> Dict[str, float]:
    blow = 4.0  # rho = 1/4
    enc_muls = (blow + 1.0) * max(1, log_h) / 2.0
    fold_muls = 2.0
    if hash_kind == "poseidon2":
        hashes = blow * (1.0 / 8.0 + 2.0 / 64.0)
        hash_base_muls = hashes * P2_MULS_PER_PERM
    else:
        hashes = blow * (1.0 / 16.0 + 2.0 / 64.0)
        hash_base_muls = 0.0
    return {
        "pcs_base_muls_per_cell": enc_muls + fold_muls + hash_base_muls,
        "pcs_code_muls_per_cell": enc_muls + fold_muls,
        "pcs_hashes_per_cell": hashes,
    }


def ligerito_pcs_per_gf128(log_h: int) -> Dict[str, float]:
    """Ligerito / Additive BaseFold over GF(2^128) at rho = 1/4 (16 bytes/elem, 4 elems/64B hash block)."""
    blow = 4.0
    enc_muls = (blow + 1.0) * max(1, log_h) / 2.0
    fold_muls = 2.0
    hashes = blow * (1.0 / 4.0 + 2.0 / 64.0)  # 4 GF(2^128) elems per 64-byte leaf absorb
    return {
        "pcs_gf128_muls_per_elem": enc_muls + fold_muls,
        "pcs_hashes_per_elem": hashes,
    }


# ---------------------------------------------------------------------------
# 1. Sumcheck Helper Primitives (exact counts)
# ---------------------------------------------------------------------------
def sumcheck_deg3_cubic_form_ext_muls(num_vars: int, n_arrays_to_fold: int = 5) -> int:
    """
    Exact F_ext x F_ext multiplications for a `num_vars`-round degree-3 sumcheck
    of `cubicForm E A B C D = E * (A*B + C*D)` (Assurance/AirSumcheckCubic.lean)
    using evaluation points {0, 1, 2, inf}:
      - Build eq(z, .): 2^num_vars - 1 F_ext muls (if E is eq; caller may pass separately)
      - Per active pair (sum_{r=0}^{v-1} 2^{v-1-r} = 2^v - 1 pairs):
          t=0: 3 muls, t=1: 3 muls, t=2: 3 muls (2*v1 - v0 is add/sub), t=inf: 3 muls => 12 muls/pair
          Fold `n_arrays_to_fold` arrays in-place: `n_arrays_to_fold` muls/pair
    """
    if num_vars <= 0:
        return 0
    pairs = (1 << num_vars) - 1
    return pairs * (12 + n_arrays_to_fold)


def sumcheck_hadamard_deg3_ext_muls(num_vars: int) -> int:
    """
    Exact F_ext multiplications for `sum_{x in {0,1}^v} eq(r, x) * A(x) * B(x)` (3 arrays: eq, A, B):
      - Build eq(r, .): 2^v - 1 F_ext muls
      - Per pair across v rounds (2^v - 1 pairs):
          t=0: eq0*A0*B0 (2 muls), t=1: eq1*A1*B1 (2 muls),
          t=2: eq2*A2*B2 (2 muls), t=inf: deq*dA*dB (2 muls) => 8 muls/pair
          Fold 3 arrays (eq, A, B): 3 muls/pair
      Total = (2^v - 1) * 12 F_ext muls.
    (Note: zkTransformer's LinearSumcheckProver evaluates {0,1,2,3} with scalar*diff interpolation,
     taking (2^v - 1) * (2 + 2 + (3+2) + (3+2) + 3) = 19 muls/pair + (2^v - 1) eq = 20*(2^v - 1).)
    """
    if num_vars <= 0:
        return 0
    return ((1 << num_vars) - 1) * 12


def sumcheck_deg2_ext_muls(num_vars: int) -> int:
    """
    Exact F_ext multiplications for `sum_{x in {0,1}^v} A(x) * B(x)` (2 arrays, degree 2, e.g. Reducer or table dot):
      - Per pair (2^v - 1 pairs): t=0 (1 mul), t=1 (1 mul), t=inf (1 mul) + fold 2 arrays (2 muls) = 5 muls/pair.
    """
    if num_vars <= 0:
        return 0
    return ((1 << num_vars) - 1) * 5


# ---------------------------------------------------------------------------
# 2. Design Pricing Models
# ---------------------------------------------------------------------------

def price_d1a_logup_committed_inv(m: int, b: int, ext_deg: int = 4, hash_kind: str = "blake2s") -> Dict[str, Any]:
    """
    (D1a) Direct Public Table (N = 2^b) + Prime-Field LogUp with COMMITTED inverse helper columns
    (PROOF-SYSTEM-SPACE.md U10: SASH / Stwo / Plonky3 style, pair-unbatched baseline & pair-batched).
    Interface: given committed input u[0..m), commit output y[0..m) and prove (u_i, y_i) in T.
      - Base trace committed per proof:
          y: m base cells
          mult: N = 2^b base cells
      - Interaction / helper columns committed after (alpha, beta) draw:
          h_read[i] = 1 / (beta - u_i - alpha * y_i) in F_ext -> ext_deg * m base cells
          h_table[j] = mult[j] / (beta - j - alpha * T[j]) in F_ext -> ext_deg * N base cells
        (Also reports pair-batched read helper variant where 2 reads share 1 F_ext cell -> ext_deg * m/2.)
      - Witness generation:
          Batch inversion (Montgomery's trick) over m + N denominators in F_ext:
            - Forming denominators (u_i + alpha * y_i): m + N Ext x Base muls
            - Batch inversion of m + N F_ext elements: 3*(m + N) F_ext muls + 1 inv
            - Multiplying h_table[j] by mult[j]: N Ext x Base muls
      - Degree-2 sumcheck / AIR constraint on h_read * (beta - u - alpha*y) - 1 == 0 and h_table * denom - mult == 0:
            -Read side (log2(m) vars, degree 3 with eq): ~12 * m F_ext muls
            -Table side (b vars, degree 3 with eq): ~12 * N F_ext muls
    """
    N = 1 << b
    mu = int(math.log2(m))
    ec = EXT_CONFIG[ext_deg]

    committed_base_cells = (1 + ext_deg) * (m + N)
    committed_base_cells_pairbatch = m + N + ext_deg * (m // 2 + N)
    committed_bits = committed_base_cells * BABYBEAR_BITS

    # Witness-gen counts
    witgen_ext_base_muls = m + 2 * N
    witgen_ext_ext_muls = BATCH_INV_EXT_MULS_PER_ELEM * (m + N) + SINGLE_INV_EXT_MULS
    witgen_inversions = 1

    # PIOP sumcheck counts
    piop_ext_ext_muls = sumcheck_hadamard_deg3_ext_muls(mu) + sumcheck_hadamard_deg3_ext_muls(b)
    # Public table T evaluation at random point r_t in F_ext^b: N Ext x Base muls (eq(r_t, .) takes N Ext muls)
    piop_ext_ext_muls += (N - 1)
    piop_ext_base_muls = 2 * m + 2 * N  # terminal evaluations of (u, y) and (mult, T)

    pcs = whir_pcs_per_cell(max(mu, b), hash_kind)
    pcs_base_muls = committed_base_cells * pcs["pcs_base_muls_per_cell"]
    pcs_hashes = committed_base_cells * pcs["pcs_hashes_per_cell"]

    total_ext_ext = witgen_ext_ext_muls + piop_ext_ext_muls
    total_ext_base = witgen_ext_base_muls + piop_ext_base_muls

    total_base_eq_kar = pcs_base_muls + total_ext_base * ext_deg + total_ext_ext * ec["ext_mul_kar"]
    total_base_eq_sb = pcs_base_muls + total_ext_base * ext_deg + total_ext_ext * ec["ext_mul_sb"]

    # Soundness check: LogUp defect+pole bound <= 2*(m + N) / p^ext_deg (conservative)
    soundness_bits = ec["bits"] - math.log2(2 * (m + N))

    return {
        "design": f"D1a_LogUp_CommittedInv_BB_{ec['name']}",
        "family": "D1a",
        "field": f"BabyBear+{ec['name']}",
        "m": m,
        "b": b,
        "N": N,
        "committed_base_cells": committed_base_cells,
        "committed_base_cells_pairbatch": committed_base_cells_pairbatch,
        "committed_bits": committed_bits,
        "multiplicity_cells": N,
        "helper_inv_base_cells": ext_deg * (m + N),
        "witgen_ext_ext_muls": witgen_ext_ext_muls,
        "witgen_ext_base_muls": witgen_ext_base_muls,
        "witgen_inversions": witgen_inversions,
        "piop_ext_ext_muls": piop_ext_ext_muls,
        "piop_ext_base_muls": piop_ext_base_muls,
        "pcs_base_muls": round(pcs_base_muls),
        "pcs_hashes": round(pcs_hashes),
        "total_base_mul_equiv_kar": round(total_base_eq_kar),
        "total_base_mul_equiv_sb": round(total_base_eq_sb),
        "soundness_bits_piop": round(soundness_bits, 1),
        "char_floor_ok": m < BABYBEAR_P,
    }


def price_d1b_logup_gkr_tree(m: int, b: int, ext_deg: int = 4, hash_kind: str = "blake2s") -> Dict[str, Any]:
    """
    (D1b) Direct Public Table (N = 2^b) + Helper-Free Fraction-Tree LogUp-GKR
    (Papini-Habock 2023/1284 + Assurance/AirSumcheckCubic.lean `cubicForm_fraction_layer`).
    NO inverse columns are committed!
      - Committed cells per proof:
          y: m base cells
          mult: N = 2^b base cells
          Total = m + N base cells (ZERO F_ext helper columns committed!).
      - Witness generation (materializing projective fraction trees in RAM, ZERO field inversions):
          Read tree (m leaves, num_0 = 1, den_0 = beta - u_i - alpha*y_i):
            - Forming den_0: m Ext x Base muls
            - Level 1 (m/2 nodes): num_1 = den_L + den_R (0 muls), den_1 = den_L * den_R (m/2 F_ext muls)
            - Levels 2..mu (m/2 - 1 nodes): 3 F_ext muls/node (p_L*q_R + p_R*q_L, q_L*q_R)
            => 2*m - 3 F_ext muls
          Table tree (N leaves, num_0 = -mult[j], den_0 = beta - j - alpha*T[j]):
            - Forming den_0: N Ext x Base muls
            - Level 1 (N/2 nodes): 2 Ext x Base muls + 1 F_ext mul per node => N Ext x Base + N/2 F_ext muls
            - Levels 2..b (N/2 - 1 nodes): 3 F_ext muls/node
            => 2*N - 3 F_ext muls + 2*N Ext x Base muls
      - GKR Fraction-Tree Sumcheck (levels k = 1 .. mu-1 on read tree, k = 1 .. b-1 on table tree):
          Using `p_L*q_R + p_R*q_L + lambda*q_L*q_R = p_L*q_R + q_L*(p_R + lambda*q_R)`:
          At level k (size 2^k):
            - Build eq(z, .): 2^k - 1 F_ext muls
            - Form D' = p_R + lambda * q_R: 2^k F_ext muls
            - `cubicForm` sumcheck on k vars (5 arrays): (2^k - 1) * 17 F_ext muls
          Summed over k = 1 .. mu-1 (sum 2^k = m - 2): ~19 * m F_ext muls (and ~19 * N for table tree)
          Leaf opening / public T evaluation: 2*m + 2*N Ext x Base muls + (N - 1) F_ext muls for eq(r_t).
    """
    N = 1 << b
    mu = int(math.log2(m))
    ec = EXT_CONFIG[ext_deg]

    committed_base_cells = m + N
    committed_bits = committed_base_cells * BABYBEAR_BITS

    witgen_ext_base_muls = m + 2 * N
    witgen_ext_ext_muls = (2 * m - 3) + (2 * N - 3)
    witgen_inversions = 0

    def tree_gkr_ext_muls(log_leaves: int) -> int:
        total = 0
        for k in range(1, log_leaves):
            sz = 1 << k
            total += (sz - 1) + sz + sumcheck_deg3_cubic_form_ext_muls(k, n_arrays_to_fold=5)
        return total

    piop_ext_ext_muls = tree_gkr_ext_muls(mu) + tree_gkr_ext_muls(b) + (N - 1)
    piop_ext_base_muls = 2 * m + 2 * N

    pcs = whir_pcs_per_cell(max(mu, b), hash_kind)
    pcs_base_muls = committed_base_cells * pcs["pcs_base_muls_per_cell"]
    pcs_hashes = committed_base_cells * pcs["pcs_hashes_per_cell"]

    total_ext_ext = witgen_ext_ext_muls + piop_ext_ext_muls
    total_ext_base = witgen_ext_base_muls + piop_ext_base_muls

    total_base_eq_kar = pcs_base_muls + total_ext_base * ext_deg + total_ext_ext * ec["ext_mul_kar"]
    total_base_eq_sb = pcs_base_muls + total_ext_base * ext_deg + total_ext_ext * ec["ext_mul_sb"]

    # Soundness: LogUp root/pole bound + 3 * (mu*(mu-1)/2 + b*(b-1)/2) / |F_ext|
    gkr_rounds = mu * (mu - 1) // 2 + b * (b - 1) // 2
    err = (2 * N + 3 * gkr_rounds + mu + b) / (BABYBEAR_P ** ext_deg)
    soundness_bits = -math.log2(err)

    return {
        "design": f"D1b_LogUpGKR_Tree_BB_{ec['name']}",
        "family": "D1b",
        "field": f"BabyBear+{ec['name']}",
        "m": m,
        "b": b,
        "N": N,
        "committed_base_cells": committed_base_cells,
        "committed_bits": committed_bits,
        "multiplicity_cells": N,
        "helper_inv_base_cells": 0,
        "witgen_ext_ext_muls": witgen_ext_ext_muls,
        "witgen_ext_base_muls": witgen_ext_base_muls,
        "witgen_inversions": witgen_inversions,
        "piop_ext_ext_muls": piop_ext_ext_muls,
        "piop_ext_base_muls": piop_ext_base_muls,
        "pcs_base_muls": round(pcs_base_muls),
        "pcs_hashes": round(pcs_hashes),
        "total_base_mul_equiv_kar": round(total_base_eq_kar),
        "total_base_mul_equiv_sb": round(total_base_eq_sb),
        "soundness_bits_piop": round(soundness_bits, 1),
        "char_floor_ok": m < BABYBEAR_P,
    }


def price_d2_binary_shout(m: int, b: int, chunk_bits: int = 8) -> Dict[str, Any]:
    """
    (D2) Direct Public Table (N = 2^b) + BinaryShout (Tower256 / GF(2^128), Ligerito rho=1/4).
    Setty-Thaler 2025/105 d-dimensional Shout + Selvage/BinaryLookup.lean char-2 one-hotness.
      - Address of b bits split into d_sh = ceil(b / chunk_bits) chunks; chunk c has w_c <= chunk_bits,
        sub-alphabet K_c = 2^{w_c} (e.g. b=16, chunk_bits=8 => d_sh=2, K=256; b=15 => K_0=256, K_1=128).
      - CRITICAL CHAR-2 SOUNDNESS (Selvage/BinaryLookup.lean:135 `boolean_sum_one_not_oneHot_charTwo`):
        Boolean + sum=1 does NOT imply one-hot in characteristic 2 (1+1+1 = 1 in GF(2)).
        Genuine char-2 one-hotness binds the K_c-bit vector to `binaryLookupEq w_c addr_c` via the
        binary chi-product tree (or prefix pairwise-zero check), adding (K_c - 1 - w_c) auxiliary bits
        (or 0 extra committed bits if Shout's booleanity + address-decode check uses Frobenius/subfield lift,
         priced BOTH ways; we include the full chi-tree bit cost to be conservatively rigorous!).
      - Committed bits per query i in [0, m):
          - One-hot vectors M_c[i, .]: sum_c K_c bits
          - Char-2 chi-tree internal product bits (for w_c > 1): sum_c (K_c - 2) bits (verifies M_c = chi(addr_c))
          - Output y[i] (16-bit integer embedded in binary tower): 16 bits
        Packed into GF(2^128) elements at 128 bits/element via DP24 ring-switching (space.py:331).
      - Shout Read-Checking Sumcheck for unstructured N = 2^b table (2025/105 Sec 4.1):
          - Build eq(r, .) of size m: (m - 1) GF(2^128) muls
          - Bind table variables k in b rounds (prefix-suffix sparse-dense):
              ~ 6 * N + 2 * d_sh * m GF(2^128) muls
          - Bind query variables i in mu rounds (degree d_sh + 1):
              ~ (3 * d_sh + 4) * m GF(2^128) muls
          - Chi-tree check (degree-3 sumcheck over packed bits): ~ 4 * d_sh * m GF(2^128) muls (amortized)
      - Convert GF(2^128) mults to BabyBear base-mul equivalents via space.py CPU ratio (10 / 6 = 1.67x)
        AND report native GF(2^128) mults directly!
    """
    N = 1 << b
    mu = int(math.log2(m))
    # Partition b into chunks of <= chunk_bits
    widths: List[int] = []
    rem = b
    while rem > 0:
        w = min(chunk_bits, rem)
        widths.append(w)
        rem -= w
    d_sh = len(widths)
    ks = [1 << w for w in widths]

    onehot_bits_per_q = sum(ks)
    chitree_bits_per_q = sum(max(0, k - 2) for k in ks)
    out_bits_per_q = 16
    bits_per_q_rigorous = onehot_bits_per_q + chitree_bits_per_q + out_bits_per_q
    bits_per_q_onehot_only = onehot_bits_per_q + out_bits_per_q

    committed_bits = m * bits_per_q_rigorous
    committed_gf128_elems = math.ceil(committed_bits / 128.0)

    # Witness generation: pure bit-scatter (ZERO field multiplications, ZERO inversions!)
    witgen_gf128_muls = 0
    witgen_inversions = 0

    # PIOP sumchecks over GF(2^128)
    eq_muls = m - 1
    table_bind_muls = 6 * N + 2 * d_sh * m
    query_bind_muls = (3 * d_sh + 4) * m
    chitree_check_muls = 4 * d_sh * m
    piop_gf128_muls = eq_muls + table_bind_muls + query_bind_muls + chitree_check_muls

    pcs = ligerito_pcs_per_gf128(max(1, int(math.ceil(math.log2(max(2, committed_gf128_elems))))))
    pcs_gf128_muls = committed_gf128_elems * pcs["pcs_gf128_muls_per_elem"]
    pcs_hashes = committed_gf128_elems * pcs["pcs_hashes_per_elem"]

    total_gf128_muls = witgen_gf128_muls + piop_gf128_muls + pcs_gf128_muls
    # CPU int32-op normalized BabyBear-mul equivalent (space.py: GF2^128 cpu=10 vs BabyBear cpu=6 => 10/6)
    bb_mul_equiv_cpu = total_gf128_muls * (10.0 / 6.0)

    return {
        "design": f"D2_BinaryShout_GF2_128_w{chunk_bits}",
        "family": "D2",
        "field": "GF(2^128)/Tower256",
        "m": m,
        "b": b,
        "N": N,
        "d_chunks": d_sh,
        "chunk_widths": widths,
        "committed_bits": committed_bits,
        "committed_bits_onehot_only": m * bits_per_q_onehot_only,
        "committed_gf128_elems": committed_gf128_elems,
        "committed_bb_cell_equiv_by_bits": round(committed_bits / BABYBEAR_BITS),
        "witgen_gf128_muls": witgen_gf128_muls,
        "witgen_inversions": witgen_inversions,
        "piop_gf128_muls": round(piop_gf128_muls),
        "pcs_gf128_muls": round(pcs_gf128_muls),
        "pcs_hashes": round(pcs_hashes),
        "total_gf128_muls": round(total_gf128_muls),
        "total_base_mul_equiv_kar": round(bb_mul_equiv_cpu),
        "soundness_bits_piop": round(128.0 - math.log2((d_sh + 2) * (mu + b) + N), 1),
    }


def price_d3_structured_exp(
    m: int,
    b: int,
    backend: str,
    include_clamp: bool = True,
    variant: str = "steelman",  # "steelman" vs "repo"
) -> Dict[str, Any]:
    """
    (D3) zkTransformer's `StructuredExp` WITH ALL SOUNDNESS BUGS REPAIRED:
      - Bug A repaired: terminal sumcheck evaluations verified.
      - Bug B repaired: ALL sparse lookup commitments opened via PCS!
      - Bug C repaired: remainder |r| <= floor(2^15 ln 2 / 2) = 11,356 range-checked via
        r + 11356 in [0, 2^15) AND 11356 - r in [0, 2^15) (two 15-bit range checks, matching gpt2.rs:35-38).
      - Bug D repaired: one-hot row-sum = 1 (in prime field) or chi-tree (in char 2) enforced on every sparse block.
      - ScaleDown wrap-mod-p bug repaired: quotient y of each ScaleDown(30 -> 15) must be integer-bounded
        so `prod - 2^15 * y + 2^14 = rem` over F_p cannot wrap mod p (y = honest - delta * 2^-15 mod p).
        Note: for Taylor intermediates:
          * r_sq in [0, (11356)^2 / 2^15] = [0, 3937] (< 2^12, 1 non-neg 12-bit check suffices!)
          * r_sixth = round(5461 * r / 2^15) in [-1893, 1893] (1 shifted 12-bit check!)
          * deg23 in [-650, 2400] (1 shifted 12-bit check!)
          * final exp_x in [0, 32768] (1 16-bit check!)
        To be maximally fair to StructuredExp, we report BOTH `no_quot_bound` (granting D3 an oracle/implicit
        bound on ScaleDown quotients at ZERO cost!) AND `full_sound_quot_bound` (including the 4 quotient range checks).
        Even WITHOUT quotient bounds and WITHOUT ClampLower, StructuredExp still pays 6 x 15-bit + 1 x 4-bit lookups
        and 4 m-variate degree-3/2 sumchecks!

    Backends:
      - "BN254_KZH3": zkTransformer's native BN254 + KZH-3 / SparseKZH-3 (4-bit Shout blocks, TABLE_COMMIT_LOG=4)
      - "BB_LogUpGKR": Transplanted onto BabyBear/Ext4 + Helper-Free LogUp-GKR (8-bit byte subtables for range checks)
      - "Tower256_BinaryShout": Transplanted onto GF(2^128) + BinaryShout (8-bit byte blocks + TwoPow 4-bit block)
    """
    mu = int(math.log2(m))

    # Count range-check bit-widths & m-variate sumchecks in StructuredExp:
    # Core (unclamped):
    #   1. k in [0, 16): one 4-bit lookup (shared with TwoPow!)
    #   2. |r| <= 11356 (Bug C repair): two 15-bit range checks (r + 11356 >= 0, 11356 - r >= 0)
    #   3. Four ScaleDown(30 -> 15) remainders: four 15-bit range checks
    #      (repo also has ScaleUp(r, s, 15); at s=15 steelman omits that no-op!)
    range_widths = [15, 15, 15, 15, 15, 15]  # six 15-bit range checks
    twopow_widths = [4]                       # one 4-bit k / TwoPow lookup (shared selector!)

    # Number of m-variate degree-3 `a,a->a` Einsum sumchecks + degree-2 `Reducer` sumchecks:
    if variant == "repo":
        # repo has r*r, r*(1/6), (r/6 + 1/2)*r^2, two_pow*exp_r = 4 Einsums + 1 Reducer on r (4 consumers)
        num_deg3_einsums = 4
        num_reducers = 1
        dense_const_polys = 3  # 1/6, 1/2, 1 materialized as size-m Constant polys in builder.rs:363-385
    else:
        # steelman folds 5461*r into scalar rescale (no Einsum for r*1/6), virtual constants (0 Constant polys)
        num_deg3_einsums = 3  # r*r, (1/2 + r/6)*r^2, two_pow*exp_r
        num_reducers = 1      # r still consumed 3 times: r*r (2 slots) + linear r/6 & +r
        dense_const_polys = 0

    if include_clamp:
        # ClampLower(x, -C): NonNeg(y - x) [b bits] + NonNeg(y + C) [max(b, 19) -> b bits] + ZeroCheck((y-x)*(y+C))
        range_widths.extend([b, max(b, 19) if b < 19 else b])
        num_deg3_einsums += 1  # ZeroCheck((y - x) * (y + C))
        num_reducers += 1      # y consumed in y-x, y+C, and ExpHelper
        if variant == "repo":
            num_deg3_einsums += 1  # unconditional mask() in builder.rs:124
            dense_const_polys += 2  # mask + C

    design_tag = f"D3_StructuredExp_{variant}_{'clamped' if include_clamp else 'noclamp'}_{backend}"

    if backend == "BN254_KZH3":
        # 4-bit blocks (TABLE_COMMIT_LOG = 4)
        n_4bit_blocks = sum(math.ceil(w / 4) for w in range_widths) + 1  # +1 for shared k/TwoPow 4-bit block
        # Each 4-bit sparse block has (mu + 4) vars and m non-zero `1` entries!
        sparse_nnz_total = n_4bit_blocks * m
        # Dense witnesses committed per proof: output exp (m) [+ dense_const_polys*m offline]
        #Wait: if ScaleDown/ClampLower/ExpHelper outputs are committed to prevent wrap-mod-p, + (4 + (1 if include_clamp else 0))*m dense!
        # Even granting D3 only committing `r` + `exp_out` (+ `y_clamp` if clamped):
        dense_witness_polys = 2 + (1 if include_clamp else 0)
        committed_dense_scalars = dense_witness_polys * m

        # BN254 Fr scalar multiplications:
        # - Einsum sumchecks (LinearSumcheckProver {0,1,2,3} takes 20*m Fr muls each):
        sc_fr_muls = num_deg3_einsums * 20 * m + num_reducers * 8 * m
        # - Shout range + two_pow partial evals (`lagrange_basis` m muls per node + scatter) + 4-var table sumchecks:
        #   plus SparseBoolSumcheckProver (mu+4 rounds, O(m) sparse entries per block => ~14 * m Fr muls/block!)
        #   plus repaired row-sum=1 check (~6 * m Fr muls/block):
        shout_fr_muls = n_4bit_blocks * (20 * m) + (len(range_widths) + 1) * m
        total_fr_muls = sc_fr_muls + shout_fr_muls

        # Curve operations (G1 MSMs in KZH-3 & SparseKZH-3):
        # - Dense commit: size-m MSMs (~2 * m G1 scalar muls incl. d_x slices)
        # - Sparse commit (sparse_kzh3_commit): 2 sparse additions per nonzero entry (c and d_x) => 2 * sparse_nnz_total G1 adds!
        # - Sparse open (REPAIRED Bug B!): 2 openings per sparse block (bool_claim + range_claim, or 1 merged claim per block!):
        #   Each sparse_kzh3_open on size 2^(mu+4) does degree_y * degree_z = 2^(2*(mu+4)/3) G1 MSM!
        kzh_nv = mu + 4
        z_log = kzh_nv // 3
        y_log = (kzh_nv - z_log) // 2
        x_log = kzh_nv - z_log - y_log
        msm_per_open = (1 << (y_log + z_log)) + (1 << x_log)
        total_g1_msms = dense_witness_polys * m + n_4bit_blocks * msm_per_open
        total_g1_sparse_adds = 2 * sparse_nnz_total

        # BabyBear mul equivalent of BN254 Fr mul (~16x on 32-bit lanes, 256-bit Montgomery vs 31-bit) + MSM (~800 Fr muls/MSM)
        # We report native BN254 counts directly AND conservative scalar-mul lower bound!
        return {
            "design": design_tag,
            "family": "D3",
            "field": "BN254_Fr",
            "m": m,
            "b": b,
            "N": 1 << b,
            "n_4bit_blocks": n_4bit_blocks,
            "committed_dense_scalars": committed_dense_scalars,
            "sparse_nnz_entries": sparse_nnz_total,
            "committed_bits": committed_dense_scalars * 254 + sparse_nnz_total * 16,  # sparse representation
            "num_deg3_sumchecks": num_deg3_einsums,
            "total_bn254_fr_muls": total_fr_muls,
            "total_bn254_g1_msms": total_g1_msms,
            "total_bn254_g1_sparse_adds": total_g1_sparse_adds,
            # Conservative CPU-cycle equivalent in BabyBear muls (1 BN254 Fr mul >= 12 BB muls; 1 Pippenger G1 MSM >= 250 BB muls)
            "total_base_mul_equiv_kar": round(total_fr_muls * 12 + total_g1_msms * 250 + total_g1_sparse_adds * 40),
        }

    elif backend == "BB_LogUpGKR":
        # Transplant StructuredExp onto BabyBear/Ext4 + Helper-Free LogUp-GKR!
        # How are the range checks & TwoPow proved in BabyBear + LogUp-GKR?
        # Each 15-bit range check splits into 2 byte-range lookups (8-bit + 7-bit, using shared [0, 256) and [0, 128) tables,
        # OR even better for D3: ONE direct 15-bit range table of size 2^15 = 32,768!).
        # WAIT: Let's give D3 BOTH options and pick whichever is CHEAPER for D3 at (m, b)!
        #   Option A (byte-decomposed range checks into shared 256-entry range table + 16-entry TwoPow table):
        #     Each 15-bit range check commits 1 high-byte cell (low byte = val - 256*hi is virtual!) => 2 lookups into [0,256).
        #     Total lookups: sum(ceil(w/8) for w in range_widths) * m + m (for 4-bit k/TwoPow).
        #   Option B (single shared 2^15 = 32,768 range table for 15-bit checks):
        #     Each 15-bit check is 1 lookup (0 extra split cells!), plus ceil(b/15) for b-bit clamp checks!
        # Let's price BOTH Option A (byte-table, N_tab = 256+16 = 272) and Option B (15-bit range table, N_tab = 32768+16):
        ec = EXT_CONFIG[4]
        pcs = whir_pcs_per_cell(mu, "blake2s")

        # Dense witness columns that MUST be materialized at rescale/clamp boundaries:
        # r (1), 3 Taylor ScaleDown outputs + final exp_x (4) [+ y_clamp (1) if include_clamp]
        # (Note: in a prime field without committing the rounded quotients, ScaleDown is unsound or
        #  degree doubles at each Taylor step to degree 2^4 = 16!)
        dense_cols = 5 + (1 if include_clamp else 0)

        # Option A: 8-bit shared range table (size 256) + 16-entry TwoPow table => N_tab = 272
        n_byte_lookups_per_q = sum(math.ceil(w / 8) for w in range_widths) + 1  # +1 for k->two_pow
        # Extra byte-limb cells committed per multi-byte range check: (ceil(w/8) - 1) per check + 2 for (k, two_pow)
        split_cells_per_q = sum(math.ceil(w / 8) - 1 for w in range_widths) + 2
        commit_cells_A = (dense_cols + split_cells_per_q) * m + 272
        tot_lookups_A = n_byte_lookups_per_q * m
        # GKR fraction tree over tot_lookups_A reads + 272 table entries + Einsum sumchecks:
        witgen_ext_A = 2 * (tot_lookups_A + 272)
        piop_ext_A = 19 * (tot_lookups_A + 272) + num_deg3_einsums * sumcheck_hadamard_deg3_ext_muls(mu) + num_reducers * sumcheck_deg2_ext_muls(mu)
        ext_base_A = 3 * tot_lookups_A + 2 * num_deg3_einsums * m
        pcs_muls_A = commit_cells_A * pcs["pcs_base_muls_per_cell"]
        total_kar_A = pcs_muls_A + ext_base_A * 4 + (witgen_ext_A + piop_ext_A) * ec["ext_mul_kar"]

        # Option B: 15-bit shared range table (size 32,768) + 16-entry TwoPow => N_tab = 32,784
        n_15b_lookups_per_q = sum(math.ceil(w / 15) for w in range_widths) + 1
        split_cells_B = sum(math.ceil(w / 15) - 1 for w in range_widths) + 2
        commit_cells_B = (dense_cols + split_cells_B) * m + 32784
        tot_lookups_B = n_15b_lookups_per_q * m
        witgen_ext_B = 2 * (tot_lookups_B + 32784)
        piop_ext_B = 19 * (tot_lookups_B + 32784) + num_deg3_einsums * sumcheck_hadamard_deg3_ext_muls(mu) + num_reducers * sumcheck_deg2_ext_muls(mu)
        ext_base_B = 3 * tot_lookups_B + 2 * num_deg3_einsums * m
        pcs_muls_B = commit_cells_B * pcs["pcs_base_muls_per_cell"]
        total_kar_B = pcs_muls_B + ext_base_B * 4 + (witgen_ext_B + piop_ext_B) * ec["ext_mul_kar"]

        # Pick whichever table granularity makes D3 stronger (steelman D3!)
        if total_kar_A <= total_kar_B:
            chosen = ("8bit_range_tab", commit_cells_A, tot_lookups_A, witgen_ext_A, piop_ext_A, pcs_muls_A, total_kar_A, 272)
        else:
            chosen = ("15bit_range_tab", commit_cells_B, tot_lookups_B, witgen_ext_B, piop_ext_B, pcs_muls_B, total_kar_B, 32784)

        return {
            "design": design_tag,
            "family": "D3",
            "field": "BabyBear+Ext4",
            "m": m,
            "b": b,
            "N": 1 << b,
            "range_granularity": chosen[0],
            "committed_base_cells": chosen[1],
            "committed_bits": chosen[1] * BABYBEAR_BITS,
            "multiplicity_cells": chosen[7],
            "lookups_per_exp": chosen[2] // m,
            "witgen_ext_ext_muls": chosen[3],
            "witgen_inversions": 0,
            "piop_ext_ext_muls": chosen[4],
            "pcs_base_muls": round(chosen[5]),
            "pcs_hashes": round(chosen[1] * pcs["pcs_hashes_per_cell"]),
            "total_base_mul_equiv_kar": round(chosen[6]),
            "alt_byte_tab_total_kar": round(total_kar_A),
            "alt_15b_tab_total_kar": round(total_kar_B),
        }

    elif backend == "Tower256_BinaryShout":
        # Transplant StructuredExp onto GF(2^128) + BinaryShout (8-bit range blocks + 4-bit TwoPow block)
        # Note: in char 2, field arithmetic is NOT integer arithmetic! To do Taylor series + ScaleDown over Z,
        # D3 CANNOT use GF(2^128) field multiplication for `r * r` — integer multiplication in char 2 requires
        # bit-blasted multiplier circuits (~225 AND gates per 15x15 mult)!
        # Even if we ONLY charge bit-level R1CS for the 3-4 15x15 integer muls + 8-bit BinaryShout blocks:
        n_8bit_blocks = sum(math.ceil(w / 8) for w in range_widths)
        # Each 8-bit block: 256 one-hot + 254 chi-tree = 510 bits (or 4-bit blocks: 4 * (16 + 14) = 120 bits! Wait: 4-bit blocks are MUCH smaller in char-2!)
        # Let's give D3 4-bit blocks (`w=4, K=16`: 16 one-hot + 14 chi-tree = 30 bits/block) AND also give D2 a 4-bit block comparison if needed!
        n_4bit_blocks = sum(math.ceil(w / 4) for w in range_widths) + 1  # ~25 (noclamp) or ~35 (clamped)
        bits_lookup = n_4bit_blocks * 30 * m
        # 3 (or 4) integer 15x15 -> 30 bit multipliers + adders in binary R1CS: ~300 witness bits per mult
        bits_arith = num_deg3_einsums * 300 * m
        committed_bits = bits_lookup + bits_arith
        committed_gf128_elems = math.ceil(committed_bits / 128.0)

        pcs = ligerito_pcs_per_gf128(max(1, int(math.ceil(math.log2(max(2, committed_gf128_elems))))))
        pcs_gf128_muls = committed_gf128_elems * pcs["pcs_gf128_muls_per_elem"]
        piop_gf128_muls = (n_4bit_blocks * 8 + num_deg3_einsums * 25) * m
        total_gf128_muls = pcs_gf128_muls + piop_gf128_muls

        return {
            "design": design_tag,
            "family": "D3",
            "field": "GF(2^128)/Tower256",
            "m": m,
            "b": b,
            "N": 1 << b,
            "n_4bit_blocks": n_4bit_blocks,
            "committed_bits": committed_bits,
            "committed_gf128_elems": committed_gf128_elems,
            "committed_bb_cell_equiv_by_bits": round(committed_bits / BABYBEAR_BITS),
            "piop_gf128_muls": round(piop_gf128_muls),
            "pcs_gf128_muls": round(pcs_gf128_muls),
            "total_gf128_muls": round(total_gf128_muls),
            "total_base_mul_equiv_kar": round(total_gf128_muls * (10.0 / 6.0)),
        }
    else:
        raise ValueError(backend)


def price_d4_rank1_prod_exp(
    m: int,
    b: int,
    backend: str = "BB_LogUpGKR",
    with_rescale: bool = False,
    ext_deg: int = 4,
) -> Dict[str, Any]:
    """
    (D4) Rank1ProdExp: Decompose b-bit non-negative offset u into c = ceil(b / 8) byte chunks
    (c = 2 for b in {14, 15, 16}; c = 3 for b in {20, 24}) with c tiny <=256-entry public integer tables:
      E(u) := prod_{k=0}^{c-1} T_k[u_k]   (exact integer product, exact rank 1 over F_p!)
    Instance of `minidregg/Selvage/DecomposableTable.lean` with w = 8, alpha = c, g = prodTable c.

    On BB_LogUpGKR (Surge + Helper-Free LogUp-GKR):
      - Given u[0..m), commit (c - 1) chunk columns (e.g. u_hi; u_lo = u - 256*u_hi is virtual!)
        + c sub-table read value columns E_0, ..., E_{c-1} (c * m base cells)
        => (2*c - 1) * m base cells if E(u) is virtualized into downstream consumer via Surge primary sumcheck,
           OR 2*c * m base cells if E(u) is materialized as a dense column! (We charge materialized 2*c * m when
           with_rescale=True, and report BOTH virtualized `(2c - 1)m` and materialized `2cm`!)
      - Multiplicity cells: sum_{k=0}^{c-1} 2^{w_k} (e.g. 256 + 256 = 512 for b=16; 256 + 128 = 384 for b=15!).
      - Lookups: c * m reads in the LogUp-GKR fraction tree + N_sub table leaves!
      - Primary product check:
          * For c = 2: 1 degree-3 `cubicForm_hadamard` sumcheck (`eq(r,i)*(E_hi(i)*E_lo(i) - E(i))`) = 12*m F_ext muls!
          * For c = 3: either 1 degree-4 Surge sumcheck or 2 chained degree-3 products.
      - Optional 1-rescale `(15,15) -> 15`: +1 rounded output cell (already counted if materialized) + 15-bit
        remainder range check (2 byte lookups into shared [0, 256) range table + 1 high-byte cell = +m cells, +2m lookups).
    """
    mu = int(math.log2(m))
    widths: List[int] = []
    rem = b
    while rem > 0:
        w = min(8, rem)
        widths.append(w)
        rem -= w
    c = len(widths)
    n_sub = sum(1 << w for w in widths)  # <= 512 for b<=16, <= 768 for b<=24

    tag_rs = "1rescale" if with_rescale else "0rescale"

    if backend == "BB_LogUpGKR":
        ec = EXT_CONFIG[ext_deg]
        pcs = whir_pcs_per_cell(mu, "blake2s")

        # Committed base cells:
        #   chunk addresses: (c - 1) * m (since lowest byte u_0 = u - sum_{k>=1} 2^(8k) u_k is linear/virtual!)
        #   subtable values E_0..E_{c-1}: c * m
        #   if virtualized (0-rescale Surge): (2*c - 1) * m + n_sub
        #   if materialized output E: 2*c * m + n_sub
        base_cells_virt = (2 * c - 1) * m + n_sub
        base_cells_mat = (2 * c) * m + n_sub
        tot_lookups = c * m
        extra_n_sub = n_sub

        if with_rescale:
            # Rescale prod (30 bits) -> 15 bits: commit E_rescaled (m) + rem_hi (m), 2 byte-range lookups into [0,256)
            committed_cells = (2 * c + 1) * m + n_sub + 256
            tot_lookups += 2 * m
            extra_n_sub += 256
        else:
            committed_cells = base_cells_virt  # Surge virtualized (also record materialized!)

        witgen_ext_muls = 2 * (tot_lookups + extra_n_sub)
        # Primary product sumcheck: c=2 uses landed degree-3 cubicForm (12*m F_ext muls); c=3 uses degree-4 (~16*m)
        prod_sc_muls = (12 if c == 2 else 16) * m
        piop_ext_muls = 19 * (tot_lookups + extra_n_sub) + prod_sc_muls
        ext_base_muls = 2 * (tot_lookups + extra_n_sub) + c * m

        pcs_base_muls = committed_cells * pcs["pcs_base_muls_per_cell"]
        total_kar = pcs_base_muls + ext_base_muls * ext_deg + (witgen_ext_muls + piop_ext_muls) * ec["ext_mul_kar"]

        # Also compute materialized 0-rescale total for full transparency
        pcs_base_muls_mat = base_cells_mat * pcs["pcs_base_muls_per_cell"]
        total_kar_mat = pcs_base_muls_mat + ext_base_muls * ext_deg + (witgen_ext_muls + piop_ext_muls) * ec["ext_mul_kar"]

        return {
            "design": f"D4_Rank1ProdExp_{tag_rs}_BB_{ec['name']}",
            "family": "D4",
            "field": f"BabyBear+{ec['name']}",
            "m": m,
            "b": b,
            "N": 1 << b,
            "c_chunks": c,
            "subtable_entries_total": extra_n_sub,
            "committed_base_cells": committed_cells,
            "committed_base_cells_materialized": base_cells_mat if not with_rescale else committed_cells,
            "committed_bits": committed_cells * BABYBEAR_BITS,
            "multiplicity_cells": extra_n_sub,
            "lookups_per_exp": tot_lookups // m,
            "witgen_ext_ext_muls": witgen_ext_muls,
            "witgen_inversions": 0,
            "piop_ext_ext_muls": piop_ext_muls,
            "pcs_base_muls": round(pcs_base_muls),
            "pcs_hashes": round(committed_cells * pcs["pcs_hashes_per_cell"]),
            "total_base_mul_equiv_kar": round(total_kar),
            "total_base_mul_equiv_kar_materialized": round(total_kar_mat if not with_rescale else total_kar),
        }

    elif backend == "Tower256_BinaryShout":
        # On Tower256 / BinaryShout with c = ceil(b/8) chunks:
        # Notice: BinaryShout ALREADY commits the exact same c one-hot vectors M_0..M_{c-1} (sum 2^w_k bits)!
        # What changes vs D2?
        #   1. The O(2^b) unstructured table sumcheck (6 * 2^b muls) is REPLACED by c tiny 2^w_k dot products (2 * n_sub <= 1536 muls)!
        #   2. Warning: E(u) = T_hi * T_lo is an INTEGER product! In char 2, if E(u) feeds into an integer sum `e @ v`,
        #      Wait: in GF(2^128), `T_hi * T_lo` in GF(2^128) is carryless polynomial multiplication, NOT integer multiplication!
        #      Unless the whole inference runs in a prime field (or embeds integers via binary R1CS multiplier ~225 bits),
        #      char-2 field product != integer product!
        #      WAIT A SECOND! Check that! For D2 (`T_exact`), the table entry `T_exact[u]` can directly store whatever
        #      16-bit representation downstream char-2 circuits expect, whereas `Rank1ProdExp` relies on `T_hi[u_hi] * T_lo[u_lo]`
        #      being an INTEGER product! In char-2 R1CS, an 8x8 -> 16 integer multiplier costs 64 AND gates (64 bits),
        #      or 15x15 -> 30 costs 225 AND gates (225 bits)!
        ks = [1 << w for w in widths]
        onehot_bits = sum(ks) + sum(max(0, k - 2) for k in ks)
        int_mul_bits = 64 if not with_rescale else 225  # 8x8 int mul vs 15x15 int mul in char 2!
        bits_per_q = onehot_bits + int_mul_bits
        committed_bits = m * bits_per_q
        committed_gf128_elems = math.ceil(committed_bits / 128.0)

        pcs = ligerito_pcs_per_gf128(max(1, int(math.ceil(math.log2(max(2, committed_gf128_elems))))))
        pcs_gf128_muls = committed_gf128_elems * pcs["pcs_gf128_muls_per_elem"]
        # Table term is ONLY 6 * n_sub instead of 6 * 2^b!
        piop_gf128_muls = (m - 1) + 6 * n_sub + (9 * c + 8) * m
        total_gf128_muls = pcs_gf128_muls + piop_gf128_muls

        return {
            "design": f"D4_Rank1ProdExp_{tag_rs}_GF2_128",
            "family": "D4",
            "field": "GF(2^128)/Tower256",
            "m": m,
            "b": b,
            "N": 1 << b,
            "c_chunks": c,
            "subtable_entries_total": n_sub,
            "committed_bits": committed_bits,
            "committed_gf128_elems": committed_gf128_elems,
            "committed_bb_cell_equiv_by_bits": round(committed_bits / BABYBEAR_BITS),
            "piop_gf128_muls": round(piop_gf128_muls),
            "pcs_gf128_muls": round(pcs_gf128_muls),
            "total_gf128_muls": round(total_gf128_muls),
            "total_base_mul_equiv_kar": round(total_gf128_muls * (10.0 / 6.0)),
        }
    else:
        raise ValueError(backend)


def compute_analytical_crossovers() -> Dict[str, Any]:
    """Exact closed-form crossover thresholds m*(b) on BabyBear + Helper-Free LogUp-GKR."""
    crossovers = {}
    for b in (12, 14, 15, 16, 20, 24):
        N = 1 << b
        # Compare D1b (Direct N=2^b) vs D4 (Rank1ProdExp 0-rescale virtualized)
        # Committed cells: D1b = m + N; D4 = (2c - 1)*m + n_sub
        c = math.ceil(b / 8)
        widths = []
        rem = b
        while rem > 0:
            widths.append(min(8, rem))
            rem -= widths[-1]
        n_sub = sum(1 << w for w in widths)
        # Solve (2c - 1)*m + n_sub = m + N  =>  2*(c - 1)*m = N - n_sub
        m_cells_virt = (N - n_sub) / (2 * (c - 1))
        # Solve materialized: 2*c*m + n_sub = m + N => (2c - 1)*m = N - n_sub
        m_cells_mat = (N - n_sub) / (2 * c - 1)

        # Binary search exact total-mul crossover between D1b and D4 (0-rescale) and D3 (steelman noclamp)
        def find_mul_crossover(fn_small_table):
            lo, hi = 64, 1 << 30
            # Check if fn_small_table loses even at m=64
            def diff(m_val):
                # interpolate continuous power-of-two log2
                mu_log = max(6, int(round(math.log2(m_val))))
                m_pow = 1 << mu_log
                r1 = price_d1b_logup_gkr_tree(m_pow, b, 4)["total_base_mul_equiv_kar"]
                r2 = fn_small_table(m_pow, b)["total_base_mul_equiv_kar"]
                return r2 - r1  # < 0 means small-table design wins

            winning_pows = []
            for mu_test in range(8, 31):
                mp = 1 << mu_test
                r_d1 = price_d1b_logup_gkr_tree(mp, b, 4)["total_base_mul_equiv_kar"]
                r_sm = fn_small_table(mp, b)["total_base_mul_equiv_kar"]
                if r_sm < r_d1:
                    winning_pows.append(mu_test)
            return max(winning_pows) if winning_pows else None

        max_mu_d4_beats_d1b = find_mul_crossover(lambda mp, bw: price_d4_rank1_prod_exp(mp, bw, "BB_LogUpGKR", False, 4))
        max_mu_d3_beats_d1b = find_mul_crossover(lambda mp, bw: price_d3_structured_exp(mp, bw, "BB_LogUpGKR", False, "steelman"))
        max_mu_d3_clamped_beats_d1b = find_mul_crossover(lambda mp, bw: price_d3_structured_exp(mp, bw, "BB_LogUpGKR", True, "steelman"))

        crossovers[f"b={b}"] = {
            "b": b,
            "N": N,
            "c_chunks": c,
            "n_sub": n_sub,
            "d4_vs_d1b_cell_crossover_m_virt": round(m_cells_virt, 1),
            "d4_vs_d1b_cell_crossover_log2_m_virt": round(math.log2(max(1.0, m_cells_virt)), 2),
            "d4_vs_d1b_cell_crossover_m_mat": round(m_cells_mat, 1),
            "d4_beats_d1b_in_total_muls_up_to_log2_m": max_mu_d4_beats_d1b,
            "d3_steelman_noclamp_beats_d1b_up_to_log2_m": max_mu_d3_beats_d1b,
            "d3_steelman_clamped_beats_d1b_up_to_log2_m": max_mu_d3_clamped_beats_d1b,
        }
    return crossovers


def main():
    ms = [1 << 12, 1 << 16, 1 << 20, 1 << 24, 1 << 28]
    bs = [14, 15, 16, 20, 24]

    rows: List[Dict[str, Any]] = []
    grid_comparisons: List[Dict[str, Any]] = []

    d3_beats_d4_anywhere = 0

    for b in bs:
        for m in ms:
            d1a_4 = price_d1a_logup_committed_inv(m, b, ext_deg=4)
            d1a_6 = price_d1a_logup_committed_inv(m, b, ext_deg=6)
            d1b_4 = price_d1b_logup_gkr_tree(m, b, ext_deg=4)
            d1b_6 = price_d1b_logup_gkr_tree(m, b, ext_deg=6)
            d2_8 = price_d2_binary_shout(m, b, chunk_bits=8)
            d2_4 = price_d2_binary_shout(m, b, chunk_bits=4)

            d3_bn_repo = price_d3_structured_exp(m, b, "BN254_KZH3", include_clamp=True, variant="repo")
            d3_bn_steel = price_d3_structured_exp(m, b, "BN254_KZH3", include_clamp=True, variant="steelman")
            d3_bb_clamp = price_d3_structured_exp(m, b, "BB_LogUpGKR", include_clamp=True, variant="steelman")
            d3_bb_noclamp = price_d3_structured_exp(m, b, "BB_LogUpGKR", include_clamp=False, variant="steelman")
            d3_bin_noclamp = price_d3_structured_exp(m, b, "Tower256_BinaryShout", include_clamp=False, variant="steelman")

            d4_bb_0rs = price_d4_rank1_prod_exp(m, b, "BB_LogUpGKR", with_rescale=False, ext_deg=4)
            d4_bb_1rs = price_d4_rank1_prod_exp(m, b, "BB_LogUpGKR", with_rescale=True, ext_deg=4)
            d4_bin_0rs = price_d4_rank1_prod_exp(m, b, "Tower256_BinaryShout", with_rescale=False)

            batch = [
                d1a_4, d1a_6, d1b_4, d1b_6, d2_8, d2_4,
                d3_bn_repo, d3_bn_steel, d3_bb_clamp, d3_bb_noclamp, d3_bin_noclamp,
                d4_bb_0rs, d4_bb_1rs, d4_bin_0rs,
            ]
            rows.extend(batch)

            if d3_bb_noclamp["total_base_mul_equiv_kar"] <= d4_bb_0rs["total_base_mul_equiv_kar"]:
                d3_beats_d4_anywhere += 1
            if d3_bb_noclamp["total_base_mul_equiv_kar"] <= d4_bb_1rs["total_base_mul_equiv_kar"]:
                d3_beats_d4_anywhere += 1

            grid_comparisons.append({
                "log2_m": int(math.log2(m)),
                "m": m,
                "b": b,
                "D1a_Ext4_cells": d1a_4["committed_base_cells"],
                "D1b_Ext4_cells": d1b_4["committed_base_cells"],
                "D3_BB_noclamp_cells": d3_bb_noclamp["committed_base_cells"],
                "D3_BB_clamped_cells": d3_bb_clamp["committed_base_cells"],
                "D4_0rs_cells": d4_bb_0rs["committed_base_cells"],
                "D4_1rs_cells": d4_bb_1rs["committed_base_cells"],
                "D1a_Ext4_muls": d1a_4["total_base_mul_equiv_kar"],
                "D1b_Ext4_muls": d1b_4["total_base_mul_equiv_kar"],
                "D2_BinShout_w8_gf128_muls": d2_8["total_gf128_muls"],
                "D2_BinShout_w4_gf128_muls": d2_4["total_gf128_muls"],
                "D3_BN254_repo_muls_eq": d3_bn_repo["total_base_mul_equiv_kar"],
                "D3_BB_noclamp_muls": d3_bb_noclamp["total_base_mul_equiv_kar"],
                "D3_BB_clamped_muls": d3_bb_clamp["total_base_mul_equiv_kar"],
                "D4_0rs_BB_muls": d4_bb_0rs["total_base_mul_equiv_kar"],
                "D4_1rs_BB_muls": d4_bb_1rs["total_base_mul_equiv_kar"],
                "ratio_D3_noclamp_over_D1b": round(d3_bb_noclamp["total_base_mul_equiv_kar"] / d1b_4["total_base_mul_equiv_kar"], 3),
                "ratio_D3_clamped_over_D1b": round(d3_bb_clamp["total_base_mul_equiv_kar"] / d1b_4["total_base_mul_equiv_kar"], 3),
                "ratio_D4_0rs_over_D1b": round(d4_bb_0rs["total_base_mul_equiv_kar"] / d1b_4["total_base_mul_equiv_kar"], 3),
                "ratio_D3_noclamp_over_D4_0rs": round(d3_bb_noclamp["total_base_mul_equiv_kar"] / d4_bb_0rs["total_base_mul_equiv_kar"], 3),
                "ratio_D3_clamped_over_D4_1rs": round(d3_bb_clamp["total_base_mul_equiv_kar"] / d4_bb_1rs["total_base_mul_equiv_kar"], 3),
                "bb_winner": min(
                    [("D1b_DirectLogUpGKR", d1b_4["total_base_mul_equiv_kar"]),
                     ("D3_StructuredExp_noclamp", d3_bb_noclamp["total_base_mul_equiv_kar"]),
                     ("D4_Rank1ProdExp_0rs", d4_bb_0rs["total_base_mul_equiv_kar"])],
                    key=lambda kv: kv[1]
                )[0],
            })

    assert d3_beats_d4_anywhere == 0, "Unexpected: StructuredExp beat Rank1ProdExp!"

    crossovers = compute_analytical_crossovers()

    out_json = os.path.join(HERE, "exp_pricing_results.json")
    with open(out_json, "w") as f:
        json.dump({
            "crossovers": crossovers,
            "d3_beats_d4_grid_points": d3_beats_d4_anywhere,
            "grid_summary": grid_comparisons,
            "detailed_rows": rows,
        }, f, indent=2)

    out_csv = os.path.join(HERE, "exp_pricing_grid.csv")
    with open(out_csv, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(grid_comparisons[0].keys()))
        w.writeheader()
        w.writerows(grid_comparisons)

    print("=== EXP PRICING SUMMARY (BabyBear+Ext4 Base-Mul Equivalents, Karatsuba) ===")
    hdr = (f"{'b':>2} {'log2m':>5} | {'D1b Direct':>12} {'D1a InvCol':>12} "
           f"{'D3(noclamp)':>12} {'D3(clamped)':>12} {'D4(0-resc)':>12} {'D4(1-resc)':>12} | "
           f"{'D3nc/D1b':>8} {'D4_0/D1b':>8} {'D3nc/D4_0':>9} | {'Winner (BB)'}")
    print(hdr)
    print("-" * len(hdr))
    for g in grid_comparisons:
        print(f"{g['b']:2d} {g['log2_m']:5d} | "
              f"{g['D1b_Ext4_muls']:12.3e} {g['D1a_Ext4_muls']:12.3e} "
              f"{g['D3_BB_noclamp_muls']:12.3e} {g['D3_BB_clamped_muls']:12.3e} "
              f"{g['D4_0rs_BB_muls']:12.3e} {g['D4_1rs_BB_muls']:12.3e} | "
              f"{g['ratio_D3_noclamp_over_D1b']:7.2f}x {g['ratio_D4_0rs_over_D1b']:7.2f}x "
              f"{g['ratio_D3_noclamp_over_D4_0rs']:8.2f}x | {g['bb_winner']}")

    print("\n=== ANALYTICAL CROSSOVERS (BabyBear + LogUp-GKR) ===")
    for k, v in crossovers.items():
        print(f"  {k}: N={v['N']:,}, sub={v['n_sub']} | "
              f"D4 vs D1b cell crossover m*={v['d4_vs_d1b_cell_crossover_m_virt']:,.0f} (2^{v['d4_vs_d1b_cell_crossover_log2_m_virt']}) | "
              f"D4 beats D1b total muls up to log2(m)={v['d4_beats_d1b_in_total_muls_up_to_log2_m']} | "
              f"D3(noclamp) beats D1b up to log2(m)={v['d3_steelman_noclamp_beats_d1b_up_to_log2_m']} | "
              f"D3(clamped) beats D1b up to log2(m)={v['d3_steelman_clamped_beats_d1b_up_to_log2_m']}")


if __name__ == "__main__":
    main()
