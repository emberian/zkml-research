//! Emulation-Free Dual-Characteristic `248,320`-Vocab `Qwen` BPE Token-to-Byte Bridge
//! (`Theory/DualCharTokenBridge.lean` + `Theory/IntegerFingerprint.lean`).
//!
//! Bridges **Tensor World** (`BabyBear` `p = 2013265921` / `123.7`-bit `Ext4 = F_p[X]/(X^4 - 11)` /
//! `p61` `IntegerFingerprint`) and **Policy World** (`Tower256 = GF(2^256)` Fan–Paar level-8 tower +
//! `cSHAKE256` salted byte commitments) with **zero in-circuit Keccak bit-blasting**, **zero
//! cross-field arithmetic emulation**, and **zero per-character inner loops** on the token side:
//!
//! 1. **Real `248,320`-Entry `Qwen` ByteLevel BPE ROM (`QwenBpeRom`):**
//!    Parses `/Users/ember/.cache/huggingface/hub/models--Qwen--Qwen3.5-0.8B-Base/.../tokenizer.json`
//!    (`248,044` ByteLevel BPE tokens + `22` `added_tokens` = `248,066` active tokens + `254`
//!    unallocated padded IDs `248,066..248,319`, padded to `262,144 = 2^{18}`), decodes every token
//!    to its exact raw UTF-8/byte sequence via the inverse GPT-2 `bytes_to_unicode` bijection, and
//!    `cSHAKE256`-Merkle-commits `(tok_id, is_defined, byte_len, B_ext4^{len}, val_ext4, B_t256^{len}, val_t256)`.
//!
//! 2. **Post-Commitment Dual-Characteristic Weld (`prove_dual_char_bpe_bridge` / `verify_dual_char_bpe_bridge`):**
//!    - Commits the `K`-token witness (`K = 64..512+`) and `L`-byte witness in `BabyBear` (`SuccinctExt4Pcs`)
//!      AND commits the salted `L`-byte witness in `Tower256` (`saltedContentCommit` + `Tower256Pcs` ZK
//!      Coset-RS matrix PCS) **before** squeezing evaluation bases `(\beta_{ext4}, \beta_{256}, p_{61,0}, p_{61,1})`
//!      from the shared `CShakeTranscript`.
//!    - In **`BabyBear Ext4`**: proves every active `(tok_i, is_pad_i, len_i, \beta_{ext4}^{len_i}, val_i(\beta_{ext4}))`
//!      lies in the `262,144`-slot `Qwen` ROM via subdomain-lifted `D1b` LogUp-GKR (`m_wit <= m_tab`, `< 2^{-104.6}`
//!      unconditional soundness, `0` witness padding), proves the degree-2 rolling recurrence
//!      `acc_{i+1} = acc_i * pow_i + val_i` and `cum_len_{i+1} = cum_len_i + len_i` via `Gruen` Mode-2
//!      zerocheck + shift sumchecks (`acc_K == final_acc_ext4`, `cum_len_K == L`), and proves `bytes_bb[..L]`
//!      (`D1b`-ranged in `[0, 512)` with tail EOF `256`) evaluates at `\beta_{ext4}` to `final_acc_ext4`.
//!    - In **`Tower256` (`GF(2^256)`)**: proves `GF(2^8)` canonical byte subfield membership via the
//!      Frobenius automorphism identity `B(\phi^{-1}(z))^{256} == B(z)` (`< 2^{-250}` error, `0` lookup
//!      tables!), proves the degree-2 `Tower256` Horner trace `h_{j+1} = h_j * step_mul_j \oplus step_val_j`
//!      via zero-inversion `{0, 1, \infty}` characteristic-2 quadratic sumcheck + `Tower256Pcs` ZK openings
//!      (`h_L == final_acc_t256`), and binds `p61` `IntegerFingerprint` evaluations.

use crate::ext4::{
    bsub, build_eq_table_lsb_ext4, cshake256_32, eq_lin_ext4, eq_mle_ext4,
    eval_cubic_zero_one_two_inf_ext4, fold_ext4, merkle_node_cshake, mle_eval_bb_at_ext4,
    os_random_seed_32, ByteCursor, CShakeRng, CShakeTranscript, Ext4, P_U32,
};
use crate::gruen_ext4::{
    compute_d1b_multiplicities, prove_d1b_range_ext4, prove_gruen_einsum_mode2_ext4,
    verify_d1b_range_ext4, verify_gruen_einsum_mode2_ext4, CubicExt4RoundMsg, D1bLayerProof,
    D1bRangeExt4Proof, GruenMode2Ext4Proof,
};
use crate::pcs_ext4::{
    commit_table_pcs, open_pcs_claims, verify_pcs_claims, MerkleMultiProof, MleEvalClaim,
    PcsOpeningProof, PcsParams, PcsShape,
};
use rayon::prelude::*;
use serde_json::Value;
use std::collections::HashMap;
use std::fs;
use std::path::Path;
use std::sync::OnceLock;

/// Real pretrained `Qwen/Qwen3.5-0.8B-Base` local HuggingFace cache `tokenizer.json` path.
pub const DEFAULT_QWEN35_TOKENIZER_PATH: &str = "/Users/ember/.cache/huggingface/hub/models--Qwen--Qwen3.5-0.8B-Base/snapshots/dc7cdfe2ee4154fa7e30f5b51ca41bfa40174e68/tokenizer.json";

/// Full `Qwen3.5` / `Qwen3.8` model `vocab_size` (`text_config.vocab_size = 248,320`).
pub const QWEN_VOCAB_SIZE: usize = 248_320;
/// Exact count of defined tokens in `Qwen3.5` `tokenizer.json` (`248,044` BPE + `22` `added_tokens`).
pub const QWEN_DEFINED_TOKENS: usize = 248_066;
/// Dedicated tail-padding pseudo-token ID (`is_pad = 1, len = 0, pow = 1, val = 0`) for `i >= K`.
pub const PAD_TOK_ID: u32 = 248_320;
/// Power-of-two ROM hypercube size `2^{18} = 262,144 >= 248,321`.
pub const ROM_LOG_SIZE: usize = 18;
pub const ROM_PADDED_SIZE: usize = 1usize << ROM_LOG_SIZE;

const BRIDGE_MAGIC: &[u8; 8] = b"QWBPEB01";
const ROM_LEAF_DOM: &[u8] = b"QW35-BPE-ROM-LEAF-V1";
const ROM_NODE_DOM: &[u8] = b"QW35-BPE-ROM-NODE-V1";
const T256_SALTED_LEAF_DOM: &[u8] = b"QW35-T256-SALTED-BYTE-LEAF-V1";
const T256_SALTED_NODE_DOM: &[u8] = b"QW35-T256-SALTED-BYTE-NODE-V1";
const T256_PCS_LEAF_DOM: &[u8] = b"QW35-T256-PCS-LEAF-V1";

// ===========================================================================
// §1. `Tower256` (`GF(2^256)`) Fan–Paar Level-8 Field Arithmetic (L1 Table Accelerated)
// ===========================================================================

/// Element of `GF(2^256)` in the explicit recursive Fan–Paar binary tower (`minidregg` `T_8`):
/// `T_0 = GF(2)`, `T_{k+1} = T_k[y_k] / (y_k^2 + g_k y_k + 1)` (`g_0 = 1`, `g_{k+1} = y_k`).
/// Addition and subtraction are bitwise XOR; canonical `T_3 = GF(2^8)` embeds in the low byte of `limbs[0]`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Tower256(pub [u64; 4]);

struct Gf256Tables {
    mul: [[u8; 256]; 256],
    mul_y2: [u8; 256],
}

fn mul_bits_ref(level: u8, left: u64, right: u64) -> u64 {
    if level == 0 {
        return left & right & 1;
    }
    let child = level - 1;
    let width = 1usize << child;
    let mask = if width == 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    };
    let a0 = left & mask;
    let a1 = (left >> width) & mask;
    let b0 = right & mask;
    let b1 = (right >> width) & mask;
    let p0 = mul_bits_ref(child, a0, b0);
    let p1 = mul_bits_ref(child, a1, b1);
    let mixed = mul_bits_ref(child, a0 ^ a1, b0 ^ b1) ^ p0 ^ p1;
    let p1_coeff = if child == 0 {
        p1
    } else {
        mul_by_gen_bits_ref(child, p1)
    };
    (p0 ^ p1) | ((mixed ^ p1_coeff) << width)
}

fn mul_by_gen_bits_ref(level: u8, value: u64) -> u64 {
    let child = level - 1;
    let width = 1usize << child;
    let mask = if width == 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    };
    let low = value & mask;
    let high = (value >> width) & mask;
    let reduced_high = if child == 0 {
        low ^ high
    } else {
        low ^ mul_by_gen_bits_ref(child, high)
    };
    high | (reduced_high << width)
}

fn gf256_tables() -> &'static Gf256Tables {
    static TABS: OnceLock<Box<Gf256Tables>> = OnceLock::new();
    TABS.get_or_init(|| {
        let mut tabs = Box::new(Gf256Tables {
            mul: [[0u8; 256]; 256],
            mul_y2: [0u8; 256],
        });
        for a in 0..256u64 {
            tabs.mul_y2[a as usize] = mul_by_gen_bits_ref(3, a) as u8;
            for b in 0..256u64 {
                tabs.mul[a as usize][b as usize] = mul_bits_ref(3, a, b) as u8;
            }
        }
        tabs
    })
}

#[inline(always)]
fn mul_t3(t: &Gf256Tables, a: u8, b: u8) -> u8 {
    t.mul[a as usize][b as usize]
}

#[inline(always)]
fn mul_y3_t4(t: &Gf256Tables, v: u16) -> u16 {
    let lo = (v & 0xFF) as u8;
    let hi = (v >> 8) as u8;
    let r_hi = lo ^ t.mul_y2[hi as usize];
    (hi as u16) | ((r_hi as u16) << 8)
}

#[inline(always)]
fn mul_t4(t: &Gf256Tables, a: u16, b: u16) -> u16 {
    let a0 = (a & 0xFF) as u8;
    let a1 = (a >> 8) as u8;
    let b0 = (b & 0xFF) as u8;
    let b1 = (b >> 8) as u8;
    let p0 = mul_t3(t, a0, b0);
    let p1 = mul_t3(t, a1, b1);
    let mixed = mul_t3(t, a0 ^ a1, b0 ^ b1) ^ p0 ^ p1;
    let hi = mixed ^ t.mul_y2[p1 as usize];
    ((p0 ^ p1) as u16) | ((hi as u16) << 8)
}

#[inline(always)]
fn mul_y4_t5(t: &Gf256Tables, v: u32) -> u32 {
    let lo = (v & 0xFFFF) as u16;
    let hi = (v >> 16) as u16;
    let r_hi = lo ^ mul_y3_t4(t, hi);
    (hi as u32) | ((r_hi as u32) << 16)
}

#[inline(always)]
fn mul_t5(t: &Gf256Tables, a: u32, b: u32) -> u32 {
    let a0 = (a & 0xFFFF) as u16;
    let a1 = (a >> 16) as u16;
    let b0 = (b & 0xFFFF) as u16;
    let b1 = (b >> 16) as u16;
    let p0 = mul_t4(t, a0, b0);
    let p1 = mul_t4(t, a1, b1);
    let mixed = mul_t4(t, a0 ^ a1, b0 ^ b1) ^ p0 ^ p1;
    let hi = mixed ^ mul_y3_t4(t, p1);
    ((p0 ^ p1) as u32) | ((hi as u32) << 16)
}

#[inline(always)]
fn mul_y5_t6(t: &Gf256Tables, v: u64) -> u64 {
    let lo = (v & 0xFFFF_FFFF) as u32;
    let hi = (v >> 32) as u32;
    let r_hi = lo ^ mul_y4_t5(t, hi);
    (hi as u64) | ((r_hi as u64) << 32)
}

#[inline]
fn mul_t6(t: &Gf256Tables, a: u64, b: u64) -> u64 {
    let a0 = (a & 0xFFFF_FFFF) as u32;
    let a1 = (a >> 32) as u32;
    let b0 = (b & 0xFFFF_FFFF) as u32;
    let b1 = (b >> 32) as u32;
    let p0 = mul_t5(t, a0, b0);
    let p1 = mul_t5(t, a1, b1);
    let mixed = mul_t5(t, a0 ^ a1, b0 ^ b1) ^ p0 ^ p1;
    let hi = mixed ^ mul_y4_t5(t, p1);
    ((p0 ^ p1) as u64) | ((hi as u64) << 32)
}

#[inline(always)]
fn mul_y6_t7(t: &Gf256Tables, v: [u64; 2]) -> [u64; 2] {
    [v[1], v[0] ^ mul_y5_t6(t, v[1])]
}

#[inline]
fn mul_t7(t: &Gf256Tables, a: [u64; 2], b: [u64; 2]) -> [u64; 2] {
    let p0 = mul_t6(t, a[0], b[0]);
    let p1 = mul_t6(t, a[1], b[1]);
    let mixed = mul_t6(t, a[0] ^ a[1], b[0] ^ b[1]) ^ p0 ^ p1;
    [p0 ^ p1, mixed ^ mul_y5_t6(t, p1)]
}

impl Tower256 {
    pub const ZERO: Self = Self([0, 0, 0, 0]);
    pub const ONE: Self = Self([1, 0, 0, 0]);

    /// Canonical injective embedding `UInt8 ↪ T_3 = GF(2^8) ⊂ Tower256` (`b != b' => embed(b) != embed(b')`).
    #[inline(always)]
    pub const fn from_byte_gf256(b: u8) -> Self {
        Self([b as u64, 0, 0, 0])
    }

    ///Embed a 16-bit index into `T_4 = GF(2^{16}) ⊂ Tower256` (for coset evaluation points).
    #[inline(always)]
    pub const fn from_u16_gf2_16(x: u16) -> Self {
        Self([x as u64, 0, 0, 0])
    }

    #[inline(always)]
    pub const fn is_zero(self) -> bool {
        (self.0[0] | self.0[1] | self.0[2] | self.0[3]) == 0
    }

    #[inline(always)]
    pub const fn add(self, rhs: Self) -> Self {
        Self([
            self.0[0] ^ rhs.0[0],
            self.0[1] ^ rhs.0[1],
            self.0[2] ^ rhs.0[2],
            self.0[3] ^ rhs.0[3],
        ])
    }

    /// Fast L1-table Fan–Paar `GF(2^256)` multiplication (`243` `GF(2^8)` lookups vs `6,561` bit calls).
    #[inline]
    pub fn mul(self, rhs: Self) -> Self {
        let t = gf256_tables();
        let a0 = [self.0[0], self.0[1]];
        let a1 = [self.0[2], self.0[3]];
        let b0 = [rhs.0[0], rhs.0[1]];
        let b1 = [rhs.0[2], rhs.0[3]];
        let p0 = mul_t7(t, a0, b0);
        let p1 = mul_t7(t, a1, b1);
        let m_prod = mul_t7(t, [a0[0] ^ a1[0], a0[1] ^ a1[1]], [b0[0] ^ b1[0], b0[1] ^ b1[1]]);
        let mixed = [m_prod[0] ^ p0[0] ^ p1[0], m_prod[1] ^ p0[1] ^ p1[1]];
        let p1_y6 = mul_y6_t7(t, p1);
        Self([p0[0] ^ p1[0], p0[1] ^ p1[1], mixed[0] ^ p1_y6[0], mixed[1] ^ p1_y6[1]])
    }

    /// Reference bit-recursive multiplication matching `minidregg/prover/src/binary_tower_256.rs` line-for-line.
    pub fn mul_ref_recursive(self, rhs: Self) -> Self {
        fn mul7_ref(a: [u64; 2], b: [u64; 2]) -> [u64; 2] {
            let p0 = mul_bits_ref(6, a[0], b[0]);
            let p1 = mul_bits_ref(6, a[1], b[1]);
            let mixed = mul_bits_ref(6, a[0] ^ a[1], a[0] ^ a[0] ^ b[0] ^ b[1]) ^ p0 ^ p1;
            [p0 ^ p1, mixed ^ mul_by_gen_bits_ref(6, p1)]
        }
        let a0 = [self.0[0], self.0[1]];
        let a1 = [self.0[2], self.0[3]];
        let b0 = [rhs.0[0], rhs.0[1]];
        let b1 = [rhs.0[2], rhs.0[3]];
        let p0 = mul7_ref(a0, b0);
        let p1 = mul7_ref(a1, b1);
        let m = mul7_ref([a0[0] ^ a1[0], a0[1] ^ a1[1]], [b0[0] ^ b1[0], b0[1] ^ b1[1]]);
        let mixed = [m[0] ^ p0[0] ^ p1[0], m[1] ^ p0[1] ^ p1[1]];
        let py6 = [p1[1], p1[0] ^ mul_by_gen_bits_ref(6, p1[1])];
        Self([p0[0] ^ p1[0], p0[1] ^ p1[1], mixed[0] ^ py6[0], mixed[1] ^ py6[1]])
    }

    #[inline]
    pub fn square(self) -> Self {
        self.mul(self)
    }

    /// 8-th Frobenius automorphism `\phi(x) = x^{256}` (`x.pow256() == x` iff `x in GF(2^8)`!).
    #[inline]
    pub fn pow256(mut self) -> Self {
        for _ in 0..8 {
            self = self.square();
        }
        self
    }

    /// Inverse of `\phi(x) = x^{256}` on `GF(2^256)`: `\phi^{-1}(x) = x^{2^{248}}` (`248` squarings).
    #[inline]
    pub fn inv_pow256(mut self) -> Self {
        for _ in 0..248 {
            self = self.square();
        }
        self
    }

    pub fn pow_u64(mut self, mut exp: u64) -> Self {
        let mut acc = Self::ONE;
        while exp > 0 {
            if (exp & 1) != 0 {
                acc = acc.mul(self);
            }
            self = self.square();
            exp >>= 1;
        }
        acc
    }

    pub fn inverse(self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }
        let mut acc = self;
        for _ in 1..255 {
            acc = acc.square().mul(self);
        }
        Some(acc.square())
    }

    #[inline]
    pub fn to_le_bytes(self) -> [u8; 32] {
        let mut out = [0u8; 32];
        for i in 0..4 {
            out[8 * i..8 * (i + 1)].copy_from_slice(&self.0[i].to_le_bytes());
        }
        out
    }

    #[inline]
    pub fn from_le_bytes(bytes: &[u8; 32]) -> Self {
        let mut limbs = [0u64; 4];
        for i in 0..4 {
            limbs[i] = u64::from_le_bytes(bytes[8 * i..8 * (i + 1)].try_into().unwrap());
        }
        Self(limbs)
    }
}

/// Squeeze a 256-bit challenge in `Tower256` (`nonzero = true` rejects `0`), drawing 3 independent
/// `Ext4` limbs (`12` BabyBear elements = `370.88` bits `>> 256` bits) so `cSHAKE256` covers the
/// full `2^{256}` `Tower256` carrier (`< 2^{-57.4}` statistical distance from uniform).
pub fn squeeze_t256(tr: &mut CShakeTranscript, label: &[u8], nonzero: bool) -> Tower256 {
    let mut ctr = 0u32;
    loop {
        let mut lbl = Vec::with_capacity(label.len() + 8);
        lbl.extend_from_slice(label);
        lbl.extend_from_slice(&ctr.to_le_bytes());
        let p0 = tr.squeeze_ext4(&lbl, false).to_bytes();
        lbl.push(0xFE);
        let p1 = tr.squeeze_ext4(&lbl, false).to_bytes();
        lbl.push(0xFF);
        let p2 = tr.squeeze_ext4(&lbl, false).to_bytes();
        let mut seed = [0u8; 48];
        seed[..16].copy_from_slice(&p0);
        seed[16..32].copy_from_slice(&p1);
        seed[32..48].copy_from_slice(&p2);
        let raw = cshake256_32(b"QW35-SQUEEZE-T256-UNIFORM-V2", &seed);
        let elem = Tower256::from_le_bytes(&raw);
        if !nonzero || !elem.is_zero() {
            return elem;
        }
        ctr += 1;
    }
}

pub fn squeeze_t256_vec(tr: &mut CShakeTranscript, label: &[u8], len: usize, nonzero: bool) -> Vec<Tower256> {
    (0..len)
        .map(|i| {
            let mut l = Vec::with_capacity(label.len() + 4);
            l.extend_from_slice(label);
            l.extend_from_slice(&(i as u32).to_le_bytes());
            squeeze_t256(tr, &l, nonzero)
        })
        .collect()
}

/// Evaluate `evalBytesWith(Tower256::from_byte_gf256, base, bytes)` in `GF(2^256)`.
#[inline]
pub fn eval_bytes_t256(base: Tower256, bytes: &[u8]) -> Tower256 {
    let mut acc = Tower256::ZERO;
    for &b in bytes {
        acc = acc.mul(base).add(Tower256::from_byte_gf256(b));
    }
    acc
}

/// Evaluate `evalBytesBase(base, bytes)` in `BabyBear Ext4` (`X^4 - 11`).
#[inline]
pub fn eval_bytes_ext4(base: Ext4, bytes: &[u8]) -> Ext4 {
    let mut acc = Ext4::ZERO;
    for &b in bytes {
        acc = acc.mul(base).add(Ext4::from_bb(b as u32));
    }
    acc
}

#[inline]
pub fn ext4_pow(mut base: Ext4, mut exp: u64) -> Ext4 {
    let mut acc = Ext4::ONE;
    while exp > 0 {
        if (exp & 1) != 0 {
            acc = acc.mul(base);
        }
        base = base.sq();
        exp >>= 1;
    }
    acc
}

// ===========================================================================
// §2. `p61` Deterministic Miller–Rabin Prime Squeeze & `IntegerFingerprint` Rolling Evaluation
// ===========================================================================

fn mod_pow_u64(mut base: u64, mut exp: u64, m: u64) -> u64 {
    let mut acc = 1u64 % m;
    base %= m;
    while exp > 0 {
        if (exp & 1) != 0 {
            acc = (((acc as u128) * (base as u128)) % (m as u128)) as u64;
        }
        base = (((base as u128) * (base as u128)) % (m as u128)) as u64;
        exp >>= 1;
    }
    acc
}

/// Exact deterministic Miller–Rabin primality test for all `n < 2^64` (Sinclair 7-base witness set).
pub fn is_prime_u64_exact(n: u64) -> bool {
    if n < 2 {
        return false;
    }
    for &p in &[2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if n == p {
            return true;
        }
        if n % p == 0 {
            return false;
        }
    }
    let d_full = n - 1;
    let s = d_full.trailing_zeros();
    let d = d_full >> s;
    for &a in &[2u64, 325, 9_375, 28_178, 450_775, 9_780_504, 1_795_265_022] {
        let a_mod = a % n;
        if a_mod == 0 {
            continue;
        }
        let mut x = mod_pow_u64(a_mod, d, n);
        if x == 1 || x == n - 1 {
            continue;
        }
        let mut composite = true;
        for _ in 1..s {
            x = (((x as u128) * (x as u128)) % (n as u128)) as u64;
            if x == n - 1 {
                composite = false;
                break;
            }
        }
        if composite {
            return false;
        }
    }
    true
}

/// Squeeze a Fiat–Shamir 61-bit prime `p in [2^60 + 1, 2^61)` (`Theory.IntegerFingerprint` `P_floor = 2^60`).
pub fn squeeze_prime_61bit(tr: &mut CShakeTranscript, label: &[u8]) -> u64 {
    let mut ctr = 0u32;
    loop {
        let mut lbl = Vec::with_capacity(label.len() + 4);
        lbl.extend_from_slice(label);
        lbl.extend_from_slice(&ctr.to_le_bytes());
        let raw = cshake256_32(b"QW35-FP-PRIME61-V1", &tr.squeeze_ext4(&lbl, false).to_bytes());
        let v = u64::from_le_bytes(raw[..8].try_into().unwrap());
        let cand = ((v & ((1u64 << 60) - 1)) | (1u64 << 60)) | 1;
        if is_prime_u64_exact(cand) {
            return cand;
        }
        ctr += 1;
    }
}

/// Evaluate `evalBytesBase (256 : ZMod p) bytes` over `ZMod p`.
#[inline]
pub fn eval_bytes_mod_p61(p: u64, bytes: &[u8]) -> u64 {
    let pm = p as u128;
    let mut acc = 0u128;
    for &b in bytes {
        acc = (acc * 256 + (b as u128)) % pm;
    }
    acc as u64
}

// ===========================================================================
// §3. Succinct ZK `Tower256` Coset-RS Matrix MLE PCS & Zero-Inversion Char-2 Quadratic Sumcheck
// ===========================================================================

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Tower256PcsShape {
    pub m: usize,
    pub mc: usize,
    pub mr: usize,
    pub c_data: usize,
    pub r_data: usize,
    pub w_poly: usize,
    pub n_pts: usize,
    pub t_cols: usize,
    pub max_evals: usize,
    pub r_total: usize,
}

impl Tower256PcsShape {
    pub fn new(m: usize, max_evals: usize) -> Self {
        let mc = (m / 2).clamp(2, 5);
        let mr = m.saturating_sub(mc);
        let c_data = 1usize << mc;
        let r_data = 1usize << mr;
        // `t_cols = 208, blowup = 8` -> `103.5` bits unconditional `[AHIV17]` `d/3` UD & `172.6` bits `[BCIKS20]` UD!
        let t_cols = 208usize;
        let w_poly = (c_data + t_cols).next_power_of_two().max(c_data * 2);
        let n_pts = 8 * w_poly;
        let r_total = r_data + max_evals + 1; // `+ max_evals` eval mask rows `+ 1` proximity mask row
        Self {
            m,
            mc,
            mr,
            c_data,
            r_data,
            w_poly,
            n_pts,
            t_cols,
            max_evals,
            r_total,
        }
    }
}

struct T256CodewordBasis {
    /// `[c_idx * n_pts + pt_idx]` Lagrange basis polynomial `L_{c_idx}(x_{pt_idx})` where `H_0 = 0..w_poly`
    /// and evaluation coset `D = w_poly .. w_poly + n_pts` in `GF(2^{16}) ⊂ Tower256` (`H_0 ∩ D = ∅`!).
    lagrange_to_coset: Vec<Tower256>,
    /// `[c_idx * w_poly + coeff_k]` monomial coefficients of `L_{c_idx}(X)` (`deg < w_poly`).
    lagrange_to_coeffs: Vec<Tower256>,
}

fn t256_codeword_basis(w_poly: usize, n_pts: usize) -> &'static T256CodewordBasis {
    static CACHE: OnceLock<std::sync::Mutex<HashMap<(usize, usize), &'static T256CodewordBasis>>> =
        OnceLock::new();
    let map_mutex = CACHE.get_or_init(|| std::sync::Mutex::new(HashMap::new()));
    let mut guard = map_mutex.lock().unwrap();
    if let Some(&cached) = guard.get(&(w_poly, n_pts)) {
        return cached;
    }
    assert!(w_poly + n_pts <= 65536);
    let h_pts: Vec<Tower256> = (0..w_poly)
        .map(|i| Tower256::from_u16_gf2_16(i as u16))
        .collect();
    let d_pts: Vec<Tower256> = (0..n_pts)
        .map(|k| Tower256::from_u16_gf2_16((w_poly + k) as u16))
        .collect();

    // `Z_H(X) = \prod_{i=0}^{w_poly - 1} (X + h_i)` in `Tower256[X]` (`deg == w_poly`)
    let mut z_coeffs = vec![Tower256::ZERO; w_poly + 1];
    z_coeffs[0] = Tower256::ONE;
    for (deg, &hi) in h_pts.iter().enumerate() {
        for k in (1..=deg + 1).rev() {
            z_coeffs[k] = z_coeffs[k - 1].add(z_coeffs[k].mul(hi));
        }
        z_coeffs[0] = z_coeffs[0].mul(hi);
    }

    let per_i: Vec<(Vec<Tower256>, Vec<Tower256>)> = (0..w_poly)
        .into_par_iter()
        .map(|i| {
            let hi = h_pts[i];
            let mut q = vec![Tower256::ZERO; w_poly];
            q[w_poly - 1] = z_coeffs[w_poly];
            for k in (0..w_poly - 1).rev() {
                q[k] = z_coeffs[k + 1].add(q[k + 1].mul(hi));
            }
            let mut denom = Tower256::ZERO;
            for &ck in q.iter().rev() {
                denom = denom.mul(hi).add(ck);
            }
            let inv_denom = denom.inverse().expect("distinct GF(2^16) points");
            for ck in &mut q {
                *ck = ck.mul(inv_denom);
            }
            let mut coset_row = vec![Tower256::ZERO; n_pts];
            for (pt_idx, &xk) in d_pts.iter().enumerate() {
                let mut ev = Tower256::ZERO;
                for &ck in q.iter().rev() {
                    ev = ev.mul(xk).add(ck);
                }
                coset_row[pt_idx] = ev;
            }
            (q, coset_row)
        })
        .collect();

    let mut lagrange_to_coeffs = vec![Tower256::ZERO; w_poly * w_poly];
    let mut lagrange_to_coset = vec![Tower256::ZERO; w_poly * n_pts];
    for (i, (q, coset_row)) in per_i.into_iter().enumerate() {
        lagrange_to_coeffs[i * w_poly..(i + 1) * w_poly].copy_from_slice(&q);
        lagrange_to_coset[i * n_pts..(i + 1) * n_pts].copy_from_slice(&coset_row);
    }

    let leaked: &'static T256CodewordBasis = Box::leak(Box::new(T256CodewordBasis {
        lagrange_to_coset,
        lagrange_to_coeffs,
    }));
    guard.insert((w_poly, n_pts), leaked);
    leaked
}

/// Pre-warm `Tower256Pcs` Lagrange-to-coset basis tables so steady-state prover benchmarks measure proving only.
pub fn warm_t256_pcs_basis(m_vals: &[usize], max_evals: usize) {
    for &m in m_vals {
        let sh = Tower256PcsShape::new(m, max_evals);
        let _ = t256_codeword_basis(sh.w_poly, sh.n_pts);
    }
}

#[inline]
fn eval_poly_t256(coeffs: &[Tower256], x: Tower256) -> Tower256 {
    let mut acc = Tower256::ZERO;
    for &c in coeffs.iter().rev() {
        acc = acc.mul(x).add(c);
    }
    acc
}

fn t256_pcs_col_hash(col_idx: usize, salt: &[u8; 16], col_vals: &[Tower256]) -> [u8; 32] {
    let mut buf = Vec::with_capacity(4 + 16 + col_vals.len() * 32);
    buf.extend_from_slice(&(col_idx as u32).to_le_bytes());
    buf.extend_from_slice(salt);
    for &v in col_vals {
        buf.extend_from_slice(&v.to_le_bytes());
    }
    cshake256_32(T256_PCS_LEAF_DOM, &buf)
}

fn build_merkle_tree_levels(node_dom: &[u8], leaves: &[[u8; 32]]) -> Vec<Vec<[u8; 32]>> {
    assert!(leaves.len().is_power_of_two());
    let mut levels = Vec::new();
    levels.push(leaves.to_vec());
    let mut lvl = 0u8;
    while levels.last().unwrap().len() > 1 {
        let prev = levels.last().unwrap();
        let next: Vec<[u8; 32]> = prev
            .par_chunks_exact(2)
            .enumerate()
            .map(|(idx, pair)| merkle_node_cshake(node_dom, lvl, idx as u32, &pair[0], &pair[1]))
            .collect();
        levels.push(next);
        lvl += 1;
    }
    levels
}

pub struct Tower256PcsState {
    pub shape: Tower256PcsShape,
    pub root: [u8; 32],
    pub row_evals_h0: Vec<Tower256>,
    pub row_coeffs: Vec<Tower256>,
    pub col_codewords: Vec<Tower256>,
    pub salts: Vec<[u8; 16]>,
    pub tree_levels: Vec<Vec<[u8; 32]>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tower256MleClaim {
    pub point: Vec<Tower256>,
    pub value: Tower256,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tower256PcsProof {
    pub m: usize,
    pub max_evals: usize,
    pub s_masks: Vec<Tower256>,
    pub u_eval_polys: Vec<Vec<Tower256>>,
    pub u_prox_poly: Vec<Tower256>,
    pub opened_salts: Vec<[u8; 16]>,
    pub opened_cols: Vec<Tower256>,
    pub multiproof: MerkleMultiProof,
}

impl Tower256PcsProof {
    pub fn write_to(&self, out: &mut Vec<u8>) {
        out.push(self.m as u8);
        out.push(self.max_evals as u8);
        for &s in &self.s_masks {
            out.extend_from_slice(&s.to_le_bytes());
        }
        for poly in &self.u_eval_polys {
            out.extend_from_slice(&(poly.len() as u32).to_le_bytes());
            for &c in poly {
                out.extend_from_slice(&c.to_le_bytes());
            }
        }
        out.extend_from_slice(&(self.u_prox_poly.len() as u32).to_le_bytes());
        for &c in &self.u_prox_poly {
            out.extend_from_slice(&c.to_le_bytes());
        }
        out.extend_from_slice(&(self.opened_salts.len() as u32).to_le_bytes());
        for s in &self.opened_salts {
            out.extend_from_slice(s);
        }
        out.extend_from_slice(&(self.opened_cols.len() as u32).to_le_bytes());
        for &v in &self.opened_cols {
            out.extend_from_slice(&v.to_le_bytes());
        }
        self.multiproof.write_to(out);
    }

    pub fn read_from(cur: &mut ByteCursor) -> Result<Self, String> {
        let m = cur.read_u8()? as usize;
        let max_evals = cur.read_u8()? as usize;
        if m < 2 || m > 20 || max_evals == 0 || max_evals > 8 {
            return Err("invalid Tower256PcsProof header".to_string());
        }
        let shape = Tower256PcsShape::new(m, max_evals);
        let mut s_masks = Vec::with_capacity(max_evals);
        for _ in 0..max_evals {
            s_masks.push(Tower256::from_le_bytes(&cur.read_arr32()?));
        }
        let mut u_eval_polys = Vec::with_capacity(max_evals);
        for _ in 0..max_evals {
            let len = cur.read_u32()? as usize;
            if len != shape.w_poly || cur.remaining() < len * 32 {
                return Err("Tower256PcsProof u_eval_poly len/EOF mismatch".to_string());
            }
            let mut p = Vec::with_capacity(len);
            for _ in 0..len {
                p.push(Tower256::from_le_bytes(&cur.read_arr32()?));
            }
            u_eval_polys.push(p);
        }
        let prox_len = cur.read_u32()? as usize;
        if prox_len != shape.w_poly || cur.remaining() < prox_len * 32 {
            return Err("Tower256PcsProof u_prox_poly len/EOF mismatch".to_string());
        }
        let mut u_prox_poly = Vec::with_capacity(prox_len);
        for _ in 0..prox_len {
            u_prox_poly.push(Tower256::from_le_bytes(&cur.read_arr32()?));
        }
        let n_salts = cur.read_u32()? as usize;
        if n_salts != shape.t_cols || cur.remaining() < n_salts * 16 {
            return Err("Tower256PcsProof opened_salts count/EOF mismatch".to_string());
        }
        let mut opened_salts = Vec::with_capacity(n_salts);
        for _ in 0..n_salts {
            opened_salts.push(cur.read_arr16()?);
        }
        let n_vals = cur.read_u32()? as usize;
        if n_vals != shape.t_cols * shape.r_total || cur.remaining() < n_vals * 32 {
            return Err("Tower256PcsProof opened_cols count/EOF mismatch".to_string());
        }
        let mut opened_cols = Vec::with_capacity(n_vals);
        for _ in 0..n_vals {
            opened_cols.push(Tower256::from_le_bytes(&cur.read_arr32()?));
        }
        let multiproof = MerkleMultiProof::read_from(cur)?;
        Ok(Self {
            m,
            max_evals,
            s_masks,
            u_eval_polys,
            u_prox_poly,
            opened_salts,
            opened_cols,
            multiproof,
        })
    }
}

pub fn build_eq_table_lsb_t256(r: &[Tower256]) -> Vec<Tower256> {
    if r.is_empty() {
        return vec![Tower256::ONE];
    }
    let mut tbl = Vec::with_capacity(1usize << r.len());
    tbl.push(Tower256::ONE.add(r[0]));
    tbl.push(r[0]);
    for &ri in &r[1..] {
        let cur_len = tbl.len();
        for idx in 0..cur_len {
            let base = tbl[idx];
            let hi = base.mul(ri);
            tbl[idx] = base.add(hi);
            tbl.push(hi);
        }
    }
    tbl
}

#[inline]
pub fn eq_lin_t256(r: Tower256, x: Tower256) -> Tower256 {
    Tower256::ONE.add(r).mul(Tower256::ONE.add(x)).add(r.mul(x))
}

pub fn eq_mle_t256(z: &[Tower256], x: &[Tower256]) -> Tower256 {
    assert_eq!(z.len(), x.len());
    z.iter()
        .zip(x.iter())
        .fold(Tower256::ONE, |acc, (&zj, &xj)| acc.mul(eq_lin_t256(zj, xj)))
}

pub fn mle_eval_t256(tab: &[Tower256], pt: &[Tower256]) -> Tower256 {
    assert_eq!(tab.len(), 1usize << pt.len());
    let eq = build_eq_table_lsb_t256(pt);
    let mut acc = Tower256::ZERO;
    for (&v, &w) in tab.iter().zip(eq.iter()) {
        acc = acc.add(v.mul(w));
    }
    acc
}

pub fn commit_t256_pcs(table: &[Tower256], max_evals: usize, seed_opt: Option<[u8; 32]>) -> Tower256PcsState {
    assert!(table.len() >= 4 && table.len().is_power_of_two());
    let m = table.len().trailing_zeros() as usize;
    let shape = Tower256PcsShape::new(m, max_evals);
    let basis = t256_codeword_basis(shape.w_poly, shape.n_pts);

    let seed = seed_opt.unwrap_or_else(os_random_seed_32);
    let mut rng = CShakeRng::from_seed(b"QW35-T256-PCS-MASK-V1", &seed);

    let mut row_evals_h0 = vec![Tower256::ZERO; shape.r_total * shape.w_poly];
    // Copy data matrix `[r_data × c_data]` (`idx = col + row * c_data` -> LSB `mc` bits = col, MSB `mr` bits = row)
    for r in 0..shape.r_data {
        for c in 0..shape.c_data {
            row_evals_h0[r * shape.w_poly + c] = table[r * shape.c_data + c];
        }
        // Shamir column-hiding random tail on `c_data .. w_poly` (`w_poly - c_data >= t_cols` -> perfect HVZK!)
        for c in shape.c_data..shape.w_poly {
            let mut rb = [0u8; 32];
            rng.fill_bytes(&mut rb);
            row_evals_h0[r * shape.w_poly + c] = Tower256::from_le_bytes(&rb);
        }
    }
    // Mask rows `r_data .. r_total`
    for r in shape.r_data..shape.r_total {
        for c in 0..shape.w_poly {
            let mut rb = [0u8; 32];
            rng.fill_bytes(&mut rb);
            row_evals_h0[r * shape.w_poly + c] = Tower256::from_le_bytes(&rb);
        }
    }

    let mut row_coeffs = vec![Tower256::ZERO; shape.r_total * shape.w_poly];
    let mut col_codewords = vec![Tower256::ZERO; shape.n_pts * shape.r_total];

    let row_results: Vec<(Vec<Tower256>, Vec<Tower256>)> = (0..shape.r_total)
        .into_par_iter()
        .map(|r| {
            let h_row = &row_evals_h0[r * shape.w_poly..(r + 1) * shape.w_poly];
            let mut coeffs = vec![Tower256::ZERO; shape.w_poly];
            let mut coset = vec![Tower256::ZERO; shape.n_pts];
            for (i, &val) in h_row.iter().enumerate() {
                if val.is_zero() {
                    continue;
                }
                let lc = &basis.lagrange_to_coeffs[i * shape.w_poly..(i + 1) * shape.w_poly];
                for k in 0..shape.w_poly {
                    coeffs[k] = coeffs[k].add(val.mul(lc[k]));
                }
                let ld = &basis.lagrange_to_coset[i * shape.n_pts..(i + 1) * shape.n_pts];
                for pt in 0..shape.n_pts {
                    coset[pt] = coset[pt].add(val.mul(ld[pt]));
                }
            }
            (coeffs, coset)
        })
        .collect();

    for (r, (coeffs, coset)) in row_results.into_iter().enumerate() {
        row_coeffs[r * shape.w_poly..(r + 1) * shape.w_poly].copy_from_slice(&coeffs);
        for pt in 0..shape.n_pts {
            col_codewords[pt * shape.r_total + r] = coset[pt];
        }
    }

    let mut salts = vec![[0u8; 16]; shape.n_pts];
    for s in &mut salts {
        rng.fill_bytes(s);
    }

    let leaves: Vec<[u8; 32]> = (0..shape.n_pts)
        .into_par_iter()
        .map(|pt| {
            t256_pcs_col_hash(
                pt,
                &salts[pt],
                &col_codewords[pt * shape.r_total..(pt + 1) * shape.r_total],
            )
        })
        .collect();
    // Note: `MerkleMultiProof::verify` uses `PCS_NODE_DOM = b"QW35-PCS-NODE-V1"` in `pcs_ext4.rs`!
    let tree_levels = build_merkle_tree_levels(b"QW35-PCS-NODE-V1", &leaves);
    let root = tree_levels.last().unwrap()[0];

    Tower256PcsState {
        shape,
        root,
        row_evals_h0,
        row_coeffs,
        col_codewords,
        salts,
        tree_levels,
    }
}

pub fn open_t256_pcs(
    state: &Tower256PcsState,
    claims: &[Tower256MleClaim],
    tr: &mut CShakeTranscript,
) -> Tower256PcsProof {
    let shape = state.shape;
    assert_eq!(claims.len(), shape.max_evals);
    tr.absorb_root(b"t256_pcs_open_root", &state.root);
    for (idx, cl) in claims.iter().enumerate() {
        assert_eq!(cl.point.len(), shape.m);
        tr.absorb_u32(b"t256_cl_idx", idx as u32);
        for &p in &cl.point {
            tr.absorb_bytes(b"t256_cl_pt", &p.to_le_bytes());
        }
        tr.absorb_bytes(b"t256_cl_val", &cl.value.to_le_bytes());
    }

    let mut s_masks = Vec::with_capacity(shape.max_evals);
    let mut u_eval_polys = Vec::with_capacity(shape.max_evals);

    for (idx, cl) in claims.iter().enumerate() {
        let eq_col = build_eq_table_lsb_t256(&cl.point[..shape.mc]);
        let eq_row = build_eq_table_lsb_t256(&cl.point[shape.mc..]);
        let mask_row = shape.r_data + idx;

        let mut s_mask = Tower256::ZERO;
        for c in 0..shape.c_data {
            s_mask = s_mask.add(state.row_evals_h0[mask_row * shape.w_poly + c].mul(eq_col[c]));
        }
        // Absorb `s_mask` BEFORE squeezing `beta_zk` so `s_mask` cannot be shifted post-hoc (`< 2^{-255}` error)!
        tr.absorb_bytes(b"t256_smask", &s_mask.to_le_bytes());
        let beta_zk = squeeze_t256(tr, b"t256_beta_zk", true);

        let mut u_coeffs: Vec<Tower256> = state.row_coeffs
            [mask_row * shape.w_poly..(mask_row + 1) * shape.w_poly]
            .iter()
            .map(|&mc| beta_zk.mul(mc))
            .collect();
        for r in 0..shape.r_data {
            let w_r = eq_row[r];
            let rc = &state.row_coeffs[r * shape.w_poly..(r + 1) * shape.w_poly];
            for k in 0..shape.w_poly {
                u_coeffs[k] = u_coeffs[k].add(w_r.mul(rc[k]));
            }
        }
        for &uc in &u_coeffs {
            tr.absorb_bytes(b"t256_ueval", &uc.to_le_bytes());
        }
        s_masks.push(s_mask);
        u_eval_polys.push(u_coeffs);
    }

    let prox_chals = squeeze_t256_vec(tr, b"t256_prox_r", shape.r_total, true);
    let mut u_prox_poly = vec![Tower256::ZERO; shape.w_poly];
    for r in 0..shape.r_total {
        let gamma = prox_chals[r];
        let rc = &state.row_coeffs[r * shape.w_poly..(r + 1) * shape.w_poly];
        for k in 0..shape.w_poly {
            u_prox_poly[k] = u_prox_poly[k].add(gamma.mul(rc[k]));
        }
    }
    for &uc in &u_prox_poly {
        tr.absorb_bytes(b"t256_uprox", &uc.to_le_bytes());
    }

    let queried = tr.squeeze_distinct_indices(b"t256_q_cols", shape.n_pts, shape.t_cols);
    let mut opened_salts = Vec::with_capacity(shape.t_cols);
    let mut opened_cols = Vec::with_capacity(shape.t_cols * shape.r_total);
    for &col_idx in &queried {
        opened_salts.push(state.salts[col_idx]);
        opened_cols.extend_from_slice(&state.col_codewords[col_idx * shape.r_total..(col_idx + 1) * shape.r_total]);
    }
    let multiproof = MerkleMultiProof::build(&state.tree_levels, &queried);

    Tower256PcsProof {
        m: shape.m,
        max_evals: shape.max_evals,
        s_masks,
        u_eval_polys,
        u_prox_poly,
        opened_salts,
        opened_cols,
        multiproof,
    }
}

pub fn verify_t256_pcs(
    expected_root: &[u8; 32],
    claims: &[Tower256MleClaim],
    proof: &Tower256PcsProof,
    tr: &mut CShakeTranscript,
) -> Result<(), String> {
    let shape = Tower256PcsShape::new(proof.m, proof.max_evals);
    if claims.len() != shape.max_evals
        || proof.s_masks.len() != shape.max_evals
        || proof.u_eval_polys.len() != shape.max_evals
    {
        return Err("Tower256Pcs claim count mismatch".to_string());
    }

    tr.absorb_root(b"t256_pcs_open_root", expected_root);
    for (idx, cl) in claims.iter().enumerate() {
        if cl.point.len() != shape.m {
            return Err("Tower256Pcs point dimension mismatch".to_string());
        }
        tr.absorb_u32(b"t256_cl_idx", idx as u32);
        for &p in &cl.point {
            tr.absorb_bytes(b"t256_cl_pt", &p.to_le_bytes());
        }
        tr.absorb_bytes(b"t256_cl_val", &cl.value.to_le_bytes());
    }

    let mut eq_rows = Vec::with_capacity(shape.max_evals);
    let mut beta_zks = Vec::with_capacity(shape.max_evals);
    for (idx, cl) in claims.iter().enumerate() {
        let u_coeffs = &proof.u_eval_polys[idx];
        if u_coeffs.len() != shape.w_poly {
            return Err("Tower256Pcs u_eval degree mismatch".to_string());
        }
        let s_mask = proof.s_masks[idx];
        tr.absorb_bytes(b"t256_smask", &s_mask.to_le_bytes());
        let beta_zk = squeeze_t256(tr, b"t256_beta_zk", true);
        beta_zks.push(beta_zk);
        for &uc in u_coeffs {
            tr.absorb_bytes(b"t256_ueval", &uc.to_le_bytes());
        }
        // Check `sum_{c=0}^{c_data - 1} u_eval(h_c) * eq_col[c] == cl.value + beta_zk * s_mask`!
        let eq_col = build_eq_table_lsb_t256(&cl.point[..shape.mc]);
        let mut lhs = Tower256::ZERO;
        for c in 0..shape.c_data {
            let hc = Tower256::from_u16_gf2_16(c as u16);
            lhs = lhs.add(eval_poly_t256(u_coeffs, hc).mul(eq_col[c]));
        }
        if lhs != cl.value.add(beta_zk.mul(s_mask)) {
            return Err(format!("Tower256Pcs claim {idx} H_0 evaluation identity failed"));
        }
        eq_rows.push(build_eq_table_lsb_t256(&cl.point[shape.mc..]));
    }

    let prox_chals = squeeze_t256_vec(tr, b"t256_prox_r", shape.r_total, true);
    if proof.u_prox_poly.len() != shape.w_poly {
        return Err("Tower256Pcs u_prox degree mismatch".to_string());
    }
    for &uc in &proof.u_prox_poly {
        tr.absorb_bytes(b"t256_uprox", &uc.to_le_bytes());
    }

    let queried = tr.squeeze_distinct_indices(b"t256_q_cols", shape.n_pts, shape.t_cols);
    if proof.opened_salts.len() != shape.t_cols
        || proof.opened_cols.len() != shape.t_cols * shape.r_total
    {
        return Err("Tower256Pcs opened column shape mismatch".to_string());
    }

    let mut leaf_hashes = Vec::with_capacity(shape.t_cols);
    for (q_pos, &col_idx) in queried.iter().enumerate() {
        let col_slice = &proof.opened_cols[q_pos * shape.r_total..(q_pos + 1) * shape.r_total];
        leaf_hashes.push(t256_pcs_col_hash(col_idx, &proof.opened_salts[q_pos], col_slice));

        let x_pt = Tower256::from_u16_gf2_16((shape.w_poly + col_idx) as u16);
        // 1. Proximity check against `u_prox_poly(x_pt)`
        let mut col_prox = Tower256::ZERO;
        for r in 0..shape.r_total {
            col_prox = col_prox.add(prox_chals[r].mul(col_slice[r]));
        }
        if col_prox != eval_poly_t256(&proof.u_prox_poly, x_pt) {
            return Err(format!("Tower256Pcs proximity check failed at column {col_idx}"));
        }
        // 2. Per-claim row fold check against `u_eval_polys[idx](x_pt)` (`beta_zk * mask_row + \sum eq_row * row`)
        for idx in 0..shape.max_evals {
            let mut col_ev = beta_zks[idx].mul(col_slice[shape.r_data + idx]);
            for r in 0..shape.r_data {
                col_ev = col_ev.add(eq_rows[idx][r].mul(col_slice[r]));
            }
            if col_ev != eval_poly_t256(&proof.u_eval_polys[idx], x_pt) {
                return Err(format!("Tower256Pcs claim {idx} column fold failed at {col_idx}"));
            }
        }
    }

    if !proof
        .multiproof
        .verify(expected_root, shape.n_pts, &queried, &leaf_hashes)
    {
        return Err("Tower256Pcs cSHAKE256 Merkle multiproof failed".to_string());
    }
    Ok(())
}

/// Zero-inversion `{q(0), q(1), q(∞)}` quadratic sumcheck round message over `Tower256` (`char = 2`!):
/// `q(X) = q0 \oplus (q0 \oplus q1 \oplus q_inf) * X \oplus q_inf * X^2` (`0` divisions by `2`!).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Tower256QuadRoundMsg {
    pub q0: Tower256,
    pub q1: Tower256,
    pub q_inf: Tower256,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tower256QuadSumcheckProof {
    pub claim: Tower256,
    pub rounds: Vec<Tower256QuadRoundMsg>,
    pub term_a: Tower256,
    pub term_b: Tower256,
}

impl Tower256QuadSumcheckProof {
    pub fn write_to(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.claim.to_le_bytes());
        out.push(self.rounds.len() as u8);
        for r in &self.rounds {
            out.extend_from_slice(&r.q0.to_le_bytes());
            out.extend_from_slice(&r.q1.to_le_bytes());
            out.extend_from_slice(&r.q_inf.to_le_bytes());
        }
        out.extend_from_slice(&self.term_a.to_le_bytes());
        out.extend_from_slice(&self.term_b.to_le_bytes());
    }

    pub fn read_from(cur: &mut ByteCursor) -> Result<Self, String> {
        let claim = Tower256::from_le_bytes(&cur.read_arr32()?);
        let n = cur.read_u8()? as usize;
        if n == 0 || n > 20 {
            return Err("invalid Tower256QuadSumcheckProof round count".to_string());
        }
        let mut rounds = Vec::with_capacity(n);
        for _ in 0..n {
            rounds.push(Tower256QuadRoundMsg {
                q0: Tower256::from_le_bytes(&cur.read_arr32()?),
                q1: Tower256::from_le_bytes(&cur.read_arr32()?),
                q_inf: Tower256::from_le_bytes(&cur.read_arr32()?),
            });
        }
        let term_a = Tower256::from_le_bytes(&cur.read_arr32()?);
        let term_b = Tower256::from_le_bytes(&cur.read_arr32()?);
        Ok(Self {
            claim,
            rounds,
            term_a,
            term_b,
        })
    }
}

/// Prove `claim = \sum_{x \in {0,1}^m} left[x] * right[x]` over `Tower256` (`0` prover inversions!).
pub fn prove_t256_quad_sumcheck(
    left: &[Tower256],
    right: &[Tower256],
    tr: &mut CShakeTranscript,
) -> (Tower256QuadSumcheckProof, Vec<Tower256>) {
    assert_eq!(left.len(), right.len());
    assert!(left.len() >= 2 && left.len().is_power_of_two());
    let m = left.len().trailing_zeros() as usize;

    let mut claim = Tower256::ZERO;
    for (&a, &b) in left.iter().zip(right.iter()) {
        claim = claim.add(a.mul(b));
    }
    tr.absorb_bytes(b"t256_sc_claim", &claim.to_le_bytes());

    let mut l_cur = left.to_vec();
    let mut r_cur = right.to_vec();
    let mut rounds = Vec::with_capacity(m);
    let mut chals = Vec::with_capacity(m);

    for _ in 0..m {
        let half = l_cur.len() / 2;
        let mut q0 = Tower256::ZERO;
        let mut q1 = Tower256::ZERO;
        let mut q_inf = Tower256::ZERO;
        for i in 0..half {
            let a0 = l_cur[2 * i];
            let a1 = l_cur[2 * i + 1];
            let b0 = r_cur[2 * i];
            let b1 = r_cur[2 * i + 1];
            q0 = q0.add(a0.mul(b0));
            q1 = q1.add(a1.mul(b1));
            q_inf = q_inf.add(a0.add(a1).mul(b0.add(b1)));
        }
        tr.absorb_bytes(b"t256_sc_q0", &q0.to_le_bytes());
        tr.absorb_bytes(b"t256_sc_q1", &q1.to_le_bytes());
        tr.absorb_bytes(b"t256_sc_qi", &q_inf.to_le_bytes());
        rounds.push(Tower256QuadRoundMsg { q0, q1, q_inf });

        let ch = squeeze_t256(tr, b"t256_sc_ch", true);
        chals.push(ch);
        l_cur = l_cur
            .chunks_exact(2)
            .map(|p| p[0].add(ch.mul(p[0].add(p[1]))))
            .collect();
        r_cur = r_cur
            .chunks_exact(2)
            .map(|p| p[0].add(ch.mul(p[0].add(p[1]))))
            .collect();
    }

    let (term_a, term_b) = (l_cur[0], r_cur[0]);
    tr.absorb_bytes(b"t256_sc_ta", &term_a.to_le_bytes());
    tr.absorb_bytes(b"t256_sc_tb", &term_b.to_le_bytes());

    (
        Tower256QuadSumcheckProof {
            claim,
            rounds,
            term_a,
            term_b,
        },
        chals,
    )
}

pub fn verify_t256_quad_sumcheck(
    expected_claim: Tower256,
    m: usize,
    proof: &Tower256QuadSumcheckProof,
    tr: &mut CShakeTranscript,
) -> Result<Vec<Tower256>, String> {
    if proof.claim != expected_claim || proof.rounds.len() != m {
        return Err("Tower256QuadSumcheck claim/round mismatch".to_string());
    }
    tr.absorb_bytes(b"t256_sc_claim", &proof.claim.to_le_bytes());
    let mut sigma = proof.claim;
    let mut chals = Vec::with_capacity(m);

    for (idx, msg) in proof.rounds.iter().enumerate() {
        if msg.q0.add(msg.q1) != sigma {
            return Err(format!("Tower256QuadSumcheck q0 + q1 != sigma at round {idx}"));
        }
        tr.absorb_bytes(b"t256_sc_q0", &msg.q0.to_le_bytes());
        tr.absorb_bytes(b"t256_sc_q1", &msg.q1.to_le_bytes());
        tr.absorb_bytes(b"t256_sc_qi", &msg.q_inf.to_le_bytes());
        let ch = squeeze_t256(tr, b"t256_sc_ch", true);
        chals.push(ch);
        let c1 = msg.q0.add(msg.q1).add(msg.q_inf);
        sigma = msg.q0.add(c1.mul(ch)).add(msg.q_inf.mul(ch.square()));
    }

    tr.absorb_bytes(b"t256_sc_ta", &proof.term_a.to_le_bytes());
    tr.absorb_bytes(b"t256_sc_tb", &proof.term_b.to_le_bytes());
    if sigma != proof.term_a.mul(proof.term_b) {
        return Err("Tower256QuadSumcheck terminal sigma != term_a * term_b".to_string());
    }
    Ok(chals)
}

// ===========================================================================
// §4. Subdomain-Lifted (`m_wit <= m_tab`) `124`-Bit `Ext4` `D1b` LogUp-GKR (`0` Witness Padding!)
// ===========================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct D1bExt4TableProof {
    pub m_wit: usize,
    pub m_tab: usize,
    pub root_q: Ext4,
    pub layers: Vec<D1bLayerProof>,
    pub wit_leaf_eval: Ext4,
    pub mult_leaf_eval: Ext4,
}

impl D1bExt4TableProof {
    pub fn write_to(&self, out: &mut Vec<u8>) {
        out.push(self.m_wit as u8);
        out.push(self.m_tab as u8);
        out.extend_from_slice(&self.root_q.to_bytes());
        out.extend_from_slice(&(self.layers.len() as u32).to_le_bytes());
        for lyr in &self.layers {
            out.extend_from_slice(&(lyr.rounds.len() as u32).to_le_bytes());
            for r in &lyr.rounds {
                r.write_to(out);
            }
            out.extend_from_slice(&lyr.p_lo.to_bytes());
            out.extend_from_slice(&lyr.p_hi.to_bytes());
            out.extend_from_slice(&lyr.q_lo.to_bytes());
            out.extend_from_slice(&lyr.q_hi.to_bytes());
        }
        out.extend_from_slice(&self.wit_leaf_eval.to_bytes());
        out.extend_from_slice(&self.mult_leaf_eval.to_bytes());
    }

    pub fn read_from(cur: &mut ByteCursor) -> Result<Self, String> {
        let m_wit = cur.read_u8()? as usize;
        let m_tab = cur.read_u8()? as usize;
        if m_wit == 0 || m_tab < m_wit || m_tab > 22 {
            return Err("invalid D1bExt4TableProof dimensions".to_string());
        }
        let root_q = cur.read_ext4()?;
        let num_layers = cur.read_u32()? as usize;
        if num_layers != m_tab + 1 {
            return Err("D1bExt4TableProof layer count mismatch".to_string());
        }
        let mut layers = Vec::with_capacity(num_layers);
        for _ in 0..num_layers {
            let n_rds = cur.read_u32()? as usize;
            if n_rds > m_tab {
                return Err("D1bExt4TableProof round count overflow".to_string());
            }
            let mut rounds = Vec::with_capacity(n_rds);
            for _ in 0..n_rds {
                rounds.push(CubicExt4RoundMsg::read_from(cur)?);
            }
            layers.push(D1bLayerProof {
                rounds,
                p_lo: cur.read_ext4()?,
                p_hi: cur.read_ext4()?,
                q_lo: cur.read_ext4()?,
                q_hi: cur.read_ext4()?,
            });
        }
        let wit_leaf_eval = cur.read_ext4()?;
        let mult_leaf_eval = cur.read_ext4()?;
        Ok(Self {
            m_wit,
            m_tab,
            root_q,
            layers,
            wit_leaf_eval,
            mult_leaf_eval,
        })
    }
}

pub fn mle_eval_ext4_table(tab: &[Ext4], pt: &[Ext4]) -> Ext4 {
    assert_eq!(tab.len(), 1usize << pt.len());
    let eq = build_eq_table_lsb_ext4(pt);
    eq.par_iter()
        .zip(tab.par_iter())
        .fold(
            || Ext4::ZERO,
            |acc, (&w, &v)| acc.add(w.mul(v)),
        )
        .reduce(|| Ext4::ZERO, |a, b| a.add(b))
}

/// Prove `forall i in 0..2^m_wit, wit_ext4[i] == rom_ext4[slot_i]` (`m_wit <= m_tab`) via `124`-bit `Ext4`
/// projective fraction-tree `D1b` LogUp-GKR (`0` witness padding, `0` prover inversions!).
/// Returns `(proof, z_tab)` where `z_wit = &z_tab[..m_wit]`.
pub fn prove_d1b_ext4_table(
    wit_ext4: &[Ext4],
    rom_ext4: &[Ext4],
    mult_table: &[u32],
    tr: &mut CShakeTranscript,
) -> (D1bExt4TableProof, Vec<Ext4>) {
    let n_wit = wit_ext4.len();
    let n_tab = rom_ext4.len();
    assert!(n_wit.is_power_of_two() && n_tab.is_power_of_two() && n_tab == mult_table.len());
    let m_wit = n_wit.trailing_zeros() as usize;
    let m_tab = n_tab.trailing_zeros() as usize;
    assert!(m_wit <= m_tab);

    let alpha = tr.squeeze_ext4(b"d1b_rom_alpha", true);
    let total_leaves = n_tab * 2;
    let mask_wit = n_wit - 1;

    let mut p0 = vec![Ext4::ZERO; total_leaves];
    let mut q0 = vec![Ext4::ZERO; total_leaves];
    p0[..n_tab]
        .par_iter_mut()
        .zip(q0[..n_tab].par_iter_mut())
        .enumerate()
        .for_each(|(x, (pd, qd))| {
            *pd = if x < n_wit { Ext4::ONE } else { Ext4::ZERO };
            *qd = alpha.sub(wit_ext4[x & mask_wit]);
        });
    p0[n_tab..]
        .par_iter_mut()
        .zip(q0[n_tab..].par_iter_mut())
        .enumerate()
        .for_each(|(x, (pd, qd))| {
            let m_bb = mult_table[x] % P_U32;
            *pd = Ext4::from_bb(if m_bb == 0 { 0 } else { P_U32 - m_bb });
            *qd = alpha.sub(rom_ext4[x]);
        });

    let mut p_layers = Vec::with_capacity(m_tab + 2);
    let mut q_layers = Vec::with_capacity(m_tab + 2);
    p_layers.push(p0);
    q_layers.push(q0);

    for _ in 0..=m_tab {
        let prev_p = p_layers.last().unwrap();
        let prev_q = q_layers.last().unwrap();
        let next_len = prev_p.len() / 2;
        let mut next_p = vec![Ext4::ZERO; next_len];
        let mut next_q = vec![Ext4::ZERO; next_len];
        next_p
            .par_iter_mut()
            .zip(next_q.par_iter_mut())
            .enumerate()
            .for_each(|(i, (np, nq))| {
                let (pl, pr) = (prev_p[2 * i], prev_p[2 * i + 1]);
                let (ql, qr) = (prev_q[2 * i], prev_q[2 * i + 1]);
                *np = pl.mul(qr).add(pr.mul(ql));
                *nq = ql.mul(qr);
            });
        p_layers.push(next_p);
        q_layers.push(next_q);
    }

    let root_p = p_layers.last().unwrap()[0];
    let root_q = q_layers.last().unwrap()[0];
    debug_assert!(root_p.is_zero() && !root_q.is_zero());
    tr.absorb_ext4(b"d1b_rom_root_q", root_q);

    let mut cur_pt: Vec<Ext4> = Vec::new();
    let mut cur_p_claim = Ext4::ZERO;
    let mut cur_q_claim = root_q;
    let mut layer_proofs = Vec::with_capacity(m_tab + 1);
    let two = Ext4::from_bb(2);

    for step in 0..=m_tab {
        let child_lvl = m_tab - step;
        let child_p = &p_layers[child_lvl];
        let child_q = &q_layers[child_lvl];
        let eta = tr.squeeze_ext4(b"d1b_rom_eta", true);
        let _ = (cur_p_claim, cur_q_claim);

        let half = 1usize << step;
        let mut pl_cur = Vec::with_capacity(half);
        let mut pr_cur = Vec::with_capacity(half);
        let mut ql_cur = Vec::with_capacity(half);
        let mut qr_cur = Vec::with_capacity(half);
        for i in 0..half {
            pl_cur.push(child_p[2 * i]);
            pr_cur.push(child_p[2 * i + 1]);
            ql_cur.push(child_q[2 * i]);
            qr_cur.push(child_q[2 * i + 1]);
        }
        let mut eq_cur = build_eq_table_lsb_ext4(&cur_pt);
        let mut rounds = Vec::with_capacity(step);
        let mut sum_chals = Vec::with_capacity(step);

        for _ in 0..step {
            let h2 = eq_cur.len() / 2;
            let (p0_acc, p1_acc, p2_acc, pinf_acc) = (0..h2)
                .into_par_iter()
                .fold(
                    || (Ext4::ZERO, Ext4::ZERO, Ext4::ZERO, Ext4::ZERO),
                    |(a0, a1, a2, ainf), idx| {
                        let (e0, e1) = (eq_cur[2 * idx], eq_cur[2 * idx + 1]);
                        let de = e1.sub(e0);
                        let e2 = e0.add(two.mul(de));
                        let (pl0, pl1) = (pl_cur[2 * idx], pl_cur[2 * idx + 1]);
                        let dpl = pl1.sub(pl0);
                        let pl2 = pl0.add(two.mul(dpl));
                        let (pr0, pr1) = (pr_cur[2 * idx], pr_cur[2 * idx + 1]);
                        let dpr = pr1.sub(pr0);
                        let pr2 = pr0.add(two.mul(dpr));
                        let (ql0, ql1) = (ql_cur[2 * idx], ql_cur[2 * idx + 1]);
                        let dql = ql1.sub(ql0);
                        let ql2 = ql0.add(two.mul(dql));
                        let (qr0, qr1) = (qr_cur[2 * idx], qr_cur[2 * idx + 1]);
                        let dqr = qr1.sub(qr0);
                        let qr2 = qr0.add(two.mul(dqr));

                        let v0 = e0.mul(pl0.mul(qr0).add(pr0.mul(ql0)).add(eta.mul(ql0.mul(qr0))));
                        let v1 = e1.mul(pl1.mul(qr1).add(pr1.mul(ql1)).add(eta.mul(ql1.mul(qr1))));
                        let v2 = e2.mul(pl2.mul(qr2).add(pr2.mul(ql2)).add(eta.mul(ql2.mul(qr2))));
                        let vi =
                            de.mul(dpl.mul(dqr).add(dpr.mul(dql)).add(eta.mul(dql.mul(dqr))));
                        (a0.add(v0), a1.add(v1), a2.add(v2), ainf.add(vi))
                    },
                )
                .reduce(
                    || (Ext4::ZERO, Ext4::ZERO, Ext4::ZERO, Ext4::ZERO),
                    |x, y| (x.0.add(y.0), x.1.add(y.1), x.2.add(y.2), x.3.add(y.3)),
                );

            let msg = CubicExt4RoundMsg {
                p0: p0_acc,
                p1: p1_acc,
                p2: p2_acc,
                p_inf: pinf_acc,
            };
            tr.absorb_ext4(b"d1b_rom_c0", msg.p0);
            tr.absorb_ext4(b"d1b_rom_c1", msg.p1);
            tr.absorb_ext4(b"d1b_rom_c2", msg.p2);
            tr.absorb_ext4(b"d1b_rom_ci", msg.p_inf);
            rounds.push(msg);

            let ch = tr.squeeze_ext4(b"d1b_rom_ch", true);
            sum_chals.push(ch);
            eq_cur = fold_ext4(&eq_cur, ch);
            pl_cur = fold_ext4(&pl_cur, ch);
            pr_cur = fold_ext4(&pr_cur, ch);
            ql_cur = fold_ext4(&ql_cur, ch);
            qr_cur = fold_ext4(&qr_cur, ch);
        }

        let (p_lo, p_hi, q_lo, q_hi) = (pl_cur[0], pr_cur[0], ql_cur[0], qr_cur[0]);
        tr.absorb_ext4(b"d1b_rom_plo", p_lo);
        tr.absorb_ext4(b"d1b_rom_phi", p_hi);
        tr.absorb_ext4(b"d1b_rom_qlo", q_lo);
        tr.absorb_ext4(b"d1b_rom_qhi", q_hi);
        let r_bit = tr.squeeze_ext4(b"d1b_rom_rbit", true);
        cur_p_claim = p_lo.add(r_bit.mul(p_hi.sub(p_lo)));
        cur_q_claim = q_lo.add(r_bit.mul(q_hi.sub(q_lo)));

        let mut next_pt = Vec::with_capacity(step + 1);
        next_pt.push(r_bit);
        next_pt.extend_from_slice(&sum_chals);
        cur_pt = next_pt;
        layer_proofs.push(D1bLayerProof {
            rounds,
            p_lo,
            p_hi,
            q_lo,
            q_hi,
        });
    }

    let z_tab = cur_pt[..m_tab].to_vec();
    let wit_leaf_eval = mle_eval_ext4_table(wit_ext4, &z_tab[..m_wit]);
    let mult_leaf_eval = mle_eval_bb_at_ext4(mult_table, &z_tab);
    tr.absorb_ext4(b"d1b_rom_wit_ev", wit_leaf_eval);
    tr.absorb_ext4(b"d1b_rom_mult_ev", mult_leaf_eval);

    (
        D1bExt4TableProof {
            m_wit,
            m_tab,
            root_q,
            layers: layer_proofs,
            wit_leaf_eval,
            mult_leaf_eval,
        },
        z_tab,
    )
}

pub fn verify_d1b_ext4_table(
    rom_ext4: &[Ext4],
    proof: &D1bExt4TableProof,
    tr: &mut CShakeTranscript,
) -> Result<Vec<Ext4>, String> {
    if !rom_ext4.len().is_power_of_two()
        || rom_ext4.len() != (1usize << proof.m_tab)
        || proof.m_wit > proof.m_tab
    {
        return Err("D1bExt4TableProof ROM dimension mismatch".to_string());
    }
    if proof.root_q.is_zero() || proof.layers.len() != proof.m_tab + 1 {
        return Err("D1bExt4TableProof root_q == 0 or layer count mismatch".to_string());
    }

    let alpha = tr.squeeze_ext4(b"d1b_rom_alpha", true);
    tr.absorb_ext4(b"d1b_rom_root_q", proof.root_q);

    let mut cur_pt: Vec<Ext4> = Vec::new();
    let mut cur_p_claim = Ext4::ZERO; // `root_P == 0` strictly enforced!
    let mut cur_q_claim = proof.root_q;

    for (step, lyr) in proof.layers.iter().enumerate() {
        if lyr.rounds.len() != step {
            return Err(format!("D1bExt4TableProof round count mismatch at step {step}"));
        }
        let eta = tr.squeeze_ext4(b"d1b_rom_eta", true);
        let mut sigma = cur_p_claim.add(eta.mul(cur_q_claim));
        let mut sum_chals = Vec::with_capacity(step);

        for (r_idx, msg) in lyr.rounds.iter().enumerate() {
            if msg.p0.add(msg.p1) != sigma {
                return Err(format!("D1bExt4TableProof cubic sumcheck failed at {step}:{r_idx}"));
            }
            tr.absorb_ext4(b"d1b_rom_c0", msg.p0);
            tr.absorb_ext4(b"d1b_rom_c1", msg.p1);
            tr.absorb_ext4(b"d1b_rom_c2", msg.p2);
            tr.absorb_ext4(b"d1b_rom_ci", msg.p_inf);
            let ch = tr.squeeze_ext4(b"d1b_rom_ch", true);
            sum_chals.push(ch);
            sigma = eval_cubic_zero_one_two_inf_ext4(msg.p0, msg.p1, msg.p2, msg.p_inf, ch);
        }

        tr.absorb_ext4(b"d1b_rom_plo", lyr.p_lo);
        tr.absorb_ext4(b"d1b_rom_phi", lyr.p_hi);
        tr.absorb_ext4(b"d1b_rom_qlo", lyr.q_lo);
        tr.absorb_ext4(b"d1b_rom_qhi", lyr.q_hi);

        let eq_ev = eq_mle_ext4(&cur_pt, &sum_chals);
        let num_val = lyr.p_lo.mul(lyr.q_hi).add(lyr.p_hi.mul(lyr.q_lo));
        let den_val = lyr.q_lo.mul(lyr.q_hi);
        if sigma != eq_ev.mul(num_val.add(eta.mul(den_val))) {
            return Err(format!("D1bExt4TableProof layer fold equation failed at step {step}"));
        }

        let r_bit = tr.squeeze_ext4(b"d1b_rom_rbit", true);
        cur_p_claim = lyr.p_lo.add(r_bit.mul(lyr.p_hi.sub(lyr.p_lo)));
        cur_q_claim = lyr.q_lo.add(r_bit.mul(lyr.q_hi.sub(lyr.q_lo)));

        let mut next_pt = Vec::with_capacity(step + 1);
        next_pt.push(r_bit);
        next_pt.extend_from_slice(&sum_chals);
        cur_pt = next_pt;
    }

    tr.absorb_ext4(b"d1b_rom_wit_ev", proof.wit_leaf_eval);
    tr.absorb_ext4(b"d1b_rom_mult_ev", proof.mult_leaf_eval);

    let z_tab = &cur_pt[..proof.m_tab];
    let z_side = cur_pt[proof.m_tab];

    let mut subdomain_wit_zero = Ext4::ONE;
    for &zb in &z_tab[proof.m_wit..] {
        subdomain_wit_zero = subdomain_wit_zero.mul(Ext4::ONE.sub(zb));
    }
    let p_wit = subdomain_wit_zero;
    let q_wit = alpha.sub(proof.wit_leaf_eval);

    let p_tab = proof.mult_leaf_eval.neg();
    let rom_ev = mle_eval_ext4_table(rom_ext4, z_tab);
    let q_tab = alpha.sub(rom_ev);

    let expected_p = eq_lin_ext4(z_side, Ext4::ZERO)
        .mul(p_wit)
        .add(eq_lin_ext4(z_side, Ext4::ONE).mul(p_tab));
    let expected_q = eq_lin_ext4(z_side, Ext4::ZERO)
        .mul(q_wit)
        .add(eq_lin_ext4(z_side, Ext4::ONE).mul(q_tab));

    if cur_p_claim != expected_p || cur_q_claim != expected_q {
        return Err("D1bExt4TableProof leaf witness/ROM equation mismatch".to_string());
    }
    Ok(z_tab.to_vec())
}

// ===========================================================================
// §5. Packed `Ext4`-Column PCS Helpers (`4` Base Limbs in `1` `SuccinctExt4Pcs` Tree!)
// ===========================================================================

/// Pack `col: &[Ext4]` (`len = 2^m`) into a `u32` table of length `4 * 2^m` (`idx = i + limb * 2^m`).
pub fn pack_ext4_col_to_bb(col: &[Ext4]) -> Vec<u32> {
    let n = col.len();
    let mut out = vec![0u32; 4 * n];
    for limb in 0..4 {
        for i in 0..n {
            out[limb * n + i] = col[i].0[limb];
        }
    }
    out
}

/// Returns `(z_b0, z_b1, inv_scale)` where `scale = (1 + X)(1 + X^2)` in `Ext4` so that
/// `scale * packed_mle([z_0..z_{m-1}, z_b0, z_b1]) == col_ext4_mle(z)` (`1` single PCS claim per `Ext4` point!).
fn ext4_limb_selector_consts() -> (Ext4, Ext4, Ext4) {
    let x = Ext4([0, 1, 0, 0]);
    let x2 = Ext4([0, 0, 1, 0]);
    let one_p_x = Ext4::ONE.add(x);
    let one_p_x2 = Ext4::ONE.add(x2);
    let zb0 = x.mul(one_p_x.inv().unwrap());
    let zb1 = x2.mul(one_p_x2.inv().unwrap());
    let scale = one_p_x.mul(one_p_x2);
    let inv_scale = scale.inv().unwrap();
    (zb0, zb1, inv_scale)
}

pub fn make_packed_ext4_pcs_claim(point_m: &[Ext4], ext4_val: Ext4) -> MleEvalClaim {
    let (zb0, zb1, inv_scale) = ext4_limb_selector_consts();
    let mut pt = Vec::with_capacity(point_m.len() + 2);
    pt.extend_from_slice(point_m);
    pt.push(zb0);
    pt.push(zb1);
    MleEvalClaim {
        point: pt,
        value: ext4_val.mul(inv_scale),
    }
}

// ===========================================================================
// §6. Real `248,320`-Vocab `Qwen` ByteLevel BPE Vocabulary & `cSHAKE256` Merkle ROM
// ===========================================================================

/// Inverse of HuggingFace / GPT-2 `bytes_to_unicode()` mapping `char -> u8` across all `256` raw bytes.
pub fn build_gpt2_unicode_to_byte_map() -> HashMap<char, u8> {
    let mut bs: Vec<u8> = Vec::with_capacity(256);
    bs.extend(b'!'..=b'~');
    bs.extend(0xA1u8..=0xACu8);
    bs.extend(0xAEu8..=0xFFu8);

    let mut cs: Vec<u32> = bs.iter().map(|&b| b as u32).collect();
    let mut n = 0u32;
    for b in 0u16..256u16 {
        let bu8 = b as u8;
        if !bs.contains(&bu8) {
            bs.push(bu8);
            cs.push(256 + n);
            n += 1;
        }
    }
    bs.into_iter()
        .zip(cs)
        .map(|(b, c)| (char::from_u32(c).expect("valid GPT-2 unicode scalar"), b))
        .collect()
}

pub fn build_gpt2_byte_to_unicode_map() -> [char; 256] {
    let u2b = build_gpt2_unicode_to_byte_map();
    let mut b2u = ['\0'; 256];
    for (ch, b) in u2b {
        b2u[b as usize] = ch;
    }
    b2u
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct QwenRomStaticEntry {
    pub tok_id: u32,
    pub is_defined: bool,
    pub is_pad_slot: bool,
    pub byte_len: u16,
    pub pow_rom_ext4: Ext4,
    pub val_rom_ext4: Ext4,
    pub pow_rom_t256: Tower256,
    pub val_rom_t256: Tower256,
}

impl QwenRomStaticEntry {
    pub fn leaf_hash(&self, raw_bytes: &[u8]) -> [u8; 32] {
        let bytes_digest = cshake256_32(b"QW35-BPE-RAW-BYTES-V1", raw_bytes);
        let mut buf = [0u8; 4 + 2 + 2 + 16 + 16 + 32 + 32 + 32];
        buf[0..4].copy_from_slice(&self.tok_id.to_le_bytes());
        buf[4] = u8::from(self.is_defined);
        buf[5] = u8::from(self.is_pad_slot);
        buf[6..8].copy_from_slice(&self.byte_len.to_le_bytes());
        buf[8..24].copy_from_slice(&self.pow_rom_ext4.to_bytes());
        buf[24..40].copy_from_slice(&self.val_rom_ext4.to_bytes());
        buf[40..72].copy_from_slice(&self.pow_rom_t256.to_le_bytes());
        buf[72..104].copy_from_slice(&self.val_rom_t256.to_le_bytes());
        buf[104..136].copy_from_slice(&bytes_digest);
        cshake256_32(ROM_LEAF_DOM, &buf)
    }
}

/// Real `248,320`-entry `Qwen` BPE ROM (`248,044` BPE + `22` added + `254` unallocated, padded to `262,144`).
pub struct QwenBpeRom {
    pub vocab_size: usize,
    pub defined_count: usize,
    pub bpe_vocab_count: usize,
    pub added_tokens_count: usize,
    pub max_token_byte_len: usize,
    pub rom_base_ext4: Ext4,
    pub rom_base_t256: Tower256,
    pub rom_merkle_root: [u8; 32],
    /// Flat contiguous byte storage for all `248,320` token IDs (`offsets.len() == 248,321`).
    pub byte_offsets: Vec<u32>,
    pub flat_bytes: Vec<u8>,
    pub is_defined: Vec<bool>,
    pub entries: Vec<QwenRomStaticEntry>,
    /// Exact reverse map `raw_bytes -> tok_id` for all `248,044` BPE tokens (for canonical & split BPE!).
    pub bytes_to_bpe_id: HashMap<Vec<u8>, u32>,
    /// BPE merge priority `(left_id, right_id) -> (rank, merged_id)` parsed from `model.merges`.
    pub merge_ranks: HashMap<(u32, u32), (u32, u32)>,
}

impl QwenBpeRom {
    pub fn load_default() -> Result<Self, String> {
        Self::load_from_path(Path::new(DEFAULT_QWEN35_TOKENIZER_PATH))
    }

    pub fn load_from_path(path: &Path) -> Result<Self, String> {
        let json_bytes =
            fs::read(path).map_err(|e| format!("failed reading {}: {e}", path.display()))?;
        let root: Value = serde_json::from_slice(&json_bytes)
            .map_err(|e| format!("failed parsing tokenizer.json: {e}"))?;

        let u2b = build_gpt2_unicode_to_byte_map();
        let vocab_obj = root
            .get("model")
            .and_then(|m| m.get("vocab"))
            .and_then(|v| v.as_object())
            .ok_or_else(|| "missing model.vocab object in tokenizer.json".to_string())?;

        let mut token_bytes: Vec<Option<Vec<u8>>> = vec![None; QWEN_VOCAB_SIZE];
        let mut bytes_to_bpe_id: HashMap<Vec<u8>, u32> = HashMap::with_capacity(vocab_obj.len());

        for (tok_str, id_val) in vocab_obj {
            let tid = id_val
                .as_u64()
                .ok_or_else(|| format!("non-integer token id for {tok_str:?}"))? as usize;
            if tid >= QWEN_VOCAB_SIZE {
                return Err(format!("token id {tid} >= {QWEN_VOCAB_SIZE}"));
            }
            let mut raw = Vec::with_capacity(tok_str.len());
            for ch in tok_str.chars() {
                let b = u2b.get(&ch).ok_or_else(|| {
                    format!("unmapped ByteLevel unicode char U+{:04X} in token {tid}", ch as u32)
                })?;
                raw.push(*b);
            }
            bytes_to_bpe_id.entry(raw.clone()).or_insert(tid as u32);
            token_bytes[tid] = Some(raw);
        }
        let bpe_vocab_count = vocab_obj.len();

        let mut added_tokens_count = 0usize;
        if let Some(added_arr) = root.get("added_tokens").and_then(|a| a.as_array()) {
            for item in added_arr {
                let tid = item
                    .get("id")
                    .and_then(|v| v.as_u64())
                    .ok_or_else(|| "added_token missing id".to_string())? as usize;
                let content = item
                    .get("content")
                    .and_then(|v| v.as_str())
                    .ok_or_else(|| "added_token missing content".to_string())?;
                if tid < QWEN_VOCAB_SIZE {
                    token_bytes[tid] = Some(content.as_bytes().to_vec());
                    added_tokens_count += 1;
                }
            }
        }

        // Parse BPE `merges` (supports both `["a b", ...]` and `[["a", "b"], ...]` HF formats!)
        let mut merge_ranks: HashMap<(u32, u32), (u32, u32)> = HashMap::new();
        if let Some(merges_arr) = root
            .get("model")
            .and_then(|m| m.get("merges"))
            .and_then(|m| m.as_array())
        {
            let decode_piece = |s: &str| -> Option<Vec<u8>> {
                let mut out = Vec::with_capacity(s.len());
                for ch in s.chars() {
                    out.push(*u2b.get(&ch)?);
                }
                Some(out)
            };
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
                if let Some((ls, rs)) = pair_opt {
                    if let (Some(lb), Some(rb)) = (decode_piece(ls), decode_piece(rs)) {
                        if let (Some(&lid), Some(&rid)) =
                            (bytes_to_bpe_id.get(&lb), bytes_to_bpe_id.get(&rb))
                        {
                            let mut merged = lb;
                            merged.extend_from_slice(&rb);
                            if let Some(&mid) = bytes_to_bpe_id.get(&merged) {
                                merge_ranks.insert((lid, rid), (rank as u32, mid));
                            }
                        }
                    }
                }
            }
        }

        let mut byte_offsets = Vec::with_capacity(QWEN_VOCAB_SIZE + 1);
        let mut flat_bytes = Vec::with_capacity(bpe_vocab_count * 7);
        let mut is_defined = Vec::with_capacity(QWEN_VOCAB_SIZE);
        let mut defined_count = 0usize;
        let mut max_token_byte_len = 0usize;

        for slot in &token_bytes {
            byte_offsets.push(flat_bytes.len() as u32);
            match slot {
                Some(bs) => {
                    is_defined.push(true);
                    defined_count += 1;
                    max_token_byte_len = max_token_byte_len.max(bs.len());
                    flat_bytes.extend_from_slice(bs);
                }
                None => {
                    is_defined.push(false);
                }
            }
        }
        byte_offsets.push(flat_bytes.len() as u32);

        // Derive nothing-up-my-sleeve static ROM bases `(rom_base_ext4, rom_base_t256)` from catalog digest
        let mut cat_tr = CShakeTranscript::new(b"QW35-BPE-ROM-BASE-DERIVE-V1");
        cat_tr.absorb_u32(b"vocab_size", QWEN_VOCAB_SIZE as u32);
        cat_tr.absorb_u32(b"defined_count", defined_count as u32);
        cat_tr.absorb_bytes(
            b"flat_bytes_digest",
            &cshake256_32(b"QW35-BPE-FLAT-BYTES-V1", &flat_bytes),
        );
        let rom_base_ext4 = cat_tr.squeeze_ext4(b"rom_base_ext4", true);
        let rom_base_t256 = squeeze_t256(&mut cat_tr, b"rom_base_t256", true);

        // Precompute powers `0..=max_token_byte_len`
        let mut pows_ext4 = Vec::with_capacity(max_token_byte_len + 1);
        let mut pows_t256 = Vec::with_capacity(max_token_byte_len + 1);
        let mut cur_e = Ext4::ONE;
        let mut cur_t = Tower256::ONE;
        for _ in 0..=max_token_byte_len {
            pows_ext4.push(cur_e);
            pows_t256.push(cur_t);
            cur_e = cur_e.mul(rom_base_ext4);
            cur_t = cur_t.mul(rom_base_t256);
        }

        let entries: Vec<QwenRomStaticEntry> = (0..ROM_PADDED_SIZE)
            .into_par_iter()
            .map(|slot| {
                if slot < QWEN_VOCAB_SIZE && is_defined[slot] {
                    let st = byte_offsets[slot] as usize;
                    let en = byte_offsets[slot + 1] as usize;
                    let bs = &flat_bytes[st..en];
                    QwenRomStaticEntry {
                        tok_id: slot as u32,
                        is_defined: true,
                        is_pad_slot: false,
                        byte_len: bs.len() as u16,
                        pow_rom_ext4: pows_ext4[bs.len()],
                        val_rom_ext4: eval_bytes_ext4(rom_base_ext4, bs),
                        pow_rom_t256: pows_t256[bs.len()],
                        val_rom_t256: eval_bytes_t256(rom_base_t256, bs),
                    }
                } else {
                    QwenRomStaticEntry {
                        tok_id: PAD_TOK_ID,
                        is_defined: false,
                        is_pad_slot: true,
                        byte_len: 0,
                        pow_rom_ext4: Ext4::ONE,
                        val_rom_ext4: Ext4::ZERO,
                        pow_rom_t256: Tower256::ONE,
                        val_rom_t256: Tower256::ZERO,
                    }
                }
            })
            .collect();

        let leaves: Vec<[u8; 32]> = entries
            .par_iter()
            .enumerate()
            .map(|(slot, entry)| {
                let bs: &[u8] = if slot < QWEN_VOCAB_SIZE && is_defined[slot] {
                    &flat_bytes[byte_offsets[slot] as usize..byte_offsets[slot + 1] as usize]
                } else {
                    &[]
                };
                entry.leaf_hash(bs)
            })
            .collect();
        let tree_levels = build_merkle_tree_levels(ROM_NODE_DOM, &leaves);
        let rom_merkle_root = tree_levels.last().unwrap()[0];

        Ok(Self {
            vocab_size: QWEN_VOCAB_SIZE,
            defined_count,
            bpe_vocab_count,
            added_tokens_count,
            max_token_byte_len,
            rom_base_ext4,
            rom_base_t256,
            rom_merkle_root,
            byte_offsets,
            flat_bytes,
            is_defined,
            entries,
            bytes_to_bpe_id,
            merge_ranks,
        })
    }

    #[inline]
    pub fn token_bytes(&self, tok_id: u32) -> Result<&[u8], String> {
        let idx = tok_id as usize;
        if idx >= QWEN_VOCAB_SIZE || !self.is_defined[idx] {
            return Err(format!("undefined Qwen token id {tok_id}"));
        }
        let st = self.byte_offsets[idx] as usize;
        let en = self.byte_offsets[idx + 1] as usize;
        Ok(&self.flat_bytes[st..en])
    }

    #[inline]
    pub fn lookup_bpe_id(&self, raw: &[u8]) -> Option<u32> {
        self.bytes_to_bpe_id.get(raw).copied()
    }

    /// Exact free-monoid `detok` (`ts.flatMap V`) over real Qwen token IDs.
    pub fn detokenize(&self, tokens: &[u32]) -> Result<Vec<u8>, String> {
        let mut out = Vec::with_capacity(tokens.len() * 5);
        for &t in tokens {
            out.extend_from_slice(self.token_bytes(t)?);
        }
        Ok(out)
    }

    /// Apply real Qwen BPE merges to a pre-tokenized chunk `chunk_bytes` (starting from 1-byte BPE tokens).
    pub fn bpe_encode_chunk(&self, chunk_bytes: &[u8]) -> Vec<u32> {
        if chunk_bytes.is_empty() {
            return Vec::new();
        }
        let mut word: Vec<u32> = chunk_bytes
            .iter()
            .map(|&b| *self.bytes_to_bpe_id.get(&[b][..]).expect("all 256 byte tokens exist"))
            .collect();
        while word.len() >= 2 {
            let mut best: Option<(u32, usize, u32)> = None;
            for i in 0..(word.len() - 1) {
                if let Some(&(rank, mid)) = self.merge_ranks.get(&(word[i], word[i + 1])) {
                    if best.map_or(true, |b| rank < b.0) {
                        best = Some((rank, i, mid));
                    }
                }
            }
            let Some((_, best_idx, merged_id)) = best else {
                break;
            };
            word[best_idx] = merged_id;
            word.remove(best_idx + 1);
        }
        word
    }

    /// Pre-tokenize ASCII/UTF-8 text along Qwen-style letter / digit / punctuation / space boundaries and run BPE.
    pub fn encode_qwen_bpe(&self, raw: &[u8]) -> Vec<u32> {
        #[derive(Clone, Copy, PartialEq, Eq)]
        enum Cls {
            Alpha,
            Digit,
            Punct,
            Ws,
        }
        fn classify(b: u8) -> Cls {
            if b.is_ascii_alphabetic() || b >= 0x80 {
                Cls::Alpha
            } else if b.is_ascii_digit() {
                Cls::Digit
            } else if b == b' ' || b == b'\t' || b == b'\n' || b == b'\r' {
                Cls::Ws
            } else {
                Cls::Punct
            }
        }
        let mut out = Vec::new();
        let mut i = 0;
        while i < raw.len() {
            // Digits are isolated in Qwen's `\\p{N}` rule!
            if raw[i].is_ascii_digit() {
                out.extend(self.bpe_encode_chunk(&raw[i..i + 1]));
                i += 1;
                continue;
            }
            // Optional leading space/punct attached to alpha run (`[^\\r\\n\\p{L}\\p{N}]?[\\p{L}]+`)
            if (raw[i] == b' ' || classify(raw[i]) == Cls::Punct)
                && i + 1 < raw.len()
                && classify(raw[i + 1]) == Cls::Alpha
            {
                let start = i;
                i += 2;
                while i < raw.len() && classify(raw[i]) == Cls::Alpha {
                    i += 1;
                }
                out.extend(self.bpe_encode_chunk(&raw[start..i]));
                continue;
            }
            let c0 = classify(raw[i]);
            let start = i;
            i += 1;
            while i < raw.len() && classify(raw[i]) == c0 {
                i += 1;
            }
            out.extend(self.bpe_encode_chunk(&raw[start..i]));
        }
        out
    }

    /// Enumerate up to `limit` distinct valid Qwen BPE token sequences whose `detok` equals `target_bytes`!
    pub fn enumerate_valid_splits(&self, target_bytes: &[u8], limit: usize) -> Vec<Vec<u32>> {
        let mut results = Vec::new();
        let mut cur = Vec::new();
        fn dfs(
            rom: &QwenBpeRom,
            target: &[u8],
            pos: usize,
            cur: &mut Vec<u32>,
            results: &mut Vec<Vec<u32>>,
            limit: usize,
        ) {
            if results.len() >= limit {
                return;
            }
            if pos == target.len() {
                results.push(cur.clone());
                return;
            }
            let max_end = target.len().min(pos + rom.max_token_byte_len);
            for end in (pos + 1..=max_end).rev() {
                if let Some(tid) = rom.lookup_bpe_id(&target[pos..end]) {
                    cur.push(tid);
                    dfs(rom, target, end, cur, results, limit);
                    cur.pop();
                    if results.len() >= limit {
                        return;
                    }
                }
            }
        }
        dfs(self, target_bytes, 0, &mut cur, &mut results, limit);
        results
    }

    /// Evaluate packed `262,144`-slot `Ext4` ROM table at post-commitment Fiat–Shamir base `beta_ext4`
    /// and tuple-packing challenges `gammas = [g1, g2, g3, g4]`:
    /// `T_rom[slot] = tok_id + g1 * is_pad + g2 * byte_len + g3 * beta_ext4^{byte_len} + g4 * eval_bytes_ext4(beta_ext4, V(slot))`.
    pub fn build_packed_rom_table_ext4(&self, beta_ext4: Ext4, gammas: [Ext4; 4]) -> Vec<Ext4> {
        let mut pows = Vec::with_capacity(self.max_token_byte_len + 1);
        let mut cur = Ext4::ONE;
        for _ in 0..=self.max_token_byte_len {
            pows.push(cur);
            cur = cur.mul(beta_ext4);
        }
        let pad_tuple = Ext4::from_bb(PAD_TOK_ID)
            .add(gammas[0]) // `is_pad == 1`
            .add(gammas[2]); // `len == 0 => pow == 1, val == 0`

        (0..ROM_PADDED_SIZE)
            .into_par_iter()
            .map(|slot| {
                if slot < QWEN_DEFINED_TOKENS && self.is_defined[slot] {
                    let st = self.byte_offsets[slot] as usize;
                    let en = self.byte_offsets[slot + 1] as usize;
                    let bs = &self.flat_bytes[st..en];
                    let len = bs.len();
                    let val = eval_bytes_ext4(beta_ext4, bs);
                    Ext4::from_bb(slot as u32)
                        .add(gammas[1].scale_bb(len as u32))
                        .add(gammas[2].mul(pows[len]))
                        .add(gammas[3].mul(val))
                } else {
                    pad_tuple
                }
            })
            .collect()
    }
}

// ===========================================================================
// §7. Salted `Tower256` Byte Merkle Commitment & Shift Kernel Helpers
// ===========================================================================

pub fn pack_salted_byte_t256(b: u8, salt: &[u8; 31]) -> Tower256 {
    let mut raw = [0u8; 32];
    raw[0] = b;
    raw[1..32].copy_from_slice(salt);
    Tower256::from_le_bytes(&raw)
}

pub fn commit_salted_bytes_t256(
    bytes: &[u8],
    pad_len: usize,
    salts: &[[u8; 31]],
) -> ([u8; 32], Vec<Vec<[u8; 32]>>) {
    assert!(pad_len.is_power_of_two() && bytes.len() <= pad_len && salts.len() == pad_len);
    let leaves: Vec<[u8; 32]> = (0..pad_len)
        .into_par_iter()
        .map(|j| {
            let (is_eof, b) = if j < bytes.len() {
                (0u8, bytes[j])
            } else {
                (1u8, 0u8)
            };
            let packed = pack_salted_byte_t256(b, &salts[j]);
            let mut buf = [0u8; 5 + 32];
            buf[0..4].copy_from_slice(&(j as u32).to_le_bytes());
            buf[4] = is_eof;
            buf[5..37].copy_from_slice(&packed.to_le_bytes());
            cshake256_32(T256_SALTED_LEAF_DOM, &buf)
        })
        .collect();
    let levels = build_merkle_tree_levels(T256_SALTED_NODE_DOM, &leaves);
    let root = levels.last().unwrap()[0];
    (root, levels)
}

fn eval_shift_kernel_ext4(z: &[Ext4], u_pt: &[Ext4]) -> Ext4 {
    let eq_z = build_eq_table_lsb_ext4(z);
    let eq_u = build_eq_table_lsb_ext4(u_pt);
    let mut acc = Ext4::ZERO;
    for t in 0..(eq_z.len() - 1) {
        acc = acc.add(eq_z[t].mul(eq_u[t + 1]));
    }
    acc
}

fn eval_shift_kernel_t256(z: &[Tower256], u_pt: &[Tower256]) -> Tower256 {
    let eq_z = build_eq_table_lsb_t256(z);
    let eq_u = build_eq_table_lsb_t256(u_pt);
    let mut acc = Tower256::ZERO;
    for t in 0..(eq_z.len() - 1) {
        acc = acc.add(eq_z[t].mul(eq_u[t + 1]));
    }
    acc
}

fn eval_tail_indicator_ext4(active_len: usize, pad_len: usize, pt: &[Ext4]) -> Ext4 {
    let eq = build_eq_table_lsb_ext4(pt);
    let mut acc = Ext4::ZERO;
    for i in active_len..pad_len {
        acc = acc.add(eq[i]);
    }
    acc
}

// ===========================================================================
// §8. Dual-Characteristic Token-to-Byte Bridge Statement, Proof, Prover, & Verifier
// ===========================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DualCharBridgeStatement {
    pub rom_merkle_root: [u8; 32],
    pub num_tokens: usize,
    pub byte_len: usize,
    pub tok_pad_len: usize,
    pub byte_pad_len: usize,
    /// `BabyBear` ZK PCS root of `[t_0, ..., t_{K-1}, PAD...]` (`Tensor World` witness).
    pub tok_pcs_root: [u8; 32],
    /// `BabyBear` ZK PCS root of `[b_0, ..., b_{L-1}, 256...]` (directly compatible with `u1_audit` `P6` `content_root`!).
    pub bytes_bb_pcs_root: [u8; 32],
    /// `P6` `cSHAKE256(byte_len || bytes_bb_pcs_root)` content root for direct `PaddedAbsenceZkReceipt` composition.
    pub content_root_bb: [u8; 32],
    /// `Tower256` `cSHAKE256` salted byte Merkle root (`Policy World` `saltedContentCommit`).
    pub tower256_salted_root: [u8; 32],
    /// `Tower256` ZK Coset-RS Matrix MLE PCS root of `GF(2^8)`-embedded bytes.
    pub tower256_bytes_pcs_root: [u8; 32],
}

impl DualCharBridgeStatement {
    pub fn write_to(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.rom_merkle_root);
        for v in [
            self.num_tokens,
            self.byte_len,
            self.tok_pad_len,
            self.byte_pad_len,
        ] {
            out.extend_from_slice(&(v as u32).to_le_bytes());
        }
        for r in [
            &self.tok_pcs_root,
            &self.bytes_bb_pcs_root,
            &self.content_root_bb,
            &self.tower256_salted_root,
            &self.tower256_bytes_pcs_root,
        ] {
            out.extend_from_slice(r);
        }
    }

    pub fn read_from(cur: &mut ByteCursor) -> Result<Self, String> {
        Ok(Self {
            rom_merkle_root: cur.read_arr32()?,
            num_tokens: cur.read_u32()? as usize,
            byte_len: cur.read_u32()? as usize,
            tok_pad_len: cur.read_u32()? as usize,
            byte_pad_len: cur.read_u32()? as usize,
            tok_pcs_root: cur.read_arr32()?,
            bytes_bb_pcs_root: cur.read_arr32()?,
            content_root_bb: cur.read_arr32()?,
            tower256_salted_root: cur.read_arr32()?,
            tower256_bytes_pcs_root: cur.read_arr32()?,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DualCharBridgeProof {
    pub stmt: DualCharBridgeStatement,
    // Auxiliary Phase-1 & Phase-3 PCS roots
    pub len_pcs_root: [u8; 32],
    pub cum_len_pcs_root: [u8; 32],
    pub cum_len_next_pcs_root: [u8; 32],
    pub mult_byte_range_pcs_root: [u8; 32],
    pub pow_ext4_pcs_root: [u8; 32],
    pub val_ext4_pcs_root: [u8; 32],
    pub acc_ext4_pcs_root: [u8; 32],
    pub acc_next_ext4_pcs_root: [u8; 32],
    pub mult_rom_pcs_root: [u8; 32],
    pub t256_h_pcs_root: [u8; 32],
    pub t256_h_next_pcs_root: [u8; 32],

    // Cross-characteristic rolled digests (at post-commitment Fiat–Shamir bases + `p61` primes)
    pub final_acc_ext4: Ext4,
    pub final_acc_t256: Tower256,
    pub fp_p61_0: (u64, u64),
    pub fp_p61_1: (u64, u64),

    // 1. `BabyBear Ext4` `D1b` `262,144`-vocab Qwen ROM lookup proof + leaf openings
    pub rom_d1b_proof: D1bExt4TableProof,
    pub tok_at_rom_leaf: Ext4,
    pub len_at_rom_leaf: Ext4,
    pub pow_at_rom_leaf: Ext4,
    pub val_at_rom_leaf: Ext4,

    // 2. `BabyBear Ext4` degree-2 rolling accumulator AIR (`acc_next - val == acc * pow`) + shift sumchecks
    pub acc_next_at_zroll: Ext4,
    pub val_at_zroll: Ext4,
    pub cum_len_at_zroll: Ext4,
    pub len_at_zroll: Ext4,
    pub cum_len_next_at_zroll: Ext4,
    pub roll_prod_gruen_proof: GruenMode2Ext4Proof,
    pub acc_next_at_zsh: Ext4,
    pub acc_shift_gruen_proof: GruenMode2Ext4Proof,
    pub cum_len_next_at_zsh: Ext4,
    pub cum_len_shift_gruen_proof: GruenMode2Ext4Proof,

    // 3. `BabyBear Ext4` byte range `[0, 512)`, tail EOF `== 256`, & `\beta_{ext4}` Horner inner-product sumcheck
    pub byte_range_d1b_proof: D1bRangeExt4Proof,
    pub byte_horner_gruen_proof: GruenMode2Ext4Proof,
    pub byte_eof_tail_gruen_proof: GruenMode2Ext4Proof,

    // 4. `Tower256` (`GF(2^256)`) Frobenius `GF(2^8)` subfield check + degree-2 Horner trace & shift sumchecks
    pub t256_b_at_zfrob: Tower256,
    pub t256_b_at_zfrob_inv256: Tower256,
    pub t256_h_next_at_zstep: Tower256,
    pub t256_b_at_zstep: Tower256,
    pub t256_step_quad_proof: Tower256QuadSumcheckProof,
    pub t256_h_next_at_zsh: Tower256,
    pub t256_shift_quad_proof: Tower256QuadSumcheckProof,
    pub t256_direct_ip_quad_proof: Tower256QuadSumcheckProof,
    pub t256_tail_zero_quad_proof: Tower256QuadSumcheckProof,

    // 5. Succinct ZK PCS opening proofs (`BabyBear Ext4` + `Tower256`)
    pub tok_pcs_proof: PcsOpeningProof,
    pub len_pcs_proof: PcsOpeningProof,
    pub cum_len_pcs_proof: PcsOpeningProof,
    pub cum_len_next_pcs_proof: PcsOpeningProof,
    pub bytes_bb_pcs_proof: PcsOpeningProof,
    pub mult_byte_range_pcs_proof: PcsOpeningProof,
    pub pow_ext4_pcs_proof: PcsOpeningProof,
    pub val_ext4_pcs_proof: PcsOpeningProof,
    pub acc_ext4_pcs_proof: PcsOpeningProof,
    pub acc_next_ext4_pcs_proof: PcsOpeningProof,
    pub mult_rom_pcs_proof: PcsOpeningProof,
    pub t256_bytes_pcs_proof: Tower256PcsProof,
    pub t256_h_pcs_proof: Tower256PcsProof,
    pub t256_h_next_pcs_proof: Tower256PcsProof,
}

impl DualCharBridgeProof {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(256 * 1024);
        out.extend_from_slice(BRIDGE_MAGIC);
        self.stmt.write_to(&mut out);
        for r in [
            &self.len_pcs_root,
            &self.cum_len_pcs_root,
            &self.cum_len_next_pcs_root,
            &self.mult_byte_range_pcs_root,
            &self.pow_ext4_pcs_root,
            &self.val_ext4_pcs_root,
            &self.acc_ext4_pcs_root,
            &self.acc_next_ext4_pcs_root,
            &self.mult_rom_pcs_root,
            &self.t256_h_pcs_root,
            &self.t256_h_next_pcs_root,
        ] {
            out.extend_from_slice(r);
        }
        out.extend_from_slice(&self.final_acc_ext4.to_bytes());
        out.extend_from_slice(&self.final_acc_t256.to_le_bytes());
        for (p, v) in [self.fp_p61_0, self.fp_p61_1] {
            out.extend_from_slice(&p.to_le_bytes());
            out.extend_from_slice(&v.to_le_bytes());
        }
        self.rom_d1b_proof.write_to(&mut out);
        for e in [
            self.tok_at_rom_leaf,
            self.len_at_rom_leaf,
            self.pow_at_rom_leaf,
            self.val_at_rom_leaf,
            self.acc_next_at_zroll,
            self.val_at_zroll,
            self.cum_len_at_zroll,
            self.len_at_zroll,
            self.cum_len_next_at_zroll,
            self.acc_next_at_zsh,
            self.cum_len_next_at_zsh,
        ] {
            out.extend_from_slice(&e.to_bytes());
        }
        self.roll_prod_gruen_proof.write_to(&mut out);
        self.acc_shift_gruen_proof.write_to(&mut out);
        self.cum_len_shift_gruen_proof.write_to(&mut out);
        self.byte_range_d1b_proof.write_to(&mut out);
        self.byte_horner_gruen_proof.write_to(&mut out);
        self.byte_eof_tail_gruen_proof.write_to(&mut out);

        for t in [
            self.t256_b_at_zfrob,
            self.t256_b_at_zfrob_inv256,
            self.t256_h_next_at_zstep,
            self.t256_b_at_zstep,
            self.t256_h_next_at_zsh,
        ] {
            out.extend_from_slice(&t.to_le_bytes());
        }
        self.t256_step_quad_proof.write_to(&mut out);
        self.t256_shift_quad_proof.write_to(&mut out);
        self.t256_direct_ip_quad_proof.write_to(&mut out);
        self.t256_tail_zero_quad_proof.write_to(&mut out);

        for pf in [
            &self.tok_pcs_proof,
            &self.len_pcs_proof,
            &self.cum_len_pcs_proof,
            &self.cum_len_next_pcs_proof,
            &self.bytes_bb_pcs_proof,
            &self.mult_byte_range_pcs_proof,
            &self.pow_ext4_pcs_proof,
            &self.val_ext4_pcs_proof,
            &self.acc_ext4_pcs_proof,
            &self.acc_next_ext4_pcs_proof,
            &self.mult_rom_pcs_proof,
        ] {
            pf.write_to(&mut out);
        }
        self.t256_bytes_pcs_proof.write_to(&mut out);
        self.t256_h_pcs_proof.write_to(&mut out);
        self.t256_h_next_pcs_proof.write_to(&mut out);
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        let mut cur = ByteCursor::new(bytes);
        let magic = cur.read_exact(8)?;
        if magic != BRIDGE_MAGIC {
            return Err("invalid DualCharBridgeProof magic".to_string());
        }
        let stmt = DualCharBridgeStatement::read_from(&mut cur)?;
        let len_pcs_root = cur.read_arr32()?;
        let cum_len_pcs_root = cur.read_arr32()?;
        let cum_len_next_pcs_root = cur.read_arr32()?;
        let mult_byte_range_pcs_root = cur.read_arr32()?;
        let pow_ext4_pcs_root = cur.read_arr32()?;
        let val_ext4_pcs_root = cur.read_arr32()?;
        let acc_ext4_pcs_root = cur.read_arr32()?;
        let acc_next_ext4_pcs_root = cur.read_arr32()?;
        let mult_rom_pcs_root = cur.read_arr32()?;
        let t256_h_pcs_root = cur.read_arr32()?;
        let t256_h_next_pcs_root = cur.read_arr32()?;

        let final_acc_ext4 = cur.read_ext4()?;
        let final_acc_t256 = Tower256::from_le_bytes(&cur.read_arr32()?);
        let read_u64 = |c: &mut ByteCursor| -> Result<u64, String> {
            Ok(u64::from_le_bytes(c.read_exact(8)?.try_into().unwrap()))
        };
        let fp_p61_0 = (read_u64(&mut cur)?, read_u64(&mut cur)?);
        let fp_p61_1 = (read_u64(&mut cur)?, read_u64(&mut cur)?);

        let rom_d1b_proof = D1bExt4TableProof::read_from(&mut cur)?;
        let tok_at_rom_leaf = cur.read_ext4()?;
        let len_at_rom_leaf = cur.read_ext4()?;
        let pow_at_rom_leaf = cur.read_ext4()?;
        let val_at_rom_leaf = cur.read_ext4()?;
        let acc_next_at_zroll = cur.read_ext4()?;
        let val_at_zroll = cur.read_ext4()?;
        let cum_len_at_zroll = cur.read_ext4()?;
        let len_at_zroll = cur.read_ext4()?;
        let cum_len_next_at_zroll = cur.read_ext4()?;
        let acc_next_at_zsh = cur.read_ext4()?;
        let cum_len_next_at_zsh = cur.read_ext4()?;

        let roll_prod_gruen_proof = GruenMode2Ext4Proof::read_from(&mut cur)?;
        let acc_shift_gruen_proof = GruenMode2Ext4Proof::read_from(&mut cur)?;
        let cum_len_shift_gruen_proof = GruenMode2Ext4Proof::read_from(&mut cur)?;
        let byte_range_d1b_proof = D1bRangeExt4Proof::read_from(&mut cur)?;
        let byte_horner_gruen_proof = GruenMode2Ext4Proof::read_from(&mut cur)?;
        let byte_eof_tail_gruen_proof = GruenMode2Ext4Proof::read_from(&mut cur)?;

        let t256_b_at_zfrob = Tower256::from_le_bytes(&cur.read_arr32()?);
        let t256_b_at_zfrob_inv256 = Tower256::from_le_bytes(&cur.read_arr32()?);
        let t256_h_next_at_zstep = Tower256::from_le_bytes(&cur.read_arr32()?);
        let t256_b_at_zstep = Tower256::from_le_bytes(&cur.read_arr32()?);
        let t256_h_next_at_zsh = Tower256::from_le_bytes(&cur.read_arr32()?);

        let t256_step_quad_proof = Tower256QuadSumcheckProof::read_from(&mut cur)?;
        let t256_shift_quad_proof = Tower256QuadSumcheckProof::read_from(&mut cur)?;
        let t256_direct_ip_quad_proof = Tower256QuadSumcheckProof::read_from(&mut cur)?;
        let t256_tail_zero_quad_proof = Tower256QuadSumcheckProof::read_from(&mut cur)?;

        let tok_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        let len_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        let cum_len_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        let cum_len_next_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        let bytes_bb_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        let mult_byte_range_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        let pow_ext4_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        let val_ext4_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        let acc_ext4_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        let acc_next_ext4_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        let mult_rom_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        let t256_bytes_pcs_proof = Tower256PcsProof::read_from(&mut cur)?;
        let t256_h_pcs_proof = Tower256PcsProof::read_from(&mut cur)?;
        let t256_h_next_pcs_proof = Tower256PcsProof::read_from(&mut cur)?;

        if cur.remaining() != 0 {
            return Err(format!("trailing {} bytes in DualCharBridgeProof", cur.remaining()));
        }
        Ok(Self {
            stmt,
            len_pcs_root,
            cum_len_pcs_root,
            cum_len_next_pcs_root,
            mult_byte_range_pcs_root,
            pow_ext4_pcs_root,
            val_ext4_pcs_root,
            acc_ext4_pcs_root,
            acc_next_ext4_pcs_root,
            mult_rom_pcs_root,
            t256_h_pcs_root,
            t256_h_next_pcs_root,
            final_acc_ext4,
            final_acc_t256,
            fp_p61_0,
            fp_p61_1,
            rom_d1b_proof,
            tok_at_rom_leaf,
            len_at_rom_leaf,
            pow_at_rom_leaf,
            val_at_rom_leaf,
            acc_next_at_zroll,
            val_at_zroll,
            cum_len_at_zroll,
            len_at_zroll,
            cum_len_next_at_zroll,
            roll_prod_gruen_proof,
            acc_next_at_zsh,
            acc_shift_gruen_proof,
            cum_len_next_at_zsh,
            cum_len_shift_gruen_proof,
            byte_range_d1b_proof,
            byte_horner_gruen_proof,
            byte_eof_tail_gruen_proof,
            t256_b_at_zfrob,
            t256_b_at_zfrob_inv256,
            t256_h_next_at_zstep,
            t256_b_at_zstep,
            t256_step_quad_proof,
            t256_h_next_at_zsh,
            t256_shift_quad_proof,
            t256_direct_ip_quad_proof,
            t256_tail_zero_quad_proof,
            tok_pcs_proof,
            len_pcs_proof,
            cum_len_pcs_proof,
            cum_len_next_pcs_proof,
            bytes_bb_pcs_proof,
            mult_byte_range_pcs_proof,
            pow_ext4_pcs_proof,
            val_ext4_pcs_proof,
            acc_ext4_pcs_proof,
            acc_next_ext4_pcs_proof,
            mult_rom_pcs_proof,
            t256_bytes_pcs_proof,
            t256_h_pcs_proof,
            t256_h_next_pcs_proof,
        })
    }
}

fn absorb_phase1_statement(
    tr: &mut CShakeTranscript,
    stmt: &DualCharBridgeStatement,
    len_pcs_root: &[u8; 32],
    cum_len_pcs_root: &[u8; 32],
    cum_len_next_pcs_root: &[u8; 32],
    mult_byte_range_pcs_root: &[u8; 32],
) {
    let mut s_bytes = Vec::with_capacity(200);
    stmt.write_to(&mut s_bytes);
    tr.absorb_bytes(b"bpe_bridge_stmt", &s_bytes);
    for r in [
        len_pcs_root,
        cum_len_pcs_root,
        cum_len_next_pcs_root,
        mult_byte_range_pcs_root,
    ] {
        tr.absorb_root(b"bpe_bridge_p1_aux", r);
    }
}

/// Prove in **both** `BabyBear Ext4` and `Tower256` (`GF(2^256)`) that the committed `tokens` stream
/// (`K` Qwen token IDs) and the `Tower256` salted byte stream detokenize to the exact same `(byte_len, raw_bytes)`.
pub fn prove_dual_char_bpe_bridge(
    rom: &QwenBpeRom,
    tokens: &[u32],
    salts_opt: Option<&[[u8; 31]]>,
) -> Result<(DualCharBridgeProof, Vec<u8>), String> {
    if tokens.is_empty() || tokens.len() > 4096 {
        return Err("tokens length must lie in 1..=4096".to_string());
    }
    let raw_bytes = rom.detokenize(tokens)?;
    prove_dual_char_bpe_bridge_with_explicit_bytes(rom, tokens, &raw_bytes, salts_opt)
}

/// Enclave-ready prover entry returning `(proof, raw_bytes, salts)` so `verify_dual_char_bpe_bridge_with_salts`
/// binds prover-supplied `raw_bytes` directly to the pre-challenge `stmt.tower256_salted_root` commitment!
pub fn prove_dual_char_bpe_bridge_salted(
    rom: &QwenBpeRom,
    tokens: &[u32],
) -> Result<(DualCharBridgeProof, Vec<u8>, Vec<[u8; 31]>), String> {
    if tokens.is_empty() || tokens.len() > 4096 {
        return Err("tokens length must lie in 1..=4096".to_string());
    }
    let raw_bytes = rom.detokenize(tokens)?;
    let byte_pad_len = (raw_bytes.len() + 2).next_power_of_two().max(512);
    let mut rng = CShakeRng::from_seed(b"QW35-T256-SALT-GEN-V1", &os_random_seed_32());
    let salts: Vec<[u8; 31]> = (0..byte_pad_len)
        .map(|_| {
            let mut s = [0u8; 31];
            rng.fill_bytes(&mut s);
            s
        })
        .collect();
    let (proof, _) = prove_dual_char_bpe_bridge_with_explicit_bytes(rom, tokens, &raw_bytes, Some(&salts))?;
    Ok((proof, raw_bytes, salts))
}

/// Internal/testable prover entry taking `(tokens, tower_and_bb_bytes)` explicitly (used by honest prover
/// with `raw_bytes = rom.detokenize(tokens)`, and by negative tests planting cross-world mismatches!).
pub fn prove_dual_char_bpe_bridge_with_explicit_bytes(
    rom: &QwenBpeRom,
    tokens: &[u32],
    claimed_bytes: &[u8],
    salts_opt: Option<&[[u8; 31]]>,
) -> Result<(DualCharBridgeProof, Vec<u8>), String> {
    let k_toks = tokens.len();
    let l_bytes = claimed_bytes.len();
    let tok_pad_len = (k_toks + 2).next_power_of_two().max(64);
    let m_tok = tok_pad_len.trailing_zeros() as usize;
    // `byte_pad_len >= 512` (`2^9`) so `D1b` `[0, 512)` range proof has `m_wit >= m_tab = 9`!
    let byte_pad_len = (l_bytes + 2).next_power_of_two().max(512);
    let m_byte = byte_pad_len.trailing_zeros() as usize;

    // --- Phase 1: Witness construction & Pre-Challenge Commitments (`BabyBear` + `Tower256`) ---
    let mut tok_col = vec![PAD_TOK_ID; tok_pad_len];
    let mut len_col = vec![0u32; tok_pad_len];
    let mut cum_len_col = vec![0u32; tok_pad_len];
    let mut cum_len_next_col = vec![0u32; tok_pad_len];
    let mut mult_rom = vec![0u32; ROM_PADDED_SIZE];

    let mut running_len = 0u32;
    for i in 0..tok_pad_len {
        cum_len_col[i] = running_len;
        if i < k_toks {
            let tid = tokens[i];
            let bs = rom.token_bytes(tid)?;
            tok_col[i] = tid;
            len_col[i] = bs.len() as u32;
            running_len += bs.len() as u32;
            mult_rom[tid as usize] += 1;
        } else {
            tok_col[i] = PAD_TOK_ID;
            len_col[i] = 0;
            mult_rom[QWEN_DEFINED_TOKENS] += 1; // canonical pad slot `248,066`
        }
        cum_len_next_col[i] = running_len;
    }

    let mut bytes_bb_col = vec![256u32; byte_pad_len];
    let mut bytes_t256_col = vec![Tower256::ZERO; byte_pad_len];
    for (j, &b) in claimed_bytes.iter().enumerate() {
        bytes_bb_col[j] = b as u32;
        bytes_t256_col[j] = Tower256::from_byte_gf256(b);
    }
    let mult_byte_range = compute_d1b_multiplicities(&bytes_bb_col, 9)?;

    let owned_salts: Vec<[u8; 31]>;
    let salts_ref: &[[u8; 31]] = match salts_opt {
        Some(s) => {
            if s.len() != byte_pad_len {
                return Err("salts_opt length must equal byte_pad_len".to_string());
            }
            s
        }
        None => {
            let mut rng = CShakeRng::from_seed(b"QW35-T256-SALT-GEN-V1", &os_random_seed_32());
            owned_salts = (0..byte_pad_len)
                .map(|_| {
                    let mut s = [0u8; 31];
                    rng.fill_bytes(&mut s);
                    s
                })
                .collect();
            &owned_salts
        }
    };

    let tok_state = commit_table_pcs(&tok_col, PcsParams::default_zk(1), None);
    let len_state = commit_table_pcs(&len_col, PcsParams::default_zk(2), None);
    let cum_len_state = commit_table_pcs(&cum_len_col, PcsParams::default_zk(3), None);
    let cum_len_next_state = commit_table_pcs(&cum_len_next_col, PcsParams::default_zk(2), None);
    let bytes_bb_state = commit_table_pcs(&bytes_bb_col, PcsParams::default_zk(3), None);
    let mult_byte_range_state = commit_table_pcs(&mult_byte_range, PcsParams::default_zk(1), None);

    let mut root_in = [0u8; 40];
    root_in[0..8].copy_from_slice(&(l_bytes as u64).to_le_bytes());
    root_in[8..40].copy_from_slice(&bytes_bb_state.root);
    let content_root_bb = cshake256_32(b"QW35-CONTENT-SCHEME-ROOT-V1", &root_in);

    let (tower256_salted_root, _) = commit_salted_bytes_t256(claimed_bytes, byte_pad_len, salts_ref);
    let t256_bytes_state = commit_t256_pcs(&bytes_t256_col, 5, None);

    let stmt = DualCharBridgeStatement {
        rom_merkle_root: rom.rom_merkle_root,
        num_tokens: k_toks,
        byte_len: l_bytes,
        tok_pad_len,
        byte_pad_len,
        tok_pcs_root: tok_state.root,
        bytes_bb_pcs_root: bytes_bb_state.root,
        content_root_bb,
        tower256_salted_root,
        tower256_bytes_pcs_root: t256_bytes_state.root,
    };

    let mut tr = CShakeTranscript::new(b"QW35-DUAL-CHAR-BPE-BRIDGE-V1");
    absorb_phase1_statement(
        &mut tr,
        &stmt,
        &len_state.root,
        &cum_len_state.root,
        &cum_len_next_state.root,
        &mult_byte_range_state.root,
    );

    // --- Phase 2: Squeeze Post-Commitment Cross-Characteristic Evaluation Bases! ---
    let beta_ext4 = tr.squeeze_ext4(b"bridge_beta_ext4", true);
    let beta_256 = squeeze_t256(&mut tr, b"bridge_beta_256", true);
    let p61_0 = squeeze_prime_61bit(&mut tr, b"bridge_p61_0");
    let p61_1 = squeeze_prime_61bit(&mut tr, b"bridge_p61_1");

    // --- Phase 3: Compute & Commit Post-Challenge Rolling Accumulator Traces ---
    let mut pow_ext4_col = vec![Ext4::ONE; tok_pad_len];
    let mut val_ext4_col = vec![Ext4::ZERO; tok_pad_len];
    let mut acc_ext4_col = vec![Ext4::ZERO; tok_pad_len];
    let mut acc_next_ext4_col = vec![Ext4::ZERO; tok_pad_len];

    let mut cur_acc_ext4 = Ext4::ZERO;
    for i in 0..tok_pad_len {
        acc_ext4_col[i] = cur_acc_ext4;
        if i < k_toks {
            let bs = rom.token_bytes(tokens[i])?;
            let pw = ext4_pow(beta_ext4, bs.len() as u64);
            let vl = eval_bytes_ext4(beta_ext4, bs);
            pow_ext4_col[i] = pw;
            val_ext4_col[i] = vl;
            cur_acc_ext4 = cur_acc_ext4.mul(pw).add(vl);
        } else {
            pow_ext4_col[i] = Ext4::ONE;
            val_ext4_col[i] = Ext4::ZERO;
        }
        acc_next_ext4_col[i] = cur_acc_ext4;
    }
    let final_acc_ext4 = cur_acc_ext4;

    let mut t256_h_col = vec![Tower256::ZERO; byte_pad_len];
    let mut t256_h_next_col = vec![Tower256::ZERO; byte_pad_len];
    let mut cur_h_t256 = Tower256::ZERO;
    for j in 0..byte_pad_len {
        t256_h_col[j] = cur_h_t256;
        if j < l_bytes {
            cur_h_t256 = cur_h_t256.mul(beta_256).add(bytes_t256_col[j]);
        }
        t256_h_next_col[j] = cur_h_t256;
    }
    let final_acc_t256 = cur_h_t256;

    // `p61` `IntegerFingerprint` evaluations over detokenized token bytes
    let detok_bytes_from_tokens = rom.detokenize(tokens)?;
    let fp_p61_0 = (p61_0, eval_bytes_mod_p61(p61_0, &detok_bytes_from_tokens));
    let fp_p61_1 = (p61_1, eval_bytes_mod_p61(p61_1, &detok_bytes_from_tokens));

    let pow_packed = pack_ext4_col_to_bb(&pow_ext4_col);
    let val_packed = pack_ext4_col_to_bb(&val_ext4_col);
    let acc_packed = pack_ext4_col_to_bb(&acc_ext4_col);
    let acc_next_packed = pack_ext4_col_to_bb(&acc_next_ext4_col);

    let pow_state = commit_table_pcs(&pow_packed, PcsParams::default_zk(2), None);
    let val_state = commit_table_pcs(&val_packed, PcsParams::default_zk(2), None);
    let acc_state = commit_table_pcs(&acc_packed, PcsParams::default_zk(3), None);
    let acc_next_state = commit_table_pcs(&acc_next_packed, PcsParams::default_zk(2), None);
    let mult_rom_state = commit_table_pcs(&mult_rom, PcsParams::default_zk(1), None);

    let t256_h_state = commit_t256_pcs(&t256_h_col, 3, None);
    let t256_h_next_state = commit_t256_pcs(&t256_h_next_col, 2, None);

    for r in [
        &pow_state.root,
        &val_state.root,
        &acc_state.root,
        &acc_next_state.root,
        &mult_rom_state.root,
        &t256_h_state.root,
        &t256_h_next_state.root,
    ] {
        tr.absorb_root(b"bpe_bridge_p3_root", r);
    }
    tr.absorb_ext4(b"final_acc_ext4", final_acc_ext4);
    tr.absorb_bytes(b"final_acc_t256", &final_acc_t256.to_le_bytes());
    tr.absorb_bytes(b"fp_p61_0", &fp_p61_0.1.to_le_bytes());
    tr.absorb_bytes(b"fp_p61_1", &fp_p61_1.1.to_le_bytes());

    // --- Proof 1: `D1b` `262,144`-slot `Qwen` ROM Lookup (`m_tok <= 18`) ---
    let gammas = [
        tr.squeeze_ext4(b"rom_g1", true),
        tr.squeeze_ext4(b"rom_g2", true),
        tr.squeeze_ext4(b"rom_g3", true),
        tr.squeeze_ext4(b"rom_g4", true),
    ];
    let rom_packed_ext4 = rom.build_packed_rom_table_ext4(beta_ext4, gammas);
    let wit_packed_ext4: Vec<Ext4> = (0..tok_pad_len)
        .map(|i| {
            let is_pad = if i < k_toks { Ext4::ZERO } else { Ext4::ONE };
            Ext4::from_bb(tok_col[i])
                .add(gammas[0].mul(is_pad))
                .add(gammas[1].scale_bb(len_col[i]))
                .add(gammas[2].mul(pow_ext4_col[i]))
                .add(gammas[3].mul(val_ext4_col[i]))
        })
        .collect();
    let (rom_d1b_proof, z_rom_tab) =
        prove_d1b_ext4_table(&wit_packed_ext4, &rom_packed_ext4, &mult_rom, &mut tr);
    let z_rom_tok = z_rom_tab[..m_tok].to_vec();

    let tok_at_rom_leaf = mle_eval_bb_at_ext4(&tok_col, &z_rom_tok);
    let len_at_rom_leaf = mle_eval_bb_at_ext4(&len_col, &z_rom_tok);
    let pow_at_rom_leaf = mle_eval_ext4_table(&pow_ext4_col, &z_rom_tok);
    let val_at_rom_leaf = mle_eval_ext4_table(&val_ext4_col, &z_rom_tok);
    for e in [
        tok_at_rom_leaf,
        len_at_rom_leaf,
        pow_at_rom_leaf,
        val_at_rom_leaf,
    ] {
        tr.absorb_ext4(b"rom_leaf_comp", e);
    }

    // --- Proof 2: `Ext4` Degree-2 Rolling AIR (`acc_next - val == acc * pow`) + Shift Sumchecks ---
    let z_roll = tr.squeeze_ext4_vec(b"z_roll_tok", m_tok, true);
    let acc_next_at_zroll = mle_eval_ext4_table(&acc_next_ext4_col, &z_roll);
    let val_at_zroll = mle_eval_ext4_table(&val_ext4_col, &z_roll);
    let cum_len_at_zroll = mle_eval_bb_at_ext4(&cum_len_col, &z_roll);
    let len_at_zroll = mle_eval_bb_at_ext4(&len_col, &z_roll);
    let cum_len_next_at_zroll = mle_eval_bb_at_ext4(&cum_len_next_col, &z_roll);
    for e in [
        acc_next_at_zroll,
        val_at_zroll,
        cum_len_at_zroll,
        len_at_zroll,
        cum_len_next_at_zroll,
    ] {
        tr.absorb_ext4(b"zroll_ev", e);
    }
    let (roll_prod_gruen_proof, z_roll_prod_chals) = prove_gruen_einsum_mode2_ext4(
        &acc_ext4_col,
        &pow_ext4_col,
        m_tok,
        0,
        &z_roll,
        &mut tr,
    );

    let z_sh_tok = tr.squeeze_ext4_vec(b"z_sh_tok", m_tok, true);
    let acc_next_at_zsh = mle_eval_ext4_table(&acc_next_ext4_col, &z_sh_tok);
    let cum_len_next_at_zsh = mle_eval_bb_at_ext4(&cum_len_next_col, &z_sh_tok);
    tr.absorb_ext4(b"acc_next_zsh", acc_next_at_zsh);
    tr.absorb_ext4(b"clen_next_zsh", cum_len_next_at_zsh);

    let eq_zsh_tok = build_eq_table_lsb_ext4(&z_sh_tok);
    let mut shift_tok_col = vec![Ext4::ZERO; tok_pad_len];
    for t in 0..(tok_pad_len - 1) {
        shift_tok_col[t + 1] = eq_zsh_tok[t];
    }
    let (acc_shift_gruen_proof, z_acc_sh_chals) =
        prove_gruen_einsum_mode2_ext4(&shift_tok_col, &acc_ext4_col, 0, m_tok, &[], &mut tr);
    let cum_len_ext: Vec<Ext4> = cum_len_col.iter().map(|&v| Ext4::from_bb(v)).collect();
    let (cum_len_shift_gruen_proof, z_clen_sh_chals) =
        prove_gruen_einsum_mode2_ext4(&shift_tok_col, &cum_len_ext, 0, m_tok, &[], &mut tr);

    // --- Proof 3: `BabyBear` Byte `[0, 512)` Range + `\beta_{ext4}` Horner IP + Tail EOF `== 256` ---
    let (byte_range_d1b_proof, z_byte_range_leaf) =
        prove_d1b_range_ext4(&bytes_bb_col, &mult_byte_range, m_byte, 9, &mut tr);

    let mut w_pow_ext4 = vec![Ext4::ZERO; byte_pad_len];
    if l_bytes > 0 {
        let mut cur = Ext4::ONE;
        for j in (0..l_bytes).rev() {
            w_pow_ext4[j] = cur;
            cur = cur.mul(beta_ext4);
        }
    }
    let bytes_bb_ext: Vec<Ext4> = bytes_bb_col.iter().map(|&b| Ext4::from_bb(b)).collect();
    let (byte_horner_gruen_proof, z_byte_ip_chals) =
        prove_gruen_einsum_mode2_ext4(&w_pow_ext4, &bytes_bb_ext, 0, m_byte, &[], &mut tr);

    let z_eof = tr.squeeze_ext4_vec(b"z_byte_eof", m_byte, true);
    let mut tail_ind = vec![Ext4::ZERO; byte_pad_len];
    let mut b_minus_256 = vec![Ext4::ZERO; byte_pad_len];
    for j in 0..byte_pad_len {
        if j >= l_bytes {
            tail_ind[j] = Ext4::ONE;
        }
        b_minus_256[j] = Ext4::from_bb(bsub(bytes_bb_col[j], 256));
    }
    let (byte_eof_tail_gruen_proof, z_byte_eof_chals) =
        prove_gruen_einsum_mode2_ext4(&tail_ind, &b_minus_256, m_byte, 0, &z_eof, &mut tr);

    // --- Proof 4: `Tower256` (`GF(2^256)`) Frobenius `GF(2^8)` Subfield Check + Horner AIR + Shift + Direct IP ---
    let z_frob = squeeze_t256_vec(&mut tr, b"t256_zfrob", m_byte, true);
    let z_frob_inv256: Vec<Tower256> = z_frob.iter().map(|&z| z.inv_pow256()).collect();
    let t256_b_at_zfrob = mle_eval_t256(&bytes_t256_col, &z_frob);
    let t256_b_at_zfrob_inv256 = mle_eval_t256(&bytes_t256_col, &z_frob_inv256);
    tr.absorb_bytes(b"t256_bfrob", &t256_b_at_zfrob.to_le_bytes());
    tr.absorb_bytes(b"t256_bfrob_inv", &t256_b_at_zfrob_inv256.to_le_bytes());

    // Horner step in `Tower256`: `h_next[j] \oplus active_b[j] == h[j] * step_mul[j]`
    // where `step_mul[j] = if j < L { beta_256 } else { 1 }`, and `bytes_t256_col[j] == 0` for `j >= L`!
    // Wait: let's also enforce `(j >= L) * bytes_t256_col[j] == 0` via `step_mul` + `direct_ip` AND check `b_at_zstep`!
    let z_step_t256 = squeeze_t256_vec(&mut tr, b"t256_zstep", m_byte, true);
    let t256_h_next_at_zstep = mle_eval_t256(&t256_h_next_col, &z_step_t256);
    let t256_b_at_zstep = mle_eval_t256(&bytes_t256_col, &z_step_t256);
    tr.absorb_bytes(b"t256_hn_zs", &t256_h_next_at_zstep.to_le_bytes());
    tr.absorb_bytes(b"t256_b_zs", &t256_b_at_zstep.to_le_bytes());

    let eq_zstep_256 = build_eq_table_lsb_t256(&z_step_t256);
    let mut step_mul_weighted = vec![Tower256::ZERO; byte_pad_len];
    for j in 0..byte_pad_len {
        let m_j = if j < l_bytes { beta_256 } else { Tower256::ONE };
        step_mul_weighted[j] = eq_zstep_256[j].mul(m_j);
    }
    let (t256_step_quad_proof, z_t256_step_chals) =
        prove_t256_quad_sumcheck(&step_mul_weighted, &t256_h_col, &mut tr);

    let z_sh_t256 = squeeze_t256_vec(&mut tr, b"t256_zsh", m_byte, true);
    let t256_h_next_at_zsh = mle_eval_t256(&t256_h_next_col, &z_sh_t256);
    tr.absorb_bytes(b"t256_hn_zsh", &t256_h_next_at_zsh.to_le_bytes());
    let eq_zsh_256 = build_eq_table_lsb_t256(&z_sh_t256);
    let mut shift_256_col = vec![Tower256::ZERO; byte_pad_len];
    for j in 0..(byte_pad_len - 1) {
        shift_256_col[j + 1] = eq_zsh_256[j];
    }
    let (t256_shift_quad_proof, z_t256_sh_chals) =
        prove_t256_quad_sumcheck(&shift_256_col, &t256_h_col, &mut tr);

    let mut w_pow_t256 = vec![Tower256::ZERO; byte_pad_len];
    if l_bytes > 0 {
        let mut cur = Tower256::ONE;
        for j in (0..l_bytes).rev() {
            w_pow_t256[j] = cur;
            cur = cur.mul(beta_256);
        }
    }
    let (t256_direct_ip_quad_proof, z_t256_ip_chals) =
        prove_t256_quad_sumcheck(&w_pow_t256, &bytes_t256_col, &mut tr);

    // Pointwise `Tower256` tail-zero zerocheck (`j >= l_bytes => bytes_t256_col[j] == 0`):
    let z_tail_t256 = squeeze_t256_vec(&mut tr, b"t256_ztail", m_byte, true);
    let eq_ztail_256 = build_eq_table_lsb_t256(&z_tail_t256);
    let mut tail_weighted_256 = vec![Tower256::ZERO; byte_pad_len];
    for j in l_bytes..byte_pad_len {
        tail_weighted_256[j] = eq_ztail_256[j];
    }
    let (t256_tail_zero_quad_proof, z_t256_tail_chals) =
        prove_t256_quad_sumcheck(&tail_weighted_256, &bytes_t256_col, &mut tr);

    // --- Proof 5: Open all Succinct ZK PCS Commitments (`BabyBear Ext4` + `Tower256`) ---
    let tok_pcs_proof = open_pcs_claims(
        &tok_state,
        &[MleEvalClaim {
            point: z_rom_tok.clone(),
            value: tok_at_rom_leaf,
        }],
        &mut tr,
    );
    let len_pcs_proof = open_pcs_claims(
        &len_state,
        &[
            MleEvalClaim {
                point: z_rom_tok.clone(),
                value: len_at_rom_leaf,
            },
            MleEvalClaim {
                point: z_roll.clone(),
                value: len_at_zroll,
            },
        ],
        &mut tr,
    );
    let cum_len_pcs_proof = open_pcs_claims(
        &cum_len_state,
        &[
            MleEvalClaim {
                point: vec![Ext4::ZERO; m_tok],
                value: Ext4::ZERO, // `cum_len[0] == 0`!
            },
            MleEvalClaim {
                point: z_roll.clone(),
                value: cum_len_at_zroll,
            },
            MleEvalClaim {
                point: z_clen_sh_chals,
                value: cum_len_shift_gruen_proof.terminal_openings.1,
            },
        ],
        &mut tr,
    );
    let cum_len_next_pcs_proof = open_pcs_claims(
        &cum_len_next_state,
        &[
            MleEvalClaim {
                point: z_roll.clone(),
                value: cum_len_next_at_zroll,
            },
            MleEvalClaim {
                point: z_sh_tok.clone(),
                value: cum_len_next_at_zsh,
            },
        ],
        &mut tr,
    );
    let bytes_bb_pcs_proof = open_pcs_claims(
        &bytes_bb_state,
        &[
            MleEvalClaim {
                point: z_byte_range_leaf.clone(),
                value: byte_range_d1b_proof.rem_leaf_eval,
            },
            MleEvalClaim {
                point: z_byte_ip_chals,
                value: byte_horner_gruen_proof.terminal_openings.1,
            },
            MleEvalClaim {
                point: z_byte_eof_chals,
                value: byte_eof_tail_gruen_proof
                    .terminal_openings
                    .1
                    .add(Ext4::from_bb(256)),
            },
        ],
        &mut tr,
    );
    let mult_byte_range_pcs_proof = open_pcs_claims(
        &mult_byte_range_state,
        &[MleEvalClaim {
            point: z_byte_range_leaf[..9].to_vec(),
            value: byte_range_d1b_proof.mult_leaf_eval,
        }],
        &mut tr,
    );
    let pow_ext4_pcs_proof = open_pcs_claims(
        &pow_state,
        &[
            make_packed_ext4_pcs_claim(&z_rom_tok, pow_at_rom_leaf),
            make_packed_ext4_pcs_claim(&z_roll_prod_chals, roll_prod_gruen_proof.terminal_openings.1),
        ],
        &mut tr,
    );
    let val_ext4_pcs_proof = open_pcs_claims(
        &val_state,
        &[
            make_packed_ext4_pcs_claim(&z_rom_tok, val_at_rom_leaf),
            make_packed_ext4_pcs_claim(&z_roll, val_at_zroll),
        ],
        &mut tr,
    );
    let acc_ext4_pcs_proof = open_pcs_claims(
        &acc_state,
        &[
            make_packed_ext4_pcs_claim(&vec![Ext4::ZERO; m_tok], Ext4::ZERO), // `acc[0] == 0`!
            make_packed_ext4_pcs_claim(&z_roll_prod_chals, roll_prod_gruen_proof.terminal_openings.0),
            make_packed_ext4_pcs_claim(&z_acc_sh_chals, acc_shift_gruen_proof.terminal_openings.1),
        ],
        &mut tr,
    );
    let acc_next_ext4_pcs_proof = open_pcs_claims(
        &acc_next_state,
        &[
            make_packed_ext4_pcs_claim(&z_roll, acc_next_at_zroll),
            make_packed_ext4_pcs_claim(&z_sh_tok, acc_next_at_zsh),
        ],
        &mut tr,
    );
    let mult_rom_pcs_proof = open_pcs_claims(
        &mult_rom_state,
        &[MleEvalClaim {
            point: z_rom_tab,
            value: rom_d1b_proof.mult_leaf_eval,
        }],
        &mut tr,
    );

    let t256_bytes_pcs_proof = open_t256_pcs(
        &t256_bytes_state,
        &[
            Tower256MleClaim {
                point: z_frob,
                value: t256_b_at_zfrob,
            },
            Tower256MleClaim {
                point: z_frob_inv256,
                value: t256_b_at_zfrob_inv256,
            },
            Tower256MleClaim {
                point: z_step_t256.clone(),
                value: t256_b_at_zstep,
            },
            Tower256MleClaim {
                point: z_t256_ip_chals,
                value: t256_direct_ip_quad_proof.term_b,
            },
            Tower256MleClaim {
                point: z_t256_tail_chals,
                value: t256_tail_zero_quad_proof.term_b,
            },
        ],
        &mut tr,
    );
    let t256_h_pcs_proof = open_t256_pcs(
        &t256_h_state,
        &[
            Tower256MleClaim {
                point: vec![Tower256::ZERO; m_byte],
                value: Tower256::ZERO, // `h[0] == 0`!
            },
            Tower256MleClaim {
                point: z_t256_step_chals,
                value: t256_step_quad_proof.term_b,
            },
            Tower256MleClaim {
                point: z_t256_sh_chals,
                value: t256_shift_quad_proof.term_b,
            },
        ],
        &mut tr,
    );
    let t256_h_next_pcs_proof = open_t256_pcs(
        &t256_h_next_state,
        &[
            Tower256MleClaim {
                point: z_step_t256,
                value: t256_h_next_at_zstep,
            },
            Tower256MleClaim {
                point: z_sh_t256,
                value: t256_h_next_at_zsh,
            },
        ],
        &mut tr,
    );

    Ok((
        DualCharBridgeProof {
            stmt,
            len_pcs_root: len_state.root,
            cum_len_pcs_root: cum_len_state.root,
            cum_len_next_pcs_root: cum_len_next_state.root,
            mult_byte_range_pcs_root: mult_byte_range_state.root,
            pow_ext4_pcs_root: pow_state.root,
            val_ext4_pcs_root: val_state.root,
            acc_ext4_pcs_root: acc_state.root,
            acc_next_ext4_pcs_root: acc_next_state.root,
            mult_rom_pcs_root: mult_rom_state.root,
            t256_h_pcs_root: t256_h_state.root,
            t256_h_next_pcs_root: t256_h_next_state.root,
            final_acc_ext4,
            final_acc_t256,
            fp_p61_0,
            fp_p61_1,
            rom_d1b_proof,
            tok_at_rom_leaf,
            len_at_rom_leaf,
            pow_at_rom_leaf,
            val_at_rom_leaf,
            acc_next_at_zroll,
            val_at_zroll,
            cum_len_at_zroll,
            len_at_zroll,
            cum_len_next_at_zroll,
            roll_prod_gruen_proof,
            acc_next_at_zsh,
            acc_shift_gruen_proof,
            cum_len_next_at_zsh,
            cum_len_shift_gruen_proof,
            byte_range_d1b_proof,
            byte_horner_gruen_proof,
            byte_eof_tail_gruen_proof,
            t256_b_at_zfrob,
            t256_b_at_zfrob_inv256,
            t256_h_next_at_zstep,
            t256_b_at_zstep,
            t256_step_quad_proof,
            t256_h_next_at_zsh,
            t256_shift_quad_proof,
            t256_direct_ip_quad_proof,
            t256_tail_zero_quad_proof,
            tok_pcs_proof,
            len_pcs_proof,
            cum_len_pcs_proof,
            cum_len_next_pcs_proof,
            bytes_bb_pcs_proof,
            mult_byte_range_pcs_proof,
            pow_ext4_pcs_proof,
            val_ext4_pcs_proof,
            acc_ext4_pcs_proof,
            acc_next_ext4_pcs_proof,
            mult_rom_pcs_proof,
            t256_bytes_pcs_proof,
            t256_h_pcs_proof,
            t256_h_next_pcs_proof,
        },
        claimed_bytes.to_vec(),
    ))
}

/// Standalone fail-closed verifier for `DualCharBridgeProof`.
/// - When `opt_expected_bytes = Some(bs)` (Gateway / Policy-Enclave Weld): verifies `bs.len() == stmt.byte_len`,
///   `final_acc_ext4 == eval_bytes_ext4(beta_ext4, bs)`, `final_acc_t256 == eval_bytes_t256(beta_256, bs)`,
///   AND both `p61` `IntegerFingerprint` evaluations (`< 2^{-104.6}` overall soundness, `0` token witness access!).
/// - Even when `opt_expected_bytes = None` (Zero-Cleartext External Audit): verifies all `BabyBear Ext4`
///   (`D1b` ROM + rolling AIR + `bytes_bb` weld) and `Tower256` (`GF(2^8)` Frobenius + Horner AIR + ZK PCS) proofs!
pub fn verify_dual_char_bpe_bridge(
    rom: &QwenBpeRom,
    opt_expected_bytes: Option<&[u8]>,
    proof: &DualCharBridgeProof,
) -> Result<(), String> {
    verify_dual_char_bpe_bridge_with_salts(rom, opt_expected_bytes, None, proof)
}

/// Extended standalone verifier that ALSO binds `stmt.tower256_salted_root` directly to `(expected_bytes, salts)`
/// when the `Tower256` policy enclave supplies its `248`-bit per-leaf salts `opt_salts`.
pub fn verify_dual_char_bpe_bridge_with_salts(
    rom: &QwenBpeRom,
    opt_expected_bytes: Option<&[u8]>,
    opt_salts: Option<&[[u8; 31]]>,
    proof: &DualCharBridgeProof,
) -> Result<(), String> {
    let stmt = &proof.stmt;
    if stmt.rom_merkle_root != rom.rom_merkle_root {
        return Err("ROM Merkle root mismatch against QwenBpeRom".to_string());
    }
    if stmt.num_tokens == 0
        || stmt.num_tokens > 4096
        || stmt.tok_pad_len != (stmt.num_tokens + 2).next_power_of_two().max(64)
    {
        return Err("invalid canonical token stream shape in DualCharBridgeStatement".to_string());
    }
    let max_possible_bytes = stmt.num_tokens.saturating_mul(rom.max_token_byte_len);
    if stmt.byte_len > max_possible_bytes
        || stmt.byte_pad_len != (stmt.byte_len + 2).next_power_of_two().max(512)
    {
        return Err("invalid canonical byte stream shape in DualCharBridgeStatement".to_string());
    }
    if let Some(salts) = opt_salts {
        let expected_bs = opt_expected_bytes
            .ok_or_else(|| "opt_salts requires opt_expected_bytes = Some(..)".to_string())?;
        if expected_bs.len() != stmt.byte_len || salts.len() != stmt.byte_pad_len {
            return Err("salted Tower256 root check length mismatch".to_string());
        }
        let (recomputed_salted_root, _) =
            commit_salted_bytes_t256(expected_bs, stmt.byte_pad_len, salts);
        if recomputed_salted_root != stmt.tower256_salted_root {
            return Err("Tower256 salted byte Merkle root mismatch".to_string());
        }
    }

    let mut root_in = [0u8; 40];
    root_in[0..8].copy_from_slice(&(stmt.byte_len as u64).to_le_bytes());
    root_in[8..40].copy_from_slice(&stmt.bytes_bb_pcs_root);
    if cshake256_32(b"QW35-CONTENT-SCHEME-ROOT-V1", &root_in) != stmt.content_root_bb {
        return Err("content_root_bb != cSHAKE256(byte_len || bytes_bb_pcs_root)".to_string());
    }

    let m_tok = stmt.tok_pad_len.trailing_zeros() as usize;
    let m_byte = stmt.byte_pad_len.trailing_zeros() as usize;

    let mut tr = CShakeTranscript::new(b"QW35-DUAL-CHAR-BPE-BRIDGE-V1");
    absorb_phase1_statement(
        &mut tr,
        stmt,
        &proof.len_pcs_root,
        &proof.cum_len_pcs_root,
        &proof.cum_len_next_pcs_root,
        &proof.mult_byte_range_pcs_root,
    );

    let beta_ext4 = tr.squeeze_ext4(b"bridge_beta_ext4", true);
    let beta_256 = squeeze_t256(&mut tr, b"bridge_beta_256", true);
    let p61_0 = squeeze_prime_61bit(&mut tr, b"bridge_p61_0");
    let p61_1 = squeeze_prime_61bit(&mut tr, b"bridge_p61_1");

    if proof.fp_p61_0.0 != p61_0 || proof.fp_p61_1.0 != p61_1 {
        return Err("squeezed 61-bit IntegerFingerprint prime mismatch".to_string());
    }

    if let Some(expected_bs) = opt_expected_bytes {
        if expected_bs.len() != stmt.byte_len {
            return Err(format!(
                "byte_len mismatch: expected_bytes={} vs stmt.byte_len={} (leading-zero / length-omission guard)",
                expected_bs.len(),
                stmt.byte_len
            ));
        }
        if proof.final_acc_ext4 != eval_bytes_ext4(beta_ext4, expected_bs) {
            return Err("cross-characteristic mismatch: final_acc_ext4 != eval_bytes_ext4(beta_ext4, raw_bytes)".to_string());
        }
        if proof.final_acc_t256 != eval_bytes_t256(beta_256, expected_bs) {
            return Err("cross-characteristic mismatch: final_acc_t256 != eval_bytes_t256(beta_256, raw_bytes)".to_string());
        }
        if proof.fp_p61_0.1 != eval_bytes_mod_p61(p61_0, expected_bs)
            || proof.fp_p61_1.1 != eval_bytes_mod_p61(p61_1, expected_bs)
        {
            return Err("IntegerFingerprint mod-p61 cross-characteristic check failed".to_string());
        }
    }

    for r in [
        &proof.pow_ext4_pcs_root,
        &proof.val_ext4_pcs_root,
        &proof.acc_ext4_pcs_root,
        &proof.acc_next_ext4_pcs_root,
        &proof.mult_rom_pcs_root,
        &proof.t256_h_pcs_root,
        &proof.t256_h_next_pcs_root,
    ] {
        tr.absorb_root(b"bpe_bridge_p3_root", r);
    }
    tr.absorb_ext4(b"final_acc_ext4", proof.final_acc_ext4);
    tr.absorb_bytes(b"final_acc_t256", &proof.final_acc_t256.to_le_bytes());
    tr.absorb_bytes(b"fp_p61_0", &proof.fp_p61_0.1.to_le_bytes());
    tr.absorb_bytes(b"fp_p61_1", &proof.fp_p61_1.1.to_le_bytes());

    // 1. Verify `D1b` `262,144`-slot Qwen ROM lookup & tuple equation!
    let gammas = [
        tr.squeeze_ext4(b"rom_g1", true),
        tr.squeeze_ext4(b"rom_g2", true),
        tr.squeeze_ext4(b"rom_g3", true),
        tr.squeeze_ext4(b"rom_g4", true),
    ];
    if proof.rom_d1b_proof.m_wit != m_tok || proof.rom_d1b_proof.m_tab != ROM_LOG_SIZE {
        return Err("ROM D1b dimensions mismatch".to_string());
    }
    let rom_packed_ext4 = rom.build_packed_rom_table_ext4(beta_ext4, gammas);
    let z_rom_tab = verify_d1b_ext4_table(&rom_packed_ext4, &proof.rom_d1b_proof, &mut tr)?;
    let z_rom_tok = z_rom_tab[..m_tok].to_vec();

    for e in [
        proof.tok_at_rom_leaf,
        proof.len_at_rom_leaf,
        proof.pow_at_rom_leaf,
        proof.val_at_rom_leaf,
    ] {
        tr.absorb_ext4(b"rom_leaf_comp", e);
    }
    let is_pad_ev = eval_tail_indicator_ext4(stmt.num_tokens, stmt.tok_pad_len, &z_rom_tok);
    let expected_rom_wit_tuple = proof
        .tok_at_rom_leaf
        .add(gammas[0].mul(is_pad_ev))
        .add(gammas[1].mul(proof.len_at_rom_leaf))
        .add(gammas[2].mul(proof.pow_at_rom_leaf))
        .add(gammas[3].mul(proof.val_at_rom_leaf));
    if proof.rom_d1b_proof.wit_leaf_eval != expected_rom_wit_tuple {
        return Err("ROM D1b leaf tuple != tok + g1*is_pad + g2*len + g3*pow + g4*val".to_string());
    }

    // 2. Verify `Ext4` degree-2 rolling accumulator (`acc_next - val == acc * pow`) + `cum_len` + shifts!
    let z_roll = tr.squeeze_ext4_vec(b"z_roll_tok", m_tok, true);
    for e in [
        proof.acc_next_at_zroll,
        proof.val_at_zroll,
        proof.cum_len_at_zroll,
        proof.len_at_zroll,
        proof.cum_len_next_at_zroll,
    ] {
        tr.absorb_ext4(b"zroll_ev", e);
    }
    if proof.cum_len_next_at_zroll != proof.cum_len_at_zroll.add(proof.len_at_zroll) {
        return Err("cum_len_next(z_roll) != cum_len(z_roll) + len(z_roll)".to_string());
    }
    if proof.roll_prod_gruen_proof.mu_s != m_tok || proof.roll_prod_gruen_proof.kappa != 0 {
        return Err("roll_prod Gruen dimensions mismatch".to_string());
    }
    let expected_prod_claim = proof.acc_next_at_zroll.sub(proof.val_at_zroll);
    let z_roll_prod_chals = verify_gruen_einsum_mode2_ext4(
        expected_prod_claim,
        &z_roll,
        &proof.roll_prod_gruen_proof,
        &mut tr,
    )?;

    let z_sh_tok = tr.squeeze_ext4_vec(b"z_sh_tok", m_tok, true);
    tr.absorb_ext4(b"acc_next_zsh", proof.acc_next_at_zsh);
    tr.absorb_ext4(b"clen_next_zsh", proof.cum_len_next_at_zsh);

    if proof.acc_shift_gruen_proof.mu_s != 0
        || proof.acc_shift_gruen_proof.kappa != m_tok
        || proof.cum_len_shift_gruen_proof.mu_s != 0
        || proof.cum_len_shift_gruen_proof.kappa != m_tok
    {
        return Err("token shift Gruen dimensions mismatch".to_string());
    }
    let eq_last_tok = eq_mle_ext4(&z_sh_tok, &vec![Ext4::ONE; m_tok]);
    let expected_acc_shift_claim = proof
        .acc_next_at_zsh
        .sub(eq_last_tok.mul(proof.final_acc_ext4));
    let z_acc_sh_chals = verify_gruen_einsum_mode2_ext4(
        expected_acc_shift_claim,
        &[],
        &proof.acc_shift_gruen_proof,
        &mut tr,
    )?;
    if proof.acc_shift_gruen_proof.terminal_openings.0
        != eval_shift_kernel_ext4(&z_sh_tok, &z_acc_sh_chals)
    {
        return Err("Ext4 acc shift kernel evaluation mismatch".to_string());
    }

    let expected_clen_shift_claim = proof
        .cum_len_next_at_zsh
        .sub(eq_last_tok.scale_bb(stmt.byte_len as u32));
    let z_clen_sh_chals = verify_gruen_einsum_mode2_ext4(
        expected_clen_shift_claim,
        &[],
        &proof.cum_len_shift_gruen_proof,
        &mut tr,
    )?;
    if proof.cum_len_shift_gruen_proof.terminal_openings.0
        != eval_shift_kernel_ext4(&z_sh_tok, &z_clen_sh_chals)
    {
        return Err("cum_len shift kernel evaluation mismatch".to_string());
    }

    // 3. Verify `BabyBear` byte `[0, 512)` range + `\beta_{ext4}` Horner IP == `final_acc_ext4` + EOF tail!
    if proof.byte_range_d1b_proof.m_wit != m_byte || proof.byte_range_d1b_proof.m_tab != 9 {
        return Err("byte_range D1b dimension mismatch".to_string());
    }
    let z_byte_range_leaf = verify_d1b_range_ext4(&proof.byte_range_d1b_proof, &mut tr)?;

    if proof.byte_horner_gruen_proof.mu_s != 0
        || proof.byte_horner_gruen_proof.kappa != m_byte
        || proof.byte_eof_tail_gruen_proof.mu_s != m_byte
        || proof.byte_eof_tail_gruen_proof.kappa != 0
    {
        return Err("byte Gruen dimensions mismatch".to_string());
    }

    let mut w_pow_ext4 = vec![Ext4::ZERO; stmt.byte_pad_len];
    if stmt.byte_len > 0 {
        let mut cur = Ext4::ONE;
        for j in (0..stmt.byte_len).rev() {
            w_pow_ext4[j] = cur;
            cur = cur.mul(beta_ext4);
        }
    }
    let z_byte_ip_chals = verify_gruen_einsum_mode2_ext4(
        proof.final_acc_ext4,
        &[],
        &proof.byte_horner_gruen_proof,
        &mut tr,
    )?;
    if proof.byte_horner_gruen_proof.terminal_openings.0
        != mle_eval_ext4_table(&w_pow_ext4, &z_byte_ip_chals)
    {
        return Err("BabyBear byte Horner weight MLE mismatch".to_string());
    }

    let z_eof = tr.squeeze_ext4_vec(b"z_byte_eof", m_byte, true);
    let z_byte_eof_chals =
        verify_gruen_einsum_mode2_ext4(Ext4::ZERO, &z_eof, &proof.byte_eof_tail_gruen_proof, &mut tr)?;
    if proof.byte_eof_tail_gruen_proof.terminal_openings.0
        != eval_tail_indicator_ext4(stmt.byte_len, stmt.byte_pad_len, &z_byte_eof_chals)
    {
        return Err("BabyBear byte EOF tail indicator mismatch".to_string());
    }

    // 4. Verify `Tower256` (`GF(2^256)`) Frobenius `GF(2^8)` subfield check + Horner step + shift + direct IP!
    let z_frob = squeeze_t256_vec(&mut tr, b"t256_zfrob", m_byte, true);
    let z_frob_inv256: Vec<Tower256> = z_frob.iter().map(|&z| z.inv_pow256()).collect();
    tr.absorb_bytes(b"t256_bfrob", &proof.t256_b_at_zfrob.to_le_bytes());
    tr.absorb_bytes(b"t256_bfrob_inv", &proof.t256_b_at_zfrob_inv256.to_le_bytes());
    if proof.t256_b_at_zfrob_inv256.pow256() != proof.t256_b_at_zfrob {
        return Err("Tower256 Frobenius GF(2^8) canonical-byte subfield check failed!".to_string());
    }

    let z_step_t256 = squeeze_t256_vec(&mut tr, b"t256_zstep", m_byte, true);
    tr.absorb_bytes(b"t256_hn_zs", &proof.t256_h_next_at_zstep.to_le_bytes());
    tr.absorb_bytes(b"t256_b_zs", &proof.t256_b_at_zstep.to_le_bytes());

    let expected_t256_step_claim = proof.t256_h_next_at_zstep.add(proof.t256_b_at_zstep);
    let z_t256_step_chals = verify_t256_quad_sumcheck(
        expected_t256_step_claim,
        m_byte,
        &proof.t256_step_quad_proof,
        &mut tr,
    )?;
    let eq_zstep_256 = build_eq_table_lsb_t256(&z_step_t256);
    let mut step_mul_weighted = vec![Tower256::ZERO; stmt.byte_pad_len];
    for j in 0..stmt.byte_pad_len {
        let m_j = if j < stmt.byte_len { beta_256 } else { Tower256::ONE };
        step_mul_weighted[j] = eq_zstep_256[j].mul(m_j);
    }
    if proof.t256_step_quad_proof.term_a != mle_eval_t256(&step_mul_weighted, &z_t256_step_chals) {
        return Err("Tower256 Horner step multiplier MLE mismatch".to_string());
    }

    let z_sh_t256 = squeeze_t256_vec(&mut tr, b"t256_zsh", m_byte, true);
    tr.absorb_bytes(b"t256_hn_zsh", &proof.t256_h_next_at_zsh.to_le_bytes());
    let eq_last_256 = eq_mle_t256(&z_sh_t256, &vec![Tower256::ONE; m_byte]);
    let expected_t256_sh_claim = proof
        .t256_h_next_at_zsh
        .add(eq_last_256.mul(proof.final_acc_t256));
    let z_t256_sh_chals = verify_t256_quad_sumcheck(
        expected_t256_sh_claim,
        m_byte,
        &proof.t256_shift_quad_proof,
        &mut tr,
    )?;
    if proof.t256_shift_quad_proof.term_a != eval_shift_kernel_t256(&z_sh_t256, &z_t256_sh_chals) {
        return Err("Tower256 Horner shift kernel MLE mismatch".to_string());
    }

    let mut w_pow_t256 = vec![Tower256::ZERO; stmt.byte_pad_len];
    if stmt.byte_len > 0 {
        let mut cur = Tower256::ONE;
        for j in (0..stmt.byte_len).rev() {
            w_pow_t256[j] = cur;
            cur = cur.mul(beta_256);
        }
    }
    let z_t256_ip_chals = verify_t256_quad_sumcheck(
        proof.final_acc_t256,
        m_byte,
        &proof.t256_direct_ip_quad_proof,
        &mut tr,
    )?;
    if proof.t256_direct_ip_quad_proof.term_a != mle_eval_t256(&w_pow_t256, &z_t256_ip_chals) {
        return Err("Tower256 direct Horner power vector MLE mismatch".to_string());
    }

    let z_tail_t256 = squeeze_t256_vec(&mut tr, b"t256_ztail", m_byte, true);
    let eq_ztail_256 = build_eq_table_lsb_t256(&z_tail_t256);
    let mut tail_weighted_256 = vec![Tower256::ZERO; stmt.byte_pad_len];
    for j in stmt.byte_len..stmt.byte_pad_len {
        tail_weighted_256[j] = eq_ztail_256[j];
    }
    let z_t256_tail_chals = verify_t256_quad_sumcheck(
        Tower256::ZERO,
        m_byte,
        &proof.t256_tail_zero_quad_proof,
        &mut tr,
    )?;
    if proof.t256_tail_zero_quad_proof.term_a
        != mle_eval_t256(&tail_weighted_256, &z_t256_tail_chals)
    {
        return Err("Tower256 tail-zero indicator MLE mismatch".to_string());
    }

    // 5. Verify all 11 `BabyBear Ext4` + 3 `Tower256` ZK PCS openings!
    verify_pcs_claims(
        &stmt.tok_pcs_root,
        PcsShape::new(m_tok, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: z_rom_tok.clone(),
            value: proof.tok_at_rom_leaf,
        }],
        &proof.tok_pcs_proof,
        &mut tr,
    )?;
    verify_pcs_claims(
        &proof.len_pcs_root,
        PcsShape::new(m_tok, PcsParams::default_zk(2)),
        &[
            MleEvalClaim {
                point: z_rom_tok.clone(),
                value: proof.len_at_rom_leaf,
            },
            MleEvalClaim {
                point: z_roll.clone(),
                value: proof.len_at_zroll,
            },
        ],
        &proof.len_pcs_proof,
        &mut tr,
    )?;
    verify_pcs_claims(
        &proof.cum_len_pcs_root,
        PcsShape::new(m_tok, PcsParams::default_zk(3)),
        &[
            MleEvalClaim {
                point: vec![Ext4::ZERO; m_tok],
                value: Ext4::ZERO,
            },
            MleEvalClaim {
                point: z_roll.clone(),
                value: proof.cum_len_at_zroll,
            },
            MleEvalClaim {
                point: z_clen_sh_chals,
                value: proof.cum_len_shift_gruen_proof.terminal_openings.1,
            },
        ],
        &proof.cum_len_pcs_proof,
        &mut tr,
    )?;
    verify_pcs_claims(
        &proof.cum_len_next_pcs_root,
        PcsShape::new(m_tok, PcsParams::default_zk(2)),
        &[
            MleEvalClaim {
                point: z_roll.clone(),
                value: proof.cum_len_next_at_zroll,
            },
            MleEvalClaim {
                point: z_sh_tok.clone(),
                value: proof.cum_len_next_at_zsh,
            },
        ],
        &proof.cum_len_next_pcs_proof,
        &mut tr,
    )?;
    verify_pcs_claims(
        &stmt.bytes_bb_pcs_root,
        PcsShape::new(m_byte, PcsParams::default_zk(3)),
        &[
            MleEvalClaim {
                point: z_byte_range_leaf.clone(),
                value: proof.byte_range_d1b_proof.rem_leaf_eval,
            },
            MleEvalClaim {
                point: z_byte_ip_chals,
                value: proof.byte_horner_gruen_proof.terminal_openings.1,
            },
            MleEvalClaim {
                point: z_byte_eof_chals,
                value: proof
                    .byte_eof_tail_gruen_proof
                    .terminal_openings
                    .1
                    .add(Ext4::from_bb(256)),
            },
        ],
        &proof.bytes_bb_pcs_proof,
        &mut tr,
    )?;
    verify_pcs_claims(
        &proof.mult_byte_range_pcs_root,
        PcsShape::new(9, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: z_byte_range_leaf[..9].to_vec(),
            value: proof.byte_range_d1b_proof.mult_leaf_eval,
        }],
        &proof.mult_byte_range_pcs_proof,
        &mut tr,
    )?;
    verify_pcs_claims(
        &proof.pow_ext4_pcs_root,
        PcsShape::new(m_tok + 2, PcsParams::default_zk(2)),
        &[
            make_packed_ext4_pcs_claim(&z_rom_tok, proof.pow_at_rom_leaf),
            make_packed_ext4_pcs_claim(&z_roll_prod_chals, proof.roll_prod_gruen_proof.terminal_openings.1),
        ],
        &proof.pow_ext4_pcs_proof,
        &mut tr,
    )?;
    verify_pcs_claims(
        &proof.val_ext4_pcs_root,
        PcsShape::new(m_tok + 2, PcsParams::default_zk(2)),
        &[
            make_packed_ext4_pcs_claim(&z_rom_tok, proof.val_at_rom_leaf),
            make_packed_ext4_pcs_claim(&z_roll, proof.val_at_zroll),
        ],
        &proof.val_ext4_pcs_proof,
        &mut tr,
    )?;
    verify_pcs_claims(
        &proof.acc_ext4_pcs_root,
        PcsShape::new(m_tok + 2, PcsParams::default_zk(3)),
        &[
            make_packed_ext4_pcs_claim(&vec![Ext4::ZERO; m_tok], Ext4::ZERO),
            make_packed_ext4_pcs_claim(&z_roll_prod_chals, proof.roll_prod_gruen_proof.terminal_openings.0),
            make_packed_ext4_pcs_claim(&z_acc_sh_chals, proof.acc_shift_gruen_proof.terminal_openings.1),
        ],
        &proof.acc_ext4_pcs_proof,
        &mut tr,
    )?;
    verify_pcs_claims(
        &proof.acc_next_ext4_pcs_root,
        PcsShape::new(m_tok + 2, PcsParams::default_zk(2)),
        &[
            make_packed_ext4_pcs_claim(&z_roll, proof.acc_next_at_zroll),
            make_packed_ext4_pcs_claim(&z_sh_tok, proof.acc_next_at_zsh),
        ],
        &proof.acc_next_ext4_pcs_proof,
        &mut tr,
    )?;
    verify_pcs_claims(
        &proof.mult_rom_pcs_root,
        PcsShape::new(ROM_LOG_SIZE, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: z_rom_tab,
            value: proof.rom_d1b_proof.mult_leaf_eval,
        }],
        &proof.mult_rom_pcs_proof,
        &mut tr,
    )?;

    verify_t256_pcs(
        &stmt.tower256_bytes_pcs_root,
        &[
            Tower256MleClaim {
                point: z_frob,
                value: proof.t256_b_at_zfrob,
            },
            Tower256MleClaim {
                point: z_frob_inv256,
                value: proof.t256_b_at_zfrob_inv256,
            },
            Tower256MleClaim {
                point: z_step_t256.clone(),
                value: proof.t256_b_at_zstep,
            },
            Tower256MleClaim {
                point: z_t256_ip_chals,
                value: proof.t256_direct_ip_quad_proof.term_b,
            },
            Tower256MleClaim {
                point: z_t256_tail_chals,
                value: proof.t256_tail_zero_quad_proof.term_b,
            },
        ],
        &proof.t256_bytes_pcs_proof,
        &mut tr,
    )?;
    verify_t256_pcs(
        &proof.t256_h_pcs_root,
        &[
            Tower256MleClaim {
                point: vec![Tower256::ZERO; m_byte],
                value: Tower256::ZERO,
            },
            Tower256MleClaim {
                point: z_t256_step_chals,
                value: proof.t256_step_quad_proof.term_b,
            },
            Tower256MleClaim {
                point: z_t256_sh_chals,
                value: proof.t256_shift_quad_proof.term_b,
            },
        ],
        &proof.t256_h_pcs_proof,
        &mut tr,
    )?;
    verify_t256_pcs(
        &proof.t256_h_next_pcs_root,
        &[
            Tower256MleClaim {
                point: z_step_t256,
                value: proof.t256_h_next_at_zstep,
            },
            Tower256MleClaim {
                point: z_sh_t256,
                value: proof.t256_h_next_at_zsh,
            },
        ],
        &proof.t256_h_next_pcs_proof,
        &mut tr,
    )?;

    Ok(())
}

/// Deterministic multi-pattern byte-level redaction (`VerifiedAstTransducer.defaultSecretRules` mirror)
/// scrubbing `sk-...`, `Bearer ...`, `-----BEGIN ...`, `{{`, and `ghp_...`.
pub fn redact_default_secret_classes(raw: &[u8]) -> (Vec<u8>, usize) {
    #[inline]
    fn is_api_body(b: u8) -> bool {
        b.is_ascii_alphanumeric() || b == b'_' || b == b'-'
    }
    #[inline]
    fn is_bearer_body(b: u8) -> bool {
        is_api_body(b) || b == b'.' || b == b'~' || b == b'+' || b == b'/' || b == b'='
    }
    #[inline]
    fn is_pem_body(b: u8) -> bool {
        b.is_ascii_uppercase() || b.is_ascii_digit() || b == b' ' || b == b'-'
    }

    let rules: [(&[u8], Option<fn(u8) -> bool>, &[u8]); 5] = [
        (b"sk-", Some(is_api_body), b"[REDACTED_API_KEY]"),
        (b"Bearer ", Some(is_bearer_body), b"[REDACTED_BEARER]"),
        (b"-----BEGIN ", Some(is_pem_body), b"[REDACTED_PEM]"),
        (b"{{", None, b"[REDACTED_TPL]"),
        (b"ghp_", Some(is_api_body), b"[REDACTED_GH_PAT]"),
    ];

    let mut out = Vec::with_capacity(raw.len());
    let mut hits = 0usize;
    let mut i = 0usize;
    while i < raw.len() {
        let rem = &raw[i..];
        let mut best: Option<(usize, &[u8])> = None;
        for &(pat, pred_opt, repl) in &rules {
            if rem.starts_with(pat) {
                let mut mlen = pat.len();
                if let Some(pred) = pred_opt {
                    while mlen < rem.len() && pred(rem[mlen]) {
                        mlen += 1;
                    }
                }
                if best.map_or(true, |b| mlen > b.0) {
                    best = Some((mlen, repl));
                }
            }
        }
        if let Some((mlen, repl)) = best {
            out.extend_from_slice(repl);
            hits += 1;
            i += mlen;
        } else {
            out.push(raw[i]);
            i += 1;
        }
    }
    (out, hits)
}
