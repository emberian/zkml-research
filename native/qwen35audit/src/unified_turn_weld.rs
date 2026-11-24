//! Wave-8 Cross-Tree Gate `G9` + Flagship Vertical #2 (`PayableComputeReceipt`):
//! Unified Salted Byte PCS (`pad >= 2048`, `TVD = 0` Cross-Commitment Equality Weld) +
//! Autoregressive `SpecPrefill` Token-Carry & Looped Residual-Carry Weld (`wave7` §4 `L2/L7`) +
//! Post-Countersignature League-of-Entropy `drand` `quicknet` (`BLS12-381` RFC 9380) Audited
//! `Qwen/Qwen3.5-0.8B-Base` `PayableComputeReceipt` (`< 650 KiB`, `< 25 ms` standalone verify).

use crate::bpe_bridge::{
    eval_bytes_ext4, ext4_pow, pack_ext4_col_to_bb, prove_d1b_ext4_table,
    prove_dual_char_bpe_bridge_salted, verify_dual_char_bpe_bridge_with_salts, D1bExt4TableProof,
    DualCharBridgeProof, QwenBpeRom, PAD_TOK_ID, QWEN_DEFINED_TOKENS, ROM_LOG_SIZE,
    ROM_PADDED_SIZE,
};
use crate::ext4::{
    badd, bb_from_i64, build_eq_table_lsb_ext4, cshake256_32, cshake256_xof, eq_lin_ext4,
    eq_mle_ext4, eval_cubic_zero_one_two_inf_ext4, merkle_node_cshake, mle_eval_bb_at_ext4,
    os_random_seed_32, ByteCursor, CShakeRng, CShakeTranscript, Ext4, MerkleSinglePath, INV2_BB, P,
    P_U32,
};
use crate::gruen_ext4::{
    compute_d1b_multiplicities, compute_d1b_public_table_multiplicities,
    prove_d1b_public_table_ext4, prove_d1b_range_ext4, prove_mxfp4_delayed_bjk_horner_ext4,
    verify_d1b_public_table_ext4, verify_d1b_range_ext4, verify_mxfp4_delayed_bjk_horner_ext4,
    D1bRangeExt4Proof, Mxfp4DelayedBjkExt4Proof,
};
use crate::pcs_ext4::{
    open_pcs_claims, verify_pcs_claims, MleEvalClaim, PcsOpeningProof, PcsParams, PcsShape,
};
use crate::qwen35_layer::{eval_mxfp4_int_contraction, pad_mxfp4_cols_pow2, Qwen35TurnExecution};
use crate::safetensors_mmap::{decode_e2m1_x2_bb, Mxfp4Matrix, Qwen35WeightRegistry, WY_SCALE};
use crate::u1_audit::run_padded_complement_sk_dfa;
use crate::whir_ext4::{
    build_collision_free_sk_dfa_table_4096, open_whir_batch_ext4, pack_ext4_slice,
    prove_gmask_einsum_ext4, unpack_ext4_slice, verify_gmask_einsum_ext4, verify_whir_batch_ext4,
    BlindedEinSumExt4Proof, GMaskExt4, GMaskSpecExt4, GmaskEinSumParams, JointLinearClaimExt4,
    LinearTermExt4, PrecommittedWhirMxfp4, WhirBatchOpeningProofExt4, WhirCommittedMatrixExt4,
    WhirExt4MatrixShape, WHIR_EXT4_BLOWUP, WHIR_EXT4_T_QUERIES_100,
};
use rayon::prelude::*;
use sha2::{Digest, Sha256};
use std::ops::{Add, Mul, Neg, Sub};

// ================================================================================================
// §1. Zero-Dependency Pure-Rust `BLS12-381` Pairing + RFC 9380 `drand` `quicknet` Verifier + `WOTS+`
// ================================================================================================

/// League of Entropy `drand` `quicknet` scheme ID (`G2` 96B keys, `G1` 48B signatures, unchained).
pub const DRAND_QUICKNET_SCHEME: &str = "bls-unchained-g1-rfc9380";
/// RFC 9380 `hash_to_curve` DST fixed by `drand` `quicknet`.
pub const DRAND_QUICKNET_DST: &[u8] = b"BLS_SIG_BLS12381G1_XMD:SHA-256_SSWU_RO_NUL_";
/// Genesis-pinned `drand` `quicknet` group public key (`chain_hash = 52db9ba7...00c84e971`).
pub const DRAND_QUICKNET_GROUP_PUBLIC_KEY: [u8; 96] = [
    0x83, 0xcf, 0x0f, 0x28, 0x96, 0xad, 0xee, 0x7e, 0xb8, 0xb5, 0xf0, 0x1f, 0xca, 0xd3, 0x91, 0x22,
    0x12, 0xc4, 0x37, 0xe0, 0x07, 0x3e, 0x91, 0x1f, 0xb9, 0x00, 0x22, 0xd3, 0xe7, 0x60, 0x18, 0x3c,
    0x8c, 0x4b, 0x45, 0x0b, 0x6a, 0x0a, 0x6c, 0x3a, 0xc6, 0xa5, 0x77, 0x6a, 0x2d, 0x10, 0x64, 0x51,
    0x0d, 0x1f, 0xec, 0x75, 0x8c, 0x92, 0x1c, 0xc2, 0x2b, 0x0e, 0x17, 0xe6, 0x3a, 0xaf, 0x4b, 0xcb,
    0x5e, 0xd6, 0x63, 0x04, 0xde, 0x9c, 0xf8, 0x09, 0xbd, 0x27, 0x4c, 0xa7, 0x3b, 0xab, 0x4a, 0xf5,
    0xa6, 0xe9, 0xc7, 0x6a, 0x4b, 0xc0, 0x9e, 0x76, 0xea, 0xe8, 0x99, 0x1e, 0xf5, 0xec, 0xe4, 0x5a,
];

/// Published League of Entropy `drand` `quicknet` round `1_000_000` vector (`breadstuffs/procgen-dregg`).
pub const PINNED_QUICKNET_ROUND_1M: u64 = 1_000_000;
pub const PINNED_QUICKNET_SIG_1M: [u8; 48] = [
    0x83, 0xad, 0x29, 0xe4, 0xc4, 0x09, 0xf9, 0x47, 0x0f, 0xc2, 0xef, 0x02, 0xf9, 0x02, 0x14, 0xdf,
    0x49, 0xe0, 0x2b, 0x44, 0x1a, 0x1a, 0x24, 0x1a, 0x82, 0xd6, 0x22, 0xd9, 0xf6, 0x08, 0xef, 0x98,
    0xfd, 0x8b, 0x11, 0xa0, 0x29, 0xf1, 0xbe, 0xe9, 0xd9, 0xe8, 0x3b, 0x45, 0x08, 0x8a, 0xbe, 0x72,
];

/// Verified or candidate `drand` `quicknet` beacon opening.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DrandQuicknetBeacon {
    pub round: u64,
    pub signature: [u8; 48],
    pub randomness: [u8; 32],
}

#[inline]
fn read_u64_le(cur: &mut ByteCursor<'_>) -> Result<u64, String> {
    let b = cur.read_exact(8)?;
    Ok(u64::from_le_bytes(b.try_into().unwrap()))
}

impl DrandQuicknetBeacon {
    pub fn from_round_and_sig(round: u64, signature: [u8; 48]) -> Self {
        let mut h = Sha256::new();
        h.update(signature);
        let randomness: [u8; 32] = h.finalize().into();
        Self {
            round,
            signature,
            randomness,
        }
    }

    pub fn pinned_round_1m() -> Self {
        Self::from_round_and_sig(PINNED_QUICKNET_ROUND_1M, PINNED_QUICKNET_SIG_1M)
    }

    pub fn write_to(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.round.to_le_bytes());
        out.extend_from_slice(&self.signature);
        out.extend_from_slice(&self.randomness);
    }

    pub fn read_from(cur: &mut ByteCursor<'_>) -> Result<Self, String> {
        let round = read_u64_le(cur)?;
        let sig_s = cur.read_exact(48)?;
        let mut signature = [0u8; 48];
        signature.copy_from_slice(sig_s);
        let randomness = cur.read_arr32()?;
        Ok(Self {
            round,
            signature,
            randomness,
        })
    }
}

pub mod bls_drand {
    use super::{DrandQuicknetBeacon, DRAND_QUICKNET_DST, DRAND_QUICKNET_GROUP_PUBLIC_KEY};
    use crate::ext4::CShakeRng;
    use sha2::{Digest, Sha256};
    use std::ops::Add;

    const BLS_X: u64 = 0xd201_0000_0001_0000;
    const BLS_X_IS_NEGATIVE: bool = true;

    const MODULUS: [u64; 6] = [
        0xb9fe_ffff_ffff_aaab,
        0x1eab_fffe_b153_ffff,
        0x6730_d2a0_f6b0_f624,
        0x6477_4b84_f385_12bf,
        0x4b1b_a7b6_434b_acd7,
        0x1a01_11ea_397f_e69a,
    ];
    const INV: u64 = 0x89f3_fffc_fffc_fffd;

    #[inline(always)]
    const fn adc(a: u64, b: u64, carry: u64) -> (u64, u64) {
        let ret = (a as u128) + (b as u128) + (carry as u128);
        (ret as u64, (ret >> 64) as u64)
    }

    #[inline(always)]
    const fn sbb(a: u64, b: u64, borrow: u64) -> (u64, u64) {
        let ret = (a as u128).wrapping_sub((b as u128) + ((borrow >> 63) as u128));
        (ret as u64, (ret >> 64) as u64)
    }

    #[inline(always)]
    const fn mac(a: u64, b: u64, c: u64, carry: u64) -> (u64, u64) {
        let ret = (a as u128) + ((b as u128) * (c as u128)) + (carry as u128);
        (ret as u64, (ret >> 64) as u64)
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct Fp(pub [u64; 6]);

    const R: Fp = Fp([
        0x7609_0000_0002_fffd,
        0xebf4_000b_c40c_0002,
        0x5f48_9857_53c7_58ba,
        0x77ce_5853_7052_5745,
        0x5c07_1a97_a256_ec6d,
        0x15f6_5ec3_fa80_e493,
    ]);

    const R2: Fp = Fp([
        0xf4df_1f34_1c34_1746,
        0x0a76_e6a6_09d1_04f1,
        0x8de5_476c_4c95_b6d5,
        0x67eb_88a9_939d_83c0,
        0x9a79_3e85_b519_952d,
        0x1198_8fe5_92ca_e3aa,
    ]);

    impl Fp {
        pub const ZERO: Self = Self([0; 6]);
        pub const ONE: Self = R;

        #[inline(always)]
        pub const fn from_raw(v: [u64; 6]) -> Self {
            Self(v)
        }

        #[inline(always)]
        pub const fn is_zero(&self) -> bool {
            (self.0[0] | self.0[1] | self.0[2] | self.0[3] | self.0[4] | self.0[5]) == 0
        }

        #[inline]
        const fn subtract_p(&self) -> Self {
            let (r0, borrow) = sbb(self.0[0], MODULUS[0], 0);
            let (r1, borrow) = sbb(self.0[1], MODULUS[1], borrow);
            let (r2, borrow) = sbb(self.0[2], MODULUS[2], borrow);
            let (r3, borrow) = sbb(self.0[3], MODULUS[3], borrow);
            let (r4, borrow) = sbb(self.0[4], MODULUS[4], borrow);
            let (r5, borrow) = sbb(self.0[5], MODULUS[5], borrow);
            Self([
                (self.0[0] & borrow) | (r0 & !borrow),
                (self.0[1] & borrow) | (r1 & !borrow),
                (self.0[2] & borrow) | (r2 & !borrow),
                (self.0[3] & borrow) | (r3 & !borrow),
                (self.0[4] & borrow) | (r4 & !borrow),
                (self.0[5] & borrow) | (r5 & !borrow),
            ])
        }

        #[inline]
        pub const fn add(self, rhs: Self) -> Self {
            let (d0, carry) = adc(self.0[0], rhs.0[0], 0);
            let (d1, carry) = adc(self.0[1], rhs.0[1], carry);
            let (d2, carry) = adc(self.0[2], rhs.0[2], carry);
            let (d3, carry) = adc(self.0[3], rhs.0[3], carry);
            let (d4, carry) = adc(self.0[4], rhs.0[4], carry);
            let (d5, _) = adc(self.0[5], rhs.0[5], carry);
            Self([d0, d1, d2, d3, d4, d5]).subtract_p()
        }

        #[inline]
        pub const fn neg(self) -> Self {
            let (d0, borrow) = sbb(MODULUS[0], self.0[0], 0);
            let (d1, borrow) = sbb(MODULUS[1], self.0[1], borrow);
            let (d2, borrow) = sbb(MODULUS[2], self.0[2], borrow);
            let (d3, borrow) = sbb(MODULUS[3], self.0[3], borrow);
            let (d4, borrow) = sbb(MODULUS[4], self.0[4], borrow);
            let (d5, _) = sbb(MODULUS[5], self.0[5], borrow);
            let mask = (self.is_zero() as u64).wrapping_sub(1);
            Self([
                d0 & mask,
                d1 & mask,
                d2 & mask,
                d3 & mask,
                d4 & mask,
                d5 & mask,
            ])
        }

        #[inline]
        pub const fn sub(self, rhs: Self) -> Self {
            self.add(rhs.neg())
        }

        #[inline(always)]
        const fn montgomery_reduce(t: [u64; 12]) -> Self {
            let [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11] = t;
            let k = t0.wrapping_mul(INV);
            let (_, carry) = mac(t0, k, MODULUS[0], 0);
            let (r1, carry) = mac(t1, k, MODULUS[1], carry);
            let (r2, carry) = mac(t2, k, MODULUS[2], carry);
            let (r3, carry) = mac(t3, k, MODULUS[3], carry);
            let (r4, carry) = mac(t4, k, MODULUS[4], carry);
            let (r5, carry) = mac(t5, k, MODULUS[5], carry);
            let (r6, r7) = adc(t6, 0, carry);

            let k = r1.wrapping_mul(INV);
            let (_, carry) = mac(r1, k, MODULUS[0], 0);
            let (r2, carry) = mac(r2, k, MODULUS[1], carry);
            let (r3, carry) = mac(r3, k, MODULUS[2], carry);
            let (r4, carry) = mac(r4, k, MODULUS[3], carry);
            let (r5, carry) = mac(r5, k, MODULUS[4], carry);
            let (r6, carry) = mac(r6, k, MODULUS[5], carry);
            let (r7, r8) = adc(t7, r7, carry);

            let k = r2.wrapping_mul(INV);
            let (_, carry) = mac(r2, k, MODULUS[0], 0);
            let (r3, carry) = mac(r3, k, MODULUS[1], carry);
            let (r4, carry) = mac(r4, k, MODULUS[2], carry);
            let (r5, carry) = mac(r5, k, MODULUS[3], carry);
            let (r6, carry) = mac(r6, k, MODULUS[4], carry);
            let (r7, carry) = mac(r7, k, MODULUS[5], carry);
            let (r8, r9) = adc(t8, r8, carry);

            let k = r3.wrapping_mul(INV);
            let (_, carry) = mac(r3, k, MODULUS[0], 0);
            let (r4, carry) = mac(r4, k, MODULUS[1], carry);
            let (r5, carry) = mac(r5, k, MODULUS[2], carry);
            let (r6, carry) = mac(r6, k, MODULUS[3], carry);
            let (r7, carry) = mac(r7, k, MODULUS[4], carry);
            let (r8, carry) = mac(r8, k, MODULUS[5], carry);
            let (r9, r10) = adc(t9, r9, carry);

            let k = r4.wrapping_mul(INV);
            let (_, carry) = mac(r4, k, MODULUS[0], 0);
            let (r5, carry) = mac(r5, k, MODULUS[1], carry);
            let (r6, carry) = mac(r6, k, MODULUS[2], carry);
            let (r7, carry) = mac(r7, k, MODULUS[3], carry);
            let (r8, carry) = mac(r8, k, MODULUS[4], carry);
            let (r9, carry) = mac(r9, k, MODULUS[5], carry);
            let (r10, r11) = adc(t10, r10, carry);

            let k = r5.wrapping_mul(INV);
            let (_, carry) = mac(r5, k, MODULUS[0], 0);
            let (r6, carry) = mac(r6, k, MODULUS[1], carry);
            let (r7, carry) = mac(r7, k, MODULUS[2], carry);
            let (r8, carry) = mac(r8, k, MODULUS[3], carry);
            let (r9, carry) = mac(r9, k, MODULUS[4], carry);
            let (r10, carry) = mac(r10, k, MODULUS[5], carry);
            let (r11, _) = adc(t11, r11, carry);

            Self([r6, r7, r8, r9, r10, r11]).subtract_p()
        }

        #[inline]
        pub const fn mul(self, rhs: Self) -> Self {
            let (t0, carry) = mac(0, self.0[0], rhs.0[0], 0);
            let (t1, carry) = mac(0, self.0[0], rhs.0[1], carry);
            let (t2, carry) = mac(0, self.0[0], rhs.0[2], carry);
            let (t3, carry) = mac(0, self.0[0], rhs.0[3], carry);
            let (t4, carry) = mac(0, self.0[0], rhs.0[4], carry);
            let (t5, t6) = mac(0, self.0[0], rhs.0[5], carry);

            let (t1, carry) = mac(t1, self.0[1], rhs.0[0], 0);
            let (t2, carry) = mac(t2, self.0[1], rhs.0[1], carry);
            let (t3, carry) = mac(t3, self.0[1], rhs.0[2], carry);
            let (t4, carry) = mac(t4, self.0[1], rhs.0[3], carry);
            let (t5, carry) = mac(t5, self.0[1], rhs.0[4], carry);
            let (t6, t7) = mac(t6, self.0[1], rhs.0[5], carry);

            let (t2, carry) = mac(t2, self.0[2], rhs.0[0], 0);
            let (t3, carry) = mac(t3, self.0[2], rhs.0[1], carry);
            let (t4, carry) = mac(t4, self.0[2], rhs.0[2], carry);
            let (t5, carry) = mac(t5, self.0[2], rhs.0[3], carry);
            let (t6, carry) = mac(t6, self.0[2], rhs.0[4], carry);
            let (t7, t8) = mac(t7, self.0[2], rhs.0[5], carry);

            let (t3, carry) = mac(t3, self.0[3], rhs.0[0], 0);
            let (t4, carry) = mac(t4, self.0[3], rhs.0[1], carry);
            let (t5, carry) = mac(t5, self.0[3], rhs.0[2], carry);
            let (t6, carry) = mac(t6, self.0[3], rhs.0[3], carry);
            let (t7, carry) = mac(t7, self.0[3], rhs.0[4], carry);
            let (t8, t9) = mac(t8, self.0[3], rhs.0[5], carry);

            let (t4, carry) = mac(t4, self.0[4], rhs.0[0], 0);
            let (t5, carry) = mac(t5, self.0[4], rhs.0[1], carry);
            let (t6, carry) = mac(t6, self.0[4], rhs.0[2], carry);
            let (t7, carry) = mac(t7, self.0[4], rhs.0[3], carry);
            let (t8, carry) = mac(t8, self.0[4], rhs.0[4], carry);
            let (t9, t10) = mac(t9, self.0[4], rhs.0[5], carry);

            let (t5, carry) = mac(t5, self.0[5], rhs.0[0], 0);
            let (t6, carry) = mac(t6, self.0[5], rhs.0[1], carry);
            let (t7, carry) = mac(t7, self.0[5], rhs.0[2], carry);
            let (t8, carry) = mac(t8, self.0[5], rhs.0[3], carry);
            let (t9, carry) = mac(t9, self.0[5], rhs.0[4], carry);
            let (t10, t11) = mac(t10, self.0[5], rhs.0[5], carry);

            Self::montgomery_reduce([t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11])
        }

        #[inline]
        pub const fn square(self) -> Self {
            self.mul(self)
        }

        pub fn pow_vartime(self, by: &[u64; 6]) -> Self {
            let mut res = Self::ONE;
            for e in by.iter().rev() {
                for i in (0..64).rev() {
                    res = res.square();
                    if ((*e >> i) & 1) == 1 {
                        res = res.mul(self);
                    }
                }
            }
            res
        }

        pub fn invert(self) -> Option<Self> {
            if self.is_zero() {
                return None;
            }
            Some(self.pow_vartime(&[
                0xb9fe_ffff_ffff_aaa9,
                0x1eab_fffe_b153_ffff,
                0x6730_d2a0_f6b0_f624,
                0x6477_4b84_f385_12bf,
                0x4b1b_a7b6_434b_acd7,
                0x1a01_11ea_397f_e69a,
            ]))
        }

        pub fn sqrt(self) -> Option<Self> {
            let s = self.pow_vartime(&[
                0xee7f_bfff_ffff_eaab,
                0x07aa_ffff_ac54_ffff,
                0xd9cc_34a8_3dac_3d89,
                0xd91d_d2e1_3ce1_44af,
                0x92c6_e9ed_90d2_eb35,
                0x0680_447a_8e5f_f9a6,
            ]);
            if s.square() == self {
                Some(s)
            } else {
                None
            }
        }

        pub fn from_bytes_be(bytes: &[u8; 48]) -> Option<Self> {
            let mut tmp = [0u64; 6];
            for (i, slot) in tmp.iter_mut().enumerate() {
                let st = (5 - i) * 8;
                *slot = u64::from_be_bytes(bytes[st..st + 8].try_into().unwrap());
            }
            let (_, borrow) = sbb(tmp[0], MODULUS[0], 0);
            let (_, borrow) = sbb(tmp[1], MODULUS[1], borrow);
            let (_, borrow) = sbb(tmp[2], MODULUS[2], borrow);
            let (_, borrow) = sbb(tmp[3], MODULUS[3], borrow);
            let (_, borrow) = sbb(tmp[4], MODULUS[4], borrow);
            let (_, borrow) = sbb(tmp[5], MODULUS[5], borrow);
            if (borrow & 1) == 0 {
                return None;
            }
            Some(Self(tmp).mul(R2))
        }

        pub fn to_bytes_be(self) -> [u8; 48] {
            let tmp = Self::montgomery_reduce([
                self.0[0], self.0[1], self.0[2], self.0[3], self.0[4], self.0[5], 0, 0, 0, 0, 0, 0,
            ]);
            let mut res = [0u8; 48];
            for i in 0..6 {
                let st = (5 - i) * 8;
                res[st..st + 8].copy_from_slice(&tmp.0[i].to_be_bytes());
            }
            res
        }

        pub fn lexicographically_largest(self) -> bool {
            let tmp = Self::montgomery_reduce([
                self.0[0], self.0[1], self.0[2], self.0[3], self.0[4], self.0[5], 0, 0, 0, 0, 0, 0,
            ]);
            let (_, borrow) = sbb(tmp.0[0], 0xdcff_7fff_ffff_d556, 0);
            let (_, borrow) = sbb(tmp.0[1], 0x0f55_ffff_58a9_ffff, borrow);
            let (_, borrow) = sbb(tmp.0[2], 0xb398_6950_7b58_7b12, borrow);
            let (_, borrow) = sbb(tmp.0[3], 0xb23b_a5c2_79c2_895f, borrow);
            let (_, borrow) = sbb(tmp.0[4], 0x258d_d3db_21a5_d66b, borrow);
            let (_, borrow) = sbb(tmp.0[5], 0x0d00_88f5_1cbf_f34d, borrow);
            (borrow & 1) == 0
        }

        pub fn sgn0(self) -> bool {
            let tmp = Self::montgomery_reduce([
                self.0[0], self.0[1], self.0[2], self.0[3], self.0[4], self.0[5], 0, 0, 0, 0, 0, 0,
            ]);
            (tmp.0[0] & 1) == 1
        }

        pub fn pow_pm3div4(self) -> Self {
            self.pow_vartime(&[
                0xee7f_bfff_ffff_eaaa,
                0x07aa_ffff_ac54_ffff,
                0xd9cc_34a8_3dac_3d89,
                0xd91d_d2e1_3ce1_44af,
                0x92c6_e9ed_90d2_eb35,
                0x0680_447a_8e5f_f9a6,
            ])
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct Fp2 {
        pub c0: Fp,
        pub c1: Fp,
    }

    impl Fp2 {
        pub const ZERO: Self = Self {
            c0: Fp::ZERO,
            c1: Fp::ZERO,
        };
        pub const ONE: Self = Self {
            c0: Fp::ONE,
            c1: Fp::ZERO,
        };

        #[inline]
        pub const fn is_zero(&self) -> bool {
            self.c0.is_zero() && self.c1.is_zero()
        }

        #[inline]
        pub const fn add(self, rhs: Self) -> Self {
            Self {
                c0: self.c0.add(rhs.c0),
                c1: self.c1.add(rhs.c1),
            }
        }

        #[inline]
        pub const fn sub(self, rhs: Self) -> Self {
            Self {
                c0: self.c0.sub(rhs.c0),
                c1: self.c1.sub(rhs.c1),
            }
        }

        #[inline]
        pub const fn neg(self) -> Self {
            Self {
                c0: self.c0.neg(),
                c1: self.c1.neg(),
            }
        }

        #[inline]
        pub const fn conjugate(self) -> Self {
            Self {
                c0: self.c0,
                c1: self.c1.neg(),
            }
        }

        #[inline]
        pub const fn frobenius_map(self) -> Self {
            self.conjugate()
        }

        #[inline]
        pub const fn mul_by_nonresidue(self) -> Self {
            Self {
                c0: self.c0.sub(self.c1),
                c1: self.c0.add(self.c1),
            }
        }

        #[inline]
        pub const fn mul(self, rhs: Self) -> Self {
            let aa = self.c0.mul(rhs.c0);
            let bb = self.c1.mul(rhs.c1);
            let o = self.c0.add(self.c1).mul(rhs.c0.add(rhs.c1));
            Self {
                c0: aa.sub(bb),
                c1: o.sub(aa).sub(bb),
            }
        }

        #[inline]
        pub const fn square(self) -> Self {
            let a = self.c0.add(self.c1);
            let b = self.c0.sub(self.c1);
            let c = self.c0.add(self.c0);
            Self {
                c0: a.mul(b),
                c1: c.mul(self.c1),
            }
        }

        pub fn invert(self) -> Option<Self> {
            let t = self.c0.square().add(self.c1.square()).invert()?;
            Some(Self {
                c0: self.c0.mul(t),
                c1: self.c1.mul(t.neg()),
            })
        }

        pub fn pow_vartime(self, by: &[u64; 6]) -> Self {
            let mut res = Self::ONE;
            for e in by.iter().rev() {
                for i in (0..64).rev() {
                    res = res.square();
                    if ((*e >> i) & 1) == 1 {
                        res = res.mul(self);
                    }
                }
            }
            res
        }

        pub fn lexicographically_largest(self) -> bool {
            self.c1.lexicographically_largest()
                || (self.c1.is_zero() && self.c0.lexicographically_largest())
        }

        pub fn sqrt(self) -> Option<Self> {
            if self.is_zero() {
                return Some(Self::ZERO);
            }
            let a1 = self.pow_vartime(&[
                0xee7f_bfff_ffff_eaaa,
                0x07aa_ffff_ac54_ffff,
                0xd9cc_34a8_3dac_3d89,
                0xd91d_d2e1_3ce1_44af,
                0x92c6_e9ed_90d2_eb35,
                0x0680_447a_8e5f_f9a6,
            ]);
            let alpha = a1.square().mul(self);
            let x0 = a1.mul(self);
            let cand = if alpha == Self::ONE.neg() {
                Self {
                    c0: x0.c1.neg(),
                    c1: x0.c0,
                }
            } else {
                alpha
                    .add(Self::ONE)
                    .pow_vartime(&[
                        0xdcff_7fff_ffff_d555,
                        0x0f55_ffff_58a9_ffff,
                        0xb398_6950_7b58_7b12,
                        0xb23b_a5c2_79c2_895f,
                        0x258d_d3db_21a5_d66b,
                        0x0d00_88f5_1cbf_f34d,
                    ])
                    .mul(x0)
            };
            if cand.square() == self {
                Some(cand)
            } else {
                None
            }
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct Fp6 {
        pub c0: Fp2,
        pub c1: Fp2,
        pub c2: Fp2,
    }

    impl Fp6 {
        pub const ZERO: Self = Self {
            c0: Fp2::ZERO,
            c1: Fp2::ZERO,
            c2: Fp2::ZERO,
        };
        pub const ONE: Self = Self {
            c0: Fp2::ONE,
            c1: Fp2::ZERO,
            c2: Fp2::ZERO,
        };

        #[inline]
        pub const fn add(self, rhs: Self) -> Self {
            Self {
                c0: self.c0.add(rhs.c0),
                c1: self.c1.add(rhs.c1),
                c2: self.c2.add(rhs.c2),
            }
        }

        #[inline]
        pub const fn sub(self, rhs: Self) -> Self {
            Self {
                c0: self.c0.sub(rhs.c0),
                c1: self.c1.sub(rhs.c1),
                c2: self.c2.sub(rhs.c2),
            }
        }

        #[inline]
        pub const fn neg(self) -> Self {
            Self {
                c0: self.c0.neg(),
                c1: self.c1.neg(),
                c2: self.c2.neg(),
            }
        }

        #[inline]
        pub const fn mul_by_nonresidue(self) -> Self {
            Self {
                c0: self.c2.mul_by_nonresidue(),
                c1: self.c0,
                c2: self.c1,
            }
        }

        #[inline]
        pub const fn mul_by_1(self, c1: Fp2) -> Self {
            Self {
                c0: self.c2.mul(c1).mul_by_nonresidue(),
                c1: self.c0.mul(c1),
                c2: self.c1.mul(c1),
            }
        }

        #[inline]
        pub const fn mul_by_01(self, c0: Fp2, c1: Fp2) -> Self {
            let a_a = self.c0.mul(c0);
            let b_b = self.c1.mul(c1);
            let t1 = self.c2.mul(c1).mul_by_nonresidue().add(a_a);
            let t2 = c0.add(c1).mul(self.c0.add(self.c1)).sub(a_a).sub(b_b);
            let t3 = self.c2.mul(c0).add(b_b);
            Self {
                c0: t1,
                c1: t2,
                c2: t3,
            }
        }

        #[inline]
        pub const fn mul(self, rhs: Self) -> Self {
            let v0 = self.c0.mul(rhs.c0);
            let v1 = self.c1.mul(rhs.c1);
            let v2 = self.c2.mul(rhs.c2);
            let c0 = self
                .c1
                .add(self.c2)
                .mul(rhs.c1.add(rhs.c2))
                .sub(v1)
                .sub(v2)
                .mul_by_nonresidue()
                .add(v0);
            let c1 = self
                .c0
                .add(self.c1)
                .mul(rhs.c0.add(rhs.c1))
                .sub(v0)
                .sub(v1)
                .add(v2.mul_by_nonresidue());
            let c2 = self
                .c0
                .add(self.c2)
                .mul(rhs.c0.add(rhs.c2))
                .sub(v0)
                .add(v1)
                .sub(v2);
            Self { c0, c1, c2 }
        }

        #[inline]
        pub const fn square(self) -> Self {
            let s0 = self.c0.square();
            let ab = self.c0.mul(self.c1);
            let s1 = ab.add(ab);
            let s2 = self.c0.sub(self.c1).add(self.c2).square();
            let bc = self.c1.mul(self.c2);
            let s3 = bc.add(bc);
            let s4 = self.c2.square();
            Self {
                c0: s3.mul_by_nonresidue().add(s0),
                c1: s4.mul_by_nonresidue().add(s1),
                c2: s1.add(s2).add(s3).sub(s0).sub(s4),
            }
        }

        pub fn frobenius_map(self) -> Self {
            let c0 = self.c0.frobenius_map();
            let c1 = self.c1.frobenius_map().mul(Fp2 {
                c0: Fp::ZERO,
                c1: Fp::from_raw([
                    0xcd03_c9e4_8671_f071,
                    0x5dab_2246_1fcd_a5d2,
                    0x5870_42af_d385_1b95,
                    0x8eb6_0ebe_01ba_cb9e,
                    0x03f9_7d6e_83d0_50d2,
                    0x18f0_2065_5463_8741,
                ]),
            });
            let c2 = self.c2.frobenius_map().mul(Fp2 {
                c0: Fp::from_raw([
                    0x890d_c9e4_8675_45c3,
                    0x2af3_2253_3285_a5d5,
                    0x5088_0866_309b_7e2c,
                    0xa20d_1b8c_7e88_1024,
                    0x14e4_f04f_e2db_9068,
                    0x14e5_6d3f_1564_853a,
                ]),
                c1: Fp::ZERO,
            });
            Self { c0, c1, c2 }
        }

        pub fn invert(self) -> Option<Self> {
            let c0 = self
                .c0
                .square()
                .sub(self.c1.mul(self.c2).mul_by_nonresidue());
            let c1 = self
                .c2
                .square()
                .mul_by_nonresidue()
                .sub(self.c0.mul(self.c1));
            let c2 = self.c1.square().sub(self.c0.mul(self.c2));
            let tmp = self
                .c1
                .mul(c2)
                .add(self.c2.mul(c1))
                .mul_by_nonresidue()
                .add(self.c0.mul(c0))
                .invert()?;
            Some(Self {
                c0: tmp.mul(c0),
                c1: tmp.mul(c1),
                c2: tmp.mul(c2),
            })
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct Fp12 {
        pub c0: Fp6,
        pub c1: Fp6,
    }

    impl Fp12 {
        pub const ONE: Self = Self {
            c0: Fp6::ONE,
            c1: Fp6::ZERO,
        };

        #[inline]
        pub const fn conjugate(self) -> Self {
            Self {
                c0: self.c0,
                c1: self.c1.neg(),
            }
        }

        #[inline]
        pub const fn mul(self, other: Self) -> Self {
            let aa = self.c0.mul(other.c0);
            let bb = self.c1.mul(other.c1);
            let o = other.c0.add(other.c1);
            let c1 = self.c1.add(self.c0).mul(o).sub(aa).sub(bb);
            let c0 = bb.mul_by_nonresidue().add(aa);
            Self { c0, c1 }
        }

        #[inline]
        pub const fn square(self) -> Self {
            let ab = self.c0.mul(self.c1);
            let c0c1 = self.c0.add(self.c1);
            let c0 = self
                .c1
                .mul_by_nonresidue()
                .add(self.c0)
                .mul(c0c1)
                .sub(ab)
                .sub(ab.mul_by_nonresidue());
            let c1 = ab.add(ab);
            Self { c0, c1 }
        }

        #[inline]
        pub const fn mul_by_014(self, c0: Fp2, c1: Fp2, c4: Fp2) -> Self {
            let aa = self.c0.mul_by_01(c0, c1);
            let bb = self.c1.mul_by_1(c4);
            let o = c1.add(c4);
            let c1_out = self.c1.add(self.c0).mul_by_01(c0, o).sub(aa).sub(bb);
            let c0_out = bb.mul_by_nonresidue().add(aa);
            Self {
                c0: c0_out,
                c1: c1_out,
            }
        }

        pub fn frobenius_map(self) -> Self {
            let c0 = self.c0.frobenius_map();
            let f_coeff = Fp2 {
                c0: Fp::from_raw([
                    0x0708_9552_b319_d465,
                    0xc669_5f92_b50a_8313,
                    0x97e8_3ccc_d117_228f,
                    0xa35b_aeca_b2dc_29ee,
                    0x1ce3_93ea_5daa_ce4d,
                    0x08f2_220f_b0fb_66eb,
                ]),
                c1: Fp::from_raw([
                    0xb2f6_6aad_4ce5_d646,
                    0x5842_a06b_fc49_7cec,
                    0xcf48_95d4_2599_d394,
                    0xc11b_9cba_40a8_e8d0,
                    0x2e38_13cb_e5a0_de89,
                    0x110e_efda_8884_7faf,
                ]),
            };
            let c1_f = self.c1.frobenius_map();
            Self {
                c0,
                c1: Fp6 {
                    c0: c1_f.c0.mul(f_coeff),
                    c1: c1_f.c1.mul(f_coeff),
                    c2: c1_f.c2.mul(f_coeff),
                },
            }
        }

        pub fn invert(self) -> Option<Self> {
            let t = self
                .c0
                .square()
                .sub(self.c1.square().mul_by_nonresidue())
                .invert()?;
            Some(Self {
                c0: self.c0.mul(t),
                c1: self.c1.mul(t.neg()),
            })
        }

        pub fn final_exponentiation(self) -> Option<Self> {
            fn fp4_square(a: Fp2, b: Fp2) -> (Fp2, Fp2) {
                let t0 = a.square();
                let t1 = b.square();
                let c0 = t1.mul_by_nonresidue().add(t0);
                let c1 = a.add(b).square().sub(t0).sub(t1);
                (c0, c1)
            }
            fn cyclotomic_square(f: Fp12) -> Fp12 {
                let mut z0 = f.c0.c0;
                let mut z4 = f.c0.c1;
                let mut z3 = f.c0.c2;
                let mut z2 = f.c1.c0;
                let mut z1 = f.c1.c1;
                let mut z5 = f.c1.c2;
                let (t0, t1) = fp4_square(z0, z1);
                z0 = t0.sub(z0);
                z0 = z0.add(z0).add(t0);
                z1 = t1.add(z1);
                z1 = z1.add(z1).add(t1);
                let (t0_b, t1_b) = fp4_square(z2, z3);
                let (t2, t3) = fp4_square(z4, z5);
                z4 = t0_b.sub(z4);
                z4 = z4.add(z4).add(t0_b);
                z5 = t1_b.add(z5);
                z5 = z5.add(z5).add(t1_b);
                let t0_c = t3.mul_by_nonresidue();
                z2 = t0_c.add(z2);
                z2 = z2.add(z2).add(t0_c);
                z3 = t2.sub(z3);
                z3 = z3.add(z3).add(t2);
                Fp12 {
                    c0: Fp6 {
                        c0: z0,
                        c1: z4,
                        c2: z3,
                    },
                    c1: Fp6 {
                        c0: z2,
                        c1: z1,
                        c2: z5,
                    },
                }
            }
            fn cyclotomic_exp(f: Fp12) -> Fp12 {
                let mut tmp = Fp12::ONE;
                let mut found_one = false;
                for b in (0..64).rev() {
                    let bit = ((BLS_X >> b) & 1) == 1;
                    if found_one {
                        tmp = cyclotomic_square(tmp);
                    } else {
                        found_one = bit;
                    }
                    if bit {
                        tmp = tmp.mul(f);
                    }
                }
                tmp.conjugate()
            }

            let mut t0 = self
                .frobenius_map()
                .frobenius_map()
                .frobenius_map()
                .frobenius_map()
                .frobenius_map()
                .frobenius_map();
            let mut t1 = self.invert()?;
            let mut t2 = t0.mul(t1);
            t1 = t2;
            t2 = t2.frobenius_map().frobenius_map().mul(t1);
            t1 = cyclotomic_square(t2).conjugate();
            let mut t3 = cyclotomic_exp(t2);
            let mut t4 = cyclotomic_square(t3);
            let mut t5 = t1.mul(t3);
            t1 = cyclotomic_exp(t5);
            t0 = cyclotomic_exp(t1);
            let mut t6 = cyclotomic_exp(t0).mul(t4);
            t4 = cyclotomic_exp(t6);
            t5 = t5.conjugate();
            t4 = t4.mul(t5.mul(t2));
            t5 = t2.conjugate();
            t1 = t1.mul(t2).frobenius_map().frobenius_map().frobenius_map();
            t6 = t6.mul(t5).frobenius_map();
            t3 = t3.mul(t0).frobenius_map().frobenius_map().mul(t1).mul(t6);
            Some(t3.mul(t4))
        }
    }

    const fn b_g1() -> Fp {
        let two = Fp::ONE.add(Fp::ONE);
        two.add(two)
    }

    const fn b_g2() -> Fp2 {
        let four = b_g1();
        Fp2 { c0: four, c1: four }
    }

    const BETA_G1: Fp = Fp::from_raw([
        0x30f1_361b_798a_64e8,
        0xf3b8_ddab_7ece_5a2a,
        0x16a8_ca3a_c615_77f7,
        0xc26a_2ff8_74fd_029b,
        0x3636_b766_6070_1c6e,
        0x051b_a4ab_241b_6160,
    ]);

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct G1Affine {
        pub x: Fp,
        pub y: Fp,
        pub infinity: bool,
    }

    #[derive(Clone, Copy, Debug)]
    pub struct G1Projective {
        pub x: Fp,
        pub y: Fp,
        pub z: Fp,
    }

    impl G1Projective {
        pub const IDENTITY: Self = Self {
            x: Fp::ZERO,
            y: Fp::ONE,
            z: Fp::ZERO,
        };

        #[inline]
        pub const fn is_identity(&self) -> bool {
            self.z.is_zero()
        }

        #[inline]
        pub const fn neg(self) -> Self {
            Self {
                x: self.x,
                y: self.y.neg(),
                z: self.z,
            }
        }

        pub fn double(self) -> Self {
            if self.is_identity() {
                return Self::IDENTITY;
            }
            let mul_3b = |a: Fp| -> Fp {
                let a2 = a.add(a);
                let a4 = a2.add(a2);
                a4.add(a4).add(a4)
            };
            let t0 = self.y.square();
            let z3 = t0.add(t0);
            let z3 = z3.add(z3);
            let z3 = z3.add(z3);
            let t1 = self.y.mul(self.z);
            let t2 = mul_3b(self.z.square());
            let x3 = t2.mul(z3);
            let y3 = t0.add(t2);
            let z3 = t1.mul(z3);
            let t1 = t2.add(t2);
            let t2 = t1.add(t2);
            let t0 = t0.sub(t2);
            let y3 = t0.mul(y3).add(x3);
            let t1 = self.x.mul(self.y);
            let x3 = t0.mul(t1);
            let x3 = x3.add(x3);
            Self {
                x: x3,
                y: y3,
                z: z3,
            }
        }

        pub fn mul_by_x(self) -> Self {
            let mut xself = Self::IDENTITY;
            let mut x = BLS_X >> 1;
            let mut tmp = self;
            while x != 0 {
                tmp = tmp.double();
                if (x & 1) == 1 {
                    xself = xself.add(tmp);
                }
                x >>= 1;
            }
            if BLS_X_IS_NEGATIVE {
                xself = xself.neg();
            }
            xself
        }

        pub fn clear_cofactor(self) -> Self {
            self.add(self.mul_by_x().neg())
        }

        pub fn mul_bytes_be(self, scalar_be: &[u8; 32]) -> Self {
            let mut acc = Self::IDENTITY;
            for &byte in scalar_be {
                for i in (0..8).rev() {
                    acc = acc.double();
                    if ((byte >> i) & 1) == 1 {
                        acc = acc.add(self);
                    }
                }
            }
            acc
        }

        pub fn to_affine(self) -> G1Affine {
            match self.z.invert() {
                None => G1Affine {
                    x: Fp::ZERO,
                    y: Fp::ONE,
                    infinity: true,
                },
                Some(zinv) => G1Affine {
                    x: self.x.mul(zinv),
                    y: self.y.mul(zinv),
                    infinity: false,
                },
            }
        }

        pub fn eq_proj(self, other: Self) -> bool {
            if self.is_identity() && other.is_identity() {
                return true;
            }
            if self.is_identity() || other.is_identity() {
                return false;
            }
            self.x.mul(other.z) == other.x.mul(self.z) && self.y.mul(other.z) == other.y.mul(self.z)
        }
    }

    impl Add for G1Projective {
        type Output = Self;

        fn add(self, rhs: Self) -> Self {
            let mul_3b = |a: Fp| -> Fp {
                let a2 = a.add(a);
                let a4 = a2.add(a2);
                a4.add(a4).add(a4)
            };
            let t0 = self.x.mul(rhs.x);
            let t1 = self.y.mul(rhs.y);
            let t2 = self.z.mul(rhs.z);
            let t3 = self.x.add(self.y).mul(rhs.x.add(rhs.y)).sub(t0.add(t1));
            let t4 = self.y.add(self.z).mul(rhs.y.add(rhs.z)).sub(t1.add(t2));
            let y3 = self.x.add(self.z).mul(rhs.x.add(rhs.z)).sub(t0.add(t2));
            let x3 = t0.add(t0);
            let t0 = x3.add(t0);
            let t2 = mul_3b(t2);
            let z3 = t1.add(t2);
            let t1 = t1.sub(t2);
            let y3 = mul_3b(y3);
            let x3 = t3.mul(t1).sub(t4.mul(y3));
            let y3 = t1.mul(z3).add(y3.mul(t0));
            let z3 = z3.mul(t4).add(t0.mul(t3));
            Self {
                x: x3,
                y: y3,
                z: z3,
            }
        }
    }

    impl G1Affine {
        pub fn to_proj(self) -> G1Projective {
            if self.infinity {
                G1Projective::IDENTITY
            } else {
                G1Projective {
                    x: self.x,
                    y: self.y,
                    z: Fp::ONE,
                }
            }
        }

        pub fn is_torsion_free(self) -> bool {
            if self.infinity {
                return true;
            }
            let lhs = self.to_proj().mul_by_x().mul_by_x().neg();
            let rhs = G1Projective {
                x: self.x.mul(BETA_G1),
                y: self.y,
                z: Fp::ONE,
            };
            lhs.eq_proj(rhs)
        }

        pub fn from_compressed(bytes: &[u8; 48]) -> Option<Self> {
            let comp = (bytes[0] >> 7) & 1 == 1;
            let inf = (bytes[0] >> 6) & 1 == 1;
            let sort = (bytes[0] >> 5) & 1 == 1;
            if !comp {
                return None;
            }
            let mut tmp = *bytes;
            tmp[0] &= 0b0001_1111;
            let x = Fp::from_bytes_be(&tmp)?;
            if inf {
                if !sort && x.is_zero() {
                    return Some(Self {
                        x: Fp::ZERO,
                        y: Fp::ONE,
                        infinity: true,
                    });
                }
                return None;
            }
            let mut y = x.square().mul(x).add(b_g1()).sqrt()?;
            if y.lexicographically_largest() != sort {
                y = y.neg();
            }
            let pt = Self {
                x,
                y,
                infinity: false,
            };
            if pt.is_torsion_free() {
                Some(pt)
            } else {
                None
            }
        }

        pub fn to_compressed(self) -> [u8; 48] {
            if self.infinity {
                let mut res = [0u8; 48];
                res[0] = 0b1100_0000;
                return res;
            }
            let mut res = self.x.to_bytes_be();
            res[0] |= 1u8 << 7;
            if self.y.lexicographically_largest() {
                res[0] |= 1u8 << 5;
            }
            res
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct G2Affine {
        pub x: Fp2,
        pub y: Fp2,
        pub infinity: bool,
    }

    #[derive(Clone, Copy, Debug)]
    pub struct G2Projective {
        pub x: Fp2,
        pub y: Fp2,
        pub z: Fp2,
    }

    impl G2Affine {
        pub const fn generator() -> Self {
            Self {
                x: Fp2 {
                    c0: Fp::from_raw([
                        0xf5f2_8fa2_0294_0a10,
                        0xb3f5_fb26_87b4_961a,
                        0xa1a8_93b5_3e2a_e580,
                        0x9894_999d_1a3c_aee9,
                        0x6f67_b763_1863_366b,
                        0x0581_9192_4350_bcd7,
                    ]),
                    c1: Fp::from_raw([
                        0xa5a9_c075_9e23_f606,
                        0xaaa0_c59d_bccd_60c3,
                        0x3bb1_7e18_e286_7806,
                        0x1b1a_b6cc_8541_b367,
                        0xc2b6_ed0e_f215_8547,
                        0x1192_2a09_7360_edf3,
                    ]),
                },
                y: Fp2 {
                    c0: Fp::from_raw([
                        0x4c73_0af8_6049_4c4a,
                        0x597c_fa1f_5e36_9c5a,
                        0xe7e6_856c_aa0a_635a,
                        0xbbef_b5e9_6e0d_495f,
                        0x07d3_a975_f0ef_25a2,
                        0x0083_fd8e_7e80_dae5,
                    ]),
                    c1: Fp::from_raw([
                        0xadc0_fc92_df64_b05d,
                        0x18aa_270a_2b14_61dc,
                        0x86ad_ac6a_3be4_eba0,
                        0x7949_5c4e_c93d_a33a,
                        0xe717_5850_a43c_caed,
                        0x0b2b_c2a1_63de_1bf2,
                    ]),
                },
                infinity: false,
            }
        }

        pub const fn neg(self) -> Self {
            Self {
                x: self.x,
                y: self.y.neg(),
                infinity: self.infinity,
            }
        }

        pub fn to_proj(self) -> G2Projective {
            if self.infinity {
                G2Projective::IDENTITY
            } else {
                G2Projective {
                    x: self.x,
                    y: self.y,
                    z: Fp2::ONE,
                }
            }
        }

        pub fn is_torsion_free(self) -> bool {
            if self.infinity {
                return true;
            }
            let p = self.to_proj();
            p.psi().eq_proj(p.mul_by_x())
        }

        pub fn from_compressed(bytes: &[u8; 96]) -> Option<Self> {
            let comp = (bytes[0] >> 7) & 1 == 1;
            let inf = (bytes[0] >> 6) & 1 == 1;
            let sort = (bytes[0] >> 5) & 1 == 1;
            if !comp {
                return None;
            }
            let mut b1 = [0u8; 48];
            let mut b0 = [0u8; 48];
            b1.copy_from_slice(&bytes[0..48]);
            b0.copy_from_slice(&bytes[48..96]);
            b1[0] &= 0b0001_1111;
            let xc1 = Fp::from_bytes_be(&b1)?;
            let xc0 = Fp::from_bytes_be(&b0)?;
            let x = Fp2 { c0: xc0, c1: xc1 };
            if inf {
                if !sort && x.is_zero() {
                    return Some(Self {
                        x: Fp2::ZERO,
                        y: Fp2::ONE,
                        infinity: true,
                    });
                }
                return None;
            }
            let mut y = x.square().mul(x).add(b_g2()).sqrt()?;
            if y.lexicographically_largest() != sort {
                y = y.neg();
            }
            let pt = Self {
                x,
                y,
                infinity: false,
            };
            if pt.is_torsion_free() {
                Some(pt)
            } else {
                None
            }
        }

        pub fn to_compressed(self) -> [u8; 96] {
            if self.infinity {
                let mut res = [0u8; 96];
                res[0] = 0b1100_0000;
                return res;
            }
            let mut res = [0u8; 96];
            res[0..48].copy_from_slice(&self.x.c1.to_bytes_be());
            res[48..96].copy_from_slice(&self.x.c0.to_bytes_be());
            res[0] |= 1u8 << 7;
            if self.y.lexicographically_largest() {
                res[0] |= 1u8 << 5;
            }
            res
        }
    }

    impl G2Projective {
        pub const IDENTITY: Self = Self {
            x: Fp2::ZERO,
            y: Fp2::ONE,
            z: Fp2::ZERO,
        };

        #[inline]
        pub const fn is_identity(&self) -> bool {
            self.z.is_zero()
        }

        #[inline]
        pub const fn neg(self) -> Self {
            Self {
                x: self.x,
                y: self.y.neg(),
                z: self.z,
            }
        }

        pub fn double(self) -> Self {
            if self.is_identity() {
                return Self::IDENTITY;
            }
            let b3 = {
                let b = b_g2();
                b.add(b).add(b)
            };
            let t0 = self.y.square();
            let z3 = t0.add(t0);
            let z3 = z3.add(z3);
            let z3 = z3.add(z3);
            let t1 = self.y.mul(self.z);
            let t2 = self.z.square().mul(b3);
            let x3 = t2.mul(z3);
            let y3 = t0.add(t2);
            let z3 = t1.mul(z3);
            let t1 = t2.add(t2);
            let t2 = t1.add(t2);
            let t0 = t0.sub(t2);
            let y3 = t0.mul(y3).add(x3);
            let t1 = self.x.mul(self.y);
            let x3 = t0.mul(t1);
            let x3 = x3.add(x3);
            Self {
                x: x3,
                y: y3,
                z: z3,
            }
        }

        pub fn mul_by_x(self) -> Self {
            let mut xself = Self::IDENTITY;
            let mut x = BLS_X >> 1;
            let mut acc = self;
            while x != 0 {
                acc = acc.double();
                if (x & 1) == 1 {
                    xself = xself.add(acc);
                }
                x >>= 1;
            }
            if BLS_X_IS_NEGATIVE {
                xself = xself.neg();
            }
            xself
        }

        pub fn psi(self) -> Self {
            let psi_x = Fp2 {
                c0: Fp::ZERO,
                c1: Fp::from_raw([
                    0x890d_c9e4_8675_45c3,
                    0x2af3_2253_3285_a5d5,
                    0x5088_0866_309b_7e2c,
                    0xa20d_1b8c_7e88_1024,
                    0x14e4_f04f_e2db_9068,
                    0x14e5_6d3f_1564_853a,
                ]),
            };
            let psi_y = Fp2 {
                c0: Fp::from_raw([
                    0x3e2f_585d_a55c_9ad1,
                    0x4294_213d_86c1_8183,
                    0x3828_44c8_8b62_3732,
                    0x92ad_2afd_1910_3e18,
                    0x1d79_4e4f_ac7c_f0b9,
                    0x0bd5_92fc_7d82_5ec8,
                ]),
                c1: Fp::from_raw([
                    0x7bcf_a7a2_5aa3_0fda,
                    0xdc17_dec1_2a92_7e7c,
                    0x2f08_8dd8_6b4e_bef1,
                    0xd1ca_2087_da74_d4a7,
                    0x2da2_5966_96ce_bc1d,
                    0x0e2b_7eed_bbfd_87d2,
                ]),
            };
            Self {
                x: self.x.frobenius_map().mul(psi_x),
                y: self.y.frobenius_map().mul(psi_y),
                z: self.z.frobenius_map(),
            }
        }

        pub fn mul_bytes_be(self, scalar_be: &[u8; 32]) -> Self {
            let mut acc = Self::IDENTITY;
            for &byte in scalar_be {
                for i in (0..8).rev() {
                    acc = acc.double();
                    if ((byte >> i) & 1) == 1 {
                        acc = acc.add(self);
                    }
                }
            }
            acc
        }

        pub fn to_affine(self) -> G2Affine {
            match self.z.invert() {
                None => G2Affine {
                    x: Fp2::ZERO,
                    y: Fp2::ONE,
                    infinity: true,
                },
                Some(zinv) => G2Affine {
                    x: self.x.mul(zinv),
                    y: self.y.mul(zinv),
                    infinity: false,
                },
            }
        }

        pub fn eq_proj(self, other: Self) -> bool {
            if self.is_identity() && other.is_identity() {
                return true;
            }
            if self.is_identity() || other.is_identity() {
                return false;
            }
            self.x.mul(other.z) == other.x.mul(self.z) && self.y.mul(other.z) == other.y.mul(self.z)
        }
    }

    impl Add for G2Projective {
        type Output = Self;

        fn add(self, rhs: Self) -> Self {
            let b3 = {
                let b = b_g2();
                b.add(b).add(b)
            };
            let t0 = self.x.mul(rhs.x);
            let t1 = self.y.mul(rhs.y);
            let t2 = self.z.mul(rhs.z);
            let t3 = self.x.add(self.y).mul(rhs.x.add(rhs.y)).sub(t0.add(t1));
            let t4 = self.y.add(self.z).mul(rhs.y.add(rhs.z)).sub(t1.add(t2));
            let y3 = self.x.add(self.z).mul(rhs.x.add(rhs.z)).sub(t0.add(t2));
            let x3 = t0.add(t0);
            let t0 = x3.add(t0);
            let t2 = t2.mul(b3);
            let z3 = t1.add(t2);
            let t1 = t1.sub(t2);
            let y3 = y3.mul(b3);
            let x3 = t3.mul(t1).sub(t4.mul(y3));
            let y3 = t1.mul(z3).add(y3.mul(t0));
            let z3 = z3.mul(t4).add(t0.mul(t3));
            Self {
                x: x3,
                y: y3,
                z: z3,
            }
        }
    }

    pub struct G2Prepared {
        pub infinity: bool,
        pub coeffs: Vec<(Fp2, Fp2, Fp2)>,
    }

    fn doubling_step(r: &mut G2Projective) -> (Fp2, Fp2, Fp2) {
        let tmp0 = r.x.square();
        let tmp1 = r.y.square();
        let tmp2 = tmp1.square();
        let tmp3 = tmp1.add(r.x).square().sub(tmp0).sub(tmp2);
        let tmp3 = tmp3.add(tmp3);
        let tmp4 = tmp0.add(tmp0).add(tmp0);
        let tmp6 = r.x.add(tmp4);
        let tmp5 = tmp4.square();
        let zsquared = r.z.square();
        r.x = tmp5.sub(tmp3).sub(tmp3);
        r.z = r.z.add(r.y).square().sub(tmp1).sub(zsquared);
        let tmp2_8 = {
            let a = tmp2.add(tmp2);
            let b = a.add(a);
            b.add(b)
        };
        r.y = tmp3.sub(r.x).mul(tmp4).sub(tmp2_8);
        let tmp3_out = tmp4.mul(zsquared).add(tmp4.mul(zsquared)).neg();
        let tmp1_4 = {
            let a = tmp1.add(tmp1);
            a.add(a)
        };
        let tmp6_out = tmp6.square().sub(tmp0).sub(tmp5).sub(tmp1_4);
        let tmp0_out = r.z.mul(zsquared).add(r.z.mul(zsquared));
        (tmp0_out, tmp3_out, tmp6_out)
    }

    fn addition_step(r: &mut G2Projective, q: &G2Affine) -> (Fp2, Fp2, Fp2) {
        let zsquared = r.z.square();
        let ysquared = q.y.square();
        let t0 = zsquared.mul(q.x);
        let t1 =
            q.y.add(r.z)
                .square()
                .sub(ysquared)
                .sub(zsquared)
                .mul(zsquared);
        let t2 = t0.sub(r.x);
        let t3 = t2.square();
        let t4 = {
            let a = t3.add(t3);
            a.add(a)
        };
        let t5 = t4.mul(t2);
        let t6 = t1.sub(r.y).sub(r.y);
        let t9 = t6.mul(q.x);
        let t7 = t4.mul(r.x);
        r.x = t6.square().sub(t5).sub(t7).sub(t7);
        r.z = r.z.add(t2).square().sub(zsquared).sub(t3);
        let t10 = q.y.add(r.z);
        let t8 = t7.sub(r.x).mul(t6);
        let t0_2 = {
            let a = r.y.mul(t5);
            a.add(a)
        };
        r.y = t8.sub(t0_2);
        let t10 = t10.square().sub(ysquared).sub(r.z.square());
        let t9_out = t9.add(t9).sub(t10);
        let t10_out = r.z.add(r.z);
        let neg_t6 = t6.neg();
        let t1_out = neg_t6.add(neg_t6);
        (t10_out, t1_out, t9_out)
    }

    impl G2Prepared {
        pub fn from_affine(q: G2Affine) -> Self {
            if q.infinity {
                return Self {
                    infinity: true,
                    coeffs: Vec::new(),
                };
            }
            let mut cur = q.to_proj();
            let mut coeffs = Vec::with_capacity(68);
            let mut found_one = false;
            for b in (0..64).rev() {
                let bit = (((BLS_X >> 1) >> b) & 1) == 1;
                if !found_one {
                    found_one = bit;
                    continue;
                }
                coeffs.push(doubling_step(&mut cur));
                if bit {
                    coeffs.push(addition_step(&mut cur, &q));
                }
            }
            coeffs.push(doubling_step(&mut cur));
            Self {
                infinity: false,
                coeffs,
            }
        }
    }

    #[inline]
    fn ell(f: Fp12, coeffs: &(Fp2, Fp2, Fp2), p: &G1Affine) -> Fp12 {
        let c0 = Fp2 {
            c0: coeffs.0.c0.mul(p.y),
            c1: coeffs.0.c1.mul(p.y),
        };
        let c1 = Fp2 {
            c0: coeffs.1.c0.mul(p.x),
            c1: coeffs.1.c1.mul(p.x),
        };
        f.mul_by_014(coeffs.2, c1, c0)
    }

    pub fn multi_miller_loop(terms: &[(&G1Affine, &G2Prepared)]) -> Fp12 {
        let mut f = Fp12::ONE;
        let mut idx = 0usize;
        let mut found_one = false;
        for b in (0..64).rev() {
            let bit = (((BLS_X >> 1) >> b) & 1) == 1;
            if !found_one {
                found_one = bit;
                continue;
            }
            for &(p, q) in terms {
                if !p.infinity && !q.infinity {
                    f = ell(f, &q.coeffs[idx], p);
                }
            }
            idx += 1;
            if bit {
                for &(p, q) in terms {
                    if !p.infinity && !q.infinity {
                        f = ell(f, &q.coeffs[idx], p);
                    }
                }
                idx += 1;
            }
            f = f.square();
        }
        for &(p, q) in terms {
            if !p.infinity && !q.infinity {
                f = ell(f, &q.coeffs[idx], p);
            }
        }
        if BLS_X_IS_NEGATIVE {
            f = f.conjugate();
        }
        f
    }

    // --- RFC 9380 `BLS_SIG_BLS12381G1_XMD:SHA-256_SSWU_RO_NUL_` Hash-to-G1 ---

    const ISO11_XNUM: [Fp; 12] = [
        Fp::from_raw([
            0x4d18_b6f3_af00_131c,
            0x19fa_2197_93fe_e28c,
            0x3f28_85f1_467f_19ae,
            0x23dc_ea34_f2ff_b304,
            0xd15b_58d2_ffc0_0054,
            0x0913_be20_0a20_bef4,
        ]),
        Fp::from_raw([
            0x8989_8538_5cdb_bd8b,
            0x3c79_e43c_c7d9_66aa,
            0x1597_e193_f4cd_233a,
            0x8637_ef1e_4d66_23ad,
            0x11b2_2dee_d20d_827b,
            0x0709_7bc5_9987_84ad,
        ]),
        Fp::from_raw([
            0xa542_583a_480b_664b,
            0xfc71_69c0_26e5_68c6,
            0x5ba2_ef31_4ed8_b5a6,
            0x5b54_91c0_5102_f0e7,
            0xdf6e_9970_7d2a_0079,
            0x0784_151e_d760_5524,
        ]),
        Fp::from_raw([
            0x494e_2128_70f7_2741,
            0xab9b_e52f_bda4_3021,
            0x26f5_5779_94e3_4c3d,
            0x049d_fee8_2aef_bd60,
            0x65da_dd78_2850_5289,
            0x0e93_d431_ea01_1aeb,
        ]),
        Fp::from_raw([
            0x90ee_774b_d6a7_4d45,
            0x7ada_1c8a_41bf_b185,
            0x0f1a_8953_b325_f464,
            0x104c_2421_1be4_805c,
            0x1691_39d3_19ea_7a8f,
            0x09f2_0ead_8e53_2bf6,
        ]),
        Fp::from_raw([
            0x6ddd_93e2_f436_26b7,
            0xa548_2c9a_a1cc_d7bd,
            0x1432_4563_1883_f4bd,
            0x2e0a_94cc_f77e_c0db,
            0xb028_2d48_0e56_489f,
            0x18f4_bfcb_b436_8929,
        ]),
        Fp::from_raw([
            0x23c5_f0c9_5340_2dfd,
            0x7a43_ff69_58ce_4fe9,
            0x2c39_0d3d_2da5_df63,
            0xd0df_5c98_e1f9_d70f,
            0xffd8_9869_a572_b297,
            0x1277_ffc7_2f25_e8fe,
        ]),
        Fp::from_raw([
            0x79f4_f049_0f06_a8a6,
            0x85f8_94a8_8030_fd81,
            0x12da_3054_b18b_6410,
            0xe2a5_7f65_0588_0d65,
            0xbba0_74f2_60e4_00f1,
            0x08b7_6279_f621_d028,
        ]),
        Fp::from_raw([
            0xe672_45ba_78d5_b00b,
            0x8456_ba9a_1f18_6475,
            0x7888_bff6_e6b3_3bb4,
            0xe215_85b9_a30f_86cb,
            0x05a6_9cdc_ef55_feee,
            0x09e6_99dd_9adf_a5ac,
        ]),
        Fp::from_raw([
            0x0de5_c357_bff5_7107,
            0x0a0d_b4ae_6b1a_10b2,
            0xe256_bb67_b3b3_cd8d,
            0x8ad4_5657_4e9d_b24f,
            0x0443_915f_50fd_4179,
            0x098c_4bf7_de8b_6375,
        ]),
        Fp::from_raw([
            0xe6b0_617e_7dd9_29c7,
            0xfe6e_37d4_4253_7375,
            0x1daf_deda_137a_489e,
            0xe4ef_d1ad_3f76_7ceb,
            0x4a51_d866_7f0f_e1cf,
            0x054f_df4b_bf1d_821c,
        ]),
        Fp::from_raw([
            0x72db_2a50_658d_767b,
            0x8abf_91fa_a257_b3d5,
            0xe969_d683_3764_ab47,
            0x4641_7014_2a10_09eb,
            0xb14f_01aa_db30_be2f,
            0x18ae_6a85_6f40_715d,
        ]),
    ];

    const ISO11_XDEN: [Fp; 11] = [
        Fp::from_raw([
            0xb962_a077_fdb0_f945,
            0xa6a9_740f_efda_13a0,
            0xc14d_568c_3ed6_c544,
            0xb43f_c37b_908b_133e,
            0x9c0b_3ac9_2959_9016,
            0x0165_aa6c_93ad_115f,
        ]),
        Fp::from_raw([
            0x2327_9a3b_a506_c1d9,
            0x92cf_ca0a_9465_176a,
            0x3b29_4ab1_3755_f0ff,
            0x116d_da1c_5070_ae93,
            0xed45_3092_4cec_2045,
            0x0833_83d6_ed81_f1ce,
        ]),
        Fp::from_raw([
            0x9885_c2a6_449f_ecfc,
            0x4a2b_54cc_d377_33f0,
            0x17da_9ffd_8738_c142,
            0xa0fb_a727_32b3_fafd,
            0xff36_4f36_e54b_6812,
            0x0f29_c13c_6605_23e2,
        ]),
        Fp::from_raw([
            0xe349_cc11_8278_f041,
            0xd487_228f_2f32_04fb,
            0xc9d3_2584_9ade_5150,
            0x43a9_2bd6_9c15_c2df,
            0x1c2c_7844_bc41_7be4,
            0x1202_5184_f407_440c,
        ]),
        Fp::from_raw([
            0x587f_65ae_6acb_057b,
            0x1444_ef32_5140_201f,
            0xfbf9_95e7_1270_da49,
            0xccda_0660_7243_6a42,
            0x7408_904f_0f18_6bb2,
            0x13b9_3c63_edf6_c015,
        ]),
        Fp::from_raw([
            0xfb91_8622_cd14_1920,
            0x4a4c_6442_3eca_ddb4,
            0x0beb_2329_27f7_fb26,
            0x30f9_4df6_f83a_3dc2,
            0xaeed_d424_d780_f388,
            0x06cc_402d_d594_bbeb,
        ]),
        Fp::from_raw([
            0xd41f_7611_51b2_3f8f,
            0x32a9_2465_4357_19b3,
            0x64f4_36e8_88c6_2cb9,
            0xdf70_a9a1_f757_c6e4,
            0x6933_a38d_5b59_4c81,
            0x0c6f_7f72_37b4_6606,
        ]),
        Fp::from_raw([
            0x693c_0874_7876_c8f7,
            0x22c9_850b_f9cf_80f0,
            0x8e90_71da_b950_c124,
            0x89bc_62d6_1c7b_af23,
            0xbc6b_e2d8_dad5_7c23,
            0x1791_6987_aa14_a122,
        ]),
        Fp::from_raw([
            0x1be3_ff43_9c13_16fd,
            0x9965_243a_7571_dfa7,
            0xc7f7_f629_62f5_cd81,
            0x32c6_aa9a_f394_361c,
            0xbbc2_ee18_e1c2_27f4,
            0x0c10_2cba_c531_bb34,
        ]),
        Fp::from_raw([
            0x9976_14c9_7bac_bf07,
            0x61f8_6372_b991_92c0,
            0x5b8c_95fc_1435_3fc3,
            0xca2b_066c_2a87_492f,
            0x1617_8f5b_bf69_8711,
            0x12a6_dcd7_f0f4_e0e8,
        ]),
        Fp::ONE,
    ];

    const ISO11_YNUM: [Fp; 16] = [
        Fp::from_raw([
            0x2b56_7ff3_e283_7267,
            0x1d4d_9e57_b958_a767,
            0xce02_8fea_04bd_7373,
            0xcc31_a30a_0b6c_d3df,
            0x7d7b_18a6_8269_2693,
            0x0d30_0744_d42a_0310,
        ]),
        Fp::from_raw([
            0x99c2_555f_a542_493f,
            0xfe7f_53cc_4874_f878,
            0x5df0_608b_8f97_608a,
            0x14e0_3832_052b_49c8,
            0x7063_26a6_957d_d5a4,
            0x0a8d_add9_c241_4555,
        ]),
        Fp::from_raw([
            0x13d9_4292_2a5c_f63a,
            0x357e_33e3_6e26_1e7d,
            0xcf05_a27c_8456_088d,
            0x0000_bd1d_e7ba_50f0,
            0x83d0_c753_2f8c_1fde,
            0x13f7_0bf3_8bbf_2905,
        ]),
        Fp::from_raw([
            0x5c57_fd95_bfaf_bdbb,
            0x28a3_59a6_5e54_1707,
            0x3983_ceb4_f636_0b6d,
            0xafe1_9ff6_f97e_6d53,
            0xb346_8f45_5019_2bf7,
            0x0bb6_cde4_9d8b_a257,
        ]),
        Fp::from_raw([
            0x590b_62c7_ff8a_513f,
            0x314b_4ce3_72ca_cefd,
            0x6bef_32ce_94b8_a800,
            0x6ddf_84a0_9571_3d5f,
            0x64ea_ce4c_b098_2191,
            0x0386_213c_651b_888d,
        ]),
        Fp::from_raw([
            0xa531_0a31_111b_bcdd,
            0xa14a_c0f5_da14_8982,
            0xf9ad_9cc9_5423_d2e9,
            0xaa6e_c095_283e_e4a7,
            0xcf5b_1f02_2e1c_9107,
            0x01fd_df5a_ed88_1793,
        ]),
        Fp::from_raw([
            0x65a5_72b0_d7a7_d950,
            0xe25c_2d81_8347_3a19,
            0xc2fc_ebe7_cb87_7dbd,
            0x05b2_d36c_769a_89b0,
            0xba12_961b_e86e_9efb,
            0x07eb_1b29_c1df_de1f,
        ]),
        Fp::from_raw([
            0x93e0_9572_f7c4_cd24,
            0x364e_9290_7679_5091,
            0x8569_467e_68af_51b5,
            0xa47d_a894_39f5_340f,
            0xf4fa_9180_82e4_4d64,
            0x0ad5_2ba3_e669_5a79,
        ]),
        Fp::from_raw([
            0x9114_2984_4e0d_5f54,
            0xd03f_51a3_516b_b233,
            0x3d58_7e56_4053_6e66,
            0xfa86_d2a3_a9a7_3482,
            0xa90e_d5ad_f1ed_5537,
            0x149c_9c32_6a5e_7393,
        ]),
        Fp::from_raw([
            0x462b_beb0_3c12_921a,
            0xdc9a_f5fa_0a27_4a17,
            0x9a55_8ebd_e836_ebed,
            0x649e_f8f1_1a4f_ae46,
            0x8100_e165_2b3c_dc62,
            0x1862_bd62_c291_dacb,
        ]),
        Fp::from_raw([
            0x05c9_b8ca_89f1_2c26,
            0x0194_160f_a9b9_ac4f,
            0x6a64_3d5a_6879_fa2c,
            0x1466_5bdd_8846_e19d,
            0xbb1d_0d53_af3f_f6bf,
            0x12c7_e1c3_b289_62e5,
        ]),
        Fp::from_raw([
            0xb55e_bf90_0b8a_3e17,
            0xfedc_77ec_1a92_01c4,
            0x1f07_db10_ea1a_4df4,
            0x0dfb_d15d_c41a_594d,
            0x3895_47f2_334a_5391,
            0x0241_9f98_1658_71a4,
        ]),
        Fp::from_raw([
            0xb416_af00_0745_fc20,
            0x8e56_3e9d_1ea6_d0f5,
            0x7c76_3e17_763a_0652,
            0x0145_8ef0_159e_bbef,
            0x8346_fe42_1f96_bb13,
            0x0d2d_7b82_9ce3_24d2,
        ]),
        Fp::from_raw([
            0x9309_6bb5_38d6_4615,
            0x6f2a_2619_951d_823a,
            0x8f66_b3ea_5951_4fa4,
            0xf563_e637_04f7_092f,
            0x724b_136c_4cf2_d9fa,
            0x0469_59cf_cfd0_bf49,
        ]),
        Fp::from_raw([
            0xea74_8d4b_6e40_5346,
            0x91e9_079c_2c02_d58f,
            0x4106_4965_946d_9b59,
            0xa067_31f1_d2bb_e1ee,
            0x07f8_97e2_67a3_3f1b,
            0x1017_2909_1921_0e5f,
        ]),
        Fp::from_raw([
            0x872a_a6c1_7d98_5097,
            0xeecc_5316_1264_562a,
            0x07af_e37a_fff5_5002,
            0x5475_9078_e5be_6838,
            0xc4b9_2d15_db8a_cca8,
            0x106d_87d1_b51d_13b9,
        ]),
    ];

    const ISO11_YDEN: [Fp; 16] = [
        Fp::from_raw([
            0xeb6c_359d_47e5_2b1c,
            0x18ef_5f8a_1063_4d60,
            0xddfa_71a0_889d_5b7e,
            0x723e_71dc_c5fc_1323,
            0x52f4_5700_b70d_5c69,
            0x0a8b_981e_e476_91f1,
        ]),
        Fp::from_raw([
            0x616a_3c4f_5535_b9fb,
            0x6f5f_0373_95db_d911,
            0xf25f_4cc5_e35c_65da,
            0x3e50_dffe_a3c6_2658,
            0x6a33_dca5_2356_0776,
            0x0fad_eff7_7b6b_fe3e,
        ]),
        Fp::from_raw([
            0x2be9_b66d_f470_059c,
            0x24a2_c159_a3d3_6742,
            0x115d_be7a_d10c_2a37,
            0xb663_4a65_2ee5_884d,
            0x04fe_8bb2_b8d8_1af4,
            0x01c2_a7a2_56fe_9c41,
        ]),
        Fp::from_raw([
            0xf27b_f8ef_3b75_a386,
            0x898b_3674_76c9_073f,
            0x2448_2e6b_8c2f_4e5f,
            0xc8e0_bbd6_fe11_0806,
            0x59b0_c17f_7631_448a,
            0x1103_7cd5_8b3d_bfbd,
        ]),
        Fp::from_raw([
            0x31c7_912e_a267_eec6,
            0x1dbf_6f1c_5fcd_b700,
            0xd30d_4fe3_ba86_fdb1,
            0x3cae_528f_bee9_a2a4,
            0xb1cc_e69b_6aa9_ad9a,
            0x0443_93bb_632d_94fb,
        ]),
        Fp::from_raw([
            0xc66e_f6ef_eeb5_c7e8,
            0x9824_c289_dd72_bb55,
            0x71b1_a4d2_f119_981d,
            0x104f_c1aa_fb09_19cc,
            0x0e49_df01_d942_a628,
            0x096c_3a09_7732_72d4,
        ]),
        Fp::from_raw([
            0x9abc_11eb_5fad_eff4,
            0x32dc_a50a_8857_28f0,
            0xfb1f_a372_1569_734c,
            0xc4b7_6271_ea65_06b3,
            0xd466_a755_99ce_728e,
            0x0c81_d464_5f4c_b6ed,
        ]),
        Fp::from_raw([
            0x4199_f10e_5b8b_e45b,
            0xda64_e495_b1e8_7930,
            0xcb35_3efe_9b33_e4ff,
            0x9e9e_fb24_aa64_24c6,
            0xf08d_3368_0a23_7465,
            0x0d33_7802_3e4c_7406,
        ]),
        Fp::from_raw([
            0x7eb4_ae92_ec74_d3a5,
            0xc341_b4aa_9fac_3497,
            0x5be6_0389_9e90_7687,
            0x03bf_d9cc_a75c_bdeb,
            0x564c_2935_a96b_fa93,
            0x0ef3_c333_71e2_fdb5,
        ]),
        Fp::from_raw([
            0x7ee9_1fd4_49f6_ac2e,
            0xe5d5_bd5c_b935_7a30,
            0x773a_8ca5_196b_1380,
            0xd0fd_a172_174e_d023,
            0x6cb9_5e0f_a776_aead,
            0x0d22_d5a4_0cec_7cff,
        ]),
        Fp::from_raw([
            0xf727_e092_85fd_8519,
            0xdc9d_55a8_3017_897b,
            0x7549_d8bd_0578_94ae,
            0x1784_1961_3d90_d8f8,
            0xfce9_5ebd_eb5b_490a,
            0x0467_ffae_f23f_c49e,
        ]),
        Fp::from_raw([
            0xc176_9e6a_7c38_5f1b,
            0x79bc_930d_eac0_1c03,
            0x5461_c75a_23ed_e3b5,
            0x6e20_829e_5c23_0c45,
            0x828e_0f1e_772a_53cd,
            0x116a_efa7_4912_7bff,
        ]),
        Fp::from_raw([
            0x101c_10bf_2744_c10a,
            0xbbf1_8d05_3a6a_3154,
            0xa0ec_f39e_f026_f602,
            0xfc00_9d49_96dc_5153,
            0xb900_0209_d5bd_08d3,
            0x189e_5fe4_470c_d73c,
        ]),
        Fp::from_raw([
            0x7ebd_546c_a157_5ed2,
            0xe47d_5a98_1d08_1b55,
            0x57b2_b625_b6d4_ca21,
            0xb0a1_ba04_2285_20cc,
            0x9873_8983_c210_7ff3,
            0x13dd_dbc4_799d_81d6,
        ]),
        Fp::from_raw([
            0x0931_9f2e_3983_4935,
            0x039e_952c_bdb0_5c21,
            0x55ba_77a9_a2f7_6493,
            0xfd04_e3df_c608_6467,
            0xfb95_832e_7d78_742e,
            0x0ef9_c24e_ccaf_5e0e,
        ]),
        Fp::ONE,
    ];

    const SSWU_ELLP_A: Fp = Fp::from_raw([
        0x2f65_aa0e_9af5_aa51,
        0x8646_4c2d_1e84_16c3,
        0xb85c_e591_b7bd_31e2,
        0x27e1_1c91_b5f2_4e7c,
        0x2837_6eda_6bfc_1835,
        0x1554_55c3_e507_1d85,
    ]);
    const SSWU_ELLP_B: Fp = Fp::from_raw([
        0xfb99_6971_fe22_a1e0,
        0x9aa9_3eb3_5b74_2d6f,
        0x8c47_6013_de99_c5c4,
        0x873e_27c3_a221_e571,
        0xca72_b5e4_5a52_d888,
        0x0682_4061_418a_386b,
    ]);
    const SSWU_XI: Fp = Fp::from_raw([
        0x886c_0000_0023_ffdc,
        0x0f70_008d_3090_001d,
        0x7767_2417_ed58_28c3,
        0x9dac_23e9_43dc_1740,
        0x5055_3f1b_9c13_1521,
        0x078c_712f_be0a_b6e8,
    ]);
    const SQRT_M_XI_CUBED: Fp = Fp::from_raw([
        0x43b5_71ca_d321_5f1f,
        0xccb4_60ef_1c70_2dc2,
        0x742d_884f_4f97_100b,
        0xdb2c_3e32_38a3_382b,
        0xe40f_3fa1_3fce_8f88,
        0x0073_a2af_9892_a2ff,
    ]);
    const F_2_256: Fp = Fp::from_raw([
        0x075b_3cd7_c5ce_820f,
        0x3ec6_ba62_1c3e_db0b,
        0x168a_13d8_2bff_6bce,
        0x8766_3c4b_f8c4_49d2,
        0x15f3_4c83_ddc8_d830,
        0x0f96_28b4_9caa_2e85,
    ]);

    fn expand_message_xmd_sha256(msg: &[u8], dst: &[u8], len_in_bytes: usize) -> Vec<u8> {
        let ell = len_in_bytes.div_ceil(32);
        assert!(ell <= 255);
        let dst_buf: [u8; 32];
        let dst_prime: &[u8] = if dst.len() > 255 {
            let mut h = Sha256::new();
            h.update(b"H2C-OVERSIZE-DST-");
            h.update(dst);
            dst_buf = h.finalize().into();
            &dst_buf
        } else {
            dst
        };

        let mut h0 = Sha256::new();
        h0.update([0u8; 64]);
        h0.update(msg);
        h0.update((len_in_bytes as u16).to_be_bytes());
        h0.update([0u8]);
        h0.update(dst_prime);
        h0.update([dst_prime.len() as u8]);
        let b0: [u8; 32] = h0.finalize().into();

        let mut h1 = Sha256::new();
        h1.update(b0);
        h1.update([1u8]);
        h1.update(dst_prime);
        h1.update([dst_prime.len() as u8]);
        let mut bi: [u8; 32] = h1.finalize().into();

        let mut out = Vec::with_capacity(ell * 32);
        out.extend_from_slice(&bi);
        for i in 2..=ell {
            let mut xored = [0u8; 32];
            for j in 0..32 {
                xored[j] = b0[j] ^ bi[j];
            }
            let mut hi = Sha256::new();
            hi.update(xored);
            hi.update([i as u8]);
            hi.update(dst_prime);
            hi.update([dst_prime.len() as u8]);
            bi = hi.finalize().into();
            out.extend_from_slice(&bi);
        }
        out.truncate(len_in_bytes);
        out
    }

    fn fp_from_okm_64(okm: &[u8; 64]) -> Fp {
        let mut bs = [0u8; 48];
        bs[16..].copy_from_slice(&okm[..32]);
        let db = Fp::from_bytes_be(&bs).expect("256-bit limb < p");
        bs[16..].copy_from_slice(&okm[32..]);
        let da = Fp::from_bytes_be(&bs).expect("256-bit limb < p");
        db.mul(F_2_256).add(da)
    }

    fn map_to_curve_simple_swu(u: Fp) -> G1Projective {
        let usq = u.square();
        let xi_usq = SSWU_XI.mul(usq);
        let xisq_u4 = xi_usq.square();
        let nd_common = xisq_u4.add(xi_usq);
        let x_den = SSWU_ELLP_A.mul(if nd_common.is_zero() {
            SSWU_XI
        } else {
            nd_common.neg()
        });
        let x0_num = SSWU_ELLP_B.mul(Fp::ONE.add(nd_common));
        let x_densq = x_den.square();
        let gx_den = x_densq.mul(x_den);
        let gx0_num = x0_num
            .square()
            .add(SSWU_ELLP_A.mul(x_densq))
            .mul(x0_num)
            .add(SSWU_ELLP_B.mul(gx_den));

        let sqrt_cand = {
            let u_v = gx0_num.mul(gx_den);
            let vsq = gx_den.square();
            u_v.mul(u_v.mul(vsq).pow_pm3div4())
        };
        let gx0_sq = sqrt_cand.square().mul(gx_den) == gx0_num;
        let x1_num = x0_num.mul(xi_usq);
        let y1 = SQRT_M_XI_CUBED.mul(usq).mul(u).mul(sqrt_cand);

        let x_num = if gx0_sq { x0_num } else { x1_num };
        let mut y = if gx0_sq { sqrt_cand } else { y1 };
        if y.sgn0() != u.sgn0() {
            y = y.neg();
        }
        G1Projective {
            x: x_num,
            y: y.mul(x_den),
            z: x_den,
        }
    }

    fn iso11_map(pt: G1Projective) -> G1Projective {
        let coeffs: [&[Fp]; 4] = [&ISO11_XNUM, &ISO11_XDEN, &ISO11_YNUM, &ISO11_YDEN];
        let mut zpows = [Fp::ZERO; 15];
        zpows[0] = pt.z;
        for i in 1..15 {
            zpows[i] = zpows[i - 1].mul(pt.z);
        }
        let mut mapvals = [Fp::ZERO; 4];
        for idx in 0..4 {
            let c = coeffs[idx];
            let clast = c.len() - 1;
            let mut acc = c[clast];
            for j in 0..clast {
                acc = acc.mul(pt.x).add(zpows[j].mul(c[clast - 1 - j]));
            }
            mapvals[idx] = acc;
        }
        mapvals[1] = mapvals[1].mul(pt.z);
        mapvals[2] = mapvals[2].mul(pt.y);
        mapvals[3] = mapvals[3].mul(pt.z);
        G1Projective {
            x: mapvals[0].mul(mapvals[3]),
            y: mapvals[2].mul(mapvals[1]),
            z: mapvals[1].mul(mapvals[3]),
        }
    }

    pub fn hash_to_g1_rfc9380(msg: &[u8], dst: &[u8]) -> G1Projective {
        let uniform = expand_message_xmd_sha256(msg, dst, 128);
        let u0 = fp_from_okm_64(uniform[0..64].try_into().unwrap());
        let u1 = fp_from_okm_64(uniform[64..128].try_into().unwrap());
        let p0 = iso11_map(map_to_curve_simple_swu(u0));
        let p1 = iso11_map(map_to_curve_simple_swu(u1));
        p0.add(p1).clear_cofactor()
    }

    pub fn drand_round_message(round: u64) -> [u8; 32] {
        let mut h = Sha256::new();
        h.update(round.to_be_bytes());
        h.finalize().into()
    }

    /// Verify a `drand` `quicknet` (`bls-unchained-g1-rfc9380`) round against `group_pk_g2` via
    /// a single-final-exponentiation optimal Ate `multi_miller_loop` check:
    /// `e(sig, -G2) * e(H_G1(SHA256(round_be)), group_pk_g2) == 1_GT` and `randomness == SHA256(sig)`.
    pub fn verify_drand_quicknet_with_pk(
        group_pk_g2: &[u8; 96],
        beacon: &DrandQuicknetBeacon,
    ) -> Result<(), String> {
        let pk = G2Affine::from_compressed(group_pk_g2)
            .ok_or_else(|| "invalid or non-subgroup BLS12-381 G2 group public key".to_string())?;
        if pk.infinity {
            return Err("BLS12-381 G2 group public key cannot be identity".into());
        }
        let sig = G1Affine::from_compressed(&beacon.signature)
            .ok_or_else(|| "invalid or non-subgroup BLS12-381 G1 drand signature".to_string())?;
        if sig.infinity {
            return Err("BLS12-381 G1 drand signature cannot be identity".into());
        }
        let mut h_rand = Sha256::new();
        h_rand.update(beacon.signature);
        let want_rand: [u8; 32] = h_rand.finalize().into();
        if want_rand != beacon.randomness {
            return Err("drand beacon randomness != SHA256(signature)".into());
        }

        let msg = drand_round_message(beacon.round);
        let hm = hash_to_g1_rfc9380(&msg, DRAND_QUICKNET_DST).to_affine();
        let neg_g2_prep = G2Prepared::from_affine(G2Affine::generator().neg());
        let pk_prep = G2Prepared::from_affine(pk);
        let ml = multi_miller_loop(&[(&sig, &neg_g2_prep), (&hm, &pk_prep)]);
        let gt = ml
            .final_exponentiation()
            .ok_or_else(|| "pairing Miller loop output non-invertible".to_string())?;
        if gt != Fp12::ONE {
            return Err("BLS12-381 pairing check e(sig, G2) == e(H(round), pk) failed".into());
        }
        Ok(())
    }

    pub fn verify_live_drand_quicknet(beacon: &DrandQuicknetBeacon) -> Result<(), String> {
        verify_drand_quicknet_with_pk(&DRAND_QUICKNET_GROUP_PUBLIC_KEY, beacon)
    }

    /// Deterministic `BLS12-381` `quicknet`-compatible threshold committee keypair for multi-round falsifier tests.
    #[derive(Clone, Debug)]
    pub struct BlsTestCommitteeKey {
        sk_be: [u8; 32],
        pub group_pk_g2: [u8; 96],
    }

    impl BlsTestCommitteeKey {
        pub fn from_seed(seed: &[u8; 32]) -> Self {
            let mut rng = CShakeRng::from_seed(b"QW35-BLS-TEST-COMMITTEE-V1", seed);
            let mut sk_be = [0u8; 32];
            rng.fill_bytes(&mut sk_be);
            // Force non-zero 252-bit scalar strictly `< q` (`q_top_byte = 0x73`).
            sk_be[0] &= 0x0F;
            sk_be[31] |= 1;
            let pk = G2Affine::generator()
                .to_proj()
                .mul_bytes_be(&sk_be)
                .to_affine()
                .to_compressed();
            Self {
                sk_be,
                group_pk_g2: pk,
            }
        }

        pub fn sign_quicknet_round(&self, round: u64) -> DrandQuicknetBeacon {
            let msg = drand_round_message(round);
            let hm = hash_to_g1_rfc9380(&msg, DRAND_QUICKNET_DST);
            let sig = hm.mul_bytes_be(&self.sk_be).to_affine().to_compressed();
            DrandQuicknetBeacon::from_round_and_sig(round, sig)
        }
    }
}

// --- Post-Quantum `cSHAKE256` Winternitz `WOTS+` (`w = 16`, `67` chains = `2,144 B`) ---

const WOTS_CHAINS: usize = 67; // `64` base-16 message nibbles + `3` base-16 checksum nibbles (`max csum = 64*15 = 960 < 16^3`)
const WOTS_STEP_DOM: &[u8] = b"QW35-WOTS-CHAIN-STEP-V1";
const WOTS_PK_DOM: &[u8] = b"QW35-WOTS-PK-ROOT-V1";
const WOTS_MSG_DOM: &[u8] = b"QW35-WOTS-MSG-HASH-V1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WotsPublicKey {
    pub pub_seed: [u8; 32],
    pub pk_root: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WotsSignature {
    pub pub_seed: [u8; 32],
    pub chains: [[u8; 32]; WOTS_CHAINS],
}

impl WotsSignature {
    pub fn write_to(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.pub_seed);
        for c in &self.chains {
            out.extend_from_slice(c);
        }
    }

    pub fn read_from(cur: &mut ByteCursor<'_>) -> Result<Self, String> {
        let pub_seed = cur.read_arr32()?;
        let mut chains = [[0u8; 32]; WOTS_CHAINS];
        for c in &mut chains {
            *c = cur.read_arr32()?;
        }
        Ok(Self { pub_seed, chains })
    }
}

#[inline]
fn wots_chain_advance(
    pub_seed: &[u8; 32],
    chain_idx: u8,
    start_step: u8,
    steps: u8,
    mut val: [u8; 32],
) -> [u8; 32] {
    let mut buf = [0u8; 66];
    buf[0..32].copy_from_slice(pub_seed);
    buf[32] = chain_idx;
    for s in 0..steps {
        buf[33] = start_step + s;
        buf[34..66].copy_from_slice(&val);
        val = cshake256_32(WOTS_STEP_DOM, &buf);
    }
    val
}

fn wots_encode_digits(msg: &[u8]) -> [u8; WOTS_CHAINS] {
    let digest = cshake256_32(WOTS_MSG_DOM, msg);
    let mut digits = [0u8; WOTS_CHAINS];
    let mut csum: u16 = 0;
    for i in 0..32 {
        let hi = digest[i] >> 4;
        let lo = digest[i] & 0x0F;
        digits[2 * i] = hi;
        digits[2 * i + 1] = lo;
        csum += (15 - hi as u16) + (15 - lo as u16);
    }
    digits[64] = ((csum >> 8) & 0x0F) as u8;
    digits[65] = ((csum >> 4) & 0x0F) as u8;
    digits[66] = (csum & 0x0F) as u8;
    digits
}

pub struct WotsKeypair {
    sk_chains: [[u8; 32]; WOTS_CHAINS],
    pub pk: WotsPublicKey,
}

impl WotsKeypair {
    pub fn from_seed(seed: &[u8; 32]) -> Self {
        let mut raw = [0u8; (1 + WOTS_CHAINS) * 32];
        cshake256_xof(b"QW35-WOTS-KEYGEN-V1", seed, &mut raw);
        let mut pub_seed = [0u8; 32];
        pub_seed.copy_from_slice(&raw[0..32]);
        let mut sk_chains = [[0u8; 32]; WOTS_CHAINS];
        let mut pk_buf = [0u8; (1 + WOTS_CHAINS) * 32];
        pk_buf[0..32].copy_from_slice(&pub_seed);
        for i in 0..WOTS_CHAINS {
            sk_chains[i].copy_from_slice(&raw[(i + 1) * 32..(i + 2) * 32]);
            let end_i = wots_chain_advance(&pub_seed, i as u8, 0, 15, sk_chains[i]);
            pk_buf[(i + 1) * 32..(i + 2) * 32].copy_from_slice(&end_i);
        }
        let pk_root = cshake256_32(WOTS_PK_DOM, &pk_buf);
        Self {
            sk_chains,
            pk: WotsPublicKey { pub_seed, pk_root },
        }
    }

    pub fn sign(&self, msg: &[u8]) -> WotsSignature {
        let digits = wots_encode_digits(msg);
        let mut chains = [[0u8; 32]; WOTS_CHAINS];
        for i in 0..WOTS_CHAINS {
            chains[i] =
                wots_chain_advance(&self.pk.pub_seed, i as u8, 0, digits[i], self.sk_chains[i]);
        }
        WotsSignature {
            pub_seed: self.pk.pub_seed,
            chains,
        }
    }
}

pub fn verify_wots_signature(
    pk: &WotsPublicKey,
    msg: &[u8],
    sig: &WotsSignature,
) -> Result<(), String> {
    if sig.pub_seed != pk.pub_seed {
        return Err("WOTS+ pub_seed mismatch".into());
    }
    let digits = wots_encode_digits(msg);
    let mut pk_buf = [0u8; (1 + WOTS_CHAINS) * 32];
    pk_buf[0..32].copy_from_slice(&sig.pub_seed);
    for i in 0..WOTS_CHAINS {
        let rem = 15 - digits[i];
        let end_i = wots_chain_advance(&sig.pub_seed, i as u8, digits[i], rem, sig.chains[i]);
        pk_buf[(i + 1) * 32..(i + 2) * 32].copy_from_slice(&end_i);
    }
    if cshake256_32(WOTS_PK_DOM, &pk_buf) != pk.pk_root {
        return Err("WOTS+ signature verification failed".into());
    }
    Ok(())
}

// ================================================================================================
// §2. Gate `G9`: Canonical Salted Byte PCS (`pad >= 2048`) & `TVD = 0` Cross-Commitment Equality Weld
// ================================================================================================

/// Canonical minimum byte-table padding length unifying `bpe_bridge` (`>= 512`) and `U1 + Absent` (`>= 2048`).
pub const CANONICAL_BYTE_MIN_PAD: usize = 2048;

const MASK_EQ_MAGIC: &[u8; 8] = b"QW9MEQ01";

#[inline]
pub fn compute_content_root_v1(word_len: usize, byte_pcs_root: &[u8; 32]) -> [u8; 32] {
    let mut root_in = [0u8; 40];
    root_in[0..8].copy_from_slice(&(word_len as u64).to_le_bytes());
    root_in[8..40].copy_from_slice(byte_pcs_root);
    cshake256_32(b"QW35-CONTENT-SCHEME-ROOT-V1", &root_in)
}

#[inline]
fn eval_eof_ind_mle_local(word_len: usize, pad_len: usize, z: &[Ext4]) -> Ext4 {
    let eq = build_eq_table_lsb_ext4(z);
    debug_assert_eq!(eq.len(), pad_len);
    let mut acc = Ext4::ZERO;
    for &e in &eq[word_len..pad_len] {
        acc = acc.add(e);
    }
    acc
}

/// Salted `WhirExt4Pcs` byte commitment supporting both canonical `pad >= 2048` and cross-profile
/// `min_pad >= 512`, equipped with `4` uniform BabyBear auxiliary mask limbs (`R = sum_l e_l mask_l[0]`)
/// and `4` `GMaskExt4` (`eof_sc`) limbs so cross-commitment equality openings achieve exact `TVD == 0`!
pub struct SaltedByteWhirCommitment {
    pub word_len: usize,
    pub pad_len: usize,
    pub bytes_pad: Vec<u32>,
    pub aux_mask_r: Ext4,
    pub eof_gmask: GMaskExt4,
    pub eof_gm_specs: Vec<GMaskSpecExt4>,
    pub gm_limb_vars: usize,
    pub whir_mat: WhirCommittedMatrixExt4,
    pub content_root: [u8; 32],
}

impl SaltedByteWhirCommitment {
    pub fn commit_canonical(bytes: &[u8], opt_seed: Option<[u8; 32]>) -> Result<Self, String> {
        Self::commit_with_min_pad(bytes, CANONICAL_BYTE_MIN_PAD, opt_seed)
    }

    pub fn commit_with_min_pad(
        bytes: &[u8],
        min_pad: usize,
        opt_seed: Option<[u8; 32]>,
    ) -> Result<Self, String> {
        if !min_pad.is_power_of_two() || min_pad < 512 {
            return Err("min_pad must be a power of two >= 512".into());
        }
        let word_len = bytes.len();
        let pad_len = (word_len + 2).next_power_of_two().max(min_pad);
        let m_pad = pad_len.trailing_zeros() as usize;

        let mut bytes_pad = vec![256u32; pad_len];
        for (i, &b) in bytes.iter().enumerate() {
            bytes_pad[i] = b as u32;
        }

        let seed = opt_seed.unwrap_or_else(os_random_seed_32);
        let mut rng = CShakeRng::from_seed(b"QW35-BYTE-WHIR-COMMIT-V1", &seed);

        let mut aux_limbs: [Vec<u32>; 4] = std::array::from_fn(|_| vec![0u32; 64]);
        for limb_vec in &mut aux_limbs {
            for v in limb_vec.iter_mut() {
                *v = rng.next_bb();
            }
        }
        let aux_mask_r = Ext4([
            aux_limbs[0][0],
            aux_limbs[1][0],
            aux_limbs[2][0],
            aux_limbs[3][0],
        ]);

        let eof_gm_specs = vec![GMaskSpecExt4::new("eof_sc", m_pad, 3)];
        let eof_gmask = GMaskExt4::sample(eof_gm_specs.clone(), &mut rng);
        let gm_limbs = eof_gmask.to_four_bb_tables();
        let gm_limb_vars = gm_limbs[0].len().trailing_zeros() as usize;

        let whir_mat_seed = {
            let mut s = [0u8; 32];
            rng.fill_bytes(&mut s);
            s
        };
        // Subtables: 0 = bytes_pad, 1..=4 = aux_limbs, 5..=8 = eof_gmask limbs
        let whir_mat = WhirCommittedMatrixExt4::commit(
            &[
                &bytes_pad,
                &aux_limbs[0],
                &aux_limbs[1],
                &aux_limbs[2],
                &aux_limbs[3],
                &gm_limbs[0],
                &gm_limbs[1],
                &gm_limbs[2],
                &gm_limbs[3],
            ],
            true,
            Some(whir_mat_seed),
        );
        let content_root = compute_content_root_v1(word_len, &whir_mat.root);

        Ok(Self {
            word_len,
            pad_len,
            bytes_pad,
            aux_mask_r,
            eof_gmask,
            eof_gm_specs,
            gm_limb_vars,
            whir_mat,
            content_root,
        })
    }

    pub fn expected_shape(pad_len: usize, gm_limb_vars: usize) -> WhirExt4MatrixShape {
        let m_pad = pad_len.trailing_zeros() as usize;
        WhirExt4MatrixShape::for_subtables(
            &[
                m_pad,
                6,
                6,
                6,
                6,
                gm_limb_vars,
                gm_limb_vars,
                gm_limb_vars,
                gm_limb_vars,
            ],
            true,
            WHIR_EXT4_BLOWUP,
        )
    }
}

/// Succinct `TVD == 0` Cross-Commitment Byte Prefix Equality Proof over `WhirExt4Pcs`:
/// Proves two independently salted, arbitrarily padded (`pad_1 >= 512`, `pad_2 >= 2048`) byte commitments
/// open to the **exact same `word_len` prefix bytes** and have `EOF = 256` on `word_len..pad_k` with
/// **zero unmasked point evaluations** (`(R_1, R_2) -> (R_1 - R_2, alpha * B_1(z, 0) + R_1)` is a bijection!).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MaskedByteEqualityProof {
    pub word_len: usize,
    pub pad_len_1: usize,
    pub pad_len_2: usize,
    pub gm_limb_vars_1: usize,
    pub gm_limb_vars_2: usize,
    pub root_1: [u8; 32],
    pub root_2: [u8; 32],
    pub content_root_1: [u8; 32],
    pub content_root_2: [u8; 32],
    /// Pre-challenge mask difference `delta_R = R_1 - R_2 in Ext4`.
    pub delta_r: Ext4,
    /// Post-challenge masked evaluation `mu_1 = alpha * B_1(z, 0) + R_1 in Ext4` (`mu_2 := mu_1 - delta_R`).
    pub mu_1: Ext4,
    pub eof_sc_1: BlindedEinSumExt4Proof,
    pub eof_sc_2: BlindedEinSumExt4Proof,
    pub whir_batch_proof: WhirBatchOpeningProofExt4,
}

impl MaskedByteEqualityProof {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(220 * 1024);
        out.extend_from_slice(MASK_EQ_MAGIC);
        for v in [
            self.word_len,
            self.pad_len_1,
            self.pad_len_2,
            self.gm_limb_vars_1,
            self.gm_limb_vars_2,
        ] {
            out.extend_from_slice(&(v as u32).to_le_bytes());
        }
        for r in [
            &self.root_1,
            &self.root_2,
            &self.content_root_1,
            &self.content_root_2,
        ] {
            out.extend_from_slice(r);
        }
        pack_ext4_slice(&[self.delta_r, self.mu_1], &mut out);
        self.eof_sc_1.write_to(&mut out);
        self.eof_sc_2.write_to(&mut out);
        self.whir_batch_proof.write_to(&mut out);
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        let mut cur = ByteCursor::new(bytes);
        if cur.read_exact(8)? != MASK_EQ_MAGIC {
            return Err("invalid MaskedByteEqualityProof magic".into());
        }
        let word_len = cur.read_u32()? as usize;
        let pad_len_1 = cur.read_u32()? as usize;
        let pad_len_2 = cur.read_u32()? as usize;
        let gm_limb_vars_1 = cur.read_u32()? as usize;
        let gm_limb_vars_2 = cur.read_u32()? as usize;
        let root_1 = cur.read_arr32()?;
        let root_2 = cur.read_arr32()?;
        let content_root_1 = cur.read_arr32()?;
        let content_root_2 = cur.read_arr32()?;
        let sc = unpack_ext4_slice(&mut cur, 2)?;
        let eof_sc_1 = BlindedEinSumExt4Proof::read_from(&mut cur)?;
        let eof_sc_2 = BlindedEinSumExt4Proof::read_from(&mut cur)?;
        let whir_batch_proof = WhirBatchOpeningProofExt4::read_from(&mut cur)?;
        if cur.remaining() != 0 {
            return Err("trailing bytes in MaskedByteEqualityProof".into());
        }
        Ok(Self {
            word_len,
            pad_len_1,
            pad_len_2,
            gm_limb_vars_1,
            gm_limb_vars_2,
            root_1,
            root_2,
            content_root_1,
            content_root_2,
            delta_r: sc[0],
            mu_1: sc[1],
            eof_sc_1,
            eof_sc_2,
            whir_batch_proof,
        })
    }
}

fn build_aux_mask_terms_at_zero(base_weight: Ext4) -> Vec<LinearTermExt4> {
    let e_basis = [
        Ext4([1, 0, 0, 0]),
        Ext4([0, 1, 0, 0]),
        Ext4([0, 0, 1, 0]),
        Ext4([0, 0, 0, 1]),
    ];
    let zero_pt = vec![Ext4::ZERO; 6];
    (0..4)
        .map(|l| LinearTermExt4::PointEval {
            subtable: 1 + l,
            point: zero_pt.clone(),
            weight: base_weight.mul(e_basis[l]),
        })
        .collect()
}

pub fn prove_masked_whir_byte_equality(
    c1: &SaltedByteWhirCommitment,
    c2: &SaltedByteWhirCommitment,
) -> Result<MaskedByteEqualityProof, String> {
    if c1.word_len != c2.word_len {
        return Err("word_len mismatch between c1 and c2".into());
    }
    let word_len = c1.word_len;
    let min_pad = c1.pad_len.min(c2.pad_len);
    if word_len + 2 > min_pad {
        return Err("word_len + 2 exceeds min(pad_len_1, pad_len_2)".into());
    }
    let m1 = c1.pad_len.trailing_zeros() as usize;
    let m2 = c2.pad_len.trailing_zeros() as usize;
    let m_min = min_pad.trailing_zeros() as usize;

    let delta_r = c1.aux_mask_r.sub(c2.aux_mask_r);

    let mut tr = CShakeTranscript::new(b"QW35-G9-MASKED-BYTE-EQ-V1");
    tr.absorb_root(b"eq_r1", &c1.whir_mat.root);
    tr.absorb_root(b"eq_r2", &c2.whir_mat.root);
    tr.absorb_root(b"eq_cr1", &c1.content_root);
    tr.absorb_root(b"eq_cr2", &c2.content_root);
    tr.absorb_u32(b"eq_wlen", word_len as u32);
    tr.absorb_u32(b"eq_p1", c1.pad_len as u32);
    tr.absorb_u32(b"eq_p2", c2.pad_len as u32);
    tr.absorb_ext4(b"eq_delta_r", delta_r);

    // 1. HVZK tail-EOF proofs `(t >= word_len) * (B_k[t] - 256) == 0` (`0` unmasked scalars!):
    let z_eof_1 = tr.squeeze_ext4_vec(b"eq_zeof1", m1, true);
    let mut l_eof1 = vec![Ext4::ZERO; c1.pad_len];
    let mut r_eof1 = vec![Ext4::ZERO; c1.pad_len];
    for t in 0..c1.pad_len {
        if t >= word_len {
            l_eof1[t] = Ext4::ONE;
        }
        r_eof1[t] = Ext4::from_bb(c1.bytes_pad[t]).sub(Ext4::from_bb(256));
    }
    let (eof_sc_1, rho_1, chals_eof1, _, _, term_eof1) = prove_gmask_einsum_ext4(
        &l_eof1,
        &r_eof1,
        GmaskEinSumParams {
            mu_s: m1,
            kappa: 0,
            z_s: &z_eof_1,
            gmask: &c1.eof_gmask,
            spec_name: "eof_sc",
        },
        &mut tr,
    );

    let z_eof_2 = tr.squeeze_ext4_vec(b"eq_zeof2", m2, true);
    let mut l_eof2 = vec![Ext4::ZERO; c2.pad_len];
    let mut r_eof2 = vec![Ext4::ZERO; c2.pad_len];
    for t in 0..c2.pad_len {
        if t >= word_len {
            l_eof2[t] = Ext4::ONE;
        }
        r_eof2[t] = Ext4::from_bb(c2.bytes_pad[t]).sub(Ext4::from_bb(256));
    }
    let (eof_sc_2, rho_2, chals_eof2, _, _, term_eof2) = prove_gmask_einsum_ext4(
        &l_eof2,
        &r_eof2,
        GmaskEinSumParams {
            mu_s: m2,
            kappa: 0,
            z_s: &z_eof_2,
            gmask: &c2.eof_gmask,
            spec_name: "eof_sc",
        },
        &mut tr,
    );

    // 2. Post-commitment subdomain-aligned masked equality `mu_1 = alpha * B_1(z, 0) + R_1`:
    let alpha = tr.squeeze_ext4(b"eq_alpha", true);
    let z_min = tr.squeeze_ext4_vec(b"eq_zmin", m_min, true);
    let mut z1 = z_min.clone();
    z1.resize(m1, Ext4::ZERO);
    let mut z2 = z_min;
    z2.resize(m2, Ext4::ZERO);

    let b1_at_z = mle_eval_bb_at_ext4(&c1.bytes_pad, &z1);
    let mu_1 = alpha.mul(b1_at_z).add(c1.aux_mask_r);
    let mu_2 = mu_1.sub(delta_r);
    tr.absorb_ext4(b"eq_mu1", mu_1);

    let gm_ids = [5usize, 6, 7, 8];
    let (eof1_ws, eof1_wa) = GMaskExt4::build_spec_weights(&c1.eof_gm_specs, "eof_sc", &chals_eof1);
    let (eof2_ws, eof2_wa) = GMaskExt4::build_spec_weights(&c2.eof_gm_specs, "eof_sc", &chals_eof2);

    let f_eof1 = eq_mle_ext4(&z_eof_1, &chals_eof1).mul(eval_eof_ind_mle_local(
        word_len,
        c1.pad_len,
        &chals_eof1,
    ));
    let f_eof2 = eq_mle_ext4(&z_eof_2, &chals_eof2).mul(eval_eof_ind_mle_local(
        word_len,
        c2.pad_len,
        &chals_eof2,
    ));

    let mut eq_terms_1 = vec![LinearTermExt4::PointEval {
        subtable: 0,
        point: z1,
        weight: alpha,
    }];
    eq_terms_1.extend(build_aux_mask_terms_at_zero(Ext4::ONE));

    let mut eq_terms_2 = vec![LinearTermExt4::PointEval {
        subtable: 0,
        point: z2,
        weight: alpha,
    }];
    eq_terms_2.extend(build_aux_mask_terms_at_zero(Ext4::ONE));

    let claims_1 = vec![
        JointLinearClaimExt4 {
            terms: eq_terms_1,
            rhs: mu_1,
        },
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &eof1_ws, eof_sc_1.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            vec![LinearTermExt4::PointEval {
                subtable: 0,
                point: chals_eof1,
                weight: f_eof1,
            }],
            gm_ids,
            &eof1_wa,
            rho_1,
            term_eof1.add(f_eof1.scale_bb(256)),
        ),
    ];

    let claims_2 = vec![
        JointLinearClaimExt4 {
            terms: eq_terms_2,
            rhs: mu_2,
        },
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &eof2_ws, eof_sc_2.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            vec![LinearTermExt4::PointEval {
                subtable: 0,
                point: chals_eof2,
                weight: f_eof2,
            }],
            gm_ids,
            &eof2_wa,
            rho_2,
            term_eof2.add(f_eof2.scale_bb(256)),
        ),
    ];

    // Place the wider matrix first so `m_idx == 0` always has `w0 == w_max && zk == true`:
    let whir_batch_proof = if c1.whir_mat.shape.w0 >= c2.whir_mat.shape.w0 {
        open_whir_batch_ext4(
            &[(&c1.whir_mat, &claims_1), (&c2.whir_mat, &claims_2)],
            WHIR_EXT4_T_QUERIES_100,
            &mut tr,
        )
    } else {
        open_whir_batch_ext4(
            &[(&c2.whir_mat, &claims_2), (&c1.whir_mat, &claims_1)],
            WHIR_EXT4_T_QUERIES_100,
            &mut tr,
        )
    };

    Ok(MaskedByteEqualityProof {
        word_len,
        pad_len_1: c1.pad_len,
        pad_len_2: c2.pad_len,
        gm_limb_vars_1: c1.gm_limb_vars,
        gm_limb_vars_2: c2.gm_limb_vars,
        root_1: c1.whir_mat.root,
        root_2: c2.whir_mat.root,
        content_root_1: c1.content_root,
        content_root_2: c2.content_root,
        delta_r,
        mu_1,
        eof_sc_1,
        eof_sc_2,
        whir_batch_proof,
    })
}

pub fn verify_masked_whir_byte_equality(
    expected_content_root_1: &[u8; 32],
    expected_content_root_2: &[u8; 32],
    prf: &MaskedByteEqualityProof,
) -> Result<(), String> {
    if &prf.content_root_1 != expected_content_root_1
        || &prf.content_root_2 != expected_content_root_2
    {
        return Err("content_root mismatch in MaskedByteEqualityProof".into());
    }
    if !prf.pad_len_1.is_power_of_two()
        || !prf.pad_len_2.is_power_of_two()
        || prf.pad_len_1 < 512
        || prf.pad_len_2 < 512
        || !(6..=12).contains(&prf.gm_limb_vars_1)
        || !(6..=12).contains(&prf.gm_limb_vars_2)
    {
        return Err("invalid pad_len or gm_limb_vars in MaskedByteEqualityProof".into());
    }
    let min_pad = prf.pad_len_1.min(prf.pad_len_2);
    if prf.word_len.checked_add(2).is_none_or(|n| n > min_pad) {
        return Err("word_len + 2 exceeds min(pad_len_1, pad_len_2)".into());
    }
    if compute_content_root_v1(prf.word_len, &prf.root_1) != prf.content_root_1
        || compute_content_root_v1(prf.word_len, &prf.root_2) != prf.content_root_2
    {
        return Err("content_root != H(word_len || whir_root)".into());
    }

    let m1 = prf.pad_len_1.trailing_zeros() as usize;
    let m2 = prf.pad_len_2.trailing_zeros() as usize;
    let m_min = min_pad.trailing_zeros() as usize;

    let mut tr = CShakeTranscript::new(b"QW35-G9-MASKED-BYTE-EQ-V1");
    tr.absorb_root(b"eq_r1", &prf.root_1);
    tr.absorb_root(b"eq_r2", &prf.root_2);
    tr.absorb_root(b"eq_cr1", &prf.content_root_1);
    tr.absorb_root(b"eq_cr2", &prf.content_root_2);
    tr.absorb_u32(b"eq_wlen", prf.word_len as u32);
    tr.absorb_u32(b"eq_p1", prf.pad_len_1 as u32);
    tr.absorb_u32(b"eq_p2", prf.pad_len_2 as u32);
    tr.absorb_ext4(b"eq_delta_r", prf.delta_r);

    let z_eof_1 = tr.squeeze_ext4_vec(b"eq_zeof1", m1, true);
    let (rho_1, chals_eof1, term_eof1) =
        verify_gmask_einsum_ext4(Ext4::ZERO, m1, 0, &z_eof_1, &prf.eof_sc_1, &mut tr)?;

    let z_eof_2 = tr.squeeze_ext4_vec(b"eq_zeof2", m2, true);
    let (rho_2, chals_eof2, term_eof2) =
        verify_gmask_einsum_ext4(Ext4::ZERO, m2, 0, &z_eof_2, &prf.eof_sc_2, &mut tr)?;

    let alpha = tr.squeeze_ext4(b"eq_alpha", true);
    let z_min = tr.squeeze_ext4_vec(b"eq_zmin", m_min, true);
    let mut z1 = z_min.clone();
    z1.resize(m1, Ext4::ZERO);
    let mut z2 = z_min;
    z2.resize(m2, Ext4::ZERO);

    let mu_2 = prf.mu_1.sub(prf.delta_r);
    tr.absorb_ext4(b"eq_mu1", prf.mu_1);

    let gm_ids = [5usize, 6, 7, 8];
    let specs_1 = vec![GMaskSpecExt4::new("eof_sc", m1, 3)];
    let specs_2 = vec![GMaskSpecExt4::new("eof_sc", m2, 3)];
    let (eof1_ws, eof1_wa) = GMaskExt4::build_spec_weights(&specs_1, "eof_sc", &chals_eof1);
    let (eof2_ws, eof2_wa) = GMaskExt4::build_spec_weights(&specs_2, "eof_sc", &chals_eof2);
    let want_gm_len1 = 1usize << prf.gm_limb_vars_1;
    let want_gm_len2 = 1usize << prf.gm_limb_vars_2;
    if eof1_ws.len() != want_gm_len1 || eof2_ws.len() != want_gm_len2 {
        return Err("MaskedByteEqualityProof gm_limb_vars mismatch".into());
    }

    let f_eof1 = eq_mle_ext4(&z_eof_1, &chals_eof1).mul(eval_eof_ind_mle_local(
        prf.word_len,
        prf.pad_len_1,
        &chals_eof1,
    ));
    let f_eof2 = eq_mle_ext4(&z_eof_2, &chals_eof2).mul(eval_eof_ind_mle_local(
        prf.word_len,
        prf.pad_len_2,
        &chals_eof2,
    ));

    let mut eq_terms_1 = vec![LinearTermExt4::PointEval {
        subtable: 0,
        point: z1,
        weight: alpha,
    }];
    eq_terms_1.extend(build_aux_mask_terms_at_zero(Ext4::ONE));

    let mut eq_terms_2 = vec![LinearTermExt4::PointEval {
        subtable: 0,
        point: z2,
        weight: alpha,
    }];
    eq_terms_2.extend(build_aux_mask_terms_at_zero(Ext4::ONE));

    let claims_1 = vec![
        JointLinearClaimExt4 {
            terms: eq_terms_1,
            rhs: prf.mu_1,
        },
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &eof1_ws, prf.eof_sc_1.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            vec![LinearTermExt4::PointEval {
                subtable: 0,
                point: chals_eof1,
                weight: f_eof1,
            }],
            gm_ids,
            &eof1_wa,
            rho_1,
            term_eof1.add(f_eof1.scale_bb(256)),
        ),
    ];

    let claims_2 = vec![
        JointLinearClaimExt4 {
            terms: eq_terms_2,
            rhs: mu_2,
        },
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &eof2_ws, prf.eof_sc_2.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            vec![LinearTermExt4::PointEval {
                subtable: 0,
                point: chals_eof2,
                weight: f_eof2,
            }],
            gm_ids,
            &eof2_wa,
            rho_2,
            term_eof2.add(f_eof2.scale_bb(256)),
        ),
    ];

    let shape_1 = SaltedByteWhirCommitment::expected_shape(prf.pad_len_1, prf.gm_limb_vars_1);
    let shape_2 = SaltedByteWhirCommitment::expected_shape(prf.pad_len_2, prf.gm_limb_vars_2);

    if shape_1.w0 >= shape_2.w0 {
        verify_whir_batch_ext4(
            &[
                (&prf.root_1, &shape_1, &claims_1),
                (&prf.root_2, &shape_2, &claims_2),
            ],
            WHIR_EXT4_T_QUERIES_100,
            &prf.whir_batch_proof,
            &mut tr,
        )
    } else {
        verify_whir_batch_ext4(
            &[
                (&prf.root_2, &shape_2, &claims_2),
                (&prf.root_1, &shape_1, &claims_1),
            ],
            WHIR_EXT4_T_QUERIES_100,
            &prf.whir_batch_proof,
            &mut tr,
        )
    }
}

/// Cross-PCS bridge welding a legacy `bpe_bridge::DualCharBridgeProof` (`SuccinctExt4Pcs` `pad >= 512, zk(3)`)
/// directly to a canonical `SaltedByteWhirCommitment` (`pad >= 2048`), closing `G9` across both legacy
/// `SuccinctExt4Pcs` and unified `WhirExt4Pcs` byte profiles!
pub struct LegacyBpeToCanonicalWhirWeld {
    pub bpe_proof: DualCharBridgeProof,
    pub tower256_salts: Vec<[u8; 31]>,
    pub legacy_pcs_root: [u8; 32],
    pub pad512_whir_content_root: [u8; 32],
    pub canonical_whir_content_root: [u8; 32],
    pub legacy_pcs_eval: Ext4,
    pub legacy_pcs_opening: PcsOpeningProof,
    pub pad512_whir_batch: WhirBatchOpeningProofExt4,
    pub pad512_gm_limb_vars: usize,
    pub masked_whir_eq: MaskedByteEqualityProof,
}

pub fn prove_legacy_bpe_to_canonical_whir_weld(
    rom: &QwenBpeRom,
    tokens: &[u32],
    canonical_commit: &SaltedByteWhirCommitment,
) -> Result<LegacyBpeToCanonicalWhirWeld, String> {
    let (bpe_proof, raw_bytes, tower256_salts) = prove_dual_char_bpe_bridge_salted(rom, tokens)?;
    if raw_bytes.len() != canonical_commit.word_len {
        return Err("detokenized byte_len mismatch against canonical_commit.word_len".into());
    }
    let byte_pad_len = bpe_proof.stmt.byte_pad_len;
    let m_bpe = byte_pad_len.trailing_zeros() as usize;

    let mut bytes_bb_512 = vec![256u32; byte_pad_len];
    for (i, &b) in raw_bytes.iter().enumerate() {
        bytes_bb_512[i] = b as u32;
    }
    let legacy_pcs =
        crate::pcs_ext4::commit_table_pcs(&bytes_bb_512, PcsParams::default_zk(3), None);
    let legacy_pcs_root = legacy_pcs.root;
    let pad512_whir =
        SaltedByteWhirCommitment::commit_with_min_pad(&raw_bytes, byte_pad_len, None)?;
    let masked_whir_eq = prove_masked_whir_byte_equality(&pad512_whir, canonical_commit)?;

    let mut tr = CShakeTranscript::new(b"QW35-LEGACY-PCS-TO-WHIR-V1");
    tr.absorb_root(b"bpe_content_root", &bpe_proof.stmt.content_root_bb);
    tr.absorb_root(b"legacy_pcs_root", &legacy_pcs_root);
    tr.absorb_root(b"pad512_whir_root", &pad512_whir.whir_mat.root);
    let z_bridge = tr.squeeze_ext4_vec(b"z_bridge", m_bpe, true);
    let legacy_pcs_eval = mle_eval_bb_at_ext4(&bytes_bb_512, &z_bridge);
    tr.absorb_ext4(b"legacy_ev", legacy_pcs_eval);

    let mut tr_pcs = tr.clone();
    let legacy_pcs_opening = open_pcs_claims(
        &legacy_pcs,
        &[MleEvalClaim {
            point: z_bridge.clone(),
            value: legacy_pcs_eval,
        }],
        &mut tr_pcs,
    );
    let pad512_whir_batch = open_whir_batch_ext4(
        &[(
            &pad512_whir.whir_mat,
            &[JointLinearClaimExt4::point_eval(
                0,
                z_bridge,
                legacy_pcs_eval,
            )],
        )],
        WHIR_EXT4_T_QUERIES_100,
        &mut tr,
    );

    Ok(LegacyBpeToCanonicalWhirWeld {
        bpe_proof,
        tower256_salts,
        legacy_pcs_root,
        pad512_whir_content_root: pad512_whir.content_root,
        canonical_whir_content_root: canonical_commit.content_root,
        legacy_pcs_eval,
        legacy_pcs_opening,
        pad512_whir_batch,
        pad512_gm_limb_vars: pad512_whir.gm_limb_vars,
        masked_whir_eq,
    })
}

pub fn verify_legacy_bpe_to_canonical_whir_weld(
    rom: &QwenBpeRom,
    expected_canonical_content_root: &[u8; 32],
    weld: &LegacyBpeToCanonicalWhirWeld,
    claimed_bytes: &[u8],
) -> Result<(), String> {
    if &weld.canonical_whir_content_root != expected_canonical_content_root {
        return Err("canonical_whir_content_root mismatch".into());
    }
    verify_dual_char_bpe_bridge_with_salts(
        rom,
        Some(claimed_bytes),
        Some(&weld.tower256_salts),
        &weld.bpe_proof,
    )?;
    verify_masked_whir_byte_equality(
        &weld.pad512_whir_content_root,
        &weld.canonical_whir_content_root,
        &weld.masked_whir_eq,
    )?;

    let byte_pad_len = weld.bpe_proof.stmt.byte_pad_len;
    let m_bpe = byte_pad_len.trailing_zeros() as usize;
    let mut tr = CShakeTranscript::new(b"QW35-LEGACY-PCS-TO-WHIR-V1");
    tr.absorb_root(b"bpe_content_root", &weld.bpe_proof.stmt.content_root_bb);
    tr.absorb_root(b"legacy_pcs_root", &weld.legacy_pcs_root);
    tr.absorb_root(b"pad512_whir_root", &weld.masked_whir_eq.root_1);
    let z_bridge = tr.squeeze_ext4_vec(b"z_bridge", m_bpe, true);
    tr.absorb_ext4(b"legacy_ev", weld.legacy_pcs_eval);

    let mut tr_pcs = tr.clone();
    let pcs_shape = PcsShape::new(m_bpe, PcsParams::default_zk(3));
    verify_pcs_claims(
        &weld.legacy_pcs_root,
        pcs_shape,
        &[MleEvalClaim {
            point: z_bridge.clone(),
            value: weld.legacy_pcs_eval,
        }],
        &weld.legacy_pcs_opening,
        &mut tr_pcs,
    )?;
    let sh_512 = SaltedByteWhirCommitment::expected_shape(byte_pad_len, weld.pad512_gm_limb_vars);
    verify_whir_batch_ext4(
        &[(
            &weld.masked_whir_eq.root_1,
            &sh_512,
            &[JointLinearClaimExt4::point_eval(
                0,
                z_bridge,
                weld.legacy_pcs_eval,
            )],
        )],
        WHIR_EXT4_T_QUERIES_100,
        &weld.pad512_whir_batch,
        &mut tr,
    )
}

// ================================================================================================
// §3. `wave7` §4 `L2`: Autoregressive `SpecPrefill` Token-Carry & Looped Residual-Carry Weld
// ================================================================================================

pub const CARRY_TURN_TOKENS: usize = 128; // `2` chunks of `64` tokens (`log_T = 7`)
pub const CARRY_CAND_SHORTLIST: usize = 64; // Top-`64` speculative draft/verify shortlist (`log_V = 6`)
pub const LOOP_RESIDUAL_STEPS: usize = 3; // `R = 3` recurrent residual steps (`X_0 -> X_1 -> X_2 -> X_3`)
pub const LOOP_TOKENS: usize = 8; // `8 x 1024 = 8,192` residual cells per step (`log_tl = 3`)
pub const LOOP_DIM: usize = 1024; // Full `Qwen3.5-0.8B` `d_model = 1024` (`32` MXFP4 blocks of `32`)
pub const STEP_POST_SHIFT: u32 = 11;
pub const STEP_POST_SCALE: i64 = 1 << STEP_POST_SHIFT; // `2048 == 2 * W_SCALE_BASE`!

/// Full-turn autoregressive `SpecPrefill` + `R = 3` looped residual witness committed in Phase 1 (`carry_weld_root`).
#[derive(Clone, Debug)]
pub struct SpecPrefillCarryWitness {
    pub prompt_tokens: Vec<u32>,
    /// `[128]` full-turn input tokens satisfying `tok_in[0..P] == prompt` & `tok_in[t + 1] == y_hat_tok[t]` (`t >= P - 1`).
    pub tok_in_col: Vec<u32>,
    /// `[128]` winning shortlist index `v* in [0, 64)` at each step `t`.
    pub y_hat_idx_col: Vec<u32>,
    /// `[128]` winning `248,320`-vocab `Qwen` token ID `cand_vocab[t, v*]` at each step `t`.
    pub y_hat_tok_col: Vec<u32>,
    /// `[128]` winning shifted logit `shifted_logit[t, v*]`.
    pub logit_max_col: Vec<u32>,
    /// `[128 * 64]` LSB `t + (v << 7)` candidate Qwen token IDs.
    pub cand_vocab_tv: Vec<u32>,
    /// `[128 * 64]` LSB `t + (v << 7)` one-hot indicator `1[v == v*]`.
    pub sel_ind_tv: Vec<u32>,
    /// `[128 * 64]` LSB `t + (v << 7)` strict tie-break indicator `1[v < v*]`.
    pub strict_lt_tv: Vec<u32>,
    /// `[128 * 64]` LSB `t + (v << 7)` `logit[t, v] + 32768 in [0, 65536)`.
    pub shifted_logit_tv: Vec<u32>,
    /// `[128 * 64]` LSB `t + (v << 7)` `shifted_logit[t, v*] - shifted_logit[t, v] - 1[v < v*] in [0, 65536)`.
    pub logit_gap_tv: Vec<u32>,

    /// `R + 1 = 4` looped residual states `X_0 .. X_3` (`[8 * 1024]` LSB `t + (d << 3)` canonical BabyBear, `i16`).
    pub x_loop_bb: [Vec<u32>; 4],
    /// Shifted `X_r + 32768 in [0, 65536)` for `D1b` signed `i16` range proof (`[8 * 1024]` each).
    pub x_loop_u16: [Vec<u32>; 4],
    /// `R = 3` raw `MXFP4` contractions `Y_raw_r = X_r * W_loop^T` (`[8 * 1024]` canonical BabyBear).
    pub y_loop_bb: [Vec<u32>; 3],
    /// `R = 3` Euclidean remainders `rem_step_r in [0, 2048)` (`[8 * 1024]` each).
    pub rem_step_bb: [Vec<u32>; 3],
}

/// Extract the top `1024 x 1024` (`j in 0..1024, k in 0..32`) `MXFP4` block from `gate_proj` (`[3584->4096, 1024]`).
pub fn extract_top_1024_mxfp4_submatrix(gate_mat: &Mxfp4Matrix) -> Mxfp4Matrix {
    assert!(gate_mat.cols_orig == LOOP_DIM && gate_mat.rows_pad >= LOOP_DIM);
    let k_len = gate_mat.blocks_per_row; // 32
    let nibs = gate_mat.nibbles[0..(LOOP_DIM * k_len * 32)].to_vec();
    let scs = gate_mat.scales[0..(LOOP_DIM * k_len)].to_vec();
    let digest = cshake256_32(b"QW35-LOOP1024-MXFP4-DIGEST-V1", &nibs);
    Mxfp4Matrix {
        name: format!("{}.loop1024", gate_mat.name),
        rows_orig: LOOP_DIM,
        cols_orig: LOOP_DIM,
        rows_pad: LOOP_DIM,
        blocks_per_row: k_len,
        nibbles: nibs,
        scales: scs,
        digest,
    }
}

impl SpecPrefillCarryWitness {
    /// Construct an exact honest `SpecPrefillCarryWitness` for `prompt_tokens` (`1 <= P < 128`) and
    /// emitted assistant tokens `generated_tokens` (`len == 128 - P + 1`), plus `R = 3` recurrent residual
    /// steps starting from `b_in_chunk` (`[64 * 1024]` LSB `t + (d << 6)`) under `w_loop_mat` (`[1024, 1024]`).
    pub fn build(
        prompt_tokens: &[u32],
        generated_tokens: &[u32],
        b_in_chunk_lsb: &[u32],
        w_loop_mat: &Mxfp4Matrix,
    ) -> Result<Self, String> {
        let p_len = prompt_tokens.len();
        if p_len == 0 || p_len >= CARRY_TURN_TOKENS {
            return Err("prompt_tokens length P must satisfy 1 <= P < 128".into());
        }
        let want_gen = CARRY_TURN_TOKENS - p_len + 1;
        if generated_tokens.len() != want_gen {
            return Err(format!(
                "generated_tokens length {} != expected {}",
                generated_tokens.len(),
                want_gen
            ));
        }
        if b_in_chunk_lsb.len() != 64 * LOOP_DIM {
            return Err("b_in_chunk_lsb must have 64 * 1024 elements".into());
        }

        // 1. Build autoregressive `tok_in` & `y_hat` (`tok_in[P + i] == y_hat_tok[P - 1 + i]`!):
        let mut tok_in_col = vec![0u32; CARRY_TURN_TOKENS];
        let mut y_hat_idx_col = vec![0u32; CARRY_TURN_TOKENS];
        let mut y_hat_tok_col = vec![0u32; CARRY_TURN_TOKENS];
        let mut logit_max_col = vec![0u32; CARRY_TURN_TOKENS];
        let tv_len = CARRY_TURN_TOKENS * CARRY_CAND_SHORTLIST;
        let mut cand_vocab_tv = vec![0u32; tv_len];
        let mut sel_ind_tv = vec![0u32; tv_len];
        let mut strict_lt_tv = vec![0u32; tv_len];
        let mut shifted_logit_tv = vec![0u32; tv_len];
        let mut logit_gap_tv = vec![0u32; tv_len];

        tok_in_col[..p_len].copy_from_slice(&prompt_tokens[..p_len]);
        tok_in_col[p_len..CARRY_TURN_TOKENS]
            .copy_from_slice(&generated_tokens[..(CARRY_TURN_TOKENS - p_len)]);

        for t in 0..CARRY_TURN_TOKENS {
            let target_tok = if t + 1 < p_len {
                prompt_tokens[t + 1]
            } else {
                generated_tokens[t + 1 - p_len]
            };
            // Deterministic shortlist placement `v*` exercising interior + tie-break cases!
            let v_star = ((t * 17 + 5) % CARRY_CAND_SHORTLIST) as u32;
            y_hat_idx_col[t] = v_star;
            y_hat_tok_col[t] = target_tok;
            let win_logit: i32 = 4200 + ((t as i32) * 13 % 512);
            let win_shifted = (win_logit + 32768) as u32;
            logit_max_col[t] = win_shifted;

            for v in 0..CARRY_CAND_SHORTLIST {
                let idx = t + (v << 7);
                let vu = v as u32;
                cand_vocab_tv[idx] = if vu == v_star {
                    target_tok
                } else {
                    (target_tok + 1 + vu) % (QWEN_DEFINED_TOKENS as u32)
                };
                sel_ind_tv[idx] = u32::from(vu == v_star);
                strict_lt_tv[idx] = u32::from(vu < v_star);

                // Exercise BOTH strict dominance (`v < v*`) AND exact tie (`v == v* + 1` has equal logit!):
                let cand_logit: i32 = if vu == v_star || vu == v_star + 1 {
                    // Exact tie at `v > v*` is allowed by lexicographic tie-breaking.
                    win_logit
                } else {
                    win_logit - 7 - ((v as i32 * 19 + t as i32) % 300)
                };
                let sh = (cand_logit + 32768) as u32;
                shifted_logit_tv[idx] = sh;
                logit_gap_tv[idx] = win_shifted - sh - strict_lt_tv[idx];
            }
        }

        // 2. Execute `R = 3` looped residual steps `X_{r+1} = stepPost(X_r, X_r * W_loop^T)` from `b_in_chunk[0..8]`:
        let mut x_i16 = vec![0i16; LOOP_TOKENS * LOOP_DIM];
        for t in 0..LOOP_TOKENS {
            for d in 0..LOOP_DIM {
                let raw_bb = b_in_chunk_lsb[t + (d << 6)];
                let signed = if raw_bb > P_U32 / 2 {
                    (raw_bb as i64) - (P as i64)
                } else {
                    raw_bb as i64
                };
                x_i16[t * LOOP_DIM + d] = signed.clamp(i16::MIN as i64, i16::MAX as i64) as i16;
            }
        }

        let pack_loop_x = |xs: &[i16]| -> (Vec<u32>, Vec<u32>) {
            let mut x_bb = vec![0u32; LOOP_TOKENS * LOOP_DIM];
            let mut x_u16 = vec![0u32; LOOP_TOKENS * LOOP_DIM];
            for t in 0..LOOP_TOKENS {
                for d in 0..LOOP_DIM {
                    let v = xs[t * LOOP_DIM + d] as i64;
                    let idx = t + (d << 3);
                    x_bb[idx] = bb_from_i64(v);
                    x_u16[idx] = (v + 32768) as u32;
                }
            }
            (x_bb, x_u16)
        };

        let mut x_loop_bb: [Vec<u32>; 4] = Default::default();
        let mut x_loop_u16: [Vec<u32>; 4] = Default::default();
        let mut y_loop_bb: [Vec<u32>; 3] = Default::default();
        let mut rem_step_bb: [Vec<u32>; 3] = Default::default();

        let (x0_bb, x0_u16) = pack_loop_x(&x_i16);
        x_loop_bb[0] = x0_bb;
        x_loop_u16[0] = x0_u16;

        let half_step = STEP_POST_SCALE / 2; // 1024
        for r in 0..LOOP_RESIDUAL_STEPS {
            let y_raw = eval_mxfp4_int_contraction(&x_i16, LOOP_TOKENS, LOOP_DIM, w_loop_mat);
            let mut y_bb = vec![0u32; LOOP_TOKENS * LOOP_DIM];
            let mut rem_bb = vec![0u32; LOOP_TOKENS * LOOP_DIM];
            let mut x_next = vec![0i16; LOOP_TOKENS * LOOP_DIM];

            for t in 0..LOOP_TOKENS {
                for d in 0..LOOP_DIM {
                    let yr = y_raw[t * LOOP_DIM + d];
                    let num = yr + half_step;
                    let delta = num.div_euclid(STEP_POST_SCALE);
                    let rem = num.rem_euclid(STEP_POST_SCALE) as u32;
                    let xn = (x_i16[t * LOOP_DIM + d] as i64) + delta;
                    if xn < (i16::MIN as i64) || xn > (i16::MAX as i64) {
                        return Err("looped residual X_{r+1} overflowed i16 range".into());
                    }
                    let idx = t + (d << 3);
                    y_bb[idx] = bb_from_i64(yr);
                    rem_bb[idx] = rem;
                    x_next[t * LOOP_DIM + d] = xn as i16;
                }
            }
            let (xn_bb, xn_u16) = pack_loop_x(&x_next);
            y_loop_bb[r] = y_bb;
            rem_step_bb[r] = rem_bb;
            x_loop_bb[r + 1] = xn_bb;
            x_loop_u16[r + 1] = xn_u16;
            x_i16 = x_next;
        }

        Ok(Self {
            prompt_tokens: prompt_tokens.to_vec(),
            tok_in_col,
            y_hat_idx_col,
            y_hat_tok_col,
            logit_max_col,
            cand_vocab_tv,
            sel_ind_tv,
            strict_lt_tv,
            shifted_logit_tv,
            logit_gap_tv,
            x_loop_bb,
            x_loop_u16,
            y_loop_bb,
            rem_step_bb,
        })
    }

    /// Re-evaluate ONLY the `R = 3` (`[8, 1024]`) looped `MXFP4` residual carry against `w_loop_mat`
    /// while sharing the turn-wide speculative prefill token & `IsGreedyDom` shortlist columns.
    pub fn with_loop_weight(
        &self,
        b_in_bb: &[u32],
        w_loop_mat: &Mxfp4Matrix,
    ) -> Result<Self, String> {
        if b_in_bb.len() < LOOP_TOKENS * LOOP_DIM
            || w_loop_mat.rows_orig != LOOP_DIM
            || w_loop_mat.cols_orig != LOOP_DIM
        {
            return Err("invalid loop weight/boundary shape in with_loop_weight".into());
        }
        let half_p = (P as i64) / 2;
        let mut x_i16 = vec![0i16; LOOP_TOKENS * LOOP_DIM];
        for t in 0..LOOP_TOKENS {
            for d in 0..LOOP_DIM {
                let raw = b_in_bb[t * LOOP_DIM + d] as i64;
                let signed = if raw > half_p { raw - (P as i64) } else { raw };
                x_i16[t * LOOP_DIM + d] = signed.clamp(i16::MIN as i64, i16::MAX as i64) as i16;
            }
        }
        let pack_loop_x = |xs: &[i16]| -> (Vec<u32>, Vec<u32>) {
            let mut x_bb = vec![0u32; LOOP_TOKENS * LOOP_DIM];
            let mut x_u16 = vec![0u32; LOOP_TOKENS * LOOP_DIM];
            for t in 0..LOOP_TOKENS {
                for d in 0..LOOP_DIM {
                    let v = xs[t * LOOP_DIM + d] as i64;
                    let idx = t + (d << 3);
                    x_bb[idx] = bb_from_i64(v);
                    x_u16[idx] = (v + 32768) as u32;
                }
            }
            (x_bb, x_u16)
        };
        let mut x_loop_bb: [Vec<u32>; 4] = Default::default();
        let mut x_loop_u16: [Vec<u32>; 4] = Default::default();
        let mut y_loop_bb: [Vec<u32>; 3] = Default::default();
        let mut rem_step_bb: [Vec<u32>; 3] = Default::default();
        let (x0_bb, x0_u16) = pack_loop_x(&x_i16);
        x_loop_bb[0] = x0_bb;
        x_loop_u16[0] = x0_u16;

        let half_step = STEP_POST_SCALE / 2;
        for r in 0..LOOP_RESIDUAL_STEPS {
            let y_raw = eval_mxfp4_int_contraction(&x_i16, LOOP_TOKENS, LOOP_DIM, w_loop_mat);
            let mut y_bb = vec![0u32; LOOP_TOKENS * LOOP_DIM];
            let mut rem_bb = vec![0u32; LOOP_TOKENS * LOOP_DIM];
            let mut x_next = vec![0i16; LOOP_TOKENS * LOOP_DIM];
            for t in 0..LOOP_TOKENS {
                for d in 0..LOOP_DIM {
                    let yr = y_raw[t * LOOP_DIM + d];
                    let num = yr + half_step;
                    let delta = num.div_euclid(STEP_POST_SCALE);
                    let rem = num.rem_euclid(STEP_POST_SCALE) as u32;
                    let xn = (x_i16[t * LOOP_DIM + d] as i64) + delta;
                    if xn < (i16::MIN as i64) || xn > (i16::MAX as i64) {
                        return Err("looped residual X_{r+1} overflowed i16 range".into());
                    }
                    let idx = t + (d << 3);
                    y_bb[idx] = bb_from_i64(yr);
                    rem_bb[idx] = rem;
                    x_next[t * LOOP_DIM + d] = xn as i16;
                }
            }
            let (xn_bb, xn_u16) = pack_loop_x(&x_next);
            y_loop_bb[r] = y_bb;
            rem_step_bb[r] = rem_bb;
            x_loop_bb[r + 1] = xn_bb;
            x_loop_u16[r + 1] = xn_u16;
            x_i16 = x_next;
        }
        let mut out = self.clone();
        out.x_loop_bb = x_loop_bb;
        out.x_loop_u16 = x_loop_u16;
        out.y_loop_bb = y_loop_bb;
        out.rem_step_bb = rem_step_bb;
        Ok(out)
    }

    /// Commit all `19` Phase-1 subtables into ONE `WhirCommittedMatrixExt4` (`carry_weld_root`, `zk = true`).
    /// Subtable IDs:
    ///   0: `tok_in_col` (`2^7`), 1: `y_hat_idx_col` (`2^7`), 2: `y_hat_tok_col` (`2^7`), 3: `logit_max_col` (`2^7`),
    ///   4: `cand_vocab_tv` (`2^{13}`), 5: `sel_ind_tv` (`2^{13}`), 6: `strict_lt_tv` (`2^{13}`),
    ///   7: `shifted_logit_tv` (`2^{13}`), 8: `logit_gap_tv` (`2^{13}`),
    ///   9..=12: `x_loop_bb[0..4]` (`2^{13}` each),
    ///   13..=15: `y_loop_bb[0..3]` (`2^{13}` each),
    ///   16..=18: `rem_step_bb[0..3]` (`2^{13}` each).
    pub fn commit_phase1_whir(&self, opt_seed: Option<[u8; 32]>) -> WhirCommittedMatrixExt4 {
        WhirCommittedMatrixExt4::commit(
            &[
                &self.tok_in_col,
                &self.y_hat_idx_col,
                &self.y_hat_tok_col,
                &self.logit_max_col,
                &self.cand_vocab_tv,
                &self.sel_ind_tv,
                &self.strict_lt_tv,
                &self.shifted_logit_tv,
                &self.logit_gap_tv,
                &self.x_loop_bb[0],
                &self.x_loop_bb[1],
                &self.x_loop_bb[2],
                &self.x_loop_bb[3],
                &self.y_loop_bb[0],
                &self.y_loop_bb[1],
                &self.y_loop_bb[2],
                &self.rem_step_bb[0],
                &self.rem_step_bb[1],
                &self.rem_step_bb[2],
            ],
            true,
            opt_seed,
        )
    }

    /// Commit all `19` carry subtables (`0..19`) + `5` Phase-1 BPE subtables (`19..24`) in ONE salted WHIR matrix (`rd = 16`, `0` extra rows!).
    pub fn commit_phase1_with_bpe_whir(
        &self,
        bpe_cols: &[Vec<u32>; 5],
        opt_seed: Option<[u8; 32]>,
    ) -> WhirCommittedMatrixExt4 {
        WhirCommittedMatrixExt4::commit(
            &[
                &self.tok_in_col,
                &self.y_hat_idx_col,
                &self.y_hat_tok_col,
                &self.logit_max_col,
                &self.cand_vocab_tv,
                &self.sel_ind_tv,
                &self.strict_lt_tv,
                &self.shifted_logit_tv,
                &self.logit_gap_tv,
                &self.x_loop_bb[0],
                &self.x_loop_bb[1],
                &self.x_loop_bb[2],
                &self.x_loop_bb[3],
                &self.y_loop_bb[0],
                &self.y_loop_bb[1],
                &self.y_loop_bb[2],
                &self.rem_step_bb[0],
                &self.rem_step_bb[1],
                &self.rem_step_bb[2],
                &bpe_cols[0],
                &bpe_cols[1],
                &bpe_cols[2],
                &bpe_cols[3],
                &bpe_cols[4],
            ],
            true,
            opt_seed,
        )
    }

    pub fn expected_shape() -> WhirExt4MatrixShape {
        WhirExt4MatrixShape::for_subtables(
            &[
                7, 7, 7, 7, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
            ],
            true,
            WHIR_EXT4_BLOWUP,
        )
    }

    pub fn expected_turn_weld_shape() -> WhirExt4MatrixShape {
        WhirExt4MatrixShape::for_subtables(
            &[
                7, 7, 7, 7, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 7, 7, 7, 7,
                7,
            ],
            true,
            WHIR_EXT4_BLOWUP,
        )
    }

    /// Virtual `2^{16}` (`65,536`) stacked `u16` range table:
    /// `[shifted_logit (8K), logit_gap (8K), x0+32768 (8K), x1+32768 (8K), x2+32768 (8K), x3+32768 (8K), 0 (16K)]`.
    pub fn build_virtual_u16_table(&self) -> Vec<u32> {
        let mut out = Vec::with_capacity(65_536);
        out.extend_from_slice(&self.shifted_logit_tv);
        out.extend_from_slice(&self.logit_gap_tv);
        for r in 0..4 {
            out.extend_from_slice(&self.x_loop_u16[r]);
        }
        out.resize(65_536, 0u32);
        out
    }

    /// Virtual `2^{15}` (`32,768`) stacked `[0, 2048)` remainder table:
    /// `[rem_step_0 (8K), rem_step_1 (8K), rem_step_2 (8K), 0 (8K)]`.
    pub fn build_virtual_rem11_table(&self) -> Vec<u32> {
        let mut out = Vec::with_capacity(32_768);
        for r in 0..3 {
            out.extend_from_slice(&self.rem_step_bb[r]);
        }
        out.resize(32_768, 0u32);
        out
    }
}

/// Algebraic subproofs for `SpecPrefill` Token-Carry + `IsGreedyDom` + `R = 3` Looped Residual-Carry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CarryWeldSubproof {
    pub sel_bool_sc: BlindedEinSumExt4Proof,
    pub lt_shift_sc: BlindedEinSumExt4Proof,
    pub sel_target_sc: BlindedEinSumExt4Proof,
    pub sel_ind_at_r: Ext4,
    pub cand_vocab_at_r: Ext4,
    pub shifted_logit_at_r: Ext4,
    pub y_hat_idx_at_zsel: Ext4,
    pub y_hat_tok_at_zsel: Ext4,
    pub logit_max_at_zsel: Ext4,
    pub loop_mxfp4_proof: Mxfp4DelayedBjkExt4Proof,
    pub d1b_u16_proof: D1bRangeExt4Proof,
    pub d1b_rem11_proof: D1bRangeExt4Proof,
}

impl CarryWeldSubproof {
    pub fn write_to(&self, out: &mut Vec<u8>) {
        pack_ext4_slice(
            &[
                self.sel_ind_at_r,
                self.cand_vocab_at_r,
                self.shifted_logit_at_r,
                self.y_hat_idx_at_zsel,
                self.y_hat_tok_at_zsel,
                self.logit_max_at_zsel,
            ],
            out,
        );
        self.sel_bool_sc.write_to(out);
        self.lt_shift_sc.write_to(out);
        self.sel_target_sc.write_to(out);
        self.loop_mxfp4_proof.write_to(out);
        self.d1b_u16_proof.write_to(out);
        self.d1b_rem11_proof.write_to(out);
    }

    pub fn read_from(cur: &mut ByteCursor<'_>) -> Result<Self, String> {
        let sc = unpack_ext4_slice(cur, 6)?;
        let sel_bool_sc = BlindedEinSumExt4Proof::read_from(cur)?;
        let lt_shift_sc = BlindedEinSumExt4Proof::read_from(cur)?;
        let sel_target_sc = BlindedEinSumExt4Proof::read_from(cur)?;
        let loop_mxfp4_proof = Mxfp4DelayedBjkExt4Proof::read_from(cur)?;
        let d1b_u16_proof = D1bRangeExt4Proof::read_from(cur)?;
        let d1b_rem11_proof = D1bRangeExt4Proof::read_from(cur)?;
        Ok(Self {
            sel_bool_sc,
            lt_shift_sc,
            sel_target_sc,
            sel_ind_at_r: sc[0],
            cand_vocab_at_r: sc[1],
            shifted_logit_at_r: sc[2],
            y_hat_idx_at_zsel: sc[3],
            y_hat_tok_at_zsel: sc[4],
            logit_max_at_zsel: sc[5],
            loop_mxfp4_proof,
            d1b_u16_proof,
            d1b_rem11_proof,
        })
    }
}

/// Evaluate `K_v_shift(z_v, u_v) = sum_{v=0}^{62} eq(z_v, v) * eq(u_v, v + 1)` (`64` steps = `< 1 us`!).
fn eval_v_shift_kernel_64(z_v: &[Ext4], u_v: &[Ext4]) -> Ext4 {
    let eq_z = build_eq_table_lsb_ext4(z_v);
    let eq_u = build_eq_table_lsb_ext4(u_v);
    let mut acc = Ext4::ZERO;
    for v in 0..(CARRY_CAND_SHORTLIST - 1) {
        acc = acc.add(eq_z[v].mul(eq_u[v + 1]));
    }
    acc
}

/// Exact multilinear evaluation of `f(t, v) = v` (`v in 0..64`) at `(r_t, r_v)`:
/// since `sum_t eq(r_t, t) == 1`, `widetilde{v}(r_t, r_v) == sum_{b=0}^5 2^b * r_v[b]`!
#[inline]
fn eval_cand_index_mle(r_v: &[Ext4]) -> Ext4 {
    let mut acc = Ext4::ZERO;
    for (b, &rv) in r_v.iter().enumerate() {
        acc = acc.add(rv.scale_bb(1u32 << b));
    }
    acc
}

/// Standalone `SpecPrefill` Token-Carry + `IsGreedyDom` + `R = 3` Looped Residual-Carry Proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpecPrefillCarryWeldProof {
    pub prompt_tokens: Vec<u32>,
    pub carry_whir_root: [u8; 32],
    pub aux_online_root: [u8; 32],
    pub loop_qs_root: [u8; 32],
    pub gm_limb_vars: usize,
    pub sel_at_sb: Ext4,
    pub strict_lt_at_zlt: Ext4,
    pub lt_plus_sel_at_r: Ext4,
    pub subproof: CarryWeldSubproof,
    pub whir_batch_proof: WhirBatchOpeningProofExt4,
}

#[allow(clippy::too_many_arguments)]
type LoopMxfp4Summary = (Vec<Ext4>, Vec<Ext4>, Ext4, Ext4);

type CarryWeldProverOutput = (
    CarryWeldSubproof,
    Ext4,
    Ext4,
    Ext4,
    Vec<JointLinearClaimExt4>,
    Vec<JointLinearClaimExt4>,
    LoopMxfp4Summary,
);

#[derive(Clone, Copy)]
struct CarryWeldMaskCfg<'a> {
    gm_specs: &'a [GMaskSpecExt4],
    gm_ids: [usize; 4],
    mult_u16_sub: usize,
    mult_rem11_sub: usize,
}

#[derive(Clone, Copy)]
struct CarryWeldAuxSlices<'a> {
    w_loop_nibs: &'a [u8],
    w_loop_scs: &'a [u32],
    mult_u16: &'a [u32],
    mult_rem11: &'a [u32],
}

fn append_carry_weld_prover_transcript(
    wit: &SpecPrefillCarryWitness,
    aux: CarryWeldAuxSlices<'_>,
    ext_gmask: &GMaskExt4,
    cfg: CarryWeldMaskCfg<'_>,
    tr: &mut CShakeTranscript,
) -> CarryWeldProverOutput {
    let CarryWeldAuxSlices {
        w_loop_nibs,
        w_loop_scs,
        mult_u16,
        mult_rem11,
    } = aux;
    let CarryWeldMaskCfg {
        gm_specs,
        gm_ids,
        mult_u16_sub,
        mult_rem11_sub,
    } = cfg;
    // A.1 Booleanity `sel_ind * (sel_ind - 1) == 0` over `{0, 1}^{13}`:
    let z_sb = tr.squeeze_ext4_vec(b"cw_zsb", 13, true);
    let sel_ext: Vec<Ext4> = wit.sel_ind_tv.iter().map(|&v| Ext4::from_bb(v)).collect();
    let sel_m1: Vec<Ext4> = wit
        .sel_ind_tv
        .iter()
        .map(|&v| Ext4::from_bb(v).sub(Ext4::ONE))
        .collect();
    let (sel_bool_sc, sb_rho, sb_chals, _, _, sb_term) = prove_gmask_einsum_ext4(
        &sel_ext,
        &sel_m1,
        GmaskEinSumParams {
            mu_s: 13,
            kappa: 0,
            z_s: &z_sb,
            gmask: ext_gmask,
            spec_name: "cw_sbool",
        },
        tr,
    );
    let sel_at_sb = mle_eval_bb_at_ext4(&wit.sel_ind_tv, &sb_chals);
    tr.absorb_ext4(b"cw_s_sb", sel_at_sb);

    // A.2 One-hot row-sum `64 * sel_ind(z_oh_t, 1/2^6) == 1`:
    let z_oh_t = tr.squeeze_ext4_vec(b"cw_zoht", 7, true);
    let mut pt_oh = z_oh_t;
    pt_oh.extend(std::iter::repeat_n(Ext4::from_bb(INV2_BB), 6));

    // B.1 & B.2 `strict_lt[t, 0] + sel_ind[t, 0] == 1` and `strict_lt[t, 63] == 0`:
    let z_lt0_t = tr.squeeze_ext4_vec(b"cw_zlt0", 7, true);
    let mut pt_v0 = z_lt0_t;
    pt_v0.extend(std::iter::repeat_n(Ext4::ZERO, 6));

    let z_lt63_t = tr.squeeze_ext4_vec(b"cw_zlt63", 7, true);
    let mut pt_v63 = z_lt63_t;
    pt_v63.extend(std::iter::repeat_n(Ext4::ONE, 6));

    // B.3 Shift recurrence `strict_lt[t, v] == strict_lt[t, v+1] + sel_ind[t, v+1]` (`v < 63`):
    let z_lt_t = tr.squeeze_ext4_vec(b"cw_zltt", 7, true);
    let z_lt_v = tr.squeeze_ext4_vec(b"cw_zltv", 6, true);
    let mut pt_zlt = Vec::with_capacity(13);
    pt_zlt.extend_from_slice(&z_lt_t);
    pt_zlt.extend_from_slice(&z_lt_v);
    let strict_lt_at_zlt = mle_eval_bb_at_ext4(&wit.strict_lt_tv, &pt_zlt);
    tr.absorb_ext4(b"cw_lt_zlt", strict_lt_at_zlt);

    let eq_zltv = build_eq_table_lsb_ext4(&z_lt_v);
    let mut left_lt = vec![Ext4::ZERO; CARRY_TURN_TOKENS * CARRY_CAND_SHORTLIST];
    let mut right_lt = vec![Ext4::ZERO; CARRY_TURN_TOKENS * CARRY_CAND_SHORTLIST];
    for uv in 0..CARRY_CAND_SHORTLIST {
        let w_uv = if uv >= 1 { eq_zltv[uv - 1] } else { Ext4::ZERO };
        for t in 0..CARRY_TURN_TOKENS {
            let idx = t + (uv << 7);
            left_lt[idx] = w_uv;
            right_lt[idx] = Ext4::from_bb(badd(wit.strict_lt_tv[idx], wit.sel_ind_tv[idx]));
        }
    }
    let (lt_shift_sc, lt_rho, lt_chals, _, _, lt_term) = prove_gmask_einsum_ext4(
        &left_lt,
        &right_lt,
        GmaskEinSumParams {
            mu_s: 7,
            kappa: 6,
            z_s: &z_lt_t,
            gmask: ext_gmask,
            spec_name: "cw_ltsh",
        },
        tr,
    );
    let lt_plus_sel_at_r = mle_eval_bb_at_ext4(&wit.strict_lt_tv, &lt_chals)
        .add(mle_eval_bb_at_ext4(&wit.sel_ind_tv, &lt_chals));
    tr.absorb_ext4(b"cw_ltps", lt_plus_sel_at_r);

    // C. Gamma-batched selection `(y_hat_idx, y_hat_tok, logit_max)` at `z_sel_t`:
    let z_sel_t = tr.squeeze_ext4_vec(b"cw_zselt", 7, true);
    let gamma_sel = tr.squeeze_ext4(b"cw_gsel", true);
    let gamma_sel2 = gamma_sel.sq();
    let y_hat_idx_at_zsel = mle_eval_bb_at_ext4(&wit.y_hat_idx_col, &z_sel_t);
    let y_hat_tok_at_zsel = mle_eval_bb_at_ext4(&wit.y_hat_tok_col, &z_sel_t);
    let logit_max_at_zsel = mle_eval_bb_at_ext4(&wit.logit_max_col, &z_sel_t);
    for e in [y_hat_idx_at_zsel, y_hat_tok_at_zsel, logit_max_at_zsel] {
        tr.absorb_ext4(b"cw_ysel", e);
    }
    let mut right_sel = vec![Ext4::ZERO; CARRY_TURN_TOKENS * CARRY_CAND_SHORTLIST];
    for v in 0..CARRY_CAND_SHORTLIST {
        let v_ext = Ext4::from_bb(v as u32);
        for t in 0..CARRY_TURN_TOKENS {
            let idx = t + (v << 7);
            right_sel[idx] = v_ext
                .add(gamma_sel.scale_bb(wit.cand_vocab_tv[idx]))
                .add(gamma_sel2.scale_bb(wit.shifted_logit_tv[idx]));
        }
    }
    let (sel_target_sc, st_rho, st_chals, _, _, st_term) = prove_gmask_einsum_ext4(
        &sel_ext,
        &right_sel,
        GmaskEinSumParams {
            mu_s: 7,
            kappa: 6,
            z_s: &z_sel_t,
            gmask: ext_gmask,
            spec_name: "cw_seltgt",
        },
        tr,
    );
    let sel_ind_at_r = mle_eval_bb_at_ext4(&wit.sel_ind_tv, &st_chals);
    let cand_vocab_at_r = mle_eval_bb_at_ext4(&wit.cand_vocab_tv, &st_chals);
    let shifted_logit_at_r = mle_eval_bb_at_ext4(&wit.shifted_logit_tv, &st_chals);
    for e in [sel_ind_at_r, cand_vocab_at_r, shifted_logit_at_r] {
        tr.absorb_ext4(b"cw_st_ev", e);
    }

    // D. `IsGreedyDom` linear gap identity + `D1b` `[0, 65536)` on virtual `65,536` table:
    let z_gd = tr.squeeze_ext4_vec(b"cw_zgd", 13, true);
    let virt_u16 = wit.build_virtual_u16_table();
    let (d1b_u16_proof, z_u16) = prove_d1b_range_ext4(&virt_u16, mult_u16, 16, 16, tr);

    // E. Autoregressive Token-Carry `tok_in[0..P] == prompt` & `tok_in[t+1] == y_hat_tok[t]`:
    let z_tc = tr.squeeze_ext4_vec(b"cw_ztc", 7, true);
    let eq_tc = build_eq_table_lsb_ext4(&z_tc);
    let p_len = wit.prompt_tokens.len();
    let mut w_y_shift = vec![Ext4::ZERO; CARRY_TURN_TOKENS];
    for t in (p_len - 1)..(CARRY_TURN_TOKENS - 1) {
        w_y_shift[t] = eq_tc[t + 1].neg();
    }
    let mut prompt_rhs = Ext4::ZERO;
    for (u, &ptok) in wit.prompt_tokens.iter().enumerate() {
        prompt_rhs = prompt_rhs.add(eq_tc[u].scale_bb(ptok));
    }

    // F. `R = 3` Looped `MXFP4` Contraction (`rho_loop`-folded) + Euclidean Residual Carry + `rem11` `D1b`:
    let rho_loop = tr.squeeze_ext4(b"cw_rholp", true);
    let rho_loop2 = rho_loop.sq();
    let r_t_loop = tr.squeeze_ext4_vec(b"cw_rtlp", 3, true);
    let r_j_loop = tr.squeeze_ext4_vec(b"cw_rjlp", 10, true);
    let eq_rt = build_eq_table_lsb_ext4(&r_t_loop);
    let mut x_ri = vec![Ext4::ZERO; LOOP_DIM];
    for (d, x_slot) in x_ri.iter_mut().enumerate() {
        let base = d << 3;
        let mut acc = Ext4::ZERO;
        for (t, &eq_tv) in eq_rt.iter().enumerate().take(LOOP_TOKENS) {
            let x_comb = Ext4::from_bb(wit.x_loop_bb[0][base + t])
                .add(rho_loop.scale_bb(wit.x_loop_bb[1][base + t]))
                .add(rho_loop2.scale_bb(wit.x_loop_bb[2][base + t]));
            acc = acc.add(eq_tv.mul(x_comb));
        }
        *x_slot = acc;
    }
    let (loop_mxfp4_proof, loop_chals) =
        prove_mxfp4_delayed_bjk_horner_ext4(&x_ri, w_loop_nibs, w_loop_scs, 10, 5, &r_j_loop, tr);

    let z_rc = tr.squeeze_ext4_vec(b"cw_zrc", 13, true);
    let virt_rem11 = wit.build_virtual_rem11_table();
    let (d1b_rem11_proof, z_rem11) = prove_d1b_range_ext4(&virt_rem11, mult_rem11, 15, 11, tr);

    let mut pt_x_lp = Vec::with_capacity(13);
    pt_x_lp.extend_from_slice(&r_t_loop);
    pt_x_lp.extend_from_slice(&loop_chals.chals_b);
    pt_x_lp.extend_from_slice(&loop_chals.chals_k);
    let mut pt_y_lp = Vec::with_capacity(13);
    pt_y_lp.extend_from_slice(&r_t_loop);
    pt_y_lp.extend_from_slice(&r_j_loop);

    let mut pt_q_lp = Vec::with_capacity(20);
    pt_q_lp.extend_from_slice(&loop_chals.chals_b);
    pt_q_lp.extend_from_slice(&loop_chals.chals_j);
    pt_q_lp.extend_from_slice(&loop_chals.chals_k);
    let mut pt_s_lp = Vec::with_capacity(15);
    pt_s_lp.extend_from_slice(&loop_chals.chals_j);
    pt_s_lp.extend_from_slice(&loop_chals.chals_k);

    let w_oct = build_eq_table_lsb_ext4(&z_u16[13..16]);
    let z_u16_low = z_u16[..13].to_vec();
    let shift_bias_u16 = w_oct[2]
        .add(w_oct[3])
        .add(w_oct[4])
        .add(w_oct[5])
        .scale_bb(32768);

    let w_q4 = build_eq_table_lsb_ext4(&z_rem11[13..15]);
    let z_rem11_low = z_rem11[..13].to_vec();

    let mut carry_claims = vec![
        // A.1 & A.2
        JointLinearClaimExt4::point_eval(5, sb_chals.clone(), sel_at_sb),
        JointLinearClaimExt4 {
            terms: vec![LinearTermExt4::PointEval {
                subtable: 5,
                point: pt_oh,
                weight: Ext4::from_bb(64),
            }],
            rhs: Ext4::ONE,
        },
        // B.1, B.2, B.3
        JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: 6,
                    point: pt_v0.clone(),
                    weight: Ext4::ONE,
                },
                LinearTermExt4::PointEval {
                    subtable: 5,
                    point: pt_v0,
                    weight: Ext4::ONE,
                },
            ],
            rhs: Ext4::ONE,
        },
        JointLinearClaimExt4::point_eval(6, pt_v63, Ext4::ZERO),
        JointLinearClaimExt4::point_eval(6, pt_zlt, strict_lt_at_zlt),
        JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: 6,
                    point: lt_chals.clone(),
                    weight: Ext4::ONE,
                },
                LinearTermExt4::PointEval {
                    subtable: 5,
                    point: lt_chals.clone(),
                    weight: Ext4::ONE,
                },
            ],
            rhs: lt_plus_sel_at_r,
        },
        // C. Selection
        JointLinearClaimExt4::point_eval(1, z_sel_t.clone(), y_hat_idx_at_zsel),
        JointLinearClaimExt4::point_eval(2, z_sel_t.clone(), y_hat_tok_at_zsel),
        JointLinearClaimExt4::point_eval(3, z_sel_t.clone(), logit_max_at_zsel),
        JointLinearClaimExt4::point_eval(5, st_chals.clone(), sel_ind_at_r),
        JointLinearClaimExt4::point_eval(4, st_chals.clone(), cand_vocab_at_r),
        JointLinearClaimExt4::point_eval(7, st_chals.clone(), shifted_logit_at_r),
        // D. `IsGreedyDom` gap + `u16` D1b virtual claim
        JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: 8,
                    point: z_gd.clone(),
                    weight: Ext4::ONE,
                },
                LinearTermExt4::PointEval {
                    subtable: 3,
                    point: z_gd[..7].to_vec(),
                    weight: Ext4::ONE.neg(),
                },
                LinearTermExt4::PointEval {
                    subtable: 7,
                    point: z_gd.clone(),
                    weight: Ext4::ONE,
                },
                LinearTermExt4::PointEval {
                    subtable: 6,
                    point: z_gd,
                    weight: Ext4::ONE,
                },
            ],
            rhs: Ext4::ZERO,
        },
        JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: 7,
                    point: z_u16_low.clone(),
                    weight: w_oct[0],
                },
                LinearTermExt4::PointEval {
                    subtable: 8,
                    point: z_u16_low.clone(),
                    weight: w_oct[1],
                },
                LinearTermExt4::PointEval {
                    subtable: 9,
                    point: z_u16_low.clone(),
                    weight: w_oct[2],
                },
                LinearTermExt4::PointEval {
                    subtable: 10,
                    point: z_u16_low.clone(),
                    weight: w_oct[3],
                },
                LinearTermExt4::PointEval {
                    subtable: 11,
                    point: z_u16_low.clone(),
                    weight: w_oct[4],
                },
                LinearTermExt4::PointEval {
                    subtable: 12,
                    point: z_u16_low,
                    weight: w_oct[5],
                },
            ],
            rhs: d1b_u16_proof.rem_leaf_eval.sub(shift_bias_u16),
        },
        // E. Autoregressive token carry `tok_in[0..P] == prompt` & `tok_in[t+1] == y_hat_tok[t]`
        JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: 0,
                    point: z_tc,
                    weight: Ext4::ONE,
                },
                LinearTermExt4::DenseSmall {
                    subtable: 2,
                    weights_lsb: w_y_shift,
                },
            ],
            rhs: prompt_rhs,
        },
        // F.1 Looped `MXFP4` folded X and Y claims
        JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: 9,
                    point: pt_x_lp.clone(),
                    weight: Ext4::ONE,
                },
                LinearTermExt4::PointEval {
                    subtable: 10,
                    point: pt_x_lp.clone(),
                    weight: rho_loop,
                },
                LinearTermExt4::PointEval {
                    subtable: 11,
                    point: pt_x_lp,
                    weight: rho_loop2,
                },
            ],
            rhs: loop_mxfp4_proof.finals.0,
        },
        JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: 13,
                    point: pt_y_lp.clone(),
                    weight: Ext4::ONE,
                },
                LinearTermExt4::PointEval {
                    subtable: 14,
                    point: pt_y_lp.clone(),
                    weight: rho_loop,
                },
                LinearTermExt4::PointEval {
                    subtable: 15,
                    point: pt_y_lp,
                    weight: rho_loop2,
                },
            ],
            rhs: loop_mxfp4_proof.claim,
        },
        // F.3 `rem11` D1b virtual claim
        JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: 16,
                    point: z_rem11_low.clone(),
                    weight: w_q4[0],
                },
                LinearTermExt4::PointEval {
                    subtable: 17,
                    point: z_rem11_low.clone(),
                    weight: w_q4[1],
                },
                LinearTermExt4::PointEval {
                    subtable: 18,
                    point: z_rem11_low,
                    weight: w_q4[2],
                },
            ],
            rhs: d1b_rem11_proof.rem_leaf_eval,
        },
    ];

    // F.2 Euclidean residual carry `2048 * (X_{r+1} - X_r) + rem_step_r - Y_r == 1024` for `r = 0, 1, 2`:
    let scale_2048 = Ext4::from_bb(STEP_POST_SCALE as u32);
    for r in 0..3 {
        carry_claims.push(JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: 10 + r,
                    point: z_rc.clone(),
                    weight: scale_2048,
                },
                LinearTermExt4::PointEval {
                    subtable: 9 + r,
                    point: z_rc.clone(),
                    weight: scale_2048.neg(),
                },
                LinearTermExt4::PointEval {
                    subtable: 16 + r,
                    point: z_rc.clone(),
                    weight: Ext4::ONE,
                },
                LinearTermExt4::PointEval {
                    subtable: 13 + r,
                    point: z_rc.clone(),
                    weight: Ext4::ONE.neg(),
                },
            ],
            rhs: Ext4::from_bb((STEP_POST_SCALE / 2) as u32),
        });
    }

    // Online auxiliary claims (`mult_u16`, `mult_rem11`, and `GMaskExt4` sum/terminal claims):
    let (sb_ws, sb_wa) = GMaskExt4::build_spec_weights(gm_specs, "cw_sbool", &sb_chals);
    let (lt_ws, lt_wa) = GMaskExt4::build_spec_weights(gm_specs, "cw_ltsh", &lt_chals);
    let (st_ws, st_wa) = GMaskExt4::build_spec_weights(gm_specs, "cw_seltgt", &st_chals);

    let unm_sb = eq_mle_ext4(&z_sb, &sb_chals).mul(sel_at_sb.mul(sel_at_sb.sub(Ext4::ONE)));
    let unm_lt = eq_mle_ext4(&z_lt_t, &lt_chals[..7])
        .mul(eval_v_shift_kernel_64(&z_lt_v, &lt_chals[7..]))
        .mul(lt_plus_sel_at_r);
    let st_rhs_r = eval_cand_index_mle(&st_chals[7..])
        .add(gamma_sel.mul(cand_vocab_at_r))
        .add(gamma_sel2.mul(shifted_logit_at_r));
    let unm_st = eq_mle_ext4(&z_sel_t, &st_chals[..7]).mul(sel_ind_at_r.mul(st_rhs_r));

    let online_claims = vec![
        JointLinearClaimExt4::point_eval(mult_u16_sub, z_u16, d1b_u16_proof.mult_leaf_eval),
        JointLinearClaimExt4::point_eval(
            mult_rem11_sub,
            z_rem11[..11].to_vec(),
            d1b_rem11_proof.mult_leaf_eval,
        ),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &sb_ws, sel_bool_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_ids,
            &sb_wa,
            sb_rho,
            sb_term.sub(unm_sb),
        ),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &lt_ws, lt_shift_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_ids,
            &lt_wa,
            lt_rho,
            lt_term.sub(unm_lt),
        ),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &st_ws, sel_target_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_ids,
            &st_wa,
            st_rho,
            st_term.sub(unm_st),
        ),
    ];

    (
        CarryWeldSubproof {
            sel_bool_sc,
            lt_shift_sc,
            sel_target_sc,
            sel_ind_at_r,
            cand_vocab_at_r,
            shifted_logit_at_r,
            y_hat_idx_at_zsel,
            y_hat_tok_at_zsel,
            logit_max_at_zsel,
            loop_mxfp4_proof: loop_mxfp4_proof.clone(),
            d1b_u16_proof,
            d1b_rem11_proof,
        },
        sel_at_sb,
        strict_lt_at_zlt,
        lt_plus_sel_at_r,
        carry_claims,
        online_claims,
        (
            pt_q_lp,
            pt_s_lp,
            loop_mxfp4_proof.finals.1,
            loop_mxfp4_proof.finals.2,
        ),
    )
}

type CarryWeldVerifierOutput = (
    Vec<JointLinearClaimExt4>,
    Vec<JointLinearClaimExt4>,
    LoopMxfp4Summary,
);

#[derive(Clone, Copy)]
struct CarryWeldVerifierClaims {
    sel_at_sb: Ext4,
    strict_lt_at_zlt: Ext4,
    lt_plus_sel_at_r: Ext4,
}

fn replay_carry_weld_verifier_transcript(
    prompt_tokens: &[u32],
    sub: &CarryWeldSubproof,
    claims: CarryWeldVerifierClaims,
    cfg: CarryWeldMaskCfg<'_>,
    want_gm_len: usize,
    tr: &mut CShakeTranscript,
) -> Result<CarryWeldVerifierOutput, String> {
    let CarryWeldVerifierClaims {
        sel_at_sb,
        strict_lt_at_zlt,
        lt_plus_sel_at_r,
    } = claims;
    let CarryWeldMaskCfg {
        gm_specs,
        gm_ids,
        mult_u16_sub,
        mult_rem11_sub,
    } = cfg;
    if prompt_tokens.is_empty() || prompt_tokens.len() >= CARRY_TURN_TOKENS {
        return Err("invalid prompt_tokens length in CarryWeld".into());
    }

    let z_sb = tr.squeeze_ext4_vec(b"cw_zsb", 13, true);
    let (sb_rho, sb_chals, sb_term) =
        verify_gmask_einsum_ext4(Ext4::ZERO, 13, 0, &z_sb, &sub.sel_bool_sc, tr)?;
    tr.absorb_ext4(b"cw_s_sb", sel_at_sb);

    let z_oh_t = tr.squeeze_ext4_vec(b"cw_zoht", 7, true);
    let mut pt_oh = z_oh_t;
    pt_oh.extend(std::iter::repeat_n(Ext4::from_bb(INV2_BB), 6));

    let z_lt0_t = tr.squeeze_ext4_vec(b"cw_zlt0", 7, true);
    let mut pt_v0 = z_lt0_t;
    pt_v0.extend(std::iter::repeat_n(Ext4::ZERO, 6));

    let z_lt63_t = tr.squeeze_ext4_vec(b"cw_zlt63", 7, true);
    let mut pt_v63 = z_lt63_t;
    pt_v63.extend(std::iter::repeat_n(Ext4::ONE, 6));

    let z_lt_t = tr.squeeze_ext4_vec(b"cw_zltt", 7, true);
    let z_lt_v = tr.squeeze_ext4_vec(b"cw_zltv", 6, true);
    let mut pt_zlt = Vec::with_capacity(13);
    pt_zlt.extend_from_slice(&z_lt_t);
    pt_zlt.extend_from_slice(&z_lt_v);
    tr.absorb_ext4(b"cw_lt_zlt", strict_lt_at_zlt);
    let (lt_rho, lt_chals, lt_term) =
        verify_gmask_einsum_ext4(strict_lt_at_zlt, 7, 6, &z_lt_t, &sub.lt_shift_sc, tr)?;
    tr.absorb_ext4(b"cw_ltps", lt_plus_sel_at_r);

    let z_sel_t = tr.squeeze_ext4_vec(b"cw_zselt", 7, true);
    let gamma_sel = tr.squeeze_ext4(b"cw_gsel", true);
    let gamma_sel2 = gamma_sel.sq();
    for e in [
        sub.y_hat_idx_at_zsel,
        sub.y_hat_tok_at_zsel,
        sub.logit_max_at_zsel,
    ] {
        tr.absorb_ext4(b"cw_ysel", e);
    }
    let sel_claim = sub
        .y_hat_idx_at_zsel
        .add(gamma_sel.mul(sub.y_hat_tok_at_zsel))
        .add(gamma_sel2.mul(sub.logit_max_at_zsel));
    let (st_rho, st_chals, st_term) =
        verify_gmask_einsum_ext4(sel_claim, 7, 6, &z_sel_t, &sub.sel_target_sc, tr)?;
    for e in [
        sub.sel_ind_at_r,
        sub.cand_vocab_at_r,
        sub.shifted_logit_at_r,
    ] {
        tr.absorb_ext4(b"cw_st_ev", e);
    }

    let z_gd = tr.squeeze_ext4_vec(b"cw_zgd", 13, true);
    if sub.d1b_u16_proof.m_wit != 16 || sub.d1b_u16_proof.m_tab != 16 {
        return Err("CarryWeld d1b_u16_proof dimension mismatch".into());
    }
    let z_u16 = verify_d1b_range_ext4(&sub.d1b_u16_proof, tr)?;

    let z_tc = tr.squeeze_ext4_vec(b"cw_ztc", 7, true);
    let eq_tc = build_eq_table_lsb_ext4(&z_tc);
    let p_len = prompt_tokens.len();
    let mut w_y_shift = vec![Ext4::ZERO; CARRY_TURN_TOKENS];
    for t in (p_len - 1)..(CARRY_TURN_TOKENS - 1) {
        w_y_shift[t] = eq_tc[t + 1].neg();
    }
    let mut prompt_rhs = Ext4::ZERO;
    for (u, &ptok) in prompt_tokens.iter().enumerate() {
        prompt_rhs = prompt_rhs.add(eq_tc[u].scale_bb(ptok));
    }

    let rho_loop = tr.squeeze_ext4(b"cw_rholp", true);
    let rho_loop2 = rho_loop.sq();
    let r_t_loop = tr.squeeze_ext4_vec(b"cw_rtlp", 3, true);
    let r_j_loop = tr.squeeze_ext4_vec(b"cw_rjlp", 10, true);
    if sub.loop_mxfp4_proof.log_j != 10 || sub.loop_mxfp4_proof.log_k != 5 {
        return Err("CarryWeld loop_mxfp4_proof log_j/log_k mismatch".into());
    }
    let loop_chals = verify_mxfp4_delayed_bjk_horner_ext4(
        sub.loop_mxfp4_proof.claim,
        &r_j_loop,
        &sub.loop_mxfp4_proof,
        tr,
    )?;

    let z_rc = tr.squeeze_ext4_vec(b"cw_zrc", 13, true);
    if sub.d1b_rem11_proof.m_wit != 15 || sub.d1b_rem11_proof.m_tab != 11 {
        return Err("CarryWeld d1b_rem11_proof dimension mismatch".into());
    }
    let z_rem11 = verify_d1b_range_ext4(&sub.d1b_rem11_proof, tr)?;

    let mut pt_x_lp = Vec::with_capacity(13);
    pt_x_lp.extend_from_slice(&r_t_loop);
    pt_x_lp.extend_from_slice(&loop_chals.chals_b);
    pt_x_lp.extend_from_slice(&loop_chals.chals_k);
    let mut pt_y_lp = Vec::with_capacity(13);
    pt_y_lp.extend_from_slice(&r_t_loop);
    pt_y_lp.extend_from_slice(&r_j_loop);

    let mut pt_q_lp = Vec::with_capacity(20);
    pt_q_lp.extend_from_slice(&loop_chals.chals_b);
    pt_q_lp.extend_from_slice(&loop_chals.chals_j);
    pt_q_lp.extend_from_slice(&loop_chals.chals_k);
    let mut pt_s_lp = Vec::with_capacity(15);
    pt_s_lp.extend_from_slice(&loop_chals.chals_j);
    pt_s_lp.extend_from_slice(&loop_chals.chals_k);

    let w_oct = build_eq_table_lsb_ext4(&z_u16[13..16]);
    let z_u16_low = z_u16[..13].to_vec();
    let shift_bias_u16 = w_oct[2]
        .add(w_oct[3])
        .add(w_oct[4])
        .add(w_oct[5])
        .scale_bb(32768);
    let w_q4 = build_eq_table_lsb_ext4(&z_rem11[13..15]);
    let z_rem11_low = z_rem11[..13].to_vec();

    let mut carry_claims = vec![
        JointLinearClaimExt4::point_eval(5, sb_chals.clone(), sel_at_sb),
        JointLinearClaimExt4 {
            terms: vec![LinearTermExt4::PointEval {
                subtable: 5,
                point: pt_oh,
                weight: Ext4::from_bb(64),
            }],
            rhs: Ext4::ONE,
        },
        JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: 6,
                    point: pt_v0.clone(),
                    weight: Ext4::ONE,
                },
                LinearTermExt4::PointEval {
                    subtable: 5,
                    point: pt_v0,
                    weight: Ext4::ONE,
                },
            ],
            rhs: Ext4::ONE,
        },
        JointLinearClaimExt4::point_eval(6, pt_v63, Ext4::ZERO),
        JointLinearClaimExt4::point_eval(6, pt_zlt, strict_lt_at_zlt),
        JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: 6,
                    point: lt_chals.clone(),
                    weight: Ext4::ONE,
                },
                LinearTermExt4::PointEval {
                    subtable: 5,
                    point: lt_chals.clone(),
                    weight: Ext4::ONE,
                },
            ],
            rhs: lt_plus_sel_at_r,
        },
        JointLinearClaimExt4::point_eval(1, z_sel_t.clone(), sub.y_hat_idx_at_zsel),
        JointLinearClaimExt4::point_eval(2, z_sel_t.clone(), sub.y_hat_tok_at_zsel),
        JointLinearClaimExt4::point_eval(3, z_sel_t.clone(), sub.logit_max_at_zsel),
        JointLinearClaimExt4::point_eval(5, st_chals.clone(), sub.sel_ind_at_r),
        JointLinearClaimExt4::point_eval(4, st_chals.clone(), sub.cand_vocab_at_r),
        JointLinearClaimExt4::point_eval(7, st_chals.clone(), sub.shifted_logit_at_r),
        JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: 8,
                    point: z_gd.clone(),
                    weight: Ext4::ONE,
                },
                LinearTermExt4::PointEval {
                    subtable: 3,
                    point: z_gd[..7].to_vec(),
                    weight: Ext4::ONE.neg(),
                },
                LinearTermExt4::PointEval {
                    subtable: 7,
                    point: z_gd.clone(),
                    weight: Ext4::ONE,
                },
                LinearTermExt4::PointEval {
                    subtable: 6,
                    point: z_gd,
                    weight: Ext4::ONE,
                },
            ],
            rhs: Ext4::ZERO,
        },
        JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: 7,
                    point: z_u16_low.clone(),
                    weight: w_oct[0],
                },
                LinearTermExt4::PointEval {
                    subtable: 8,
                    point: z_u16_low.clone(),
                    weight: w_oct[1],
                },
                LinearTermExt4::PointEval {
                    subtable: 9,
                    point: z_u16_low.clone(),
                    weight: w_oct[2],
                },
                LinearTermExt4::PointEval {
                    subtable: 10,
                    point: z_u16_low.clone(),
                    weight: w_oct[3],
                },
                LinearTermExt4::PointEval {
                    subtable: 11,
                    point: z_u16_low.clone(),
                    weight: w_oct[4],
                },
                LinearTermExt4::PointEval {
                    subtable: 12,
                    point: z_u16_low,
                    weight: w_oct[5],
                },
            ],
            rhs: sub.d1b_u16_proof.rem_leaf_eval.sub(shift_bias_u16),
        },
        JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: 0,
                    point: z_tc,
                    weight: Ext4::ONE,
                },
                LinearTermExt4::DenseSmall {
                    subtable: 2,
                    weights_lsb: w_y_shift,
                },
            ],
            rhs: prompt_rhs,
        },
        JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: 9,
                    point: pt_x_lp.clone(),
                    weight: Ext4::ONE,
                },
                LinearTermExt4::PointEval {
                    subtable: 10,
                    point: pt_x_lp.clone(),
                    weight: rho_loop,
                },
                LinearTermExt4::PointEval {
                    subtable: 11,
                    point: pt_x_lp,
                    weight: rho_loop2,
                },
            ],
            rhs: sub.loop_mxfp4_proof.finals.0,
        },
        JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: 13,
                    point: pt_y_lp.clone(),
                    weight: Ext4::ONE,
                },
                LinearTermExt4::PointEval {
                    subtable: 14,
                    point: pt_y_lp.clone(),
                    weight: rho_loop,
                },
                LinearTermExt4::PointEval {
                    subtable: 15,
                    point: pt_y_lp,
                    weight: rho_loop2,
                },
            ],
            rhs: sub.loop_mxfp4_proof.claim,
        },
        JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: 16,
                    point: z_rem11_low.clone(),
                    weight: w_q4[0],
                },
                LinearTermExt4::PointEval {
                    subtable: 17,
                    point: z_rem11_low.clone(),
                    weight: w_q4[1],
                },
                LinearTermExt4::PointEval {
                    subtable: 18,
                    point: z_rem11_low,
                    weight: w_q4[2],
                },
            ],
            rhs: sub.d1b_rem11_proof.rem_leaf_eval,
        },
    ];

    let scale_2048 = Ext4::from_bb(STEP_POST_SCALE as u32);
    for r in 0..3 {
        carry_claims.push(JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: 10 + r,
                    point: z_rc.clone(),
                    weight: scale_2048,
                },
                LinearTermExt4::PointEval {
                    subtable: 9 + r,
                    point: z_rc.clone(),
                    weight: scale_2048.neg(),
                },
                LinearTermExt4::PointEval {
                    subtable: 16 + r,
                    point: z_rc.clone(),
                    weight: Ext4::ONE,
                },
                LinearTermExt4::PointEval {
                    subtable: 13 + r,
                    point: z_rc.clone(),
                    weight: Ext4::ONE.neg(),
                },
            ],
            rhs: Ext4::from_bb((STEP_POST_SCALE / 2) as u32),
        });
    }

    let (sb_ws, sb_wa) = GMaskExt4::build_spec_weights(gm_specs, "cw_sbool", &sb_chals);
    let (lt_ws, lt_wa) = GMaskExt4::build_spec_weights(gm_specs, "cw_ltsh", &lt_chals);
    let (st_ws, st_wa) = GMaskExt4::build_spec_weights(gm_specs, "cw_seltgt", &st_chals);
    if sb_ws.len() != want_gm_len {
        return Err("CarryWeld gm_limb_vars mismatch".into());
    }

    let unm_sb = eq_mle_ext4(&z_sb, &sb_chals).mul(sel_at_sb.mul(sel_at_sb.sub(Ext4::ONE)));
    let unm_lt = eq_mle_ext4(&z_lt_t, &lt_chals[..7])
        .mul(eval_v_shift_kernel_64(&z_lt_v, &lt_chals[7..]))
        .mul(lt_plus_sel_at_r);
    let st_rhs_r = eval_cand_index_mle(&st_chals[7..])
        .add(gamma_sel.mul(sub.cand_vocab_at_r))
        .add(gamma_sel2.mul(sub.shifted_logit_at_r));
    let unm_st = eq_mle_ext4(&z_sel_t, &st_chals[..7]).mul(sub.sel_ind_at_r.mul(st_rhs_r));

    let online_claims = vec![
        JointLinearClaimExt4::point_eval(mult_u16_sub, z_u16, sub.d1b_u16_proof.mult_leaf_eval),
        JointLinearClaimExt4::point_eval(
            mult_rem11_sub,
            z_rem11[..11].to_vec(),
            sub.d1b_rem11_proof.mult_leaf_eval,
        ),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &sb_ws, sub.sel_bool_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_ids,
            &sb_wa,
            sb_rho,
            sb_term.sub(unm_sb),
        ),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &lt_ws, sub.lt_shift_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_ids,
            &lt_wa,
            lt_rho,
            lt_term.sub(unm_lt),
        ),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &st_ws, sub.sel_target_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_ids,
            &st_wa,
            st_rho,
            st_term.sub(unm_st),
        ),
    ];

    Ok((
        carry_claims,
        online_claims,
        (
            pt_q_lp,
            pt_s_lp,
            sub.loop_mxfp4_proof.finals.1,
            sub.loop_mxfp4_proof.finals.2,
        ),
    ))
}

pub fn prove_spec_prefill_carry_weld(
    wit: &SpecPrefillCarryWitness,
    loop_qs: &PrecommittedWhirMxfp4,
) -> Result<SpecPrefillCarryWeldProof, String> {
    let carry_mat = wit.commit_phase1_whir(None);
    let virt_u16 = wit.build_virtual_u16_table();
    let mult_u16 = compute_d1b_multiplicities(&virt_u16, 16)?;
    let virt_rem11 = wit.build_virtual_rem11_table();
    let mult_rem11 = compute_d1b_multiplicities(&virt_rem11, 11)?;

    let gm_specs = vec![
        GMaskSpecExt4::new("cw_sbool", 13, 3),
        GMaskSpecExt4::new("cw_ltsh", 13, 3),
        GMaskSpecExt4::new("cw_seltgt", 13, 3),
    ];
    let mut gm_rng = CShakeRng::from_seed(b"QW35-CARRY-GMASK-V1", &os_random_seed_32());
    let ext_gmask = GMaskExt4::sample(gm_specs.clone(), &mut gm_rng);
    let gm_limbs = ext_gmask.to_four_bb_tables();
    let gm_limb_vars = gm_limbs[0].len().trailing_zeros() as usize;

    // `aux_online_mat` (`0 = mult_u16`, `1 = mult_rem11`, `2..=5 = gm_limbs`):
    let aux_online_mat = WhirCommittedMatrixExt4::commit(
        &[
            &mult_u16,
            &mult_rem11,
            &gm_limbs[0],
            &gm_limbs[1],
            &gm_limbs[2],
            &gm_limbs[3],
        ],
        true,
        None,
    );

    let mut tr = CShakeTranscript::new(b"QW35-SPEC-PREFILL-CARRY-WELD-V1");
    tr.absorb_root(b"cw_root", &carry_mat.root);
    tr.absorb_root(b"cw_aux", &aux_online_mat.root);
    tr.absorb_root(b"cw_qs", &loop_qs.qs_mat.root);
    tr.absorb_u32(b"cw_plen", wit.prompt_tokens.len() as u32);
    for &pt in &wit.prompt_tokens {
        tr.absorb_u32(b"cw_ptok", pt);
    }

    let (
        subproof,
        sel_at_sb,
        strict_lt_at_zlt,
        lt_plus_sel_at_r,
        carry_claims,
        online_claims,
        qs_lp,
    ) = append_carry_weld_prover_transcript(
        wit,
        CarryWeldAuxSlices {
            w_loop_nibs: &loop_qs.nibs_pad,
            w_loop_scs: &loop_qs.scs_pad,
            mult_u16: &mult_u16,
            mult_rem11: &mult_rem11,
        },
        &ext_gmask,
        CarryWeldMaskCfg {
            gm_specs: &gm_specs,
            gm_ids: [2, 3, 4, 5],
            mult_u16_sub: 0,
            mult_rem11_sub: 1,
        },
        &mut tr,
    );

    let qs_claims = vec![
        JointLinearClaimExt4::point_eval(0, qs_lp.0, qs_lp.2),
        JointLinearClaimExt4::point_eval(1, qs_lp.1, qs_lp.3),
    ];

    // `carry_mat` has `w0 = 32,768 == w_max` and `zk == true`, so put it at `m_idx == 0`!
    let whir_batch_proof = open_whir_batch_ext4(
        &[
            (&carry_mat, &carry_claims),
            (&aux_online_mat, &online_claims),
            (&loop_qs.qs_mat, &qs_claims),
        ],
        WHIR_EXT4_T_QUERIES_100,
        &mut tr,
    );

    Ok(SpecPrefillCarryWeldProof {
        prompt_tokens: wit.prompt_tokens.clone(),
        carry_whir_root: carry_mat.root,
        aux_online_root: aux_online_mat.root,
        loop_qs_root: loop_qs.qs_mat.root,
        gm_limb_vars,
        sel_at_sb,
        strict_lt_at_zlt,
        lt_plus_sel_at_r,
        subproof,
        whir_batch_proof,
    })
}

pub fn verify_spec_prefill_carry_weld(
    expected_prompt_tokens: &[u32],
    expected_loop_qs_root: &[u8; 32],
    prf: &SpecPrefillCarryWeldProof,
) -> Result<(), String> {
    if prf.prompt_tokens != expected_prompt_tokens || &prf.loop_qs_root != expected_loop_qs_root {
        return Err("prompt_tokens or loop_qs_root mismatch".into());
    }
    if !(6..=12).contains(&prf.gm_limb_vars) {
        return Err("invalid gm_limb_vars in SpecPrefillCarryWeldProof".into());
    }
    let gm_specs = vec![
        GMaskSpecExt4::new("cw_sbool", 13, 3),
        GMaskSpecExt4::new("cw_ltsh", 13, 3),
        GMaskSpecExt4::new("cw_seltgt", 13, 3),
    ];

    let mut tr = CShakeTranscript::new(b"QW35-SPEC-PREFILL-CARRY-WELD-V1");
    tr.absorb_root(b"cw_root", &prf.carry_whir_root);
    tr.absorb_root(b"cw_aux", &prf.aux_online_root);
    tr.absorb_root(b"cw_qs", &prf.loop_qs_root);
    tr.absorb_u32(b"cw_plen", prf.prompt_tokens.len() as u32);
    for &pt in &prf.prompt_tokens {
        tr.absorb_u32(b"cw_ptok", pt);
    }

    let (carry_claims, online_claims, qs_lp) = replay_carry_weld_verifier_transcript(
        &prf.prompt_tokens,
        &prf.subproof,
        CarryWeldVerifierClaims {
            sel_at_sb: prf.sel_at_sb,
            strict_lt_at_zlt: prf.strict_lt_at_zlt,
            lt_plus_sel_at_r: prf.lt_plus_sel_at_r,
        },
        CarryWeldMaskCfg {
            gm_specs: &gm_specs,
            gm_ids: [2, 3, 4, 5],
            mult_u16_sub: 0,
            mult_rem11_sub: 1,
        },
        1usize << prf.gm_limb_vars,
        &mut tr,
    )?;

    let qs_claims = vec![
        JointLinearClaimExt4::point_eval(0, qs_lp.0, qs_lp.2),
        JointLinearClaimExt4::point_eval(1, qs_lp.1, qs_lp.3),
    ];
    let carry_shape = SpecPrefillCarryWitness::expected_shape();
    let aux_shape = WhirExt4MatrixShape::for_subtables(
        &[
            16,
            11,
            prf.gm_limb_vars,
            prf.gm_limb_vars,
            prf.gm_limb_vars,
            prf.gm_limb_vars,
        ],
        true,
        WHIR_EXT4_BLOWUP,
    );
    let qs_shape = WhirExt4MatrixShape::for_subtables(&[20, 15], false, WHIR_EXT4_BLOWUP);

    verify_whir_batch_ext4(
        &[
            (&prf.carry_whir_root, &carry_shape, &carry_claims),
            (&prf.aux_online_root, &aux_shape, &online_claims),
            (&prf.loop_qs_root, &qs_shape, &qs_claims),
        ],
        WHIR_EXT4_T_QUERIES_100,
        &prf.whir_batch_proof,
        &mut tr,
    )
}

// ================================================================================================
// §4. Gate `G9` + Vertical #2: Post-Countersignature `drand` Beacon & `PayableComputeReceipt`
// ================================================================================================

pub const GDN_LAYER_INDICES_18: [usize; 18] = [
    0, 1, 2, 4, 5, 6, 8, 9, 10, 12, 13, 14, 16, 17, 18, 20, 21, 22,
];

const TRACE_LEAF_DOM: &[u8] = b"QW35-TRACE-MERKLE-LEAF-V1";
const TRACE_NODE_DOM: &[u8] = b"QW35-TRACE-MERKLE-NODE-V1";
const PAYABLE_RECEIPT_MAGIC: &[u8; 8] = b"QW9PAY01";

#[inline]
fn hash_trace_boundary_leaf(chunk_idx: usize, boundary_idx: usize, root: &[u8; 32]) -> [u8; 32] {
    let mut buf = [0u8; 41];
    buf[0] = 0x00; // leaf domain byte
    buf[1..5].copy_from_slice(&(chunk_idx as u32).to_le_bytes());
    buf[5..9].copy_from_slice(&(boundary_idx as u32).to_le_bytes());
    buf[9..41].copy_from_slice(root);
    cshake256_32(TRACE_LEAF_DOM, &buf)
}

fn build_trace_merkle_tree(
    chunk_boundary_roots: &[Vec<[u8; 32]>],
) -> (Vec<Vec<[u8; 32]>>, [u8; 32]) {
    let num_chunks = chunk_boundary_roots.len();
    let raw_count = num_chunks * 25;
    let n_leaves = raw_count.next_power_of_two().max(64);
    let mut leaves = vec![[0u8; 32]; n_leaves];
    for (c, bnds) in chunk_boundary_roots.iter().enumerate() {
        assert_eq!(bnds.len(), 25);
        for (b, r) in bnds.iter().enumerate() {
            leaves[c * 25 + b] = hash_trace_boundary_leaf(c, b, r);
        }
    }
    let mut tree = vec![leaves];
    let mut lvl = 0u8;
    while tree.last().unwrap().len() > 1 {
        let prev = tree.last().unwrap();
        let next: Vec<[u8; 32]> = prev
            .chunks_exact(2)
            .enumerate()
            .map(|(idx, p)| merkle_node_cshake(TRACE_NODE_DOM, lvl, idx as u32, &p[0], &p[1]))
            .collect();
        tree.push(next);
        lvl += 1;
    }
    let root = tree.last().unwrap()[0];
    (tree, root)
}

fn open_trace_merkle_path(tree: &[Vec<[u8; 32]>], leaf_idx: usize) -> MerkleSinglePath {
    let mut siblings = Vec::with_capacity(tree.len() - 1);
    let mut cur = leaf_idx;
    for level in &tree[..tree.len() - 1] {
        siblings.push(level[cur ^ 1]);
        cur >>= 1;
    }
    MerkleSinglePath {
        index: leaf_idx,
        leaf: tree[0][leaf_idx],
        siblings,
    }
}

const CARRY_TREE_DOM: &[u8] = b"QW35-CARRY-TREE-V1";

/// Compact exact-dyadic (`3584 = 2048 + 1024 + 512`) public WHIR commitment for `Qwen3.5-0.8B` `gate_proj`
/// (`[3584, 1024]`): fits in `3,784,704 <= 4,194,304` cells (`rd = 128` rows instead of `256`, saving `67.8 KiB`
/// of zero padding AND hosting the `j < 1024` looped residual `MXFP4` subdomain with `0` extra matrices!).
pub struct CompactWhirMxfp4 {
    pub qs_mat: WhirCommittedMatrixExt4,
    pub j_pad: usize,
    pub k_pad: usize,
    pub nibs_pad: Vec<u8>,
    pub scs_pad: Vec<u32>,
}

impl CompactWhirMxfp4 {
    pub fn build(mat: &Mxfp4Matrix) -> Result<Self, String> {
        if mat.rows_orig != 3584 || mat.cols_orig != 1024 {
            return Err("CompactWhirMxfp4 requires Qwen3.5 [3584, 1024] gate_proj shape".into());
        }
        let (j_pad, k_pad, nibs_pad, scs_pad) = pad_mxfp4_cols_pow2(mat);
        debug_assert_eq!(j_pad, 4096);
        debug_assert_eq!(k_pad, 32);

        let mut q_2048 = vec![0u32; 2048 * k_pad * 32];
        let mut q_1024 = vec![0u32; 1024 * k_pad * 32];
        let mut q_512 = vec![0u32; 512 * k_pad * 32];
        let mut s_2048 = vec![0u32; 2048 * k_pad];
        let mut s_1024 = vec![0u32; 1024 * k_pad];
        let mut s_512 = vec![0u32; 512 * k_pad];

        for j in 0..3584 {
            for k in 0..k_pad {
                let sc = scs_pad[j * k_pad + k];
                let src = (j * k_pad + k) * 32;
                if j < 2048 {
                    s_2048[k * 2048 + j] = sc;
                    let dst = (k * 2048 + j) * 32;
                    for b in 0..32 {
                        q_2048[dst + b] = decode_e2m1_x2_bb(nibs_pad[src + b]);
                    }
                } else if j < 3072 {
                    let j_off = j - 2048;
                    s_1024[k * 1024 + j_off] = sc;
                    let dst = (k * 1024 + j_off) * 32;
                    for b in 0..32 {
                        q_1024[dst + b] = decode_e2m1_x2_bb(nibs_pad[src + b]);
                    }
                } else {
                    let j_off = j - 3072;
                    s_512[k * 512 + j_off] = sc;
                    let dst = (k * 512 + j_off) * 32;
                    for b in 0..32 {
                        q_512[dst + b] = decode_e2m1_x2_bb(nibs_pad[src + b]);
                    }
                }
            }
        }
        let qs_mat = WhirCommittedMatrixExt4::commit(
            &[&q_2048, &q_1024, &q_512, &s_2048, &s_1024, &s_512],
            false,
            None,
        );
        Ok(Self {
            qs_mat,
            j_pad,
            k_pad,
            nibs_pad,
            scs_pad,
        })
    }

    pub fn expected_shape() -> WhirExt4MatrixShape {
        WhirExt4MatrixShape::for_subtables(&[21, 20, 19, 16, 15, 14], false, WHIR_EXT4_BLOWUP)
    }
}

/// Public escrow lease contract aligning `minidregg/Kernel/ProviderExecutionLease.lean` (`Terms`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProviderExecutionLease {
    pub lease_id: [u8; 32],
    pub manifest_root: [u8; 32],
    pub weight_root: [u8; 32],
    pub rom_merkle_root: [u8; 32],
    /// Precommitted WHIR bindings `H(layer_gate_digest || qs_whir_root)` for all 18 GDN layers.
    pub gdn_qs_bindings: [[u8; 32]; 18],
    pub prompt_tokens: Vec<u32>,
    pub num_chunks: usize,
    pub max_units: u64,
    pub unit_price: u64,
    pub base_fee: u64,
    pub expiry_round: u64,
    /// Minimum post-countersignature `drand` round advance (`>= 1`, `target_beacon_round = round_commit + beacon_delay`).
    pub beacon_delay: u64,
    pub drand_group_pk_g2: [u8; 96],
    pub provider_pk: WotsPublicKey,
    pub escrow_pk: WotsPublicKey,
}

impl ProviderExecutionLease {
    pub fn prepaid_budget(&self) -> u128 {
        (self.base_fee as u128) + (self.max_units as u128) * (self.unit_price as u128)
    }

    pub fn prompt_root(&self) -> [u8; 32] {
        let mut buf = Vec::with_capacity(4 + self.prompt_tokens.len() * 4);
        buf.extend_from_slice(&(self.prompt_tokens.len() as u32).to_le_bytes());
        for &t in &self.prompt_tokens {
            buf.extend_from_slice(&t.to_le_bytes());
        }
        cshake256_32(b"QW35-LEASE-PROMPT-ROOT-V1", &buf)
    }

    /// Canonical `provider_invocation_key` (`ProviderExecutionLease.lean:413`).
    pub fn invocation_key(&self) -> [u8; 32] {
        let mut buf = Vec::with_capacity(200);
        buf.extend_from_slice(&self.lease_id);
        buf.extend_from_slice(&self.manifest_root);
        buf.extend_from_slice(&self.weight_root);
        buf.extend_from_slice(&self.rom_merkle_root);
        buf.extend_from_slice(&self.prompt_root());
        buf.extend_from_slice(&self.max_units.to_le_bytes());
        buf.extend_from_slice(&self.unit_price.to_le_bytes());
        buf.extend_from_slice(&self.base_fee.to_le_bytes());
        buf.extend_from_slice(&self.expiry_round.to_le_bytes());
        buf.extend_from_slice(&self.beacon_delay.to_le_bytes());
        cshake256_32(b"QW35-PROVIDER-INVOCATION-KEY-V1", &buf)
    }
}

/// Phase-1 Provider Turn Commitment (signed **BEFORE** `round_commit` and **BEFORE** `drand` beacon!).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProviderTurnCommitment {
    pub lease_id: [u8; 32],
    pub run_id: [u8; 32],
    pub claimed_units: u64,
    pub word_len: usize,
    pub final_dfa_state: u8,
    pub content_root: [u8; 32],
    pub trace_merkle_root: [u8; 32],
    pub byte_root: [u8; 32],
    pub bpe_weld_root: [u8; 32],
    pub carry_weld_root: [u8; 32],
    pub usage_root: [u8; 32],
    pub provider_sig: WotsSignature,
}

impl ProviderTurnCommitment {
    pub fn body_digest(&self) -> [u8; 32] {
        let mut buf = Vec::with_capacity(280);
        buf.extend_from_slice(&self.lease_id);
        buf.extend_from_slice(&self.run_id);
        buf.extend_from_slice(&self.claimed_units.to_le_bytes());
        buf.extend_from_slice(&(self.word_len as u32).to_le_bytes());
        buf.push(self.final_dfa_state);
        for r in [
            &self.content_root,
            &self.trace_merkle_root,
            &self.byte_root,
            &self.bpe_weld_root,
            &self.carry_weld_root,
            &self.usage_root,
        ] {
            buf.extend_from_slice(r);
        }
        cshake256_32(b"QW35-PROVIDER-TURN-COMMIT-V1", &buf)
    }

    pub fn provider_evidence_root(&self) -> [u8; 32] {
        let inner = merkle_node_cshake(
            b"QW35-PROVIDER-EVIDENCE-V1",
            0,
            0,
            &self.content_root,
            &self.usage_root,
        );
        merkle_node_cshake(b"QW35-PROVIDER-EVIDENCE-V1", 1, 0, &self.run_id, &inner)
    }

    pub fn write_to(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.lease_id);
        out.extend_from_slice(&self.run_id);
        out.extend_from_slice(&self.claimed_units.to_le_bytes());
        out.extend_from_slice(&(self.word_len as u32).to_le_bytes());
        out.push(self.final_dfa_state);
        for r in [
            &self.content_root,
            &self.trace_merkle_root,
            &self.byte_root,
            &self.bpe_weld_root,
            &self.carry_weld_root,
            &self.usage_root,
        ] {
            out.extend_from_slice(r);
        }
        self.provider_sig.write_to(out);
    }

    pub fn read_from(cur: &mut ByteCursor<'_>) -> Result<Self, String> {
        let lease_id = cur.read_arr32()?;
        let run_id = cur.read_arr32()?;
        let claimed_units = read_u64_le(cur)?;
        let word_len = cur.read_u32()? as usize;
        let final_dfa_state = cur.read_u8()?;
        let content_root = cur.read_arr32()?;
        let trace_merkle_root = cur.read_arr32()?;
        let byte_root = cur.read_arr32()?;
        let bpe_weld_root = cur.read_arr32()?;
        let carry_weld_root = cur.read_arr32()?;
        let usage_root = cur.read_arr32()?;
        let provider_sig = WotsSignature::read_from(cur)?;
        Ok(Self {
            lease_id,
            run_id,
            claimed_units,
            word_len,
            final_dfa_state,
            content_root,
            trace_merkle_root,
            byte_root,
            bpe_weld_root,
            carry_weld_root,
            usage_root,
            provider_sig,
        })
    }
}

/// Phase-2 Requester / Escrow Countersignature pinning `round_commit` and `target_beacon_round > round_commit`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EscrowCountersignature {
    pub commitment_digest: [u8; 32],
    pub round_commit: u64,
    pub target_beacon_round: u64,
    pub escrow_sig: WotsSignature,
}

impl EscrowCountersignature {
    pub fn signing_message(
        lease_id: &[u8; 32],
        commitment_digest: &[u8; 32],
        round_commit: u64,
        target_beacon_round: u64,
    ) -> [u8; 80] {
        let mut msg = [0u8; 80];
        msg[0..32].copy_from_slice(lease_id);
        msg[32..64].copy_from_slice(commitment_digest);
        msg[64..72].copy_from_slice(&round_commit.to_le_bytes());
        msg[72..80].copy_from_slice(&target_beacon_round.to_le_bytes());
        msg
    }

    pub fn sign(
        lease: &ProviderExecutionLease,
        commit: &ProviderTurnCommitment,
        round_commit: u64,
        escrow_kp: &WotsKeypair,
    ) -> Result<Self, String> {
        if lease.beacon_delay == 0 {
            return Err("lease.beacon_delay must be >= 1".into());
        }
        if commit.lease_id != lease.lease_id {
            return Err("commit.lease_id != lease.lease_id".into());
        }
        verify_wots_signature(
            &lease.provider_pk,
            &commit.body_digest(),
            &commit.provider_sig,
        )?;
        let target_beacon_round = round_commit
            .checked_add(lease.beacon_delay)
            .ok_or_else(|| "round_commit + beacon_delay overflow".to_string())?;
        if target_beacon_round > lease.expiry_round {
            return Err("target_beacon_round exceeds lease.expiry_round".into());
        }
        let commitment_digest = commit.body_digest();
        let msg = Self::signing_message(
            &lease.lease_id,
            &commitment_digest,
            round_commit,
            target_beacon_round,
        );
        let escrow_sig = escrow_kp.sign(&msg);
        Ok(Self {
            commitment_digest,
            round_commit,
            target_beacon_round,
            escrow_sig,
        })
    }

    pub fn write_to(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.commitment_digest);
        out.extend_from_slice(&self.round_commit.to_le_bytes());
        out.extend_from_slice(&self.target_beacon_round.to_le_bytes());
        self.escrow_sig.write_to(out);
    }

    pub fn read_from(cur: &mut ByteCursor<'_>) -> Result<Self, String> {
        let commitment_digest = cur.read_arr32()?;
        let round_commit = read_u64_le(cur)?;
        let target_beacon_round = read_u64_le(cur)?;
        let escrow_sig = WotsSignature::read_from(cur)?;
        Ok(Self {
            commitment_digest,
            round_commit,
            target_beacon_round,
            escrow_sig,
        })
    }
}

/// Deterministic post-countersignature `drand` audit selector -> `(gdn_slot_0..18, audited_layer, audited_chunk)`.
pub fn derive_post_countersig_audit_target(
    lease_id: &[u8; 32],
    commitment_digest: &[u8; 32],
    countersig: &EscrowCountersignature,
    beacon: &DrandQuicknetBeacon,
    num_chunks: usize,
) -> (usize, usize, usize) {
    let mut buf = [0u8; 112];
    buf[0..32].copy_from_slice(lease_id);
    buf[32..64].copy_from_slice(commitment_digest);
    buf[64..72].copy_from_slice(&countersig.round_commit.to_le_bytes());
    buf[72..80].copy_from_slice(&beacon.round.to_le_bytes());
    buf[80..112].copy_from_slice(&beacon.randomness);
    let sel = cshake256_32(b"QW35-POST-COUNTERSIG-AUDIT-SELECT-V1", &buf);
    let w0 = u64::from_le_bytes(sel[0..8].try_into().unwrap()) as usize;
    let w1 = u64::from_le_bytes(sel[8..16].try_into().unwrap()) as usize;
    let gdn_slot = w0 % GDN_LAYER_INDICES_18.len();
    let audited_layer = GDN_LAYER_INDICES_18[gdn_slot];
    let audited_chunk = w1 % num_chunks.max(1);
    (gdn_slot, audited_layer, audited_chunk)
}

/// Conserved escrow settlement outcome (`paid + refunded == lease.prepaid_budget()`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeaseSettlement {
    pub paid: u128,
    pub refunded: u128,
    pub provider_invocation_key: [u8; 32],
    pub provider_evidence_root: [u8; 32],
    pub audited_gdn_layer: usize,
    pub audited_token_chunk: usize,
    pub expired_refund_only: bool,
}

/// Deterministic timeout refund when `current_round > lease.expiry_round` (`0` payout, `100%` refund!).
pub fn settle_expired_lease_refund(
    lease: &ProviderExecutionLease,
    current_round: u64,
) -> Result<LeaseSettlement, String> {
    if current_round <= lease.expiry_round {
        return Err("cannot claim timeout refund before lease.expiry_round has elapsed".into());
    }
    Ok(LeaseSettlement {
        paid: 0,
        refunded: lease.prepaid_budget(),
        provider_invocation_key: lease.invocation_key(),
        provider_evidence_root: [0u8; 32],
        audited_gdn_layer: 0,
        audited_token_chunk: 0,
        expired_refund_only: true,
    })
}

/// Prover-side Phase-1 state held across countersignature and `drand` reveal.
pub struct ProviderPhase1State {
    pub commitment: ProviderTurnCommitment,
    pub generated_tokens: Vec<u32>,
    pub raw_output_bytes: Vec<u8>,
    pub chunk_tokens: Vec<Vec<u32>>,
    pub chunk_boundary_mats: Vec<Vec<WhirCommittedMatrixExt4>>,
    pub trace_tree: Vec<Vec<[u8; 32]>>,
    pub byte_commit: SaltedByteWhirCommitment,
    pub bpe_phase1_cols: [Vec<u32>; 5],
    pub carry_witnesses: Vec<SpecPrefillCarryWitness>,
    pub turn_weld_mats: Vec<WhirCommittedMatrixExt4>,
    pub carry_weld_tree: Vec<Vec<[u8; 32]>>,
}

pub fn compute_bpe_weld_root_v1(
    word_len: usize,
    num_generated_tokens: usize,
    carry_weld_root: &[u8; 32],
) -> [u8; 32] {
    let mut buf = [0u8; 48];
    buf[0..8].copy_from_slice(&(word_len as u64).to_le_bytes());
    buf[8..16].copy_from_slice(&(num_generated_tokens as u64).to_le_bytes());
    buf[16..48].copy_from_slice(carry_weld_root);
    cshake256_32(b"QW35-BPE-WELD-ROOT-V1", &buf)
}

fn build_carry_merkle_tree(slot_roots: &[[u8; 32]]) -> (Vec<Vec<[u8; 32]>>, [u8; 32]) {
    assert_eq!(slot_roots.len(), GDN_LAYER_INDICES_18.len());
    let mut leaves = Vec::with_capacity(32);
    for (s, r) in slot_roots.iter().enumerate() {
        let mut buf = [0u8; 36];
        buf[0..4].copy_from_slice(&(s as u32).to_le_bytes());
        buf[4..36].copy_from_slice(r);
        leaves.push(cshake256_32(b"QW35-CARRY-LEAF-V1", &buf));
    }
    leaves.resize(32, [0u8; 32]);
    let mut tree = vec![leaves];
    let mut lvl = 0u8;
    while tree.last().unwrap().len() > 1 {
        let prev = tree.last().unwrap();
        let next: Vec<[u8; 32]> = prev
            .chunks_exact(2)
            .enumerate()
            .map(|(idx, p)| merkle_node_cshake(CARRY_TREE_DOM, lvl, idx as u32, &p[0], &p[1]))
            .collect();
        tree.push(next);
        lvl += 1;
    }
    let root = tree.last().unwrap()[0];
    (tree, root)
}

#[inline]
fn hash_carry_slot_leaf(slot: usize, whir_root: &[u8; 32]) -> [u8; 32] {
    let mut buf = [0u8; 36];
    buf[0..4].copy_from_slice(&(slot as u32).to_le_bytes());
    buf[4..36].copy_from_slice(whir_root);
    cshake256_32(b"QW35-CARRY-LEAF-V1", &buf)
}

#[inline]
fn eval_packed_ext4_limb_consts() -> (Ext4, Ext4, Ext4) {
    let x = Ext4([0, 1, 0, 0]);
    let x2 = Ext4([0, 0, 1, 0]);
    let one_p_x = Ext4::ONE.add(x);
    let one_p_x2 = Ext4::ONE.add(x2);
    let zb0 = x.mul(one_p_x.inv().unwrap());
    let zb1 = x2.mul(one_p_x2.inv().unwrap());
    let scale = one_p_x.mul(one_p_x2);
    (zb0, zb1, scale)
}

#[inline]
fn eval_ext4_vec_mle(col: &[Ext4], pt: &[Ext4]) -> Ext4 {
    let eq = build_eq_table_lsb_ext4(pt);
    let mut acc = Ext4::ZERO;
    for (&w, &v) in eq.iter().zip(col.iter()) {
        acc = acc.add(w.mul(v));
    }
    acc
}

/// L1-cached `u64` MADD verifier for `D1bExt4TableProof` against `QwenBpeRom` (`0` `Ext4` muls per token, `< 1 ms`!).
fn verify_d1b_qwen_rom_fast(
    rom: &QwenBpeRom,
    beta_ext4: Ext4,
    gammas: [Ext4; 4],
    proof: &D1bExt4TableProof,
    tr: &mut CShakeTranscript,
) -> Result<Vec<Ext4>, String> {
    if proof.m_tab != ROM_LOG_SIZE
        || proof.m_wit > proof.m_tab
        || proof.root_q.is_zero()
        || proof.layers.len() != proof.m_tab + 1
    {
        return Err("D1bExt4TableProof ROM dimension/header mismatch".into());
    }
    let alpha = tr.squeeze_ext4(b"d1b_rom_alpha", true);
    tr.absorb_ext4(b"d1b_rom_root_q", proof.root_q);

    let mut cur_pt: Vec<Ext4> = Vec::new();
    let mut cur_p_claim = Ext4::ZERO;
    let mut cur_q_claim = proof.root_q;

    for (step, lyr) in proof.layers.iter().enumerate() {
        if lyr.rounds.len() != step {
            return Err(format!(
                "D1bExt4TableProof round count mismatch at step {step}"
            ));
        }
        let eta = tr.squeeze_ext4(b"d1b_rom_eta", true);
        let mut sigma = cur_p_claim.add(eta.mul(cur_q_claim));
        let mut sum_chals = Vec::with_capacity(step);

        for (r_idx, msg) in lyr.rounds.iter().enumerate() {
            if msg.p0.add(msg.p1) != sigma {
                return Err(format!(
                    "D1bExt4TableProof sumcheck failed at {step}:{r_idx}"
                ));
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
            return Err(format!(
                "D1bExt4TableProof layer fold failed at step {step}"
            ));
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

    let eq_tab = build_eq_table_lsb_ext4(z_tab);
    let max_len = rom.max_token_byte_len;
    let c0 = eval_bytes_ext4(beta_ext4, &[0u8]);
    let slope = eval_bytes_ext4(beta_ext4, &[1u8]).sub(c0);
    let g3_slope = gammas[3].mul(slope);

    let mut pows = Vec::with_capacity(max_len + 1);
    let mut c_lens = Vec::with_capacity(max_len + 1);
    let mut cp = Ext4::ONE;
    let mut c_run = Ext4::ZERO;
    for _ in 0..=max_len {
        pows.push(cp);
        c_lens.push(c_run);
        c_run = c_run.add(c0.mul(cp));
        cp = cp.mul(beta_ext4);
    }
    let len_const_tup: Vec<Ext4> = (0..=max_len)
        .map(|l| {
            gammas[1]
                .scale_bb(l as u32)
                .add(gammas[2].mul(pows[l]))
                .add(gammas[3].mul(c_lens[l]))
        })
        .collect();
    let pos_weights: Vec<Ext4> = (0..max_len).map(|k| g3_slope.mul(pows[k])).collect();
    let pad_tuple = Ext4::from_bb(PAD_TOK_ID).add(gammas[0]).add(gammas[2]);
    let p_u64 = P;

    // 32 parallel chunks of `8,192` slots (`8192 * 248320 * 2.01e9 = 4.1e18 < u64::MAX`, `0` inner `% P` or `Ext4` muls!):
    let rom_ev = (0..32usize)
        .into_par_iter()
        .map(|ch_idx| {
            let base = ch_idx * 8192;
            let end = base + 8192;
            let mut slot_acc = [0u64; 4];
            let mut pad_acc = Ext4::ZERO;
            let mut len_buckets = vec![Ext4::ZERO; max_len + 1];
            let mut pos_acc = vec![[0u64; 4]; max_len];

            for (slot, &w) in eq_tab.iter().enumerate().take(end).skip(base) {
                if slot < QWEN_DEFINED_TOKENS && rom.is_defined[slot] {
                    let s_u64 = slot as u64;
                    slot_acc[0] += (w.0[0] as u64) * s_u64;
                    slot_acc[1] += (w.0[1] as u64) * s_u64;
                    slot_acc[2] += (w.0[2] as u64) * s_u64;
                    slot_acc[3] += (w.0[3] as u64) * s_u64;

                    let st = rom.byte_offsets[slot] as usize;
                    let en = rom.byte_offsets[slot + 1] as usize;
                    let bs = &rom.flat_bytes[st..en];
                    let len = bs.len();
                    len_buckets[len] = len_buckets[len].add(w);
                    for k in 0..len {
                        let b = bs[len - 1 - k] as u64;
                        let pa = &mut pos_acc[k];
                        pa[0] += (w.0[0] as u64) * b;
                        pa[1] += (w.0[1] as u64) * b;
                        pa[2] += (w.0[2] as u64) * b;
                        pa[3] += (w.0[3] as u64) * b;
                    }
                } else {
                    pad_acc = pad_acc.add(w);
                }
            }

            let mut out = Ext4([
                (slot_acc[0] % p_u64) as u32,
                (slot_acc[1] % p_u64) as u32,
                (slot_acc[2] % p_u64) as u32,
                (slot_acc[3] % p_u64) as u32,
            ])
            .add(pad_acc.mul(pad_tuple));
            for l in 0..=max_len {
                out = out.add(len_buckets[l].mul(len_const_tup[l]));
            }
            for k in 0..max_len {
                let pa = &pos_acc[k];
                let pe = Ext4([
                    (pa[0] % p_u64) as u32,
                    (pa[1] % p_u64) as u32,
                    (pa[2] % p_u64) as u32,
                    (pa[3] % p_u64) as u32,
                ]);
                out = out.add(pe.mul(pos_weights[k]));
            }
            out
        })
        .reduce(|| Ext4::ZERO, |a, b| a.add(b));

    let expected_p = eq_lin_ext4(z_side, Ext4::ZERO)
        .mul(subdomain_wit_zero)
        .add(eq_lin_ext4(z_side, Ext4::ONE).mul(proof.mult_leaf_eval.neg()));
    let expected_q = eq_lin_ext4(z_side, Ext4::ZERO)
        .mul(alpha.sub(proof.wit_leaf_eval))
        .add(eq_lin_ext4(z_side, Ext4::ONE).mul(alpha.sub(rom_ev)));
    if cur_p_claim != expected_p || cur_q_claim != expected_q {
        return Err("D1bExt4TableProof leaf witness/ROM equation mismatch".into());
    }
    Ok(z_tab.to_vec())
}

/// Build linear weights `w_horner[0..pad_len]` and scalar offset `c_sum` such that for ANY byte array
/// `bs[0..word_len]`, `<w_horner, bytes_pad> + c_sum == eval_bytes_ext4(beta_ext4, bs)`!
fn build_horner_byte_weights(
    beta_ext4: Ext4,
    word_len: usize,
    pad_len: usize,
) -> (Vec<Ext4>, Ext4) {
    let c0 = eval_bytes_ext4(beta_ext4, &[0u8]);
    let slope = eval_bytes_ext4(beta_ext4, &[1u8]).sub(c0);
    let mut weights = vec![Ext4::ZERO; pad_len];
    let mut cur_pow = Ext4::ONE;
    let mut c_sum = Ext4::ZERO;
    for rev in 0..word_len {
        let j = word_len - 1 - rev;
        weights[j] = slope.mul(cur_pow);
        c_sum = c_sum.add(c0.mul(cur_pow));
        cur_pow = cur_pow.mul(beta_ext4);
    }
    (weights, c_sum)
}

fn eval_shift_kernel_128(z: &[Ext4], u_pt: &[Ext4]) -> Ext4 {
    let eq_z = build_eq_table_lsb_ext4(z);
    let eq_u = build_eq_table_lsb_ext4(u_pt);
    let n = eq_z.len();
    let mut acc = Ext4::ZERO;
    for t in 0..(n - 1) {
        acc = acc.add(eq_z[t].mul(eq_u[t + 1]));
    }
    acc
}

fn eval_non_slt_mask_mle_local(z_i: &[Ext4], z_j: &[Ext4]) -> Ext4 {
    let eq_i = build_eq_table_lsb_ext4(z_i);
    let eq_j = build_eq_table_lsb_ext4(z_j);
    let mut acc = Ext4::ZERO;
    for (j, &eq_jv) in eq_j.iter().enumerate() {
        let mut s_i = Ext4::ZERO;
        for &eq_iv in &eq_i[..=j] {
            s_i = s_i.add(eq_iv);
        }
        acc = acc.add(eq_jv.mul(s_i));
    }
    acc
}

/// Phase-1 Provider Commit: executes the `128`-token (`2 x 64`) `Qwen3.5-0.8B` turn and commits
/// `(trace_merkle_root, byte_root, bpe_weld_root, carry_weld_root)` **BEFORE** countersignature & `drand`!
#[allow(clippy::too_many_arguments)]
pub fn provider_commit_turn_phase1(
    lease: &ProviderExecutionLease,
    rom: &QwenBpeRom,
    chunk_boundaries_bb: Vec<Vec<Vec<u32>>>,
    chunk_tokens: Vec<Vec<u32>>,
    generated_tokens: Vec<u32>,
    gdn_loop_mats: &[Mxfp4Matrix],
    run_id: [u8; 32],
    claimed_units: u64,
    provider_kp: &WotsKeypair,
) -> Result<ProviderPhase1State, String> {
    if chunk_boundaries_bb.len() != lease.num_chunks || chunk_tokens.len() != lease.num_chunks {
        return Err("chunk count mismatch against lease.num_chunks".into());
    }
    if gdn_loop_mats.len() != GDN_LAYER_INDICES_18.len() {
        return Err("gdn_loop_mats must provide all 18 GDN [1024, 1024] loop submatrices".into());
    }
    if claimed_units > lease.max_units {
        return Err("claimed_units exceeds lease.max_units".into());
    }
    let k_gen = generated_tokens.len();
    if lease.prompt_tokens.len() + k_gen != CARRY_TURN_TOKENS + 1 {
        return Err("prompt_tokens.len() + generated_tokens.len() must equal 129".into());
    }

    // 1. Detokenize `generated_tokens` & run `Absent("sk-...")` check + Canonical Salted Byte PCS (`pad >= 2048`):
    let raw_output_bytes = rom.detokenize(&generated_tokens)?;
    let (final_dfa_state, _) = run_padded_complement_sk_dfa(&raw_output_bytes);
    if final_dfa_state >= 4 {
        return Err("prover refusal: output enters Absent(\"sk-...\") sink state 4".into());
    }
    let byte_commit = SaltedByteWhirCommitment::commit_canonical(&raw_output_bytes, None)?;

    // 2. Commit all `num_chunks * 25` `U1` boundary WHIR matrices -> `trace_merkle_root`:
    let mut chunk_boundary_mats = Vec::with_capacity(lease.num_chunks);
    let mut chunk_boundary_roots = Vec::with_capacity(lease.num_chunks);
    for bnds in &chunk_boundaries_bb {
        if bnds.len() != 25 {
            return Err("each chunk must have 25 U1 boundaries".into());
        }
        let mats: Vec<WhirCommittedMatrixExt4> = bnds
            .par_iter()
            .map(|b| WhirCommittedMatrixExt4::commit(&[b.as_slice()], true, None))
            .collect();
        let roots: Vec<[u8; 32]> = mats.iter().map(|m| m.root).collect();
        chunk_boundary_roots.push(roots);
        chunk_boundary_mats.push(mats);
    }
    let (trace_tree, trace_merkle_root) = build_trace_merkle_tree(&chunk_boundary_roots);

    // 3. Build Phase-1 BPE columns (`tok_col, is_pad_col, len_col, cum_len_col, cum_len_next_col`, `128` slots):
    let mut tok_col = vec![PAD_TOK_ID; CARRY_TURN_TOKENS];
    let mut is_pad_col = vec![1u32; CARRY_TURN_TOKENS];
    let mut len_col = vec![0u32; CARRY_TURN_TOKENS];
    let mut cum_len_col = vec![0u32; CARRY_TURN_TOKENS];
    let mut cum_len_next_col = vec![0u32; CARRY_TURN_TOKENS];
    let mut running_len = 0u32;
    for i in 0..CARRY_TURN_TOKENS {
        cum_len_col[i] = running_len;
        if i < k_gen {
            let tid = generated_tokens[i];
            let bs = rom.token_bytes(tid)?;
            tok_col[i] = tid;
            is_pad_col[i] = 0;
            len_col[i] = bs.len() as u32;
            running_len += bs.len() as u32;
        }
        cum_len_next_col[i] = running_len;
    }
    debug_assert_eq!(running_len as usize, raw_output_bytes.len());
    let bpe_phase1_cols = [tok_col, is_pad_col, len_col, cum_len_col, cum_len_next_col];

    // 4. Commit unified Phase-1 `turn_weld_mats[0..18]` (`SpecPrefill` + `R = 3` Looped Carry + BPE) -> `(carry_weld_root, bpe_weld_root)`:
    let base_carry = SpecPrefillCarryWitness::build(
        &lease.prompt_tokens,
        &generated_tokens,
        &chunk_boundaries_bb[0][GDN_LAYER_INDICES_18[0]],
        &gdn_loop_mats[0],
    )?;
    let mut carry_witnesses = Vec::with_capacity(GDN_LAYER_INDICES_18.len());
    carry_witnesses.push(base_carry);
    for s in 1..GDN_LAYER_INDICES_18.len() {
        let l_idx = GDN_LAYER_INDICES_18[s];
        carry_witnesses.push(
            carry_witnesses[0]
                .with_loop_weight(&chunk_boundaries_bb[0][l_idx], &gdn_loop_mats[s])?,
        );
    }
    let turn_weld_mats: Vec<WhirCommittedMatrixExt4> = carry_witnesses
        .par_iter()
        .map(|cw| cw.commit_phase1_with_bpe_whir(&bpe_phase1_cols, None))
        .collect();
    let slot_roots: Vec<[u8; 32]> = turn_weld_mats.iter().map(|m| m.root).collect();
    let (carry_weld_tree, carry_weld_root) = build_carry_merkle_tree(&slot_roots);
    let bpe_weld_root = compute_bpe_weld_root_v1(raw_output_bytes.len(), k_gen, &carry_weld_root);

    let mut usage_in = [0u8; 16];
    usage_in[0..8].copy_from_slice(&claimed_units.to_le_bytes());
    usage_in[8..16].copy_from_slice(&(k_gen as u64).to_le_bytes());
    let usage_root = cshake256_32(b"QW35-USAGE-ROOT-V1", &usage_in);

    let mut commitment = ProviderTurnCommitment {
        lease_id: lease.lease_id,
        run_id,
        claimed_units,
        word_len: raw_output_bytes.len(),
        final_dfa_state,
        content_root: byte_commit.content_root,
        trace_merkle_root,
        byte_root: byte_commit.whir_mat.root,
        bpe_weld_root,
        carry_weld_root,
        usage_root,
        provider_sig: WotsSignature {
            pub_seed: provider_kp.pk.pub_seed,
            chains: [[0u8; 32]; WOTS_CHAINS],
        },
    };
    commitment.provider_sig = provider_kp.sign(&commitment.body_digest());

    Ok(ProviderPhase1State {
        commitment,
        generated_tokens,
        raw_output_bytes,
        chunk_tokens,
        chunk_boundary_mats,
        trace_tree,
        byte_commit,
        bpe_phase1_cols,
        carry_witnesses,
        turn_weld_mats,
        carry_weld_tree,
    })
}

/// Complete compressed Flagship Vertical #2 Receipt (`< 650 KiB`, `< 25 ms` standalone verify).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PayableComputeReceipt {
    pub commitment: ProviderTurnCommitment,
    pub countersig: EscrowCountersignature,
    pub beacon: DrandQuicknetBeacon,
    pub audited_gdn_slot: usize,
    pub audited_layer: usize,
    pub audited_chunk: usize,
    pub num_generated_tokens: usize,
    pub byte_pad_len: usize,
    pub byte_gm_limb_vars: usize,
    pub online_gm_limb_vars: usize,

    pub b_in_whir_root: [u8; 32],
    pub b_out_whir_root: [u8; 32],
    pub b_in_trace_path: MerkleSinglePath,
    pub b_out_trace_path: MerkleSinglePath,
    pub carry_slot_whir_root: [u8; 32],
    pub carry_weld_path: MerkleSinglePath,

    pub layer_weight_path: MerkleSinglePath,
    pub layer_tensor_digests: Vec<[u8; 32]>,
    pub gate_proj_tensor_slot: usize,
    pub qs_whir_root: [u8; 32],
    pub online_whir_root: [u8; 32],

    // Audited `U1 + WY + Consolidated [UW, RHS, rem, L, b, q] D1b + MXFP4` scalars & subproofs:
    pub rhs_eval_at_z: Ext4,
    pub uw_eval_at_z: Ext4,
    pub rem_eval_at_z: Ext4,
    pub wy_l_eval: Ext4,
    pub wy_uw_eval: Ext4,
    pub wy_blinded_sc: BlindedEinSumExt4Proof,
    pub slt_blinded_sc: BlindedEinSumExt4Proof,
    pub d1b_wy8192_proof: D1bRangeExt4Proof,
    pub b_at_zwy8192: Ext4,
    pub mxfp4_proof: Mxfp4DelayedBjkExt4Proof,
    pub b_in_eval: Ext4,
    pub b_out_eval: Ext4,
    pub delta_gdn_eval: Ext4,
    pub delta_mlp_eval: Ext4,

    // Unified Salted Byte PCS `Absent("sk-...")` subproofs:
    pub dfa_d1b_proof: D1bRangeExt4Proof,
    pub q_at_dfa_leaf: Ext4,
    pub b_at_dfa_leaf: Ext4,
    pub q_next_at_dfa_leaf: Ext4,
    pub eof_blinded_sc: BlindedEinSumExt4Proof,
    pub q_next_at_zsh: Ext4,
    pub shift_blinded_sc: BlindedEinSumExt4Proof,

    // Post-commitment `248,320`-vocab `QwenBpeRom` token-to-byte weld subproofs:
    pub final_acc_ext4: Ext4,
    pub rom_d1b_proof: D1bExt4TableProof,
    pub tok_at_zrom: Ext4,
    pub is_pad_at_zrom: Ext4,
    pub len_at_zrom: Ext4,
    pub pow_at_zrom: Ext4,
    pub val_at_zrom: Ext4,
    pub acc_next_at_zacc: Ext4,
    pub val_at_zacc: Ext4,
    pub bpe_acc_sc: BlindedEinSumExt4Proof,
    pub acc_at_racc: Ext4,
    pub pow_at_racc: Ext4,
    pub acc_next_at_zash: Ext4,
    pub bpe_acc_shift_sc: BlindedEinSumExt4Proof,
    pub cum_next_at_zcsh: Ext4,
    pub emit_tok_eval: Ext4,

    // Autoregressive `SpecPrefill` Token-Carry & Looped Residual-Carry subproofs:
    pub cw_sel_at_sb: Ext4,
    pub cw_strict_lt_at_zlt: Ext4,
    pub cw_lt_plus_sel_at_r: Ext4,
    pub carry_subproof: CarryWeldSubproof,

    /// ONE shared subdomain-lifted `WhirBatchOpeningProofExt4` opening ALL 6 WHIR matrices!
    pub whir_batch_proof: WhirBatchOpeningProofExt4,
}

fn write_single_path(p: &MerkleSinglePath, out: &mut Vec<u8>) {
    out.extend_from_slice(&(p.index as u32).to_le_bytes());
    out.extend_from_slice(&p.leaf);
    out.extend_from_slice(&(p.siblings.len() as u32).to_le_bytes());
    for s in &p.siblings {
        out.extend_from_slice(s);
    }
}

fn read_single_path(cur: &mut ByteCursor<'_>) -> Result<MerkleSinglePath, String> {
    let index = cur.read_u32()? as usize;
    let leaf = cur.read_arr32()?;
    let n = cur.read_u32()? as usize;
    if n > 32 {
        return Err("MerkleSinglePath depth > 32".into());
    }
    let mut siblings = Vec::with_capacity(n);
    for _ in 0..n {
        siblings.push(cur.read_arr32()?);
    }
    Ok(MerkleSinglePath {
        index,
        leaf,
        siblings,
    })
}

impl PayableComputeReceipt {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(600 * 1024);
        out.extend_from_slice(PAYABLE_RECEIPT_MAGIC);
        self.commitment.write_to(&mut out);
        self.countersig.write_to(&mut out);
        self.beacon.write_to(&mut out);

        for v in [
            self.audited_gdn_slot,
            self.audited_layer,
            self.audited_chunk,
            self.num_generated_tokens,
            self.byte_pad_len,
            self.byte_gm_limb_vars,
            self.online_gm_limb_vars,
            self.gate_proj_tensor_slot,
        ] {
            out.extend_from_slice(&(v as u32).to_le_bytes());
        }
        for r in [
            &self.b_in_whir_root,
            &self.b_out_whir_root,
            &self.qs_whir_root,
            &self.online_whir_root,
            &self.carry_slot_whir_root,
        ] {
            out.extend_from_slice(r);
        }
        write_single_path(&self.b_in_trace_path, &mut out);
        write_single_path(&self.b_out_trace_path, &mut out);
        write_single_path(&self.carry_weld_path, &mut out);
        write_single_path(&self.layer_weight_path, &mut out);

        out.extend_from_slice(&(self.layer_tensor_digests.len() as u32).to_le_bytes());
        for d in &self.layer_tensor_digests {
            out.extend_from_slice(d);
        }

        pack_ext4_slice(
            &[
                self.rhs_eval_at_z,
                self.uw_eval_at_z,
                self.rem_eval_at_z,
                self.wy_l_eval,
                self.wy_uw_eval,
                self.b_in_eval,
                self.b_out_eval,
                self.delta_gdn_eval,
                self.delta_mlp_eval,
                self.q_at_dfa_leaf,
                self.b_at_dfa_leaf,
                self.q_next_at_dfa_leaf,
                self.q_next_at_zsh,
                self.b_at_zwy8192,
                self.final_acc_ext4,
                self.tok_at_zrom,
                self.is_pad_at_zrom,
                self.len_at_zrom,
                self.pow_at_zrom,
                self.val_at_zrom,
                self.acc_next_at_zacc,
                self.val_at_zacc,
                self.acc_at_racc,
                self.pow_at_racc,
                self.acc_next_at_zash,
                self.cum_next_at_zcsh,
                self.emit_tok_eval,
                self.cw_sel_at_sb,
                self.cw_strict_lt_at_zlt,
                self.cw_lt_plus_sel_at_r,
            ],
            &mut out,
        );

        self.wy_blinded_sc.write_to(&mut out);
        self.slt_blinded_sc.write_to(&mut out);
        self.d1b_wy8192_proof.write_to(&mut out);
        self.mxfp4_proof.write_to(&mut out);
        self.dfa_d1b_proof.write_to(&mut out);
        self.eof_blinded_sc.write_to(&mut out);
        self.shift_blinded_sc.write_to(&mut out);

        self.rom_d1b_proof.write_to(&mut out);
        self.bpe_acc_sc.write_to(&mut out);
        self.bpe_acc_shift_sc.write_to(&mut out);

        self.carry_subproof.write_to(&mut out);
        self.whir_batch_proof.write_to(&mut out);
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        let mut cur = ByteCursor::new(bytes);
        if cur.read_exact(8)? != PAYABLE_RECEIPT_MAGIC {
            return Err("invalid PayableComputeReceipt magic".into());
        }
        let commitment = ProviderTurnCommitment::read_from(&mut cur)?;
        let countersig = EscrowCountersignature::read_from(&mut cur)?;
        let beacon = DrandQuicknetBeacon::read_from(&mut cur)?;

        let audited_gdn_slot = cur.read_u32()? as usize;
        let audited_layer = cur.read_u32()? as usize;
        let audited_chunk = cur.read_u32()? as usize;
        let num_generated_tokens = cur.read_u32()? as usize;
        let byte_pad_len = cur.read_u32()? as usize;
        let byte_gm_limb_vars = cur.read_u32()? as usize;
        let online_gm_limb_vars = cur.read_u32()? as usize;
        let gate_proj_tensor_slot = cur.read_u32()? as usize;

        let b_in_whir_root = cur.read_arr32()?;
        let b_out_whir_root = cur.read_arr32()?;
        let qs_whir_root = cur.read_arr32()?;
        let online_whir_root = cur.read_arr32()?;
        let carry_slot_whir_root = cur.read_arr32()?;

        let b_in_trace_path = read_single_path(&mut cur)?;
        let b_out_trace_path = read_single_path(&mut cur)?;
        let carry_weld_path = read_single_path(&mut cur)?;
        let layer_weight_path = read_single_path(&mut cur)?;

        let td_len = cur.read_u32()? as usize;
        if td_len > 32 {
            return Err("layer_tensor_digests overflow".into());
        }
        let mut layer_tensor_digests = Vec::with_capacity(td_len);
        for _ in 0..td_len {
            layer_tensor_digests.push(cur.read_arr32()?);
        }

        let sc = unpack_ext4_slice(&mut cur, 30)?;
        if sc.len() != 30 {
            return Err("PayableComputeReceipt scalar slice length != 30".into());
        }
        let wy_blinded_sc = BlindedEinSumExt4Proof::read_from(&mut cur)?;
        let slt_blinded_sc = BlindedEinSumExt4Proof::read_from(&mut cur)?;
        let d1b_wy8192_proof = D1bRangeExt4Proof::read_from(&mut cur)?;
        let mxfp4_proof = Mxfp4DelayedBjkExt4Proof::read_from(&mut cur)?;
        let dfa_d1b_proof = D1bRangeExt4Proof::read_from(&mut cur)?;
        let eof_blinded_sc = BlindedEinSumExt4Proof::read_from(&mut cur)?;
        let shift_blinded_sc = BlindedEinSumExt4Proof::read_from(&mut cur)?;

        let rom_d1b_proof = D1bExt4TableProof::read_from(&mut cur)?;
        let bpe_acc_sc = BlindedEinSumExt4Proof::read_from(&mut cur)?;
        let bpe_acc_shift_sc = BlindedEinSumExt4Proof::read_from(&mut cur)?;

        let carry_subproof = CarryWeldSubproof::read_from(&mut cur)?;
        let whir_batch_proof = WhirBatchOpeningProofExt4::read_from(&mut cur)?;
        if cur.remaining() != 0 {
            return Err("trailing bytes in PayableComputeReceipt".into());
        }

        Ok(Self {
            commitment,
            countersig,
            beacon,
            audited_gdn_slot,
            audited_layer,
            audited_chunk,
            num_generated_tokens,
            byte_pad_len,
            byte_gm_limb_vars,
            online_gm_limb_vars,
            b_in_whir_root,
            b_out_whir_root,
            b_in_trace_path,
            b_out_trace_path,
            carry_slot_whir_root,
            carry_weld_path,
            layer_weight_path,
            layer_tensor_digests,
            gate_proj_tensor_slot,
            qs_whir_root,
            online_whir_root,
            rhs_eval_at_z: sc[0],
            uw_eval_at_z: sc[1],
            rem_eval_at_z: sc[2],
            wy_l_eval: sc[3],
            wy_uw_eval: sc[4],
            wy_blinded_sc,
            slt_blinded_sc,
            d1b_wy8192_proof,
            b_at_zwy8192: sc[13],
            mxfp4_proof,
            b_in_eval: sc[5],
            b_out_eval: sc[6],
            delta_gdn_eval: sc[7],
            delta_mlp_eval: sc[8],
            dfa_d1b_proof,
            q_at_dfa_leaf: sc[9],
            b_at_dfa_leaf: sc[10],
            q_next_at_dfa_leaf: sc[11],
            eof_blinded_sc,
            q_next_at_zsh: sc[12],
            shift_blinded_sc,
            final_acc_ext4: sc[14],
            rom_d1b_proof,
            tok_at_zrom: sc[15],
            is_pad_at_zrom: sc[16],
            len_at_zrom: sc[17],
            pow_at_zrom: sc[18],
            val_at_zrom: sc[19],
            acc_next_at_zacc: sc[20],
            val_at_zacc: sc[21],
            bpe_acc_sc,
            acc_at_racc: sc[22],
            pow_at_racc: sc[23],
            acc_next_at_zash: sc[24],
            bpe_acc_shift_sc,
            cum_next_at_zcsh: sc[25],
            emit_tok_eval: sc[26],
            cw_sel_at_sb: sc[27],
            cw_strict_lt_at_zlt: sc[28],
            cw_lt_plus_sel_at_r: sc[29],
            carry_subproof,
            whir_batch_proof,
        })
    }
}

/// Phase-4 Post-Beacon Prover: verifies countersignature & `drand` beacon `round > round_commit`,
/// derives `(audited_layer, audited_chunk)`, and produces a single-cascade `PayableComputeReceipt`.
#[allow(clippy::too_many_arguments)]
pub fn prove_payable_compute_receipt(
    lease: &ProviderExecutionLease,
    rom: &QwenBpeRom,
    registry: &Qwen35WeightRegistry,
    phase1: &ProviderPhase1State,
    countersig: &EscrowCountersignature,
    beacon: &DrandQuicknetBeacon,
    audited_turn_exec: &Qwen35TurnExecution,
    layer_tensor_digests: Vec<[u8; 32]>,
    gate_proj_slot: usize,
    gate_whir: &CompactWhirMxfp4,
) -> Result<PayableComputeReceipt, String> {
    let commit_digest = phase1.commitment.body_digest();
    if countersig.commitment_digest != commit_digest {
        return Err("countersig.commitment_digest mismatch".into());
    }
    if beacon.round <= countersig.round_commit || beacon.round != countersig.target_beacon_round {
        return Err("beacon.round violates post-countersignature schedule".into());
    }
    bls_drand::verify_drand_quicknet_with_pk(&lease.drand_group_pk_g2, beacon)?;

    let (gdn_slot, audited_layer, audited_chunk) = derive_post_countersig_audit_target(
        &lease.lease_id,
        &commit_digest,
        countersig,
        beacon,
        lease.num_chunks,
    );
    if audited_turn_exec.audited_layer != audited_layer {
        return Err("audited_turn_exec.audited_layer != beacon-selected layer".into());
    }

    let b_in_mat = &phase1.chunk_boundary_mats[audited_chunk][audited_layer];
    let b_out_mat = &phase1.chunk_boundary_mats[audited_chunk][audited_layer + 1];
    let b_in_trace_path =
        open_trace_merkle_path(&phase1.trace_tree, audited_chunk * 25 + audited_layer);
    let b_out_trace_path =
        open_trace_merkle_path(&phase1.trace_tree, audited_chunk * 25 + audited_layer + 1);
    let turn_weld_mat = &phase1.turn_weld_mats[gdn_slot];
    let carry_weld_path = open_trace_merkle_path(&phase1.carry_weld_tree, gdn_slot);
    let carry_wit = &phase1.carry_witnesses[gdn_slot];

    // 1. Prepare `Absent("sk-...")` witness over `phase1.byte_commit`:
    let pad_len = phase1.byte_commit.pad_len;
    let m_abs = pad_len.trailing_zeros() as usize;
    let word_len = phase1.raw_output_bytes.len();
    let (final_dfa_state, dfa_trace) = run_padded_complement_sk_dfa(&phase1.raw_output_bytes);
    let mut b_unbiased = vec![0u32; pad_len];
    for (i, &b) in phase1.raw_output_bytes.iter().enumerate() {
        b_unbiased[i] = b as u32;
    }
    let mut q_vec = vec![final_dfa_state as u32; pad_len];
    let mut q_next_vec = vec![final_dfa_state as u32; pad_len];
    let mut dfa_tuples = vec![0u32; pad_len];
    for t in 0..pad_len {
        let qt = if t < dfa_trace.len() {
            dfa_trace[t] as u32
        } else {
            final_dfa_state as u32
        };
        let qn = if t + 1 < dfa_trace.len() {
            dfa_trace[t + 1] as u32
        } else {
            final_dfa_state as u32
        };
        q_vec[t] = qt;
        q_next_vec[t] = qn;
        dfa_tuples[t] = qt + 8 * phase1.byte_commit.bytes_pad[t] + 4096 * qn;
    }
    let pub_dfa_tab = build_collision_free_sk_dfa_table_4096();
    let mult_dfa = compute_d1b_public_table_multiplicities(&dfa_tuples, &pub_dfa_tab)?;

    // 2. Prepare WY + Consolidated `virt_wy8192` (`m_wit = 21`, `[UW, RHS, wy.rem, L, b_unb, q] in [0, 8192)`) + `MXFP4`:
    let wy = &audited_turn_exec.wy_witness;
    let log_h = wy.h_pad.trailing_zeros() as usize;
    let log_c = wy.c_len.trailing_zeros() as usize;
    let wy_cols = wy.d_v + wy.d_k;
    let log_col = wy_cols.trailing_zeros() as usize;
    let m_wy_wit = log_h + log_c + log_col; // 18

    let mut virt_wy8192 = Vec::with_capacity(1usize << 21);
    // Octant 0 (`262,144`): `UW + 4096`
    for &u in &wy.uw_lsb_hik {
        virt_wy8192.push(badd(u, 4096));
    }
    // Octant 1 (`262,144`): `RHS + 4096`
    for &r_v in &wy.rhs_lsb_hik {
        virt_wy8192.push(badd(r_v, 4096));
    }
    // Octant 2 (`262,144`): `wy.rem` (`in [0, 8192)`)
    virt_wy8192.extend_from_slice(&wy.rem_lsb_hik);
    // Octant 3 (`262,144`): `wy.rem + 4096` (`in [0, 8192)` => `wy.rem in [0, 4096)`!)
    for &rm in &wy.rem_lsb_hik {
        virt_wy8192.push(badd(rm, 4096));
    }
    // Octant 4, Sub-quadrant 0 (`65,536`): `L + 4096` (`L in [-4096, 4096)`)
    for &l in &wy.l_lsb_hij {
        virt_wy8192.push(badd(l, 4096));
    }
    // Octant 4, Sub-quadrant 1 (`65,536` = Blocks `0..4` of `2,048` + `0` padding):
    virt_wy8192.extend_from_slice(&b_unbiased);
    for &bu in &b_unbiased {
        virt_wy8192.push(badd(bu, 7936)); // `8192 - 256 = 7936` => `b_unbiased in [0, 256)`!
    }
    virt_wy8192.extend_from_slice(&q_vec);
    for &qv in &q_vec {
        virt_wy8192.push(badd(qv, 8184)); // `8192 - 8 = 8184` => `q_vec in [0, 8)`!
    }
    virt_wy8192.resize(1usize << 21, 0u32);
    let mult_wy8192 = compute_d1b_multiplicities(&virt_wy8192, 13)?;

    let k_pad = gate_whir.k_pad;
    let j_pad = gate_whir.j_pad;
    let in_orig = audited_turn_exec.x_ln2_i16.len() / wy.c_len;
    let mut x_lsb_tbk = vec![0u32; wy.c_len * k_pad * 32];
    for t in 0..wy.c_len {
        for d in 0..in_orig {
            let k = d / 32;
            let b = d % 32;
            x_lsb_tbk[t + (b << log_c) + (k << (log_c + 5))] =
                bb_from_i64(audited_turn_exec.x_ln2_i16[t * in_orig + d] as i64);
        }
    }
    let mut y_lsb_tj = vec![0u32; wy.c_len * j_pad];
    for t in 0..wy.c_len {
        for j in 0..j_pad {
            y_lsb_tj[t + (j << log_c)] =
                bb_from_i64(audited_turn_exec.gate_proj_y_raw[t * j_pad + j]);
        }
    }

    // 3. Begin Unified Fiat–Shamir Transcript & Squeeze Post-Commitment `beta_ext4`!
    let mut tr = CShakeTranscript::new(b"QW35-PAYABLE-COMPUTE-RECEIPT-V1");
    tr.absorb_root(b"pay_inv_key", &lease.invocation_key());
    tr.absorb_root(b"pay_commit_dig", &commit_digest);
    tr.absorb_u32(b"pay_r_commit_lo", countersig.round_commit as u32);
    tr.absorb_u32(b"pay_r_beacon_lo", beacon.round as u32);
    tr.absorb_root(b"pay_drand_rand", &beacon.randomness);
    tr.absorb_u32(b"pay_layer", audited_layer as u32);
    tr.absorb_u32(b"pay_chunk", audited_chunk as u32);
    tr.absorb_root(b"pay_bin_root", &b_in_mat.root);
    tr.absorb_root(b"pay_bout_root", &b_out_mat.root);
    tr.absorb_root(b"pay_qs_root", &gate_whir.qs_mat.root);
    tr.absorb_root(b"pay_cwslot_root", &turn_weld_mat.root);

    // Post-commitment BPE evaluation base `beta_ext4` squeezed strictly AFTER `bpe_weld_root` & `byte_root`!
    let beta_ext4 = tr.squeeze_ext4(b"pay_bpe_beta", true);
    let k_gen = phase1.generated_tokens.len();
    let mut pow_col = vec![Ext4::ONE; CARRY_TURN_TOKENS];
    let mut val_col = vec![Ext4::ZERO; CARRY_TURN_TOKENS];
    let mut acc_col = vec![Ext4::ZERO; CARRY_TURN_TOKENS];
    let mut acc_next_col = vec![Ext4::ZERO; CARRY_TURN_TOKENS];
    let mut mult_rom = vec![0u32; ROM_PADDED_SIZE];
    let mut cur_acc = Ext4::ZERO;
    for i in 0..CARRY_TURN_TOKENS {
        acc_col[i] = cur_acc;
        if i < k_gen {
            let tid = phase1.generated_tokens[i];
            let bs = rom.token_bytes(tid)?;
            let pw = ext4_pow(beta_ext4, bs.len() as u64);
            let vl = eval_bytes_ext4(beta_ext4, bs);
            pow_col[i] = pw;
            val_col[i] = vl;
            cur_acc = cur_acc.mul(pw).add(vl);
            mult_rom[tid as usize] += 1;
        } else {
            mult_rom[QWEN_DEFINED_TOKENS] += 1;
        }
        acc_next_col[i] = cur_acc;
    }
    let final_acc_ext4 = cur_acc;
    let pow_packed = pack_ext4_col_to_bb(&pow_col);
    let val_packed = pack_ext4_col_to_bb(&val_col);
    let acc_packed = pack_ext4_col_to_bb(&acc_col);
    let acc_next_packed = pack_ext4_col_to_bb(&acc_next_col);

    // Carry multiplicities:
    let virt_cw_u16 = carry_wit.build_virtual_u16_table();
    let mult_cw_u16 = compute_d1b_multiplicities(&virt_cw_u16, 16)?;
    let virt_cw_rem11 = carry_wit.build_virtual_rem11_table();
    let mult_cw_rem11 = compute_d1b_multiplicities(&virt_cw_rem11, 11)?;

    // Sample ONE shared external `GMaskExt4` covering all 8 blinded sumchecks (`gm_limb_vars <= 10`):
    let gm_specs = vec![
        GMaskSpecExt4::new("wy_sc", log_h + log_c, 3),
        GMaskSpecExt4::new("slt_sc", log_h + 2 * log_c, 3),
        GMaskSpecExt4::new("shift_sc", m_abs, 3),
        GMaskSpecExt4::new("bpe_acc", 7, 3),
        GMaskSpecExt4::new("bpe_ash", 7, 3),
        GMaskSpecExt4::new("cw_sbool", 13, 3),
        GMaskSpecExt4::new("cw_ltsh", 13, 3),
        GMaskSpecExt4::new("cw_seltgt", 13, 3),
    ];
    let mut gm_rng = CShakeRng::from_seed(b"QW35-PAYABLE-GMASK-V1", &os_random_seed_32());
    let ext_gmask = GMaskExt4::sample(gm_specs.clone(), &mut gm_rng);
    let gm_limbs = ext_gmask.to_four_bb_tables();
    let online_gm_limb_vars = gm_limbs[0].len().trailing_zeros() as usize;

    // Pack ALL 23 post-beacon subtables into ONE `online_mat` (`1,658K <= 2,031K` cells -> `rd = 128`, `0` extra rows!):
    //   0: L, 1: RHS, 2: UW, 3: rem_wy, 4: mult_wy8192, 5: X_ln2, 6: Y_gate, 7: delta_gdn, 8: delta_mlp,
    //   9: q, 10: q_next, 11: mult_dfa,
    //   12: pow_packed, 13: val_packed, 14: acc_packed, 15: acc_next_packed, 16: mult_rom,
    //   17: mult_cw_u16, 18: mult_cw_rem11, 19..=22: gm_limbs[0..4].
    let online_mat = WhirCommittedMatrixExt4::commit(
        &[
            &wy.l_lsb_hij,
            &wy.rhs_lsb_hik,
            &wy.uw_lsb_hik,
            &wy.rem_lsb_hik,
            &mult_wy8192,
            &x_lsb_tbk,
            &y_lsb_tj,
            &audited_turn_exec.delta_gdn_bb,
            &audited_turn_exec.delta_mlp_bb,
            &q_vec,
            &q_next_vec,
            &mult_dfa,
            &pow_packed,
            &val_packed,
            &acc_packed,
            &acc_next_packed,
            &mult_rom,
            &mult_cw_u16,
            &mult_cw_rem11,
            &gm_limbs[0],
            &gm_limbs[1],
            &gm_limbs[2],
            &gm_limbs[3],
        ],
        true,
        None,
    );
    tr.absorb_root(b"pay_online_root", &online_mat.root);
    tr.absorb_ext4(b"pay_fin_acc", final_acc_ext4);

    // --- Prove Section A: `GDN WY + Consolidated [UW, RHS, rem, L, b, q] D1b + MXFP4 + U1` ---
    let z_h = tr.squeeze_ext4_vec(b"wy_zh", log_h, true);
    let z_i = tr.squeeze_ext4_vec(b"wy_zi", log_c, true);
    let z_k = tr.squeeze_ext4_vec(b"wy_zk", log_col, true);
    let mut z_hik = Vec::with_capacity(m_wy_wit);
    z_hik.extend_from_slice(&z_h);
    z_hik.extend_from_slice(&z_i);
    z_hik.extend_from_slice(&z_k);

    let rhs_eval_at_z = mle_eval_bb_at_ext4(&wy.rhs_lsb_hik, &z_hik);
    let uw_eval_at_z = mle_eval_bb_at_ext4(&wy.uw_lsb_hik, &z_hik);
    let rem_eval_at_z = mle_eval_bb_at_ext4(&wy.rem_lsb_hik, &z_hik);
    for e in [rhs_eval_at_z, uw_eval_at_z, rem_eval_at_z] {
        tr.absorb_ext4(b"wy_ev", e);
    }

    let eq_i = build_eq_table_lsb_ext4(&z_i);
    let eq_k = build_eq_table_lsb_ext4(&z_k);
    let mut left_hj = vec![Ext4::ZERO; wy.h_pad * wy.c_len];
    let mut right_hj = vec![Ext4::ZERO; wy.h_pad * wy.c_len];
    for j in 0..wy.c_len {
        for h in 0..wy.h_pad {
            let mut al = Ext4::ZERO;
            for (i, &eq_iv) in eq_i.iter().enumerate() {
                al =
                    al.add(eq_iv.scale_bb(wy.l_lsb_hij[h + (i << log_h) + (j << (log_h + log_c))]));
            }
            left_hj[h + (j << log_h)] = al;
            let mut ar = Ext4::ZERO;
            for (k, &eq_kv) in eq_k.iter().enumerate() {
                ar = ar
                    .add(eq_kv.scale_bb(wy.uw_lsb_hik[h + (j << log_h) + (k << (log_h + log_c))]));
            }
            right_hj[h + (j << log_h)] = ar;
        }
    }
    let (wy_blinded_sc, wy_rho, wy_chals, wy_l_eval, wy_uw_eval, wy_term) = prove_gmask_einsum_ext4(
        &left_hj,
        &right_hj,
        GmaskEinSumParams {
            mu_s: log_h,
            kappa: log_c,
            z_s: &z_h,
            gmask: &ext_gmask,
            spec_name: "wy_sc",
        },
        &mut tr,
    );
    tr.absorb_ext4(b"wy_l_ev", wy_l_eval);
    tr.absorb_ext4(b"wy_uw_ev", wy_uw_eval);

    let m_slt = log_h + 2 * log_c;
    let z_slt = tr.squeeze_ext4_vec(b"slt_z", m_slt, true);
    let mut non_slt = vec![Ext4::ZERO; 1usize << m_slt];
    let mut l_ext = vec![Ext4::ZERO; 1usize << m_slt];
    for j in 0..wy.c_len {
        for i in 0..wy.c_len {
            let m_ij = if i <= j { Ext4::ONE } else { Ext4::ZERO };
            for h in 0..wy.h_pad {
                let idx = h + (i << log_h) + (j << (log_h + log_c));
                non_slt[idx] = m_ij;
                l_ext[idx] = Ext4::from_bb(wy.l_lsb_hij[idx]);
            }
        }
    }
    let (slt_blinded_sc, slt_rho, slt_chals, _, _, slt_term) = prove_gmask_einsum_ext4(
        &non_slt,
        &l_ext,
        GmaskEinSumParams {
            mu_s: m_slt,
            kappa: 0,
            z_s: &z_slt,
            gmask: &ext_gmask,
            spec_name: "slt_sc",
        },
        &mut tr,
    );

    let (d1b_wy8192_proof, z_wy8192) =
        prove_d1b_range_ext4(&virt_wy8192, &mult_wy8192, 21, 13, &mut tr);
    let b_at_zwy8192 = mle_eval_bb_at_ext4(&phase1.byte_commit.bytes_pad, &z_wy8192[..m_abs]);
    tr.absorb_ext4(b"wy_bz", b_at_zwy8192);

    let log_j = j_pad.trailing_zeros() as usize;
    let log_k = k_pad.trailing_zeros() as usize;
    let r_i_mxfp4 = tr.squeeze_ext4_vec(b"mxfp4_ri", log_c, true);
    let r_j_mxfp4 = tr.squeeze_ext4_vec(b"mxfp4_rj", log_j, true);
    let eq_ri = build_eq_table_lsb_ext4(&r_i_mxfp4);
    let mut x_ri = vec![Ext4::ZERO; k_pad * 32];
    for k in 0..k_pad {
        for b in 0..32 {
            let mut acc = Ext4::ZERO;
            let base = (b << log_c) + (k << (log_c + 5));
            for t in 0..wy.c_len {
                acc = acc.add(eq_ri[t].scale_bb(x_lsb_tbk[base + t]));
            }
            x_ri[k * 32 + b] = acc;
        }
    }
    let (mxfp4_proof, mxfp4_chals) = prove_mxfp4_delayed_bjk_horner_ext4(
        &x_ri,
        &gate_whir.nibs_pad,
        &gate_whir.scs_pad,
        log_j,
        log_k,
        &r_j_mxfp4,
        &mut tr,
    );

    let bnd_vars = 16usize; // `64 * 1024`
    let z_bnd = tr.squeeze_ext4_vec(b"u1_zb", bnd_vars, true);
    let b_in_eval = mle_eval_bb_at_ext4(&audited_turn_exec.boundaries_bb[audited_layer], &z_bnd);
    let b_out_eval =
        mle_eval_bb_at_ext4(&audited_turn_exec.boundaries_bb[audited_layer + 1], &z_bnd);
    let delta_gdn_eval = mle_eval_bb_at_ext4(&audited_turn_exec.delta_gdn_bb, &z_bnd);
    let delta_mlp_eval = mle_eval_bb_at_ext4(&audited_turn_exec.delta_mlp_bb, &z_bnd);
    for e in [b_in_eval, b_out_eval, delta_gdn_eval, delta_mlp_eval] {
        tr.absorb_ext4(b"u1_ev", e);
    }

    // --- Prove Section B: `Absent("sk-...")` over `phase1.byte_commit` (`TVD == 0` EOF via `byte_commit.eof_gmask`!) ---
    let (dfa_d1b_proof, z_dfa_leaf) =
        prove_d1b_public_table_ext4(&dfa_tuples, &pub_dfa_tab, &mult_dfa, &mut tr);
    let q_at_dfa_leaf = mle_eval_bb_at_ext4(&q_vec, &z_dfa_leaf);
    let b_at_dfa_leaf = mle_eval_bb_at_ext4(&phase1.byte_commit.bytes_pad, &z_dfa_leaf);
    let q_next_at_dfa_leaf = mle_eval_bb_at_ext4(&q_next_vec, &z_dfa_leaf);
    for e in [q_at_dfa_leaf, b_at_dfa_leaf, q_next_at_dfa_leaf] {
        tr.absorb_ext4(b"abs_dl", e);
    }

    let z_eof = tr.squeeze_ext4_vec(b"abs_zeof", m_abs, true);
    let mut left_eof = vec![Ext4::ZERO; pad_len];
    let mut right_eof = vec![Ext4::ZERO; pad_len];
    for t in 0..pad_len {
        if t >= word_len {
            left_eof[t] = Ext4::ONE;
        }
        right_eof[t] = Ext4::from_bb(phase1.byte_commit.bytes_pad[t]).sub(Ext4::from_bb(256));
    }
    let (eof_blinded_sc, eof_rho, eof_chals, _, _, eof_term) = prove_gmask_einsum_ext4(
        &left_eof,
        &right_eof,
        GmaskEinSumParams {
            mu_s: m_abs,
            kappa: 0,
            z_s: &z_eof,
            gmask: &phase1.byte_commit.eof_gmask,
            spec_name: "eof_sc",
        },
        &mut tr,
    );

    let z_sh = tr.squeeze_ext4_vec(b"abs_zsh", m_abs, true);
    let q_next_at_zsh = mle_eval_bb_at_ext4(&q_next_vec, &z_sh);
    tr.absorb_ext4(b"abs_qn", q_next_at_zsh);
    let eq_zsh = build_eq_table_lsb_ext4(&z_sh);
    let mut shift_col_abs = vec![Ext4::ZERO; pad_len];
    shift_col_abs[1..pad_len].copy_from_slice(&eq_zsh[..(pad_len - 1)]);
    let q_ext: Vec<Ext4> = q_vec.iter().map(|&v| Ext4::from_bb(v)).collect();
    let (shift_blinded_sc, sh_rho, sh_chals, _, _, sh_term) = prove_gmask_einsum_ext4(
        &shift_col_abs,
        &q_ext,
        GmaskEinSumParams {
            mu_s: 0,
            kappa: m_abs,
            z_s: &[],
            gmask: &ext_gmask,
            spec_name: "shift_sc",
        },
        &mut tr,
    );

    // --- Prove Section C: Post-Commitment `248,320`-Vocab `QwenBpeRom` Token-to-Byte Weld ---
    let rom_gammas = [
        tr.squeeze_ext4(b"bpe_rg0", true),
        tr.squeeze_ext4(b"bpe_rg1", true),
        tr.squeeze_ext4(b"bpe_rg2", true),
        tr.squeeze_ext4(b"bpe_rg3", true),
    ];
    let rom_table_ext4 = rom.build_packed_rom_table_ext4(beta_ext4, rom_gammas);
    let wit_rom_tuples: Vec<Ext4> = (0..CARRY_TURN_TOKENS)
        .map(|i| {
            Ext4::from_bb(phase1.bpe_phase1_cols[0][i])
                .add(rom_gammas[0].scale_bb(phase1.bpe_phase1_cols[1][i]))
                .add(rom_gammas[1].scale_bb(phase1.bpe_phase1_cols[2][i]))
                .add(rom_gammas[2].mul(pow_col[i]))
                .add(rom_gammas[3].mul(val_col[i]))
        })
        .collect();
    let (rom_d1b_proof, z_rom_tab) =
        prove_d1b_ext4_table(&wit_rom_tuples, &rom_table_ext4, &mult_rom, &mut tr);
    let z_rom_wit = z_rom_tab[..7].to_vec();
    let tok_at_zrom = mle_eval_bb_at_ext4(&phase1.bpe_phase1_cols[0], &z_rom_wit);
    let is_pad_at_zrom = mle_eval_bb_at_ext4(&phase1.bpe_phase1_cols[1], &z_rom_wit);
    let len_at_zrom = mle_eval_bb_at_ext4(&phase1.bpe_phase1_cols[2], &z_rom_wit);
    let pow_at_zrom = eval_ext4_vec_mle(&pow_col, &z_rom_wit);
    let val_at_zrom = eval_ext4_vec_mle(&val_col, &z_rom_wit);
    for e in [
        tok_at_zrom,
        is_pad_at_zrom,
        len_at_zrom,
        pow_at_zrom,
        val_at_zrom,
    ] {
        tr.absorb_ext4(b"bpe_rom_ev", e);
    }

    let z_acc = tr.squeeze_ext4_vec(b"bpe_zacc", 7, true);
    let acc_next_at_zacc = eval_ext4_vec_mle(&acc_next_col, &z_acc);
    let val_at_zacc = eval_ext4_vec_mle(&val_col, &z_acc);
    tr.absorb_ext4(b"bpe_anz", acc_next_at_zacc);
    tr.absorb_ext4(b"bpe_vz", val_at_zacc);
    let (bpe_acc_sc, bacc_rho, bacc_chals, acc_at_racc, pow_at_racc, bacc_term) =
        prove_gmask_einsum_ext4(
            &acc_col,
            &pow_col,
            GmaskEinSumParams {
                mu_s: 7,
                kappa: 0,
                z_s: &z_acc,
                gmask: &ext_gmask,
                spec_name: "bpe_acc",
            },
            &mut tr,
        );
    tr.absorb_ext4(b"bpe_ar", acc_at_racc);
    tr.absorb_ext4(b"bpe_pr", pow_at_racc);

    let z_ash = tr.squeeze_ext4_vec(b"bpe_zash", 7, true);
    let acc_next_at_zash = eval_ext4_vec_mle(&acc_next_col, &z_ash);
    tr.absorb_ext4(b"bpe_ansh", acc_next_at_zash);
    let eq_zash = build_eq_table_lsb_ext4(&z_ash);
    let mut ash_col = vec![Ext4::ZERO; CARRY_TURN_TOKENS];
    ash_col[1..CARRY_TURN_TOKENS].copy_from_slice(&eq_zash[..(CARRY_TURN_TOKENS - 1)]);
    let (bpe_acc_shift_sc, bash_rho, bash_chals, _, _, bash_term) = prove_gmask_einsum_ext4(
        &ash_col,
        &acc_col,
        GmaskEinSumParams {
            mu_s: 0,
            kappa: 7,
            z_s: &[],
            gmask: &ext_gmask,
            spec_name: "bpe_ash",
        },
        &mut tr,
    );

    let z_clen = tr.squeeze_ext4_vec(b"bpe_zcl", 7, true);
    let z_csh = tr.squeeze_ext4_vec(b"bpe_zcsh", 7, true);
    let cum_next_at_zcsh = mle_eval_bb_at_ext4(&phase1.bpe_phase1_cols[4], &z_csh);
    tr.absorb_ext4(b"bpe_cnsh", cum_next_at_zcsh);
    let eq_zcsh = build_eq_table_lsb_ext4(&z_csh);
    let mut csh_col = vec![Ext4::ZERO; CARRY_TURN_TOKENS];
    csh_col[1..CARRY_TURN_TOKENS].copy_from_slice(&eq_zcsh[..(CARRY_TURN_TOKENS - 1)]);

    let (w_horner, c_horner) = build_horner_byte_weights(beta_ext4, word_len, pad_len);

    let z_emit = tr.squeeze_ext4_vec(b"bpe_zemit", 7, true);
    let emit_tok_eval = mle_eval_bb_at_ext4(&phase1.bpe_phase1_cols[0], &z_emit);
    tr.absorb_ext4(b"bpe_emitev", emit_tok_eval);

    // --- Prove Section D: `SpecPrefill` Token-Carry & Looped Residual-Carry on `audited_layer`'s top-1024 `gate_proj` ---
    let mut w_loop_nibs = vec![0u8; LOOP_DIM * k_pad * 32];
    let mut w_loop_scs = vec![0u32; LOOP_DIM * k_pad];
    w_loop_nibs.copy_from_slice(&gate_whir.nibs_pad[..LOOP_DIM * k_pad * 32]);
    w_loop_scs.copy_from_slice(&gate_whir.scs_pad[..LOOP_DIM * k_pad]);

    let gm_ids = [19usize, 20, 21, 22];
    let (
        carry_subproof,
        cw_sel_at_sb,
        cw_strict_lt_at_zlt,
        cw_lt_plus_sel_at_r,
        mut turn_weld_claims,
        cw_online_claims,
        qs_lp,
    ) = append_carry_weld_prover_transcript(
        carry_wit,
        CarryWeldAuxSlices {
            w_loop_nibs: &w_loop_nibs,
            w_loop_scs: &w_loop_scs,
            mult_u16: &mult_cw_u16,
            mult_rem11: &mult_cw_rem11,
        },
        &ext_gmask,
        CarryWeldMaskCfg {
            gm_specs: &gm_specs,
            gm_ids,
            mult_u16_sub: 17,
            mult_rem11_sub: 18,
        },
        &mut tr,
    );

    // Add `emit_tok_eval` weld (`subtable 2`) + Phase-1 BPE subtable claims (`19..=23`) onto `turn_weld_mat`:
    let eq_emit = build_eq_table_lsb_ext4(&z_emit);
    let p_len = lease.prompt_tokens.len();
    let mut w_emit_y = vec![Ext4::ZERO; CARRY_TURN_TOKENS];
    let mut pad_tail_emit = Ext4::ZERO;
    for i in 0..CARRY_TURN_TOKENS {
        if i < k_gen {
            w_emit_y[p_len - 1 + i] = eq_emit[i];
        } else {
            pad_tail_emit = pad_tail_emit.add(eq_emit[i].scale_bb(PAD_TOK_ID));
        }
    }
    let is_pad_want = eq_emit[k_gen..CARRY_TURN_TOKENS]
        .iter()
        .fold(Ext4::ZERO, |a, &e| a.add(e));
    let eq_zcsh_last = eq_zcsh[CARRY_TURN_TOKENS - 1];
    turn_weld_claims.extend([
        JointLinearClaimExt4 {
            terms: vec![LinearTermExt4::DenseSmall {
                subtable: 2,
                weights_lsb: w_emit_y,
            }],
            rhs: emit_tok_eval.sub(pad_tail_emit),
        },
        JointLinearClaimExt4::point_eval(19, z_rom_wit.clone(), tok_at_zrom),
        JointLinearClaimExt4::point_eval(19, z_emit.clone(), emit_tok_eval),
        JointLinearClaimExt4::point_eval(20, z_rom_wit.clone(), is_pad_at_zrom),
        JointLinearClaimExt4::point_eval(20, z_emit, is_pad_want),
        JointLinearClaimExt4::point_eval(21, z_rom_wit.clone(), len_at_zrom),
        JointLinearClaimExt4::point_eval(22, vec![Ext4::ZERO; 7], Ext4::ZERO),
        JointLinearClaimExt4::point_eval(23, vec![Ext4::ONE; 7], Ext4::from_bb(word_len as u32)),
        JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: 23,
                    point: z_clen.clone(),
                    weight: Ext4::ONE,
                },
                LinearTermExt4::PointEval {
                    subtable: 22,
                    point: z_clen.clone(),
                    weight: Ext4::ONE.neg(),
                },
                LinearTermExt4::PointEval {
                    subtable: 21,
                    point: z_clen,
                    weight: Ext4::ONE.neg(),
                },
            ],
            rhs: Ext4::ZERO,
        },
        JointLinearClaimExt4::point_eval(23, z_csh, cum_next_at_zcsh),
        JointLinearClaimExt4 {
            terms: vec![LinearTermExt4::DenseSmall {
                subtable: 22,
                weights_lsb: csh_col,
            }],
            rhs: cum_next_at_zcsh.sub(eq_zcsh_last.scale_bb(word_len as u32)),
        },
    ]);

    // --- Assemble Claims for ALL 6 WHIR Matrices in ONE Shared Cascade ---
    let (zb0, zb1, limb_scale) = eval_packed_ext4_limb_consts();
    let packed_pt = |pt: &[Ext4]| -> Vec<Ext4> {
        let mut out = Vec::with_capacity(pt.len() + 2);
        out.extend_from_slice(pt);
        out.push(zb0);
        out.push(zb1);
        out
    };
    let inv_limb_scale = limb_scale.inv().unwrap();

    let (wy_ws, wy_wa) = GMaskExt4::build_spec_weights(&gm_specs, "wy_sc", &wy_chals);
    let (slt_ws, slt_wa) = GMaskExt4::build_spec_weights(&gm_specs, "slt_sc", &slt_chals);
    let (sh_ws, sh_wa) = GMaskExt4::build_spec_weights(&gm_specs, "shift_sc", &sh_chals);
    let (bacc_ws, bacc_wa) = GMaskExt4::build_spec_weights(&gm_specs, "bpe_acc", &bacc_chals);
    let (bash_ws, bash_wa) = GMaskExt4::build_spec_weights(&gm_specs, "bpe_ash", &bash_chals);

    let mut l_pt1 = Vec::new();
    l_pt1.extend_from_slice(&wy_chals[..log_h]);
    l_pt1.extend_from_slice(&z_i);
    l_pt1.extend_from_slice(&wy_chals[log_h..]);
    let mut uw_pt2 = Vec::new();
    uw_pt2.extend_from_slice(&wy_chals[..log_h]);
    uw_pt2.extend_from_slice(&wy_chals[log_h..]);
    uw_pt2.extend_from_slice(&z_k);

    let mut pt_x = Vec::new();
    pt_x.extend_from_slice(&r_i_mxfp4);
    pt_x.extend_from_slice(&mxfp4_chals.chals_b);
    pt_x.extend_from_slice(&mxfp4_chals.chals_k);
    let mut pt_y = Vec::new();
    pt_y.extend_from_slice(&r_i_mxfp4);
    pt_y.extend_from_slice(&r_j_mxfp4);

    let non_slt_factor = eq_mle_ext4(&z_slt, &slt_chals).mul(eval_non_slt_mask_mle_local(
        &slt_chals[log_h..log_h + log_c],
        &slt_chals[log_h + log_c..],
    ));
    let shift_factor_abs = eval_shift_kernel_128(&z_sh, &sh_chals);
    let wy_unm_term = eq_mle_ext4(&z_h, &wy_chals[..log_h])
        .mul(wy_l_eval)
        .mul(wy_uw_eval);
    let bacc_unm_term = eq_mle_ext4(&z_acc, &bacc_chals)
        .mul(acc_at_racc)
        .mul(pow_at_racc);
    let bash_k = eval_shift_kernel_128(&z_ash, &bash_chals);

    // Consolidated `virt_wy8192` (`2^{21}`):
    let w_o8 = build_eq_table_lsb_ext4(&z_wy8192[18..21]);
    let w_s4 = build_eq_table_lsb_ext4(&z_wy8192[16..18]);
    let w_b32 = build_eq_table_lsb_ext4(&z_wy8192[11..16]);
    let w_oct4_s0 = w_o8[4].mul(w_s4[0]);
    let w_oct4_s1 = w_o8[4].mul(w_s4[1]);
    let w_q_zwy = w_oct4_s1.mul(w_b32[2].add(w_b32[3]));
    let eof_bias_zwy = eval_eof_ind_mle_local(word_len, pad_len, &z_wy8192[..m_abs]).scale_bb(256);
    let b_unb_zwy = b_at_zwy8192.sub(eof_bias_zwy);
    let b_contrib_zwy = w_oct4_s1.mul(w_b32[0].add(w_b32[1])).mul(b_unb_zwy);
    let bias_wy8192 = w_o8[0]
        .add(w_o8[1])
        .add(w_o8[3])
        .add(w_oct4_s0)
        .scale_bb(4096)
        .add(w_oct4_s1.mul(w_b32[1].scale_bb(7936).add(w_b32[3].scale_bb(8184))));

    let mut online_claims = vec![
        JointLinearClaimExt4::point_eval(0, l_pt1, wy_l_eval),
        JointLinearClaimExt4::point_eval(1, z_hik.clone(), rhs_eval_at_z),
        JointLinearClaimExt4::point_eval(2, z_hik.clone(), uw_eval_at_z),
        JointLinearClaimExt4::point_eval(2, uw_pt2, wy_uw_eval),
        JointLinearClaimExt4::point_eval(3, z_hik, rem_eval_at_z),
        JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: 2,
                    point: z_wy8192[..18].to_vec(),
                    weight: w_o8[0],
                },
                LinearTermExt4::PointEval {
                    subtable: 1,
                    point: z_wy8192[..18].to_vec(),
                    weight: w_o8[1],
                },
                LinearTermExt4::PointEval {
                    subtable: 3,
                    point: z_wy8192[..18].to_vec(),
                    weight: w_o8[2].add(w_o8[3]),
                },
                LinearTermExt4::PointEval {
                    subtable: 0,
                    point: z_wy8192[..16].to_vec(),
                    weight: w_oct4_s0,
                },
                LinearTermExt4::PointEval {
                    subtable: 9,
                    point: z_wy8192[..m_abs].to_vec(),
                    weight: w_q_zwy,
                },
            ],
            rhs: d1b_wy8192_proof
                .rem_leaf_eval
                .sub(b_contrib_zwy)
                .sub(bias_wy8192),
        },
        JointLinearClaimExt4::point_eval(
            4,
            z_wy8192[..13].to_vec(),
            d1b_wy8192_proof.mult_leaf_eval,
        ),
        JointLinearClaimExt4::point_eval(5, pt_x, mxfp4_proof.finals.0),
        JointLinearClaimExt4::point_eval(6, pt_y, mxfp4_proof.claim),
        JointLinearClaimExt4::point_eval(7, z_bnd.clone(), delta_gdn_eval),
        JointLinearClaimExt4::point_eval(8, z_bnd.clone(), delta_mlp_eval),
        // `Absent`:
        JointLinearClaimExt4::point_eval(9, vec![Ext4::ZERO; m_abs], Ext4::ZERO),
        JointLinearClaimExt4::point_eval(9, z_dfa_leaf.clone(), q_at_dfa_leaf),
        JointLinearClaimExt4::point_eval(10, z_dfa_leaf.clone(), q_next_at_dfa_leaf),
        JointLinearClaimExt4::point_eval(10, z_sh.clone(), q_next_at_zsh),
        JointLinearClaimExt4::point_eval(
            11,
            z_dfa_leaf[..11].to_vec(),
            dfa_d1b_proof.mult_leaf_eval,
        ),
        // Phase-3 BPE `Ext4` packed columns + `mult_rom`:
        JointLinearClaimExt4::point_eval(
            12,
            packed_pt(&z_rom_wit),
            pow_at_zrom.mul(inv_limb_scale),
        ),
        JointLinearClaimExt4::point_eval(
            12,
            packed_pt(&bacc_chals),
            pow_at_racc.mul(inv_limb_scale),
        ),
        JointLinearClaimExt4::point_eval(
            13,
            packed_pt(&z_rom_wit),
            val_at_zrom.mul(inv_limb_scale),
        ),
        JointLinearClaimExt4::point_eval(13, packed_pt(&z_acc), val_at_zacc.mul(inv_limb_scale)),
        JointLinearClaimExt4::point_eval(14, packed_pt(&[Ext4::ZERO; 7]), Ext4::ZERO),
        JointLinearClaimExt4::point_eval(
            14,
            packed_pt(&bacc_chals),
            acc_at_racc.mul(inv_limb_scale),
        ),
        JointLinearClaimExt4::point_eval(
            15,
            packed_pt(&[Ext4::ONE; 7]),
            final_acc_ext4.mul(inv_limb_scale),
        ),
        JointLinearClaimExt4::point_eval(
            15,
            packed_pt(&z_acc),
            acc_next_at_zacc.mul(inv_limb_scale),
        ),
        JointLinearClaimExt4::point_eval(
            15,
            packed_pt(&z_ash),
            acc_next_at_zash.mul(inv_limb_scale),
        ),
        JointLinearClaimExt4::point_eval(16, z_rom_tab, rom_d1b_proof.mult_leaf_eval),
        // `GMaskExt4` sum & HVZK terminal welds:
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &wy_ws, wy_blinded_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_ids,
            &wy_wa,
            wy_rho,
            wy_term.sub(wy_unm_term),
        ),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &slt_ws, slt_blinded_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            vec![LinearTermExt4::PointEval {
                subtable: 0,
                point: slt_chals,
                weight: non_slt_factor,
            }],
            gm_ids,
            &slt_wa,
            slt_rho,
            slt_term,
        ),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &sh_ws, shift_blinded_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            vec![LinearTermExt4::PointEval {
                subtable: 9,
                point: sh_chals,
                weight: shift_factor_abs,
            }],
            gm_ids,
            &sh_wa,
            sh_rho,
            sh_term,
        ),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &bacc_ws, bpe_acc_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_ids,
            &bacc_wa,
            bacc_rho,
            bacc_term.sub(bacc_unm_term),
        ),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &bash_ws, bpe_acc_shift_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            vec![LinearTermExt4::PointEval {
                subtable: 14,
                point: packed_pt(&bash_chals),
                weight: bash_k.mul(limb_scale),
            }],
            gm_ids,
            &bash_wa,
            bash_rho,
            bash_term,
        ),
    ];
    online_claims.extend(cw_online_claims);

    // `byte_commit` claims (`subtable 0 = bytes_pad`, `5..=8 = byte_commit.eof_gmask`):
    let (byte_eof_ws, byte_eof_wa) =
        GMaskExt4::build_spec_weights(&phase1.byte_commit.eof_gm_specs, "eof_sc", &eof_chals);
    let f_eof_byte =
        eq_mle_ext4(&z_eof, &eof_chals).mul(eval_eof_ind_mle_local(word_len, pad_len, &eof_chals));
    let byte_claims = vec![
        JointLinearClaimExt4::point_eval(0, z_dfa_leaf, b_at_dfa_leaf),
        JointLinearClaimExt4::point_eval(0, z_wy8192[..m_abs].to_vec(), b_at_zwy8192),
        JointLinearClaimExt4 {
            terms: vec![LinearTermExt4::DenseSmall {
                subtable: 0,
                weights_lsb: w_horner,
            }],
            rhs: final_acc_ext4.sub(c_horner),
        },
        JointLinearClaimExt4::gmask_sum_claim([5, 6, 7, 8], &byte_eof_ws, eof_blinded_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            vec![LinearTermExt4::PointEval {
                subtable: 0,
                point: eof_chals,
                weight: f_eof_byte,
            }],
            [5, 6, 7, 8],
            &byte_eof_wa,
            eof_rho,
            eof_term.add(f_eof_byte.scale_bb(256)),
        ),
    ];

    // `CompactWhirMxfp4` `qs_claims` (`3584 = 2048 + 1024 + 512` + `j < 1024` looped residual subdomain!):
    let j9 = mxfp4_chals.chals_j[9];
    let j10 = mxfp4_chals.chals_j[10];
    let j11 = mxfp4_chals.chals_j[11];
    let wq_0 = Ext4::ONE.sub(j11);
    let wq_1 = j11.mul(Ext4::ONE.sub(j10));
    let wq_2 = j11.mul(j10).mul(Ext4::ONE.sub(j9));

    let mk_q_pt = |j_len: usize| -> Vec<Ext4> {
        let mut p = Vec::with_capacity(5 + j_len + 5);
        p.extend_from_slice(&mxfp4_chals.chals_b);
        p.extend_from_slice(&mxfp4_chals.chals_j[..j_len]);
        p.extend_from_slice(&mxfp4_chals.chals_k);
        p
    };
    let mk_s_pt = |j_len: usize| -> Vec<Ext4> {
        let mut p = Vec::with_capacity(j_len + 5);
        p.extend_from_slice(&mxfp4_chals.chals_j[..j_len]);
        p.extend_from_slice(&mxfp4_chals.chals_k);
        p
    };
    let mut pt_lp_q = Vec::with_capacity(21);
    pt_lp_q.extend_from_slice(&qs_lp.0[..15]);
    pt_lp_q.push(Ext4::ZERO);
    pt_lp_q.extend_from_slice(&qs_lp.0[15..20]);
    let mut pt_lp_s = Vec::with_capacity(16);
    pt_lp_s.extend_from_slice(&qs_lp.1[..10]);
    pt_lp_s.push(Ext4::ZERO);
    pt_lp_s.extend_from_slice(&qs_lp.1[10..15]);

    let qs_claims = vec![
        JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: 0,
                    point: mk_q_pt(11),
                    weight: wq_0,
                },
                LinearTermExt4::PointEval {
                    subtable: 1,
                    point: mk_q_pt(10),
                    weight: wq_1,
                },
                LinearTermExt4::PointEval {
                    subtable: 2,
                    point: mk_q_pt(9),
                    weight: wq_2,
                },
            ],
            rhs: mxfp4_proof.finals.1,
        },
        JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: 3,
                    point: mk_s_pt(11),
                    weight: wq_0,
                },
                LinearTermExt4::PointEval {
                    subtable: 4,
                    point: mk_s_pt(10),
                    weight: wq_1,
                },
                LinearTermExt4::PointEval {
                    subtable: 5,
                    point: mk_s_pt(9),
                    weight: wq_2,
                },
            ],
            rhs: mxfp4_proof.finals.2,
        },
        JointLinearClaimExt4::point_eval(0, pt_lp_q, qs_lp.2),
        JointLinearClaimExt4::point_eval(3, pt_lp_s, qs_lp.3),
    ];

    let b_in_claims = vec![JointLinearClaimExt4::point_eval(
        0,
        z_bnd.clone(),
        b_in_eval,
    )];
    let b_out_claims = vec![JointLinearClaimExt4::point_eval(0, z_bnd, b_out_eval)];

    // Open ALL 6 WHIR Matrices in **ONE SINGLE SHARED WHIR CASCADE**!
    let whir_batch_proof = open_whir_batch_ext4(
        &[
            (&online_mat, &online_claims),
            (&gate_whir.qs_mat, &qs_claims),
            (b_in_mat, &b_in_claims),
            (b_out_mat, &b_out_claims),
            (&phase1.byte_commit.whir_mat, &byte_claims),
            (turn_weld_mat, &turn_weld_claims),
        ],
        WHIR_EXT4_T_QUERIES_100,
        &mut tr,
    );

    Ok(PayableComputeReceipt {
        commitment: phase1.commitment.clone(),
        countersig: countersig.clone(),
        beacon: *beacon,
        audited_gdn_slot: gdn_slot,
        audited_layer,
        audited_chunk,
        num_generated_tokens: k_gen,
        byte_pad_len: pad_len,
        byte_gm_limb_vars: phase1.byte_commit.gm_limb_vars,
        online_gm_limb_vars,
        b_in_whir_root: b_in_mat.root,
        b_out_whir_root: b_out_mat.root,
        b_in_trace_path,
        b_out_trace_path,
        carry_slot_whir_root: turn_weld_mat.root,
        carry_weld_path,
        layer_weight_path: registry.open_layer(audited_layer),
        layer_tensor_digests,
        gate_proj_tensor_slot: gate_proj_slot,
        qs_whir_root: gate_whir.qs_mat.root,
        online_whir_root: online_mat.root,
        rhs_eval_at_z,
        uw_eval_at_z,
        rem_eval_at_z,
        wy_l_eval,
        wy_uw_eval,
        wy_blinded_sc,
        slt_blinded_sc,
        d1b_wy8192_proof,
        b_at_zwy8192,
        mxfp4_proof,
        b_in_eval,
        b_out_eval,
        delta_gdn_eval,
        delta_mlp_eval,
        dfa_d1b_proof,
        q_at_dfa_leaf,
        b_at_dfa_leaf,
        q_next_at_dfa_leaf,
        eof_blinded_sc,
        q_next_at_zsh,
        shift_blinded_sc,
        final_acc_ext4,
        rom_d1b_proof,
        tok_at_zrom,
        is_pad_at_zrom,
        len_at_zrom,
        pow_at_zrom,
        val_at_zrom,
        acc_next_at_zacc,
        val_at_zacc,
        bpe_acc_sc,
        acc_at_racc,
        pow_at_racc,
        acc_next_at_zash,
        bpe_acc_shift_sc,
        cum_next_at_zcsh,
        emit_tok_eval,
        cw_sel_at_sb,
        cw_strict_lt_at_zlt,
        cw_lt_plus_sel_at_r,
        carry_subproof,
        whir_batch_proof,
    })
}

/// Standalone `< 25 ms` Verifier + Conserved Escrow Settlement for `PayableComputeReceipt` (`0` witness access!).
pub fn verify_payable_compute_receipt_and_settle(
    lease: &ProviderExecutionLease,
    rom: &QwenBpeRom,
    receipt_bytes: &[u8],
    opt_cleartext_bytes: Option<&[u8]>,
) -> Result<LeaseSettlement, String> {
    if rom.rom_merkle_root != lease.rom_merkle_root {
        return Err("rom.rom_merkle_root != lease.rom_merkle_root".into());
    }
    if lease.beacon_delay == 0 || lease.num_chunks == 0 {
        return Err("invalid lease parameters".into());
    }

    let r = PayableComputeReceipt::from_bytes(receipt_bytes)?;
    let c = &r.commitment;

    // 1. Verify Phase-1 Provider Commitment, Phase-2 Escrow Countersignature, & Phase-3 `drand` Beacon:
    if c.lease_id != lease.lease_id {
        return Err("commitment.lease_id != lease.lease_id".into());
    }
    if c.claimed_units > lease.max_units {
        return Err("claimed_units > lease.max_units".into());
    }
    if c.final_dfa_state >= 4 {
        return Err("Absent(\"sk-...\") rejected: final_dfa_state >= 4".into());
    }
    if lease.prompt_tokens.len() + r.num_generated_tokens != CARRY_TURN_TOKENS + 1
        || r.num_generated_tokens == 0
    {
        return Err("invalid num_generated_tokens".into());
    }
    if r.byte_pad_len != CANONICAL_BYTE_MIN_PAD
        || c.word_len.checked_add(2).is_none_or(|n| n > r.byte_pad_len)
    {
        return Err("byte_pad_len must equal canonical 2048 and cover word_len + 2".into());
    }
    if compute_content_root_v1(c.word_len, &c.byte_root) != c.content_root {
        return Err("content_root != H(word_len || byte_root)".into());
    }
    if compute_bpe_weld_root_v1(c.word_len, r.num_generated_tokens, &c.carry_weld_root)
        != c.bpe_weld_root
    {
        return Err(
            "bpe_weld_root != H(word_len || num_generated_tokens || carry_weld_root)".into(),
        );
    }
    let mut usage_in = [0u8; 16];
    usage_in[0..8].copy_from_slice(&c.claimed_units.to_le_bytes());
    usage_in[8..16].copy_from_slice(&(r.num_generated_tokens as u64).to_le_bytes());
    if cshake256_32(b"QW35-USAGE-ROOT-V1", &usage_in) != c.usage_root {
        return Err("usage_root mismatch".into());
    }

    let commit_digest = c.body_digest();
    verify_wots_signature(&lease.provider_pk, &commit_digest, &c.provider_sig)?;

    if r.countersig.commitment_digest != commit_digest {
        return Err("countersig.commitment_digest != provider commitment digest".into());
    }
    let want_target_round = r
        .countersig
        .round_commit
        .checked_add(lease.beacon_delay)
        .ok_or_else(|| "round_commit + beacon_delay overflow".to_string())?;
    if r.countersig.target_beacon_round != want_target_round
        || r.countersig.target_beacon_round > lease.expiry_round
    {
        return Err("countersig.target_beacon_round violates lease schedule/expiry".into());
    }
    let cs_msg = EscrowCountersignature::signing_message(
        &lease.lease_id,
        &commit_digest,
        r.countersig.round_commit,
        r.countersig.target_beacon_round,
    );
    verify_wots_signature(&lease.escrow_pk, &cs_msg, &r.countersig.escrow_sig)?;

    if r.beacon.round <= r.countersig.round_commit
        || r.beacon.round != r.countersig.target_beacon_round
        || r.beacon.round > lease.expiry_round
    {
        return Err("stale, off-schedule, or expired drand beacon round rejected".into());
    }
    bls_drand::verify_drand_quicknet_with_pk(&lease.drand_group_pk_g2, &r.beacon)?;

    let (want_gdn_slot, want_layer, want_chunk) = derive_post_countersig_audit_target(
        &lease.lease_id,
        &commit_digest,
        &r.countersig,
        &r.beacon,
        lease.num_chunks,
    );
    if r.audited_gdn_slot != want_gdn_slot
        || r.audited_layer != want_layer
        || r.audited_chunk != want_chunk
    {
        return Err(
            "audited (layer, token_chunk) does not match post-countersignature drand target".into(),
        );
    }

    if let Some(clear) = opt_cleartext_bytes {
        if clear.len() != c.word_len {
            return Err("cleartext length != committed word_len".into());
        }
        let (q_end, _) = run_padded_complement_sk_dfa(clear);
        if q_end >= 4 || q_end != c.final_dfa_state {
            return Err("cleartext fails padded-complement Absent DFA".into());
        }
    }

    // 2. Verify `trace_merkle_root`, `carry_weld_root`, & `weight_root` / `qs_binding`:
    let n_trace_leaves = (lease.num_chunks * 25).next_power_of_two().max(64);
    let in_idx = r.audited_chunk * 25 + r.audited_layer;
    let out_idx = in_idx + 1;
    if r.b_in_trace_path.index != in_idx
        || r.b_out_trace_path.index != out_idx
        || r.b_in_trace_path.leaf
            != hash_trace_boundary_leaf(r.audited_chunk, r.audited_layer, &r.b_in_whir_root)
        || r.b_out_trace_path.leaf
            != hash_trace_boundary_leaf(r.audited_chunk, r.audited_layer + 1, &r.b_out_whir_root)
        || !r
            .b_in_trace_path
            .verify(TRACE_NODE_DOM, &c.trace_merkle_root, n_trace_leaves)
        || !r
            .b_out_trace_path
            .verify(TRACE_NODE_DOM, &c.trace_merkle_root, n_trace_leaves)
    {
        return Err("trace_merkle_root boundary path verification failed".into());
    }

    if r.carry_weld_path.index != r.audited_gdn_slot
        || r.carry_weld_path.leaf
            != hash_carry_slot_leaf(r.audited_gdn_slot, &r.carry_slot_whir_root)
        || !r
            .carry_weld_path
            .verify(CARRY_TREE_DOM, &c.carry_weld_root, 32)
    {
        return Err("carry_weld_root Merkle path verification failed".into());
    }

    if r.gate_proj_tensor_slot >= r.layer_tensor_digests.len()
        || r.layer_weight_path.index != r.audited_layer
    {
        return Err("invalid gate_proj_tensor_slot or layer_weight_path".into());
    }
    let mut layer_buf = Vec::with_capacity(4 + r.layer_tensor_digests.len() * 32);
    layer_buf.extend_from_slice(&(r.audited_layer as u32).to_le_bytes());
    for d in &r.layer_tensor_digests {
        layer_buf.extend_from_slice(d);
    }
    if cshake256_32(b"QW35-LAYER-WEIGHT-LEAF-V1", &layer_buf) != r.layer_weight_path.leaf {
        return Err("layer weight leaf hash mismatch".into());
    }
    let n_wleaves = 1usize << r.layer_weight_path.siblings.len();
    if !r
        .layer_weight_path
        .verify(b"QW35-GLOBAL-WEIGHT-TREE-V1", &lease.weight_root, n_wleaves)
    {
        return Err("global weight_root Merkle path failed".into());
    }
    let mut qs_bind_in = [0u8; 64];
    qs_bind_in[0..32].copy_from_slice(&r.layer_tensor_digests[r.gate_proj_tensor_slot]);
    qs_bind_in[32..64].copy_from_slice(&r.qs_whir_root);
    if cshake256_32(b"QW35-QS-WHIR-BIND-V1", &qs_bind_in)
        != lease.gdn_qs_bindings[r.audited_gdn_slot]
    {
        return Err("qs_whir_root binding mismatch for audited GDN layer".into());
    }

    // 3. Replay Unified Fiat–Shamir Transcript:
    let log_h = 4usize; // `h_pad = 16`
    let log_c = 6usize; // `c_len = 64`
    let log_col = 8usize; // `wy_cols = 256`
    let m_wy_wit = 18usize;
    let m_abs = r.byte_pad_len.trailing_zeros() as usize; // 11
    let log_j = 12usize; // `j_pad = 4096`
    let log_k = 5usize; // `k_pad = 32`
    let bnd_vars = 16usize;

    let mut tr = CShakeTranscript::new(b"QW35-PAYABLE-COMPUTE-RECEIPT-V1");
    tr.absorb_root(b"pay_inv_key", &lease.invocation_key());
    tr.absorb_root(b"pay_commit_dig", &commit_digest);
    tr.absorb_u32(b"pay_r_commit_lo", r.countersig.round_commit as u32);
    tr.absorb_u32(b"pay_r_beacon_lo", r.beacon.round as u32);
    tr.absorb_root(b"pay_drand_rand", &r.beacon.randomness);
    tr.absorb_u32(b"pay_layer", r.audited_layer as u32);
    tr.absorb_u32(b"pay_chunk", r.audited_chunk as u32);
    tr.absorb_root(b"pay_bin_root", &r.b_in_whir_root);
    tr.absorb_root(b"pay_bout_root", &r.b_out_whir_root);
    tr.absorb_root(b"pay_qs_root", &r.qs_whir_root);
    tr.absorb_root(b"pay_cwslot_root", &r.carry_slot_whir_root);

    let beta_ext4 = tr.squeeze_ext4(b"pay_bpe_beta", true);
    tr.absorb_root(b"pay_online_root", &r.online_whir_root);
    tr.absorb_ext4(b"pay_fin_acc", r.final_acc_ext4);

    // Section A: WY + SLT + Consolidated `[UW, RHS, rem, L, b, q] in [0, 8192)` + MXFP4 + U1
    let z_h = tr.squeeze_ext4_vec(b"wy_zh", log_h, true);
    let z_i = tr.squeeze_ext4_vec(b"wy_zi", log_c, true);
    let z_k = tr.squeeze_ext4_vec(b"wy_zk", log_col, true);
    let mut z_hik = Vec::with_capacity(m_wy_wit);
    z_hik.extend_from_slice(&z_h);
    z_hik.extend_from_slice(&z_i);
    z_hik.extend_from_slice(&z_k);
    for e in [r.rhs_eval_at_z, r.uw_eval_at_z, r.rem_eval_at_z] {
        tr.absorb_ext4(b"wy_ev", e);
    }
    let wy_claim = r
        .rhs_eval_at_z
        .sub(r.uw_eval_at_z)
        .scale_bb(WY_SCALE as u32)
        .add(Ext4::from_bb((WY_SCALE / 2) as u32))
        .sub(r.rem_eval_at_z);
    let (wy_rho, wy_chals, wy_term) =
        verify_gmask_einsum_ext4(wy_claim, log_h, log_c, &z_h, &r.wy_blinded_sc, &mut tr)?;
    tr.absorb_ext4(b"wy_l_ev", r.wy_l_eval);
    tr.absorb_ext4(b"wy_uw_ev", r.wy_uw_eval);

    let m_slt = log_h + 2 * log_c;
    let z_slt = tr.squeeze_ext4_vec(b"slt_z", m_slt, true);
    let (slt_rho, slt_chals, slt_term) =
        verify_gmask_einsum_ext4(Ext4::ZERO, m_slt, 0, &z_slt, &r.slt_blinded_sc, &mut tr)?;

    if r.d1b_wy8192_proof.m_wit != 21 || r.d1b_wy8192_proof.m_tab != 13 {
        return Err("WY d1b_wy8192_proof dimension mismatch".into());
    }
    let z_wy8192 = verify_d1b_range_ext4(&r.d1b_wy8192_proof, &mut tr)?;
    tr.absorb_ext4(b"wy_bz", r.b_at_zwy8192);

    let r_i_mxfp4 = tr.squeeze_ext4_vec(b"mxfp4_ri", log_c, true);
    let r_j_mxfp4 = tr.squeeze_ext4_vec(b"mxfp4_rj", log_j, true);
    if r.mxfp4_proof.log_j != log_j || r.mxfp4_proof.log_k != log_k {
        return Err("audited gate_proj mxfp4_proof log_j/log_k mismatch".into());
    }
    let mxfp4_chals = verify_mxfp4_delayed_bjk_horner_ext4(
        r.mxfp4_proof.claim,
        &r_j_mxfp4,
        &r.mxfp4_proof,
        &mut tr,
    )?;

    let z_bnd = tr.squeeze_ext4_vec(b"u1_zb", bnd_vars, true);
    for e in [
        r.b_in_eval,
        r.b_out_eval,
        r.delta_gdn_eval,
        r.delta_mlp_eval,
    ] {
        tr.absorb_ext4(b"u1_ev", e);
    }
    if r.b_out_eval != r.b_in_eval.add(r.delta_gdn_eval).add(r.delta_mlp_eval) {
        return Err("U1 residual weld B_{l*+1} == B_{l*} + delta_gdn + delta_mlp failed".into());
    }

    // Section B: `Absent("sk-...")`
    let pub_dfa_tab = build_collision_free_sk_dfa_table_4096();
    if r.dfa_d1b_proof.m_wit != m_abs || r.dfa_d1b_proof.m_tab != 11 {
        return Err("Absent dfa_d1b_proof dimension mismatch".into());
    }
    let z_dfa_leaf = verify_d1b_public_table_ext4(&pub_dfa_tab, &r.dfa_d1b_proof, &mut tr)?;
    for e in [r.q_at_dfa_leaf, r.b_at_dfa_leaf, r.q_next_at_dfa_leaf] {
        tr.absorb_ext4(b"abs_dl", e);
    }
    let want_dfa_tup = r
        .q_at_dfa_leaf
        .add(r.b_at_dfa_leaf.scale_bb(8))
        .add(r.q_next_at_dfa_leaf.scale_bb(4096));
    if r.dfa_d1b_proof.rem_leaf_eval != want_dfa_tup {
        return Err("Absent DFA tuple linear relation q + 8*b + 4096*q_next failed".into());
    }

    let z_eof = tr.squeeze_ext4_vec(b"abs_zeof", m_abs, true);
    let (eof_rho, eof_chals, eof_term) =
        verify_gmask_einsum_ext4(Ext4::ZERO, m_abs, 0, &z_eof, &r.eof_blinded_sc, &mut tr)?;

    let z_sh = tr.squeeze_ext4_vec(b"abs_zsh", m_abs, true);
    tr.absorb_ext4(b"abs_qn", r.q_next_at_zsh);
    let eq_zsh_last = {
        let mut prod = Ext4::ONE;
        for &zi in &z_sh {
            prod = prod.mul(zi);
        }
        prod
    };
    let want_sh_claim = r
        .q_next_at_zsh
        .sub(eq_zsh_last.scale_bb(c.final_dfa_state as u32));
    let (sh_rho, sh_chals, sh_term) =
        verify_gmask_einsum_ext4(want_sh_claim, 0, m_abs, &[], &r.shift_blinded_sc, &mut tr)?;

    // Section C: Post-Commitment `QwenBpeRom` Token-to-Byte Weld
    let rom_gammas = [
        tr.squeeze_ext4(b"bpe_rg0", true),
        tr.squeeze_ext4(b"bpe_rg1", true),
        tr.squeeze_ext4(b"bpe_rg2", true),
        tr.squeeze_ext4(b"bpe_rg3", true),
    ];
    if r.rom_d1b_proof.m_wit != 7 {
        return Err("rom_d1b_proof m_wit != 7".into());
    }
    let z_rom_tab =
        verify_d1b_qwen_rom_fast(rom, beta_ext4, rom_gammas, &r.rom_d1b_proof, &mut tr)?;
    let z_rom_wit = z_rom_tab[..7].to_vec();
    for e in [
        r.tok_at_zrom,
        r.is_pad_at_zrom,
        r.len_at_zrom,
        r.pow_at_zrom,
        r.val_at_zrom,
    ] {
        tr.absorb_ext4(b"bpe_rom_ev", e);
    }
    let want_rom_wit = r
        .tok_at_zrom
        .add(rom_gammas[0].mul(r.is_pad_at_zrom))
        .add(rom_gammas[1].mul(r.len_at_zrom))
        .add(rom_gammas[2].mul(r.pow_at_zrom))
        .add(rom_gammas[3].mul(r.val_at_zrom));
    if r.rom_d1b_proof.wit_leaf_eval != want_rom_wit {
        return Err("BPE ROM tuple decomposition mismatch at z_rom_wit".into());
    }

    let z_acc = tr.squeeze_ext4_vec(b"bpe_zacc", 7, true);
    tr.absorb_ext4(b"bpe_anz", r.acc_next_at_zacc);
    tr.absorb_ext4(b"bpe_vz", r.val_at_zacc);
    let (bacc_rho, bacc_chals, bacc_term) = verify_gmask_einsum_ext4(
        r.acc_next_at_zacc.sub(r.val_at_zacc),
        7,
        0,
        &z_acc,
        &r.bpe_acc_sc,
        &mut tr,
    )?;
    tr.absorb_ext4(b"bpe_ar", r.acc_at_racc);
    tr.absorb_ext4(b"bpe_pr", r.pow_at_racc);

    let z_ash = tr.squeeze_ext4_vec(b"bpe_zash", 7, true);
    tr.absorb_ext4(b"bpe_ansh", r.acc_next_at_zash);
    let eq_zash = build_eq_table_lsb_ext4(&z_ash);
    let want_ash_claim = r
        .acc_next_at_zash
        .sub(eq_zash[CARRY_TURN_TOKENS - 1].mul(r.final_acc_ext4));
    let (bash_rho, bash_chals, bash_term) =
        verify_gmask_einsum_ext4(want_ash_claim, 0, 7, &[], &r.bpe_acc_shift_sc, &mut tr)?;

    let z_clen = tr.squeeze_ext4_vec(b"bpe_zcl", 7, true);
    let z_csh = tr.squeeze_ext4_vec(b"bpe_zcsh", 7, true);
    tr.absorb_ext4(b"bpe_cnsh", r.cum_next_at_zcsh);
    let eq_zcsh = build_eq_table_lsb_ext4(&z_csh);
    let mut csh_col = vec![Ext4::ZERO; CARRY_TURN_TOKENS];
    csh_col[1..CARRY_TURN_TOKENS].copy_from_slice(&eq_zcsh[..(CARRY_TURN_TOKENS - 1)]);

    let z_emit = tr.squeeze_ext4_vec(b"bpe_zemit", 7, true);
    tr.absorb_ext4(b"bpe_emitev", r.emit_tok_eval);

    // Section D: `SpecPrefill` Token-Carry & Looped Residual-Carry
    if !(6..=12).contains(&r.online_gm_limb_vars) || !(6..=12).contains(&r.byte_gm_limb_vars) {
        return Err("invalid gm_limb_vars".into());
    }
    let gm_specs = vec![
        GMaskSpecExt4::new("wy_sc", log_h + log_c, 3),
        GMaskSpecExt4::new("slt_sc", log_h + 2 * log_c, 3),
        GMaskSpecExt4::new("shift_sc", m_abs, 3),
        GMaskSpecExt4::new("bpe_acc", 7, 3),
        GMaskSpecExt4::new("bpe_ash", 7, 3),
        GMaskSpecExt4::new("cw_sbool", 13, 3),
        GMaskSpecExt4::new("cw_ltsh", 13, 3),
        GMaskSpecExt4::new("cw_seltgt", 13, 3),
    ];
    let gm_ids = [19usize, 20, 21, 22];
    let want_online_gm_len = 1usize << r.online_gm_limb_vars;

    let (mut turn_weld_claims, cw_online_claims, qs_lp) = replay_carry_weld_verifier_transcript(
        &lease.prompt_tokens,
        &r.carry_subproof,
        CarryWeldVerifierClaims {
            sel_at_sb: r.cw_sel_at_sb,
            strict_lt_at_zlt: r.cw_strict_lt_at_zlt,
            lt_plus_sel_at_r: r.cw_lt_plus_sel_at_r,
        },
        CarryWeldMaskCfg {
            gm_specs: &gm_specs,
            gm_ids,
            mult_u16_sub: 17,
            mult_rem11_sub: 18,
        },
        want_online_gm_len,
        &mut tr,
    )?;

    let eq_emit = build_eq_table_lsb_ext4(&z_emit);
    let p_len = lease.prompt_tokens.len();
    let k_gen = r.num_generated_tokens;
    let mut w_emit_y = vec![Ext4::ZERO; CARRY_TURN_TOKENS];
    let mut pad_tail_emit = Ext4::ZERO;
    for i in 0..CARRY_TURN_TOKENS {
        if i < k_gen {
            w_emit_y[p_len - 1 + i] = eq_emit[i];
        } else {
            pad_tail_emit = pad_tail_emit.add(eq_emit[i].scale_bb(PAD_TOK_ID));
        }
    }
    let is_pad_want = eq_emit[k_gen..CARRY_TURN_TOKENS]
        .iter()
        .fold(Ext4::ZERO, |a, &e| a.add(e));
    let eq_zcsh_last = eq_zcsh[CARRY_TURN_TOKENS - 1];
    turn_weld_claims.extend([
        JointLinearClaimExt4 {
            terms: vec![LinearTermExt4::DenseSmall {
                subtable: 2,
                weights_lsb: w_emit_y,
            }],
            rhs: r.emit_tok_eval.sub(pad_tail_emit),
        },
        JointLinearClaimExt4::point_eval(19, z_rom_wit.clone(), r.tok_at_zrom),
        JointLinearClaimExt4::point_eval(19, z_emit.clone(), r.emit_tok_eval),
        JointLinearClaimExt4::point_eval(20, z_rom_wit.clone(), r.is_pad_at_zrom),
        JointLinearClaimExt4::point_eval(20, z_emit, is_pad_want),
        JointLinearClaimExt4::point_eval(21, z_rom_wit.clone(), r.len_at_zrom),
        JointLinearClaimExt4::point_eval(22, vec![Ext4::ZERO; 7], Ext4::ZERO),
        JointLinearClaimExt4::point_eval(23, vec![Ext4::ONE; 7], Ext4::from_bb(c.word_len as u32)),
        JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: 23,
                    point: z_clen.clone(),
                    weight: Ext4::ONE,
                },
                LinearTermExt4::PointEval {
                    subtable: 22,
                    point: z_clen.clone(),
                    weight: Ext4::ONE.neg(),
                },
                LinearTermExt4::PointEval {
                    subtable: 21,
                    point: z_clen,
                    weight: Ext4::ONE.neg(),
                },
            ],
            rhs: Ext4::ZERO,
        },
        JointLinearClaimExt4::point_eval(23, z_csh, r.cum_next_at_zcsh),
        JointLinearClaimExt4 {
            terms: vec![LinearTermExt4::DenseSmall {
                subtable: 22,
                weights_lsb: csh_col,
            }],
            rhs: r
                .cum_next_at_zcsh
                .sub(eq_zcsh_last.scale_bb(c.word_len as u32)),
        },
    ]);

    // Rebuild all 6 matrix claim lists & shapes and verify ONE shared WHIR cascade:
    let (zb0, zb1, limb_scale) = eval_packed_ext4_limb_consts();
    let packed_pt = |pt: &[Ext4]| -> Vec<Ext4> {
        let mut out = Vec::with_capacity(pt.len() + 2);
        out.extend_from_slice(pt);
        out.push(zb0);
        out.push(zb1);
        out
    };
    let inv_limb_scale = limb_scale.inv().unwrap();

    let (wy_ws, wy_wa) = GMaskExt4::build_spec_weights(&gm_specs, "wy_sc", &wy_chals);
    let (slt_ws, slt_wa) = GMaskExt4::build_spec_weights(&gm_specs, "slt_sc", &slt_chals);
    let (sh_ws, sh_wa) = GMaskExt4::build_spec_weights(&gm_specs, "shift_sc", &sh_chals);
    let (bacc_ws, bacc_wa) = GMaskExt4::build_spec_weights(&gm_specs, "bpe_acc", &bacc_chals);
    let (bash_ws, bash_wa) = GMaskExt4::build_spec_weights(&gm_specs, "bpe_ash", &bash_chals);

    let mut l_pt1 = Vec::new();
    l_pt1.extend_from_slice(&wy_chals[..log_h]);
    l_pt1.extend_from_slice(&z_i);
    l_pt1.extend_from_slice(&wy_chals[log_h..]);
    let mut uw_pt2 = Vec::new();
    uw_pt2.extend_from_slice(&wy_chals[..log_h]);
    uw_pt2.extend_from_slice(&wy_chals[log_h..]);
    uw_pt2.extend_from_slice(&z_k);

    let mut pt_x = Vec::new();
    pt_x.extend_from_slice(&r_i_mxfp4);
    pt_x.extend_from_slice(&mxfp4_chals.chals_b);
    pt_x.extend_from_slice(&mxfp4_chals.chals_k);
    let mut pt_y = Vec::new();
    pt_y.extend_from_slice(&r_i_mxfp4);
    pt_y.extend_from_slice(&r_j_mxfp4);

    let non_slt_factor = eq_mle_ext4(&z_slt, &slt_chals).mul(eval_non_slt_mask_mle_local(
        &slt_chals[log_h..log_h + log_c],
        &slt_chals[log_h + log_c..],
    ));
    let shift_factor_abs = eval_shift_kernel_128(&z_sh, &sh_chals);
    let wy_unm_term = eq_mle_ext4(&z_h, &wy_chals[..log_h])
        .mul(r.wy_l_eval)
        .mul(r.wy_uw_eval);
    let bacc_unm_term = eq_mle_ext4(&z_acc, &bacc_chals)
        .mul(r.acc_at_racc)
        .mul(r.pow_at_racc);
    let bash_k = eval_shift_kernel_128(&z_ash, &bash_chals);

    let w_o8 = build_eq_table_lsb_ext4(&z_wy8192[18..21]);
    let w_s4 = build_eq_table_lsb_ext4(&z_wy8192[16..18]);
    let w_b32 = build_eq_table_lsb_ext4(&z_wy8192[11..16]);
    let w_oct4_s0 = w_o8[4].mul(w_s4[0]);
    let w_oct4_s1 = w_o8[4].mul(w_s4[1]);
    let w_q_zwy = w_oct4_s1.mul(w_b32[2].add(w_b32[3]));
    let eof_bias_zwy =
        eval_eof_ind_mle_local(c.word_len, r.byte_pad_len, &z_wy8192[..m_abs]).scale_bb(256);
    let b_unb_zwy = r.b_at_zwy8192.sub(eof_bias_zwy);
    let b_contrib_zwy = w_oct4_s1.mul(w_b32[0].add(w_b32[1])).mul(b_unb_zwy);
    let bias_wy8192 = w_o8[0]
        .add(w_o8[1])
        .add(w_o8[3])
        .add(w_oct4_s0)
        .scale_bb(4096)
        .add(w_oct4_s1.mul(w_b32[1].scale_bb(7936).add(w_b32[3].scale_bb(8184))));

    let mut online_claims = vec![
        JointLinearClaimExt4::point_eval(0, l_pt1, r.wy_l_eval),
        JointLinearClaimExt4::point_eval(1, z_hik.clone(), r.rhs_eval_at_z),
        JointLinearClaimExt4::point_eval(2, z_hik.clone(), r.uw_eval_at_z),
        JointLinearClaimExt4::point_eval(2, uw_pt2, r.wy_uw_eval),
        JointLinearClaimExt4::point_eval(3, z_hik, r.rem_eval_at_z),
        JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: 2,
                    point: z_wy8192[..18].to_vec(),
                    weight: w_o8[0],
                },
                LinearTermExt4::PointEval {
                    subtable: 1,
                    point: z_wy8192[..18].to_vec(),
                    weight: w_o8[1],
                },
                LinearTermExt4::PointEval {
                    subtable: 3,
                    point: z_wy8192[..18].to_vec(),
                    weight: w_o8[2].add(w_o8[3]),
                },
                LinearTermExt4::PointEval {
                    subtable: 0,
                    point: z_wy8192[..16].to_vec(),
                    weight: w_oct4_s0,
                },
                LinearTermExt4::PointEval {
                    subtable: 9,
                    point: z_wy8192[..m_abs].to_vec(),
                    weight: w_q_zwy,
                },
            ],
            rhs: r
                .d1b_wy8192_proof
                .rem_leaf_eval
                .sub(b_contrib_zwy)
                .sub(bias_wy8192),
        },
        JointLinearClaimExt4::point_eval(
            4,
            z_wy8192[..13].to_vec(),
            r.d1b_wy8192_proof.mult_leaf_eval,
        ),
        JointLinearClaimExt4::point_eval(5, pt_x, r.mxfp4_proof.finals.0),
        JointLinearClaimExt4::point_eval(6, pt_y, r.mxfp4_proof.claim),
        JointLinearClaimExt4::point_eval(7, z_bnd.clone(), r.delta_gdn_eval),
        JointLinearClaimExt4::point_eval(8, z_bnd.clone(), r.delta_mlp_eval),
        JointLinearClaimExt4::point_eval(9, vec![Ext4::ZERO; m_abs], Ext4::ZERO),
        JointLinearClaimExt4::point_eval(9, z_dfa_leaf.clone(), r.q_at_dfa_leaf),
        JointLinearClaimExt4::point_eval(10, z_dfa_leaf.clone(), r.q_next_at_dfa_leaf),
        JointLinearClaimExt4::point_eval(10, z_sh, r.q_next_at_zsh),
        JointLinearClaimExt4::point_eval(
            11,
            z_dfa_leaf[..11].to_vec(),
            r.dfa_d1b_proof.mult_leaf_eval,
        ),
        JointLinearClaimExt4::point_eval(
            12,
            packed_pt(&z_rom_wit),
            r.pow_at_zrom.mul(inv_limb_scale),
        ),
        JointLinearClaimExt4::point_eval(
            12,
            packed_pt(&bacc_chals),
            r.pow_at_racc.mul(inv_limb_scale),
        ),
        JointLinearClaimExt4::point_eval(
            13,
            packed_pt(&z_rom_wit),
            r.val_at_zrom.mul(inv_limb_scale),
        ),
        JointLinearClaimExt4::point_eval(13, packed_pt(&z_acc), r.val_at_zacc.mul(inv_limb_scale)),
        JointLinearClaimExt4::point_eval(14, packed_pt(&[Ext4::ZERO; 7]), Ext4::ZERO),
        JointLinearClaimExt4::point_eval(
            14,
            packed_pt(&bacc_chals),
            r.acc_at_racc.mul(inv_limb_scale),
        ),
        JointLinearClaimExt4::point_eval(
            15,
            packed_pt(&[Ext4::ONE; 7]),
            r.final_acc_ext4.mul(inv_limb_scale),
        ),
        JointLinearClaimExt4::point_eval(
            15,
            packed_pt(&z_acc),
            r.acc_next_at_zacc.mul(inv_limb_scale),
        ),
        JointLinearClaimExt4::point_eval(
            15,
            packed_pt(&z_ash),
            r.acc_next_at_zash.mul(inv_limb_scale),
        ),
        JointLinearClaimExt4::point_eval(16, z_rom_tab, r.rom_d1b_proof.mult_leaf_eval),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &wy_ws, r.wy_blinded_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_ids,
            &wy_wa,
            wy_rho,
            wy_term.sub(wy_unm_term),
        ),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &slt_ws, r.slt_blinded_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            vec![LinearTermExt4::PointEval {
                subtable: 0,
                point: slt_chals,
                weight: non_slt_factor,
            }],
            gm_ids,
            &slt_wa,
            slt_rho,
            slt_term,
        ),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &sh_ws, r.shift_blinded_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            vec![LinearTermExt4::PointEval {
                subtable: 9,
                point: sh_chals,
                weight: shift_factor_abs,
            }],
            gm_ids,
            &sh_wa,
            sh_rho,
            sh_term,
        ),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &bacc_ws, r.bpe_acc_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_ids,
            &bacc_wa,
            bacc_rho,
            bacc_term.sub(bacc_unm_term),
        ),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &bash_ws, r.bpe_acc_shift_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            vec![LinearTermExt4::PointEval {
                subtable: 14,
                point: packed_pt(&bash_chals),
                weight: bash_k.mul(limb_scale),
            }],
            gm_ids,
            &bash_wa,
            bash_rho,
            bash_term,
        ),
    ];
    online_claims.extend(cw_online_claims);

    let (w_horner, c_horner) = build_horner_byte_weights(beta_ext4, c.word_len, r.byte_pad_len);
    let byte_specs = vec![GMaskSpecExt4::new("eof_sc", m_abs, 3)];
    let (byte_eof_ws, byte_eof_wa) =
        GMaskExt4::build_spec_weights(&byte_specs, "eof_sc", &eof_chals);
    if byte_eof_ws.len() != (1usize << r.byte_gm_limb_vars) {
        return Err("byte_gm_limb_vars mismatch".into());
    }
    let f_eof_byte = eq_mle_ext4(&z_eof, &eof_chals).mul(eval_eof_ind_mle_local(
        c.word_len,
        r.byte_pad_len,
        &eof_chals,
    ));
    let byte_claims = vec![
        JointLinearClaimExt4::point_eval(0, z_dfa_leaf, r.b_at_dfa_leaf),
        JointLinearClaimExt4::point_eval(0, z_wy8192[..m_abs].to_vec(), r.b_at_zwy8192),
        JointLinearClaimExt4 {
            terms: vec![LinearTermExt4::DenseSmall {
                subtable: 0,
                weights_lsb: w_horner,
            }],
            rhs: r.final_acc_ext4.sub(c_horner),
        },
        JointLinearClaimExt4::gmask_sum_claim(
            [5, 6, 7, 8],
            &byte_eof_ws,
            r.eof_blinded_sc.gmask_sum,
        ),
        JointLinearClaimExt4::hvzk_terminal_weld(
            vec![LinearTermExt4::PointEval {
                subtable: 0,
                point: eof_chals,
                weight: f_eof_byte,
            }],
            [5, 6, 7, 8],
            &byte_eof_wa,
            eof_rho,
            eof_term.add(f_eof_byte.scale_bb(256)),
        ),
    ];

    let j9 = mxfp4_chals.chals_j[9];
    let j10 = mxfp4_chals.chals_j[10];
    let j11 = mxfp4_chals.chals_j[11];
    let wq_0 = Ext4::ONE.sub(j11);
    let wq_1 = j11.mul(Ext4::ONE.sub(j10));
    let wq_2 = j11.mul(j10).mul(Ext4::ONE.sub(j9));
    let mk_q_pt = |j_len: usize| -> Vec<Ext4> {
        let mut p = Vec::with_capacity(5 + j_len + 5);
        p.extend_from_slice(&mxfp4_chals.chals_b);
        p.extend_from_slice(&mxfp4_chals.chals_j[..j_len]);
        p.extend_from_slice(&mxfp4_chals.chals_k);
        p
    };
    let mk_s_pt = |j_len: usize| -> Vec<Ext4> {
        let mut p = Vec::with_capacity(j_len + 5);
        p.extend_from_slice(&mxfp4_chals.chals_j[..j_len]);
        p.extend_from_slice(&mxfp4_chals.chals_k);
        p
    };
    let mut pt_lp_q = Vec::with_capacity(21);
    pt_lp_q.extend_from_slice(&qs_lp.0[..15]);
    pt_lp_q.push(Ext4::ZERO);
    pt_lp_q.extend_from_slice(&qs_lp.0[15..20]);
    let mut pt_lp_s = Vec::with_capacity(16);
    pt_lp_s.extend_from_slice(&qs_lp.1[..10]);
    pt_lp_s.push(Ext4::ZERO);
    pt_lp_s.extend_from_slice(&qs_lp.1[10..15]);

    let qs_claims = vec![
        JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: 0,
                    point: mk_q_pt(11),
                    weight: wq_0,
                },
                LinearTermExt4::PointEval {
                    subtable: 1,
                    point: mk_q_pt(10),
                    weight: wq_1,
                },
                LinearTermExt4::PointEval {
                    subtable: 2,
                    point: mk_q_pt(9),
                    weight: wq_2,
                },
            ],
            rhs: r.mxfp4_proof.finals.1,
        },
        JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: 3,
                    point: mk_s_pt(11),
                    weight: wq_0,
                },
                LinearTermExt4::PointEval {
                    subtable: 4,
                    point: mk_s_pt(10),
                    weight: wq_1,
                },
                LinearTermExt4::PointEval {
                    subtable: 5,
                    point: mk_s_pt(9),
                    weight: wq_2,
                },
            ],
            rhs: r.mxfp4_proof.finals.2,
        },
        JointLinearClaimExt4::point_eval(0, pt_lp_q, qs_lp.2),
        JointLinearClaimExt4::point_eval(3, pt_lp_s, qs_lp.3),
    ];

    let b_in_claims = vec![JointLinearClaimExt4::point_eval(
        0,
        z_bnd.clone(),
        r.b_in_eval,
    )];
    let b_out_claims = vec![JointLinearClaimExt4::point_eval(0, z_bnd, r.b_out_eval)];

    let online_shape = WhirExt4MatrixShape::for_subtables(
        &[
            16,
            18,
            18,
            18,
            13,
            16,
            18,
            16,
            16,
            m_abs,
            m_abs,
            11,
            9,
            9,
            9,
            9,
            18,
            16,
            11,
            r.online_gm_limb_vars,
            r.online_gm_limb_vars,
            r.online_gm_limb_vars,
            r.online_gm_limb_vars,
        ],
        true,
        WHIR_EXT4_BLOWUP,
    );
    let qs_shape = CompactWhirMxfp4::expected_shape();
    let bnd_shape = WhirExt4MatrixShape::single_table(16, true);
    let byte_shape = SaltedByteWhirCommitment::expected_shape(r.byte_pad_len, r.byte_gm_limb_vars);
    let turn_weld_shape = SpecPrefillCarryWitness::expected_turn_weld_shape();

    verify_whir_batch_ext4(
        &[
            (&r.online_whir_root, &online_shape, &online_claims),
            (&r.qs_whir_root, &qs_shape, &qs_claims),
            (&r.b_in_whir_root, &bnd_shape, &b_in_claims),
            (&r.b_out_whir_root, &bnd_shape, &b_out_claims),
            (&c.byte_root, &byte_shape, &byte_claims),
            (&r.carry_slot_whir_root, &turn_weld_shape, &turn_weld_claims),
        ],
        WHIR_EXT4_T_QUERIES_100,
        &r.whir_batch_proof,
        &mut tr,
    )?;

    // 4. Conserved `ProviderExecutionLease` Payout + Refund (`paid + refunded == prepaid_budget()`):
    let paid = (lease.base_fee as u128) + (c.claimed_units as u128) * (lease.unit_price as u128);
    let budget = lease.prepaid_budget();
    let refunded = budget
        .checked_sub(paid)
        .ok_or_else(|| "paid exceeded prepaid_budget".to_string())?;
    debug_assert_eq!(paid + refunded, budget);

    Ok(LeaseSettlement {
        paid,
        refunded,
        provider_invocation_key: lease.invocation_key(),
        provider_evidence_root: c.provider_evidence_root(),
        audited_gdn_layer: r.audited_layer,
        audited_token_chunk: r.audited_chunk,
        expired_refund_only: false,
    })
}
