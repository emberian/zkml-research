//! Extended-Basis RNS-NTT Hoisted `ct x ct` Engine (`N = 8192`, `3` `Qp` + `5` `Bp` = `8` 61-bit NTT primes).
//!
//! Provides:
//! - Negacyclic (`X^N + 1`) + Cyclic (`X^N - 1`) `O(N log N)` NTTs across all 8 primes for both
//!   fast homomorphic execution and exact ring-quotient `K_{k,p}^{(r)}(X)` extraction;
//! - Precomputed NTT representations (`PrecomputedCt`, `PrecomputedGrid`) for persistent encrypted
//!   weights (`vFHEML`, `Hoist(b, tau=64)`, `Dark-vPIR`) and deduplicated input vectors;
//! - `rayon`-parallel 32-block lazy-`u128` tensor accumulation across `(c0, c1, c2)`, single inverse
//!   NTT per output group `r`, and single exact BEHZ integer rescale;
//! - RNS-gadget relinearization (`P_ks = bp[0]`, four 60-bit limbs from `w = 20` digits) and
//!   `TemporalOuterAccumulator` (`tau`-step outer-product accumulation before BEHZ rescale + relin).

use crate::bigint::{behz_rescale_from_8limbs, crt3_unsigned, lift_q_to_8limbs_and_u, SignedU320};
use crate::{FastPrime61, HoistedParams};
use darkstep::arith::{addmod, from_i64, invmod, mulmod, mulmod_shoup, powmod, shoup, submod};
use darkstep::bfv::{Ct, OwnKey};
use darkstep::ntt::Ntt;
use darkstep::rns::Rns;
use pycompat::PyRandom;
use rayon::prelude::*;
use std::sync::Arc;

/// 3-component ciphertext in `Qp` RNS form (limb-major `k * N + j`, `3 * N` words per component).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ct3 {
    pub c0: Vec<u64>,
    pub c1: Vec<u64>,
    pub c2: Vec<u64>,
}

/// Cyclic NTT of power-of-two length `N` over `Z_q[X]/(X^N - 1)` with Shoup twiddles.
/// Paired with `darkstep::ntt::Ntt` (`X^N + 1`), recovers the exact integer ring quotient
/// `K(X) = ((P mod (X^N - 1)) - (P mod (X^N + 1))) / 2 mod q` in `O(N log N)`.
pub struct CyclicNtt {
    pub q: u64,
    pub n: usize,
    tw: Vec<u64>,
    tw_s: Vec<u64>,
    itw: Vec<u64>,
    itw_s: Vec<u64>,
    ninv: u64,
    ninv_s: u64,
}

impl CyclicNtt {
    pub fn new(q: u64, n: usize) -> Self {
        assert!(n.is_power_of_two() && (q - 1) % (2 * n as u64) == 0);
        let mut psi0 = 0u64;
        for g in 2u64.. {
            let c = powmod(g, (q - 1) / (2 * n as u64), q);
            if powmod(c, n as u64, q) == q - 1 {
                psi0 = c;
                break;
            }
        }
        let omega = mulmod(psi0, psi0, q);
        let iomega = invmod(omega, q);
        let half = n / 2;
        let mut tw = vec![0u64; half];
        let mut itw = vec![0u64; half];
        let mut cur = 1u64;
        let mut icur = 1u64;
        for k in 0..half {
            tw[k] = cur;
            itw[k] = icur;
            cur = mulmod(cur, omega, q);
            icur = mulmod(icur, iomega, q);
        }
        let tw_s = tw.iter().map(|&w| shoup(w, q)).collect();
        let itw_s = itw.iter().map(|&w| shoup(w, q)).collect();
        let ninv = invmod(n as u64, q);
        CyclicNtt {
            q,
            n,
            tw,
            tw_s,
            itw,
            itw_s,
            ninv,
            ninv_s: shoup(ninv, q),
        }
    }

    #[inline]
    fn bitrev_permute(a: &mut [u64]) {
        let n = a.len();
        let lg = n.trailing_zeros();
        for i in 0..n {
            let r = if lg == 0 { 0 } else { i.reverse_bits() >> (usize::BITS - lg) };
            if i < r {
                a.swap(i, r);
            }
        }
    }

    pub fn forward(&self, a: &mut [u64]) {
        let (q, n) = (self.q, self.n);
        Self::bitrev_permute(a);
        let mut len = 2;
        while len <= n {
            let half = len / 2;
            let step = n / len;
            for st in (0..n).step_by(len) {
                let (lo, hi) = a[st..st + len].split_at_mut(half);
                for j in 0..half {
                    let idx = j * step;
                    let u = lo[j];
                    let v = mulmod_shoup(hi[j], self.tw[idx], self.tw_s[idx], q);
                    lo[j] = addmod(u, v, q);
                    hi[j] = submod(u, v, q);
                }
            }
            len <<= 1;
        }
    }

    pub fn inverse(&self, a: &mut [u64]) {
        let (q, n) = (self.q, self.n);
        Self::bitrev_permute(a);
        let mut len = 2;
        while len <= n {
            let half = len / 2;
            let step = n / len;
            for st in (0..n).step_by(len) {
                let (lo, hi) = a[st..st + len].split_at_mut(half);
                for j in 0..half {
                    let idx = j * step;
                    let u = lo[j];
                    let v = mulmod_shoup(hi[j], self.itw[idx], self.itw_s[idx], q);
                    lo[j] = addmod(u, v, q);
                    hi[j] = submod(u, v, q);
                }
            }
            len <<= 1;
        }
        for x in a.iter_mut() {
            *x = mulmod_shoup(*x, self.ninv, self.ninv_s, q);
        }
    }
}

/// Precomputed extended-basis NTT ciphertext across all 8 61-bit primes (`8 * N` words per poly).
#[derive(Clone, Debug)]
pub struct PrecomputedCt {
    /// Negacyclic (`X^N + 1`) NTT of `(c0, c1)` lifted to `Qp union Bp`, limb-major `l * N + j`.
    pub c0_neg_ntt: Vec<u64>,
    pub c1_neg_ntt: Vec<u64>,
    /// Optional cyclic (`X^N - 1`) NTT of `(c0, c1)` for `O(N log N)` `K_{k,p}^{(r)}` prover generation,
    /// plus shifted unsigned `[0, Q)` lifts `u0, u1` (`[u64; 3]` per coefficient).
    pub prover_aux: Option<PrecomputedProverAux>,
}

#[derive(Clone, Debug)]
pub struct PrecomputedProverAux {
    pub c0_cyc_ntt: Vec<u64>,
    pub c1_cyc_ntt: Vec<u64>,
    pub u0: Vec<[u64; 3]>,
    pub u1: Vec<[u64; 3]>,
}

/// Output of `HoistedEngine::hoisted_matvec_prove_raw` for `R` output groups.
#[derive(Clone, Debug)]
pub struct RawHoistedOutput {
    pub out_cts: Vec<Ct3>,
    /// Per `(r, k_comp)` (`3 * R` entries), length `N` signed quotients `y_{k,j}^{(r)}`.
    pub ys: Vec<Vec<SignedU320>>,
    /// Per `(r, k_comp)` (`3 * R` entries), length `N` remainders `s_{k,j}^{(r)} in [0, Q)`.
    pub ss: Vec<Vec<[u64; 3]>>,
    /// Per `(r, k_comp)` (`3 * R` entries), per prime `l in 0..8`, length `N - 1` quotient `K_{k,p_l}^{(r)}`.
    pub k_res: Vec<[[Vec<u64>; 8]; 3]>,
}

/// RNS-Gadget Relinearization Key (`P_ks = bp[0]`, 4 gadget limbs of 60 bits extracted from `w = 20` digits).
/// Lives on the 4-prime basis `(q0, q1, q2, b0)` in negacyclic NTT form.
#[derive(Clone)]
pub struct RelinearizationKey {
    pub rns_qp: Arc<Rns>,
    /// 4 gadget levels `m in 0..4` (`2^{60 m}`), each storing `(rlk0_ntt, rlk1_ntt)` of length `4 * N`.
    pub rlk0_ntt: [Vec<u64>; 4],
    pub rlk1_ntt: [Vec<u64>; 4],
}

impl RelinearizationKey {
    /// Generate a relinearization key for secret key `s in {-1, 0, 1}^N` under deterministic `seed`.
    pub fn generate(params: &HoistedParams, s: &[i64], seed: u64) -> Self {
        let n = params.n;
        let qs4 = [params.qp[0], params.qp[1], params.qp[2], params.bp[0]];
        let rns4 = Arc::new(Rns::new(n, &qs4, params.t));
        let mut rng = PyRandom::from_u64(seed);

        let mut s_ntt = rns4.from_signed(s);
        rns4.fwd(&mut s_ntt);
        let mut s2 = rns4.mul_pw(&s_ntt, &s_ntt);
        rns4.inv(&mut s2); // s^2 mod (X^N + 1) in coefficient form across (q0, q1, q2, b0)

        let p_ks = params.bp[0];
        let mut rlk0_ntt = std::array::from_fn(|_| vec![0u64; 4 * n]);
        let mut rlk1_ntt = std::array::from_fn(|_| vec![0u64; 4 * n]);

        let mut q4_limbs = [0u64; 5];
        for (i, v) in rns4.q_big.to_u64_digits().into_iter().enumerate() {
            q4_limbs[i] = v;
        }

        for m in 0..4 {
            // Compute 2^(60*m) * P_ks mod q_k (note: for k == 3, P_ks mod b0 == 0!)
            let mut scale_k = [0u64; 4];
            for k in 0..3 {
                let qk = qs4[k];
                let pow60m = powmod(1u64 << 60, m as u64, qk);
                scale_k[k] = mulmod(p_ks % qk, pow60m, qk);
            }

            let mut a = vec![0u64; 4 * n];
            for j in 0..n {
                let v = rng.randbelow_arr::<5>(&q4_limbs);
                for k in 0..4 {
                    a[k * n + j] = rns4.md[k].limbs5(&v);
                }
            }
            let e: Vec<i64> = (0..n).map(|_| rng.randint_i64(-8, 8)).collect();

            let mut a_ntt = a;
            rns4.fwd(&mut a_ntt);
            let mut as_coeff = rns4.mul_pw(&a_ntt, &s_ntt);
            rns4.inv(&mut as_coeff);

            let mut b = vec![0u64; 4 * n];
            for k in 0..4 {
                let qk = qs4[k];
                for j in 0..n {
                    // rlk0 + rlk1 * s = P_ks * 2^(60m) * s^2 + e (mod Q * P_ks)
                    let term = mulmod(scale_k[k], s2[k * n + j], qk);
                    let rhs = addmod(term, from_i64(e[j], qk), qk);
                    b[k * n + j] = submod(rhs, as_coeff[k * n + j], qk);
                }
            }
            rns4.fwd(&mut b);
            rlk0_ntt[m] = b;
            rlk1_ntt[m] = a_ntt;
        }

        RelinearizationKey {
            rns_qp: rns4,
            rlk0_ntt,
            rlk1_ntt,
        }
    }
}

/// Multithreaded (`rayon`) Extended-Basis RNS-NTT Hoisted `ct x ct` Engine.
pub struct HoistedEngine {
    pub params: Arc<HoistedParams>,
    pub rns_q: Arc<Rns>,
    pub neg_ntts: Vec<Ntt>,
    pub cyc_ntts: Vec<CyclicNtt>,
    pub inv2_mod_p: [u64; 8],
}

impl HoistedEngine {
    pub fn new(params: Arc<HoistedParams>) -> Self {
        let n = params.n;
        let rns_q = Arc::new(Rns::new(n, &params.qp, params.t));
        let neg_ntts: Vec<Ntt> = params.all_primes.iter().map(|&p| Ntt::new(p, n)).collect();
        let cyc_ntts: Vec<CyclicNtt> = params.all_primes.iter().map(|&p| CyclicNtt::new(p, n)).collect();
        let mut inv2_mod_p = [0u64; 8];
        for l in 0..8 {
            inv2_mod_p[l] = (params.all_primes[l] + 1) / 2;
        }
        HoistedEngine {
            params,
            rns_q,
            neg_ntts,
            cyc_ntts,
            inv2_mod_p,
        }
    }

    /// Decrypt a 3-component ciphertext `(c0, c1, c2)` using `OwnKey`'s secret `s` (`c0 + c1*s + c2*s^2`).
    pub fn decrypt_ct3(&self, key: &OwnKey, ct: &Ct3) -> Vec<u64> {
        let rns = &self.rns_q;
        let n = rns.n;
        let mut s_ntt = rns.from_signed(&key.s);
        rns.fwd(&mut s_ntt);
        let s2_ntt = rns.mul_pw(&s_ntt, &s_ntt);

        let mut c1_ntt = ct.c1.clone();
        let mut c2_ntt = ct.c2.clone();
        rns.fwd(&mut c1_ntt);
        rns.fwd(&mut c2_ntt);

        let mut acc = rns.mul_pw(&c1_ntt, &s_ntt);
        rns.mul_acc(&mut acc, &c2_ntt, &s2_ntt);
        rns.inv(&mut acc);
        rns.add_assign(&mut acc, &ct.c0);

        (0..n)
            .map(|j| {
                let res = [acc[j], acc[n + j], acc[2 * n + j]];
                rns.decrypt_round(&res)
            })
            .collect()
    }

    /// Exact `l_inf` post-rescale phase noise `max_j |centered(c0 + c1*s + c2*s^2 - round(Q*m/t), Q)|`
    /// as bit-length and `u128` (for small/medium noise; `BigUint` exact).
    pub fn phase_noise_inf(&self, key: &OwnKey, ct: &Ct3, expected_msg: &[u64]) -> num_bigint::BigUint {
        use num_bigint::{BigInt, BigUint};
        let rns = &self.rns_q;
        let n = rns.n;
        let mut s_ntt = rns.from_signed(&key.s);
        rns.fwd(&mut s_ntt);
        let s2_ntt = rns.mul_pw(&s_ntt, &s_ntt);
        let mut c1_ntt = ct.c1.clone();
        let mut c2_ntt = ct.c2.clone();
        rns.fwd(&mut c1_ntt);
        rns.fwd(&mut c2_ntt);
        let mut acc = rns.mul_pw(&c1_ntt, &s_ntt);
        rns.mul_acc(&mut acc, &c2_ntt, &s2_ntt);
        rns.inv(&mut acc);
        rns.add_assign(&mut acc, &ct.c0);

        let q_bi = BigInt::from(self.params.q_big.clone());
        let hq_bi = &q_bi >> 1usize;
        let mut enc_res = [0u64; 3];
        let mut max_err = BigUint::from(0u32);
        for j in 0..n {
            rns.encode_round(expected_msg[j] % self.params.t, &mut enc_res);
            let diff_res = [
                submod(acc[j], enc_res[0], self.params.qp[0]),
                submod(acc[n + j], enc_res[1], self.params.qp[1]),
                submod(acc[2 * n + j], enc_res[2], self.params.qp[2]),
            ];
            let z = rns.crt_big(&diff_res);
            let mut z_bi = BigInt::from(z);
            if z_bi > hq_bi {
                z_bi -= &q_bi;
            }
            let err = z_bi.magnitude().clone();
            if err > max_err {
                max_err = err;
            }
        }
        max_err
    }

    /// Lift a 2-component `Qp` ciphertext `ct` into the 8-prime `(Qp, Bp)` basis and precompute NTTs.
    pub fn precompute_ct(&self, ct: &Ct, with_prover_aux: bool) -> PrecomputedCt {
        let n = self.params.n;
        let mut c0_neg = vec![0u64; 8 * n];
        let mut c1_neg = vec![0u64; 8 * n];
        let mut u0 = if with_prover_aux { Vec::with_capacity(n) } else { Vec::new() };
        let mut u1 = if with_prover_aux { Vec::with_capacity(n) } else { Vec::new() };

        for j in 0..n {
            let (r8_0, u_val0) = lift_q_to_8limbs_and_u(
                &self.params,
                ct.c0[j],
                ct.c0[n + j],
                ct.c0[2 * n + j],
            );
            let (r8_1, u_val1) = lift_q_to_8limbs_and_u(
                &self.params,
                ct.c1[j],
                ct.c1[n + j],
                ct.c1[2 * n + j],
            );
            for l in 0..8 {
                c0_neg[l * n + j] = r8_0[l];
                c1_neg[l * n + j] = r8_1[l];
            }
            if with_prover_aux {
                u0.push(u_val0);
                u1.push(u_val1);
            }
        }

        let prover_aux = if with_prover_aux {
            let mut c0_cyc = c0_neg.clone();
            let mut c1_cyc = c1_neg.clone();
            for l in 0..8 {
                self.cyc_ntts[l].forward(&mut c0_cyc[l * n..(l + 1) * n]);
                self.cyc_ntts[l].forward(&mut c1_cyc[l * n..(l + 1) * n]);
            }
            Some(PrecomputedProverAux {
                c0_cyc_ntt: c0_cyc,
                c1_cyc_ntt: c1_cyc,
                u0,
                u1,
            })
        } else {
            None
        };

        for l in 0..8 {
            self.neg_ntts[l].forward(&mut c0_neg[l * n..(l + 1) * n]);
            self.neg_ntts[l].forward(&mut c1_neg[l * n..(l + 1) * n]);
        }

        PrecomputedCt {
            c0_neg_ntt: c0_neg,
            c1_neg_ntt: c1_neg,
            prover_aux,
        }
    }

    pub fn precompute_vec(&self, cts: &[Ct], with_prover_aux: bool) -> Vec<PrecomputedCt> {
        cts.par_iter().map(|ct| self.precompute_ct(ct, with_prover_aux)).collect()
    }

    pub fn precompute_grid(&self, grid: &[Vec<Ct>], with_prover_aux: bool) -> Vec<Vec<PrecomputedCt>> {
        grid.par_iter()
            .map(|row| row.par_iter().map(|ct| self.precompute_ct(ct, with_prover_aux)).collect())
            .collect()
    }

    /// Accumulate `(c0, c1, c2)` pointwise across `k_blk` blocks for a single prime limb `l` using
    /// 32-way lazy `u128` reduction (`64 * (2^61 - 1)^2 < u128::MAX`).
    #[inline]
    fn accumulate_row_limb(
        fp: &FastPrime61,
        n: usize,
        l: usize,
        a_row: &[PrecomputedCt],
        b_vec: &[PrecomputedCt],
        use_cyclic: bool,
    ) -> (Vec<u64>, Vec<u64>, Vec<u64>) {
        let k_blk = b_vec.len();
        debug_assert_eq!(a_row.len(), k_blk);
        let mut out0 = vec![0u64; n];
        let mut out1 = vec![0u64; n];
        let mut out2 = vec![0u64; n];
        let lo = l * n;
        let hi = (l + 1) * n;

        // Process in chunks of 32 blocks so `u128` never overflows even for `c1 = a0*b1 + a1*b0`!
        let mut acc0 = vec![0u128; n];
        let mut acc1 = vec![0u128; n];
        let mut acc2 = vec![0u128; n];

        for chunk_start in (0..k_blk).step_by(32) {
            let chunk_end = (chunk_start + 32).min(k_blk);
            acc0.fill(0);
            acc1.fill(0);
            acc2.fill(0);
            for c in chunk_start..chunk_end {
                let (a0, a1, b0, b1) = if !use_cyclic {
                    (
                        &a_row[c].c0_neg_ntt[lo..hi],
                        &a_row[c].c1_neg_ntt[lo..hi],
                        &b_vec[c].c0_neg_ntt[lo..hi],
                        &b_vec[c].c1_neg_ntt[lo..hi],
                    )
                } else {
                    let pa = a_row[c].prover_aux.as_ref().expect("prover_aux required");
                    let pb = b_vec[c].prover_aux.as_ref().expect("prover_aux required");
                    (
                        &pa.c0_cyc_ntt[lo..hi],
                        &pa.c1_cyc_ntt[lo..hi],
                        &pb.c0_cyc_ntt[lo..hi],
                        &pb.c1_cyc_ntt[lo..hi],
                    )
                };
                for j in 0..n {
                    let x0 = a0[j] as u128;
                    let x1 = a1[j] as u128;
                    let y0 = b0[j] as u128;
                    let y1 = b1[j] as u128;
                    acc0[j] += x0 * y0;
                    acc1[j] += x0 * y1 + x1 * y0;
                    acc2[j] += x1 * y1;
                }
            }
            for j in 0..n {
                out0[j] = fp.add(out0[j], fp.red128(acc0[j]));
                out1[j] = fp.add(out1[j], fp.red128(acc1[j]));
                out2[j] = fp.add(out2[j], fp.red128(acc2[j]));
            }
        }
        (out0, out1, out2)
    }

    /// Fast FHE-only hoisted `ct x ct` matvec from pre-NTT'd inputs (`R` row-groups x `K` col-blocks):
    /// Parallelizes across all `8 * R` `(r, l)` limb tasks, runs 1 inverse NTT per `(r, l)` and 1
    /// exact BEHZ rescale per output group `r`.
    pub fn hoisted_matvec_precomputed(
        &self,
        a_grid: &[Vec<PrecomputedCt>],
        b_vec: &[PrecomputedCt],
    ) -> Vec<Ct3> {
        let r_blk = a_grid.len();
        let n = self.params.n;

        // Parallelize across all (r, l) pairs (8 * R tasks -> full saturation even at R = 1 or 2!):
        let limb_results: Vec<[Vec<u64>; 3]> = (0..r_blk * 8)
            .into_par_iter()
            .map(|idx| {
                let r = idx / 8;
                let l = idx % 8;
                let (mut d0, mut d1, mut d2) =
                    Self::accumulate_row_limb(&self.params.fp[l], n, l, &a_grid[r], b_vec, false);
                self.neg_ntts[l].inverse(&mut d0);
                self.neg_ntts[l].inverse(&mut d1);
                self.neg_ntts[l].inverse(&mut d2);
                [d0, d1, d2]
            })
            .collect();

        (0..r_blk)
            .into_par_iter()
            .map(|r| {
                let mut out = [vec![0u64; 3 * n], vec![0u64; 3 * n], vec![0u64; 3 * n]];
                for k_comp in 0..3 {
                    for j in 0..n {
                        let mut res8 = [0u64; 8];
                        for l in 0..8 {
                            res8[l] = limb_results[r * 8 + l][k_comp][j];
                        }
                        let (_, _, y_qp) = behz_rescale_from_8limbs(&self.params, &res8);
                        out[k_comp][j] = y_qp[0];
                        out[k_comp][n + j] = y_qp[1];
                        out[k_comp][2 * n + j] = y_qp[2];
                    }
                }
                let [c0, c1, c2] = out;
                Ct3 { c0, c1, c2 }
            })
            .collect()
    }

    /// End-to-end FHE hoisted `ct x ct` matvec from raw `Qp` ciphertexts.
    pub fn hoisted_matvec(&self, a_grid: &[Vec<Ct>], b_vec: &[Ct]) -> Vec<Ct3> {
        let a_pre = self.precompute_grid(a_grid, false);
        let b_pre = self.precompute_vec(b_vec, false);
        self.hoisted_matvec_precomputed(&a_pre, &b_pre)
    }

    /// Baseline **eager** per-block `ct x ct` rescale + sum (`R * K` inverse NTTs and `R * K` BEHZ
    /// rescales), used to measure the wall-clock & rounding-noise advantage of `HoistedB61`.
    pub fn eager_matvec(&self, a_grid: &[Vec<Ct>], b_vec: &[Ct]) -> Vec<Ct3> {
        let a_pre = self.precompute_grid(a_grid, false);
        let b_pre = self.precompute_vec(b_vec, false);
        self.eager_matvec_precomputed(&a_pre, &b_pre)
    }

    pub fn eager_matvec_precomputed(
        &self,
        a_grid: &[Vec<PrecomputedCt>],
        b_vec: &[PrecomputedCt],
    ) -> Vec<Ct3> {
        let r_blk = a_grid.len();
        let k_blk = b_vec.len();
        let n = self.params.n;

        // Every (r, c) block rescales independently before summing mod Q!
        let block_cts: Vec<Ct3> = (0..r_blk * k_blk)
            .into_par_iter()
            .map(|blk_idx| {
                let r = blk_idx / k_blk;
                let c = blk_idx % k_blk;
                let mut d_limbs = [[vec![0u64; n], vec![0u64; n], vec![0u64; n]], [vec![], vec![], vec![]]];
                let _ = &mut d_limbs;
                let mut per_l: Vec<[Vec<u64>; 3]> = Vec::with_capacity(8);
                for l in 0..8 {
                    let fp = &self.params.fp[l];
                    let lo = l * n;
                    let hi = (l + 1) * n;
                    let a0 = &a_grid[r][c].c0_neg_ntt[lo..hi];
                    let a1 = &a_grid[r][c].c1_neg_ntt[lo..hi];
                    let b0 = &b_vec[c].c0_neg_ntt[lo..hi];
                    let b1 = &b_vec[c].c1_neg_ntt[lo..hi];
                    let mut z0 = vec![0u64; n];
                    let mut z1 = vec![0u64; n];
                    let mut z2 = vec![0u64; n];
                    for j in 0..n {
                        let (x0, x1, y0, y1) = (a0[j] as u128, a1[j] as u128, b0[j] as u128, b1[j] as u128);
                        z0[j] = fp.red128(x0 * y0);
                        z1[j] = fp.red128(x0 * y1 + x1 * y0);
                        z2[j] = fp.red128(x1 * y1);
                    }
                    self.neg_ntts[l].inverse(&mut z0);
                    self.neg_ntts[l].inverse(&mut z1);
                    self.neg_ntts[l].inverse(&mut z2);
                    per_l.push([z0, z1, z2]);
                }
                let mut out = [vec![0u64; 3 * n], vec![0u64; 3 * n], vec![0u64; 3 * n]];
                for k_comp in 0..3 {
                    for j in 0..n {
                        let mut res8 = [0u64; 8];
                        for l in 0..8 {
                            res8[l] = per_l[l][k_comp][j];
                        }
                        let (_, _, y_qp) = behz_rescale_from_8limbs(&self.params, &res8);
                        out[k_comp][j] = y_qp[0];
                        out[k_comp][n + j] = y_qp[1];
                        out[k_comp][2 * n + j] = y_qp[2];
                    }
                }
                let [c0, c1, c2] = out;
                Ct3 { c0, c1, c2 }
            })
            .collect();

        (0..r_blk)
            .into_par_iter()
            .map(|r| {
                let mut sum0 = vec![0u64; 3 * n];
                let mut sum1 = vec![0u64; 3 * n];
                let mut sum2 = vec![0u64; 3 * n];
                for c in 0..k_blk {
                    let bct = &block_cts[r * k_blk + c];
                    self.rns_q.add_assign(&mut sum0, &bct.c0);
                    self.rns_q.add_assign(&mut sum1, &bct.c1);
                    self.rns_q.add_assign(&mut sum2, &bct.c2);
                }
                Ct3 {
                    c0: sum0,
                    c1: sum1,
                    c2: sum2,
                }
            })
            .collect()
    }

    /// Prover hoisted `ct x ct` matvec: computes `out_cts`, exact signed quotients `ys`, exact
    /// remainders `ss in [0, Q)`, AND exact degree-`< N - 1` ring quotients `K_{k,p_l}^{(r)}(X)`
    /// across all 8 primes in `O(N log N)` via `(C(X) - D(X)) / 2 mod p_l`.
    pub fn hoisted_matvec_prove_raw(
        &self,
        a_grid: &[Vec<PrecomputedCt>],
        b_vec: &[PrecomputedCt],
    ) -> RawHoistedOutput {
        let r_blk = a_grid.len();
        let n = self.params.n;

        // Parallelize over all 8 * R (r, l) tasks, computing both negacyclic D and cyclic C!
        let limb_results: Vec<([Vec<u64>; 3], [Vec<u64>; 3])> = (0..r_blk * 8)
            .into_par_iter()
            .map(|idx| {
                let r = idx / 8;
                let l = idx % 8;
                let fp = &self.params.fp[l];
                let inv2 = self.inv2_mod_p[l];
                let (mut d0, mut d1, mut d2) =
                    Self::accumulate_row_limb(fp, n, l, &a_grid[r], b_vec, false);
                let (mut c0, mut c1, mut c2) =
                    Self::accumulate_row_limb(fp, n, l, &a_grid[r], b_vec, true);
                self.neg_ntts[l].inverse(&mut d0);
                self.neg_ntts[l].inverse(&mut d1);
                self.neg_ntts[l].inverse(&mut d2);
                self.cyc_ntts[l].inverse(&mut c0);
                self.cyc_ntts[l].inverse(&mut c1);
                self.cyc_ntts[l].inverse(&mut c2);

                let mut k0 = vec![0u64; n - 1];
                let mut k1 = vec![0u64; n - 1];
                let mut k2 = vec![0u64; n - 1];
                for j in 0..(n - 1) {
                    k0[j] = fp.mul(fp.sub(c0[j], d0[j]), inv2);
                    k1[j] = fp.mul(fp.sub(c1[j], d1[j]), inv2);
                    k2[j] = fp.mul(fp.sub(c2[j], d2[j]), inv2);
                }
                debug_assert_eq!(c0[n - 1], d0[n - 1], "cyclic vs negacyclic top degree check (k=0)");
                debug_assert_eq!(c1[n - 1], d1[n - 1], "cyclic vs negacyclic top degree check (k=1)");
                debug_assert_eq!(c2[n - 1], d2[n - 1], "cyclic vs negacyclic top degree check (k=2)");
                ([d0, d1, d2], [k0, k1, k2])
            })
            .collect();

        // Parallelize exact BEHZ rescale across all 3 * R (r, k_comp) polynomials:
        let rescaled: Vec<(Vec<u64>, Vec<SignedU320>, Vec<[u64; 3]>)> = (0..3 * r_blk)
            .into_par_iter()
            .map(|rk| {
                let r = rk / 3;
                let k_comp = rk % 3;
                let mut c_out = vec![0u64; 3 * n];
                let mut ys = Vec::with_capacity(n);
                let mut ss = Vec::with_capacity(n);
                for j in 0..n {
                    let mut res8 = [0u64; 8];
                    for l in 0..8 {
                        res8[l] = limb_results[r * 8 + l].0[k_comp][j];
                    }
                    let (y_sig, s_lim, y_qp) = behz_rescale_from_8limbs(&self.params, &res8);
                    c_out[j] = y_qp[0];
                    c_out[n + j] = y_qp[1];
                    c_out[2 * n + j] = y_qp[2];
                    ys.push(y_sig);
                    ss.push(s_lim);
                }
                (c_out, ys, ss)
            })
            .collect();

        let mut out_cts = Vec::with_capacity(r_blk);
        let mut all_ys = Vec::with_capacity(3 * r_blk);
        let mut all_ss = Vec::with_capacity(3 * r_blk);
        let mut k_res = Vec::with_capacity(r_blk);

        for r in 0..r_blk {
            let c0 = rescaled[3 * r].0.clone();
            let c1 = rescaled[3 * r + 1].0.clone();
            let c2 = rescaled[3 * r + 2].0.clone();
            out_cts.push(Ct3 { c0, c1, c2 });
            for k_comp in 0..3 {
                all_ys.push(rescaled[3 * r + k_comp].1.clone());
                all_ss.push(rescaled[3 * r + k_comp].2.clone());
            }
            let kr: [[Vec<u64>; 8]; 3] = std::array::from_fn(|k_comp| {
                std::array::from_fn(|l| limb_results[r * 8 + l].1[k_comp].clone())
            });
            k_res.push(kr);
        }

        RawHoistedOutput {
            out_cts,
            ys: all_ys,
            ss: all_ss,
            k_res,
        }
    }

    /// RNS-Gadget relinearization of a 3-component ciphertext `(c0, c1, c2)` -> 2-component `(c0', c1')`:
    /// Extracts 10 `w = 20`-bit digits of `c2 in [0, Q)`, groups them into four 60-bit gadget limbs
    /// `g_0..g_3`, multiplies by `rlk` in `(q0, q1, q2, b0)` NTT domain, and modulus-switches `P_ks = b0`!
    pub fn relinearize_ct3(&self, ct3: &Ct3, rlk: &RelinearizationKey) -> Ct {
        let n = self.params.n;
        let rns4 = &rlk.rns_qp;
        let mask60 = (1u64 << 60) - 1;

        // Extract 10 w=20 digits of c2_j in [0, Q) and group triples into four 60-bit limbs g_0..g_3:
        let mut g_ntt = [
            vec![0u64; 4 * n],
            vec![0u64; 4 * n],
            vec![0u64; 4 * n],
            vec![0u64; 4 * n],
        ];
        for j in 0..n {
            let z = crt3_unsigned(&self.params, ct3.c2[j], ct3.c2[n + j], ct3.c2[2 * n + j]);
            // z = z[0] + 2^64 z[1] + 2^128 z[2] < Q < 2^183:
            // g0 = bits 0..60, g1 = bits 60..120, g2 = bits 120..180, g3 = bits 180..183 (from d_9 < 8)
            let g0 = z[0] & mask60;
            let g1 = ((z[0] >> 60) | (z[1] << 4)) & mask60;
            let g2 = ((z[1] >> 56) | (z[2] << 8)) & mask60;
            let g3 = z[2] >> 52;
            debug_assert!(g3 < 8);
            let gs = [g0, g1, g2, g3];
            for m in 0..4 {
                for k in 0..4 {
                    let qk = rns4.qs[k];
                    g_ntt[m][k * n + j] = if gs[m] >= qk { gs[m] % qk } else { gs[m] };
                }
            }
        }
        for m in 0..4 {
            rns4.fwd(&mut g_ntt[m]);
        }

        let mut ks0 = vec![0u64; 4 * n];
        let mut ks1 = vec![0u64; 4 * n];
        for m in 0..4 {
            rns4.mul_acc(&mut ks0, &g_ntt[m], &rlk.rlk0_ntt[m]);
            rns4.mul_acc(&mut ks1, &g_ntt[m], &rlk.rlk1_ntt[m]);
        }
        rns4.inv(&mut ks0);
        rns4.inv(&mut ks1);

        // Exact RNS modulus-switch dropping P_ks = bp[0] (index 3) down to Qp (indices 0..3):
        let b0 = self.params.bp[0];
        let half_b0 = b0 / 2;
        let drop_b0 = |ks: &[u64], base_c: &[u64]| -> Vec<u64> {
            let mut out = base_c.to_vec();
            for k in 0..3 {
                let qk = self.params.qp[k];
                let inv = self.params.inv_b0_mod_q[k];
                for j in 0..n {
                    let r_top = ks[3 * n + j];
                    let rq = if r_top > half_b0 {
                        submod(0, (b0 - r_top) % qk, qk)
                    } else {
                        r_top % qk
                    };
                    let sw = mulmod(submod(ks[k * n + j], rq, qk), inv, qk);
                    out[k * n + j] = addmod(out[k * n + j], sw, qk);
                }
            }
            out
        };

        Ct {
            c0: drop_b0(&ks0, &ct3.c0),
            c1: drop_b0(&ks1, &ct3.c1),
        }
    }
}

/// `Hoist(b, tau)` Temporal Outer-Product Accumulator:
/// Accumulates `tau` rank-1 encrypted outer-product blocks `u_m^{(r)} (x) v_m^{(c)}` in the 8-prime
/// `(Qp, Bp)` NTT domain BEFORE rescaling, then flushes once per `tau` steps with 1 BEHZ rescale +
/// 1 RNS-gadget relinearization per `(r, c)` block!
pub struct TemporalOuterAccumulator {
    pub r_blk: usize,
    pub k_blk: usize,
    pub n: usize,
    pub steps_accumulated: usize,
    /// Per block `blk = r * k_blk + c`, 3 components `[acc0, acc1, acc2]`, each `8 * N` words in NTT domain.
    pub acc_ntt: Vec<[Vec<u64>; 3]>,
}

impl TemporalOuterAccumulator {
    pub fn new(params: &HoistedParams, r_blk: usize, k_blk: usize) -> Self {
        let n = params.n;
        let acc_ntt = (0..r_blk * k_blk)
            .map(|_| [vec![0u64; 8 * n], vec![0u64; 8 * n], vec![0u64; 8 * n]])
            .collect();
        TemporalOuterAccumulator {
            r_blk,
            k_blk,
            n,
            steps_accumulated: 0,
            acc_ntt,
        }
    }

    /// Accumulate one step's outer-product factors `u_row` (`r_blk` cts) and `v_col` (`k_blk` cts)
    /// into the unrescaled 8-prime NTT tensor accumulator (`0` inverse NTTs, `0` BEHZ rescales!).
    pub fn accumulate_step(&mut self, engine: &HoistedEngine, u_row: &[Ct], v_col: &[Ct]) {
        assert_eq!(u_row.len(), self.r_blk);
        assert_eq!(v_col.len(), self.k_blk);
        let u_pre = engine.precompute_vec(u_row, false);
        let v_pre = engine.precompute_vec(v_col, false);
        let n = self.n;
        let k_blk = self.k_blk;
        let fp = &engine.params.fp;

        self.acc_ntt
            .par_iter_mut()
            .enumerate()
            .for_each(|(blk, [acc0, acc1, acc2])| {
                let r = blk / k_blk;
                let c = blk % k_blk;
                let u = &u_pre[r];
                let v = &v_pre[c];
                for l in 0..8 {
                    let fpl = &fp[l];
                    let lo = l * n;
                    let hi = (l + 1) * n;
                    for j in lo..hi {
                        let (x0, x1) = (u.c0_neg_ntt[j] as u128, u.c1_neg_ntt[j] as u128);
                        let (y0, y1) = (v.c0_neg_ntt[j] as u128, v.c1_neg_ntt[j] as u128);
                        acc0[j] = fpl.add(acc0[j], fpl.red128(x0 * y0));
                        acc1[j] = fpl.add(acc1[j], fpl.red128(x0 * y1 + x1 * y0));
                        acc2[j] = fpl.add(acc2[j], fpl.red128(x1 * y1));
                    }
                }
            });
        self.steps_accumulated += 1;
    }

    /// Flush the accumulated `tau`-step outer product: 1 inverse NTT + 1 exact BEHZ rescale +
    /// 1 RNS-gadget relinearization per `(r, c)` block, subtracted from `w_base` (`W_new = W_0 - dW`).
    pub fn flush_and_update(
        &mut self,
        engine: &HoistedEngine,
        w_base: &[Vec<Ct>],
        rlk: &RelinearizationKey,
    ) -> Vec<Vec<Ct>> {
        let n = self.n;
        let k_blk = self.k_blk;
        let r_blk = self.r_blk;

        let updated_flat: Vec<Ct> = self
            .acc_ntt
            .par_iter_mut()
            .enumerate()
            .map(|(blk, [acc0, acc1, acc2])| {
                let r = blk / k_blk;
                let c = blk % k_blk;
                for l in 0..8 {
                    let lo = l * n;
                    let hi = (l + 1) * n;
                    engine.neg_ntts[l].inverse(&mut acc0[lo..hi]);
                    engine.neg_ntts[l].inverse(&mut acc1[lo..hi]);
                    engine.neg_ntts[l].inverse(&mut acc2[lo..hi]);
                }
                let mut out = [vec![0u64; 3 * n], vec![0u64; 3 * n], vec![0u64; 3 * n]];
                for (k_comp, comp_buf) in [acc0.as_slice(), acc1.as_slice(), acc2.as_slice()]
                    .into_iter()
                    .enumerate()
                {
                    for j in 0..n {
                        let mut res8 = [0u64; 8];
                        for l in 0..8 {
                            res8[l] = comp_buf[l * n + j];
                        }
                        let (_, _, y_qp) = behz_rescale_from_8limbs(&engine.params, &res8);
                        out[k_comp][j] = y_qp[0];
                        out[k_comp][n + j] = y_qp[1];
                        out[k_comp][2 * n + j] = y_qp[2];
                    }
                }
                let [c0, c1, c2] = out;
                let dw_relin = engine.relinearize_ct3(&Ct3 { c0, c1, c2 }, rlk);
                acc0.fill(0);
                acc1.fill(0);
                acc2.fill(0);

                // Subtract relinearized 2-component dW from w_base[r][c] mod Qp:
                let base_ct = &w_base[r][c];
                let mut new_c0 = vec![0u64; 3 * n];
                let mut new_c1 = vec![0u64; 3 * n];
                for k in 0..3 {
                    let qk = engine.params.qp[k];
                    for j in 0..n {
                        let idx = k * n + j;
                        new_c0[idx] = submod(base_ct.c0[idx], dw_relin.c0[idx], qk);
                        new_c1[idx] = submod(base_ct.c1[idx], dw_relin.c1[idx], qk);
                    }
                }
                Ct {
                    c0: new_c0,
                    c1: new_c1,
                }
            })
            .collect();

        self.steps_accumulated = 0;
        (0..r_blk)
            .map(|r| updated_flat[r * k_blk..(r + 1) * k_blk].to_vec())
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cyclic_and_negacyclic_recover_exact_ring_quotient() {
        let params = HoistedParams::for_ring(64);
        let eng = HoistedEngine::new(Arc::new(params));
        let q = eng.params.all_primes[0];
        let fp = &eng.params.fp[0];
        let n = 64;

        let a: Vec<u64> = (0..n).map(|i| ((i * 17 + 3) as u64) % q).collect();
        let b: Vec<u64> = (0..n).map(|i| (q - ((i * 5 + 1) as u64) % q) % q).collect();

        // Schoolbook polynomial product in F_q[X]:
        let mut prod = vec![0u64; 2 * n - 1];
        for i in 0..n {
            for j in 0..n {
                prod[i + j] = fp.add(prod[i + j], fp.mul(a[i], b[j]));
            }
        }
        let want_k: Vec<u64> = prod[n..2 * n - 1].to_vec();

        let mut an = a.clone();
        let mut bn = b.clone();
        eng.neg_ntts[0].forward(&mut an);
        eng.neg_ntts[0].forward(&mut bn);
        let mut d: Vec<u64> = an.iter().zip(&bn).map(|(&x, &y)| fp.mul(x, y)).collect();
        eng.neg_ntts[0].inverse(&mut d);

        let mut ac = a;
        let mut bc = b;
        eng.cyc_ntts[0].forward(&mut ac);
        eng.cyc_ntts[0].forward(&mut bc);
        let mut c: Vec<u64> = ac.iter().zip(&bc).map(|(&x, &y)| fp.mul(x, y)).collect();
        eng.cyc_ntts[0].inverse(&mut c);

        let inv2 = eng.inv2_mod_p[0];
        let got_k: Vec<u64> = (0..n - 1).map(|j| fp.mul(fp.sub(c[j], d[j]), inv2)).collect();
        assert_eq!(got_k, want_k);
        assert_eq!(c[n - 1], d[n - 1]);
    }
}
