//! Integration test suite for `darkvfhe`:
//! 1. Bit-exact decryption & post-rescale phase noise check (`eager` vs `hoisted` rounding noise drop
//!    across `K = 64` blocks at `N = 128` and `N = 8192`, plus RNS-gadget relinearization and `tau = 8`
//!    temporal outer-product accumulation).
//! 2. Bit-for-bit Python cross-check against `research/vfhe_sota_2026_11_21/experiments/vfhe_hoisted_b61_and_pir.py`
//!    (`Direct-20`, `Exact-Garner-15`, `out_cts`, `y_lifts`, `s_lifts`, `K_res`, and `N = 8192` primes).
//! 3. Constructive adversarial falsifier suite:
//!    - `Hole B` mod-`Q` alias (`Q = 31, t = 4` AND full 8-limb certificate mod-`Q` shift);
//!    - `Attack F-FS` (`Astra E5` statement-only Fiat-Shamir forgery accepted by legacy FS, refused by `HoistedB61`);
//!    - `Attack F-Boundary` (`Astra E4 / E7` `u + Q in [Q, 2^183)` accepted by power-of-two `< 2^183`,
//!      refused by `Exact-Garner-15` AND `D1b` LogUp-GKR);
//!    - `wrong_quotient`, `mixed_limbs`, `stale_parent`, `wrong_delta` (`4/4` refused);
//!    - Out-of-range digit (`2^20` and narrowed-top overflow `8`) rejected purely by `D1b` LogUp-GKR
//!      (`BatchedC3` and `MonolithicC4`).

use darkstep::arith::{addmod, from_i64, submod};
use darkstep::bfv::{Ct, OwnKey};
use darkvfhe::bigint::{biguint_to_limbs3, SignedU320};
use darkvfhe::cert::{
    collect_online_lookup_entries, ct2_handle, ct3_handle, derive_fs_point, prove_hoisted_matvec,
    verify_hoisted_matvec, ProveOptions, VerifyOptions,
};
use darkvfhe::digits::{DigitCols, DirectDigitSpec, ExactGarnerSpec, LiftMode};
use darkvfhe::logup_gkr::{prove_logup_gkr_with_mults, verify_logup_gkr, LogUpConfig, TABLE_SIZE};
use darkvfhe::rns_hoist::{HoistedEngine, RelinearizationKey, TemporalOuterAccumulator};
use darkvfhe::HoistedParams;
use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use pycompat::PyRandom;
use serde::Deserialize;
use sha2::{Digest, Sha256};
use std::path::PathBuf;
use std::process::Command;
use std::sync::Arc;

fn negacyclic_mul_mod_t(a: &[u64], b: &[u64], t: u64) -> Vec<u64> {
    let n = a.len();
    let mut out = vec![0u64; n];
    for i in 0..n {
        if a[i] == 0 {
            continue;
        }
        for j in 0..n {
            if b[j] == 0 {
                continue;
            }
            let prod = ((a[i] as u128 * b[j] as u128) % t as u128) as u64;
            if i + j < n {
                out[i + j] = addmod(out[i + j], prod, t);
            } else {
                out[i + j - n] = submod(out[i + j - n], prod, t);
            }
        }
    }
    out
}

/// Zero-error ciphertext `(-a*s mod Q, a)` encrypting `0` (isolates pure BEHZ rounding noise!).
fn encrypt_zero_noiseless(eng: &HoistedEngine, key: &OwnKey, rng: &mut PyRandom) -> Ct {
    let rns = &eng.rns_q;
    let n = rns.n;
    let mut ql = [0u64; 5];
    for (k, x) in rns.q_big.to_u64_digits().into_iter().enumerate() {
        ql[k] = x;
    }
    let mut a = rns.zero();
    for i in 0..n {
        let v = rng.randbelow_arr::<5>(&ql);
        for k in 0..3 {
            a[k * n + i] = rns.md[k].limbs5(&v);
        }
    }
    let mut s_ntt = rns.from_signed(&key.s);
    rns.fwd(&mut s_ntt);
    let mut a_ntt = a.clone();
    rns.fwd(&mut a_ntt);
    let mut as_coeff = rns.mul_pw(&a_ntt, &s_ntt);
    rns.inv(&mut as_coeff);
    let mut c0 = rns.zero();
    for k in 0..3 {
        let qk = rns.qs[k];
        for i in 0..n {
            c0[k * n + i] = submod(0, as_coeff[k * n + i], qk);
        }
    }
    Ct { c0, c1: a }
}

#[test]
fn test_bit_exact_decryption_rounding_noise_relin_and_tau_outer() {
    // 1. K = 64 hoisted vs eager rounding noise drop & exact decryption at N = 128 AND N = 8192:
    for &n_ring in &[128usize, 8192usize] {
        let params = Arc::new(HoistedParams::for_ring(n_ring));
        let eng = HoistedEngine::new(params.clone());
        let mut key = OwnKey::new(eng.rns_q.clone(), 42);
        let t = params.t;
        let k_blk = 64usize;

        let mut rng = PyRandom::from_u64(101);
        let mut a_row = Vec::with_capacity(k_blk);
        let mut b_vec = Vec::with_capacity(k_blk);
        let mut want_sum = vec![0u64; n_ring];

        // Sparse/structured messages at N=8192 so schoolbook reference check is instant, full dense at N=128:
        let active_slots = n_ring.min(128);
        for _ in 0..k_blk {
            let mut ma = vec![0u64; n_ring];
            let mut mb = vec![0u64; n_ring];
            for j in 0..active_slots {
                ma[j] = from_i64(rng.randint_i64(-7, 7), t);
                mb[j] = from_i64(rng.randint_i64(-7, 7), t);
            }
            let prod = negacyclic_mul_mod_t(&ma, &mb, t);
            for j in 0..n_ring {
                want_sum[j] = addmod(want_sum[j], prod[j], t);
            }
            a_row.push(key.encrypt_exact(&ma));
            b_vec.push(key.encrypt_exact(&mb));
        }

        let hoisted_out = eng.hoisted_matvec(&[a_row.clone()], &b_vec);
        let eager_out = eng.eager_matvec(&[a_row.clone()], &b_vec);
        assert_eq!(eng.decrypt_ct3(&key, &hoisted_out[0]), want_sum, "hoisted decrypt mismatch N={n_ring}");
        assert_eq!(eng.decrypt_ct3(&key, &eager_out[0]), want_sum, "eager decrypt mismatch N={n_ring}");

        // RNS-gadget relinearization (`P_ks = b0`, four 60b limbs from `w = 20` digits) check:
        let rlk = RelinearizationKey::generate(&params, &key.s, 777);
        let relin_ct2 = eng.relinearize_ct3(&hoisted_out[0], &rlk);
        assert_eq!(
            key.decrypt(&relin_ct2, None),
            want_sum,
            "RNS-gadget relinearized ct2 decrypt mismatch at N={n_ring}"
        );

        // Zero-error ciphertexts: isolate pure BEHZ rounding error (`+1` vs `+K` roundings):
        let mut zrng = PyRandom::from_u64(99);
        let mut az = Vec::with_capacity(k_blk);
        let mut bz = Vec::with_capacity(k_blk);
        for _ in 0..k_blk {
            az.push(encrypt_zero_noiseless(&eng, &key, &mut zrng));
            bz.push(encrypt_zero_noiseless(&eng, &key, &mut zrng));
        }
        let hoist_z = eng.hoisted_matvec(&[az.clone()], &bz);
        let eager_z = eng.eager_matvec(&[az], &bz);
        let zeros = vec![0u64; n_ring];
        let noise_hoist = eng.phase_noise_inf(&key, &hoist_z[0], &zeros);
        let noise_eager = eng.phase_noise_inf(&key, &eager_z[0], &zeros);
        assert!(
            &noise_hoist * 3u32 < noise_eager,
            "expected substantial rounding noise drop at N={n_ring}: hoist={noise_hoist} vs eager={noise_eager}"
        );
    }

    // 2. Temporal `tau = 8` outer-product accumulation + single BEHZ rescale + gadget relin at N = 8192:
    let params8k = Arc::new(HoistedParams::n8192());
    let eng8k = HoistedEngine::new(params8k.clone());
    let mut key8k = OwnKey::new(eng8k.rns_q.clone(), 2026);
    let rlk8k = RelinearizationKey::generate(&params8k, &key8k.s, 2027);
    let t = params8k.t;
    let tau = 8usize;
    let (r_blk, k_blk) = (2usize, 2usize);

    let mut w_plain = vec![vec![vec![0u64; 8192]; k_blk]; r_blk];
    let mut w_cts = vec![Vec::new(); r_blk];
    for r in 0..r_blk {
        for c in 0..k_blk {
            for i in 0..16 {
                w_plain[r][c][i] = ((r * 7 + c * 3 + i) as u64) % t;
            }
            w_cts[r].push(key8k.encrypt_exact(&w_plain[r][c]));
        }
    }

    let mut accum = TemporalOuterAccumulator::new(&params8k, r_blk, k_blk);
    for step in 0..tau {
        let mut u_cts = Vec::with_capacity(r_blk);
        let mut v_cts = Vec::with_capacity(k_blk);
        let mut u_msgs = Vec::with_capacity(r_blk);
        let mut v_msgs = Vec::with_capacity(k_blk);
        for r in 0..r_blk {
            let mut m = vec![0u64; 8192];
            for i in 0..8 {
                m[8 * i] = ((step + r + i + 1) as u64) % 5;
            }
            u_cts.push(key8k.encrypt_exact(&m));
            u_msgs.push(m);
        }
        for c in 0..k_blk {
            let mut m = vec![0u64; 8192];
            for j in 0..8 {
                m[j] = ((step * 2 + c + j + 1) as u64) % 5;
            }
            v_cts.push(key8k.encrypt_exact(&m));
            v_msgs.push(m);
        }
        for r in 0..r_blk {
            for c in 0..k_blk {
                let prod = negacyclic_mul_mod_t(&u_msgs[r], &v_msgs[c], t);
                for idx in 0..8192 {
                    w_plain[r][c][idx] = submod(w_plain[r][c][idx], prod[idx], t);
                }
            }
        }
        accum.accumulate_step(&eng8k, &u_cts, &v_cts);
    }
    let updated_w = accum.flush_and_update(&eng8k, &w_cts, &rlk8k);
    for r in 0..r_blk {
        for c in 0..k_blk {
            assert_eq!(
                key8k.decrypt(&updated_w[r][c], None),
                w_plain[r][c],
                "Temporal tau=8 outer flush decrypt mismatch at block ({r}, {c})"
            );
        }
    }
}

#[derive(Deserialize)]
struct PyCrossCheckPayload {
    qp_8k: [u64; 3],
    bp_8k: [u64; 5],
    t_8k: u64,
    qp_64: [u64; 3],
    bp_64: [u64; 5],
    t_64: u64,
    a_rns: Vec<Vec<[Vec<u64>; 2]>>,
    b_rns: Vec<[Vec<u64>; 2]>,
    out_rns: Vec<[Vec<u64>; 3]>,
    direct_y_lifts: Vec<Vec<Vec<u32>>>,
    direct_s_lifts: Vec<Vec<Vec<u32>>>,
    garner_a_lifts: Vec<Vec<Vec<u32>>>,
    garner_s_lifts: Vec<Vec<Vec<u32>>>,
    k_res: Vec<Vec<Vec<Vec<u64>>>>,
}

#[test]
fn test_python_vs_rust_cross_check_bit_exact() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let repo_root = manifest_dir.parent().unwrap().parent().unwrap();
    let exp_dir = repo_root.join("research/vfhe_sota_2026_11_21/experiments");
    let dl_dir = repo_root.join("research/dark_learning_2026_11_06");

    let py_script = format!(
        r#"
import json, math, sys
sys.path.insert(0, {dl:?})
sys.path.insert(0, {exp:?})
import bfv_ref as bfv
import fhe_fork as FF
import vfhe_hoisted_b61_and_pir as H

_, qp_8k, bp_8k, t_8k = FF.setup(N=8192)
N = 64
qp_64 = bfv.ntt_primes(61, 3, 2 * N)
t_64 = bfv.ntt_primes(61, 4, 2 * N)[3]
bp_64 = bfv.ntt_primes(61, 5, 2 * N, exclude=set(qp_64 + [t_64]))
Q = math.prod(qp_64)
sch = bfv.BFV(N, Q, t_64, seed=55)
sch.keygen()

R_blk, K_blk = 2, 4
A_grid = [[sch.encrypt_exact([(r + c + j) % 11 for j in range(N)]) for c in range(K_blk)] for r in range(R_blk)]
B_vec = [sch.encrypt_exact([(2 * c + j * 3) % 11 for j in range(N)]) for c in range(K_blk)]

out_dir, w_dir = H.build_hoisted_matvec(sch, qp_64, bp_64, A_grid, B_vec, w_bits=20, mode="direct")
out_gar, w_gar = H.build_hoisted_matvec(sch, qp_64, bp_64, A_grid, B_vec, w_bits=20, mode="exact_garner")
assert out_dir == out_gar

def to_rns(poly):
    out = []
    for q in qp_64:
        out.extend([c % q for c in poly])
    return out

all_p = qp_64 + bp_64
payload = dict(
    qp_8k=qp_8k, bp_8k=bp_8k, t_8k=t_8k,
    qp_64=qp_64, bp_64=bp_64, t_64=t_64,
    a_rns=[[[to_rns(ct[0]), to_rns(ct[1])] for ct in row] for row in A_grid],
    b_rns=[[to_rns(ct[0]), to_rns(ct[1])] for ct in B_vec],
    out_rns=[[to_rns(ct[0]), to_rns(ct[1]), to_rns(ct[2])] for ct in out_dir],
    direct_y_lifts=w_dir["y_lifts"],
    direct_s_lifts=w_dir["s_lifts"],
    garner_a_lifts=w_gar["A_lifts"],
    garner_s_lifts=w_gar["s_lifts"],
    k_res=[[[w_dir["K_res"][r][k][p] for p in all_p] for k in range(3)] for r in range(R_blk)],
)
print(json.dumps(payload))
"#,
        dl = dl_dir.to_str().unwrap(),
        exp = exp_dir.to_str().unwrap()
    );

    let out = Command::new("python3")
        .arg("-c")
        .arg(&py_script)
        .output()
        .expect("python3 must be available");
    assert!(
        out.status.success(),
        "python3 cross-check script failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let py_data: PyCrossCheckPayload = serde_json::from_slice(&out.stdout).expect("parse JSON");

    // 1. Verify N = 8192 and N = 64 prime parameter agreement:
    let rust_8k = HoistedParams::n8192();
    assert_eq!(rust_8k.qp, py_data.qp_8k);
    assert_eq!(rust_8k.bp, py_data.bp_8k);
    assert_eq!(rust_8k.t, py_data.t_8k);

    let rust_64 = Arc::new(HoistedParams::for_ring(64));
    assert_eq!(rust_64.qp, py_data.qp_64);
    assert_eq!(rust_64.bp, py_data.bp_64);
    assert_eq!(rust_64.t, py_data.t_64);

    // 2. Reconstruct exact Ct inputs and run both Direct-20 and Exact-Garner-15 provers & verifiers:
    let a_grid: Vec<Vec<Ct>> = py_data
        .a_rns
        .iter()
        .map(|row| {
            row.iter()
                .map(|[c0, c1]| Ct {
                    c0: c0.clone(),
                    c1: c1.clone(),
                })
                .collect()
        })
        .collect();
    let b_vec: Vec<Ct> = py_data
        .b_rns
        .iter()
        .map(|[c0, c1]| Ct {
            c0: c0.clone(),
            c1: c1.clone(),
        })
        .collect();

    let eng = HoistedEngine::new(rust_64.clone());
    let (out_dir, w_dir) = prove_hoisted_matvec(
        &eng,
        &a_grid,
        &b_vec,
        None,
        ProveOptions {
            mode: LiftMode::Direct20,
            logup: Some(LogUpConfig::BatchedC3 { chunk_log2: 14 }),
            persistent_a: false,
        },
    )
    .expect("Direct20 prove");

    let (out_gar, w_gar) = prove_hoisted_matvec(
        &eng,
        &a_grid,
        &b_vec,
        None,
        ProveOptions {
            mode: LiftMode::ExactGarner15,
            logup: Some(LogUpConfig::MonolithicC4),
            persistent_a: false,
        },
    )
    .expect("ExactGarner15 prove");

    assert_eq!(out_dir, out_gar);
    for r in 0..2 {
        assert_eq!(out_dir[r].c0, py_data.out_rns[r][0], "c0 mismatch vs Python at row {r}");
        assert_eq!(out_dir[r].c1, py_data.out_rns[r][1], "c1 mismatch vs Python at row {r}");
        assert_eq!(out_dir[r].c2, py_data.out_rns[r][2], "c2 mismatch vs Python at row {r}");
        for k in 0..3 {
            for l in 0..8 {
                assert_eq!(
                    w_dir.k_res[r][k][l], py_data.k_res[r][k][l],
                    "K_res mismatch vs Python at r={r}, k={k}, l={l}"
                );
            }
        }
    }
    for idx in 0..w_dir.y_lifts.len() {
        assert_eq!(w_dir.y_lifts[idx].cols, py_data.direct_y_lifts[idx], "y_lifts mismatch");
        assert_eq!(w_dir.s_lifts[idx].cols, py_data.direct_s_lifts[idx], "direct s_lifts mismatch");
        assert_eq!(w_gar.s_lifts[idx].cols, py_data.garner_s_lifts[idx], "garner s_lifts mismatch");
    }
    for idx in 0..w_gar.a_lifts.len() {
        assert_eq!(w_gar.a_lifts[idx].cols, py_data.garner_a_lifts[idx], "garner a_lifts mismatch");
    }

    let ha: Vec<Vec<[u8; 32]>> = a_grid.iter().map(|r| r.iter().map(ct2_handle).collect()).collect();
    let hb: Vec<[u8; 32]> = b_vec.iter().map(ct2_handle).collect();
    let hout: Vec<[u8; 32]> = out_dir.iter().map(ct3_handle).collect();
    verify_hoisted_matvec(
        &rust_64,
        &ha,
        &hb,
        &hout,
        &a_grid,
        &b_vec,
        &out_dir,
        &w_dir,
        None,
        VerifyOptions::default(),
    )
    .expect("Direct20 verify");
    verify_hoisted_matvec(
        &rust_64,
        &ha,
        &hb,
        &hout,
        &a_grid,
        &b_vec,
        &out_gar,
        &w_gar,
        None,
        VerifyOptions::default(),
    )
    .expect("ExactGarner15 verify");
}

#[test]
fn test_all_adversarial_falsifiers() {
    let params = Arc::new(HoistedParams::for_ring(64));
    let eng = HoistedEngine::new(params.clone());
    let mut key = OwnKey::new(eng.rns_q.clone(), 31415);
    let n = params.n;

    let k_blk = 4usize;
    let a_row: Vec<Ct> = (0..k_blk)
        .map(|c| key.encrypt_exact(&(0..n).map(|j| ((c + j) as u64) % 7).collect::<Vec<_>>()))
        .collect();
    let b_vec: Vec<Ct> = (0..k_blk)
        .map(|c| key.encrypt_exact(&(0..n).map(|j| ((2 * c + j * 3) as u64) % 7).collect::<Vec<_>>()))
        .collect();
    let a_grid = vec![a_row];

    let (honest_out, honest_w) = prove_hoisted_matvec(
        &eng,
        &a_grid,
        &b_vec,
        None,
        ProveOptions {
            mode: LiftMode::ExactGarner15,
            logup: Some(LogUpConfig::BatchedC3 { chunk_log2: 14 }),
            persistent_a: false,
        },
    )
    .expect("honest prove");

    let ha: Vec<Vec<[u8; 32]>> = a_grid.iter().map(|r| r.iter().map(ct2_handle).collect()).collect();
    let hb: Vec<[u8; 32]> = b_vec.iter().map(ct2_handle).collect();
    let hout: Vec<[u8; 32]> = honest_out.iter().map(ct3_handle).collect();

    // Sanity check: honest proof passes!
    verify_hoisted_matvec(
        &params,
        &ha,
        &hb,
        &hout,
        &a_grid,
        &b_vec,
        &honest_out,
        &honest_w,
        None,
        VerifyOptions::default(),
    )
    .expect("honest verify must pass");

    // ----------------------------------------------------------------------------------
    // Falsifier 1: `Hole B` mod-Q alias (`Q = 31, t = 4` AND full `HoistedB61` certificate)
    // ----------------------------------------------------------------------------------
    let (q_toy, t_toy) = (31i64, 4i64);
    let (z_true, z_alias) = (32i64, 1i64);
    assert_eq!(z_true.rem_euclid(q_toy), z_alias.rem_euclid(q_toy));
    let (y_true, s_true) = ((t_toy * z_true + q_toy / 2) / q_toy, (t_toy * z_true + q_toy / 2) % q_toy);
    let (y_forged, s_alias) = ((t_toy * z_alias + q_toy / 2) / q_toy, (t_toy * z_alias + q_toy / 2) % q_toy);
    assert_eq!((y_true, y_forged, s_true, s_alias), (4, 0, 19, 19));
    // Naive mod-Q rescale check `t * z + floor(Q/2) == s (mod Q)` ACCEPTS `y_forged = 0`:
    assert_eq!((t_toy * z_true + q_toy / 2 - s_true).rem_euclid(q_toy), 0);
    // Integer certificate `t * z_true + floor(Q/2) == Q * y_forged + s` with `0 <= s < Q` REFUSES:
    let rem_if_forged = t_toy * z_true + q_toy / 2 - q_toy * y_forged;
    assert!(!(0 <= rem_if_forged && rem_if_forged < q_toy));

    // Also on full HoistedB61: shift y_0[0] by +Q? Wait: shifting y_0[0] by +1 while leaving s_0[0]
    // satisfies `t * D + floor(Q/2) == s (mod Q)` across ALL Qp limbs, yet changes `out` mod Q AND
    // breaks `Q * y` in `Bp`!
    let mut w_holeb = honest_w.clone();
    let dspec = DirectDigitSpec::new(&params, honest_w.max_y_bits);
    // Reconstruct honest y_0[0] + 1:
    let mut out_holeb = honest_out.clone();
    for k in 0..3 {
        out_holeb[0].c0[k * n] = addmod(out_holeb[0].c0[k * n], 1, params.qp[k]);
    }
    let hout_holeb = vec![ct3_handle(&out_holeb[0])];
    // Increment y_lifts[0] at coeff 0 by +1 (re-encoding cleanly so range checks pass!):
    let mut y0_u = BigUint::from(0u32);
    for (m, col) in honest_w.y_lifts[0].cols.iter().enumerate() {
        y0_u += BigUint::from(col[0]) << (20 * m);
    }
    y0_u += 1u32;
    for m in 0..dspec.ly {
        let limb_v = ((&y0_u >> (20 * m)) & BigUint::from((1u32 << 20) - 1)).to_u32_digits();
        w_holeb.y_lifts[0].cols[m][0] = limb_v.first().copied().unwrap_or(0);
    }
    // Recompute witness_root and LogUp proof so ONLY the fused BEHZ rescale check is tested:
    w_holeb.logup_proof = None;
    let (_, shared_a_tmp) = darkvfhe::cert::precompute_shared_grid(&eng, &a_grid, LiftMode::ExactGarner15);
    w_holeb.witness_root = darkvfhe::cert::compute_witness_root(
        w_holeb.mode,
        &shared_a_tmp.pair_hashes,
        &w_holeb.b_lifts,
        &w_holeb.y_lifts,
        &w_holeb.s_lifts,
        &w_holeb.k_res,
    );
    let err_holeb = verify_hoisted_matvec(
        &params,
        &ha,
        &hb,
        &hout_holeb,
        &a_grid,
        &b_vec,
        &out_holeb,
        &w_holeb,
        None,
        VerifyOptions::default(),
    )
    .expect_err("Hole B forged y+1 must be refused by extension primes Bp!");
    assert!(err_holeb.contains("fused hoisted rescale identity fails"), "{err_holeb}");

    // ----------------------------------------------------------------------------------
    // Falsifier 2: `Attack F-FS` (`Astra E5` statement-only Fiat-Shamir adaptive quotient forgery)
    // ----------------------------------------------------------------------------------
    // Shift z_forged = D_0[0] + floor(Q/t)^2 (altering decrypted plaintext at X^0!), recompute valid
    // (y_forged, s_forged), and adapt K_res[0][0][l][0] for the predictable legacy FS challenge!
    let q_bi = BigInt::from(params.q_big.clone());
    let t_bi = BigInt::from(params.t);
    let hq_bi = &q_bi >> 1usize;
    let delta_bi = &q_bi / &t_bi;

    // Reconstruct true D_0[0] from honest y_0[0] and s_0[0]:
    let mut y_orig_u = BigUint::from(0u32);
    for (m, col) in honest_w.y_lifts[0].cols.iter().enumerate() {
        y_orig_u += BigUint::from(col[0]) << (20 * m);
    }
    let y_orig = BigInt::from(y_orig_u) - (BigInt::from(1) << (honest_w.max_y_bits as usize));
    let g_c = &honest_w.s_lifts[0].cols;
    let r0_orig = (g_c[0][0] as u128)
        + ((g_c[1][0] as u128) << 20)
        + ((g_c[2][0] as u128) << 39)
        + ((g_c[3][0] as u128) << 57);
    let r1_orig = (g_c[5][0] as u128)
        + ((g_c[6][0] as u128) << 20)
        + ((g_c[7][0] as u128) << 39)
        + ((g_c[8][0] as u128) << 57);
    let r2_orig = (g_c[10][0] as u128)
        + ((g_c[11][0] as u128) << 20)
        + ((g_c[12][0] as u128) << 39)
        + ((g_c[13][0] as u128) << 57);
    let s_orig = BigInt::from(r0_orig)
        + BigInt::from(params.qp[0]) * BigInt::from(r1_orig)
        + BigInt::from(params.qp[0]) * BigInt::from(params.qp[1]) * BigInt::from(r2_orig);
    let d0_0 = (&q_bi * &y_orig + &s_orig - &hq_bi) / &t_bi;

    let z_forged = &d0_0 + (&delta_bi * &delta_bi);
    let (y_forged_bi, s_forged_bi) = (&t_bi * &z_forged + &hq_bi).div_mod_floor(&q_bi);

    let mut w_fs = honest_w.clone();
    w_fs.logup_proof = None; // Legacy statement-only FS test on polynomial rescale cert
    let (yf_sign, yf_digs) = y_forged_bi.to_u64_digits();
    let mut yf_mag = [0u64; 5];
    for (i, &v) in yf_digs.iter().enumerate() {
        yf_mag[i] = v;
    }
    let yf_col0 = dspec.encode_signed_y(&[SignedU320 {
        neg: yf_sign == num_bigint::Sign::Minus,
        mag: yf_mag,
    }]);
    for m in 0..dspec.ly {
        w_fs.y_lifts[0].cols[m][0] = yf_col0.cols[m][0];
    }
    let gspec = ExactGarnerSpec::new(&params);
    let sf_col0 = gspec.encode_u_exact(&[biguint_to_limbs3(&s_forged_bi.to_biguint().unwrap())]);
    for m in 0..15 {
        w_fs.s_lifts[0].cols[m][0] = sf_col0.cols[m][0];
    }

    let mut out_fs = honest_out.clone();
    for k in 0..3 {
        let pk = BigInt::from(params.qp[k]);
        out_fs[0].c0[k * n] = y_forged_bi.mod_floor(&pk).to_u64_digits().1.first().copied().unwrap_or(0);
    }
    assert_ne!(
        eng.decrypt_ct3(&key, &out_fs[0]),
        eng.decrypt_ct3(&key, &honest_out[0]),
        "Attack F-FS must alter decrypted plaintext!"
    );

    let hout_fs = vec![ct3_handle(&out_fs[0])];
    // Recompute statement digest identically to cert.rs:
    let mut sh = Sha256::new();
    sh.update(b"HOISTED_B61_STMT_V1|");
    sh.update(&(params.n as u64).to_le_bytes());
    sh.update(&params.t.to_le_bytes());
    for &q in &params.all_primes {
        sh.update(&q.to_le_bytes());
    }
    for row in &ha {
        for h_el in row {
            sh.update(h_el);
        }
    }
    for h_el in &hb {
        sh.update(h_el);
    }
    for h_el in &hout_fs {
        sh.update(h_el);
    }
    let stmt_h_fs: [u8; 32] = sh.finalize().into();

    for l in 0..8 {
        let fp = &params.fp[l];
        let p_bi = BigInt::from(fp.p);
        let r_pt = derive_fs_point(&stmt_h_fs, &[0u8; 32], fp.p, true);
        let dy_mod = (&y_forged_bi - &y_orig).mod_floor(&p_bi).to_u64_digits().1.first().copied().unwrap_or(0);
        let ds_mod = (&s_forged_bi - &s_orig).mod_floor(&p_bi).to_u64_digits().1.first().copied().unwrap_or(0);
        let rhs_diff = fp.add(fp.mul(params.q_mod_p[l], dy_mod), ds_mod);
        let denom = fp.mul(params.t_mod_p[l], fp.add(fp.pow(r_pt, n as u64), 1));
        let k_adj = fp.mul(fp.neg(rhs_diff), fp.inv(denom));
        w_fs.k_res[0][0][l][0] = fp.add(w_fs.k_res[0][0][l][0], k_adj);
    }
    w_fs.witness_root = darkvfhe::cert::compute_witness_root(
        w_fs.mode,
        &shared_a_tmp.pair_hashes,
        &w_fs.b_lifts,
        &w_fs.y_lifts,
        &w_fs.s_lifts,
        &w_fs.k_res,
    );

    // Legacy statement-only FS MUST ACCEPT the forged plaintext, while HoistedB61 MUST REFUSE!
    verify_hoisted_matvec(
        &params,
        &ha,
        &hb,
        &hout_fs,
        &a_grid,
        &b_vec,
        &out_fs,
        &w_fs,
        None,
        VerifyOptions {
            legacy_statement_only_fs: true,
            ..Default::default()
        },
    )
    .expect("legacy statement-only FS should accept adaptive quotient forgery");

    let err_fs = verify_hoisted_matvec(
        &params,
        &ha,
        &hb,
        &hout_fs,
        &a_grid,
        &b_vec,
        &out_fs,
        &w_fs,
        None,
        VerifyOptions::default(),
    )
    .expect_err("HoistedB61 witness-bound FS must refuse Attack F-FS!");
    assert!(err_fs.contains("fused hoisted rescale identity fails"), "{err_fs}");

    // ----------------------------------------------------------------------------------
    // Falsifier 3: `Attack F-Boundary` (`Astra E4 / E7`, `u + Q in [Q, 2^183)`)
    // ----------------------------------------------------------------------------------
    let u_alias_big = BigUint::from(42u32) + &params.q_big;
    assert!(u_alias_big.bits() <= 183, "u_alias fits inside 183-bit power-of-two range");
    let u_alias_limbs = biguint_to_limbs3(&u_alias_big);
    // Un-tightened Direct-20 `< 2^183` ACCEPTS `u_alias`:
    let alias_direct_cols = dspec.encode_u192(&[u_alias_limbs]);
    dspec
        .check_digits(&alias_direct_cols, dspec.lx, dspec.top_x_bits)
        .expect("power-of-two < 2^183 check accepts u + Q");

    // Attempt to forge `Exact-Garner-15` columns for `u_alias` (`r2 >= q2`):
    let q0_u = BigUint::from(params.qp[0]);
    let q1_u = BigUint::from(params.qp[1]);
    let r0_a = (&u_alias_big % &q0_u).to_u64_digits().first().copied().unwrap_or(0);
    let q_step1 = (&u_alias_big - r0_a) / &q0_u;
    let r1_a = (&q_step1 % &q1_u).to_u64_digits().first().copied().unwrap_or(0);
    let r2_a = ((&q_step1 - r1_a) / &q1_u).to_u64_digits().first().copied().unwrap_or(0);
    assert!(r2_a >= params.qp[2] && r2_a < (1u64 << 61));

    let mut forged_garner = Vec::with_capacity(15);
    for (ri, delta) in [(r0_a, gspec.deltas[0]), (r1_a, gspec.deltas[1]), (r2_a, gspec.deltas[2])] {
        let d0 = (ri & ((1 << 20) - 1)) as u32;
        let d1 = ((ri >> 20) & ((1 << 19) - 1)) as u32;
        let d2 = ((ri >> 39) & ((1 << 18) - 1)) as u32;
        let d3 = (ri >> 57) as u32;
        let v0 = ((d0 as u64 + delta) & ((1 << 20) - 1)) as u32;
        forged_garner.extend([vec![d0], vec![d1], vec![d2], vec![d3], vec![v0]]);
    }
    let forged_garner_dc = DigitCols { cols: forged_garner };
    let err_garner = gspec
        .check_u_exact(&forged_garner_dc)
        .expect_err("Exact-Garner-15 must refuse u + Q in [Q, 2^183)!");
    assert!(err_garner.contains("boundary overflow refused"), "{err_garner}");

    // Also verify `D1b` LogUp-GKR independently rejects `forged_garner_dc` (`T_2 = p - 1 not in [0, 2^20)`):
    let mut boundary_lkps = Vec::new();
    gspec.append_lookups_fp(&forged_garner_dc, params.all_primes[0], &mut boundary_lkps);
    let mut fake_mults = vec![0u64; TABLE_SIZE];
    fake_mults[0] = boundary_lkps.len() as u64;
    let bad_b_prf = prove_logup_gkr_with_mults(
        &params.fp[0],
        &boundary_lkps,
        &fake_mults,
        LogUpConfig::BatchedC3 { chunk_log2: 8 },
        &[0x11u8; 32],
    );
    assert!(
        verify_logup_gkr(&params.fp[0], &bad_b_prf, &[0x11u8; 32], Some((&boundary_lkps, &fake_mults)))
            .is_err(),
        "D1b LogUp-GKR must reject Exact-Garner-15 T_2 = p - 1 overflow!"
    );

    // ----------------------------------------------------------------------------------
    // Falsifier 4: `wrong_quotient`, `mixed_limbs`, `stale_parent`, `wrong_delta`
    // ----------------------------------------------------------------------------------
    // 4a. `wrong_quotient`:
    let mut bad_out = honest_out.clone();
    bad_out[0].c2[7] = addmod(bad_out[0].c2[7], 1, params.qp[0]);
    assert!(
        verify_hoisted_matvec(
            &params,
            &ha,
            &hb,
            &hout,
            &a_grid,
            &b_vec,
            &bad_out,
            &honest_w,
            None,
            VerifyOptions::default()
        )
        .is_err(),
        "wrong_quotient (unmatched hout) must fail"
    );
    let bad_hout = vec![ct3_handle(&bad_out[0])];
    assert!(
        verify_hoisted_matvec(
            &params,
            &ha,
            &hb,
            &bad_hout,
            &a_grid,
            &b_vec,
            &bad_out,
            &honest_w,
            None,
            VerifyOptions::default()
        )
        .is_err(),
        "wrong_quotient (re-hashed hout vs y_lift) must fail"
    );

    // 4b. `mixed_limbs`: splice limb 0 of `b_vec[0]` into `a_grid[0][0]`!
    let mut mixed_a = a_grid.clone();
    mixed_a[0][0].c0[..n].copy_from_slice(&b_vec[0].c0[..n]);
    let (_, w_mixed) = prove_hoisted_matvec(
        &eng,
        &mixed_a,
        &b_vec,
        None,
        ProveOptions::default(),
    )
    .unwrap();
    let err_mixed = verify_hoisted_matvec(
        &params,
        &ha,
        &hb,
        &hout,
        &mixed_a,
        &b_vec,
        &honest_out,
        &w_mixed,
        None,
        VerifyOptions::default(),
    )
    .expect_err("mixed_limbs must fail handle binding!");
    assert!(err_mixed.contains("handle mismatch"), "{err_mixed}");

    // 4c. `stale_parent`: substitute an older weight ciphertext for `a_grid[0][0]`!
    let mut stale_a = a_grid.clone();
    stale_a[0][0] = key.encrypt_exact(&vec![0u64; n]);
    let (stale_out, w_stale) = prove_hoisted_matvec(&eng, &stale_a, &b_vec, None, ProveOptions::default()).unwrap();
    let h_stale_out = vec![ct3_handle(&stale_out[0])];
    assert!(
        verify_hoisted_matvec(
            &params,
            &ha,
            &hb,
            &h_stale_out,
            &stale_a,
            &b_vec,
            &stale_out,
            &w_stale,
            None,
            VerifyOptions::default()
        )
        .is_err(),
        "stale_parent must fail handle binding!"
    );

    // 4d. `wrong_delta`: substitute a forged vector ciphertext for `b_vec[0]`!
    let mut bad_b = b_vec.clone();
    bad_b[0] = key.encrypt_exact(&vec![1u64; n]);
    let (bad_b_out, w_bad_b) = prove_hoisted_matvec(&eng, &a_grid, &bad_b, None, ProveOptions::default()).unwrap();
    let h_bad_b_out = vec![ct3_handle(&bad_b_out[0])];
    assert!(
        verify_hoisted_matvec(
            &params,
            &ha,
            &hb,
            &h_bad_b_out,
            &a_grid,
            &bad_b,
            &bad_b_out,
            &w_bad_b,
            None,
            VerifyOptions::default()
        )
        .is_err(),
        "wrong_delta must fail handle binding!"
    );

    // ----------------------------------------------------------------------------------
    // Falsifier 5: Out-of-range digit rejected purely by `D1b` LogUp-GKR (`direct_digit_check = false`)
    // ----------------------------------------------------------------------------------
    for cfg in [
        LogUpConfig::BatchedC3 { chunk_log2: 14 },
        LogUpConfig::MonolithicC4,
    ] {
        let mut w_oor = honest_w.clone();
        w_oor.b_lifts[0].cols[0][0] = 1 << 20; // OUT OF RANGE `[0, 2^20)`!
        w_oor.witness_root = darkvfhe::cert::compute_witness_root(
            w_oor.mode,
            &shared_a_tmp.pair_hashes,
            &w_oor.b_lifts,
            &w_oor.y_lifts,
            &w_oor.s_lifts,
            &w_oor.k_res,
        );
        let oor_entries = collect_online_lookup_entries(
            &params,
            w_oor.mode,
            w_oor.max_y_bits,
            &w_oor.a_lifts,
            &w_oor.b_lifts,
            &w_oor.y_lifts,
            &w_oor.s_lifts,
        );
        let (_, mut honest_mults) = honest_w.logup_proof.as_ref().unwrap().clone();
        // Cheating prover keeps total sum(mults) == M by placing the forged count at bucket 0:
        honest_mults[0] += 1;
        let forged_lu_prf = prove_logup_gkr_with_mults(
            &params.fp[0],
            &oor_entries,
            &honest_mults,
            cfg,
            &w_oor.witness_root,
        );
        w_oor.logup_proof = Some((forged_lu_prf, honest_mults));

        let err_oor = verify_hoisted_matvec(
            &params,
            &ha,
            &hb,
            &hout,
            &a_grid,
            &b_vec,
            &honest_out,
            &w_oor,
            None,
            VerifyOptions {
                direct_digit_check: false, // Isolate pure D1b LogUp-GKR rejection!
                full_logup_opening_check: true,
                legacy_statement_only_fs: false,
            },
        )
        .expect_err("D1b LogUp-GKR must reject out-of-range digit 2^20!");
        assert!(err_oor.contains("LogUp-GKR"), "{err_oor}");
    }
}
