//! Prover, verifier and the legacy-transcript simulator (zkpopk_ligero.prove / verify / simulate_legacy).

use crate::field::{batch_inv, peval, Fe, ONE};
use crate::ntt::{Code, Nega};
use crate::rng::{Hiding, OsHiding};
use crate::statement::{exact_nega, shape, weights, Group, Kind, Shape, Statement, EB};
use crate::transcript::{leaf, mverify, Merkle, Transcript};
use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive, Zero};
use rayon::prelude::*;

// ------------------------------------------------------------------------------------------- witness
/// Secret-key ciphertext witness: e in [-8, 8]^N, r at the slots in [-(t-1)/2, (t-1)/2].
#[derive(Clone, Debug)]
pub struct SkCt {
    pub e: Vec<i64>,
    pub r: Vec<i64>,
}

/// Public-key ciphertext witness: u ternary, e0, e1 in [-8, 8]^N, r at the slots.
#[derive(Clone, Debug)]
pub struct PkCt {
    pub u: Vec<i64>,
    pub e0: Vec<i64>,
    pub e1: Vec<i64>,
    pub r: Vec<i64>,
}

#[derive(Clone, Debug)]
pub enum Witness {
    /// kinds "sk" and "key" (a key witness has no cts)
    Sk { s: Vec<i64>, e_pk: Vec<i64>, cts: Vec<SkCt> },
    Pk { cts: Vec<PkCt> },
}

/// One group's integers: small (every honest witness) or arbitrary (forgers only).
#[derive(Clone, Debug)]
pub enum Vals {
    Small(Vec<i64>),
    Big(Vec<BigInt>),
}

impl Vals {
    pub fn len(&self) -> usize {
        match self {
            Vals::Small(v) => v.len(),
            Vals::Big(v) => v.len(),
        }
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    fn big(&self, i: usize) -> BigInt {
        match self {
            Vals::Small(v) => BigInt::from(v[i]),
            Vals::Big(v) => v[i].clone(),
        }
    }
    fn small(&self) -> Option<&Vec<i64>> {
        match self {
            Vals::Small(v) => Some(v),
            Vals::Big(_) => None,
        }
    }
}

/// FORGERS ONLY (the attack table): overrides that skip the prover's own checks, as `cheat=` in the harness.
#[derive(Clone, Debug, Default)]
pub struct Cheat {
    pub values1: Vec<(String, Vals)>,
    pub digits1: Option<Vec<Fe>>,
    pub digits2: Option<Vec<Fe>>,
    pub k: Vec<(String, BigInt)>,
    /// an out-of-range value is packed into its first digit as a field element
    pub raw: bool,
}

/// Prover options. `det_seed` is TEST ONLY: the harness's DL_DETERMINISTIC=<seed> streams. A proof made with a
/// known seed has known masks and is not zero knowledge; a custodian process must leave it None.
#[derive(Default)]
pub struct ProveOpts {
    #[cfg(feature = "test-det")]
    pub det_seed: Option<String>,
    pub legacy: bool,
    pub cheat: Option<Cheat>,
    /// re-encode the round-1 rows on each pass instead of keeping them (same bytes; about 3 x the encoding work,
    /// and no m1 x nD table: for several provers sharing one machine)
    pub low_memory: bool,
}

fn group_vals(st: &Statement, wit: &Witness) -> Result<Vec<(String, Vals)>, String> {
    let mut v = vec![];
    match (st.kind(), wit) {
        (Kind::Sk | Kind::Key, Witness::Sk { s, e_pk, cts }) => {
            v.push(("s".to_string(), Vals::Small(s.clone())));
            v.push(("e_pk".to_string(), Vals::Small(e_pk.clone())));
            for (j, w) in cts.iter().enumerate() {
                v.push((format!("e{j}"), Vals::Small(w.e.clone())));
                v.push((format!("r{j}"), Vals::Small(w.r.clone())));
            }
        }
        (Kind::Pk, Witness::Pk { cts }) => {
            for (j, w) in cts.iter().enumerate() {
                v.push((format!("u{j}"), Vals::Small(w.u.clone())));
                v.push((format!("e0_{j}"), Vals::Small(w.e0.clone())));
                v.push((format!("e1_{j}"), Vals::Small(w.e1.clone())));
                v.push((format!("r{j}"), Vals::Small(w.r.clone())));
            }
        }
        _ => return Err("witness kind does not match the statement".into()),
    }
    Ok(v)
}

fn lookup<'a>(vals: &'a [(String, Vals)], name: &str) -> Result<&'a Vals, String> {
    vals.iter().find(|(n, _)| n == name).map(|(_, v)| v).ok_or_else(|| format!("'{name}'"))
}

/// zkpopk_ligero.values_to_digits.
pub fn values_to_digits(groups: &[Group], vals: &[(String, Vals)], raw: bool) -> Result<Vec<Fe>, String> {
    let mut out = Vec::new();
    for g in groups {
        let v = lookup(vals, &g.name)?;
        if v.len() != g.n {
            return Err(format!("{}: length", g.name));
        }
        let u = g.range();
        let ws = weights(&u);
        let nd = ws.len();
        let lo_small = g.lo.to_i64();
        let u_small = u.to_u64();
        for i in 0..g.n {
            if let (Vals::Small(sv), Some(lo), Some(us)) = (v, lo_small, u_small) {
                let x = sv[i];
                let z = (x as i128) - (lo as i128);
                if z < 0 || z > us as i128 {
                    if !raw {
                        return Err(format!("{} outside its exact range", g.name));
                    }
                    out.push(Fe::from_i128(z));
                    out.extend(std::iter::repeat_n(Fe::ZERO, nd - 1));
                    continue;
                }
                push_digits_u64(z as u64, us, nd, &mut out);
            } else {
                let x = v.big(i);
                let z = &x - &g.lo;
                if z.is_negative() || z > BigInt::from(u.clone()) {
                    if !raw {
                        return Err(format!("{} outside its exact range", g.name));
                    }
                    out.push(Fe::from_bigint(&z));
                    out.extend(std::iter::repeat_n(Fe::ZERO, nd - 1));
                    continue;
                }
                push_digits_big(z.to_biguint().unwrap(), &ws, &mut out);
            }
        }
    }
    Ok(out)
}

fn push_digits_u64(mut z: u64, u: u64, nd: usize, out: &mut Vec<Fe>) {
    if nd == 1 {
        out.push(Fe::from_u64(z));
        return;
    }
    let top_w = u - (1u64 << (nd - 1)) + 1;
    let mut top = 0;
    if z >= 1u64 << (nd - 1) {
        top = 1;
        z -= top_w;
    }
    for j in 0..nd - 1 {
        out.push(if (z >> j) & 1 == 1 { ONE } else { Fe::ZERO });
    }
    out.push(if top == 1 { ONE } else { Fe::ZERO });
}

fn push_digits_big(mut z: BigUint, ws: &[BigUint], out: &mut Vec<Fe>) {
    let nd = ws.len();
    if nd == 1 {
        out.push(Fe::from_biguint(&z));
        return;
    }
    let mut top = false;
    if z >= BigUint::one() << (nd - 1) {
        top = true;
        z -= &ws[nd - 1];
    }
    for j in 0..nd - 1 {
        out.push(if z.bit(j as u64) { ONE } else { Fe::ZERO });
    }
    out.push(if top { ONE } else { Fe::ZERO });
}

fn rows(d: &[Fe], k: usize, m: usize) -> Vec<Vec<Fe>> {
    (0..m)
        .map(|r| {
            let mut row = vec![Fe::ZERO; k];
            let lo = (r * k).min(d.len());
            let hi = ((r + 1) * k).min(d.len());
            row[..hi - lo].copy_from_slice(&d[lo..hi]);
            row
        })
        .collect()
}

// ------------------------------------------------------------------------------------------- folds
/// rho[f][i][slot]: sk/key slot 0 = key, 1 + j = ciphertext j; pk slot 2j + b = (ciphertext j, equation b).
pub type Rho = Vec<Vec<Vec<Vec<u64>>>>;

pub fn draw_rho(tr: &mut Transcript, st: &Statement, f: usize) -> Rho {
    let n = st.reg().n;
    let l = st.reg().primes.len();
    let mut calls = vec![];
    for fi in 0..f {
        for (i, &q) in st.reg().primes.iter().enumerate() {
            if st.kind().secret() {
                calls.push((format!("rho-{fi}-key-{i}"), n, q));
                for j in 0..st.cts().len() {
                    calls.push((format!("rho-{fi}-ct-{j}-{i}"), n, q));
                }
            } else {
                for j in 0..st.cts().len() {
                    calls.push((format!("rho-{fi}-ct-{j}-{i}-0"), n, q));
                    calls.push((format!("rho-{fi}-ct-{j}-{i}-1"), n, q));
                }
            }
        }
    }
    let mut flat = tr.ints_u64_many(&calls).into_iter();
    let per = if st.kind().secret() { 1 + st.cts().len() } else { 2 * st.cts().len() };
    (0..f).map(|_| (0..l).map(|_| (0..per).map(|_| flat.next().unwrap()).collect()).collect()).collect()
}

fn adj_fe(c: &[u64]) -> Vec<Fe> {
    let n = c.len();
    let mut out = Vec::with_capacity(n);
    out.push(Fe::from_u64(c[0]));
    for i in 1..n {
        out.push(Fe::from_u64(c[n - i]).neg());
    }
    out
}

fn dot_u64(a: &[Fe], b: &[u64]) -> Fe {
    a.iter().zip(b).fold(Fe::ZERO, |acc, (x, y)| acc.add(x.mul(Fe::from_u64(*y))))
}

/// The lambda-combination of the F * L folded limb equations: per group the coefficient vector (mod P), and the
/// combined constant. (zkpopk_ligero.linear_system + the coefficient half of alpha_beta, by linearity.)
pub fn combine(st: &Statement, rho: &Rho, lam: &[Fe], f: usize) -> (Vec<(String, Vec<Fe>)>, Fe) {
    let reg = st.reg();
    let n = reg.n;
    let l = reg.primes.len();
    let m = st.cts().len();
    let t = Fe::from_u64(reg.t);
    let nega = Nega::new(n);
    let res = st.ct_res();
    let lamc = |fi: usize, i: usize| lam[fi * l + i];
    // per (i, slot): sum_f lam_{f,i} rho_{f,i,slot}
    let per = if st.kind().secret() { 1 + m } else { 2 * m };
    let rsum: Vec<Vec<Vec<Fe>>> = (0..l)
        .into_par_iter()
        .map(|i| {
            (0..per)
                .map(|sl| {
                    let mut acc = vec![Fe::ZERO; n];
                    for fi in 0..f {
                        let c = lamc(fi, i);
                        for (a, r) in acc.iter_mut().zip(&rho[fi][i][sl]) {
                            *a = a.add(c.mul(Fe::from_u64(*r)));
                        }
                    }
                    acc
                })
                .collect()
        })
        .collect();
    let mut groups: Vec<(String, Vec<Fe>)> = vec![];
    let mut constant = Fe::ZERO;
    let sumv = |vs: &mut dyn Iterator<Item = &Vec<Fe>>| -> Vec<Fe> {
        let mut acc = vec![Fe::ZERO; n];
        for v in vs {
            for (a, x) in acc.iter_mut().zip(v) {
                *a = a.add(*x);
            }
        }
        acc
    };
    let scale = |v: Vec<Fe>, c: Fe| -> Vec<Fe> { v.into_iter().map(|x| x.mul(c)).collect() };
    if st.kind().secret() {
        // s: sum_i adj(a_i) * R_key_i + t * sum_{i,j} adj(c1_ij) * R_ij, in the transform domain
        let jobs: Vec<(usize, Option<usize>)> = (0..l).flat_map(|i| std::iter::once((i, None)).chain((0..m).map(move |j| (i, Some(j))))).collect();
        let hat = jobs
            .par_iter()
            .map(|&(i, j)| {
                let (poly, r, c) = match j {
                    None => (&reg.a_res()[i], &rsum[i][0], ONE),
                    Some(j) => (&res[i][j].1, &rsum[i][1 + j], t),
                };
                let pa = nega.fwd(&adj_fe(poly));
                let pr = nega.fwd(r);
                pa.iter().zip(&pr).map(|(x, y)| x.mul(*y).mul(c)).collect::<Vec<Fe>>()
            })
            .reduce(|| vec![Fe::ZERO; n], |a, b| a.iter().zip(&b).map(|(x, y)| x.add(*y)).collect());
        groups.push(("s".into(), nega.inv(hat)));
        groups.push(("e_pk".into(), sumv(&mut (0..l).map(|i| &rsum[i][0]))));
        for (j, s) in st.slots().iter().enumerate() {
            let rj = sumv(&mut (0..l).map(|i| &rsum[i][1 + j]));
            groups.push((format!("r{j}"), s.iter().map(|&k| rj[k].neg()).collect()));
            groups.push((format!("e{j}"), scale(rj, t)));
        }
        for i in 0..l {
            constant = constant.add(dot_u64(&rsum[i][0], &reg.b_res()[i]));
            for j in 0..m {
                constant = constant.add(t.mul(dot_u64(&rsum[i][1 + j], &res[i][j].0)));
            }
        }
    } else {
        let tn = t.neg();
        for j in 0..m {
            let hat = (0..l)
                .into_par_iter()
                .map(|i| {
                    let b = nega.fwd(&adj_fe(&reg.b_res()[i]));
                    let a = nega.fwd(&adj_fe(&reg.a_res()[i]));
                    let r0 = nega.fwd(&rsum[i][2 * j]);
                    let r1 = nega.fwd(&rsum[i][2 * j + 1]);
                    (0..n).map(|k| tn.mul(b[k]).mul(r0[k]).sub(a[k].mul(r1[k]))).collect::<Vec<Fe>>()
                })
                .reduce(|| vec![Fe::ZERO; n], |a, b| a.iter().zip(&b).map(|(x, y)| x.add(*y)).collect());
            groups.push((format!("u{j}"), nega.inv(hat)));
            let r0 = sumv(&mut (0..l).map(|i| &rsum[i][2 * j]));
            let r1 = sumv(&mut (0..l).map(|i| &rsum[i][2 * j + 1]));
            groups.push((format!("r{j}"), st.slots()[j].iter().map(|&k| r0[k].neg()).collect()));
            groups.push((format!("e0_{j}"), scale(r0, tn)));
            groups.push((format!("e1_{j}"), r1.into_iter().map(|x| x.neg()).collect()));
            for i in 0..l {
                constant = constant.add(t.mul(dot_u64(&rsum[i][2 * j], &res[i][j].0)));
                constant = constant.add(dot_u64(&rsum[i][2 * j + 1], &res[i][j].1));
            }
        }
    }
    for fi in 0..f {
        for (i, &q) in reg.primes.iter().enumerate() {
            groups.push((format!("K{fi}_{i}"), vec![Fe::from_u64(q).neg().mul(lamc(fi, i))]));
        }
    }
    (groups, constant)
}

/// alpha over the flat digit vector (rows 1 then rows 2) and beta with <alpha, digits> = beta.
pub fn alpha_beta(groups: &[Group], comb: &[(String, Vec<Fe>)], constant: Fe) -> (Vec<Fe>, Fe) {
    let mut beta = constant.neg();
    let mut alpha = Vec::new();
    for g in groups {
        let c = &comb.iter().find(|(n, _)| *n == g.name).expect("group in the combination").1;
        let ws: Vec<Fe> = weights(&g.range()).iter().map(Fe::from_biguint).collect();
        let s = c.iter().fold(Fe::ZERO, |a, x| a.add(*x));
        beta = beta.sub(Fe::from_bigint(&g.lo).mul(s));
        alpha.reserve(c.len() * ws.len());
        for x in c {
            for w in &ws {
                alpha.push(x.mul(*w));
            }
        }
    }
    (alpha, beta)
}

// ------------------------------------------------------------------------------------------- exact quotients
/// Wrapping 256-bit two's-complement accumulator (exact when the true sum is below 2^255 in magnitude).
#[derive(Clone, Copy, Default)]
struct W256([u64; 4]);

impl W256 {
    fn add(&mut self, o: &W256) {
        let mut c = 0u128;
        for i in 0..4 {
            let s = self.0[i] as u128 + o.0[i] as u128 + c;
            self.0[i] = s as u64;
            c = s >> 64;
        }
    }
    fn from_i128(y: i128) -> W256 {
        let s = if y < 0 { u64::MAX } else { 0 };
        W256([y as u64, (y >> 64) as u64, s, s])
    }
    fn mul_u64(&self, a: u64) -> W256 {
        let mut out = [0u64; 4];
        let mut c = 0u128;
        for i in 0..4 {
            let p = self.0[i] as u128 * a as u128 + c;
            out[i] = p as u64;
            c = p >> 64;
        }
        W256(out)
    }
    fn add_mul(&mut self, a: u64, y: i128) {
        let p = W256::from_i128(y).mul_u64(a);
        self.add(&p);
    }
    fn neg(&self) -> W256 {
        let mut x = W256([!self.0[0], !self.0[1], !self.0[2], !self.0[3]]);
        x.add(&W256([1, 0, 0, 0]));
        x
    }
    fn to_bigint(self) -> BigInt {
        let neg = self.0[3] >> 63 == 1;
        let m = if neg { self.neg() } else { self };
        let mut u = vec![];
        for x in m.0 {
            u.push(x as u32);
            u.push((x >> 32) as u32);
        }
        let v = BigInt::from(BigUint::from_slice(&u));
        if neg {
            -v
        } else {
            v
        }
    }
}

/// The exact folded totals sum rho * LHS for every (fold, prime), over Z (the prover's quotient numerators).
fn totals(st: &Statement, rho: &Rho, vals: &[(String, Vals)], f: usize) -> Result<Vec<BigInt>, String> {
    let reg = st.reg();
    let n = reg.n;
    let l = reg.primes.len();
    let m = st.cts().len();
    let nega = Nega::new(n);
    let res = st.ct_res();
    let small = |name: &str| -> Result<Vec<i64>, String> {
        lookup(vals, name)?.small().cloned().ok_or_else(|| format!("{name}: the ring factor must be small"))
    };
    let all_small = vals.iter().all(|(_, v)| v.small().is_some());
    let get = |name: &str| lookup(vals, name);
    // exact ring products with the secret (s or u), per prime
    let mut out = vec![BigInt::zero(); f * l];
    if st.kind().secret() {
        let s = small("s")?;
        if s.len() != n {
            return Err("s: length".into());
        }
        let prods: Vec<(Vec<i128>, Vec<Vec<i128>>)> = (0..l)
            .into_par_iter()
            .map(|i| {
                let a_s = exact_nega(&nega, &reg.a_res()[i], &s).ok_or("s too large")?;
                let cs = (0..m).map(|j| exact_nega(&nega, &res[i][j].1, &s).ok_or("s too large")).collect::<Result<Vec<_>, _>>()?;
                Ok((a_s, cs))
            })
            .collect::<Result<_, &str>>()?;
        let e_pk = get("e_pk")?;
        let es: Vec<&Vals> = (0..m).map(|j| get(&format!("e{j}"))).collect::<Result<_, _>>()?;
        let rs: Vec<&Vals> = (0..m).map(|j| get(&format!("r{j}"))).collect::<Result<_, _>>()?;
        for v in std::iter::once(e_pk).chain(es.iter().copied()) {
            if v.len() != n {
                return Err("error vector: length".into());
            }
        }
        for (v, sl) in rs.iter().zip(st.slots()) {
            if v.len() != sl.len() {
                return Err("r: length".into());
            }
        }
        let tb = BigInt::from(reg.t);
        let r = (0..f * l)
            .into_par_iter()
            .map(|c| {
                let (fi, i) = (c / l, c % l);
                let (a_s, cs) = &prods[i];
                let bq = &reg.b_res()[i];
                let rk = &rho[fi][i][0];
                if all_small {
                    let ep = e_pk.small().unwrap();
                    let mut acc = W256::default();
                    for k in 0..n {
                        acc.add_mul(rk[k], bq[k] as i128 + a_s[k] + ep[k] as i128);
                    }
                    let mut act = W256::default();
                    let mut accr = W256::default();
                    for j in 0..m {
                        let rc = &rho[fi][i][1 + j];
                        let e = es[j].small().unwrap();
                        let c0 = &res[i][j].0;
                        for k in 0..n {
                            act.add_mul(rc[k], c0[k] as i128 + cs[j][k] + e[k] as i128);
                        }
                        let rr = rs[j].small().unwrap();
                        for (idx, &k) in st.slots()[j].iter().enumerate() {
                            accr.add_mul(rc[k], rr[idx] as i128);
                        }
                    }
                    let mut tot = act.mul_u64(reg.t);
                    tot.add(&acc);
                    tot.add(&accr.neg());
                    tot.to_bigint()
                } else {
                    let mut tot = BigInt::zero();
                    for k in 0..n {
                        tot += BigInt::from(rk[k]) * (BigInt::from(bq[k] as i128 + a_s[k]) + e_pk.big(k));
                    }
                    for j in 0..m {
                        let rc = &rho[fi][i][1 + j];
                        let c0 = &res[i][j].0;
                        let mut ct = BigInt::zero();
                        for k in 0..n {
                            ct += BigInt::from(rc[k]) * (BigInt::from(c0[k] as i128 + cs[j][k]) + es[j].big(k));
                        }
                        tot += &tb * ct;
                        for (idx, &k) in st.slots()[j].iter().enumerate() {
                            tot -= BigInt::from(rc[k]) * rs[j].big(idx);
                        }
                    }
                    tot
                }
            })
            .collect::<Vec<_>>();
        out = r;
    } else {
        let us: Vec<Vec<i64>> = (0..m).map(|j| small(&format!("u{j}"))).collect::<Result<_, _>>()?;
        if us.iter().any(|u| u.len() != n) {
            return Err("u: length".into());
        }
        // per (i, j): b_i * u_j and a_i * u_j exactly
        let prods: Vec<Vec<(Vec<i128>, Vec<i128>)>> = (0..l)
            .into_par_iter()
            .map(|i| {
                us.iter()
                    .map(|u| Ok((exact_nega(&nega, &reg.b_res()[i], u).ok_or("u too large")?, exact_nega(&nega, &reg.a_res()[i], u).ok_or("u too large")?)))
                    .collect::<Result<Vec<_>, &str>>()
            })
            .collect::<Result<_, &str>>()?;
        let e0s: Vec<&Vals> = (0..m).map(|j| get(&format!("e0_{j}"))).collect::<Result<_, _>>()?;
        let e1s: Vec<&Vals> = (0..m).map(|j| get(&format!("e1_{j}"))).collect::<Result<_, _>>()?;
        let rs: Vec<&Vals> = (0..m).map(|j| get(&format!("r{j}"))).collect::<Result<_, _>>()?;
        if e0s.iter().chain(&e1s).any(|v| v.len() != n) || rs.iter().zip(st.slots()).any(|(v, s)| v.len() != s.len()) {
            return Err("pk witness: length".into());
        }
        let tb = BigInt::from(reg.t);
        out = (0..f * l)
            .into_par_iter()
            .map(|c| {
                let (fi, i) = (c / l, c % l);
                let mut tot = BigInt::zero();
                for j in 0..m {
                    let (bu, au) = &prods[i][j];
                    let (c0, c1) = &res[i][j];
                    let r0 = &rho[fi][i][2 * j];
                    let r1 = &rho[fi][i][2 * j + 1];
                    if all_small {
                        let (e0, e1, rr) = (e0s[j].small().unwrap(), e1s[j].small().unwrap(), rs[j].small().unwrap());
                        let mut a0 = W256::default();
                        let mut a1 = W256::default();
                        let mut ar = W256::default();
                        for k in 0..n {
                            a0.add_mul(r0[k], c0[k] as i128 - bu[k] - e0[k] as i128);
                            a1.add_mul(r1[k], c1[k] as i128 - au[k] - e1[k] as i128);
                        }
                        for (idx, &k) in st.slots()[j].iter().enumerate() {
                            ar.add_mul(r0[k], rr[idx] as i128);
                        }
                        let mut x = a0.mul_u64(reg.t);
                        x.add(&a1);
                        x.add(&ar.neg());
                        tot += x.to_bigint();
                    } else {
                        let mut s0 = BigInt::zero();
                        let mut s1 = BigInt::zero();
                        for k in 0..n {
                            s0 += BigInt::from(r0[k]) * (BigInt::from(c0[k] as i128 - bu[k]) - e0s[j].big(k));
                            s1 += BigInt::from(r1[k]) * (BigInt::from(c1[k] as i128 - au[k]) - e1s[j].big(k));
                        }
                        tot += &tb * s0 + s1;
                        for (idx, &k) in st.slots()[j].iter().enumerate() {
                            tot -= BigInt::from(r0[k]) * rs[j].big(idx);
                        }
                    }
                }
                tot
            })
            .collect();
    }
    Ok(out)
}

// ------------------------------------------------------------------------------------------- prover
fn colbytes(rows: &[Vec<Fe>], j: usize) -> Vec<u8> {
    let mut out = Vec::with_capacity(rows.len() * EB);
    for r in rows {
        out.extend_from_slice(&r[j].to_be32());
    }
    out
}

fn commit(rows: &[Vec<Fe>], salts: &[[u8; 32]]) -> Merkle {
    let n_d = salts.len();
    let leaves: Vec<[u8; 32]> = (0..n_d).into_par_iter().map(|j| leaf(&salts[j], &colbytes(rows, j))).collect();
    Merkle::build(leaves)
}

fn encode_row(code: &Code, msg: &[Fe], rv: &[Fe]) -> Vec<Fe> {
    let mut c = code.interp(msg);
    c.resize(code.k + code.th, Fe::ZERO);
    for (l, r) in rv.iter().enumerate() {
        c[l] = c[l].sub(*r);
        c[code.k + l] = c[code.k + l].add(*r);
    }
    code.eval_d(&c)
}

fn draw_row_rand(code: &Code, n: usize, rng: &mut dyn Hiding) -> Vec<Vec<Fe>> {
    (0..n).map(|_| (0..code.th).map(|_| rng.fe()).collect()).collect()
}

fn encode_rows(code: &Code, msgs: &[Vec<Fe>], rng: &mut dyn Hiding) -> Vec<Vec<Fe>> {
    // the row randomness is drawn in row order, then the rows are encoded in parallel
    let rand = draw_row_rand(code, msgs.len(), rng);
    msgs.par_iter().zip(rand.par_iter()).map(|(msg, rv)| encode_row(code, msg, rv)).collect()
}

/// The round-1 data rows' codewords: kept (fast), or re-encoded from (message, randomness) on every pass (low
/// memory: three encodings instead of one, and no m1 x nD table). Same field values either way.
enum Rows1 {
    Stored(Vec<Vec<Fe>>),
    Lean { msgs: Vec<Vec<Fe>>, rand: Vec<Vec<Fe>> },
}

impl Rows1 {
    /// Visit the codewords in row order, in chunks: f(first row index, rows).
    fn chunks(&self, code: &Code, mut f: impl FnMut(usize, &[Vec<Fe>])) {
        match self {
            Rows1::Stored(e) => {
                let c = 2 * rayon::current_num_threads().max(1);
                for (b, ch) in e.chunks(c).enumerate() {
                    f(b * c, ch);
                }
            }
            Rows1::Lean { msgs, rand } => {
                let c = 2 * rayon::current_num_threads().max(1);
                let mut r0 = 0;
                while r0 < msgs.len() {
                    let r1 = (r0 + c).min(msgs.len());
                    let enc: Vec<Vec<Fe>> = (r0..r1).into_par_iter().map(|r| encode_row(code, &msgs[r], &rand[r])).collect();
                    f(r0, &enc);
                    r0 = r1;
                }
            }
        }
    }
}

/// Merkle tree over the columns of (rows, then extra rows), hashing each leaf as a stream over the rows.
fn commit_streamed(code: &Code, rows: &Rows1, nrows: usize, extra: &[Vec<Fe>], salts: &[[u8; 32]]) -> Merkle {
    use sha2::{Digest, Sha256};
    let n_d = salts.len();
    let colb = ((nrows + extra.len()) * EB) as u64;
    let mut hs: Vec<Sha256> = salts
        .par_iter()
        .map(|s| {
            let mut h = Sha256::new();
            h.update(4u64.to_be_bytes());
            h.update(b"leaf");
            h.update(32u64.to_be_bytes());
            h.update(s);
            h.update(colb.to_be_bytes());
            h
        })
        .collect();
    let feed = |hs: &mut Vec<Sha256>, ch: &[Vec<Fe>]| {
        hs.par_iter_mut().enumerate().for_each(|(j, h)| {
            for r in ch {
                h.update(r[j].to_be32());
            }
        });
    };
    rows.chunks(code, |_, ch| feed(&mut hs, ch));
    feed(&mut hs, extra);
    let leaves: Vec<[u8; 32]> = hs.into_par_iter().map(|h| h.finalize().into()).collect();
    debug_assert_eq!(leaves.len(), n_d);
    Merkle::build(leaves)
}

fn alpha_rows(sh: &Shape, alpha: &[Fe]) -> Vec<Vec<Fe>> {
    let (k, m1, m2) = (sh.k, sh.m1, sh.m2);
    let a1 = &alpha[..sh.n1.min(alpha.len())];
    let a2 = &alpha[sh.n1.min(alpha.len())..];
    let mut r = rows(a1, k, m1);
    r.extend(rows(a2, k, m2));
    r
}

/// Prove with OS randomness. Errors: a statement out of the field's range, a witness that is out of range or does
/// not satisfy the relation.
pub fn prove(st: &Statement, wit: &Witness, tcols: usize) -> Result<Vec<u8>, String> {
    prove_with(st, wit, tcols, &mut ProveOpts::default())
}

pub fn prove_with(st: &Statement, wit: &Witness, tcols: usize, opts: &mut ProveOpts) -> Result<Vec<u8>, String> {
    let sh = shape(st, tcols)?;
    let (k, th, m1, m2) = (sh.k, sh.th, sh.m1, sh.m2);
    let code = Code::new(k, th);
    let n_d = code.n_d;
    #[cfg(feature = "test-det")]
    let mut rng: Box<dyn Hiding> = match &opts.det_seed {
        Some(s) => Box::new(crate::rng::DetHiding::for_statement(s, "prove", &st.digest())),
        None => Box::new(OsHiding::new()),
    };
    #[cfg(not(feature = "test-det"))]
    let mut rng: Box<dyn Hiding> = Box::new(OsHiding::new());
    let cheat = opts.cheat.clone();
    let mut vals = group_vals(st, wit)?;
    if let Some(c) = &cheat {
        for (name, v) in &c.values1 {
            match vals.iter_mut().find(|(n, _)| n == name) {
                Some(slot) => slot.1 = v.clone(),
                None => vals.push((name.clone(), v.clone())),
            }
        }
    }
    let raw = cheat.as_ref().is_some_and(|c| c.raw);
    let d1 = match cheat.as_ref().and_then(|c| c.digits1.clone()) {
        Some(d) => d,
        None => values_to_digits(&sh.g1, &vals, raw)?,
    };
    let mut tr = Transcript::new(&st.digest(), opts.legacy);
    // round 1: digit rows and every mask
    let r1 = rows(&d1, k, m1);
    drop(d1);
    let rand1 = draw_row_rand(&code, m1, rng.as_mut());
    let rows1 = if opts.low_memory {
        Rows1::Lean { msgs: r1, rand: rand1 }
    } else {
        let e = r1.par_iter().zip(rand1.par_iter()).map(|(m, rv)| encode_row(&code, m, rv)).collect();
        drop(r1);
        Rows1::Stored(e)
    };
    let mp: Vec<Fe> = (0..k + th).map(|_| rng.fe()).collect();
    let mut ml: Vec<Fe> = (0..2 * k + th - 1).map(|_| rng.fe()).collect();
    let s0 = ml.iter().step_by(k).fold(Fe::ZERO, |a, x| a.add(*x));
    ml[0] = ml[0].sub(s0);
    let g: Vec<Fe> = (0..k + 2 * th - 1).map(|_| rng.fe()).collect();
    let mut mq = vec![Fe::ZERO; 2 * k + 2 * th - 1];
    for (i, x) in g.iter().enumerate() {
        mq[i] = mq[i].sub(*x);
        mq[i + k] = mq[i + k].add(*x);
    }
    let masks: Vec<Vec<Fe>> = [mp, ml, mq].par_iter().map(|c| code.eval_d(c)).collect();
    let salts1: Vec<[u8; 32]> = (0..n_d).map(|_| rng.salt()).collect();
    let t1 = commit_streamed(&code, &rows1, m1, &masks, &salts1);
    tr.absorb("root1", &t1.root());
    let rho = draw_rho(&mut tr, st, sh.f);
    // round 2: quotients
    let tots = totals(st, &rho, &vals, sh.f)?;
    drop(vals);
    let mut ks: Vec<(String, Vals)> = vec![];
    for (c, tot) in tots.iter().enumerate() {
        let (fi, i) = (c / st.reg().primes.len(), c % st.reg().primes.len());
        let q = BigInt::from(st.reg().primes[i]);
        let kn = format!("K{fi}_{i}");
        if !(tot % &q).is_zero() && cheat.is_none() {
            return Err(format!("witness does not satisfy constraint {kn}"));
        }
        ks.push((kn, Vals::Big(vec![tot.div_floor(&q)])));
    }
    if let Some(c) = &cheat {
        for (name, v) in &c.k {
            if let Some(slot) = ks.iter_mut().find(|(n, _)| n == name) {
                slot.1 = Vals::Big(vec![v.clone()]);
            }
        }
    }
    let d2 = match cheat.as_ref().and_then(|c| c.digits2.clone()) {
        Some(d) => d,
        None => values_to_digits(&sh.g2, &ks, raw)?,
    };
    let r2 = rows(&d2, k, m2);
    let e2 = encode_rows(&code, &r2, rng.as_mut());
    let salts2: Vec<[u8; 32]> = (0..n_d).map(|_| rng.salt()).collect();
    let t2 = commit(&e2, &salts2);
    tr.absorb("root2", &t2.root());
    let mrows = m1 + m2;
    let gam = tr.ints_p("gamma", mrows);
    let lam = tr.ints_p("lambda", sh.f * st.reg().primes.len());
    let gq = tr.ints_p("gamma-q", mrows);
    let (comb, constant) = combine(st, &rho, &lam, sh.f);
    drop(rho);
    let groups: Vec<Group> = sh.g1.iter().chain(&sh.g2).cloned().collect();
    let (alpha, _beta) = alpha_beta(&groups, &comb, constant);
    drop(comb);
    let arows = alpha_rows(&sh, &alpha);
    drop(alpha);
    // w, q, p on D: masks + sum over rows of gamma_r E_r, RD_r E_r, gamma'_r (E_r^2 - E_r), in row chunks
    let mut wd = masks[0].clone();
    let mut qd = masks[1].clone();
    let mut pd = masks[2].clone();
    let mut acc = |r0: usize, ch: &[Vec<Fe>]| {
        let rds: Vec<Vec<Fe>> = (0..ch.len()).into_par_iter().map(|x| code.eval_d(&code.interp(&arows[r0 + x]))).collect();
        let blk = 4096.min(n_d);
        wd.par_chunks_mut(blk).zip(qd.par_chunks_mut(blk)).zip(pd.par_chunks_mut(blk)).enumerate().for_each(|(b, ((w, q), p))| {
            for (x, er) in ch.iter().enumerate() {
                let (gr, gqr) = (gam[r0 + x], gq[r0 + x]);
                let rd = &rds[x];
                for o in 0..w.len() {
                    let j = b * blk + o;
                    let y = er[j];
                    w[o] = w[o].add(gr.mul(y));
                    q[o] = q[o].add(rd[j].mul(y));
                    p[o] = p[o].add(gqr.mul(y.mul(y).sub(y)));
                }
            }
        });
    };
    rows1.chunks(&code, |r0, ch| acc(r0, ch));
    for (x, ch) in e2.chunks(2 * rayon::current_num_threads().max(1)).enumerate() {
        acc(m1 + x * 2 * rayon::current_num_threads().max(1), ch);
    }
    let polys: Vec<Vec<Fe>> = [wd, qd, pd].par_iter().map(|v| code.coeffs_d(v)).collect();
    let (lw, lq, lp) = (k + th, 2 * k + th - 1, 2 * k + 2 * th - 1);
    if cheat.is_none() && (polys[0][lw..].iter().any(|x| !x.is_zero()) || polys[1][lq..].iter().any(|x| !x.is_zero()) || polys[2][lp..].iter().any(|x| !x.is_zero())) {
        return Err("prover: a message exceeds its degree (internal)".into());
    }
    let mut msg = Vec::with_capacity(EB * (lw + lq + lp));
    for x in polys[0][..lw].iter().chain(&polys[1][..lq]).chain(&polys[2][..lp]) {
        msg.extend_from_slice(&x.to_be32());
    }
    tr.absorb("msgs", &msg);
    let jcols = tr.distinct("cols", tcols, n_d);
    let mut out = Vec::with_capacity(crate::statement::proof_bytes(k, th, tcols, m1, m2));
    out.extend_from_slice(&t1.root());
    out.extend_from_slice(&t2.root());
    out.extend_from_slice(&msg);
    // the opened round-1 columns (one more pass in low-memory mode)
    let mut cols1: Vec<Vec<u8>> = vec![Vec::with_capacity((m1 + 3) * EB); jcols.len()];
    rows1.chunks(&code, |_, ch| {
        for (c, &j) in jcols.iter().enumerate() {
            for r in ch {
                cols1[c].extend_from_slice(&r[j].to_be32());
            }
        }
    });
    for (c, &j) in jcols.iter().enumerate() {
        for m in &masks {
            cols1[c].extend_from_slice(&m[j].to_be32());
        }
    }
    for (c, &j) in jcols.iter().enumerate() {
        out.extend_from_slice(&cols1[c]);
        out.extend_from_slice(&salts1[j]);
        for h in t1.path(j) {
            out.extend_from_slice(&h);
        }
        out.extend(colbytes(&e2, j));
        out.extend_from_slice(&salts2[j]);
        for h in t2.path(j) {
            out.extend_from_slice(&h);
        }
    }
    if out.len() != crate::statement::proof_bytes(k, th, tcols, m1, m2) {
        return Err("prover: proof length differs from the formula (internal)".into());
    }
    Ok(out)
}

// ------------------------------------------------------------------------------------------- verifier
/// Verify untrusted bytes against a statement the recipient built from its OWN expected context and the pinned
/// registry. Ok(()) is accept; Err(reason) names the check that refused (the harness's reason strings).
pub fn verify(st: &Statement, blob: &[u8], tcols: usize) -> Result<(), String> {
    verify_opts(st, blob, tcols, false)
}

/// `legacy = true` reproduces the statement-only transcript (the Fiat-Shamir falsifier); never for a recipient.
pub fn verify_opts(st: &Statement, blob: &[u8], tcols: usize, legacy: bool) -> Result<(), String> {
    let reg = st.reg();
    if tcols == 0 {
        return Err("profile: T must be positive".into());
    }
    if !reg.valid() {
        return Err("key registry invalid".into());
    }
    if reg.a.len() != reg.n || reg.a.to_big() != crate::statement::public_a(&reg.seed, reg.n, &reg.q) {
        return Err("key registry: a is not the pinned seed's".into());
    }
    let sh = shape(st, tcols).map_err(|e| format!("malformed: {e}"))?;
    let (k, th, m1, m2) = (sh.k, sh.th, sh.m1, sh.m2);
    if blob.len() != crate::statement::proof_bytes(k, th, tcols, m1, m2) {
        return Err("proof length".into());
    }
    let code = Code::new(k, th);
    let (n_d, lg_d) = (code.n_d, code.lg_d);
    let mut at = 0usize;
    let take = |at: &mut usize, n: usize| -> &[u8] {
        let x = &blob[*at..*at + n];
        *at += n;
        x
    };
    let elems = |at: &mut usize, n: usize| -> Result<Vec<Fe>, String> {
        let mut out = Vec::with_capacity(n);
        for _ in 0..n {
            let x = &blob[*at..*at + EB];
            *at += EB;
            out.push(Fe::from_be32(x).ok_or("malformed: noncanonical field element")?);
        }
        Ok(out)
    };
    let root1 = take(&mut at, 32).to_vec();
    let root2 = take(&mut at, 32).to_vec();
    let mstart = at;
    let w = elems(&mut at, k + th)?;
    let q = elems(&mut at, 2 * k + th - 1)?;
    let p = elems(&mut at, 2 * k + 2 * th - 1)?;
    let msg = &blob[mstart..at];
    let mut tr = Transcript::new(&st.digest(), legacy);
    tr.absorb("root1", &root1);
    let rho = draw_rho(&mut tr, st, sh.f);
    tr.absorb("root2", &root2);
    let mrows = m1 + m2;
    let gam = tr.ints_p("gamma", mrows);
    let lam = tr.ints_p("lambda", sh.f * reg.primes.len());
    let gq = tr.ints_p("gamma-q", mrows);
    tr.absorb("msgs", msg);
    let jcols = tr.distinct("cols", tcols, n_d);
    let (comb, constant) = combine(st, &rho, &lam, sh.f);
    drop(rho);
    let groups: Vec<Group> = sh.g1.iter().chain(&sh.g2).cloned().collect();
    let (alpha, beta) = alpha_beta(&groups, &comb, constant);
    drop(comb);
    let arows = alpha_rows(&sh, &alpha);
    drop(alpha);
    // linear: sum over H of q = beta; quadratic: (X^k - 1) | p
    let sq = q.iter().step_by(k).fold(Fe::ZERO, |a, x| a.add(*x));
    if Fe::from_u64(k as u64).mul(sq) != beta {
        return Err("linear test: the folded limb equations do not hold".into());
    }
    let mut fold = vec![Fe::ZERO; k];
    for (i, x) in p.iter().enumerate() {
        fold[i % k] = fold[i % k].add(*x);
    }
    if fold.iter().any(|x| !x.is_zero()) {
        return Err("quadratic test: a committed digit is not binary".into());
    }
    let mut cols = Vec::with_capacity(tcols);
    for &j in &jcols {
        let c1 = elems(&mut at, m1 + 3)?;
        let s1 = take(&mut at, 32).to_vec();
        let p1: Vec<&[u8]> = (0..lg_d).map(|_| take(&mut at, 32)).collect();
        let c2 = elems(&mut at, m2)?;
        let s2 = take(&mut at, 32).to_vec();
        let p2: Vec<&[u8]> = (0..lg_d).map(|_| take(&mut at, 32)).collect();
        let cb1: Vec<u8> = c1.iter().flat_map(|x| x.to_be32()).collect();
        if !mverify(&root1, &cb1, &s1, j, &p1) {
            return Err("Merkle path (root 1)".into());
        }
        let cb2: Vec<u8> = c2.iter().flat_map(|x| x.to_be32()).collect();
        if !mverify(&root2, &cb2, &s2, j, &p2) {
            return Err("Merkle path (root 2)".into());
        }
        cols.push((j, c1, c2));
    }
    if at != blob.len() {
        return Err("proof length".into());
    }
    // <alpha_r, Lagrange basis at x> = interp(alpha_r)(x): the rows' encodings, read at the opened columns
    let ra: Vec<Vec<Fe>> = arows
        .par_iter()
        .map(|ar| {
            let rd = code.eval_d(&code.interp(ar));
            jcols.iter().map(|&j| rd[j]).collect()
        })
        .collect();
    drop(arows);
    let results: Vec<Result<(), String>> = cols
        .par_iter()
        .enumerate()
        .map(|(ci, (j, c1, c2))| {
            let x = code.pts[*j];
            let u: Vec<Fe> = c1[..m1].iter().chain(c2.iter()).copied().collect();
            let (mp, ml, mq) = (c1[m1], c1[m1 + 1], c1[m1 + 2]);
            let prox = gam.iter().zip(&u).fold(mp, |a, (g, y)| a.add(g.mul(*y)));
            if peval(&w, x) != prox {
                return Err("proximity test (column)".to_string());
            }
            let lin = ra.iter().zip(&u).fold(ml, |a, (r, y)| a.add(y.mul(r[ci])));
            if peval(&q, x) != lin {
                return Err("linear test (column)".to_string());
            }
            let quad = gq.iter().zip(&u).fold(mq, |a, (g, y)| a.add(g.mul(y.mul(*y).sub(*y))));
            if peval(&p, x) != quad {
                return Err("quadratic test (column)".to_string());
            }
            Ok(())
        })
        .collect();
    for r in results {
        r?;
    }
    Ok(())
}

// ------------------------------------------------------------------------------------------- simulator / falsifier
/// Honest-verifier simulator run as an ATTACK: with statement-only (legacy) challenges it fabricates an accepting
/// proof for ANY statement, true or false, with no witness. The real verifier refuses it.
pub fn simulate_legacy(st: &Statement, tcols: usize, rng: &mut dyn Hiding) -> Result<Vec<u8>, String> {
    let sh = shape(st, tcols)?;
    let (k, th, m1, m2) = (sh.k, sh.th, sh.m1, sh.m2);
    let code = Code::new(k, th);
    let n_d = code.n_d;
    let mut tr = Transcript::new(&st.digest(), true);
    let rho = draw_rho(&mut tr, st, sh.f);
    let mrows = m1 + m2;
    let gam = tr.ints_p("gamma", mrows);
    let lam = tr.ints_p("lambda", sh.f * st.reg().primes.len());
    let gq = tr.ints_p("gamma-q", mrows);
    let jcols = tr.distinct("cols", tcols, n_d);
    let (comb, constant) = combine(st, &rho, &lam, sh.f);
    let groups: Vec<Group> = sh.g1.iter().chain(&sh.g2).cloned().collect();
    let (alpha, beta) = alpha_beta(&groups, &comb, constant);
    let arows = alpha_rows(&sh, &alpha);
    let w: Vec<Fe> = (0..k + th).map(|_| rng.fe()).collect();
    let mut q: Vec<Fe> = (0..2 * k + th - 1).map(|_| rng.fe()).collect();
    let sq = q.iter().step_by(k).fold(Fe::ZERO, |a, x| a.add(*x));
    q[0] = q[0].add(beta.mul(Fe::from_u64(k as u64).inv())).sub(sq);
    let g: Vec<Fe> = (0..k + 2 * th - 1).map(|_| rng.fe()).collect();
    let mut p = vec![Fe::ZERO; 2 * k + 2 * th - 1];
    for (i, x) in g.iter().enumerate() {
        p[i] = p[i].sub(*x);
        p[i + k] = p[i + k].add(*x);
    }
    let mut e1: Vec<Vec<Fe>> = (0..m1 + 3).map(|_| (0..n_d).map(|_| rng.fe()).collect()).collect();
    let e2: Vec<Vec<Fe>> = (0..m2).map(|_| (0..n_d).map(|_| rng.fe()).collect()).collect();
    let hk: Vec<Fe> = {
        let mut v = vec![ONE; k];
        for i in 1..k {
            v[i] = v[i - 1].mul(code.wk);
        }
        v
    };
    let kinv = Fe::from_u64(k as u64).inv();
    for &j in &jcols {
        let x = code.pts[j];
        let u: Vec<Fe> = (0..m1).map(|r| e1[r][j]).chain((0..m2).map(|r| e2[r][j])).collect();
        let z = x.pow_u64(k as u64).sub(ONE).mul(kinv);
        let inv = batch_inv(&hk.iter().map(|h| x.sub(*h)).collect::<Vec<_>>());
        let wb: Vec<Fe> = hk.iter().zip(&inv).map(|(h, iv)| h.mul(*iv).mul(z)).collect();
        e1[m1][j] = peval(&w, x).sub(gam.iter().zip(&u).fold(Fe::ZERO, |a, (g, y)| a.add(g.mul(*y))));
        let lin = arows.iter().zip(&u).fold(Fe::ZERO, |a, (ar, y)| a.add(y.mul(ar.iter().zip(&wb).fold(Fe::ZERO, |s, (x, y)| s.add(x.mul(*y))))));
        e1[m1 + 1][j] = peval(&q, x).sub(lin);
        e1[m1 + 2][j] = peval(&p, x).sub(gq.iter().zip(&u).fold(Fe::ZERO, |a, (g, y)| a.add(g.mul(y.mul(*y).sub(*y)))));
    }
    let salts1: Vec<[u8; 32]> = (0..n_d).map(|_| rng.salt()).collect();
    let salts2: Vec<[u8; 32]> = (0..n_d).map(|_| rng.salt()).collect();
    let t1 = commit(&e1, &salts1);
    let t2 = commit(&e2, &salts2);
    let mut out = Vec::new();
    out.extend_from_slice(&t1.root());
    out.extend_from_slice(&t2.root());
    for x in w.iter().chain(&q).chain(&p) {
        out.extend_from_slice(&x.to_be32());
    }
    for &j in &jcols {
        out.extend(colbytes(&e1, j));
        out.extend_from_slice(&salts1[j]);
        for h in t1.path(j) {
            out.extend_from_slice(&h);
        }
        out.extend(colbytes(&e2, j));
        out.extend_from_slice(&salts2[j]);
        for h in t2.path(j) {
            out.extend_from_slice(&h);
        }
    }
    Ok(out)
}

/// FORGERS ONLY: integers -> field (a helper for building cheat digits in tests).
pub fn fe_of(x: &BigInt) -> Fe {
    Fe::from_bigint(x)
}

