//! One custodian's SPDZ online phase (spdz.Engine, live mode, from one party's seat): its shares and MAC shares, its
//! tape, the public transcript every party holds identically, and its own open log for the MAC check. Vector ops
//! batch every independent opening of a round into one exchange, and write the transcript and open log back in the
//! harness's element-major order, so digests and Fiat-Shamir coins equal the harness's.
use crate::arith::*;
use crate::net::{self, Net};
use crate::tape::{Tag, Tape};
use pycompat::{PyRandom, ReprHasher};
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Sh {
    pub s: u64,
    pub m: u64,
}

pub const PHASES: [&str; 8] =
    ["input", "mul", "trunc", "lookup", "he_auth", "freivalds", "he_outer_commit", "he_outer_check"];
pub const PH_INPUT: u8 = 0;
pub const PH_MUL: u8 = 1;
pub const PH_TRUNC: u8 = 2;
pub const PH_LOOKUP: u8 = 3;
pub const PH_HE_AUTH: u8 = 4;
pub const PH_FREIVALDS: u8 = 5;
pub const PH_OUTER_COMMIT: u8 = 6;
pub const PH_OUTER_CHECK: u8 = 7;

/// The public transcript: (phase, broadcast shares or commitments, value) per entry, stored column-wise.
#[derive(Default)]
pub struct Transcript {
    pub phase: Vec<u8>,
    pub v: Vec<u64>,
    pub sh: Vec<[u64; 3]>,
    pub commits: Vec<[String; 3]>,
}

impl Transcript {
    pub fn len(&self) -> usize {
        self.phase.len()
    }

    pub fn is_empty(&self) -> bool {
        self.phase.is_empty()
    }

    pub fn push_open(&mut self, ph: u8, sh: [u64; 3], v: u64) {
        self.phase.push(ph);
        self.v.push(v);
        self.sh.push(sh);
    }

    /// repr(transcript) streamed into h: [('input', {}, c), ('mul', {0: a, 1: b, 2: c}, v), ...].
    pub fn repr_into(&self, h: &mut ReprHasher) {
        h.raw(b"[");
        let (mut si, mut ci) = (0usize, 0usize);
        for k in 0..self.len() {
            if k > 0 {
                h.raw(b", ");
            }
            let ph = self.phase[k];
            h.raw(b"(");
            h.s(PHASES[ph as usize]);
            match ph {
                PH_INPUT => h.raw(b", {}, "),
                PH_OUTER_COMMIT => {
                    let c = &self.commits[ci];
                    ci += 1;
                    h.raw(b", {");
                    for i in 0..3 {
                        if i > 0 {
                            h.raw(b", ");
                        }
                        h.u64(i as u64);
                        h.raw(b": ");
                        h.s(&c[i]);
                    }
                    h.raw(b"}, ");
                }
                _ => {
                    let s = self.sh[si];
                    si += 1;
                    h.raw(b", {");
                    for i in 0..3 {
                        if i > 0 {
                            h.raw(b", ");
                        }
                        h.u64(i as u64);
                        h.raw(b": ");
                        h.u64(s[i]);
                    }
                    h.raw(b"}, ");
                }
            }
            h.u64(self.v[k]);
            h.raw(b")");
        }
        h.raw(b"]");
    }

    /// One repr per line (as native_ref.py writes), for diffing.
    pub fn dump(&self, w: &mut impl std::io::Write) -> std::io::Result<()> {
        let (mut si, mut ci) = (0usize, 0usize);
        for k in 0..self.len() {
            let ph = self.phase[k];
            let mid = match ph {
                PH_INPUT => "{}".to_string(),
                PH_OUTER_COMMIT => {
                    let c = &self.commits[ci];
                    ci += 1;
                    format!("{{0: '{}', 1: '{}', 2: '{}'}}", c[0], c[1], c[2])
                }
                _ => {
                    let s = self.sh[si];
                    si += 1;
                    format!("{{0: {}, 1: {}, 2: {}}}", s[0], s[1], s[2])
                }
            };
            writeln!(w, "('{}', {}, {})", PHASES[ph as usize], mid, self.v[k])?;
        }
        Ok(())
    }
}

pub struct Party {
    pub i: usize,
    pub n: usize,
    pub p: u64,
    pub net: Net,
    pub tape: Tape,
    pub cur: usize,
    pub tr: Transcript,
    pub open_log: Vec<(u64, u64)>,
    pub wire: BTreeMap<&'static str, u64>,
    pub nopen: u64,
}

/// One opening staged for the transcript: phase, all broadcast shares, value, this party's MAC share.
type Staged = (u8, [u64; 3], u64, u64);

impl Party {
    pub fn new(i: usize, p: u64, net: Net, tape: Tape) -> Self {
        Party { i, n: 3, p, net, tape, cur: 0, tr: Transcript::default(), open_log: Vec::new(), wire: BTreeMap::new(), nopen: 0 }
    }

    pub fn alpha(&self) -> u64 {
        self.tape.alpha_i
    }

    fn count(&mut self, phase: u8, k: u64) {
        *self.wire.entry(PHASES[phase as usize]).or_insert(0) += k;
    }

    // ------------------------------------------------------------------ tape
    #[inline]
    pub fn tape_at(&self, pos: usize, tag: Tag) -> Sh {
        assert_eq!(self.tape.tags[pos], tag as u8, "tape tag mismatch at {pos}: want {tag:?}");
        Sh { s: self.tape.sh[pos], m: self.tape.mac[pos] }
    }

    pub fn take(&mut self, k: usize) -> usize {
        let b = self.cur;
        self.cur += k;
        assert!(self.cur <= self.tape.len(), "tape exhausted");
        b
    }

    // ------------------------------------------------------------------ local linear ops
    #[inline]
    pub fn add(&self, x: Sh, y: Sh) -> Sh {
        Sh { s: addmod(x.s, y.s, self.p), m: addmod(x.m, y.m, self.p) }
    }

    #[inline]
    pub fn sub(&self, x: Sh, y: Sh) -> Sh {
        Sh { s: submod(x.s, y.s, self.p), m: submod(x.m, y.m, self.p) }
    }

    #[inline]
    pub fn cmul(&self, c: u64, x: Sh) -> Sh {
        Sh { s: mulmod(c, x.s, self.p), m: mulmod(c, x.m, self.p) }
    }

    /// x + public c (c in [0, p)): party 0 adds c to its share; every party adds alpha_i c to its MAC share.
    #[inline]
    pub fn cadd(&self, c: u64, x: Sh) -> Sh {
        let p = self.p;
        Sh { s: if self.i == 0 { addmod(x.s, c, p) } else { x.s }, m: addmod(x.m, mulmod(self.alpha(), c, p), p) }
    }

    /// sum c_k x_k + const (coefficients and const in [0, p)).
    pub fn lin(&self, terms: &[(u64, Sh)], cst: u64) -> Sh {
        let p = self.p as u128;
        let (mut s, mut m) = (0u128, 0u128);
        for (k, &(c, x)) in terms.iter().enumerate() {
            s += c as u128 * x.s as u128;
            m += c as u128 * x.m as u128;
            if k % 32 == 31 {
                s %= p;
                m %= p;
            }
        }
        let out = Sh { s: (s % p) as u64, m: (m % p) as u64 };
        if cst != 0 { self.cadd(cst, out) } else { out }
    }

    pub fn centered(&self, v: u64) -> i64 {
        if v > self.p / 2 { v as i64 - self.p as i64 } else { v as i64 }
    }

    // ------------------------------------------------------------------ opening
    /// Broadcast the shares of xs; returns, per opening, every party's broadcast share and the value.
    pub fn exchange_open(&mut self, xs: &[u64]) -> Vec<([u64; 3], u64)> {
        let all = self.net.exchange(net::OPEN, xs);
        let p = self.p;
        (0..xs.len())
            .map(|k| {
                let sh = [all[0][k], all[1][k], all[2][k]];
                (sh, addmod(addmod(sh[0], sh[1], p), sh[2], p))
            })
            .collect()
    }

    fn commit_staged(&mut self, staged: Vec<Staged>) {
        let nn = (self.n * (self.n - 1)) as u64;
        for (ph, sh, v, mac) in staged {
            self.tr.push_open(ph, sh, v);
            self.open_log.push((mac, v));
            self.count(ph, nn);
            self.nopen += 1;
        }
    }

    /// spdz.Engine.open over a vector (all openings independent): one exchange, transcript in order.
    pub fn open_vec(&mut self, xs: &[Sh], ph: u8) -> Vec<u64> {
        let r = self.exchange_open(&xs.iter().map(|x| x.s).collect::<Vec<_>>());
        let staged: Vec<Staged> = r.iter().zip(xs).map(|(&(sh, v), x)| (ph, sh, v, x.m)).collect();
        self.commit_staged(staged);
        r.iter().map(|x| x.1).collect()
    }

    /// spdz.Engine.input for public broadcasts cs (the owner's c = v - r).
    pub fn input_vec(&mut self, cs: &[u64]) -> Vec<Sh> {
        let b = self.take(cs.len());
        let mut out = Vec::with_capacity(cs.len());
        for (k, &c) in cs.iter().enumerate() {
            let r = self.tape_at(b + k, Tag::In);
            self.tr.phase.push(PH_INPUT);
            self.tr.v.push(c);
            out.push(self.cadd(c, r));
        }
        self.count(PH_INPUT, (self.n * cs.len()) as u64);
        out
    }

    /// Beaver multiplication of independent pairs (spdz.Engine.mul, element by element in the harness).
    pub fn mul_vec(&mut self, xs: &[Sh], ys: &[Sh]) -> Vec<Sh> {
        let d = xs.len();
        let b = self.take(3 * d);
        let mut opens = Vec::with_capacity(2 * d);
        let mut trip = Vec::with_capacity(d);
        for k in 0..d {
            let a = self.tape_at(b + 3 * k, Tag::Ta);
            let bb = self.tape_at(b + 3 * k + 1, Tag::Tb);
            let c = self.tape_at(b + 3 * k + 2, Tag::Tc);
            opens.push(self.sub(xs[k], a));
            opens.push(self.sub(ys[k], bb));
            trip.push((a, bb, c));
        }
        let v = self.open_vec(&opens, PH_MUL);
        (0..d).map(|k| self.beaver_out(trip[k], v[2 * k], v[2 * k + 1])).collect()
    }

    #[inline]
    fn beaver_out(&self, (a, b, c): (Sh, Sh, Sh), e: u64, f: u64) -> Sh {
        self.lin(&[(1, c), (e, b), (f, a)], mulmod(e, f, self.p))
    }

    /// spdz.Engine.trunc over a vector: exact floor(x / 2^s), |x| < 2^K. Rounds run in lockstep across elements;
    /// the transcript and open log are written element by element, as the harness does.
    pub fn trunc_vec(&mut self, xs: &[Sh], s: u32, kk: u32) -> Vec<Sh> {
        let p = self.p;
        let d = xs.len();
        let su = s as usize;
        let per = 2 + su + 6 * (su - 1);
        let ent = 1 + 4 * (su - 1);
        let base = self.take(d * per);
        let mut staged: Vec<Staged> = vec![(0, [0; 3], 0, 0); d * ent];
        // round 0: open c = x + 2^K + r
        let mut copen = Vec::with_capacity(d);
        for k in 0..d {
            let r = self.tape_at(base + k * per, Tag::Tr);
            copen.push(self.add(self.cadd((1u64 << kk) % p, xs[k]), r));
        }
        let r0 = self.exchange_open(&copen.iter().map(|x| x.s).collect::<Vec<_>>());
        let cvals: Vec<u64> = r0.iter().map(|x| x.1).collect();
        for k in 0..d {
            staged[k * ent] = (PH_TRUNC, r0[k].0, r0[k].1, copen[k].m);
        }
        let mut abits = vec![vec![0u64; su]; d];
        let mut eq = vec![vec![Sh::default(); su]; d];
        let mut rbits = vec![vec![Sh::default(); su]; d];
        for k in 0..d {
            let clow = cvals[k] & ((1u64 << s) - 1);
            for j in 0..su {
                let a = (clow >> j) & 1;
                abits[k][j] = a;
                let rb = self.tape_at(base + k * per + 1 + j, Tag::Trb);
                rbits[k][j] = rb;
                let c1 = if a == 1 { p - 1 } else { 1 };
                let e = self.lin(&[(c1, rb)], a);
                eq[k][j] = self.lin(&[(p - 1, e)], 1);
            }
        }
        // i = s - 1: borrow = term, prefix = eq[s-1]
        let mut borrow: Vec<Sh> = (0..d).map(|k| self.cmul(1 - abits[k][su - 1], rbits[k][su - 1])).collect();
        let mut prefix: Vec<Sh> = (0..d).map(|k| eq[k][su - 1]).collect();
        for (it, i) in (0..su - 1).rev().enumerate() {
            let mut opens = Vec::with_capacity(4 * d);
            let mut trips = Vec::with_capacity(2 * d);
            for k in 0..d {
                let tb = base + k * per + 2 + su + 6 * it;
                let t1 = (self.tape_at(tb, Tag::Ta), self.tape_at(tb + 1, Tag::Tb), self.tape_at(tb + 2, Tag::Tc));
                let t2 = (self.tape_at(tb + 3, Tag::Ta), self.tape_at(tb + 4, Tag::Tb), self.tape_at(tb + 5, Tag::Tc));
                let term = self.cmul(1 - abits[k][i], rbits[k][i]);
                opens.push(self.sub(term, t1.0));
                opens.push(self.sub(prefix[k], t1.1));
                opens.push(self.sub(prefix[k], t2.0));
                opens.push(self.sub(eq[k][i], t2.1));
                trips.push(t1);
                trips.push(t2);
            }
            let r = self.exchange_open(&opens.iter().map(|x| x.s).collect::<Vec<_>>());
            for k in 0..d {
                for q in 0..4 {
                    let (sh, v) = r[4 * k + q];
                    staged[k * ent + 1 + 4 * it + q] = (PH_MUL, sh, v, opens[4 * k + q].m);
                }
                let term = self.beaver_out(trips[2 * k], r[4 * k].1, r[4 * k + 1].1);
                let pre = self.beaver_out(trips[2 * k + 1], r[4 * k + 2].1, r[4 * k + 3].1);
                borrow[k] = self.add(borrow[k], term);
                prefix[k] = pre;
            }
        }
        self.commit_staged(staged);
        (0..d)
            .map(|k| {
                let rhi = self.tape_at(base + k * per + 1 + su, Tag::Trh);
                let q = (cvals[k] >> s) as i64 - (1i64 << (kk - s));
                self.lin(&[(p - 1, rhi), (p - 1, borrow[k])], from_i64(q, p))
            })
            .collect()
    }

    /// spdz.Engine.lookup2 over a vector: P(u + offset) for each table, via the masked point and [r^j].
    pub fn lookup_vec(&mut self, us: &[Sh], offset: u64, tables: &[Vec<u64>], deg: usize) -> Vec<Vec<Sh>> {
        use rayon::prelude::*;
        let d = us.len();
        let base = self.take(d * deg);
        let mut opens = Vec::with_capacity(d);
        for k in 0..d {
            let r1 = self.tape_at(base + k * deg, Tag::Lp);
            opens.push(self.sub(self.cadd(offset % self.p, us[k]), r1));
        }
        let c = self.open_vec(&opens, PH_LOOKUP);
        let p = self.p;
        for k in 0..d {
            for j in 0..deg {
                self.tape_at(base + k * deg + j, Tag::Lp);
            }
        }
        let me = &*self;
        (0..d)
            .into_par_iter()
            .map(|k| {
                tables
                    .iter()
                    .map(|coeffs| {
                        let tay = taylor_shift(coeffs, c[k], p);
                        let terms: Vec<(u64, Sh)> = (1..tay.len())
                            .map(|j| (tay[j], Sh { s: me.tape.sh[base + k * deg + j - 1], m: me.tape.mac[base + k * deg + j - 1] }))
                            .collect();
                        me.lin(&terms, tay[0])
                    })
                    .collect()
            })
            .collect()
    }

    /// spdz.Engine.auth_plain over a vector: authenticate plain additive shares.
    pub fn auth_plain_vec(&mut self, plain: &[u64], ph: u8) -> Vec<Sh> {
        let d = plain.len();
        let b = self.take(d);
        let rs: Vec<Sh> = (0..d).map(|k| self.tape_at(b + k, Tag::Ar)).collect();
        let bs: Vec<u64> = (0..d).map(|k| submod(plain[k], rs[k].s, self.p)).collect();
        let r = self.exchange_open(&bs);
        let nn = (self.n * (self.n - 1)) as u64;
        let mut out = Vec::with_capacity(d);
        for k in 0..d {
            self.tr.push_open(ph, r[k].0, r[k].1);
            self.count(ph, nn);
            self.nopen += 1;
            out.push(self.cadd(r[k].1, rs[k]));
        }
        out
    }

    /// spdz.Engine.mac_check(coin_seed) with sigma commit-then-open. Returns this party's sigma; Err on abort.
    pub fn mac_check(&mut self, coin_seed: &str) -> Result<u64, String> {
        let p = self.p;
        let mut h = ReprHasher::new();
        h.s("mac-coins");
        h.s(coin_seed);
        h.list_u64(&self.open_log.iter().map(|x| x.1).collect::<Vec<_>>());
        self.tr.repr_into(&mut h);
        let mut rng = PyRandom::from_str_seed(&h.finish_hex());
        let a = self.alpha();
        let mut sig = 0u64;
        for &(m, v) in &self.open_log {
            let rho = rng.randrange_u64(p);
            sig = addmod(sig, mulmod(rho, submod(m, mulmod(a, v, p), p), p), p);
        }
        let mut nb = [0u8; 16];
        getrandom::getrandom(&mut nb).expect("os rng");
        let nonce = pycompat::repr::hex(&nb);
        let com = sigma_commit(self.i, sig, &nonce);
        let coms = self.net.exchange_bytes(net::CTRL, com.as_bytes());
        let mut msg = sig.to_le_bytes().to_vec();
        msg.extend_from_slice(nonce.as_bytes());
        let opened = self.net.exchange_bytes(net::CTRL, &msg);
        let mut total = 0u64;
        for j in 0..self.n {
            let sj = u64::from_le_bytes(opened[j][..8].try_into().unwrap());
            let nj = std::str::from_utf8(&opened[j][8..]).map_err(|_| "bad nonce".to_string())?;
            if sigma_commit(j, sj, nj).as_bytes() != coms[j].as_slice() {
                return Err(format!("MAC check: party {j}'s opened sigma does not match its commitment"));
            }
            total = addmod(total, sj, p);
        }
        let nn = (self.n * (self.n - 1)) as u64;
        *self.wire.entry("mac_check").or_insert(0) += 2 * nn;
        if total != 0 {
            return Err("MAC check failed: an opened value is not the authenticated one".into());
        }
        Ok(sig)
    }
}

/// spdz.h("sigma", i, sigma, nonce).
fn sigma_commit(i: usize, sig: u64, nonce: &str) -> String {
    let mut h = ReprHasher::new();
    h.s("sigma");
    h.u64(i as u64);
    h.u64(sig);
    h.s(nonce);
    h.finish_hex()
}

/// spdz.taylor_shift: coefficients of P(X + c) mod p.
pub fn taylor_shift(coeffs: &[u64], c: u64, p: u64) -> Vec<u64> {
    let mut a = coeffs.to_vec();
    let n = a.len();
    let cs = shoup(c, p);
    for i in 0..n {
        for k in (i..n.saturating_sub(1)).rev() {
            a[k] = addmod(a[k], mulmod_shoup(a[k + 1], c, cs, p), p);
        }
    }
    a
}

/// spdz.interpolate: coefficients of the degree < n polynomial through (k, values[k]), mod p.
pub fn interpolate(values: &[u64], p: u64) -> Vec<u64> {
    let n = values.len();
    let mut m = vec![1u64];
    for j in 0..n as u64 {
        // M <- M (X - j)
        let mut nm = vec![0u64; m.len() + 1];
        for (i, &c) in m.iter().enumerate() {
            nm[i + 1] = addmod(nm[i + 1], c, p);
            nm[i] = submod(nm[i], mulmod(j % p, c, p), p);
        }
        m = nm;
    }
    let mut coeffs = vec![0u64; n];
    for k in 0..n {
        let kk = k as u64 % p;
        let mut q = vec![0u64; n];
        let mut acc = 0u64;
        for i in (1..=n).rev() {
            acc = addmod(m[i], mulmod(acc, kk, p), p);
            q[i - 1] = acc;
        }
        let mut qk = 0u64;
        for &c in q.iter().rev() {
            qk = addmod(mulmod(qk, kk, p), c, p);
        }
        let scale = mulmod(values[k], invmod(qk, p), p);
        for i in 0..n {
            coeffs[i] = addmod(coeffs[i], mulmod(scale, q[i], p), p);
        }
    }
    coeffs
}
