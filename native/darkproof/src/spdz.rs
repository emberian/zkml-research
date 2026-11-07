//! One custodian's view of the SPDZ engine the prover multiplies with (spdz.Engine restricted to what the proofs
//! use): authenticated shares (share, MAC share), local linear ops, Beaver products from the ideal dealer batched
//! into one exchange per call, and the batched MAC check with sigma commit-then-open.
//!
//! The ideal dealer (spdz.Dealer) is one MT stream that deals every party's shares; in-process each party replays
//! it from the same state and keeps its own share (an ideal functionality, as in the harness).
//!
//! MAC-check coins: the harness seeds them from repr() of the whole frozen transcript; here they come from a
//! SHA-256 chain over every opening (phase, every party's broadcast share, value) as it happens. Both are fixed
//! only after the last broadcast. The coins never appear in a proof, so proof bytes are unaffected.
use crate::field;
use crate::net::Net;
use pycompat::PyRandom;
use sha2::{Digest, Sha256};

pub type Sh = (u64, u64);
pub const Z: Sh = (0, 0);

pub struct Dealer {
    pub rng: PyRandom,
    pub alpha_sh: Vec<u64>,
    pub alpha: u64,
}

impl Dealer {
    pub fn from_seed(seed: u64, n: usize) -> Self {
        let mut rng = PyRandom::from_u64(seed);
        let alpha_sh: Vec<u64> = (0..n).map(|_| rng.randrange_u64(field::p())).collect();
        let alpha = alpha_sh.iter().fold(0, |a, &b| field::add(a, b));
        Dealer { rng, alpha_sh, alpha }
    }
    pub fn from_state(state: &[u64], alpha_sh: Vec<u64>) -> Self {
        let alpha = alpha_sh.iter().fold(0, |a, &b| field::add(a, b));
        Dealer { rng: PyRandom::from_state(state), alpha_sh, alpha }
    }
    pub fn clone_dealer(&self) -> Self {
        Dealer { rng: self.rng.clone(), alpha_sh: self.alpha_sh.clone(), alpha: self.alpha }
    }
    /// dealer.auth(v): every party's (share, MAC share).
    pub fn auth_all(&mut self, v: u64) -> Vec<Sh> {
        let n = self.alpha_sh.len();
        let mut xs: Vec<u64> = (0..n - 1).map(|_| self.rng.randrange_u64(field::p())).collect();
        let sx = xs.iter().fold(0, |a, &b| field::add(a, b));
        xs.push(field::sub(v, sx));
        let mut ms: Vec<u64> = (0..n - 1).map(|_| self.rng.randrange_u64(field::p())).collect();
        let sm = ms.iter().fold(0, |a, &b| field::add(a, b));
        ms.push(field::sub(field::mul(self.alpha, v), sm));
        xs.into_iter().zip(ms).collect()
    }
    #[inline]
    pub fn auth(&mut self, v: u64, i: usize) -> Sh {
        self.auth_all(v)[i]
    }
}

/// One authenticated Beaver triple, this party's shares ([a], [b], [ab]).
pub type Triple = (Sh, Sh, Sh);

/// Where the proof's Beaver triples come from: the ideal dealer (the harness; in-process every party replays its MT
/// stream) or this party's preprocessing tape (the proof section of a darkstep / darkprep tape, MASCOT in the run).
pub enum Triples {
    Dealer(Dealer),
    /// the tape's triples in REVERSE order (the next one last): a drawn triple is popped and the spent part of the
    /// buffer returned as it empties (memory: a release's proof section is 47.7M triples, 2.3 GB, at M = 52)
    Tape { t: Vec<Triple>, pos: usize },
}

impl Triples {
    fn next(&mut self, i: usize) -> Triple {
        match self {
            Triples::Dealer(dl) => {
                let av = dl.rng.randrange_u64(field::p());
                let bv = dl.rng.randrange_u64(field::p());
                let a = dl.auth(av, i);
                let b = dl.auth(bv, i);
                let c = dl.auth(field::mul(av, bv), i);
                (a, b, c)
            }
            Triples::Tape { t, pos } => {
                let x = t.pop().expect("the tape's proof section is exhausted");
                *pos += 1;
                if t.capacity() >= 2 * t.len() + (1 << 16) {
                    t.shrink_to_fit();
                }
                x
            }
        }
    }
}

pub struct Spdz {
    pub i: usize,
    pub n: usize,
    pub alpha_i: u64,
    pub src: Triples,
    open_log: Vec<(u64, u64)>,
    coins: Sha256,
    pub nopen: u64,
    pub triples: u64,
    pub wire: std::collections::BTreeMap<&'static str, u64>,
    /// openings held before the MAC check runs on its own (DP_MAC_EVERY, default 2^22: 64 MiB of log); every party
    /// opens the same counts, so all run it at the same point
    mac_every: usize,
    /// a failed bounded check, reported by the next explicit mac_check
    mac_bad: Option<String>,
}

#[inline]
pub fn lin2(c0: u64, x: Sh, c1: u64, y: Sh) -> Sh {
    (
        field::add(field::mul(c0, x.0), field::mul(c1, y.0)),
        field::add(field::mul(c0, x.1), field::mul(c1, y.1)),
    )
}
#[inline]
pub fn shadd(x: Sh, y: Sh) -> Sh {
    (field::add(x.0, y.0), field::add(x.1, y.1))
}
#[inline]
pub fn shsub(x: Sh, y: Sh) -> Sh {
    (field::sub(x.0, y.0), field::sub(x.1, y.1))
}
#[inline]
pub fn cmul(c: u64, x: Sh) -> Sh {
    (field::mul(c, x.0), field::mul(c, x.1))
}

impl Spdz {
    pub fn new(i: usize, n: usize, dealer: Dealer) -> Self {
        let alpha_i = dealer.alpha_sh[i];
        Self::with_source(i, n, alpha_i, Triples::Dealer(dealer))
    }

    /// Party i with MAC key share alpha_i and its tape's proof-section triples.
    pub fn from_tape(i: usize, n: usize, alpha_i: u64, mut triples: Vec<Triple>) -> Self {
        triples.reverse();
        Self::with_source(i, n, alpha_i, Triples::Tape { t: triples, pos: 0 })
    }

    fn with_source(i: usize, n: usize, alpha_i: u64, src: Triples) -> Self {
        Spdz {
            i,
            n,
            alpha_i,
            src,
            open_log: Vec::new(),
            coins: Sha256::new(),
            nopen: 0,
            triples: 0,
            wire: Default::default(),
            mac_every: std::env::var("DP_MAC_EVERY").ok().and_then(|v| v.parse().ok()).unwrap_or(1 << 22),
            mac_bad: None,
        }
    }

    /// x + public c (party 0 adds c to its share; every party adds alpha_i c to its MAC share).
    #[inline]
    pub fn cadd(&self, c: u64, x: Sh) -> Sh {
        (if self.i == 0 { field::add(x.0, c) } else { x.0 }, field::add(x.1, field::mul(self.alpha_i, c)))
    }

    /// Open a batch of shared values in one exchange. Returns the opened values.
    pub fn open_batch(&mut self, net: &mut dyn Net, xs: &[Sh], phase: &'static str) -> Vec<u64> {
        let n = self.n;
        let all = net.all_gather(xs.iter().map(|x| x.0).collect());
        let mut out = Vec::with_capacity(xs.len());
        self.coins.update(phase.as_bytes());
        for (k, x) in xs.iter().enumerate() {
            let mut v = 0u64;
            for a in &all {
                v = field::add(v, a[k]);
                self.coins.update(a[k].to_le_bytes());
            }
            self.coins.update(v.to_le_bytes());
            self.open_log.push((x.1, v));
            out.push(v);
        }
        self.nopen += xs.len() as u64;
        *self.wire.entry(phase).or_insert(0) += (xs.len() * n * (n - 1)) as u64;
        if self.open_log.len() >= self.mac_every {
            if let Err(e) = self.check_log(net, "bounded") {
                self.mac_bad.get_or_insert(e);
            }
        }
        out
    }

    /// A uniform authenticated value: the next triple's a (its b and c are discarded; Python draws the triple as
    /// spdz.Engine.mul does, then keeps a).
    pub fn rand_from_triple(&mut self) -> Sh {
        self.triples += 1;
        self.src.next(self.i).0
    }

    /// Beaver products x_k * y_k, triples drawn from the dealer in order (spdz.Engine.mul per pair), every e and f
    /// opening in one exchange (Python opens e, f per product in the same order).
    pub fn mul_batch(&mut self, net: &mut dyn Net, xs: &[Sh], ys: &[Sh]) -> Vec<Sh> {
        // bounded exchanges: at most CHUNK products (2 CHUNK openings) per round trip
        const CHUNK: usize = 1 << 19;
        let mut out = Vec::with_capacity(xs.len());
        for (cx, cy) in xs.chunks(CHUNK).zip(ys.chunks(CHUNK)) {
            out.extend(self.mul_chunk(net, cx, cy));
        }
        out
    }

    fn mul_chunk(&mut self, net: &mut dyn Net, xs: &[Sh], ys: &[Sh]) -> Vec<Sh> {
        let i = self.i;
        self.triples += xs.len() as u64;
        let trip: Vec<Triple> = (0..xs.len()).map(|_| self.src.next(i)).collect();
        let mut ef = Vec::with_capacity(2 * xs.len());
        for (k, &(a, b, _)) in trip.iter().enumerate() {
            ef.push(shsub(xs[k], a));
            ef.push(shsub(ys[k], b));
        }
        let opened = self.open_batch(net, &ef, "mul");
        trip.iter()
            .enumerate()
            .map(|(k, &(a, b, c))| {
                let (e, f) = (opened[2 * k], opened[2 * k + 1]);
                let s = shadd(c, shadd(cmul(e, b), cmul(f, a)));
                let ef = field::mul(e, f);
                if ef != 0 { self.cadd(ef, s) } else { s }
            })
            .collect()
    }

    /// Batched MAC check over every opening so far, sigma committed before it is opened. Also reports a bounded check
    /// (one run on its own when the log reached mac_every openings) that failed.
    pub fn mac_check(&mut self, net: &mut dyn Net, label: &str) -> Result<(), String> {
        let r = self.check_log(net, label);
        match self.mac_bad.take() {
            Some(e) => Err(e),
            None => r,
        }
    }

    fn check_log(&mut self, net: &mut dyn Net, label: &str) -> Result<(), String> {
        let n = self.n;
        let mut h = self.coins.clone();
        h.update(b"mac-coins");
        h.update(label.as_bytes());
        let seed = crate::h::hex(&h.finalize());
        let mut rng = PyRandom::from_str_seed(&seed);
        let mut sig = 0u64;
        for &(m, v) in &self.open_log {
            let r = rng.randrange_u64(field::p());
            sig = field::add(sig, field::mul(r, field::sub(m, field::mul(self.alpha_i, v))));
        }
        // the log and its coins are spent on sigma (pass or fail)
        self.open_log.clear();
        self.coins = Sha256::new();
        let nonce = crate::rng::secret_bytes(16);
        let nw: Vec<u64> = nonce.chunks(8).map(|c| u64::from_le_bytes(c.try_into().unwrap())).collect();
        let com = sigma_commit(self.i, sig, &nw);
        let coms = net.all_gather(com.to_vec());
        let opened = net.all_gather(vec![sig, nw[0], nw[1]]);
        *self.wire.entry("mac_check").or_insert(0) += (2 * n * (n - 1)) as u64;
        let mut tot = 0u64;
        for (j, o) in opened.iter().enumerate() {
            if sigma_commit(j, o[0], &o[1..3]).to_vec() != coms[j] {
                return Err(format!("MAC check: party {j}'s opened sigma does not match its commitment"));
            }
            tot = field::add(tot, o[0]);
        }
        if tot != 0 {
            return Err("MAC check failed: an opened value is not the authenticated one".into());
        }
        Ok(())
    }
}

fn sigma_commit(i: usize, sig: u64, nonce: &[u64]) -> [u64; 4] {
    let mut h = Sha256::new();
    h.update(b"sigma");
    h.update((i as u64).to_le_bytes());
    h.update(sig.to_le_bytes());
    h.update(nonce[0].to_le_bytes());
    h.update(nonce[1].to_le_bytes());
    let d: [u8; 32] = h.finalize().into();
    crate::net::h2w(&d)
}
