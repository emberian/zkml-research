//! The ideal dealer (spdz.Dealer) and the step's preprocessing schedule, drawn in exactly the harness's order, plus
//! the owner's input broadcasts. Each party gets a Tape: its alpha_i and an ordered list of (tag, share, mac share).
use crate::arith::*;
use pycompat::PyRandom;
use std::io::{Read, Write};

pub const KAPPA: u32 = 40;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum Tag {
    In = 1,
    Ta,
    Tb,
    Tc,
    Tr,
    Trb,
    Trh,
    Lp,
    Ar,
    /// proof-only preprocessing: the K + KAPPA - s bits of each truncation's rhi (cosnark_gates.RecEngine), so the
    /// middle can range-check rhi
    Trhb,
}

#[derive(Default, Clone)]
pub struct Tape {
    pub alpha_i: u64,
    pub tags: Vec<u8>,
    pub sh: Vec<u64>,
    pub mac: Vec<u64>,
}

impl Tape {
    pub fn len(&self) -> usize {
        self.tags.len()
    }

    pub fn is_empty(&self) -> bool {
        self.tags.is_empty()
    }

    pub fn write_to(&self, w: &mut impl Write) -> std::io::Result<()> {
        w.write_all(b"DLTAPE01")?;
        w.write_all(&self.alpha_i.to_le_bytes())?;
        w.write_all(&(self.len() as u64).to_le_bytes())?;
        w.write_all(&self.tags)?;
        w.write_all(&crate::net::u64s_to_bytes(&self.sh))?;
        w.write_all(&crate::net::u64s_to_bytes(&self.mac))
    }

    pub fn read_from(r: &mut impl Read) -> std::io::Result<Tape> {
        let mut hdr = [0u8; 24];
        r.read_exact(&mut hdr)?;
        assert_eq!(&hdr[..8], b"DLTAPE01", "not a tape");
        let alpha_i = u64::from_le_bytes(hdr[8..16].try_into().unwrap());
        let n = u64::from_le_bytes(hdr[16..24].try_into().unwrap()) as usize;
        let mut tags = vec![0u8; n];
        r.read_exact(&mut tags)?;
        let mut b = vec![0u8; 8 * n];
        r.read_exact(&mut b)?;
        let sh = crate::net::bytes_to_u64s(&b);
        r.read_exact(&mut b)?;
        let mac = crate::net::bytes_to_u64s(&b);
        Ok(Tape { alpha_i, tags, sh, mac })
    }
}

pub struct Dealer {
    pub p: u64,
    pub n: usize,
    pub rng: PyRandom,
    /// RecEngine's proof-preprocessing stream (random.Random(1)); None: no proof atoms on the tape
    pub proof_rng: Option<PyRandom>,
    pub alpha_sh: Vec<u64>,
    pub alpha: u64,
    pub tapes: Vec<Tape>,
}

impl Dealer {
    pub fn new(p: u64, n: usize, seed: u64) -> Self {
        let mut rng = PyRandom::from_u64(seed);
        let alpha_sh: Vec<u64> = (0..n).map(|_| rng.randrange_u64(p)).collect();
        let alpha = alpha_sh.iter().fold(0, |a, &x| addmod(a, x, p));
        let tapes = alpha_sh.iter().map(|&a| Tape { alpha_i: a, ..Default::default() }).collect();
        Dealer { p, n, rng, proof_rng: None, alpha_sh, alpha, tapes }
    }

    /// spdz.Dealer.auth(v, tag), v in [0, p).
    pub fn auth(&mut self, v: u64, tag: Tag) {
        let (p, n) = (self.p, self.n);
        let mut xs: Vec<u64> = (0..n - 1).map(|_| self.rng.randrange_u64(p)).collect();
        let sx = xs.iter().fold(0, |a, &x| addmod(a, x, p));
        xs.push(submod(v, sx, p));
        let mut ms: Vec<u64> = (0..n - 1).map(|_| self.rng.randrange_u64(p)).collect();
        let sm = ms.iter().fold(0, |a, &x| addmod(a, x, p));
        ms.push(submod(mulmod(self.alpha, v, p), sm, p));
        for i in 0..n {
            let t = &mut self.tapes[i];
            t.tags.push(tag as u8);
            t.sh.push(xs[i]);
            t.mac.push(ms[i]);
        }
    }

    pub fn mul(&mut self) {
        let p = self.p;
        let a = self.rng.randrange_u64(p);
        let b = self.rng.randrange_u64(p);
        self.auth(a, Tag::Ta);
        self.auth(b, Tag::Tb);
        self.auth(mulmod(a, b, p), Tag::Tc);
    }

    pub fn trunc(&mut self, s: u32, k: u32) {
        let r = self.rng.randrange_u64(1u64 << (k + KAPPA));
        self.auth(r % self.p, Tag::Tr);
        for i in 0..s {
            self.auth((r >> i) & 1, Tag::Trb);
        }
        self.auth(r >> s, Tag::Trh);
        if let Some(mut pr) = self.proof_rng.take() {
            // RecEngine._share with the dealer's alpha, from its own stream
            let (p, n) = (self.p, self.n);
            for j in 0..(k + KAPPA - s) {
                let v = (r >> s >> j) & 1;
                let mut xs: Vec<u64> = (0..n - 1).map(|_| pr.randrange_u64(p)).collect();
                let sx = xs.iter().fold(0, |a, &x| addmod(a, x, p));
                xs.push(submod(v, sx, p));
                let mut ms: Vec<u64> = (0..n - 1).map(|_| pr.randrange_u64(p)).collect();
                let sm = ms.iter().fold(0, |a, &x| addmod(a, x, p));
                ms.push(submod(mulmod(self.alpha, v, p), sm, p));
                for i in 0..n {
                    let t = &mut self.tapes[i];
                    t.tags.push(Tag::Trhb as u8);
                    t.sh.push(xs[i]);
                    t.mac.push(ms[i]);
                }
            }
            self.proof_rng = Some(pr);
        }
        for _ in 0..2 * (s - 1) {
            self.mul();
        }
    }

    pub fn lookup(&mut self, deg: usize) {
        let p = self.p;
        let r = self.rng.randrange_u64(p);
        let mut pw = 1u64;
        for _ in 0..deg {
            pw = mulmod(pw, r, p);
            self.auth(pw, Tag::Lp);
        }
    }

    pub fn auth_plain(&mut self) {
        let r = self.rng.randrange_u64(self.p);
        self.auth(r, Tag::Ar);
    }
}

/// Dealer + owner for one step (mpc_fork.run_step with HE matvec and HE outer): returns each party's tape and the
/// owner's public input broadcasts c = v - r, in the harness's order.
pub fn deal_step(p: u64, d: usize, dealer_seed: u64, owner_seed: u64, inputs: &[u64]) -> (Vec<Tape>, Vec<u64>) {
    deal_step_opts(p, d, dealer_seed, owner_seed, inputs, false)
}

/// proof_atoms: also deal the collaborative proof's truncation range bits (Tag::Trhb after each Trh), from
/// random.Random(1) as cosnark_gates.RecEngine does.
pub fn deal_step_opts(p: u64, d: usize, dealer_seed: u64, owner_seed: u64, inputs: &[u64], proof_atoms: bool) -> (Vec<Tape>, Vec<u64>) {
    let (c, dl) = deal_step_dealer(p, d, dealer_seed, owner_seed, inputs, proof_atoms);
    (dl.tapes, c)
}

/// deal_step_opts, returning the owner's broadcasts and the dealer itself (its `tapes`; continue its stream with
/// deal_proof_section before taking them).
pub fn deal_step_dealer(p: u64, d: usize, dealer_seed: u64, owner_seed: u64, inputs: &[u64], proof_atoms: bool) -> (Vec<u64>, Dealer) {
    deal_step_dealer_prog(p, d, dealer_seed, owner_seed, inputs, proof_atoms, &crate::step::Program::HARNESS)
}

/// deal_step_dealer for a step program (its truncation shifts and bounds; step::Program::truncs).
pub fn deal_step_dealer_prog(p: u64, d: usize, dealer_seed: u64, owner_seed: u64, inputs: &[u64], proof_atoms: bool, pg: &crate::step::Program) -> (Vec<u64>, Dealer) {
    let mut dl = Dealer::new(p, 3, dealer_seed);
    if proof_atoms {
        dl.proof_rng = Some(PyRandom::from_u64(1));
    }
    let mut owner = PyRandom::from_u64(owner_seed);
    assert_eq!(inputs.len(), 2 * d * d + 2 * d);
    let cs = deal_one_step(&mut dl, &mut owner, d, inputs, pg);
    (cs, dl)
}

/// One step on a continuing dealer and owner stream: the owner's masks for `inputs` (2d^2 + 2d at genesis, 2d for a
/// carried step: x then y), then the step's preprocessing in run_step_shares' order. Returns the owner's broadcasts.
pub fn deal_one_step(dl: &mut Dealer, owner: &mut PyRandom, d: usize, inputs: &[u64], pg: &crate::step::Program) -> Vec<u64> {
    let p = dl.p;
    let [(sa, ka), (sb, kb), (sc, kc), (sd, kd)] = pg.truncs();
    let mut cs = Vec::with_capacity(inputs.len());
    for &v in inputs {
        let r = owner.randrange_u64(p);
        dl.auth(r, Tag::In);
        cs.push(submod(v, r, p));
    }
    let matvec = |dl: &mut Dealer| {
        for _ in 0..d {
            dl.auth_plain();
        }
        for _ in 0..d {
            dl.mul();
        }
    };
    matvec(dl); // z1 = W1 x
    for _ in 0..d {
        dl.trunc(sa, ka);
    }
    for _ in 0..d {
        dl.lookup(255);
    }
    matvec(dl); // z2 = W2 h
    for _ in 0..d {
        dl.trunc(sb, kb);
    }
    for _ in 0..d {
        dl.trunc(sc, kc);
    }
    matvec(dl); // b = W2^T d2
    for _ in 0..d {
        dl.mul();
    }
    for _ in 0..d {
        dl.trunc(sd, kd);
    }
    dl.mul(); // outer check (d2 x h)
    dl.mul(); // outer check (d1 x x)
    cs
}

/// The test dealer for a run of 1 + later_inputs.len() steps on one continuing dealer stream (one alpha) and one owner
/// stream: step 0 deals the genesis inputs (W1, W2, x, y), every later step only its own x, y (2d). Each party's tape
/// holds the steps back to back. Replaced by the prep lane's MASCOT tapes in deployment.
#[allow(clippy::too_many_arguments)]
pub fn deal_steps_prog(p: u64, d: usize, dealer_seed: u64, owner_seed: u64, genesis_inputs: &[u64], later_inputs: &[Vec<u64>], proof_atoms: bool, pg: &crate::step::Program) -> (Vec<Tape>, Vec<Vec<u64>>) {
    let mut dl = Dealer::new(p, 3, dealer_seed);
    if proof_atoms {
        dl.proof_rng = Some(PyRandom::from_u64(1));
    }
    let mut owner = PyRandom::from_u64(owner_seed);
    assert_eq!(genesis_inputs.len(), 2 * d * d + 2 * d);
    let c0 = deal_one_step(&mut dl, &mut owner, d, genesis_inputs, pg);
    let mut out = vec![c0];
    for xs in later_inputs {
        assert_eq!(xs.len(), 2 * d, "a carried step inputs x and y only");
        out.push(deal_one_step(&mut dl, &mut owner, d, xs, pg));
    }
    (dl.tapes, out)
}

/// The collaborative proof's Beaver triples, dealt after the step from the same dealer stream (as the harness's prover
/// continues the step dealer): `count` = darkproof::spine::beaver_count(d) + darkproof::middle::beaver_count(n_had).
pub fn deal_proof_section(dl: &mut Dealer, count: usize) {
    for _ in 0..count {
        dl.mul();
    }
}
