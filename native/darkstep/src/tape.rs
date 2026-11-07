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
        Dealer { p, n, rng, alpha_sh, alpha, tapes }
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
    let mut dl = Dealer::new(p, 3, dealer_seed);
    let mut owner = PyRandom::from_u64(owner_seed);
    assert_eq!(inputs.len(), 2 * d * d + 2 * d);
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
    matvec(&mut dl); // z1 = W1 x
    for _ in 0..d {
        dl.trunc(5, 13);
    }
    for _ in 0..d {
        dl.lookup(255);
    }
    matvec(&mut dl); // z2 = W2 h
    for _ in 0..d {
        dl.trunc(5, 13);
    }
    for _ in 0..d {
        dl.trunc(4, 8);
    }
    matvec(&mut dl); // b = W2^T d2
    for _ in 0..d {
        dl.mul();
    }
    for _ in 0..d {
        dl.trunc(8, 13);
    }
    dl.mul(); // outer check (d2 x h)
    dl.mul(); // outer check (d1 x x)
    (dl.tapes, cs)
}
