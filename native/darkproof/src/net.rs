//! The custodians' exchanges. One primitive: every party contributes a vector of field elements (or hash words) and
//! receives every party's contribution, indexed by party (its own included). Beaver openings, Ligero share
//! openings, root broadcasts and the proof material all go through it, so a socket transport (darkstep's) only has
//! to implement `all_gather`.
use std::sync::mpsc::{channel, Receiver, Sender};

pub trait Net: Send {
    fn me(&self) -> usize;
    fn n(&self) -> usize;
    fn all_gather(&mut self, mine: Vec<u64>) -> Vec<Vec<u64>>;
    /// Elements this party has sent so far (all categories).
    fn sent(&self) -> u64;
}

/// In-process transport: one thread per party, an mpsc channel per ordered pair.
pub struct MemNet {
    me: usize,
    n: usize,
    tx: Vec<Option<Sender<Vec<u64>>>>,
    rx: Vec<Option<Receiver<Vec<u64>>>>,
    sent: u64,
}

pub fn mem_mesh(n: usize) -> Vec<MemNet> {
    let mut txs: Vec<Vec<Option<Sender<Vec<u64>>>>> = (0..n).map(|_| (0..n).map(|_| None).collect()).collect();
    let mut rxs: Vec<Vec<Option<Receiver<Vec<u64>>>>> = (0..n).map(|_| (0..n).map(|_| None).collect()).collect();
    for a in 0..n {
        for b in 0..n {
            if a != b {
                let (t, r) = channel();
                txs[a][b] = Some(t); // a sends to b
                rxs[b][a] = Some(r); // b receives from a
            }
        }
    }
    let mut out = Vec::new();
    for (me, (tx, rx)) in txs.into_iter().zip(rxs).enumerate() {
        out.push(MemNet { me, n, tx, rx, sent: 0 });
    }
    out
}

impl Net for MemNet {
    fn me(&self) -> usize {
        self.me
    }
    fn n(&self) -> usize {
        self.n
    }
    fn all_gather(&mut self, mine: Vec<u64>) -> Vec<Vec<u64>> {
        for b in 0..self.n {
            if b != self.me {
                self.sent += mine.len() as u64;
                self.tx[b].as_ref().unwrap().send(mine.clone()).expect("peer gone");
            }
        }
        let mut out = Vec::with_capacity(self.n);
        for a in 0..self.n {
            if a == self.me {
                out.push(mine.clone());
            } else {
                out.push(self.rx[a].as_ref().unwrap().recv().expect("peer gone"));
            }
        }
        out
    }
    fn sent(&self) -> u64 {
        self.sent
    }
}

/// Hashes travel as four u64 words.
pub fn h2w(h: &[u8; 32]) -> [u64; 4] {
    let mut o = [0u64; 4];
    for k in 0..4 {
        o[k] = u64::from_le_bytes(h[8 * k..8 * k + 8].try_into().unwrap());
    }
    o
}

pub fn w2h(w: &[u64]) -> [u8; 32] {
    let mut o = [0u8; 32];
    for k in 0..4 {
        o[8 * k..8 * k + 8].copy_from_slice(&w[k].to_le_bytes());
    }
    o
}

/// Gather one hash from every party.
pub fn gather_hash(net: &mut dyn Net, h: &[u8; 32]) -> Vec<[u8; 32]> {
    net.all_gather(h2w(h).to_vec()).iter().map(|w| w2h(w)).collect()
}

/// Gather a list of hashes from every party (same length everywhere).
pub fn gather_hashes(net: &mut dyn Net, hs: &[[u8; 32]]) -> Vec<Vec<[u8; 32]>> {
    let mine: Vec<u64> = hs.iter().flat_map(|h| h2w(h)).collect();
    net.all_gather(mine).iter().map(|w| w.chunks(4).map(w2h).collect()).collect()
}
