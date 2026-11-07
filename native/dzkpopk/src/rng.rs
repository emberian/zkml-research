//! Hiding randomness for the prover: the OS (default), or, for bit-exact tests only, the Python harness's
//! DL_DETERMINISTIC streams (zkpopk_ligero.det_rng / keygen_ceremony.det_custodian_rng).

use crate::field::{Fe, P};
use pycompat::PyRandom;
use std::io::Read;

pub trait Hiding {
    /// Uniform in [0, P) (Python: rng.randrange(P)).
    fn fe(&mut self) -> Fe;
    /// 32 salt bytes (Python: secrets.token_bytes(32), or det.getrandbits(256).to_bytes(32, "little")).
    fn salt(&mut self) -> [u8; 32];
}

/// /dev/urandom, buffered.
pub struct OsHiding {
    f: std::io::BufReader<std::fs::File>,
}

impl OsHiding {
    pub fn new() -> OsHiding {
        OsHiding { f: std::io::BufReader::with_capacity(1 << 16, std::fs::File::open("/dev/urandom").expect("/dev/urandom")) }
    }
    fn bytes32(&mut self) -> [u8; 32] {
        let mut b = [0u8; 32];
        self.f.read_exact(&mut b).expect("/dev/urandom read");
        b
    }
}

impl Default for OsHiding {
    fn default() -> Self {
        Self::new()
    }
}

impl Hiding for OsHiding {
    fn fe(&mut self) -> Fe {
        loop {
            let b = self.bytes32();
            let mut l = [0u64; 4];
            for i in 0..4 {
                l[i] = u64::from_le_bytes(b[i * 8..i * 8 + 8].try_into().unwrap());
            }
            l[3] &= (1u64 << 63) - 1; // 255 bits, rejection below P
            if lt_p(&l) {
                return Fe::from_canonical(l);
            }
        }
    }
    fn salt(&mut self) -> [u8; 32] {
        self.bytes32()
    }
}

fn lt_p(l: &[u64; 4]) -> bool {
    for i in (0..4).rev() {
        if l[i] != P[i] {
            return l[i] < P[i];
        }
    }
    false
}

/// TEST ONLY: random.Random(label) as the harness's DL_DETERMINISTIC hook seeds it.
pub struct DetHiding(pub PyRandom);

impl DetHiding {
    /// zkpopk_ligero.det_rng(label, st): random.Random(f"dl-zkpopk|{seed}|{label}|{digest hex}").
    pub fn for_statement(seed: &str, label: &str, digest: &[u8; 32]) -> DetHiding {
        DetHiding(PyRandom::from_str_seed(&format!("dl-zkpopk|{seed}|{label}|{}", pycompat::repr::hex(digest))))
    }
}

impl Hiding for DetHiding {
    fn fe(&mut self) -> Fe {
        let v = self.0.randbelow_limbs(&P);
        let mut l = [0u64; 4];
        l[..v.len()].copy_from_slice(&v);
        Fe::from_canonical(l)
    }
    fn salt(&mut self) -> [u8; 32] {
        let v = self.0.getrandbits_limbs(256);
        let mut b = [0u8; 32];
        for i in 0..4 {
            b[i * 8..i * 8 + 8].copy_from_slice(&v[i].to_le_bytes());
        }
        b
    }
}
