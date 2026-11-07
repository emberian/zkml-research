//! The prover's coins. Every SECRET coin (PCS tails, proximity masks and leaf salts; cozk's row tails, masks, salts
//! and pointwise polynomial triples; the owner commitment's shares; the MAC check's sigma nonce) comes from the OS
//! CSPRNG (`Coins::Os`: getrandom, buffered). Seeded streams exist only under the TEST-ONLY deterministic hook
//! (cosnark.det_rng, `DL_DETERMINISTIC=<seed>`), and only in builds with the `test-det` cargo feature: without it a
//! `Det` carrying a seed is OFF, so a production build cannot be made to draw a secret coin from a seed.
//! Public coins are Fiat-Shamir challenges (crate::transcript) and the MAC check's coins (a hash of every opening);
//! they are public by design and are not drawn here.
use num_bigint_free::*;
use pycompat::PyRandom;

mod num_bigint_free {
    pub fn os_bytes(n: usize) -> Vec<u8> {
        let mut b = vec![0u8; n];
        getrandom::getrandom(&mut b).expect("OS randomness");
        b
    }
}

/// The deterministic hook's seed (None in every real run; ignored unless built with feature `test-det`).
#[derive(Clone, Debug, Default)]
pub struct Det(pub Option<String>);

impl Det {
    pub fn off() -> Self {
        Det(None)
    }
    #[cfg(feature = "test-det")]
    pub fn on(&self) -> bool {
        self.0.is_some()
    }
    #[cfg(not(feature = "test-det"))]
    pub fn on(&self) -> bool {
        false
    }
    /// cosnark.det_rng(*label): random.Random("dl-proof|<seed>|<parts>"). None unless the hook is on.
    pub fn rng(&self, parts: &[&str]) -> Option<PyRandom> {
        if !self.on() {
            return None;
        }
        let seed = self.0.as_ref()?;
        let mut s = format!("dl-proof|{seed}");
        for p in parts {
            s.push('|');
            s.push_str(p);
        }
        Some(PyRandom::from_str_seed(&s))
    }
    /// The secret stream for `parts`: the hook's seeded stream when on, else fresh OS coins.
    pub fn coins(&self, parts: &[&str]) -> Coins {
        match self.rng(parts) {
            Some(r) => Coins::Seeded(r),
            None => secret_coins(),
        }
    }
}

/// A source of secret coins.
pub enum Coins {
    /// TEST ONLY: a seeded CPython stream (bit-exact with the harness under the hook)
    Seeded(PyRandom),
    /// the OS CSPRNG
    Os(OsCoins),
}

pub struct OsCoins {
    buf: Vec<u8>,
    pos: usize,
}

impl OsCoins {
    fn word(&mut self) -> u64 {
        if self.pos + 8 > self.buf.len() {
            self.buf = os_bytes(1 << 16);
            self.pos = 0;
        }
        let w = u64::from_le_bytes(self.buf[self.pos..self.pos + 8].try_into().unwrap());
        self.pos += 8;
        w
    }
}

impl Coins {
    /// Uniform in [0, n): Python's randbelow when seeded; rejection sampling on OS words otherwise.
    pub fn randrange_u64(&mut self, n: u64) -> u64 {
        match self {
            Coins::Seeded(r) => r.randrange_u64(n),
            Coins::Os(o) => {
                assert!(n > 0);
                let bits = 64 - (n - 1).leading_zeros();
                let mask = if bits == 64 { u64::MAX } else { (1u64 << bits) - 1 };
                loop {
                    let x = o.word() & mask;
                    if x < n {
                        return x;
                    }
                }
            }
        }
    }
    pub fn is_seeded(&self) -> bool {
        matches!(self, Coins::Seeded(_))
    }
}

/// Fresh OS coins.
pub fn secret_coins() -> Coins {
    Coins::Os(OsCoins { buf: Vec::new(), pos: 0 })
}

/// random.Random(secrets.randbits(256)): MT19937 seeded from the OS. NOT a CSPRNG (its outputs determine its
/// state): never for secret coins. Kept only for the in-process harness's ideal dealer stream (shared by the three
/// simulated parties) and for callers not yet moved to `secret_coins`.
pub fn secret_rng() -> PyRandom {
    let b = os_bytes(32);
    let mut words = Vec::with_capacity(8);
    for c in b.chunks(4) {
        words.push(u32::from_le_bytes(c.try_into().unwrap()));
    }
    while words.len() > 1 && *words.last().unwrap() == 0 {
        words.pop();
    }
    PyRandom::from_key(&words)
}

pub fn secret_bytes(n: usize) -> Vec<u8> {
    os_bytes(n)
}

/// A leaf salt: secrets.token_hex(32) (OS bytes), or det.getrandbits(256).to_bytes(32, "little") under the hook.
pub fn salt(c: &mut Coins) -> [u8; 32] {
    match c {
        Coins::Seeded(r) => {
            let limbs = r.getrandbits_limbs(256);
            let mut out = [0u8; 32];
            for (k, l) in limbs.iter().enumerate() {
                out[8 * k..8 * k + 8].copy_from_slice(&l.to_le_bytes());
            }
            out
        }
        Coins::Os(_) => os_bytes(32).try_into().unwrap(),
    }
}
