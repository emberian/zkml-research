//! Secret randomness: random.Random(secrets.randbits(256)) in real runs, cosnark.det_rng streams under the TEST-ONLY
//! deterministic hook (`DL_DETERMINISTIC=<seed>`, passed explicitly as `Det`).
use num_bigint_free::*;
use pycompat::PyRandom;

mod num_bigint_free {
    pub fn os_bytes(n: usize) -> Vec<u8> {
        let mut b = vec![0u8; n];
        getrandom::getrandom(&mut b).expect("OS randomness");
        b
    }
}

/// The deterministic hook's seed (None in every real run).
#[derive(Clone, Debug, Default)]
pub struct Det(pub Option<String>);

impl Det {
    pub fn on(&self) -> bool {
        self.0.is_some()
    }
    /// cosnark.det_rng(*label): random.Random("dl-proof|<seed>|<parts>").
    pub fn rng(&self, parts: &[&str]) -> Option<PyRandom> {
        let seed = self.0.as_ref()?;
        let mut s = format!("dl-proof|{seed}");
        for p in parts {
            s.push('|');
            s.push_str(p);
        }
        Some(PyRandom::from_str_seed(&s))
    }
}

/// random.Random(secrets.randbits(256)).
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

/// A leaf salt: secrets.token_hex(32), or det.getrandbits(256).to_bytes(32, "little") under the hook.
pub fn salt(det: Option<&mut PyRandom>) -> [u8; 32] {
    match det {
        Some(r) => {
            let limbs = r.getrandbits_limbs(256);
            let mut out = [0u8; 32];
            for (k, l) in limbs.iter().enumerate() {
                out[8 * k..8 * k + 8].copy_from_slice(&l.to_le_bytes());
            }
            out
        }
        None => os_bytes(32).try_into().unwrap(),
    }
}
