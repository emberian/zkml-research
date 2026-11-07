//! The per-epoch key ceremony (keygen_ceremony.Ceremony, Custodian, run_ceremony): commit, reveal, seed, key
//! proofs, registry. Every method validates what it is handed; nothing trusts a custodian.

use crate::canon::Json;
use crate::gen::key_b;
use crate::proof::{prove_with, verify, ProveOpts, Witness};
use crate::statement::{public_a, BigPoly, KeyRegistry, Kind, Statement};
use crate::transcript::sha256;
use num_bigint::BigUint;
use pycompat::PyRandom;
use std::collections::BTreeMap;
use std::sync::Arc;

/// keygen_ceremony.H: sha256(canonical(list(parts))).hexdigest().
pub fn h(parts: Vec<Json>) -> String {
    pycompat::repr::hex(&sha256(&[&Json::List(parts).canonical()]))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CeremonyError(pub String);

impl std::fmt::Display for CeremonyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

fn err<T>(s: &str) -> Result<T, CeremonyError> {
    Err(CeremonyError(s.into()))
}

pub struct RegisteredKey {
    pub registry: Arc<KeyRegistry>,
    /// sha256 hex of the key proof
    pub proof_digest: String,
}

/// The ledger's view of one ceremony.
pub struct Ceremony {
    pub epoch: i64,
    pub n: usize,
    pub ring_n: usize,
    pub primes: Vec<u64>,
    pub t: u64,
    pub tcols: usize,
    pub commits: BTreeMap<usize, String>,
    pub reveals: BTreeMap<usize, (String, String)>,
    pub keys: BTreeMap<usize, RegisteredKey>,
    pub seed: Option<String>,
}

impl Ceremony {
    pub fn new(epoch: i64, n: usize, ring_n: usize, primes: &[u64], t: u64, tcols: usize) -> Ceremony {
        Ceremony {
            epoch,
            n,
            ring_n,
            primes: primes.to_vec(),
            t,
            tcols,
            commits: BTreeMap::new(),
            reveals: BTreeMap::new(),
            keys: BTreeMap::new(),
            seed: None,
        }
    }

    fn idx(&self, i: usize) -> Result<usize, CeremonyError> {
        if i >= self.n {
            return err("unknown custodian index");
        }
        Ok(i)
    }

    pub fn commit(&mut self, i: usize, c: &str) -> Result<(), CeremonyError> {
        self.idx(i)?;
        if self.seed.is_some() || self.commits.contains_key(&i) {
            return err("commit refused: out of phase, duplicate or unknown custodian");
        }
        if c.len() != 64 {
            return err("commit refused: shape");
        }
        self.commits.insert(i, c.to_string());
        Ok(())
    }

    pub fn reveal(&mut self, i: usize, r: &str, salt: &str) -> Result<(), CeremonyError> {
        self.idx(i)?;
        if self.commits.len() != self.n {
            return err("reveal refused: not every commitment is on the ledger yet");
        }
        if self.reveals.contains_key(&i) {
            return err("reveal refused: duplicate");
        }
        if commitment(self.epoch, i, r, salt) != self.commits[&i] {
            return Err(CeremonyError(format!("reveal refused: custodian {i} does not open its commitment (blamed)")));
        }
        self.reveals.insert(i, (r.into(), salt.into()));
        if self.reveals.len() == self.n {
            self.seed = Some(h(vec![
                Json::s("dl-keygen-seed"),
                Json::i(self.epoch),
                Json::List((0..self.n).map(|k| Json::s(&self.commits[&k])).collect()),
                Json::List((0..self.n).map(|k| Json::s(&self.reveals[&k].0)).collect()),
            ]));
        }
        Ok(())
    }

    pub fn transcript(&self) -> String {
        h(vec![
            Json::s("dl-keygen-transcript"),
            Json::i(self.epoch),
            self.seed.as_deref().map(Json::s).unwrap_or(Json::Null),
            Json::List((0..self.n).map(|k| Json::s(&self.commits[&k])).collect()),
        ])
    }

    pub fn key_seed(&self, j: usize) -> Result<String, CeremonyError> {
        self.idx(j)?;
        match &self.seed {
            None => err("no seed yet"),
            Some(s) => Ok(format!("{s}/{j}")),
        }
    }

    pub fn context(&self, j: usize) -> Json {
        Json::list(vec![Json::s("dl-keygen-key"), Json::i(self.epoch), Json::i(j as i64), Json::s(&self.transcript())])
    }

    /// Verify custodian j's key proof against the ceremony's a_j and context, and record the key.
    pub fn register(&mut self, j: usize, b: BigPoly, proof: &[u8]) -> Result<Arc<KeyRegistry>, CeremonyError> {
        self.idx(j)?;
        if self.seed.is_none() || self.keys.contains_key(&j) {
            return err("key refused: out of phase, duplicate or unknown custodian");
        }
        let reg = Arc::new(KeyRegistry::new(self.ring_n, &self.primes, self.t, &self.key_seed(j)?, &format!("custodian-{j}"), b));
        let st = Statement::new(reg.clone(), Kind::Key, vec![], vec![], self.context(j)).map_err(|e| CeremonyError(format!("key refused: {e}")))?;
        if let Err(why) = verify(&st, proof, self.tcols) {
            return Err(CeremonyError(format!("key refused: custodian {j}'s key proof: {why}")));
        }
        let digest = pycompat::repr::hex(&sha256(&[proof]));
        self.keys.insert(j, RegisteredKey { registry: reg.clone(), proof_digest: digest });
        Ok(reg)
    }

    pub fn registry(&self, j: usize) -> Option<Arc<KeyRegistry>> {
        self.keys.get(&j).map(|k| k.registry.clone())
    }
}

/// H("dl-keygen-commit", epoch, i, r, salt).
pub fn commitment(epoch: i64, i: usize, r: &str, salt: &str) -> String {
    h(vec![Json::s("dl-keygen-commit"), Json::i(epoch), Json::i(i as i64), Json::s(r), Json::s(salt)])
}

fn hex32_os() -> String {
    use std::io::Read;
    let mut b = [0u8; 32];
    std::fs::File::open("/dev/urandom").and_then(|mut f| f.read_exact(&mut b)).expect("/dev/urandom");
    pycompat::repr::hex(&b)
}

pub struct Custodian {
    pub i: usize,
    pub r: String,
    pub salt: String,
    det: Option<(String, PyRandom)>,
    pub s: Vec<i64>,
    pub e: Vec<i64>,
    pub b: Option<BigPoly>,
}

impl Custodian {
    /// OS coins.
    pub fn new(i: usize) -> Custodian {
        Custodian::with_seed(i, None)
    }

    /// TEST ONLY: keygen_ceremony.det_custodian_rng(i) under DL_DETERMINISTIC=<seed>.
    #[cfg(feature = "test-det")]
    pub fn new_det(i: usize, seed: &str) -> Custodian {
        Custodian::with_seed(i, Some(seed))
    }

    fn with_seed(i: usize, det_seed: Option<&str>) -> Custodian {
        let mut det = det_seed.map(|s| (s.to_string(), PyRandom::from_str_seed(&format!("dl-keygen|{s}|custodian|{i}"))));
        let (r, salt) = match det.as_mut() {
            None => (hex32_os(), hex32_os()),
            Some((_, rng)) => {
                let mut draw = || {
                    let v = rng.getrandbits_limbs(256);
                    let mut b = [0u8; 32];
                    for k in 0..4 {
                        b[k * 8..k * 8 + 8].copy_from_slice(&v[k].to_le_bytes());
                    }
                    pycompat::repr::hex(&b)
                };
                let r = draw();
                (r, draw())
            }
        };
        Custodian { i, r, salt, det, s: vec![], e: vec![], b: None }
    }

    pub fn commitment(&self, epoch: i64) -> String {
        commitment(epoch, self.i, &self.r, &self.salt)
    }

    /// Sample (s, e), set b = -(a_i s + e) with a_i = public_a(seed/i), and prove the key relation.
    pub fn make_key(&mut self, cer: &Ceremony) -> Result<(BigPoly, Vec<u8>), String> {
        let n = cer.ring_n;
        let (s, e): (Vec<i64>, Vec<i64>) = match self.det.as_mut() {
            Some((_, rng)) => {
                let s = (0..n).map(|_| rng.ternary()).collect();
                let e = (0..n).map(|_| rng.randint_i64(-8, 8)).collect();
                (s, e)
            }
            None => {
                let mut os = crate::rng::OsHiding::new();
                use crate::rng::Hiding;
                // uniform choices from OS bytes by rejection
                let mut small = |m: u32| loop {
                    let lim = 256 - 256 % m;
                    if let Some(x) = os.salt().into_iter().find(|&x| (x as u32) < lim) {
                        return (x as u32 % m) as i64;
                    }
                };
                let s = (0..n).map(|_| small(3) - 1).collect();
                let e = (0..n).map(|_| small(17) - 8).collect();
                (s, e)
            }
        };
        let seed = cer.key_seed(self.i).map_err(|e| e.0)?;
        let b = key_b(n, &cer.primes, &seed, &s, &e);
        let reg = Arc::new(KeyRegistry::new(n, &cer.primes, cer.t, &seed, &format!("custodian-{}", self.i), b.clone()));
        let st = Statement::new(reg, Kind::Key, vec![], vec![], cer.context(self.i))?;
        #[cfg(feature = "test-det")]
        let mut opts = ProveOpts { det_seed: self.det.as_ref().map(|d| d.0.clone()), ..Default::default() };
        #[cfg(not(feature = "test-det"))]
        let mut opts = ProveOpts::default();
        let proof = prove_with(&st, &Witness::Sk { s: s.clone(), e_pk: e.clone(), cts: vec![] }, cer.tcols, &mut opts)?;
        self.s = s;
        self.e = e;
        self.b = Some(b.clone());
        Ok((b, proof))
    }
}

/// keygen_ceremony.run_ceremony: commit, reveal, key proofs, register, for n custodians.
pub fn run_ceremony(epoch: i64, n: usize, ring_n: usize, primes: &[u64], t: u64, tcols: usize) -> Result<(Ceremony, Vec<Custodian>), String> {
    run_with(epoch, n, ring_n, primes, t, tcols, (0..n).map(Custodian::new).collect())
}

/// TEST ONLY: run_ceremony with every custodian on the DL_DETERMINISTIC=<seed> streams.
#[cfg(feature = "test-det")]
pub fn run_ceremony_det(epoch: i64, n: usize, ring_n: usize, primes: &[u64], t: u64, tcols: usize, seed: &str) -> Result<(Ceremony, Vec<Custodian>), String> {
    run_with(epoch, n, ring_n, primes, t, tcols, (0..n).map(|i| Custodian::new_det(i, seed)).collect())
}

fn run_with(epoch: i64, n: usize, ring_n: usize, primes: &[u64], t: u64, tcols: usize, mut cs: Vec<Custodian>) -> Result<(Ceremony, Vec<Custodian>), String> {
    let mut cer = Ceremony::new(epoch, n, ring_n, primes, t, tcols);
    for c in &cs {
        cer.commit(c.i, &c.commitment(epoch)).map_err(|e| e.0)?;
    }
    for c in &cs {
        cer.reveal(c.i, &c.r, &c.salt).map_err(|e| e.0)?;
    }
    for c in cs.iter_mut() {
        let (b, proof) = c.make_key(&cer)?;
        cer.register(c.i, b, &proof).map_err(|e| e.0)?;
    }
    Ok((cer, cs))
}

/// The joint key's a: public_a(seed/"joint").
pub fn joint_a(cer: &Ceremony) -> Option<Vec<BigUint>> {
    let q: BigUint = cer.primes.iter().map(|&p| BigUint::from(p)).product();
    cer.seed.as_ref().map(|s| public_a(&format!("{s}/joint"), cer.ring_n, &q))
}

