//! The dark-learning MPC fork's collaborative ZK proof and its untrusted-input verifier, natively.
//! Reference: research/dark_learning_2026_11_06/ (cozk, cosnark, cosnark_zk, cosnark_gates, cosnark_gates_zk,
//! proofwire, owner_sig). Every proof byte equals the harness's for the same seed (`rng::Det`).
pub mod field;
pub mod h;
pub mod handover;
pub mod ledger;
pub mod ligero;
pub mod live;
pub mod middle;
pub mod net;
pub mod owner;
pub mod pcs;
pub mod poly;
pub mod rng;
pub mod run;
pub mod spdz;
pub mod spine;
pub mod step;
pub mod transcript;
pub mod wire;
pub mod witness;

/// The binding context (model id, epoch, step).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ctx {
    pub model: String,
    pub epoch: u64,
    pub step: u64,
}

impl Ctx {
    pub fn new(model: &str, epoch: u64, step: u64) -> Self {
        Ctx { model: model.into(), epoch, step }
    }
    /// str(context) / repr(context).
    pub fn repr(&self) -> String {
        format!("({}, {}, {})", h::py_str_repr(&self.model), self.epoch, self.step)
    }
}

/// proofwire.PROFILES: the verifier's pinned parameters.
#[derive(Clone, Debug, PartialEq)]
pub struct Profile {
    pub name: &'static str,
    pub t_cols: usize,
    pub hide: usize,
    pub nmask: usize,
    pub lives: usize,
    pub blow: usize,
    pub k_l: usize,
    pub t_hide: usize,
    pub t_open: usize,
    pub owner_h: usize,
    /// HE parameters that travel with the profile (N, L, F_BITS)
    pub he: (u64, u64, u64),
    /// the PCS codeword's evaluation points (proofwire DOMAIN): cosets of a 2-power subgroup (NTT), or gen 5's
    /// x_j = j + 1
    pub domain: Domain,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Domain {
    Int,
    Coset,
}

impl Profile {
    pub fn ledger() -> Self {
        Profile {
            name: "ledger",
            t_cols: 309,
            hide: 618,
            nmask: 2,
            lives: 2,
            blow: 4,
            k_l: 64,
            t_hide: 309,
            t_open: 309,
            owner_h: 12,
            he: (16384, 4, 175),
            domain: Domain::Coset,
        }
    }
    pub fn demo() -> Self {
        Profile {
            name: "demo",
            t_cols: 97,
            hide: 194,
            nmask: 2,
            lives: 2,
            blow: 4,
            k_l: 64,
            t_hide: 97,
            t_open: 97,
            owner_h: 12,
            he: (8192, 3, 118),
            domain: Domain::Coset,
        }
    }
    pub fn by_name(s: &str) -> Option<Self> {
        match s {
            "ledger" => Some(Self::ledger()),
            "demo" => Some(Self::demo()),
            // gen 5's evaluation points (the before/after comparison and the vectors made before the coset domain)
            "ledger-int" => Some(Profile { name: "ledger-int", domain: Domain::Int, ..Self::ledger() }),
            "demo-int" => Some(Profile { name: "demo-int", domain: Domain::Int, ..Self::demo() }),
            _ => None,
        }
    }
    pub fn ligero(&self) -> ligero::LigParams {
        ligero::LigParams::new(self.k_l, self.t_hide, self.t_open, self.blow)
    }
}

/// Phase timing for custodian 0 when DP_TRACE is set (stderr).
pub struct Trace {
    on: bool,
    t: std::time::Instant,
    label: &'static str,
}
impl Trace {
    pub fn new(label: &'static str, party: usize) -> Self {
        Trace { on: party == 0 && std::env::var_os("DP_TRACE").is_some(), t: std::time::Instant::now(), label }
    }
    pub fn lap(&mut self, what: &str) {
        if self.on {
            eprintln!("  [{}] {what}: {:.2}s", self.label, self.t.elapsed().as_secs_f64());
            self.t = std::time::Instant::now();
        }
    }
}
