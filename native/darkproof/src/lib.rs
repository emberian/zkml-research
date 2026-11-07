//! The dark-learning MPC fork's collaborative ZK proof and its untrusted-input verifier, natively.
//! Reference: research/dark_learning_2026_11_06/ (cozk, cosnark, cosnark_zk, cosnark_gates, cosnark_gates_zk,
//! proofwire, owner_sig). Every proof byte equals the harness's for the same seed (`rng::Det`).
pub mod ext;
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
    /// the PCS row split (proofwire SPLIT): square mr = m / 2, or balanced (pcs::row_split)
    pub split: Split,
    /// every tree's openings as one multiproof (proofwire MERKLE "multi"), or one path per column ("paths")
    pub multiproof: bool,
    /// the challenges' field F_{p^ext} (proofwire EXT; cosnark_ext): 1, or 2 for the "-x2" profiles
    pub ext: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Split {
    Square,
    Balanced,
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
            k_l: 512,
            t_hide: 309,
            t_open: 309,
            owner_h: 12,
            he: (16384, 4, 175),
            domain: Domain::Coset,
            split: Split::Balanced,
            multiproof: true,
            ext: 1,
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
            k_l: 512,
            t_hide: 97,
            t_open: 97,
            owner_h: 12,
            he: (8192, 3, 118),
            domain: Domain::Coset,
            split: Split::Balanced,
            multiproof: true,
            ext: 1,
        }
    }
    pub fn by_name(s: &str) -> Option<Self> {
        match s {
            "ledger" => Some(Self::ledger()),
            "demo" => Some(Self::demo()),
            // gen 5's evaluation points (the before/after comparison and the vectors made before the coset domain)
            // before bundle cut A: the square row split and K_L = 64 (every bundle made before 2026-11-07's cut)
            "ledger-sq" => Some(Profile { name: "ledger-sq", k_l: 64, split: Split::Square, multiproof: false, ..Self::ledger() }),
            "demo-sq" => Some(Profile { name: "demo-sq", k_l: 64, split: Split::Square, multiproof: false, ..Self::demo() }),
            "ledger-int" => Some(Profile { name: "ledger-int", domain: Domain::Int, k_l: 64, split: Split::Square, multiproof: false, ..Self::ledger() }),
            "demo-int" => Some(Profile { name: "demo-int", domain: Domain::Int, k_l: 64, split: Split::Square, multiproof: false, ..Self::demo() }),
            // F_{p^2} challenges: two lives x two proximity masks (one per component)
            "ledger-x2" => Some(Profile { name: "ledger-x2", nmask: 4, ext: 2, ..Self::ledger() }),
            "demo-x2" => Some(Profile { name: "demo-x2", nmask: 4, ext: 2, ..Self::demo() }),
            _ => None,
        }
    }
    pub fn ligero(&self) -> ligero::LigParams {
        let mut lp = ligero::LigParams::new(self.k_l, self.t_hide, self.t_open, self.blow);
        lp.ext = self.ext;
        lp
    }
}

/// The process's resident memory from /proc/self/status (VmRSS now, VmHWM peak), in GB; NaN off Linux.
pub fn rss_gb(key: &str) -> f64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| s.lines().find(|l| l.starts_with(key)).and_then(|l| l.split_whitespace().nth(1)?.parse::<f64>().ok()))
        .map(|kb| kb / 1e6)
        .unwrap_or(f64::NAN)
}

/// Phase timing (and process memory) for custodian 0 when DP_TRACE is set (stderr).
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
            eprintln!("  [{}] {what}: {:.2}s (process RSS {:.2} GB, peak {:.2} GB)", self.label, self.t.elapsed().as_secs_f64(), rss_gb("VmRSS"), rss_gb("VmHWM"));
            self.t = std::time::Instant::now();
        }
    }
}
