//! The order in which one step of the MPC fork (both HE helpers: `mpc_fork.run_step` with
//! `he_matvec.HEMatvec` and `he_outer.HEOuter`) consumes preprocessing, and the counts per kind.
//! With both helpers there are no matrix triples ("mA", "mb", "mC") and no outer tuples ("ou", "ow", "ouw").

pub const KAPPA: u32 = 40;
pub const DEG: usize = 255;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Tag {
    In = 0,
    Ta = 1,
    Tb = 2,
    Tc = 3,
    Tr = 4,
    Trb = 5,
    Trh = 6,
    Lp = 7,
    Ar = 8,
    /// proof-only: the K + KAPPA - s bits of each truncation's r >> s (darkproof's range check on rhi)
    Trhb = 9,
}

impl Tag {
    pub fn name(self) -> &'static str {
        ["in", "ta", "tb", "tc", "tr", "trb", "trh", "lp", "ar", "trhb"][self as usize]
    }
    pub fn from_code(c: u8) -> Option<Tag> {
        use Tag::*;
        [In, Ta, Tb, Tc, Tr, Trb, Trh, Lp, Ar, Trhb].get(c as usize).copied()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Inputs {
    /// `run_step` as the harness runs it: W1, W2, x, y are all input (2 d^2 + 2 d masks).
    Harness = 0,
    /// Steady state (the count model's row): the weights stay shared, only x and y are input (2 d).
    Steady = 1,
}

#[derive(Clone, Copy, Debug)]
pub struct StepParams {
    pub d: usize,
    pub inputs: Inputs,
    /// (s, K) for the four truncations in program order: u1, e, d2, d1.
    pub trunc: [(u32, u32); 4],
    /// emit Trhb after each Trh (darkstep `proof_atoms`; the online step skips them, the proof reads them)
    pub proof_atoms: bool,
    /// Beaver triples dealt after the step for the collaborative proof (darkstep `deal_proof_section`)
    pub proof_triples: usize,
    /// What this tape is for: a training step, the mind's release, or a new committee's handover tape.
    pub phase: Phase,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    Step,
    /// the mind's release (darkproof::run::deal_release), with the step's (s1, k1) = trunc[0]; proof_triples is
    /// the release's proof section (darkproof::run::release_section)
    Release(Release),
    /// a new seat's handover tape: n auth_plain entries under its new MAC key (darkhand::side::new_side
    /// re-authenticates the reshared W1, W2 on them: 2 d^2 + 16)
    Handover(usize),
}

/// The release's shape: M public test examples, ncls classes, comparisons as truncations (kc, kc).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Release {
    pub m: usize,
    pub ncls: usize,
    pub kc: u32,
}

impl StepParams {
    /// The harness's d = 64 step (mpc_fork.run_step hard-codes K = 13, 13, 8, 13 with S1, S2, S3 = 5, 4, 8).
    pub fn harness_d64() -> Self {
        StepParams { d: 64, inputs: Inputs::Harness, trunc: [(5, 13), (5, 13), (4, 8), (8, 13)], proof_atoms: false, proof_triples: 0, phase: Phase::Step }
    }
    /// `step_counts.params(d)`: S1 = max(5, ceil(log2(49 d / 128))), K1 = S1 + 8, S2 = 4, K2 = 8, S3 = S1 + 3, K3 = S1 + 8.
    pub fn at(d: usize, inputs: Inputs) -> Self {
        let x = 49.0 * d as f64 / 128.0;
        let s1 = (x.log2().ceil() as i64).max(5) as u32;
        StepParams { d, inputs, trunc: [(s1, s1 + 8), (s1, s1 + 8), (4, 8), (s1 + 3, s1 + 8)], proof_atoms: false, proof_triples: 0, phase: Phase::Step }
    }
    /// The step with the collaborative proof's preprocessing: Trhb atoms and the proof section's triples,
    /// darkproof::spine::beaver_count(d) + darkproof::middle::beaver_count(n_had).
    pub fn with_proof(mut self) -> Self {
        self.proof_atoms = true;
        self.proof_triples = spine_beaver_count(self.d) + middle_beaver_count(self.n_had());
        self
    }
    /// darkproof's Hadamard records for one step (darkproof/src/step.rs): one per online Beaver product of the
    /// recorded step (the borrow chains and b * g1; the HE Freivalds and outer checks are not recorded), one per
    /// truncation bit (s low bits and K + KAPPA - s high bits), and 254 per lookup power chain.
    /// Checked against cosnark_gates results: 1,992 / 7,968 / 31,872 at d = 4, 16, 64 and 2,260,992 at d = 4096.
    pub fn n_had(&self) -> usize {
        let per: usize = self.trunc.iter().map(|&(s, k)| 2 * (s as usize - 1) + (k + KAPPA) as usize).sum();
        self.d * (per + 1 + (DEG - 1))
    }
    /// The release with its proof atoms and its proof section of `proof_triples` (the proof lane's count).
    pub fn release(mut self, r: Release, proof_triples: usize) -> Self {
        self.phase = Phase::Release(r);
        self.proof_atoms = true;
        self.proof_triples = proof_triples;
        self
    }
    /// A new seat's handover tape of n auth_plain entries.
    pub fn handover(mut self, n: usize) -> Self {
        self.phase = Phase::Handover(n);
        self.proof_atoms = false;
        self.proof_triples = 0;
        self
    }
    pub fn n_inputs(&self) -> usize {
        if self.phase != Phase::Step {
            return 0;
        }
        match self.inputs {
            Inputs::Harness => 2 * self.d * self.d + 2 * self.d,
            Inputs::Steady => 2 * self.d,
        }
    }
}

/// One consumption event, in program order. Each expands to a fixed tag sequence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Event {
    Input,
    AuthPlain,
    Mul,
    /// (s, K)
    Trunc(u32, u32),
    Lookup,
}

pub fn events(sp: &StepParams) -> Vec<Event> {
    let d = sp.d;
    let mut ev = Vec::new();
    let rep = |ev: &mut Vec<Event>, e: Event, k: usize| ev.extend(std::iter::repeat(e).take(k));
    let tr = |t: usize| Event::Trunc(sp.trunc[t].0, sp.trunc[t].1);
    if let Phase::Handover(n) = sp.phase {
        rep(&mut ev, Event::AuthPlain, n);
        return ev;
    }
    if let Phase::Release(r) = sp.phase {
        // darkproof::run::deal_release (cosnark_release's order), then its proof section
        let (m, c) = (r.m, r.ncls);
        rep(&mut ev, tr(0), d * m); // u1 = z1 >> s1 per example
        rep(&mut ev, Event::Lookup, d * m); // h
        rep(&mut ev, Event::Mul, c * m * d); // o = W2 h
        rep(&mut ev, tr(0), c * m); // o >> s1
        rep(&mut ev, Event::Trunc(r.kc, r.kc), m * (c - 1)); // the comparisons against the label's score
        rep(&mut ev, Event::Mul, m * (c - 2)); // their AND chain
        rep(&mut ev, Event::Mul, sp.proof_triples);
        return ev;
    }
    let matvec = |ev: &mut Vec<Event>| {
        rep(ev, Event::AuthPlain, d); // auth_plain of the d returned shares
        rep(ev, Event::Mul, d); // Freivalds inner product: d Beaver products
    };
    rep(&mut ev, Event::Input, sp.n_inputs());
    matvec(&mut ev); // z1 = W1 x
    rep(&mut ev, tr(0), d); // u1
    rep(&mut ev, Event::Lookup, d); // h, g1
    matvec(&mut ev); // z2 = W2 h
    rep(&mut ev, tr(1), d); // e = trunc(z2) - y
    rep(&mut ev, tr(2), d); // d2
    matvec(&mut ev); // b = W2^T d2
    rep(&mut ev, Event::Mul, d); // bg = b * g1
    rep(&mut ev, tr(3), d); // d1
    rep(&mut ev, Event::Mul, 2); // the two HE outer checks: one Beaver product each
    rep(&mut ev, Event::Mul, sp.proof_triples); // the collaborative proof's section, after the step
    ev
}

/// Tags of one event, in the order spdz.Engine requests them.
pub fn expand(sp: &StepParams, e: Event, out: &mut Vec<Tag>) {
    match e {
        Event::Input => out.push(Tag::In),
        Event::AuthPlain => out.push(Tag::Ar),
        Event::Mul => out.extend([Tag::Ta, Tag::Tb, Tag::Tc]),
        Event::Trunc(s, k) => {
            out.push(Tag::Tr);
            out.extend(std::iter::repeat(Tag::Trb).take(s as usize));
            out.push(Tag::Trh);
            if sp.proof_atoms {
                out.extend(std::iter::repeat(Tag::Trhb).take((k + KAPPA - s) as usize));
            }
            // borrow computation: 2 (s - 1) Beaver products
            for _ in 0..2 * (s - 1) {
                out.extend([Tag::Ta, Tag::Tb, Tag::Tc]);
            }
        }
        Event::Lookup => out.extend(std::iter::repeat(Tag::Lp).take(DEG)),
    }
}

pub fn tags(sp: &StepParams) -> Vec<Tag> {
    let mut out = Vec::new();
    for e in events(sp) {
        expand(sp, e, &mut out);
    }
    out
}

/// What the MASCOT program must generate for one step.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Plan {
    pub n_in: usize,
    pub n_ar: usize,
    pub n_tri: usize,
    pub n_lp: usize,
    /// distinct (s, K) classes in order of first use, with counts
    pub trunc_classes: Vec<(u32, u32, usize)>,
}

impl Plan {
    pub fn of(sp: &StepParams) -> Plan {
        let mut p = Plan { n_in: 0, n_ar: 0, n_tri: 0, n_lp: 0, trunc_classes: vec![] };
        for e in events(sp) {
            match e {
                Event::Input => p.n_in += 1,
                Event::AuthPlain => p.n_ar += 1,
                Event::Mul => p.n_tri += 1,
                Event::Trunc(s, k) => {
                    p.n_tri += 2 * (s as usize - 1);
                    match p.trunc_classes.iter().position(|&(a, b, _)| (a, b) == (s, k)) {
                        Some(i) => p.trunc_classes[i].2 += 1,
                        None => p.trunc_classes.push((s, k, 1)),
                    }
                }
                Event::Lookup => p.n_lp += 1,
            }
        }
        p
    }

    /// The index of truncation class (s, K).
    pub fn class_of(&self, s: u32, k: u32) -> usize {
        self.trunc_classes.iter().position(|&(a, b, _)| (a, b) == (s, k)).expect("a truncation class of the plan")
    }

    /// The compile-time arguments of mpc/darkprep.mpc.
    pub fn mpc_args(&self, threads: usize, batch: usize) -> Vec<String> {
        let mut a = vec![format!("in{}", self.n_in), format!("ar{}", self.n_ar), format!("tri{}", self.n_tri),
                         format!("lp{}", self.n_lp)];
        for &(s, k, m) in &self.trunc_classes {
            a.push(format!("tr{}x{}x{}", s, k, m));
        }
        a.push(format!("th{}", threads));
        a.push(format!("b{}", batch));
        a
    }

    /// Section layout of the Transactions file (must equal darkprep.mpc's): (base, n_components, count).
    pub fn sections(&self) -> Sections {
        let mut base = 0usize;
        let mut sec = |nc: usize, m: usize| {
            let b = base;
            base += nc * m;
            (b, nc, m)
        };
        let input = sec(3, self.n_in);
        let ar = sec(1, self.n_ar);
        let tri = sec(3, self.n_tri);
        let tr: Vec<_> = self.trunc_classes.iter().map(|&(_, k, m)| sec((k + KAPPA) as usize, m)).collect();
        let lp = sec(DEG, self.n_lp);
        Sections { input, ar, tri, tr, lp, total: base }
    }
}

#[derive(Clone, Debug)]
pub struct Sections {
    pub input: (usize, usize, usize),
    pub ar: (usize, usize, usize),
    pub tri: (usize, usize, usize),
    pub tr: Vec<(usize, usize, usize)>,
    pub lp: (usize, usize, usize),
    pub total: usize,
}

/// darkproof::spine::beaver_count: three degree-2 matvec sumchecks and the degree-3 Hadamard zerocheck over d entries.
pub fn spine_beaver_count(d: usize) -> usize {
    13 * (d - 1)
}

/// darkproof::middle::beaver_count: the degree-3 zerocheck over plen(n_had) entries.
pub fn middle_beaver_count(n_had: usize) -> usize {
    4 * (n_had.max(1).next_power_of_two() - 1)
}

/// A chunk: consecutive steps generated in one MASCOT run, each its own StepParams (e.g. a genesis step that inputs
/// W1, W2, x, y, then carried steps that input x, y). All steps must share the truncation parameters.
pub fn plan_of_steps(steps: &[StepParams]) -> Plan {
    let mut p = Plan::of(&steps[0]);
    for sp in &steps[1..] {
        let q = Plan::of(sp);
        assert_eq!(q.trunc_classes.iter().map(|c| (c.0, c.1)).collect::<Vec<_>>(),
                   p.trunc_classes.iter().map(|c| (c.0, c.1)).collect::<Vec<_>>(), "steps of a chunk share truncations");
        p.n_in += q.n_in;
        p.n_ar += q.n_ar;
        p.n_tri += q.n_tri;
        p.n_lp += q.n_lp;
        for (a, b) in p.trunc_classes.iter_mut().zip(&q.trunc_classes) {
            a.2 += b.2;
        }
    }
    p
}

/// Where step j's slice of each kind starts in a chunk: (in, ar, tri, lp, per truncation class).
pub fn offsets(steps: &[StepParams], j: usize) -> (usize, usize, usize, usize, Vec<usize>) {
    if j == 0 {
        return (0, 0, 0, 0, vec![0; Plan::of(&steps[0]).trunc_classes.len()]);
    }
    let p = plan_of_steps(&steps[..j]);
    (p.n_in, p.n_ar, p.n_tri, p.n_lp, p.trunc_classes.iter().map(|c| c.2).collect())
}

impl Plan {
    /// The plan for a chunk of `steps` identical steps: every count multiplied (sections stay one per kind; step j
    /// takes the j-th slice of each, see tape::assemble_step).
    pub fn of_chunk(sp: &StepParams, steps: usize) -> Plan {
        let mut p = Plan::of(sp);
        p.n_in *= steps;
        p.n_ar *= steps;
        p.n_tri *= steps;
        p.n_lp *= steps;
        for c in p.trunc_classes.iter_mut() {
            c.2 *= steps;
        }
        p
    }
}
