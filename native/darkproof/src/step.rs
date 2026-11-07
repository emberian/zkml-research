//! The step program's record (cosnark_gates.RecEngine) as the middle proof needs it: the verifier replays
//! mpc_fork.run_step SYMBOLICALLY against the public transcript (an opening reads its value, a preprocessing call
//! makes a fresh atom) and gets the middle's constraint system: the openings' forms (O), the preprocessing
//! well-formedness relations (P) and the IO ties (X). Only the middle's atoms are numbered (input, matvec and outer
//! preprocessing never enters a middle constraint, and only the relative order of atoms matters), and the input,
//! matvec and outer openings are consumed without forms.
use crate::field;

pub const KAPPA: u32 = 40;
pub const NAMES: [&str; 9] = ["z1", "z2", "b", "y", "h", "g1", "d2", "bg", "d1"];

/// Truncation shifts and bounds of mpc_fork.run_step: (S1, K1) for z1 and z2, (S2, K2) for e, (S3, K3) for bg.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct StepParams {
    pub s1: u32,
    pub k1: u32,
    pub s2: u32,
    pub k2: u32,
    pub s3: u32,
    pub k3: u32,
    /// the deployed step (research cosnark_he): HE matvec and HE outer, weights carried from step 2 on, over the HE
    /// profile's field; false: the harness's plain-SPDZ step (matrix and outer-product triples, W input every step)
    pub he: bool,
    /// the proof checks every truncation's input interval (cosnark_gates.append_range; genesis "RC": true)
    pub rc: bool,
    /// public constant added to b * g1 before its truncation (step_spec.Program.R3; 0 floors)
    pub r3: i64,
    /// the table's domain is [t_lo, t_lo + 256) (step_spec.Program.T_LO; the harness's -128)
    pub t_lo: i64,
    /// the lookup is proved by a bit circuit on z1's range bits instead of the masked powers (cosnark_gates
    /// append_lookup; genesis "LB": true; needs rc)
    pub lb: bool,
    /// R1 + R2 (proof.md 23; genesis "RS": true; needs rc): each range chain stops at bit B with one linear high row,
    /// and the tape deals K + 1 - s Trhb bits per truncation, with no TrhRange row
    pub rs: bool,
    /// public genesis: the initial weights are public, W = darktrain::init(cfg), committed with public coins
    /// (run::public_genesis); this is sha256 of the cfg json (genesis "PG"). Every step is then the carried
    /// program, step 1's parent being the public commitment.
    pub pg: Option<[u8; 32]>,
    /// exact truncation (genesis "XT": true; needs rs; notes/dark-learning-gen6/xtrunc.md): masks uniform in [0, p); the
    /// public check on each truncation opening is c >= 2^(K+1) (below it a wrap is possible: refused by name)
    pub xt: bool,
}

impl StepParams {
    /// The harness's step (step_spec S1, S2, S3 = 5, 4, 8; run_step's K = 13, 8, 13).
    pub const HARNESS: StepParams = StepParams { s1: 5, k1: 13, s2: 4, k2: 8, s3: 8, k3: 13, he: false, rc: false, r3: 0, t_lo: -128, lb: false, rs: false, pg: None, xt: false };
    /// The d = 4096 shifts of the decision doc's count formulas (§12; cosnark_gates.counts_formula at width).
    pub const WIDE: StepParams = StepParams { s1: 11, k1: 19, s2: 4, k2: 8, s3: 14, k3: 19, he: false, rc: false, r3: 0, t_lo: -128, lb: false, rs: false, pg: None, xt: false };
    /// The program a ledger of width d runs: the harness's up to d = 1024, the wide shifts beyond.
    pub fn for_width(d: usize) -> StepParams {
        if d <= 1024 { Self::HARNESS } else { Self::WIDE }
    }
    /// The same shifts, deployed (HE helpers).
    pub const fn deployed(self) -> StepParams {
        StepParams { he: true, ..self }
    }
    /// Does step `step` (1-based, the ledger's counter) take carried weights? The deployed program inputs W at
    /// genesis only.
    pub fn carried(&self, step: u64) -> bool {
        self.he && (step > 1 || self.pg.is_some())
    }
    /// Entries of the public transcript (data-independent): owner inputs, the three matvecs, the middle's openings
    /// (truncations: c plus 2 (s - 1) products; lookups; the b * g1 products), the two outer products.
    pub fn transcript_len(&self, d: usize, carried: bool) -> usize {
        let tr = |s: u32| 1 + 4 * (s as usize - 1);
        let middle = d * (2 * tr(self.s1) + 1 + tr(self.s2) + tr(self.s3) + 2);
        if self.he {
            // per HE matvec: d he_auth + d Freivalds products + 1 check; per HE outer: commit + 1 product + check
            (if carried { 0 } else { 2 * d * d }) + 2 * d + 3 * (3 * d + 1) + middle + 2 * 4
        } else {
            2 * d * d + 2 * d + 3 * (d * d + d) + middle + 4 * d
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Atom {
    /// index among the middle's preprocessing atoms (prep and proof-only), in creation order
    Prep(u32),
    /// (index into NAMES, element)
    Ext(u8, u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    Trunc,
    Lookup,
    Mul,
    TruncMask,
    TrhRange,
    Io,
    /// the release's one opening (cosnark_release)
    Release,
    /// the proved truncation input bound (append_range)
    Range,
    /// the lookup's bit circuit (append_lookup)
    LookupBits,
}

/// The middle's external vectors for a program other than the step (cosnark_gates_zk.IO): name and padded length,
/// the carried ones (an existing commitment at its second life), and the transcript label.
#[derive(Clone, Debug)]
pub struct Io {
    pub lens: Vec<(&'static str, usize)>,
    pub carried: Vec<&'static str>,
    pub label: &'static str,
}

/// One truncation whose input interval [a, a + 2^b) the proof checks: the bit atoms R of its mask r (trb then
/// trhb), its opened c, its K and s, and the truncation's name and index (for refusals).
#[derive(Clone, Debug)]
pub struct RangeD {
    pub name: &'static str,
    pub k: usize,
    pub bits: Vec<u32>,
    pub c: u64,
    pub kk: u32,
    pub s: u32,
    pub a: i64,
    pub b: u32,
    /// the truncation's mask atom r (R1's high row); rs: the chain stops at bit b
    pub r: u32,
    pub rs: bool,
}

/// Its rows (append_range): L = K + KAPPA + 1, c' = c - (2^K + a) bitwise, the product and borrow atoms.
#[derive(Clone, Debug)]
pub struct RangeRow {
    pub d: RangeD,
    pub l: usize,
    pub cb: Vec<u64>,
    pub t: Vec<Option<u32>>,
    pub bb: Vec<u32>,
    /// rs: floor(c' / 2^B), the high row's public constant
    pub chi: i128,
}

/// The release's z1 = W1 X binding (X public): d M linear IO constraints at cons[start..start + d M], entry (j, t) at
/// start + j M + t: z1[j M + t] - sum_k X[k][t] W1[j d + k] = 0. Stored densely; build_q expands it.
#[derive(Clone, Debug)]
pub struct PubMat {
    pub d: usize,
    pub m: usize,
    /// X[k][t] at k M + t
    pub x: Vec<u64>,
    pub start: usize,
    pub z1: u8,
    pub w1: u8,
}

#[derive(Clone, Debug, Default)]
pub struct Form {
    pub terms: Vec<(Atom, u64)>,
    pub c: u64,
}

pub struct Con {
    pub form: Form,
    pub value: u64,
    pub phase: Phase,
    /// transcript position of an opening (usize::MAX for the relation constraints)
    pub pos: usize,
}

/// A stored constraint, read from `Cons`.
#[derive(Clone, Copy, Debug)]
pub struct ConRef<'a> {
    pub terms: &'a [(Atom, u64)],
    pub c: u64,
    pub value: u64,
    pub phase: Phase,
    pub pos: usize,
}

/// The constraint list, flat: every constraint's terms in one arena with an offset each (memory: a Vec per
/// constraint cost about 150 B a constraint, 5.9 GB for the release at M = 52 before RS). Same order, same values.
#[derive(Default)]
pub struct Cons {
    terms: Vec<(Atom, u64)>,
    /// end of constraint j's terms in `terms`
    end: Vec<u32>,
    c: Vec<u64>,
    value: Vec<u64>,
    phase: Vec<Phase>,
    /// u32::MAX for usize::MAX
    pos: Vec<u32>,
}

impl Cons {
    pub fn len(&self) -> usize {
        self.end.len()
    }
    pub fn is_empty(&self) -> bool {
        self.end.is_empty()
    }
    pub fn push(&mut self, con: Con) {
        self.terms.extend_from_slice(&con.form.terms);
        self.end.push(u32::try_from(self.terms.len()).expect("constraint terms beyond u32"));
        self.c.push(con.form.c);
        self.value.push(con.value);
        self.phase.push(con.phase);
        self.pos.push(if con.pos == usize::MAX { u32::MAX } else { u32::try_from(con.pos).expect("transcript position beyond u32") });
    }
    pub fn get(&self, j: usize) -> ConRef<'_> {
        let a = if j == 0 { 0 } else { self.end[j - 1] as usize };
        ConRef {
            terms: &self.terms[a..self.end[j] as usize],
            c: self.c[j],
            value: self.value[j],
            phase: self.phase[j],
            pos: if self.pos[j] == u32::MAX { usize::MAX } else { self.pos[j] as usize },
        }
    }
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = ConRef<'_>> + ExactSizeIterator + '_ {
        (0..self.len()).map(move |j| self.get(j))
    }
    /// return the buffers' spare capacity (the replay is done)
    pub fn shrink_to_fit(&mut self) {
        self.terms.shrink_to_fit();
        self.end.shrink_to_fit();
        self.c.shrink_to_fit();
        self.value.shrink_to_fit();
        self.phase.shrink_to_fit();
        self.pos.shrink_to_fit();
    }
}

/// The preprocessing tags, recorded so a live witness can be checked against the replay.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tag {
    Tr,
    Trb,
    Trh,
    Trhb,
    Ta,
    Tb,
    Tc,
    Lp,
    /// proof-only: a range row's product t_i = R_i beta_i and its borrow beta_(i+1)
    Rt,
    Rb,
    /// proof-only: the lookup's bit circuit, a linear atom and a product atom (append_lookup)
    Lq,
    Lm,
}

/// One op of a lookup's bit circuit, in creation order: atom = form (linear), or atom = x y (a proof-time product).
#[derive(Clone, Debug)]
pub enum LbOp {
    Lin(u32, Vec<(u32, u64)>, u64),
    Mul(u32, u32, u32),
}

pub struct Rec<'t> {
    pub prm: StepParams,
    pub d: usize,
    pub tags: Vec<Tag>,
    pub cons: Cons,
    pub had: Vec<(u32, u32, u32)>,
    transcript: &'t [u64],
    pub tpos: usize,
    tables: (Vec<u64>, Vec<u64>),
    /// the external vectors' names (Atom::Ext indexes this): NAMES for the step
    pub names: Vec<&'static str>,
    pub io: Option<Io>,
    pub pubmat: Option<PubMat>,
    pub ranges: Vec<RangeD>,
    pub range_rows: Vec<RangeRow>,
    /// (name, index) of truncations whose PUBLIC c' already lies outside [0, 2^L)
    pub range_fail: Vec<(&'static str, usize)>,
    /// XT: the public transcript position of the first truncation opening in the wrap zone (c < 2^(K+1))
    pub xt_zone: Option<usize>,
    /// atoms of the program (before the proof-only range rows)
    pub n_step_atoms: Option<usize>,
    /// prm.lb: per lookup, whether it has a g1 column (the step's) or only h (the release's)
    pub lb_req: Vec<bool>,
    /// prm.lb: the circuit's ops per lookup (append_lookup)
    pub lb_rows: Vec<Vec<LbOp>>,
    /// prm.lb: the masked-power atoms the MPC made and the proof drops, as (start, count) in the program's atom order
    /// with them (a record from darkstep or the native live engine carries them; the replay does not)
    pub lp_drop: Option<(usize, usize)>,
}

#[derive(Debug)]
pub enum Short {
    /// the transcript ends before the program does
    Short,
    /// the program's parameters do not admit a proof feature it asks for (the bit lookup's preconditions)
    Program(&'static str),
    /// a deployed step's he_outer_commit entry is not 0 (cosnark_he.SymOuter)
    Commit,
}

fn neg_form(f: &Form) -> Vec<(Atom, u64)> {
    f.terms.iter().map(|&(a, c)| (a, field::neg(c))).collect()
}

impl StepParams {
    /// cosnark_he.Prog.bound: the proved interval (a, B) of truncation `name`.
    pub fn bound(&self, name: &str, kc: u32) -> (i64, u32) {
        match name {
            "z1" => (self.t_lo << self.s1, self.s1 + 8),
            "z2" | "score" => (-(1i64 << self.k1), self.k1 + 1),
            "e" => (-(1i64 << self.k2), self.k2 + 1),
            "bg" => (-(1i64 << self.k3), self.k3 + 1),
            "compare" => (-(1i64 << kc), kc + 1),
            _ => panic!("no truncation {name}"),
        }
    }
    pub fn rc_of(&self, name: &'static str, kc: u32) -> Option<(&'static str, i64, u32)> {
        if self.rc {
            let (a, b) = self.bound(name, kc);
            Some((name, a, b))
        } else {
            None
        }
    }
}

impl Rec<'static> {
    /// An empty record, only for building circuits (lookup_bits_ops).
    fn scratch(prm: StepParams) -> Rec<'static> {
        Rec {
            prm,
            d: 0,
            tags: Vec::new(),
            cons: Cons::default(),
            had: Vec::new(),
            transcript: &[],
            tpos: 0,
            tables: (Vec::new(), Vec::new()),
            names: NAMES.to_vec(),
            io: None,
            pubmat: None,
            ranges: Vec::new(),
            range_rows: Vec::new(),
            range_fail: Vec::new(),
            xt_zone: None,
            n_step_atoms: None,
            lb_req: Vec::new(),
            lb_rows: Vec::new(),
            lp_drop: None,
        }
    }
}

impl<'t> Rec<'t> {
    /// XT (notes/dark-learning-gen6/xtrunc.md): Err naming the first truncation opening in the wrap zone; a step or
    /// release with one must have been redone, so the verifier and the custodians refuse it.
    pub fn xt_refusal(&self) -> Result<(), String> {
        match self.xt_zone {
            Some(pos) => Err(format!("XT: truncation opening in the wrap zone (c < 2^(K+1), public entry {pos})")),
            None => Ok(()),
        }
    }

    /// cosnark_gates.append_range: the borrow-chain rows of every checked truncation, after the program's atoms.
    pub fn append_range(&mut self) {
        self.n_step_atoms = Some(self.tags.len());
        let ds = std::mem::take(&mut self.ranges);
        for d in ds.iter() {
            let l = (d.kk + KAPPA + 1) as usize;
            let lo = (1i128 << d.kk) + d.a as i128;
            let cp = d.c as i128 - lo;
            if !(0..(1i128 << l)).contains(&cp) {
                self.range_fail.push((d.name, d.k));
            }
            let cpm = cp.rem_euclid(1i128 << l);
            let cb: Vec<u64> = (0..l).map(|i| ((cpm >> i) & 1) as u64).collect();
            if d.rs {
                // R1 (proof.md 23): the chain over i < B, then r - sum_(i<B) 2^i R_i + 2^B beta_B = 2^B floor(c' / 2^B)
                assert_eq!(d.bits.len(), (d.kk + 1) as usize);
                let bl = d.b as usize;
                let mut ts = Vec::with_capacity(bl);
                let mut bs = Vec::with_capacity(bl);
                let mut beta: Option<u32> = None;
                for i in 0..bl {
                    let rv = d.bits[i];
                    let t = beta.map(|bv| {
                        let t = self.atom(Tag::Rt);
                        self.had.push((rv, bv, t));
                        t
                    });
                    let nb = self.atom(Tag::Rb);
                    let mut f = vec![(Atom::Prep(nb), 1u64)];
                    if cb[i] == 1 {
                        if let Some(t) = t {
                            f.push((Atom::Prep(t), field::p() - 1));
                        }
                    } else {
                        for (x, co) in [(Some(rv), field::p() - 1), (beta, field::p() - 1), (t, 1)] {
                            if let Some(x) = x {
                                f.push((Atom::Prep(x), co));
                            }
                        }
                    }
                    self.cons.push(Con { form: Form { terms: f, c: 0 }, value: 0, phase: Phase::Range, pos: usize::MAX });
                    ts.push(t);
                    bs.push(nb);
                    beta = Some(nb);
                }
                let chi = cp >> bl;
                let mut g: Vec<(Atom, u64)> = vec![(Atom::Prep(d.r), 1)];
                for i in 0..bl {
                    g.push((Atom::Prep(d.bits[i]), field::neg(field::pow(2, i as u64))));
                }
                g.push((Atom::Prep(beta.unwrap()), field::pow(2, bl as u64)));
                let chi_f = field::mul(field::from_i64((chi.rem_euclid(field::p() as i128)) as i64), field::pow(2, bl as u64));
                self.cons.push(Con { form: Form { terms: g, c: field::neg(chi_f) }, value: 0, phase: Phase::Range, pos: usize::MAX });
                self.range_rows.push(RangeRow { d: d.clone(), l: bl, cb, t: ts, bb: bs, chi });
                continue;
            }
            assert_eq!(d.bits.len(), (d.kk + KAPPA) as usize);
            let mut ts = Vec::with_capacity(l);
            let mut bs = Vec::with_capacity(l);
            let mut beta: Option<u32> = None;
            for i in 0..l {
                let ri = d.bits.get(i).copied();
                let t = match (ri, beta) {
                    (Some(rv), Some(bv)) => {
                        let t = self.atom(Tag::Rt);
                        self.had.push((rv, bv, t));
                        Some(t)
                    }
                    _ => None,
                };
                let nb = self.atom(Tag::Rb);
                let mut f = vec![(Atom::Prep(nb), 1u64)];
                if cb[i] == 1 {
                    if let Some(t) = t {
                        f.push((Atom::Prep(t), field::p() - 1));
                    }
                } else {
                    for (x, co) in [(ri, field::p() - 1), (beta, field::p() - 1), (t, 1)] {
                        if let Some(x) = x {
                            f.push((Atom::Prep(x), co));
                        }
                    }
                }
                self.cons.push(Con { form: Form { terms: f, c: 0 }, value: 0, phase: Phase::Range, pos: usize::MAX });
                if i >= d.b as usize {
                    let mut g = vec![(Atom::Prep(nb), 2u64)];
                    for x in [ri, beta].into_iter().flatten() {
                        g.push((Atom::Prep(x), field::p() - 1));
                    }
                    self.cons.push(Con { form: Form { terms: g, c: cb[i] }, value: 0, phase: Phase::Range, pos: usize::MAX });
                }
                ts.push(t);
                bs.push(nb);
                beta = Some(nb);
            }
            self.cons.push(Con { form: Form { terms: vec![(Atom::Prep(beta.unwrap()), 1)], c: 0 }, value: 0, phase: Phase::Range, pos: usize::MAX });
            self.range_rows.push(RangeRow { d: d.clone(), l, cb, t: ts, bb: bs, chi: 0 });
        }
    }

    /// cosnark_gates.append_lookup: the lookup's bit circuit, per lookup after the range rows. z1's range rows prove
    /// z1 - a in [0, 2^(s1 + 8)) (a = t_lo 2^s1) through boolean difference bits; the top 8 are v = u1 - t_lo. Then
    /// h = w Bf - w lo + (q - 7) Bf - (q + 7) lo + 7 (w = v >> 2, q = t_lo / 4, lo = [w < -7 - q], Bf = [w < 8 - q])
    /// and g1 = [v < 32 - t_lo] - [v < -28 - t_lo], tied to the external atoms h[k], g1[k].
    pub fn append_lookup(&mut self) -> Result<(), Short> {
        let p = field::p();
        let (t_lo, s1) = (self.prm.t_lo, self.prm.s1);
        if !self.prm.rc {
            return Err(Short::Program("the bit lookup (LB) needs the range check (RC)"));
        }
        if t_lo.rem_euclid(4) != 0 {
            return Err(Short::Program("the bit lookup needs t_lo divisible by 4"));
        }
        let q = t_lo.div_euclid(4);
        let z1rows: Vec<usize> = (0..self.range_rows.len()).filter(|&j| self.range_rows[j].d.name == "z1").collect();
        let reqs = self.lb_req.clone();
        for (k, &has_g1) in reqs.iter().enumerate() {
            let row = self.range_rows[*z1rows.get(k).ok_or(Short::Program("a lookup without its z1 range row"))?].clone();
            if (row.d.a, row.d.b, row.d.s) != (t_lo << s1, s1 + 8, s1) {
                return Err(Short::Program("the bit lookup needs z1's interval to be the table's domain"));
            }
            let mut bx = Bits { rec: self, ops: Vec::new() };
            let mut v = Vec::with_capacity(8);
            for j in 0..8usize {
                let i = s1 as usize + j;
                let mut f = Lf::new();
                f.add(row.d.bits[i], p - 1);
                f.add(row.bb[i], 2);
                if i > 0 {
                    f.add(row.bb[i - 1], p - 1);
                }
                v.push(bx.atom(&f, row.cb[i]));
            }
            let lo = bx.lt(&v[2..], -7 - q);
            let bf = bx.lt(&v[2..], 8 - q);
            let mut wf = Lf::new();
            for j in 0..6 {
                wf.add(v[2 + j], 1u64 << j);
            }
            let (wb, wl) = if !lo.0 .0.is_empty() || !bf.0 .0.is_empty() {
                let w = bx.atom(&wf, 0);
                (bx.mul(w, &bf), bx.mul(w, &lo))
            } else {
                let pick = |c: &(Lf, u64)| if c.1 != 0 { (wf.clone(), 0) } else { (Lf::new(), 0) };
                (pick(&bf), pick(&lo))
            };
            let one = (Lf::new(), 1u64);
            let h = addf(&[(1, &wb), (-1, &wl), (q - 7, &bf), (-(q + 7), &lo), (7, &one)]);
            let mut outs = vec![h];
            if has_g1 {
                let a = bx.lt(&v, 32 - t_lo);
                let b = bx.lt(&v, -28 - t_lo);
                outs.push(addf(&[(1, &a), (-1, &b)]));
            }
            let ops = bx.ops;
            for (col, (fm, c)) in outs.into_iter().enumerate() {
                let mut terms: Vec<(Atom, u64)> = fm.0.iter().map(|(&x, &co)| (Atom::Prep(x), co)).collect();
                terms.push((self.ext(if col == 0 { "h" } else { "g1" }, k), p - 1));
                self.cons.push(Con { form: Form { terms, c }, value: 0, phase: Phase::LookupBits, pos: usize::MAX });
            }
            self.lb_rows.push(ops);
        }
        Ok(())
    }

    /// Every proof-time Beaver product of the middle's proof-only rows: the range rows', then the bit lookups'.
    pub fn proof_products(&self) -> usize {
        self.range_products() + self.lookup_products() + self.zero_test_triples()
    }

    /// RS: the masked zero test over every range row draws two triples (rho, then rho S; middle.rs fill_range).
    pub fn zero_test_triples(&self) -> usize {
        if self.range_rows.first().is_some_and(|r| r.d.rs) { 2 } else { 0 }
    }

    /// Proof-time Beaver products of the lookups' bit circuits.
    pub fn lookup_products(&self) -> usize {
        self.lb_rows.iter().map(|ops| ops.iter().filter(|o| matches!(o, LbOp::Mul(..))).count()).sum()
    }

    /// Proof-time Beaver products of the range rows.
    pub fn range_products(&self) -> usize {
        self.range_rows.iter().map(|r| r.t.iter().filter(|t| t.is_some()).count()).sum()
    }

    /// A witness's program atoms as the middle takes them: as is, or (prm.lb) with the MPC's masked-power atoms
    /// dropped when the record still carries them (darkstep's ProofRecord, the native live engine).
    pub fn witness_atoms<T: Copy>(&self, atoms: &[T]) -> Result<Vec<T>, String> {
        let n = self.n_program_atoms();
        if atoms.len() == n {
            return Ok(atoms.to_vec());
        }
        if let Some((st, cnt)) = self.lp_drop {
            if atoms.len() == n + cnt {
                let mut v = Vec::with_capacity(n);
                v.extend_from_slice(&atoms[..st]);
                v.extend_from_slice(&atoms[st + cnt..]);
                return Ok(v);
            }
        }
        Err(format!("witness atoms differ from the replay ({} vs {n})", atoms.len()))
    }

    /// The program's own atoms (the witness's), before the proof-only range rows.
    pub fn n_program_atoms(&self) -> usize {
        self.n_step_atoms.unwrap_or(self.tags.len())
    }

    fn open(&mut self, form: Form, phase: Phase) -> Result<u64, Short> {
        let v = *self.transcript.get(self.tpos).ok_or(Short::Short)?;
        self.tpos += 1;
        self.cons.push(Con { form, value: v, phase, pos: self.tpos - 1 });
        Ok(v)
    }
    fn skip(&mut self, k: usize) -> Result<(), Short> {
        if self.tpos + k > self.transcript.len() {
            return Err(Short::Short);
        }
        self.tpos += k;
        Ok(())
    }
    fn atom(&mut self, t: Tag) -> u32 {
        self.tags.push(t);
        (self.tags.len() - 1) as u32
    }
    fn mul(&mut self, x: &Form, y: &Form) -> Result<Form, Short> {
        let a = self.atom(Tag::Ta);
        let b = self.atom(Tag::Tb);
        let c = self.atom(Tag::Tc);
        self.had.push((a, b, c));
        let mut fx = x.terms.clone();
        fx.push((Atom::Prep(a), field::p() - 1));
        let e = self.open(Form { terms: fx, c: x.c }, Phase::Mul)?;
        let mut fy = y.terms.clone();
        fy.push((Atom::Prep(b), field::p() - 1));
        let f = self.open(Form { terms: fy, c: y.c }, Phase::Mul)?;
        let mut terms = vec![(Atom::Prep(c), 1)];
        if e != 0 {
            terms.push((Atom::Prep(b), e));
        }
        if f != 0 {
            terms.push((Atom::Prep(a), f));
        }
        Ok(Form { terms, c: field::mul(e, f) })
    }
    fn trunc(&mut self, x: &Form, s: u32, k: u32) -> Result<Form, Short> {
        self.trunc_rc(x, s, k, None)
    }

    /// rc = (name, a, B): the proof also checks x in [a, a + 2^B) (append_range).
    fn trunc_rc(&mut self, x: &Form, s: u32, k: u32, rc: Option<(&'static str, i64, u32)>) -> Result<Form, Short> {
        if self.prm.rs {
            // R2's soundness needs every truncation range-checked, 2^s | a and s <= B <= K + 1 (proof.md 23)
            match rc {
                Some((_, a, b)) if a.rem_euclid(1i64 << s) == 0 && s <= b && b <= k + 1 => {}
                _ => return Err(Short::Program("RS: every truncation needs a range with 2^s | a and s <= B <= K + 1")),
            }
        }
        let r = self.atom(Tag::Tr);
        let bits: Vec<u32> = (0..s)
            .map(|_| {
                let b = self.atom(Tag::Trb);
                self.had.push((b, b, b));
                b
            })
            .collect();
        let rhi = self.atom(Tag::Trh);
        let nb = if self.prm.rs { k + 1 - s } else { k + KAPPA - s };
        let hb: Vec<u32> = (0..nb)
            .map(|_| {
                let b = self.atom(Tag::Trhb);
                self.had.push((b, b, b));
                b
            })
            .collect();
        let mut f = vec![(Atom::Prep(r), 1), (Atom::Prep(rhi), field::neg(field::pow(2, s as u64)))];
        for (i, &rb) in bits.iter().enumerate() {
            f.push((Atom::Prep(rb), field::neg(1u64 << i)));
        }
        self.cons.push(Con { form: Form { terms: f, c: 0 }, value: 0, phase: Phase::TruncMask, pos: usize::MAX });
        if !self.prm.rs {
            // under RS rhi has no bound row: every truncation's range (R1) makes the output exact without it
            let mut f = vec![(Atom::Prep(rhi), 1)];
            for (j, &b) in hb.iter().enumerate() {
                f.push((Atom::Prep(b), field::neg(field::pow(2, j as u64))));
            }
            self.cons.push(Con { form: Form { terms: f, c: 0 }, value: 0, phase: Phase::TrhRange, pos: usize::MAX });
        }
        let mut fo = x.terms.clone();
        fo.push((Atom::Prep(r), 1));
        let c = self.open(Form { terms: fo, c: field::add(x.c, 1u64 << k) }, Phase::Trunc)?;
        if self.prm.xt && c < 1u64 << (k + 1) && self.xt_zone.is_none() {
            // XT: the custodians must have redone the step (a wrap is possible only here); the verifier refuses by
            // name (xt_refusal). Recorded, not an Err: the count replays run on all-zero transcripts
            self.xt_zone = Some(self.tpos - 1);
        }
        if let Some((name, a, b)) = rc {
            let kidx = self.ranges.iter().filter(|r| r.name == name).count();
            let mut all = bits.clone();
            all.extend(&hb);
            self.ranges.push(RangeD { name, k: kidx, bits: all, c, kk: k, s, a, b, r, rs: self.prm.rs });
        }
        let clow = c & ((1u64 << s) - 1);
        let a: Vec<u64> = (0..s).map(|i| (clow >> i) & 1).collect();
        // eq_j = 1 - (a_j xor r_j) = -(1 - 2 a_j) r_j + (1 - a_j)
        let eq: Vec<Form> = (0..s as usize)
            .map(|j| Form {
                terms: vec![(Atom::Prep(bits[j]), field::neg(field::from_i64(1 - 2 * a[j] as i64)))],
                c: field::from_i64(1 - a[j] as i64),
            })
            .collect();
        let mut borrow: Option<Form> = None;
        let mut prefix: Option<Form> = None;
        for i in (0..s as usize).rev() {
            let co = 1 - a[i];
            let mut term = Form { terms: if co != 0 { vec![(Atom::Prep(bits[i]), co)] } else { vec![] }, c: 0 };
            if let Some(pf) = &prefix {
                term = self.mul(&term, pf)?;
            }
            borrow = Some(match borrow {
                None => term,
                Some(b) => {
                    let mut t = b.terms;
                    t.extend(term.terms);
                    Form { terms: t, c: field::add(b.c, term.c) }
                }
            });
            prefix = Some(match prefix {
                None => eq[i].clone(),
                Some(pf) => self.mul(&pf, &eq[i])?,
            });
        }
        let borrow = borrow.unwrap();
        let q = field::from_i64((c >> s) as i64 - (1i64 << (k - s)));
        let mut terms = vec![(Atom::Prep(rhi), field::p() - 1)];
        terms.extend(neg_form(&borrow));
        Ok(Form { terms, c: field::sub(q, borrow.c) })
    }
    fn lookup2(&mut self, u: &Form, offset: u64, cols: usize) -> Result<(Form, Form), Short> {
        let deg = 255usize;
        if self.prm.lb {
            // the MPC's masked-power lookup, outside the proof: its opening has no middle constraint and its power atoms
            // are not the middle's; the outputs are the external atoms h[k], g1[k] (append_lookup proves them)
            let k = self.lb_req.len();
            let at = self.tags.len();
            self.lp_drop = Some(match self.lp_drop {
                None => (at, deg),
                Some((st, n)) => (st, n + deg),
            });
            self.skip(1)?;
            self.lb_req.push(cols == 2);
            let h = Form { terms: vec![(self.ext("h", k), 1)], c: 0 };
            let g = if cols == 2 { Form { terms: vec![(self.ext("g1", k), 1)], c: 0 } } else { Form::default() };
            return Ok((h, g));
        }
        let mut pw = Vec::with_capacity(deg);
        for _ in 0..deg {
            let a = self.atom(Tag::Lp);
            pw.push(a);
            if pw.len() >= 2 {
                self.had.push((pw[0], pw[pw.len() - 2], a));
            }
        }
        let mut f = u.terms.clone();
        f.push((Atom::Prep(pw[0]), field::p() - 1));
        let c = self.open(Form { terms: f, c: field::add(u.c, offset) }, Phase::Lookup)?;
        let mk = |coeffs: &[u64]| {
            let tay = taylor_shift(coeffs, c);
            let mut terms = Vec::with_capacity(tay.len() - 1);
            for j in 1..tay.len() {
                if tay[j] != 0 {
                    terms.push((Atom::Prep(pw[j - 1]), tay[j]));
                }
            }
            Form { terms, c: tay[0] }
        };
        let t0 = self.tables.0.clone();
        let t1 = self.tables.1.clone();
        Ok((mk(&t0), mk(&t1)))
    }
    fn ext(&self, name: &str, k: usize) -> Atom {
        Atom::Ext(self.names.iter().position(|&x| x == name).unwrap() as u8, k as u32)
    }
    fn rec_in(&self, name: &str) -> Vec<Form> {
        (0..self.d).map(|k| Form { terms: vec![(self.ext(name, k), 1)], c: 0 }).collect()
    }
    fn rec_out(&mut self, name: &str, v: &[Form]) {
        if self.prm.lb && (name == "h" || name == "g1") {
            return; // the lookup's outputs are the external atoms themselves (lookup2)
        }
        for (k, x) in v.iter().enumerate() {
            let mut f = x.terms.clone();
            f.push((self.ext(name, k), field::p() - 1));
            self.cons.push(Con { form: Form { terms: f, c: x.c }, value: 0, phase: Phase::Io, pos: usize::MAX });
        }
    }
}

/// mpc_fork.run_step(sym, ...) (prm.he: cosnark_he.replay) against the public transcript. Err if the transcript is
/// shorter than the program. carried: the step takes the previous step's weights (no W input; deployed only).
pub fn replay<'t>(transcript: &'t [u64], d: usize, prm: StepParams, tables: &(Vec<u64>, Vec<u64>), carried: bool) -> Result<Rec<'t>, Short> {
    assert!(prm.he || !carried, "the plain-SPDZ program inputs W every step");
    let mut r = Rec {
        prm,
        d,
        tags: Vec::new(),
        cons: Cons::default(),
        had: Vec::new(),
        transcript,
        tpos: 0,
        tables: tables.clone(),
        names: NAMES.to_vec(),
        io: None,
        pubmat: None,
        ranges: Vec::new(),
        range_rows: Vec::new(),
        range_fail: Vec::new(),
        xt_zone: None,
        n_step_atoms: None,
        lb_req: Vec::new(),
        lb_rows: Vec::new(),
        lp_drop: None,
    };
    // HE matvec: d he_auth, d Freivalds products (2 openings each), the check; plain: W - A (d^2) and v - b (d)
    let mv = if prm.he { 3 * d + 1 } else { d * d + d };
    if !carried {
        r.skip(2 * d * d)?; // owner inputs W1, W2
    }
    r.skip(2 * d)?; // owner inputs x, y
    r.skip(mv)?; // matvec z1
    let z1 = r.rec_in("z1");
    let mut u1 = Vec::with_capacity(d);
    for z in &z1 {
        u1.push(r.trunc_rc(z, prm.s1, prm.k1, prm.rc_of("z1", 10))?);
    }
    let mut h = Vec::with_capacity(d);
    let mut g1 = Vec::with_capacity(d);
    for u in &u1 {
        let (a, b) = r.lookup2(u, field::from_i64(-prm.t_lo), 2)?;
        h.push(a);
        g1.push(b);
    }
    r.rec_out("h", &h);
    r.rec_out("g1", &g1);
    r.skip(mv)?; // matvec z2
    let z2 = r.rec_in("z2");
    let y = r.rec_in("y");
    let mut e = Vec::with_capacity(d);
    for (z, yy) in z2.iter().zip(&y) {
        let t = r.trunc_rc(z, prm.s1, prm.k1, prm.rc_of("z2", 10))?;
        let mut terms = t.terms;
        terms.extend(neg_form(yy));
        e.push(Form { terms, c: field::sub(t.c, yy.c) });
    }
    let mut d2 = Vec::with_capacity(d);
    for v in &e {
        d2.push(r.trunc_rc(v, prm.s2, prm.k2, prm.rc_of("e", 10))?);
    }
    r.rec_out("d2", &d2);
    r.skip(mv)?; // matvec b (transposed)
    let b = r.rec_in("b");
    let mut bg = Vec::with_capacity(d);
    for (bb, g) in b.iter().zip(&g1) {
        bg.push(r.mul(bb, g)?);
    }
    r.rec_out("bg", &bg);
    let mut d1 = Vec::with_capacity(d);
    for v in &bg {
        // b * g1 + r3 (a public constant: the form's constant moves)
        let v = Form { terms: v.terms.clone(), c: field::add(v.c, field::from_i64(prm.r3)) };
        d1.push(r.trunc_rc(&v, prm.s3, prm.k3, prm.rc_of("bg", 10))?);
    }
    r.rec_out("d1", &d1);
    for _ in 0..2 {
        // outer(d2, h), then outer(d1, x)
        if prm.he {
            // the commitment entry (value 0), one Beaver product, the check opening
            if *r.transcript.get(r.tpos).ok_or(Short::Short)? != 0 {
                return Err(Short::Commit);
            }
            r.skip(4)?;
        } else {
            r.skip(2 * d)?;
        }
    }
    if prm.rc {
        r.append_range();
    }
    if prm.lb {
        r.append_lookup()?;
    }
    r.cons.shrink_to_fit();
    Ok(r)
}

/// The release program (cosnark_release.run_release) replayed against the public transcript: external vectors W1,
/// W2 (the head's, carried), z1, h; x = the public inputs X[k][t] at k M + t (mod p); labels < ncls; the comparison
/// truncation shift kc (= its bound).
#[allow(clippy::too_many_arguments)]
pub fn replay_release<'t>(
    transcript: &'t [u64],
    d: usize,
    m: usize,
    prm: StepParams,
    x: &[u64],
    labels: &[usize],
    ncls: usize,
    kc: u32,
) -> Result<Rec<'t>, Short> {
    let sig = tables_for(prm.t_lo).0;
    let mut r = Rec {
        prm,
        d,
        tags: Vec::new(),
        cons: Cons::default(),
        had: Vec::new(),
        transcript,
        tpos: 0,
        tables: (sig.clone(), sig),
        names: vec!["W1", "W2", "z1", "h"],
        io: Some(Io {
            lens: vec![("W1", d * d), ("W2", d * d), ("z1", (d * m).next_power_of_two()), ("h", (d * m).next_power_of_two())],
            carried: vec!["W1", "W2"],
            label: "release-zk",
        }),
        pubmat: None,
        ranges: Vec::new(),
        range_rows: Vec::new(),
        range_fail: Vec::new(),
        xt_zone: None,
        n_step_atoms: None,
        lb_req: Vec::new(),
        lb_rows: Vec::new(),
        lp_drop: None,
    };
    assert_eq!(x.len(), d * m);
    assert_eq!(labels.len(), m);
    // z1 = W1 X: the d M IO constraints, densely (build_q expands them)
    let start = r.cons.len();
    for _ in 0..d * m {
        r.cons.push(Con { form: Form::default(), value: 0, phase: Phase::Io, pos: usize::MAX });
    }
    r.pubmat = Some(PubMat { d, m, x: x.to_vec(), start, z1: 2, w1: 0 });
    let z1: Vec<Form> = (0..d * m).map(|k| Form { terms: vec![(r.ext("z1", k), 1)], c: 0 }).collect();
    let mut u1 = Vec::with_capacity(d * m);
    for z in &z1 {
        u1.push(r.trunc_rc(z, prm.s1, prm.k1, prm.rc_of("z1", 10))?);
    }
    let off = field::from_i64(-prm.t_lo);
    let mut h = Vec::with_capacity(d * m);
    if prm.rs && prm.lb {
        // L (proof.md 23): the MPC computed h by bits, outside the proof (its Beaver openings have no constraint);
        // h[k] is the external atom, proved by append_lookup
        if (r.ranges.iter().filter(|x| x.name == "z1").count(), prm.rc) != (d * m, true) {
            return Err(Short::Program("L: the lookup by bits needs RC on every z1"));
        }
        r.skip(2 * d * m * lookup_bits_products(prm))?;
        for k in 0..d * m {
            r.lb_req.push(false);
            h.push(Form { terms: vec![(r.ext("h", k), 1)], c: 0 });
        }
    } else {
        for u in &u1 {
            h.push(r.lookup2(u, off, 1)?.0);
        }
    }
    drop(u1);
    r.rec_out("h", &h);
    drop(h);
    // every class-row product (c, t, k), then every score truncation (c, t), then every comparison (t, k != l), then
    // the comparisons' products stage by stage (cosnark_release's batch-friendly order)
    let mut sums: Vec<Form> = Vec::with_capacity(ncls * m);
    for c in 0..ncls {
        for t in 0..m {
            let mut acc = Form::default();
            for k in 0..d {
                let w = Form { terms: vec![(r.ext("W2", c * d + k), 1)], c: 0 };
                let hb = Form { terms: vec![(r.ext("h", k * m + t), 1)], c: 0 };
                let pr_ = r.mul(&w, &hb)?;
                acc.terms.extend(pr_.terms);
                acc.c = field::add(acc.c, pr_.c);
            }
            sums.push(acc);
        }
    }
    let mut o: Vec<Vec<Form>> = Vec::with_capacity(ncls);
    for c in 0..ncls {
        let mut row = Vec::with_capacity(m);
        for t in 0..m {
            row.push(r.trunc_rc(&sums[c * m + t], prm.s1, prm.k1, prm.rc_of("score", kc))?);
        }
        o.push(row);
    }
    drop(sums);
    let mut fs: Vec<Vec<Form>> = Vec::with_capacity(m);
    for t in 0..m {
        let l = labels[t];
        let mut f_t = Vec::with_capacity(ncls - 1);
        for k in 0..ncls {
            if k == l {
                continue;
            }
            let mut terms = o[l][t].terms.clone();
            terms.extend(neg_form(&o[k][t]));
            let diff = Form { terms, c: field::sub(field::sub(o[l][t].c, o[k][t].c), 1) };
            let q = r.trunc_rc(&diff, kc, kc, prm.rc_of("compare", kc))?;
            f_t.push(Form { terms: q.terms, c: field::add(q.c, 1) });
        }
        fs.push(f_t);
    }
    let mut acc: Vec<Form> = fs.iter().map(|f| f[0].clone()).collect();
    for j in 1..ncls - 1 {
        for t in 0..m {
            acc[t] = r.mul(&acc[t], &fs[t][j])?;
        }
    }
    let mut oks = Form::default();
    for a in acc {
        oks.terms.extend(a.terms);
        oks.c = field::add(oks.c, a.c);
    }
    r.open(oks, Phase::Release)?;
    if prm.rc {
        r.append_range();
    }
    if prm.lb {
        r.append_lookup()?;
    }
    r.cons.shrink_to_fit();
    Ok(r)
}

/// cosnark_gates.lookup_bits_ops: the LB circuit for h alone over 8 placeholder atoms v_j (atoms 0..7): (its ops, the
/// placeholders, h as (form, const)). L (proof.md 23): the release MPC evaluates it on shares (run::release_mpc).
pub fn lookup_bits_ops(t_lo: i64) -> (Vec<LbOp>, Vec<u32>, (Vec<(u32, u64)>, u64)) {
    let q = t_lo.div_euclid(4);
    let mut rec = Rec::scratch(StepParams::HARNESS);
    let vph: Vec<u32> = (0..8).map(|_| rec.atom(Tag::Lq)).collect();
    let mut bx = Bits { rec: &mut rec, ops: Vec::new() };
    let v: Vec<u32> = (0..8)
        .map(|j| {
            let mut f = Lf::new();
            f.add(vph[j], 1);
            bx.atom(&f, 0)
        })
        .collect();
    let lo = bx.lt(&v[2..], -7 - q);
    let bf = bx.lt(&v[2..], 8 - q);
    let mut wf = Lf::new();
    for j in 0..6 {
        wf.add(v[2 + j], 1u64 << j);
    }
    let (wb, wl) = if !lo.0 .0.is_empty() || !bf.0 .0.is_empty() {
        let w = bx.atom(&wf, 0);
        (bx.mul(w, &bf), bx.mul(w, &lo))
    } else {
        let pick = |c: &(Lf, u64)| if c.1 != 0 { (wf.clone(), 0) } else { (Lf::new(), 0) };
        (pick(&bf), pick(&lo))
    };
    let one = (Lf::new(), 1u64);
    let (hf, hc) = addf(&[(1, &wb), (-1, &wl), (q - 7, &bf), (-(q + 7), &lo), (7, &one)]);
    let ops = bx.ops;
    (ops, vph, (hf.0.iter().map(|(&x, &c)| (x, c)).collect(), hc))
}

/// Beaver products of L's lookup by bits in the release MPC, per lookup: z1's chain to bit B = s1 + 8 (B - 1) and the
/// circuit's.
pub fn lookup_bits_products(prm: StepParams) -> usize {
    let (ops, _, _) = lookup_bits_ops(prm.t_lo);
    prm.s1 as usize + 7 + ops.iter().filter(|o| matches!(o, LbOp::Mul(..))).count()
}

/// A linear form over Prep atoms, merged and without zero coefficients (cosnark_gates' dict forms).
#[derive(Clone, Debug, Default)]
struct Lf(std::collections::BTreeMap<u32, u64>);

impl Lf {
    fn new() -> Lf {
        Lf::default()
    }
    fn add(&mut self, x: u32, c: u64) {
        let e = self.0.entry(x).or_insert(0);
        *e = field::add(*e, c);
        if *e == 0 {
            self.0.remove(&x);
        }
    }
}

/// sum co * (form, const), mod p (cosnark_gates._addf).
fn addf(terms: &[(i64, &(Lf, u64))]) -> (Lf, u64) {
    let mut f = Lf::new();
    let mut c = 0u64;
    for &(co, (fm, cc)) in terms {
        let co = field::from_i64(co);
        for (&x, &v) in fm.0.iter() {
            f.add(x, field::mul(co, v));
        }
        c = field::add(c, field::mul(co, *cc));
    }
    (f, c)
}

/// cosnark_gates._Bits: one lookup's circuit builder.
struct Bits<'a, 't> {
    rec: &'a mut Rec<'t>,
    ops: Vec<LbOp>,
}

impl Bits<'_, '_> {
    /// a fresh atom a = form + c, with its linear row a - form - c = 0
    fn atom(&mut self, form: &Lf, c: u64) -> u32 {
        let a = self.rec.atom(Tag::Lq);
        let mut f = Lf::new();
        f.add(a, 1);
        for (&x, &co) in form.0.iter() {
            f.add(x, field::neg(co));
        }
        let terms = f.0.iter().map(|(&x, &co)| (Atom::Prep(x), co)).collect();
        self.rec.cons.push(Con { form: Form { terms, c: field::neg(c) }, value: 0, phase: Phase::LookupBits, pos: usize::MAX });
        self.ops.push(LbOp::Lin(a, form.0.iter().map(|(&x, &co)| (x, co)).collect(), c));
        a
    }
    /// b v for an atom b: a constant or single-atom v costs one product; any other v is made an atom first
    fn mul(&mut self, b: u32, v: &(Lf, u64)) -> (Lf, u64) {
        let (form, c) = v;
        let mut out = Lf::new();
        if form.0.is_empty() {
            if *c != 0 {
                out.add(b, *c);
            }
            return (out, 0);
        }
        let (y, al, be) = if form.0.len() > 1 {
            (self.atom(form, *c), 1u64, 0u64)
        } else {
            let (&y, &al) = form.0.iter().next().unwrap();
            (y, al, *c)
        };
        let m = self.rec.atom(Tag::Lm);
        self.rec.had.push((b, y, m));
        self.ops.push(LbOp::Mul(m, b, y));
        out.add(m, al);
        if be != 0 {
            out.add(b, be);
        }
        (out, 0)
    }
    /// [value < c] for value = sum 2^i bits[i] and a public c (constants folded)
    fn lt(&mut self, bits: &[u32], c: i64) -> (Lf, u64) {
        let n = bits.len();
        if c <= 0 {
            return (Lf::new(), 0);
        }
        if c >= 1i64 << n {
            return (Lf::new(), 1);
        }
        let mut cur = (Lf::new(), 0u64);
        for (i, &b) in bits.iter().enumerate() {
            let (m, mc) = self.mul(b, &cur);
            if (c >> i) & 1 == 1 {
                let mut f = m.clone();
                f.add(b, field::p() - 1);
                cur = (f, field::add(1, mc));
            } else {
                let mut f = cur.0.clone();
                for (&x, &v) in m.0.iter() {
                    f.add(x, field::neg(v));
                }
                cur = (f, field::sub(cur.1, mc));
            }
        }
        cur
    }
}

/// spdz.taylor_shift: coefficients of P(X + c).
pub fn taylor_shift(coeffs: &[u64], c: u64) -> Vec<u64> {
    let mut a = coeffs.to_vec();
    let n = a.len();
    for i in 0..n {
        for k in (i..n.saturating_sub(1)).rev() {
            a[k] = field::add(a[k], field::mul(c, a[k + 1]));
        }
    }
    a
}

/// spdz.interpolate: coefficients of the degree < n polynomial with P(k) = values[k], k = 0..n-1.
pub fn interpolate(values: &[u64]) -> Vec<u64> {
    let n = values.len();
    let mut m = vec![1u64];
    for j in 0..n as u64 {
        // M(X) *= (X - j)
        let mut nm = vec![0u64; m.len() + 1];
        for (i, &c) in m.iter().enumerate() {
            nm[i + 1] = field::add(nm[i + 1], c);
            nm[i] = field::sub(nm[i], field::mul(j, c));
        }
        m = nm;
    }
    let mut coeffs = vec![0u64; n];
    for k in 0..n as u64 {
        let mut q = vec![0u64; n];
        let mut acc = 0u64;
        for i in (1..=n).rev() {
            acc = field::add(m[i], field::mul(acc, k));
            q[i - 1] = acc;
        }
        let mut qk = 0u64;
        for &c in q.iter().rev() {
            qk = field::add(field::mul(qk, k), c);
        }
        let scale = field::mul(values[k as usize], field::inv(qk));
        for i in 0..n {
            coeffs[i] = field::add(coeffs[i], field::mul(scale, q[i]));
        }
    }
    coeffs
}

/// mpc_fork.tables: the activation and its derivative on u in [-128, 128), interpolated.
pub fn tables() -> (Vec<u64>, Vec<u64>) {
    tables_for(-128)
}

/// The tables over [t_lo, t_lo + 256) (cosnark_he.Prog.tables; darkstep Program::tables).
pub fn tables_for(t_lo: i64) -> (Vec<u64>, Vec<u64>) {
    let sig = |u: i64| (u.div_euclid(4)).clamp(-7, 7);
    let dsig = |u: i64| if (-28..32).contains(&u) { 1 } else { 0 };
    let s: Vec<u64> = (0..256).map(|u| field::from_i64(sig(u + t_lo))).collect();
    let ds: Vec<u64> = (0..256).map(|u| field::from_i64(dsig(u + t_lo))).collect();
    (interpolate(&s), interpolate(&ds))
}

impl Rec<'_> {
    pub fn n_prep(&self) -> usize {
        self.tags.len()
    }
}
