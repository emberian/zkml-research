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
    /// public constant added to b * g1 before its truncation (step_spec.Program.R3; 0 floors)
    pub r3: i64,
    /// the table's domain is [t_lo, t_lo + 256) (step_spec.Program.T_LO; the harness's -128)
    pub t_lo: i64,
}

impl StepParams {
    /// The harness's step (step_spec S1, S2, S3 = 5, 4, 8; run_step's K = 13, 8, 13).
    pub const HARNESS: StepParams = StepParams { s1: 5, k1: 13, s2: 4, k2: 8, s3: 8, k3: 13, he: false, r3: 0, t_lo: -128 };
    /// The d = 4096 shifts of the decision doc's count formulas (§12; cosnark_gates.counts_formula at width).
    pub const WIDE: StepParams = StepParams { s1: 11, k1: 19, s2: 4, k2: 8, s3: 14, k3: 19, he: false, r3: 0, t_lo: -128 };
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
        self.he && step > 1
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
}

/// The middle's external vectors for a program other than the step (cosnark_gates_zk.IO): name and padded length,
/// the carried ones (an existing commitment at its second life), and the transcript label.
#[derive(Clone, Debug)]
pub struct Io {
    pub lens: Vec<(&'static str, usize)>,
    pub carried: Vec<&'static str>,
    pub label: &'static str,
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
}

pub struct Rec<'t> {
    pub prm: StepParams,
    pub d: usize,
    pub tags: Vec<Tag>,
    pub cons: Vec<Con>,
    pub had: Vec<(u32, u32, u32)>,
    transcript: &'t [u64],
    pub tpos: usize,
    tables: (Vec<u64>, Vec<u64>),
    /// the external vectors' names (Atom::Ext indexes this): NAMES for the step
    pub names: Vec<&'static str>,
    pub io: Option<Io>,
    pub pubmat: Option<PubMat>,
}

#[derive(Debug)]
pub enum Short {
    /// the transcript ends before the program does
    Short,
    /// a deployed step's he_outer_commit entry is not 0 (cosnark_he.SymOuter)
    Commit,
}

fn neg_form(f: &Form) -> Vec<(Atom, u64)> {
    f.terms.iter().map(|&(a, c)| (a, field::neg(c))).collect()
}

impl<'t> Rec<'t> {
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
        let r = self.atom(Tag::Tr);
        let bits: Vec<u32> = (0..s)
            .map(|_| {
                let b = self.atom(Tag::Trb);
                self.had.push((b, b, b));
                b
            })
            .collect();
        let rhi = self.atom(Tag::Trh);
        let nb = k + KAPPA - s;
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
        let mut f = vec![(Atom::Prep(rhi), 1)];
        for (j, &b) in hb.iter().enumerate() {
            f.push((Atom::Prep(b), field::neg(field::pow(2, j as u64))));
        }
        self.cons.push(Con { form: Form { terms: f, c: 0 }, value: 0, phase: Phase::TrhRange, pos: usize::MAX });
        let mut fo = x.terms.clone();
        fo.push((Atom::Prep(r), 1));
        let c = self.open(Form { terms: fo, c: field::add(x.c, 1u64 << k) }, Phase::Trunc)?;
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
    fn lookup2(&mut self, u: &Form, offset: u64) -> Result<(Form, Form), Short> {
        let deg = 255usize;
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
        cons: Vec::new(),
        had: Vec::new(),
        transcript,
        tpos: 0,
        tables: tables.clone(),
        names: NAMES.to_vec(),
        io: None,
        pubmat: None,
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
        u1.push(r.trunc(z, prm.s1, prm.k1)?);
    }
    let mut h = Vec::with_capacity(d);
    let mut g1 = Vec::with_capacity(d);
    for u in &u1 {
        let (a, b) = r.lookup2(u, field::from_i64(-prm.t_lo))?;
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
        let t = r.trunc(z, prm.s1, prm.k1)?;
        let mut terms = t.terms;
        terms.extend(neg_form(yy));
        e.push(Form { terms, c: field::sub(t.c, yy.c) });
    }
    let mut d2 = Vec::with_capacity(d);
    for v in &e {
        d2.push(r.trunc(v, prm.s2, prm.k2)?);
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
        d1.push(r.trunc(&v, prm.s3, prm.k3)?);
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
        cons: Vec::new(),
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
        u1.push(r.trunc(z, prm.s1, prm.k1)?);
    }
    let off = field::from_i64(-prm.t_lo);
    let mut h = Vec::with_capacity(d * m);
    for u in &u1 {
        h.push(r.lookup2(u, off)?.0);
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
            row.push(r.trunc(&sums[c * m + t], prm.s1, prm.k1)?);
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
            let q = r.trunc(&diff, kc, kc)?;
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
    Ok(r)
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
