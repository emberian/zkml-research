//! The step's wires as the prover consumes them (all parties' SPDZ shares, the middle's preprocessing atoms, the
//! public transcript and the ideal dealer's state after the step), loaded from research/.../darkproof_vectors.py's
//! JSON (until darkstep's native step feeds them directly), and the in-process bundle maker.
use crate::h::Hash;
use crate::ligero::LigParams;
use crate::middle;
use crate::net::{Nets, Transport};
use crate::owner::{self, Owner};
use crate::pcs::PcsParty;
use crate::rng::Det;
use crate::spdz::{Dealer, Sh, Spdz};
use crate::spine;
use crate::step::{self, StepParams};
use crate::wire;
use crate::{Ctx, Profile};
use serde_json::Value;
use std::collections::BTreeMap;

#[derive(Clone)]
pub struct Witness {
    pub d: usize,
    pub n: usize,
    pub alpha_sh: Vec<u64>,
    pub dealer_state: Vec<u64>,
    /// party -> name -> element share
    pub wires: Vec<BTreeMap<String, Vec<Sh>>>,
    pub public: Vec<u64>,
    /// party -> atom share (the middle's preprocessing atoms, in the replay's order)
    pub atoms: Vec<Vec<Sh>>,
}

fn u(v: &Value) -> u64 {
    v.as_u64().expect("u64")
}

fn shs(v: &Value) -> Vec<Sh> {
    v.as_array().unwrap().iter().map(|p| (u(&p[0]), u(&p[1]))).collect()
}

impl Witness {
    pub fn load(path: &std::path::Path) -> Self {
        let v: Value = serde_json::from_slice(&std::fs::read(path).expect("witness file")).expect("json");
        crate::field::set_p(u(&v["p"]));
        let n = u(&v["n"]) as usize;
        let wires = (0..n)
            .map(|i| {
                v["wires"]
                    .as_object()
                    .unwrap()
                    .iter()
                    .map(|(k, a)| (k.clone(), a.as_array().unwrap().iter().map(|e| shs(e)[i]).collect()))
                    .collect()
            })
            .collect();
        let atoms_all: Vec<Vec<Sh>> = v["atoms"].as_array().unwrap().iter().map(shs).collect();
        Witness {
            d: u(&v["d"]) as usize,
            n,
            alpha_sh: v["alpha_sh"].as_array().unwrap().iter().map(u).collect(),
            dealer_state: v["dealer_state"].as_array().unwrap().iter().map(u).collect(),
            wires,
            public: v["public"].as_array().unwrap().iter().map(u).collect(),
            atoms: (0..n).map(|i| atoms_all.iter().map(|a| a[i]).collect()).collect(),
        }
    }

    pub fn plain(&self, name: &str) -> Vec<u64> {
        let l = self.wires[0][name].len();
        (0..l).map(|k| self.wires.iter().fold(0, |a, w| crate::field::add(a, w[name][k].0))).collect()
    }
}

/// cosnark_zk.owner_commit: the owner deals vec as n additive shares and commits the share tuple; returns every
/// custodian's part.
pub fn owner_commit(pr: &Profile, vec: &[u64], label: &str, n: usize, det: &Det) -> Vec<PcsParty> {
    let mut rng = if det.on() { det.coins(&["owner-commit", label, &crate::h::h_list_hex(vec)]) } else { crate::rng::secret_coins() };
    let mut sh: Vec<Vec<u64>> = (0..n - 1).map(|_| vec.iter().map(|_| rng.randrange_u64(crate::field::p())).collect()).collect();
    let last: Vec<u64> =
        vec.iter().enumerate().map(|(c, &x)| sh.iter().fold(x, |a, s| crate::field::sub(a, s[c]))).collect();
    sh.push(last);
    (0..n).map(|i| PcsParty::commit(pr, &sh[i], label, i, det)).collect()
}

pub struct Bundle {
    pub blob: Vec<u8>,
    /// per party: the child commitments W1n, W2n (carried into the next step as W1, W2)
    pub child: Vec<BTreeMap<String, PcsParty>>,
    /// per party: the carried W1, W2 commitments after this proof (their life counters advanced)
    pub carried: Vec<BTreeMap<String, PcsParty>>,
    pub genesis_roots: Option<BTreeMap<String, Vec<Hash>>>,
    pub spine_violates: Option<String>,
    pub middle_violates: Option<String>,
    pub spine_stats: BTreeMap<String, u64>,
    pub middle_stats: BTreeMap<String, u64>,
    pub prove_secs: f64,
}

pub struct OwnerIn<'a> {
    pub owner: &'a mut Owner,
    pub x: Vec<u64>,
    pub y: Vec<u64>,
}

pub struct BundleOpts<'a> {
    pub pr: &'a Profile,
    pub lp: &'a LigParams,
    pub tables: &'a (Vec<u64>, Vec<u64>),
    pub det: Det,
    pub spine_attack: Option<&'a str>,
    /// fs_public_falsifier: shift the dead opening (the last mul f-opening) after gamma so the batch holds
    pub fs_public_attack: bool,
    pub diagnose: bool,
    pub transport: Transport,
    /// the step program (None: the harness's, StepParams::for_width(d))
    pub prm: Option<StepParams>,
}

/// run_proofwire.make_bundle with three custodian threads over the in-memory transport. carry: per party, the
/// previous step's child commitments (W1n, W2n), used as this step's W1, W2.
pub fn make_bundle(
    o: &BundleOpts,
    w: Witness,
    ctx: &Ctx,
    carry: Option<Vec<BTreeMap<String, PcsParty>>>,
    owner: Option<OwnerIn>,
) -> Result<Bundle, String> {
    let (pr, n, d) = (o.pr, w.n, w.d);
    let mut genesis_roots = None;
    let carry = match carry {
        Some(c) => c,
        None => {
            let g: Vec<BTreeMap<String, PcsParty>> = (0..n)
                .map(|i| {
                    let pw = &w.wires[i];
                    ["W1", "W2"]
                        .iter()
                        .map(|k| {
                            let s: Vec<u64> = pw[*k].iter().map(|x| x.0).collect();
                            (k.to_string(), PcsParty::commit(pr, &s, k, i, &o.det))
                        })
                        .collect()
                })
                .collect();
            genesis_roots = Some(
                ["W1", "W2"].iter().map(|k| (k.to_string(), g.iter().map(|m| m[*k].root).collect())).collect(),
            );
            g
        }
    };
    let (mut ox, mut oy, mut sig) = (None, None, None);
    if let Some(ow) = owner {
        let cx = owner_commit(pr, &ow.x, "xo", n, &o.det);
        let cy = owner_commit(pr, &ow.y, "yo", n, &o.det);
        let rx: Vec<Hash> = cx.iter().map(|c| c.root).collect();
        let ry: Vec<Hash> = cy.iter().map(|c| c.root).collect();
        sig = Some(ow.owner.sign(&owner::batch_message(ctx, &rx, &ry))?);
        ox = Some(cx);
        oy = Some(cy);
    }
    let prm = o.prm.unwrap_or(StepParams::for_width(d));
    let rec = step::replay(&w.public, d, prm, o.tables, prm.carried(ctx.step)).map_err(|_| "transcript short")?;
    assert_eq!(rec.tpos, w.public.len());
    // real runs: one secret stream per Ligero for the ideal dealer, the same for every party
    let (dl_s, dl_m) = if o.det.on() { (None, None) } else { (Some(crate::rng::secret_rng()), Some(crate::rng::secret_rng())) };
    // fs_public attack: the colluders' plaintext view and the patch they publish
    let jstar = rec.cons.iter().rposition(|c| c.phase == step::Phase::Mul).unwrap();
    let patched: std::sync::Mutex<Option<u64>> = std::sync::Mutex::new(None);
    let plain_vecs: BTreeMap<String, Vec<u64>> = if o.fs_public_attack {
        let (lens, _) = middle::public_shapes(pr, rec.n_prep(), rec.had.len(), d, false);
        let sum = |f: &dyn Fn(usize) -> Vec<Sh>| -> Vec<u64> {
            let v: Vec<Vec<Sh>> = (0..n).map(f).collect();
            (0..v[0].len()).map(|k| v.iter().fold(0, |a, x| crate::field::add(a, x[k].0))).collect()
        };
        let pvals = sum(&|i| w.atoms[i].clone());
        let mut m = BTreeMap::new();
        let pad = |mut x: Vec<u64>, l: usize| {
            x.resize(l, 0);
            x
        };
        m.insert("A".to_string(), pad(rec.had.iter().map(|t| pvals[t.0 as usize]).collect(), lens["A"]));
        m.insert("B".to_string(), pad(rec.had.iter().map(|t| pvals[t.1 as usize]).collect(), lens["B"]));
        m.insert("C".to_string(), pad(rec.had.iter().map(|t| pvals[t.2 as usize]).collect(), lens["C"]));
        m.insert("P".to_string(), pad(pvals, lens["P"]));
        for nm in step::NAMES {
            m.insert(nm.to_string(), pad(sum(&|i| w.wires[i][nm].clone()), lens[nm]));
        }
        m
    } else {
        BTreeMap::new()
    };
    let patch_fn = |q: &BTreeMap<String, Vec<u64>>, cst: u64, gam: &[u64]| -> u64 {
        let mut resid = cst;
        for (k, qq) in q {
            resid = crate::field::add(resid, crate::field::dot(qq, &plain_vecs[k]));
        }
        let dval = crate::field::mul(resid, crate::field::inv(gam[jstar]));
        *patched.lock().unwrap() = Some(dval);
        crate::field::sub(cst, crate::field::mul(gam[jstar], dval))
    };
    let patch_ref: Option<&(dyn Fn(&BTreeMap<String, Vec<u64>>, u64, &[u64]) -> u64 + Sync)> =
        if o.fs_public_attack { Some(&patch_fn) } else { None };
    let t0 = std::time::Instant::now();
    let nets = Nets::new(o.transport, n);
    let mut carry = carry;
    let public = w.public.clone();
    let (d, dealer_state, alpha_sh) = (w.d, w.dealer_state.clone(), w.alpha_sh.clone());
    let mut party_wires: Vec<Option<(BTreeMap<String, Vec<Sh>>, Vec<Sh>)>> =
        w.wires.into_iter().zip(w.atoms).map(Some).collect();
    let mut ox: Vec<Option<PcsParty>> = ox.map(|v| v.into_iter().map(Some).collect()).unwrap_or_else(|| (0..n).map(|_| None).collect());
    let mut oy: Vec<Option<PcsParty>> = oy.map(|v| v.into_iter().map(Some).collect()).unwrap_or_else(|| (0..n).map(|_| None).collect());
    let results: Vec<Result<_, String>> = std::thread::scope(|s| {
        let mut hs = Vec::new();
        for i in 0..n {
            let nets = &nets;
            let carry_i = std::mem::take(&mut carry[i]);
            let ox_i = ox[i].take();
            let oy_i = oy[i].take();
            let rec = &rec;
            let (dl_s, dl_m) = (dl_s.clone(), dl_m.clone());
            let (mut wires, atoms) = party_wires[i].take().unwrap();
            let (dealer_state, alpha_sh, public) = (&dealer_state, &alpha_sh, &public);
            hs.push(s.spawn(move || -> Result<_, String> {
                let mut net = nets.take(i);
                let mut sp = Spdz::new(i, n, Dealer::from_state(dealer_state, alpha_sh.clone()));
                let si = spine::SpineIn {
                    pr: o.pr,
                    lp: o.lp,
                    i,
                    n,
                    d,
                    wires: &wires,
                    ctx,
                    public,
                    det: &o.det,
                    attack: o.spine_attack,
                    lig_dealer: dl_s,
                    lig_tape: None,
                };
                let mut so = spine::prove(&si, &mut *net, &mut sp, carry_i, ox_i)?;
                for k in spine::MAT {
                    wires.remove(k); // the matrices are committed; the middle needs only the vectors
                }
                assert_eq!(sp.triples as usize, spine::beaver_count(d), "spine Beaver count");
                let child: BTreeMap<String, PcsParty> = [("W1", "W1n"), ("W2", "W2n")]
                    .iter()
                    .map(|(c, k)| (c.to_string(), so.coms.remove(*k).unwrap()))
                    .collect();
                let carried: BTreeMap<String, PcsParty> =
                    ["W1", "W2"].iter().map(|k| (k.to_string(), so.coms.remove(*k).unwrap())).collect();
                let spine_coms: BTreeMap<String, PcsParty> = middle::SPINE
                    .iter()
                    .map(|k| (k.to_string(), so.coms.remove(*k).unwrap()))
                    .collect();
                let mi = middle::MiddleIn {
                    pr: o.pr,
                    lp: o.lp,
                    i,
                    n,
                    d,
                    atoms: &atoms,
                    wires: &wires,
                    rec,
                    public,
                    ctx,
                    det: &o.det,
                    lig_dealer: dl_m,
                    lig_tape: None,
                    ignore_range: false,
                    cst_patch: patch_ref,
                };
                let mo = middle::prove(&mi, &mut *net, &mut sp, spine_coms, oy_i)?;
                assert_eq!(sp.triples as usize, spine::beaver_count(d) + rec.proof_products() + middle::beaver_count(rec.had.len()), "middle Beaver count");
                Ok((so, mo, child, carried))
            }));
        }
        hs.into_iter().map(|h| h.join().unwrap_or_else(|_| Err("party panicked".into()))).collect()
    });
    let prove_secs = t0.elapsed().as_secs_f64();
    let mut parts = Vec::new();
    for r in results {
        parts.push(r?);
    }
    for k in 1..n {
        assert!(parts[k].0.proof == parts[0].0.proof && parts[k].1.proof == parts[0].1.proof, "parties disagree on the proof");
    }
    let sum_rows = |rows: Vec<&Vec<Vec<u64>>>| -> Vec<Vec<u64>> {
        (0..rows[0].len())
            .map(|r| (0..rows[0][r].len()).map(|c| rows.iter().fold(0, |a, x| crate::field::add(a, x[r][c]))).collect())
            .collect()
    };
    let (spine_violates, middle_violates) = if o.diagnose {
        let sr = sum_rows(parts.iter().map(|p| &p.0.lig_rows).collect());
        let mr = sum_rows(parts.iter().map(|p| &p.1.lig_rows).collect());
        (
            crate::ligero::first_violated(&sr, &parts[0].0.sys, &parts[0].0.quad),
            crate::ligero::first_violated(&mr, &parts[0].1.sys, &parts[0].1.quad),
        )
    } else {
        (None, None)
    };
    let mut public = public;
    if let Some(dv) = *patched.lock().unwrap() {
        let tp = rec.cons[jstar].pos;
        public[tp] = crate::field::add(public[tp], dv);
    }
    let blob = wire::encode_step(
        pr,
        ctx,
        d,
        n,
        true,
        &parts[0].0.proof,
        &public,
        &parts[0].1.proof,
        rec.n_prep(),
        rec.had.len(),
        sig.as_deref(),
    );
    let spine_stats = parts[0].0.stats.clone();
    let middle_stats = parts[0].1.stats.clone();
    let mut child = Vec::new();
    let mut carried = Vec::new();
    for p in parts {
        child.push(p.2);
        carried.push(p.3);
    }
    Ok(Bundle {
        blob,
        child,
        carried,
        genesis_roots,
        spine_violates,
        middle_violates,
        spine_stats,
        middle_stats,
        prove_secs,
    })
}

pub fn clone_pcs(c: &PcsParty) -> PcsParty {
    PcsParty {
        label: c.label.clone(),
        shape: c.shape.clone(),
        ext: c.ext.clone(),
        salts: c.salts.clone(),
        tree: c.tree.clone(),
        root: c.root,
        opened_lives: c.opened_lives,
        max_lives: c.max_lives,
    }
}

/// Per-party carry maps with every commitment's life cap set (colluding custodians bypass their counters).
pub fn with_max_lives(mut c: Vec<BTreeMap<String, PcsParty>>, max: usize) -> Vec<BTreeMap<String, PcsParty>> {
    for m in c.iter_mut() {
        for p in m.values_mut() {
            p.max_lives = max;
        }
    }
    c
}

pub fn clone_carry(c: &[BTreeMap<String, PcsParty>]) -> Vec<BTreeMap<String, PcsParty>> {
    c.iter().map(|m| m.iter().map(|(k, p)| (k.clone(), clone_pcs(p))).collect()).collect()
}
