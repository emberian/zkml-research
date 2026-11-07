//! The step's wires as the prover consumes them (all parties' SPDZ shares, the middle's preprocessing atoms, the
//! public transcript and the ideal dealer's state after the step), loaded from research/.../darkproof_vectors.py's
//! JSON (until darkstep's native step feeds them directly), and the in-process bundle maker.
use crate::h::Hash;
use crate::ligero::LigParams;
use crate::middle;
use crate::net::mem_mesh;
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
        assert_eq!(u(&v["p"]), crate::field::P);
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
    let mut rng = match det.on() {
        true => det.rng(&["owner-commit", label, &crate::h::h_list_hex(vec)]).unwrap(),
        false => crate::rng::secret_rng(),
    };
    let mut sh: Vec<Vec<u64>> = (0..n - 1).map(|_| vec.iter().map(|_| rng.randrange_u64(crate::field::P)).collect()).collect();
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
    pub diagnose: bool,
}

/// run_proofwire.make_bundle with three custodian threads over the in-memory transport. carry: per party, the
/// previous step's child commitments (W1n, W2n), used as this step's W1, W2.
pub fn make_bundle(
    o: &BundleOpts,
    w: &Witness,
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
    let rec = step::replay(&w.public, d, StepParams::for_width(d), o.tables).map_err(|_| "transcript short")?;
    assert_eq!(rec.tpos, w.public.len());
    // real runs: one secret stream per Ligero for the ideal dealer, the same for every party
    let (dl_s, dl_m) = if o.det.on() { (None, None) } else { (Some(crate::rng::secret_rng()), Some(crate::rng::secret_rng())) };
    let t0 = std::time::Instant::now();
    let nets = mem_mesh(n);
    let mut carry = carry;
    let mut ox: Vec<Option<PcsParty>> = ox.map(|v| v.into_iter().map(Some).collect()).unwrap_or_else(|| (0..n).map(|_| None).collect());
    let mut oy: Vec<Option<PcsParty>> = oy.map(|v| v.into_iter().map(Some).collect()).unwrap_or_else(|| (0..n).map(|_| None).collect());
    let results: Vec<Result<_, String>> = std::thread::scope(|s| {
        let mut hs = Vec::new();
        for (i, mut net) in nets.into_iter().enumerate() {
            let carry_i = std::mem::take(&mut carry[i]);
            let ox_i = ox[i].take();
            let oy_i = oy[i].take();
            let rec = &rec;
            let (dl_s, dl_m) = (dl_s.clone(), dl_m.clone());
            hs.push(s.spawn(move || -> Result<_, String> {
                let wires = &w.wires[i];
                let atoms = &w.atoms[i];
                let mut sp = Spdz::new(i, n, Dealer::from_state(&w.dealer_state, w.alpha_sh.clone()));
                let si = spine::SpineIn {
                    pr: o.pr,
                    lp: o.lp,
                    i,
                    n,
                    d,
                    wires,
                    ctx,
                    public: &w.public,
                    det: &o.det,
                    attack: o.spine_attack,
                    lig_dealer: dl_s,
                };
                let mut so = spine::prove(&si, &mut net, &mut sp, carry_i, ox_i)?;
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
                    atoms,
                    wires,
                    rec,
                    public: &w.public,
                    ctx,
                    det: &o.det,
                    lig_dealer: dl_m,
                };
                let mo = middle::prove(&mi, &mut net, &mut sp, spine_coms, oy_i)?;
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
    let blob = wire::encode_step(
        pr,
        ctx,
        d,
        n,
        true,
        &parts[0].0.proof,
        &w.public,
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
