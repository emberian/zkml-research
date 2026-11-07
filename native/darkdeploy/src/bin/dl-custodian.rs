//! dl-custodian: `darkstep serve` with the per-step collaborative proof inside the custodian process.
//!
//!   dl-custodian serve <darkstep serve arguments> [--prove] [--model NAME]
//! With --prove, after each accepted step k this custodian runs its share of the proof of step k + 1 (ledger counter)
//! over the same TLS mesh (tag PROOF), from its own ProofRecord, its new weight shares and its tape's proof section
//! (the darkproof::run::tape_triples(..) triples right after the step), then moves its tape cursor past them. Every
//! custodian ends with the same bundle; custodian 0 also verifies it as the ledger would (darkproof::wire::verify_step
//! against the parent roots: the genesis roots at step 1, then each accepted step's child roots) and keeps the chain.
//! Files: DIR/proof_step<k>_P<I>.bin; custodian 0: DIR/genesis_roots.json, DIR/proof_chain.json.
use darkproof::step::StepParams;
use darkstep::serve::{CustodianState, StepHook};
use darkstep::step::{Program, ProofRecord};
use serde_json::json;
use std::collections::BTreeMap;

struct Prove {
    model: String,
    pr: darkproof::Profile,
    lp: darkproof::ligero::LigParams,
    tables: (Vec<u64>, Vec<u64>),
    prm: StepParams,
    carry: Option<BTreeMap<String, darkproof::pcs::PcsParty>>,
    parent: Option<BTreeMap<String, Vec<darkproof::h::Hash>>>,
    chain: Vec<serde_json::Value>,
}

fn params_of(pg: &Program) -> StepParams {
    StepParams { s1: pg.s1, k1: pg.k1, s2: pg.s2, k2: pg.k2, s3: pg.s3, k3: pg.k3, he: false, rc: true, lb: true, pg: None, r3: pg.r3, t_lo: pg.t_lo }.deployed()
}

impl StepHook for Prove {
    fn after_step(&mut self, st: &mut CustodianState, k: usize, rec: &ProofRecord, dir: &std::path::Path) -> Result<serde_json::Value, String> {
        let (i, d) = (st.i, st.pf.d);
        let step = k as u64 + 1;
        let carried = self.prm.carried(step);
        let own;
        let tb = if self.prm.t_lo == -128 { &self.tables } else { own = darkproof::step::tables_for(self.prm.t_lo); &own };
        let count = darkproof::run::step_section(&self.lp, d, self.prm, carried, tb);
        let (w1n, w2n) = st.w.as_ref().ok_or("no weights")?;
        let ps = darkproof::run::from_darkstep_n(i, d, rec, w1n, w2n, &st.pt.tape, Some(count), darkproof::rng::Det::off())?;
        let ctx = darkproof::Ctx::new(&self.model, 0, step);
        let t0 = std::time::Instant::now();
        let sp = darkproof::run::prove_step(&self.pr, &self.lp, &self.tables, self.prm, &mut darkproof::run::TcpRef(&st.pt.net), &ctx, ps, self.carry.take())?;
        let prove_s = t0.elapsed().as_secs_f64();
        st.pt.cur = rec.tape_cursor + 3 * count;
        self.carry = Some(sp.child);
        std::fs::write(dir.join(format!("proof_step{k}_P{i}.bin")), &sp.blob).map_err(|e| e.to_string())?;
        use sha2::{Digest, Sha256};
        let digest = pycompat::repr::hex(&Sha256::digest(&sp.blob));
        if k == 0 && i == 0 && sp.genesis_roots.is_none() {
            if let Some(g) = &self.parent {
                let enc: BTreeMap<&String, Vec<String>> = g.iter().map(|(k, v)| (k, v.iter().map(|h| pycompat::repr::hex(h)).collect())).collect();
                std::fs::write(dir.join("genesis_roots.json"), serde_json::to_string_pretty(&enc).unwrap()).map_err(|e| e.to_string())?;
            }
        }
        let mut out = json!({"proof_seconds": prove_s, "proof_bytes": sp.blob.len(), "proof_sha256": digest,
            "proof_field_elements_sent": sp.sent, "proof_triples": count});
        if let Some(g) = &sp.genesis_roots {
            self.parent = Some(g.clone());
            if i == 0 {
                let enc: BTreeMap<&String, Vec<String>> = g.iter().map(|(k, v)| (k, v.iter().map(|h| pycompat::repr::hex(h)).collect())).collect();
                std::fs::write(dir.join("genesis_roots.json"), serde_json::to_string_pretty(&enc).unwrap()).map_err(|e| e.to_string())?;
            }
        }
        // every custodian checks the bundle as the ledger would; all three hold the same bytes
        let tv = std::time::Instant::now();
        let parent = self.parent.as_ref().ok_or("no parent roots")?;
        let acc = darkproof::wire::verify_step(&self.pr, &self.lp, &sp.blob, &ctx, parent, &self.tables, d, self.prm, None, 0)?;
        out["verify_seconds"] = json!(tv.elapsed().as_secs_f64());
        out["verified"] = json!(true);
        self.parent = Some(acc.child);
        self.chain.push(json!({"step": step, "proof_sha256": digest}));
        if i == 0 {
            std::fs::write(dir.join("proof_chain.json"), serde_json::to_string_pretty(&self.chain).unwrap()).map_err(|e| e.to_string())?;
        }
        Ok(out)
    }
}

/// --genesis-cfg CFG.json: the public genesis W = darktrain::init(cfg) (public by design: a committed genesis file
/// with a public seed). Otherwise darkstep's --genesis-public FILE, or an owner-input genesis.
fn genesis_of(args: &[String]) -> Option<(Vec<i64>, Vec<i64>)> {
    if let Some(f) = darkstep::node::flag(args, "--genesis-cfg") {
        let c: darktrain::Cfg = serde_json::from_str(&std::fs::read_to_string(&f).expect("genesis cfg")).expect("cfg json");
        c.validate().expect("cfg");
        return Some(darktrain::init(&c));
    }
    darkstep::node::flag(args, "--genesis-public").map(|f| {
        let b = std::fs::read(&f).unwrap();
        let v: Vec<i64> = b.chunks_exact(8).map(|c| i64::from_le_bytes(c.try_into().unwrap())).collect();
        let h = v.len() / 2;
        (v[..h].to_vec(), v[h..].to_vec())
    })
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.get(1).map(|s| s.as_str()) == Some("proof-triples") {
        // dl-custodian proof-triples N L F d [--program P]: the proof section's size after a genesis and a carried step
        let pf = darkstep::node::prof(&args[2..6]);
        darkproof::field::set_p(pf.t);
        let lp = darkproof::Profile::ledger().ligero();
        let tables = darkproof::step::tables();
        let prm = params_of(&darkstep::serve::program_of(&args));
        let own;
        let tb = if prm.t_lo == -128 { &tables } else { own = darkproof::step::tables_for(prm.t_lo); &own };
        let g = darkproof::run::step_section(&lp, pf.d, prm, false, tb);
        let c = darkproof::run::step_section(&lp, pf.d, prm, true, tb);
        println!("{g},{c}");
        return;
    }
    if args.get(1).map(|s| s.as_str()) != Some("serve") {
        eprintln!("usage: dl-custodian serve <darkstep serve arguments> [--prove] [--model NAME]");
        std::process::exit(2);
    }
    if args.iter().any(|a| a == "--prove") {
        let pf = darkstep::node::prof(&args[3..7]);
        darkproof::field::set_p(pf.t);
        let pr = darkproof::Profile::ledger();
        let lp = pr.ligero();
        let program = darkstep::serve::program_of(&args);
        // public genesis: the program pins sha256 of the genesis cfg; every custodian commits the public W itself
        // (identical roots), and that commitment is the parent of step 1
        let gcfg = darkstep::node::flag(&args, "--genesis-cfg").map(|f| std::fs::read(f).expect("genesis cfg"));
        let mut prm = params_of(&program);
        let mut carry = None;
        let mut parent = None;
        if let Some(b) = &gcfg {
            use sha2::{Digest, Sha256};
            prm.pg = Some(Sha256::digest(b).into());
            let (gd, w1, w2) = darkproof::run::public_weights(b).expect("genesis cfg");
            assert_eq!(gd, pf.d, "the genesis cfg's d");
            let i: usize = args[2].parse().unwrap();
            let (c, roots) = darkproof::run::public_genesis(&pr, pf.d, i, &w1, &w2, 3);
            carry = Some(c);
            parent = Some(roots);
        }
        let mut hook = Prove {
            model: darkstep::node::flag(&args, "--model").unwrap_or_else(|| "dl-gen6".into()),
            lp,
            pr,
            tables: darkproof::step::tables(),
            prm,
            carry,
            parent,
            chain: vec![],
        };
        std::process::exit(darkstep::serve::serve_main_with(&args, &mut hook, genesis_of(&args)));
    }
    std::process::exit(darkstep::serve::serve_main_with(&args, &mut darkstep::serve::NoHook, genesis_of(&args)));
}
