//! proofwire.Ledger: durable acceptance, one append-only JSON-lines file per model, written byte-for-byte as
//! Python's json.dumps writes it (so either implementation reopens the other's file). genesis pins model, d, the
//! profile, the owner key (or "none"), the custodian set and the genesis W commitment; step and rotate records
//! follow. A torn or out-of-sequence line fails closed; accept holds an exclusive lock and re-reads the head.
use crate::h::{hex, unhex32, Hash};
use crate::ligero::LigParams;
use crate::wire;
use crate::{Ctx, Profile};
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::io::Write;
use std::path::{Path, PathBuf};

/// json.dumps(str) with ensure_ascii.
pub fn jstr(s: &str) -> String {
    let mut o = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            '\n' => o.push_str("\\n"),
            '\r' => o.push_str("\\r"),
            '\t' => o.push_str("\\t"),
            '\u{08}' => o.push_str("\\b"),
            '\u{0c}' => o.push_str("\\f"),
            c if (c as u32) < 0x20 || (c as u32) > 0x7e => {
                let mut b = [0u16; 2];
                for u in c.encode_utf16(&mut b) {
                    o.push_str(&format!("\\u{:04x}", u));
                }
            }
            c => o.push(c),
        }
    }
    o.push('"');
    o
}

fn jroots(r: &BTreeMap<String, Vec<Hash>>) -> String {
    let items: Vec<String> = ["W1", "W2"]
        .iter()
        .map(|k| {
            let hs: Vec<String> = r[*k].iter().map(|h| jstr(&hex(h))).collect();
            format!("{}: [{}]", jstr(k), hs.join(", "))
        })
        .collect();
    format!("{{{}}}", items.join(", "))
}

fn jlist(xs: &[String]) -> String {
    format!("[{}]", xs.iter().map(|s| jstr(s)).collect::<Vec<_>>().join(", "))
}

/// PARAMS as json.dumps writes the dict (insertion order of proofwire.PROFILES).
pub fn jparams(p: &Profile) -> String {
    format!(
        "{{\"PROFILE\": {}, \"HE\": {{\"N\": {}, \"L\": {}, \"F_BITS\": {}}}, \"HIDE\": {}, \"NMASK\": {}, \"LIVES\": {}, \"T_COLS\": {}, \"BLOW\": {}, \"K_L\": {}, \"T_HIDE\": {}, \"T_OPEN\": {}, \"OWNER_H\": {}}}",
        jstr(p.name), p.he.0, p.he.1, p.he.2, p.hide, p.nmask, p.lives, p.t_cols, p.blow, p.k_l, p.t_hide, p.t_open, p.owner_h
    )
}

fn roots_of(v: &Value) -> Result<BTreeMap<String, Vec<Hash>>, String> {
    let o = v.as_object().ok_or("roots")?;
    let mut out = BTreeMap::new();
    for k in ["W1", "W2"] {
        let a = o.get(k).and_then(|a| a.as_array()).ok_or("roots")?;
        out.insert(
            k.to_string(),
            a.iter().map(|h| h.as_str().and_then(unhex32).ok_or("root hex")).collect::<Result<_, _>>()?,
        );
    }
    Ok(out)
}

pub struct Ledger {
    pub path: PathBuf,
    pub model: String,
    pub pr: Profile,
    recs: Vec<Value>,
    pub d: usize,
    /// the step program the ledger's verifier replays (pinned in genesis when it is not the harness's)
    pub program: crate::step::StepParams,
    pub owner_pk: Option<Hash>,
    pub epoch: u64,
    pub step: u64,
    pub parent: BTreeMap<String, Vec<Hash>>,
    pub next_leaf: u64,
    pub custodians: Vec<String>,
    /// the mind's release was accepted: the head's commitments have no life left, so the ledger takes no further
    /// step or rotation
    pub released: Option<(u64, u64)>,
    /// the genesis record's roots
    pub genesis_roots: BTreeMap<String, Vec<Hash>>,
    /// public genesis (program.pg): the roots this process recomputed from the cfg (check_public_genesis). Until
    /// they equal the genesis record's, the ledger accepts nothing (fail closed).
    pg_verified: Option<BTreeMap<String, Vec<Hash>>>,
}

pub struct Genesis {
    pub d: usize,
    pub program: crate::step::StepParams,
    pub owner_pk: Option<Hash>,
    pub custodians: Vec<String>,
    pub roots: BTreeMap<String, Vec<Hash>>,
}

fn append(path: &Path, line: &str, new: bool) -> Result<(), String> {
    let mut f = std::fs::OpenOptions::new().create(true).append(true).open(path).map_err(|e| e.to_string())?;
    f.write_all(line.as_bytes()).and_then(|_| f.write_all(b"\n")).map_err(|e| e.to_string())?;
    f.flush().map_err(|e| e.to_string())?;
    f.sync_all().map_err(|e| e.to_string())?;
    if new {
        let dir = std::fs::canonicalize(path).map_err(|e| e.to_string())?;
        let dir = dir.parent().unwrap();
        std::fs::File::open(dir).and_then(|d| d.sync_all()).map_err(|e| e.to_string())?;
    }
    Ok(())
}

impl Ledger {
    pub fn open(path: &Path, model: &str, pr: &Profile, genesis: Option<Genesis>) -> Result<Self, String> {
        // the context is hashed as a Python repr; native ports that exactly for printable ASCII only
        if model.is_empty() || model.len() > 64 || !model.bytes().all(|b| (0x20..0x7f).contains(&b)) {
            return Err("model ids are 1..64 printable ASCII characters".into());
        }
        if !path.exists() {
            let g = genesis.ok_or("a new ledger needs its genesis record")?;
            // the harness's program is implied (Python's genesis records carry none); any other is pinned
            let prog = if g.program == crate::step::StepParams::HARNESS {
                String::new()
            } else {
                let p = g.program;
                let he = match (p.he, p.rc) {
                    (true, true) => ", \"he\": true, \"RC\": true",
                    (true, false) => ", \"he\": true",
                    (false, true) => ", \"RC\": true",
                    (false, false) => "",
                };
                let ext = if (p.r3, p.t_lo) != (0, -128) { format!(", \"R3\": {}, \"T_LO\": {}", p.r3, p.t_lo) } else { String::new() };
                let mut more = String::new();
                if p.lb {
                    more.push_str(", \"LB\": true");
                }
                if let Some(h) = p.pg {
                    more.push_str(&format!(", \"PG\": \"{}\"", crate::h::hex(&h)));
                }
                format!(", \"program\": {{\"S1\": {}, \"K1\": {}, \"S2\": {}, \"K2\": {}, \"S3\": {}, \"K3\": {}{}{}{}}}", p.s1, p.k1, p.s2, p.k2, p.s3, p.k3, ext, he, more)
            };
            let line = format!(
                "{{\"kind\": \"genesis\", \"model\": {}, \"d\": {}, \"params\": {}, \"owner_pk\": {}, \"custodians\": {}, \"roots\": {}{}}}",
                jstr(model),
                g.d,
                jparams(pr),
                jstr(&g.owner_pk.map(|k| hex(&k)).unwrap_or_else(|| "none".into())),
                jlist(&g.custodians),
                jroots(&g.roots),
                prog
            );
            append(path, &line, true)?;
        }
        let mut l = Ledger {
            path: path.to_path_buf(),
            model: model.to_string(),
            pr: pr.clone(),
            recs: vec![],
            d: 0,
            program: crate::step::StepParams::HARNESS,
            owner_pk: None,
            epoch: 0,
            step: 0,
            parent: BTreeMap::new(),
            next_leaf: 0,
            custodians: vec![],
            released: None,
            genesis_roots: BTreeMap::new(),
            pg_verified: None,
        };
        l.reload()?;
        Ok(l)
    }

    fn reload(&mut self) -> Result<(), String> {
        let text = std::fs::read_to_string(&self.path).map_err(|e| e.to_string())?;
        self.recs.clear();
        for (no, line) in text.lines().enumerate() {
            let v: Value = serde_json::from_str(line).map_err(|_| {
                format!("ledger {}: line {} is not a complete record (fail closed)", self.path.display(), no + 1)
            })?;
            self.recs.push(v);
        }
        let g = self.recs.first().ok_or("ledger genesis record missing")?;
        let want: Value = serde_json::from_str(&jparams(&self.pr)).unwrap();
        if g["kind"] != "genesis" || g["model"] != self.model.as_str() || g["params"] != want {
            return Err("ledger genesis record missing, for another model, or with other parameters".into());
        }
        self.replay()
    }

    fn replay(&mut self) -> Result<(), String> {
        let g = &self.recs[0];
        self.d = g["d"].as_u64().ok_or("d")? as usize;
        self.program = match g.get("program") {
            None => crate::step::StepParams::HARNESS,
            Some(p) => {
                let f = |k: &str| p[k].as_u64().map(|v| v as u32).ok_or("genesis program");
                let he = match p.get("he") {
                    None => false,
                    Some(Value::Bool(b)) => *b,
                    Some(_) => return Err("genesis program: he must be a boolean".into()),
                };
                let gi = |k: &str, dflt: i64| -> Result<i64, String> {
                    match p.get(k) {
                        None => Ok(dflt),
                        Some(v) => v.as_i64().ok_or_else(|| format!("genesis program: {k}")),
                    }
                };
                crate::step::StepParams { s1: f("S1")?, k1: f("K1")?, s2: f("S2")?, k2: f("K2")?, s3: f("S3")?, k3: f("K3")?, he, rc: match p.get("RC") {
                    None => false,
                    Some(Value::Bool(b)) => *b,
                    Some(_) => return Err("genesis program: RC must be a boolean".into()),
                }, r3: gi("R3", 0)?, t_lo: gi("T_LO", -128)?, lb: match p.get("LB") {
                    None => false,
                    Some(Value::Bool(b)) => *b,
                    Some(_) => return Err("genesis program: LB must be a boolean".into()),
                }, pg: match p.get("PG") {
                    None => None,
                    Some(v) => Some(v.as_str().and_then(unhex32).ok_or("genesis program: PG must be a sha256 hex")?),
                } }
            }
        };
        let pk = g["owner_pk"].as_str().ok_or("owner_pk")?;
        self.owner_pk = if pk == "none" { None } else { Some(unhex32(pk).ok_or("owner_pk hex")?) };
        self.epoch = 0;
        self.step = 0;
        self.parent = roots_of(&g["roots"])?;
        self.genesis_roots = self.parent.clone();
        self.next_leaf = 0;
        self.released = None;
        self.custodians =
            g["custodians"].as_array().ok_or("custodians")?.iter().map(|c| c.as_str().unwrap_or("").to_string()).collect();
        for (no, rec) in self.recs[1..].iter().enumerate() {
            let no = no + 2;
            if self.released.is_some() {
                return Err(format!("ledger line {no}: a record after the release (fail closed)"));
            }
            match rec["kind"].as_str() {
                Some("release") => {
                    if (rec["epoch"].as_u64(), rec["step"].as_u64()) != (Some(self.epoch), Some(self.step)) {
                        return Err(format!("ledger line {no}: the release is not at the head (fail closed)"));
                    }
                    match (rec["M"].as_u64(), rec["C"].as_u64()) {
                        (Some(m), Some(c)) if c <= m => self.released = Some((m, c)),
                        _ => return Err(format!("ledger line {no}: release record malformed (fail closed)")),
                    }
                }
                Some("step") => {
                    if (rec["epoch"].as_u64(), rec["step"].as_u64()) != (Some(self.epoch), Some(self.step + 1)) {
                        return Err(format!("ledger line {no} breaks the sequence (fail closed)"));
                    }
                    self.step += 1;
                    self.parent = roots_of(&rec["child"])?;
                    // the anti-reuse counter: an owner-bound ledger needs an integer leaf above the last one, in
                    // the owner tree; an unbound one needs null (codex review, finding 5)
                    match (self.owner_pk.is_some(), &rec["leaf"]) {
                        (false, Value::Null) => {}
                        (true, l) if l.as_u64().is_some_and(|l| l >= self.next_leaf && l < 1 << self.pr.owner_h) => {
                            self.next_leaf = l.as_u64().unwrap() + 1;
                        }
                        _ => return Err(format!("ledger line {no}: step record's owner leaf is malformed (fail closed)")),
                    }
                }
                Some("rotate") => {
                    if rec["epoch"].as_u64() != Some(self.epoch + 1) {
                        return Err(format!("ledger line {no}: rotation out of order (fail closed)"));
                    }
                    self.epoch += 1;
                    self.custodians = rec["custodians"]
                        .as_array()
                        .ok_or("custodians")?
                        .iter()
                        .map(|c| c.as_str().unwrap_or("").to_string())
                        .collect();
                    self.parent = roots_of(&rec["roots"])?;
                }
                _ => return Err(format!("ledger line {no}: unknown record kind (fail closed)")),
            }
        }
        Ok(())
    }

    pub fn head(&self) -> (Ctx, BTreeMap<String, Vec<Hash>>) {
        (Ctx::new(&self.model, self.epoch, self.step + 1), self.parent.clone())
    }

    fn lock(&self) -> Result<std::fs::File, String> {
        let f = std::fs::File::open(&self.path).map_err(|e| e.to_string())?;
        f.lock().map_err(|e| e.to_string())?;
        Ok(f)
    }

    /// Custody rotation. Refused until the handover verifier (research/.../handover.py) is ported: a rotation
    /// record with no verified handover would let a caller replace the model's weights (codex review, finding 1).
    /// Ledger.handover_context: the context a handover to `custodians` after the head must be proved under.
    pub fn handover_context(&self, custodians: &[String]) -> crate::handover::HandoverCtx {
        crate::handover::HandoverCtx {
            model: self.model.clone(),
            epoch_old: self.epoch,
            epoch_new: self.epoch + 1,
            after_step: self.step,
            old_set: self.custodians.clone(),
            new_set: custodians.to_vec(),
        }
    }

    /// Custody rotation (proofwire.Ledger.rotate): accepted only with the bytes of a handover proof that the new
    /// committee's roots commit the same weights as the head's; the record carries sha256 of those bytes. Every
    /// refusal is "rotation refused: <reason>", the reason equal to Python's.
    pub fn rotate(&mut self, custodians: &[String], new_roots: &BTreeMap<String, Vec<Hash>>, handover: &[u8]) -> Result<(), String> {
        let _l = self.lock()?;
        self.reload()?;
        if self.released.is_some() {
            return Err("rotation refused: the ledger is released".into());
        }
        if handover.is_empty() {
            return Err("rotation refused: no handover proof".into());
        }
        let lp = self.pr.ligero();
        let ctx = self.handover_context(custodians);
        let got = crate::handover::verify(&self.pr, &lp, self.d, self.custodians.len(), custodians.len(), &ctx, &self.parent, handover)
            .map_err(|e| format!("rotation refused: {e}"))?;
        if &got != new_roots {
            return Err("rotation refused: the handover proof is for other new roots".into());
        }
        let line = format!(
            "{{\"kind\": \"rotate\", \"epoch\": {}, \"custodians\": {}, \"roots\": {}, \"handover_proof\": {}}}",
            self.epoch + 1,
            jlist(custodians),
            jroots(new_roots),
            jstr(&hex(&Sha256::digest(handover)))
        );
        append(&self.path, &line, false)?;
        self.reload()
    }

    /// The mind's release (proofwire.Ledger.release): verified against the head's W1, W2 roots and the published
    /// policy; the record carries M, C, sha256 of the bundle and of the policy. Terminal: the head's commitments were
    /// opened at their last life.
    pub fn release(&mut self, lp: &LigParams, blob: &[u8], pol: &crate::run::Policy) -> Result<(usize, u64), String> {
        let _l = self.lock()?;
        self.reload()?;
        self.pg_gate()?;
        if self.released.is_some() {
            return Err("the ledger is released: no further release".into());
        }
        if self.step == 0 {
            return Err("no step accepted: nothing to release".into());
        }
        let ctx = Ctx::new(&self.model, self.epoch, self.step);
        let (m, c) = wire::verify_release(&self.pr, lp, blob, &ctx, &self.parent, &pol.x, &pol.labels, self.program, pol.ncls, self.d, pol.kc)?;
        let line = format!(
            "{{\"kind\": \"release\", \"epoch\": {}, \"step\": {}, \"M\": {}, \"C\": {}, \"digest\": {}, \"policy\": {}}}",
            ctx.epoch,
            ctx.step,
            m,
            c,
            jstr(&hex(&Sha256::digest(blob))),
            jstr(&policy_digest(pol))
        );
        append(&self.path, &line, false)?;
        self.reload()?;
        Ok((m, c))
    }

    /// Public genesis: check the genesis record against the cfg json it pins (program.pg = sha256 of the bytes).
    /// W = darktrain::init(cfg) is recomputed here and committed with public coins (run::public_genesis_roots); the
    /// record's roots must equal them. Until this succeeds the ledger accepts no step and no release.
    #[cfg(feature = "tcp")]
    pub fn check_public_genesis(&mut self, cfg_json: &[u8]) -> Result<(), String> {
        use sha2::{Digest, Sha256};
        let want = self.program.pg.ok_or("public genesis refused: the genesis program pins no PG")?;
        let got: [u8; 32] = Sha256::digest(cfg_json).into();
        if got != want {
            return Err("public genesis refused: the cfg is not the one the genesis record pins".into());
        }
        let (d, w1, w2) = crate::run::public_weights(cfg_json)?;
        if d != self.d {
            return Err(format!("public genesis refused: the cfg's d = {d}, the ledger's {}", self.d));
        }
        let roots = crate::run::public_genesis_roots(&self.pr, d, &w1, &w2, 3);
        if roots != self.genesis_roots {
            return Err("public genesis refused: the genesis roots are not the public commitment of the cfg's W".into());
        }
        self.pg_verified = Some(roots);
        Ok(())
    }

    fn pg_gate(&self) -> Result<(), String> {
        if self.program.pg.is_some() && self.pg_verified.as_ref() != Some(&self.genesis_roots) {
            return Err("public genesis not checked against its cfg (check_public_genesis): nothing accepted".into());
        }
        Ok(())
    }

    pub fn accept(&mut self, lp: &LigParams, blob: &[u8], tables: &(Vec<u64>, Vec<u64>)) -> Result<(), String> {
        let _l = self.lock()?;
        self.reload()?;
        self.pg_gate()?;
        if self.released.is_some() {
            return Err("the ledger is released: no further steps".into());
        }
        let (ctx, parent) = self.head();
        let acc = wire::verify_step(&self.pr, lp, blob, &ctx, &parent, tables, self.d, self.program, self.owner_pk.as_ref(), self.next_leaf)?;
        let line = format!(
            "{{\"kind\": \"step\", \"epoch\": {}, \"step\": {}, \"digest\": {}, \"child\": {}, \"leaf\": {}}}",
            ctx.epoch,
            ctx.step,
            jstr(&hex(&Sha256::digest(blob))),
            jroots(&acc.child),
            acc.leaf.map(|l| l.to_string()).unwrap_or_else(|| "null".into())
        );
        append(&self.path, &line, false)?;
        self.reload()
    }
}

/// sha256 of the release policy: M, ncls, kc (u32 each, big-endian), X (k M + t order, u64 each) and labels (u8).
pub fn policy_digest(pol: &crate::run::Policy) -> String {
    let mut h = Sha256::new();
    for v in [pol.labels.len() as u32, pol.ncls as u32, pol.kc] {
        h.update(v.to_be_bytes());
    }
    for x in &pol.x {
        h.update(x.to_be_bytes());
    }
    for &l in &pol.labels {
        h.update([l as u8]);
    }
    hex(&h.finalize())
}
