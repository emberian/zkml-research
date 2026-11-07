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
    pub owner_pk: Option<Hash>,
    pub epoch: u64,
    pub step: u64,
    pub parent: BTreeMap<String, Vec<Hash>>,
    pub next_leaf: u64,
    pub custodians: Vec<String>,
}

pub struct Genesis {
    pub d: usize,
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
        if !path.exists() {
            let g = genesis.ok_or("a new ledger needs its genesis record")?;
            let line = format!(
                "{{\"kind\": \"genesis\", \"model\": {}, \"d\": {}, \"params\": {}, \"owner_pk\": {}, \"custodians\": {}, \"roots\": {}}}",
                jstr(model),
                g.d,
                jparams(pr),
                jstr(&g.owner_pk.map(|k| hex(&k)).unwrap_or_else(|| "none".into())),
                jlist(&g.custodians),
                jroots(&g.roots)
            );
            append(path, &line, true)?;
        }
        let mut l = Ledger {
            path: path.to_path_buf(),
            model: model.to_string(),
            pr: pr.clone(),
            recs: vec![],
            d: 0,
            owner_pk: None,
            epoch: 0,
            step: 0,
            parent: BTreeMap::new(),
            next_leaf: 0,
            custodians: vec![],
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
        let pk = g["owner_pk"].as_str().ok_or("owner_pk")?;
        self.owner_pk = if pk == "none" { None } else { Some(unhex32(pk).ok_or("owner_pk hex")?) };
        self.epoch = 0;
        self.step = 0;
        self.parent = roots_of(&g["roots"])?;
        self.next_leaf = 0;
        self.custodians =
            g["custodians"].as_array().ok_or("custodians")?.iter().map(|c| c.as_str().unwrap_or("").to_string()).collect();
        for (no, rec) in self.recs[1..].iter().enumerate() {
            let no = no + 2;
            match rec["kind"].as_str() {
                Some("step") => {
                    if (rec["epoch"].as_u64(), rec["step"].as_u64()) != (Some(self.epoch), Some(self.step + 1)) {
                        return Err(format!("ledger line {no} breaks the sequence (fail closed)"));
                    }
                    self.step += 1;
                    self.parent = roots_of(&rec["child"])?;
                    if let Some(l) = rec["leaf"].as_u64() {
                        self.next_leaf = l + 1;
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

    pub fn rotate(&mut self, custodians: &[String], new_roots: &BTreeMap<String, Vec<Hash>>) -> Result<(), String> {
        let _l = self.lock()?;
        self.reload()?;
        let line = format!(
            "{{\"kind\": \"rotate\", \"epoch\": {}, \"custodians\": {}, \"roots\": {}, \"handover_proof\": {}}}",
            self.epoch + 1,
            jlist(custodians),
            jroots(new_roots),
            jstr("UNBUILT: equality of the old and new commitments")
        );
        append(&self.path, &line, false)?;
        self.reload()
    }

    pub fn accept(&mut self, lp: &LigParams, blob: &[u8], tables: &(Vec<u64>, Vec<u64>)) -> Result<(), String> {
        let _l = self.lock()?;
        self.reload()?;
        let (ctx, parent) = self.head();
        let acc = wire::verify_step(&self.pr, lp, blob, &ctx, &parent, tables, self.d, self.owner_pk.as_ref(), self.next_leaf)?;
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
