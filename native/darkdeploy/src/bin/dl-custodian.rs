//! dl-custodian: one custodian process of the deployed run. `darkstep serve` with, inside the same process, the
//! per-step collaborative proof, this custodian's replica of the ledger, the handover and the mind's release.
//!
//!   dl-custodian serve <darkstep serve arguments> [--prove [--pipeline-proofs --proof-mesh A0,A1,A2]
//!       [--profile NAME] [--proof-archive ADIR]] [--model NAME]
//!       [--handover-at K --mesh6 A0,..,A5 --tls6 DIR6 [--listen6 HOST:PORT] [--erase-extra FILE].. [--scan-extra PATH]..]
//!       [--self-handover-tape FILE --recover-mesh A0,A1,A2 --recover-mesh6 A0,..,A5 --tapes2 PAT --owner-msgs2 PAT]
//!       [--release --release-data MNISTDIR [--release-m M (default: the cfg's release.M)] [--release-tape FILE]]
//!   dl-custodian join J <N L F d> DIR A0 A1 A2 --tls TLSDIR --owner HOST:PORT --steps K --mesh6 A0,..,A5
//!       --tls6 DIR6 --handover-tape FILE --tapes PAT --owner-msgs PAT --genesis-cfg CFG --prove [...]
//!   dl-custodian proof-triples N L F d [--program P]
//! Every serve/join takes `--consumed-log FILE` (required outside test builds): the box's registry of consumed
//! preprocessing; a tape whose sha256 is in it is refused (single use), including after --resume.
//!
//! --prove: after each accepted step k this custodian runs its share of the proof of step k + 1 (ledger counter)
//! over the same TLS mesh (tag PROOF), from its own ProofRecord, its new weight shares and its tape's proof section
//! (darkproof::run::step_section(..) triples right after the step), then moves its tape cursor past them. Every
//! custodian ends with the same bundle and accepts it into its own ledger replica DIR/ledger_P<I>.jsonl (darkproof
//! Ledger: genesis record, check_public_genesis against the genesis cfg, then accept per step), which verifies it
//! against the head's roots. Files: DIR/proof_latest_P<I>.bin (only the latest bundle), DIR/ledger_P<I>.jsonl,
//! DIR/carry_P<I>.bin (0600); with --proof-archive ADIR (one seat) every bundle as ADIR/proof_e<epoch>_s<step>.bin;
//! custodian 0 also DIR/genesis_roots.json and DIR/proof_chain.json.
//!
//! --pipeline-proofs: the proof of step k runs in a worker thread on its own three-party mesh (--proof-mesh) while
//! step k + 1 runs (at most one in flight; the step's record and proof-section triples are copied out first). Each
//! proof's report is DIR/proof_<k>_P<I>.json; step k + 1's report carries it as proof_of_previous_step. Every exit
//! (the end, a pause, a handover, a refusal) first waits for the proof in flight.
//! --handover-at K (old seat i of a rotation): after step K is accepted and proved, the step loop ends and the seat
//! joins the six-party mesh (--mesh6: the old committee 0..2, then the new one 3..5; DIR6 holds cert6_<0..5>.der),
//! sends its ledger replica (public) to the new seats, and runs darkhand's old side: resharing, the joint handover
//! proof, then erasure of its shares, keys, tape, commitment and state files, a memory scan and a decryption
//! attempt with what is left. It writes DIR/handover_P<I>.json and exits.
//! join J (new seat J): its own three-party mesh with the new committee (A0..A2, TLSDIR), the six-party mesh at index
//! 3 + J, the ledger from all three old seats (they must agree), the new committee's ceremony and the resharing
//! (darkhand's new side), the rotation accepted by its ledger replica, then the step loop from step K + 1 on its own
//! tapes (under the new committee's MAC key).
//! --self-handover-tape (same seats after an abort): when a step is refused, every seat reloads its checkpoint (the
//! state before that step), opens a fresh three-party mesh (--recover-mesh), gives its new role a fresh TLS identity
//! (its certificate exchanged on that pinned mesh), and runs the old role (index i) and the new role (index 3 + i,
//! the HE key kept, a new MAC key from the new tape) as two threads on the six-party mesh (--recover-mesh6). The
//! ledger rotates to the same set at the next epoch, and the loop redoes the refused step on --tapes2.
//! --release: after the last step, the release program and its proof over the head's weights (darkproof::run::
//! release_custodian; policy darkproof::run::mnist_policy over the genesis cfg and MNIST, the first M test images),
//! accepted by the ledger replica. Only C is opened. Files: DIR/release_P<I>.bin, DIR/release_P<I>.json.
use darkhand::serve::OldParts;
use darkhand::side::{self, Common};
use darkproof::ledger::{Genesis, Ledger};
use darkproof::step::StepParams;
use darkstep::node::flag;
use darkstep::serve::{self, CustodianState, End, StepHook};
use darkstep::step::{Program, ProofRecord};
use serde_json::{json, Value};
use std::collections::BTreeMap;
use std::net::SocketAddr;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

/// Every heap buffer is zeroed when it is freed (the handover's erasure relies on it).
#[global_allocator]
static ALLOC: darkhand::erase::ZeroOnFree = darkhand::erase::ZeroOnFree;

type Carry = BTreeMap<String, darkproof::pcs::PcsParty>;
type Roots = BTreeMap<String, Vec<darkproof::h::Hash>>;

/// The proof chain's state: the carried commitment, this custodian's ledger replica, and what it writes per proof.
/// Inline it lives in Prove; pipelined (--pipeline-proofs) it moves into the proof worker thread.
struct Chain {
    me: usize,
    d: usize,
    dir: PathBuf,
    archive: Option<PathBuf>,
    model: String,
    pr: darkproof::Profile,
    lp: darkproof::ligero::LigParams,
    tables: (Vec<u64>, Vec<u64>),
    prm: StepParams,
    carry: Option<Carry>,
    /// the genesis roots before the ledger exists (an owner-input genesis: they come with the first proof)
    genesis: Option<Roots>,
    ledger: Option<Ledger>,
    gcfg: Option<Vec<u8>>,
    /// the committee's names on the ledger: sha256 of each custodian's certificate
    names: Vec<String>,
    chain: Vec<Value>,
}

/// One step's proof job: the party's step record and proof-section triples (copied out of the step's state), the
/// ledger counter and epoch it is proved under.
struct Job {
    k: usize,
    step: u64,
    epoch: u64,
    count: usize,
    ps: darkproof::run::PartyStep,
}

/// The proof worker (--pipeline-proofs): the proof of step k runs on its own three-party mesh (--proof-mesh) while
/// step k + 1 runs; at most one proof is in flight.
struct Worker {
    tx: std::sync::mpsc::Sender<Job>,
    rx: std::sync::mpsc::Receiver<Result<(usize, Value), String>>,
    handle: std::thread::JoinHandle<Chain>,
    inflight: bool,
}

/// darkhand's NewCustodian without its key (the key went back into the seat's He).
struct Joined {
    #[allow(dead_code)]
    j: usize,
    #[allow(dead_code)]
    keys: Option<(darkhand::side::HeSecret, dzkpopk::ceremony::Ceremony)>,
    party: darkstep::party::Party,
    w: BTreeMap<String, Vec<darkstep::party::Sh>>,
    carry: Carry,
    proof: Vec<u8>,
    new_roots: BTreeMap<String, Vec<[u8; 32]>>,
    report: Value,
    /// DEFER: the new head's pending claims' carries (this party's), joined into the carry
    defer: Option<darkproof::defer::DeferIn>,
}

/// The carry after a handover under DEFER: the new W (one life) and this party's carries of the claims the
/// handover left pending (the next step's prover takes them back out with run::carry_in).
fn joined_carry(mut carry: Carry, defer: Option<darkproof::defer::DeferIn>) -> Carry {
    if let Some(d) = defer {
        carry.extend(d.carries);
    }
    carry
}

struct Prove {
    me: usize,
    on: bool,
    args: Vec<String>,
    model: String,
    pr: darkproof::Profile,
    lp: darkproof::ligero::LigParams,
    tables: (Vec<u64>, Vec<u64>),
    prm: StepParams,
    gcfg: Option<Vec<u8>>,
    ch: Option<Chain>,
    worker: Option<Worker>,
    /// the next proof's (ledger step, epoch), counted here so that a job can be made while the last is in flight
    next: Option<(u64, u64)>,
    /// the step index the run ends at (serve's --steps counted from where this process started)
    end_step: usize,
    /// a handover the loop ended for (rotation or self-handover), run from main once serve has returned: its frames
    /// then sit on a scrubbed stack below main's, which holds boxes only (see `run_deferred`)
    deferred: Option<(Box<CustodianState>, End, PathBuf)>,
}

/// finish's code for "the handover is deferred to main" (never an exit code)
const DEFERRED: i32 = -100;

/// --profile NAME (darkproof::Profile::by_name; default "ledger"): the proof profile; it fixes the proof section's
/// size, so it must be the one the tapes' proof sections were made for (e.g. "ledger-sq" for chunks made before
/// the proof lane's bundle cut).
fn profile_of(args: &[String]) -> darkproof::Profile {
    let n = flag(args, "--profile").unwrap_or_else(|| "ledger".into());
    darkproof::Profile::by_name(&n).unwrap_or_else(|| panic!("--profile {n}: unknown"))
}

/// `--rs`: the program's truncations prove their bound by one masked zero test (proof flag RS; the genesis record
/// pins "RS": true, so a replica opened without it is refused); its tapes carry K + 1 - s bits per truncation.
fn rs_of(args: &[String]) -> bool {
    args.iter().any(|a| a == "--rs")
}

fn params_of(pg: &Program, rs: bool) -> StepParams {
    StepParams { s1: pg.s1, k1: pg.k1, s2: pg.s2, k2: pg.k2, s3: pg.s3, k3: pg.k3, he: false, rc: true, lb: true, rs, pg: None, r3: pg.r3, t_lo: pg.t_lo }.deployed()
}

fn hex_roots(g: &Roots) -> String {
    let enc: BTreeMap<&String, Vec<String>> = g.iter().map(|(k, v)| (k, v.iter().map(|h| pycompat::repr::hex(h)).collect())).collect();
    serde_json::to_string_pretty(&enc).unwrap()
}

fn addr_list(s: &str) -> Vec<SocketAddr> {
    s.split(',').map(|a| a.parse().unwrap_or_else(|e| panic!("{a}: {e}"))).collect()
}

fn timeout_of(args: &[String]) -> Duration {
    Duration::from_secs(flag(args, "--timeout").map(|t| t.parse().unwrap()).unwrap_or(600))
}

/// args with flag `name`'s value replaced (or appended)
fn with_flag(args: &[String], name: &str, val: &str) -> Vec<String> {
    let mut a = args.to_vec();
    match a.iter().position(|x| x == name) {
        Some(k) => a[k + 1] = val.to_string(),
        None => {
            a.push(name.to_string());
            a.push(val.to_string());
        }
    }
    a
}

fn write_carry(path: &Path, c: &Carry) -> std::io::Result<()> {
    let mut b: Vec<u8> = Vec::new();
    darkproof::pcs::write_carry(c, &mut b)?;
    serve::write_secret(path, b)
}

fn read_carry(path: &Path, pr: &darkproof::Profile) -> Result<Carry, String> {
    let b = serve::read_secret(path)?;
    darkproof::pcs::read_carry(&mut &b[..], pr).map_err(|e| format!("{}: {e}", path.display()))
}

/// The epoch's file key (darkhand::vault) as darkstep's sealer: the checkpoint, the carry and the TLS key are sealed
/// under it. A handover takes it out (old_side destroys it); a self-handover puts the new epoch's in.
struct VaultSlot(std::sync::Mutex<Option<darkhand::vault::Vault>>);

impl serve::Sealer for VaultSlot {
    fn seal_to(&self, path: &Path, plain: Vec<u8>) -> std::io::Result<()> {
        let g = self.0.lock().unwrap();
        let v = g.as_ref().ok_or_else(|| std::io::Error::other("the file key was handed to the erasure"))?;
        v.seal_to(path, &side::vault_role(path), plain)
    }
    fn open(&self, path: &Path) -> Result<Vec<u8>, String> {
        let g = self.0.lock().unwrap();
        g.as_ref().ok_or("the file key was handed to the erasure")?.open_file(path, &side::vault_role(path))
    }
    fn open_role(&self, path: &Path, role: &str) -> Result<Vec<u8>, String> {
        let g = self.0.lock().unwrap();
        g.as_ref().ok_or("the file key was handed to the erasure")?.open_file(path, role)
    }
}

static VAULT: std::sync::OnceLock<std::sync::Arc<VaultSlot>> = std::sync::OnceLock::new();

/// `--vault`: load this seat's file key, named in TLSDIR/vault.name (written by `vault-init` at setup, rewritten
/// by a self-handover), and seal every state file under it. Required outside test builds.
fn load_vault(args: &[String]) {
    if !args.iter().any(|a| a == "--vault") {
        if cfg!(feature = "test-harness") {
            return;
        }
        eprintln!("--vault is required: the state files are sealed under the epoch's file key (dl-custodian vault-init at setup)");
        std::process::exit(2);
    }
    let tls = PathBuf::from(flag(args, "--tls").expect("--tls"));
    let name = std::fs::read_to_string(tls.join("vault.name")).unwrap_or_else(|e| panic!("{}: {e} (run vault-init)", tls.join("vault.name").display()));
    let v = darkhand::vault::Vault::load(name.trim()).unwrap_or_else(|e| {
        eprintln!("{e}");
        std::process::exit(2)
    });
    let slot = std::sync::Arc::new(VaultSlot(std::sync::Mutex::new(Some(v))));
    let _ = VAULT.set(slot.clone());
    serve::set_sealer(Some(slot));
}

/// The loaded file key, taken out of the sealer (for old_side, which destroys it).
fn take_vault() -> Option<darkhand::vault::Vault> {
    VAULT.get().and_then(|s| s.0.lock().unwrap().take())
}

/// `dl-custodian vault-init I TLSDIR [--model M] [--epoch E]`: make seat I's file key for epoch E in the uid's
/// persistent keyring (named by model, seat, epoch and its certificate), seal TLSDIR/tls_I.key under it in place and
/// write the key's name (public) to TLSDIR/vault.name.
fn vault_init(args: &[String]) -> Result<(), String> {
    let i: usize = args[2].parse().map_err(|_| "seat")?;
    let tls = PathBuf::from(&args[3]);
    let model = flag(args, "--model").unwrap_or_else(|| "dl-gen6".into());
    let epoch: u64 = flag(args, "--epoch").map(|e| e.parse().unwrap()).unwrap_or(0);
    let cert = std::fs::read(tls.join(format!("cert_{i}.der"))).map_err(|e| e.to_string())?;
    let name = darkhand::vault::key_name(&model, i, epoch, &darkstep::tls::cert_fingerprint(&cert));
    let key = tls.join(format!("tls_{i}.key"));
    let plain = std::fs::read(&key).map_err(|e| format!("{}: {e}", key.display()))?;
    if plain.starts_with(serve::SEALED_MAGIC) {
        return Err(format!("{}: sealed already", key.display()));
    }
    let v = darkhand::vault::Vault::create(&name, true)?;
    v.seal_to(&key, &side::vault_role(&key), plain).map_err(|e| e.to_string())?;
    std::fs::write(tls.join("vault.name"), &name).map_err(|e| e.to_string())?;
    // --with-next: the next epoch's key too (a self-handover's new role: the prep lane seals its tapes under it
    // before the handover), named in vault.name.next
    let mut next = Value::Null;
    if args.iter().any(|a| a == "--with-next") {
        let n2 = darkhand::vault::key_name(&model, i, epoch + 1, &darkstep::tls::cert_fingerprint(&cert));
        drop(darkhand::vault::Vault::create(&n2, true)?);
        std::fs::write(tls.join("vault.name.next"), &n2).map_err(|e| e.to_string())?;
        next = json!(n2);
    }
    println!("{}", json!({"seat": i, "vault": name, "next": next}));
    Ok(())
}

/// `dl-custodian close I N L F d DIR A0 A1 A2 --tls TLSDIR [--profile P] [--rs] [--model M] [--vault]`: a halted run
/// under DEFER (cut E) whose head is pending: every custodian proves the head's pending claims closed (no MPC
/// product, no tape), over the committee's mesh, and its ledger replica records the close (after it the ledger refuses
/// steps, releases and rotations). DIR holds the replica (ledger_P<I>.jsonl) and the carry (carry_P<I>.bin).
fn close_main(args: &[String]) -> Result<Value, String> {
    let i: usize = args[2].parse().map_err(|_| "seat")?;
    let pf = darkstep::node::prof(&args[3..7]);
    darkproof::field::set_p(pf.t);
    let dir = PathBuf::from(&args[7]);
    let addrs: Vec<SocketAddr> = args[8..11].iter().map(|a| a.parse().unwrap()).collect();
    let pr = profile_of(args);
    let lp = pr.ligero();
    let model = flag(args, "--model").unwrap_or_else(|| "dl-gen6".into());
    let mut lg = Ledger::open(&dir.join(format!("ledger_P{i}.jsonl")), &model, &pr, None)?;
    let pend = lg.pending.clone().ok_or("the head is not pending: nothing to close")?;
    let carry = read_carry(&dir.join(format!("carry_P{i}.bin")), &pr)?;
    let ctx = darkproof::Ctx::new(&model, lg.epoch, lg.step);
    let tlsdir = PathBuf::from(flag(args, "--tls").ok_or("--tls")?);
    let (id, certs) = serve::identity(&tlsdir, i);
    let net = serve::connect_mesh(i, &addrs, flag(args, "--listen"), &id, &certs, timeout_of(args))?;
    let out = darkproof::run::close_custodian(&pr, &lp, &net, i, 3, &ctx, carry, &pend, pf.d)?;
    net.shutdown();
    lg.close(&lp, &out.blob)?;
    use sha2::{Digest, Sha256};
    std::fs::write(dir.join(format!("close_P{i}.bin")), &out.blob).map_err(|e| e.to_string())?;
    let rep = json!({"party": i, "head_step": ctx.step, "epoch": ctx.epoch, "close_seconds": out.secs, "close_bytes": out.blob.len(),
        "close_sha256": pycompat::repr::hex(&Sha256::digest(&out.blob)), "field_elements_sent": out.sent, "ledger_closed": true});
    std::fs::write(dir.join(format!("close_P{i}.json")), serde_json::to_string_pretty(&rep).unwrap()).map_err(|e| e.to_string())?;
    Ok(rep)
}

/// `--keep-erased-copy DIR` (a check, not a deployment): copies of the sealed state files as they are before the
/// erasure, so that a checker can show afterwards that nothing on the box opens them.
fn keep_erased_copy(args: &[String], files: &[PathBuf]) {
    if let Some(d) = flag(args, "--keep-erased-copy") {
        let d = PathBuf::from(d);
        let _ = std::fs::create_dir_all(&d);
        for f in files {
            // only sealed files: a copy of a plain secret (an --erase-extra MP-SPDZ key file) would outlive the erasure
            let mut head = [0u8; 8];
            let sealed = std::fs::File::open(f).and_then(|mut h| std::io::Read::read_exact(&mut h, &mut head)).is_ok() && &head == serve::SEALED_MAGIC;
            if sealed {
                let _ = std::fs::copy(f, d.join(f.file_name().unwrap()));
            }
        }
    }
}

/// The handover proof (public; the ledger keeps its sha256): DIR/handover_e<E>.bin, and in the archive if any.
fn save_handover_proof(args: &[String], dir: &Path, epoch: i64, proof: &[u8]) -> Result<(), String> {
    std::fs::write(dir.join(format!("handover_e{epoch}.bin")), proof).map_err(|e| e.to_string())?;
    if let Some(a) = flag(args, "--proof-archive") {
        std::fs::create_dir_all(&a).map_err(|e| e.to_string())?;
        std::fs::write(Path::new(&a).join(format!("handover_e{epoch}.bin")), proof).map_err(|e| e.to_string())?;
    }
    Ok(())
}

/// The weight shares and step of a checkpoint, without leaving its alpha share in the caller's frame.
#[inline(never)]
fn reload_shares(path: &Path) -> Result<(darkstep::serve::Shares, usize), String> {
    let mut ck = serve::read_checkpoint(path)?;
    let out = (std::mem::take(&mut ck.w), ck.step);
    unsafe { std::ptr::write_volatile(&mut ck.alpha_i, 0) };
    Ok(out)
}

/// The serve arguments after a self-handover at refused step k: the remaining steps, the new key's tapes and owner
/// messages (--tapes2, --owner-msgs2; their chunks start at --chunk-first2, default k), and no second recovery.
fn after_self_handover(args: &[String], k: usize, end_step: usize) -> Vec<String> {
    let mut a = with_flag(args, "--steps", &(end_step - k).to_string());
    for (from, to) in [("--tapes2", "--tapes"), ("--owner-msgs2", "--owner-msgs")] {
        if let Some(v) = flag(args, from) {
            a = with_flag(&a, to, &v);
        }
    }
    a = with_flag(&a, "--chunk-first", &flag(args, "--chunk-first2").unwrap_or_else(|| k.to_string()));
    if let Some(p) = a.iter().position(|x| x == "--self-handover-tape") {
        a.drain(p..p + 2);
    }
    a
}

impl Chain {
    fn open_ledger(&mut self, roots: Roots) -> Result<(), String> {
        let g = Genesis { d: self.d, program: self.prm, owner_pk: None, custodians: self.names.clone(), roots };
        let mut lg = Ledger::open(&self.dir.join(format!("ledger_P{}.jsonl", self.me)), &self.model, &self.pr, Some(g))?;
        if let Some(b) = &self.gcfg {
            lg.check_public_genesis(b)?;
        }
        self.ledger = Some(lg);
        Ok(())
    }

    /// A ledger replica received from the old committee (public bytes), reopened and checked here.
    fn adopt_ledger(&mut self, bytes: &[u8]) -> Result<(), String> {
        let path = self.dir.join(format!("ledger_P{}.jsonl", self.me));
        std::fs::write(&path, bytes).map_err(|e| e.to_string())?;
        let mut lg = Ledger::open(&path, &self.model, &self.pr, None)?;
        if let Some(b) = &self.gcfg {
            lg.check_public_genesis(b)?;
        }
        self.ledger = Some(lg);
        Ok(())
    }

    /// Prove one step over `net` (tag PROOF), accept the bundle into this replica, checkpoint the carry.
    fn prove(&mut self, net: &darkstep::net::Net, job: Job) -> Result<Value, String> {
        let (i, k, step, epoch, count) = (self.me, job.k, job.step, job.epoch, job.count);
        let ctx = darkproof::Ctx::new(&self.model, epoch, step);
        let t0 = Instant::now();
        // DEFER (cut E): the parent's pending claims from this replica's head, this party's carries from the carry
        let pend = self.ledger.as_ref().and_then(|l| l.pending.as_ref());
        let sp = darkproof::run::prove_step_l(&self.pr, &self.lp, &self.tables, self.prm, &mut darkproof::run::TcpRef(net), &ctx, job.ps, self.carry.take(), pend)?;
        let prove_s = t0.elapsed().as_secs_f64();
        self.carry = Some(sp.child);
        // storage: each replica keeps only the latest bundle (the header and digest chain are in its ledger); the
        // full bundles go to one archive (--proof-archive DIR, set on one seat)
        let latest = self.dir.join(format!("proof_latest_P{i}.bin"));
        std::fs::write(latest.with_extension("tmp"), &sp.blob).and_then(|_| std::fs::rename(latest.with_extension("tmp"), &latest)).map_err(|e| e.to_string())?;
        if let Some(a) = &self.archive {
            std::fs::create_dir_all(a).map_err(|e| e.to_string())?;
            std::fs::write(a.join(format!("proof_e{epoch}_s{step}.bin")), &sp.blob).map_err(|e| e.to_string())?;
        }
        use sha2::{Digest, Sha256};
        let digest = pycompat::repr::hex(&Sha256::digest(&sp.blob));
        let mut out = json!({"serve_step": k, "proof_seconds": prove_s, "proof_bytes": sp.blob.len(), "proof_sha256": digest,
            "proof_field_elements_sent": sp.sent, "proof_triples": count, "ledger_step": step, "epoch": epoch});
        if let Some(g) = &sp.genesis_roots {
            self.genesis = Some(g.clone());
        }
        if self.ledger.is_none() {
            let g = self.genesis.clone().ok_or("no genesis roots")?;
            if i == 0 {
                std::fs::write(self.dir.join("genesis_roots.json"), hex_roots(&g)).map_err(|e| e.to_string())?;
            }
            self.open_ledger(g)?;
        }
        // every custodian accepts the bundle into its own ledger replica (verified against the head's roots)
        let tv = Instant::now();
        self.ledger.as_mut().unwrap().accept(&self.lp, &sp.blob, &self.tables)?;
        out["verify_seconds"] = json!(tv.elapsed().as_secs_f64());
        out["verified"] = json!(true);
        // the carried commitment (secret: share rows and salts) beside the checkpoint, so that --resume can prove on
        let tc = Instant::now();
        write_carry(&self.dir.join(format!("carry_P{i}.bin")), self.carry.as_ref().unwrap()).map_err(|e| format!("carry checkpoint: {e}"))?;
        out["carry_checkpoint_seconds"] = json!(tc.elapsed().as_secs_f64());
        let (_, rss) = serve::proc_usage();
        out["peak_rss_kb_after_proof"] = json!(rss);
        self.chain.push(json!({"step": step, "epoch": epoch, "proof_sha256": digest}));
        if i == 0 {
            std::fs::write(self.dir.join("proof_chain.json"), serde_json::to_string_pretty(&self.chain).unwrap()).map_err(|e| e.to_string())?;
        }
        std::fs::write(self.dir.join(format!("proof_{k}_P{i}.json")), serde_json::to_string_pretty(&out).unwrap()).map_err(|e| e.to_string())?;
        Ok(out)
    }
}

impl Prove {
    /// The proof chain, with the worker (if any) drained: its last proof done and its state back here.
    fn c(&mut self) -> &mut Chain {
        self.drain().expect("proof worker");
        self.ch.as_mut().expect("the proof chain")
    }

    /// Wait for the proof in flight; with `stop`, end the worker and take its state back.
    fn wait(&mut self) -> Result<Option<Value>, String> {
        let w = match self.worker.as_mut() {
            Some(w) if w.inflight => w,
            _ => return Ok(None),
        };
        w.inflight = false;
        match w.rx.recv() {
            Ok(r) => r.map(|(_, v)| Some(v)),
            Err(_) => Err("the proof worker died".into()),
        }
    }

    fn drain(&mut self) -> Result<Option<Value>, String> {
        let last = self.wait();
        if let Some(w) = self.worker.take() {
            drop(w.tx);
            self.ch = Some(w.handle.join().map_err(|_| "the proof worker panicked".to_string())?);
        }
        last
    }

    fn start_worker(&mut self) -> Result<(), String> {
        let mut ch = self.ch.take().ok_or("no proof chain")?;
        let i = self.me;
        let addrs = addr_list(&flag(&self.args, "--proof-mesh").ok_or("--pipeline-proofs needs --proof-mesh A0,A1,A2")?);
        let tlsdir = PathBuf::from(flag(&self.args, "--tls").unwrap());
        let (id, certs) = serve::identity(&tlsdir, i);
        let timeout = timeout_of(&self.args);
        let (tx, jrx) = std::sync::mpsc::channel::<Job>();
        let (rtx, rx) = std::sync::mpsc::channel();
        let handle = std::thread::Builder::new()
            .name("proof-worker".into())
            .stack_size(64 << 20)
            .spawn(move || {
                let net = match serve::connect_mesh(i, &addrs, None, &id, &certs, timeout) {
                    Ok(n) => n,
                    Err(e) => {
                        let _ = rtx.send(Err(format!("proof mesh: {e}")));
                        return ch;
                    }
                };
                for job in jrx {
                    let k = job.k;
                    let r = ch.prove(&net, job).map(|v| (k, v));
                    let failed = r.is_err();
                    let _ = rtx.send(r);
                    if failed {
                        net.abort();
                        return ch;
                    }
                }
                net.shutdown();
                ch
            })
            .map_err(|e| e.to_string())?;
        self.worker = Some(Worker { tx, rx, handle, inflight: false });
        Ok(())
    }

    fn common(&mut self, st_rns: std::sync::Arc<darkstep::rns::Rns>, d: usize, t: u64, new_set: &[String]) -> Result<Common, String> {
        let pr = self.pr.clone();
        let lp = pr.ligero();
        let lg = self.c().ledger.as_ref().ok_or("a handover needs the ledger replica (--prove)")?;
        Ok(Common { pr, lp, d, n_old: 3, n_new: 3, ctx: lg.handover_context(new_set), rns: st_rns, t })
    }

    /// Old seat of a rotation: the six-party mesh, the ledger to the new seats, darkhand's old side; then exit.
    fn rotate_out(&mut self, st: Box<CustodianState>, dir: &Path) -> Result<Value, String> {
        let args = self.args.clone();
        let (i, d, n, t) = (st.i, st.pf.d, st.pf.n, st.pf.t);
        let tlsdir = PathBuf::from(flag(&args, "--tls").unwrap());
        let (id, certs) = serve::identity(&tlsdir, i);
        let tls6 = PathBuf::from(flag(&args, "--tls6").ok_or("--tls6 DIR6")?);
        let certs6: Vec<Vec<u8>> = (0..6).map(|j| std::fs::read(tls6.join(format!("cert6_{j}.der")))).collect::<Result<_, _>>().map_err(|e| e.to_string())?;
        if certs6[..3] != certs[..] {
            return Err("cert6_0..2 are not this committee's certificates".into());
        }
        let addrs6 = addr_list(&flag(&args, "--mesh6").ok_or("--mesh6")?);
        let new_set: Vec<String> = certs6[3..].iter().map(|c| darkstep::tls::cert_fingerprint(c)).collect();
        let common = self.common(st.he.rns.clone(), d, t, &new_set)?;
        let lbytes = std::fs::read(&self.c().ledger.as_ref().unwrap().path).map_err(|e| e.to_string())?;
        // the post-erasure decryption attempt's ciphertext: one under this custodian's key, made while it holds it
        let mut st = st;
        let m = side::os_field(n, t);
        let ct = st.he.key.encrypt_exact(&m);
        let dg = side::digest(&st.he.key.decrypt(&ct, None));
        let pre_decrypts = dg == side::digest(&m);
        let mut files = vec![dir.join(format!("ckpt_P{i}.bin")), dir.join(format!("carry_P{i}.bin")), tlsdir.join(format!("tls_{i}.key"))];
        // every tape and owner message of steps 0..=K still on disk (--wipe-spent removes them step by step)
        for f in ["--tapes", "--owner-msgs"] {
            if let Some(p) = flag(&args, f) {
                let k0: usize = flag(&args, "--chunk-first").map(|x| x.parse().unwrap()).unwrap_or(0);
                for k in k0..st.step {
                    let q = PathBuf::from(serve::step_path(&args, &p, k));
                    if q.exists() && !files.contains(&q) {
                        files.push(q);
                    }
                }
            }
        }
        if let Some(p) = flag(&args, "--tape") {
            files.push(PathBuf::from(p));
        }
        let mut carry = self.c().carry.take().ok_or("no carried commitment (the handover needs --prove)")?;
        // DEFER: the head's pending claims (public; the same at all six seats) and this party's carries of them
        let pend = self.c().ledger.as_ref().and_then(|l| l.pending.clone());
        let old_carries = darkproof::run::carry_in(&mut carry, pend.as_ref())?.map(|d| d.carries);
        self.c().ledger = None;
        let mut scan: Vec<PathBuf> = files.clone();
        scan.push(dir.to_path_buf());
        scan.push(tlsdir.clone());
        // the chunk dirs (a whole-chunk tape file beside the step files is caught too)
        for f in ["--tapes", "--owner-msgs"] {
            if let Some(p) = flag(&args, f) {
                let k0: usize = flag(&args, "--chunk-first").map(|x| x.parse().unwrap()).unwrap_or(0);
                for k in k0..st.step {
                    let q = PathBuf::from(serve::step_path(&args, &p, k));
                    if let Some(c) = q.parent().and_then(|s| if s.file_name().is_some_and(|n| n.to_string_lossy().starts_with("step-")) { s.parent() } else { Some(s) }) {
                        if !scan.iter().any(|x| x == c) {
                            scan.push(c.to_path_buf());
                        }
                    }
                }
            }
        }
        // this seat's retired MAC key outside the tapes, e.g. its MP-SPDZ key files (--erase-extra FILE, repeatable)
        let mut files = files;
        for (n, x) in args.iter().enumerate() {
            if x == "--erase-extra" {
                let f = PathBuf::from(&args[n + 1]);
                if f.exists() && !files.contains(&f) {
                    files.push(f);
                }
            }
        }
        // more places of this seat's secrets on disk, e.g. its MP-SPDZ runtime dir (--scan-extra, repeatable)
        for (n, x) in args.iter().enumerate() {
            if x == "--scan-extra" {
                scan.push(PathBuf::from(&args[n + 1]));
            }
        }
        let timeout = timeout_of(&args);
        let listen6 = flag(&args, "--listen6");
        // the boxed state is taken apart inside old_side's setup frame (dead and scrubbed before the memory scan);
        // the epoch's file key goes with it (old_side destroys it: the sealed files then open under no key)
        keep_erased_copy(&args, &files);
        let setup = darkhand::serve::rotation_setup(st, carry, files, scan, Some((ct, dg)));
        let setup: Box<dyn FnOnce() -> Box<darkhand::side::OldCustodian> + Send> = match old_carries {
            Some(c) => Box::new(darkhand::serve::with_old_carries(setup, c)),
            None => Box::new(setup),
        };
        let vault = take_vault();
        let setup: Box<dyn FnOnce() -> Box<darkhand::side::OldCustodian> + Send> = match vault {
            Some(v) => Box::new(darkhand::serve::with_vault(setup, v)),
            None => Box::new(setup),
        };
        let mut rep = side::old_side_e(&common, pend.as_ref(), setup, move || {
            let net6 = serve::connect_mesh(i, &addrs6, listen6, &id, &certs6, timeout).expect("six-party mesh");
            for j in 3..6 {
                net6.send(j, darkstep::net::CTRL, lbytes.clone());
            }
            net6
        })?;
        rep["pre_handover_decrypts"] = json!(pre_decrypts);
        Ok(rep)
    }

    /// Self-handover after a refused step k: see the module doc.
    fn self_handover(&mut self, st: Box<CustodianState>, k: usize, dir: &Path) -> Result<(Box<CustodianState>, Value), String> {
        let args = self.args.clone();
        let mut st = st;
        let (i, d, t) = (st.i, st.pf.d, st.pf.t);
        let (w, ck_step) = reload_shares(&dir.join(format!("ckpt_P{i}.bin")))?;
        if ck_step != k {
            return Err(format!("self-handover: the checkpoint is at step {ck_step}, the refused step is {k}"));
        }
        st.w = Some(w);
        st.step = ck_step;
        // the refused step's dead frames (its MAC check, its openings used the alpha share) were zeroed by
        // run_deferred's scrub_stack_all before this frame; the roles run on their own threads
        let tlsdir = PathBuf::from(flag(&args, "--tls").unwrap());
        let (id, certs) = serve::identity(&tlsdir, i);
        let timeout = timeout_of(&args);
        // the aborted mesh is dead: a fresh one, under the same pinned certificates
        let addrs3 = addr_list(&flag(&args, "--recover-mesh").ok_or("--recover-mesh")?);
        let fresh = serve::connect_mesh(i, &addrs3, None, &id, &certs, timeout)?;
        let dead = std::mem::replace(&mut st.pt.net, fresh);
        std::thread::spawn(move || dead.shutdown());
        // the new role's identity, its certificate exchanged on the pinned mesh
        let id_new = darkstep::tls::generate(3 + i);
        let mut certs6 = certs.clone();
        certs6.extend(st.pt.net.exchange_bytes(darkstep::net::CTRL, &id_new.cert_der));
        let addrs6 = addr_list(&flag(&args, "--recover-mesh6").ok_or("--recover-mesh6")?);
        let names = self.c().ledger.as_ref().ok_or("the self-handover needs the ledger replica (--prove)")?.custodians.clone();
        let common = self.common(st.he.rns.clone(), d, t, &names)?;
        let epoch = self.c().ledger.as_ref().unwrap().epoch as i64;
        let new_tape = serve::read_tape(&flag(&args, "--self-handover-tape").unwrap());
        let mut carry = self.c().carry.take().ok_or("no carried commitment")?;
        // DEFER: the pending claims of the head after the last accepted step (none after a public genesis)
        let pend = self.c().ledger.as_ref().and_then(|l| l.pending.clone());
        let old_carries = darkproof::run::carry_in(&mut carry, pend.as_ref())?.map(|d| d.carries);
        let pf = st.pf.clone();
        // the boxed state is taken apart inside the old role's setup frame, on the old role's own (scrubbed) stack;
        // the HE side and the mesh reach the new role over darkhand's channel
        // what the old role erases: the refused step's tape and owner message (old key), and the state files under
        // the old key (rewritten under the new one right after); what its disk scan covers besides
        let mut files: Vec<PathBuf> = vec![dir.join(format!("ckpt_P{i}.bin")), dir.join(format!("carry_P{i}.bin"))];
        let mut scan: Vec<PathBuf> = vec![dir.to_path_buf()];
        for f in ["--tapes", "--owner-msgs"] {
            if let Some(p) = flag(&args, f) {
                let q = PathBuf::from(serve::step_path(&args, &p, k));
                if let Some(c) = q.parent() {
                    scan.push(c.to_path_buf());
                }
                files.push(q);
            }
        }
        // the old key's files outside the tapes (its MP-SPDZ MAC-key and secrets files), retired with it
        for (n, x) in args.iter().enumerate() {
            if x == "--erase-extra" {
                let f = PathBuf::from(&args[n + 1]);
                if !files.contains(&f) {
                    files.push(f);
                }
            }
        }
        files.retain(|f| f.exists());
        for (n, x) in args.iter().enumerate() {
            if x == "--scan-extra" {
                scan.push(PathBuf::from(&args[n + 1]));
            }
        }
        // the seat keeps its TLS identity across a self-handover: its key file is resealed under the new epoch's file
        // key once the old one is destroyed
        let tls_key = if serve::sealing() { Some(serve::read_secret(&tlsdir.join(format!("tls_{i}.key")))?) } else { None };
        keep_erased_copy(&args, &files);
        let (setup, prx) = darkhand::serve::self_setup(st, carry, files, scan);
        let setup: Box<dyn FnOnce() -> Box<darkhand::side::OldCustodian> + Send> = match old_carries {
            Some(c) => Box::new(darkhand::serve::with_old_carries(setup, c)),
            None => Box::new(setup),
        };
        let vault_old = take_vault();
        let had_vault = vault_old.is_some();
        let setup: Box<dyn FnOnce() -> Box<darkhand::side::OldCustodian> + Send> = match vault_old {
            Some(v) => Box::new(darkhand::serve::with_vault(setup, v)),
            None => Box::new(setup),
        };
        let (orep, nc, he) = std::thread::scope(|s| {
            let (c6o, c6n, a6o, a6n, ido) = (certs6.clone(), certs6.clone(), addrs6.clone(), addrs6.clone(), id);
            let pend = &pend;
            let common = &common;
            let a = std::thread::Builder::new()
                .stack_size(64 << 20)
                .spawn_scoped(s, move || side::old_side_e(common, pend.as_ref(), setup, move || serve::connect_mesh(i, &a6o, None, &ido, &c6o, timeout).expect("six-party mesh (old role)")))
                .unwrap();
            let b = std::thread::Builder::new()
                .stack_size(64 << 20)
                .spawn_scoped(s, move || -> Result<(Joined, darkstep::he::He), String> {
                    let (he, net3) = prx.recv().map_err(|_| "the old role ended before handing over".to_string())?;
                    let net6 = serve::connect_mesh(3 + i, &a6n, None, &id_new, &c6n, timeout)?;
                    // the kept key goes to the new role and comes back as nc.key
                    let nc = side::new_side_e(common, pend.as_ref(), i, net3, net6, new_tape, epoch + 1, 0, Some(he.key))?;
                    let side::NewCustodian { j, keys, key, party, w, carry, proof, new_roots, report, defer, .. } = nc;
                    Ok((Joined { j, keys, party, w, carry, proof, new_roots, report, defer }, darkstep::he::He { key, ..he }))
                })
                .unwrap();
            let orep = a.join().map_err(|_| "old role panicked".to_string());
            match b.join().map_err(|_| "new role panicked".to_string()).and_then(|r| r) {
                Ok((nc, he)) => (orep, Ok(nc), Some(he)),
                Err(e) => (orep, Err(e), None),
            }
        });
        let orep = orep??;
        let nc = nc?;
        if nc.report["mac_check"] != "ok" {
            return Err(format!("the handover's MAC check under the new key failed: {}", nc.report["mac_check"]));
        }
        save_handover_proof(&args, dir, (epoch + 1) as i64, &nc.proof)?;
        if had_vault {
            // the new epoch's file key (the old one is destroyed): the state under the new MAC key is sealed under it
            let cert = std::fs::read(tlsdir.join(format!("cert_{i}.der"))).map_err(|e| e.to_string())?;
            let name = darkhand::vault::key_name(&self.model, i, epoch as u64 + 1, &darkstep::tls::cert_fingerprint(&cert));
            // made at setup (vault-init --with-next) when the prep lane sealed the new key's tapes under it
            let v = match darkhand::vault::Vault::load(&name) {
                Ok(v) => v,
                Err(_) => darkhand::vault::Vault::create(&name, true)?,
            };
            *VAULT.get().unwrap().0.lock().unwrap() = Some(v);
            serve::write_secret(&tlsdir.join(format!("tls_{i}.key")), tls_key.unwrap()).map_err(|e| format!("TLS key: {e}"))?;
            std::fs::write(tlsdir.join("vault.name"), &name).map_err(|e| e.to_string())?;
        }
        if args.iter().any(|a| a == "--wipe-spent") {
            if let Some(f) = flag(&args, "--self-handover-tape") {
                serve::wipe_file(Path::new(&f)).map_err(|e| format!("{f}: {e}"))?;
            }
        }
        self.c().ledger.as_mut().unwrap().rotate(&names, &nc.new_roots, &nc.proof)?;
        let mut he = he.expect("the new role's HE side");
        // a test attack (--attack, the abort test's fault) fires in one epoch only
        he.attack = None;
        let mut st2 = CustodianState::from_parts(i, pf, he, nc.party, darkhand::serve::shares_rows(&nc.w, d), k);
        let a2 = after_self_handover(&args, k, self.end_step);
        if let Some(p) = flag(&a2, "--tapes") {
            st2.load_tape(serve::read_tape(&serve::step_path(&a2, &p, k)))?;
        }
        // the state under the new key, carry beside checkpoint (the old role erased both under the old key)
        let carry = joined_carry(nc.carry, nc.defer);
        write_carry(&dir.join(format!("carry_P{i}.bin")), &carry).map_err(|e| format!("carry checkpoint: {e}"))?;
        self.c().carry = Some(carry);
        self.next = None;
        st2.checkpoint(&dir.join(format!("ckpt_P{i}.bin"))).map_err(|e| e.to_string())?;
        Ok((st2, json!({"old_role": orep, "new_role": nc.report, "epoch": epoch + 1, "redo_step": k})))
    }

    fn release(&mut self, st: &mut CustodianState, dir: &Path) -> Result<Value, String> {
        let args = self.args.clone();
        let i = st.i;
        let cfg = self.gcfg.clone().ok_or("--release needs --genesis-cfg (the policy's encoder)")?;
        let cfg = &cfg;
        let data = PathBuf::from(flag(&args, "--release-data").ok_or("--release-data MNISTDIR")?);
        // M: --release-m, else the genesis cfg's release.M (the train lane's policy pin), else its eval_n
        let pinned = serde_json::from_slice::<Value>(cfg).ok().and_then(|v| v["release"]["M"].as_u64().or(v["eval_n"].as_u64()));
        let m: usize = flag(&args, "--release-m").map(|x| x.parse().unwrap()).or(pinned.map(|x| x as usize)).ok_or("release: no M (--release-m or the cfg's release.M)")?;
        let pol = darkproof::run::mnist_policy(cfg, &data, m)?;
        // the release's own tape (--release-tape): the steps' tape is freed (zeroed by the allocator) first; the tape is
        // claimed in the box's registry (a streamed sha256), its MPC part loaded, its proof section (the last 3 x nrt
        // entries, Beaver triples) streamed from the file by the prover
        let mut tape_file = None;
        if let Some(f) = flag(&args, "--release-tape") {
            st.pt.tape = darkstep::tape::Tape { alpha_i: st.pt.tape.alpha_i, ..Default::default() };
            let d = st.pf.d;
            let nrt = darkproof::run::release_section(&self.lp, d, m, self.prm, &pol);
            let (pre, rt) = if dlvault::is_sealed(Path::new(&f)) {
                // prep's sealed release tape (DLVAULT2, read block by block under this epoch's file key)
                let p = Path::new(&f);
                let sd = p.parent().ok_or("release tape path")?;
                let j = sd.file_name().and_then(|n| n.to_str()).and_then(|n| n.strip_prefix("step-")).ok_or("the release tape is not in a chunk's step-<j> dir")?;
                let c = sd.parent().and_then(|c| c.file_name()).and_then(|n| n.to_str()).ok_or("release tape chunk dir")?;
                let key = {
                    let g = VAULT.get().ok_or("a sealed release tape needs --vault")?.0.lock().unwrap();
                    let v = g.as_ref().ok_or("the file key was handed to the erasure")?;
                    std::sync::Arc::new(dlvault::Key::new(&v.name, v.key_bytes()))
                };
                let (pre, rt) = darkproof::run::load_release_tape_sealed(p, nrt, key, &format!("tape|{c}|{j}"))?;
                // claimed once opened (its MAC key share is inside the seal), before any entry is used
                serve::claim_tape_file(&f, Some(pre.alpha_i))?;
                (pre, rt)
            } else {
                if serve::sealing() && !cfg!(feature = "test-harness") {
                    return Err(format!("{f}: a plain release tape, but this custodian takes only sealed preprocessing"));
                }
                serve::claim_tape_file(&f, None)?;
                darkproof::run::load_release_tape(Path::new(&f), nrt)?
            };
            st.load_tape(pre)?;
            tape_file = Some(rt);
        }
        let model = self.model.clone();
        let lg = self.c().ledger.as_ref().ok_or("--release needs the ledger replica (--prove)")?;
        let ctx = darkproof::Ctx::new(&model, lg.epoch, lg.step);
        let roots = lg.parent.clone();
        let pend = lg.pending.clone();
        let carry = self.c().carry.take().ok_or("no carried commitment of the head")?;
        let (w1, w2) = st.w.as_ref().ok_or("no weights")?;
        let t0 = Instant::now();
        let out = darkproof::run::release_custodian_src(&self.pr, &self.lp, self.prm, &mut st.pt, w1, w2, &pol, &ctx, carry, Some(&roots), pend.as_ref(), tape_file)?;
        std::fs::write(dir.join(format!("release_P{i}.bin")), &out.blob).map_err(|e| e.to_string())?;
        let lp = self.pr.ligero();
        // the replica checks the policy against the genesis's pinned cfg (recomputed from darktrain's encoder)
        let (mm, c) = self.c().ledger.as_mut().unwrap().release_checked(&lp, &out.blob, &pol, cfg, &data)?;
        if c != out.c {
            return Err(format!("release: the ledger's C = {c}, the opened C = {}", out.c));
        }
        let (cpu, rss) = serve::proc_usage();
        use sha2::{Digest, Sha256};
        let rep = json!({"party": i, "M": mm, "C": c, "policy": darkproof::ledger::policy_digest(&pol), "head_step": ctx.step,
            "epoch": ctx.epoch, "release_seconds": t0.elapsed().as_secs_f64(), "mpc_seconds": out.mpc_secs,
            "prove_seconds": out.prove_secs, "verify_seconds": out.verify_secs, "proof_bytes": out.blob.len(),
            "proof_sha256": pycompat::repr::hex(&Sha256::digest(&out.blob)), "proof_field_elements_sent": out.sent,
            "triples": out.triples, "cpu_seconds": cpu, "peak_rss_kb": rss, "ledger_accepted": true});
        std::fs::write(dir.join(format!("release_P{i}.json")), serde_json::to_string_pretty(&rep).unwrap()).map_err(|e| e.to_string())?;
        println!("{rep}");
        Ok(rep)
    }
}

impl StepHook for Prove {
    fn after_step(&mut self, st: &mut CustodianState, k: usize, rec: &ProofRecord, _dir: &Path) -> Result<Value, String> {
        if !self.on {
            return Ok(Value::Null);
        }
        let (i, d) = (st.i, st.pf.d);
        let (step, epoch) = match self.next {
            Some(x) => x,
            None => {
                let c = self.c();
                c.ledger.as_ref().map(|l| (l.step + 1, l.epoch)).unwrap_or((k as u64 + 1, 0))
            }
        };
        self.next = Some((step + 1, epoch));
        let carried = self.prm.carried(step);
        let own;
        let tb = if self.prm.t_lo == -128 { &self.tables } else { own = darkproof::step::tables_for(self.prm.t_lo); &own };
        let count = darkproof::run::step_section(&self.lp, d, self.prm, carried, tb);
        let (w1n, w2n) = st.w.as_ref().ok_or("no weights")?;
        let ps = darkproof::run::from_darkstep_n(i, d, rec, w1n, w2n, &st.pt.tape, Some(count), darkproof::rng::Det::off())?;
        st.pt.cur = rec.tape_cursor + 3 * count;
        let job = Job { k, step, epoch, count, ps };
        if !self.args.iter().any(|a| a == "--pipeline-proofs") {
            return self.ch.as_mut().ok_or("no proof chain")?.prove(&st.pt.net, job);
        }
        // pipelined: the previous step's proof must be done (one in flight), then this one starts beside step k + 1
        let tw = Instant::now();
        let prev = self.wait()?;
        let wait_s = tw.elapsed().as_secs_f64();
        if self.worker.is_none() {
            self.start_worker()?;
        }
        let w = self.worker.as_mut().unwrap();
        w.tx.send(job).map_err(|_| "the proof worker died".to_string())?;
        w.inflight = true;
        Ok(json!({"pipelined": true, "proof_of_previous_step": prev, "waited_for_previous_proof_seconds": wait_s}))
    }

    fn stop_after(&mut self, k: usize) -> bool {
        flag(&self.args, "--handover-at").map(|h| h.parse::<usize>().unwrap() == k).unwrap_or(false)
    }

    fn finish(&mut self, st: Box<CustodianState>, end: &End, dir: &Path) -> Result<i32, Box<CustodianState>> {
        let i = st.i;
        // pipelined proofs: the last step's proof finishes (on its own mesh) before anything else, so that the
        // carry, the ledger replica and the checkpoint agree at every exit, a pause included
        if let Err(e) = self.drain() {
            eprintln!("the last proof failed: {e}");
            std::fs::write(dir.join(format!("proof_error_P{i}.json")), serde_json::to_string_pretty(&json!({"party": i, "error": e})).unwrap()).unwrap();
            st.pt.net.shutdown();
            return Ok(1);
        }
        let selfh = end.refused.is_some() && flag(&self.args, "--self-handover-tape").is_some();
        if (end.code == 4 || selfh) && self.deferred.is_none() {
            self.deferred = Some((st, end.clone(), dir.to_path_buf()));
            return Ok(DEFERRED);
        }
        self.finish_release(st, end, dir)
    }
}

impl Prove {
    /// The handovers finish deferred, from main: every frame of the step loop has returned, the whole main-thread
    /// stack below this frame is zeroed (the loop's dead frames held tapes and the alpha share by value), and only
    /// then do rotate_out / self_handover and darkhand's old side run, on that zeroed stack. A self-handover goes on
    /// serving (the redo); its own end may defer again (a rotation later in the run).
    #[inline(never)]
    fn run_deferred(&mut self, code: i32) -> i32 {
        let mut code = code;
        while code == DEFERRED {
            let Some((st, end, dir)) = self.deferred.take() else { return 1 };
            side::scrub_stack_all();
            code = self.finish_deferred(st, &end, &dir);
        }
        code
    }

    fn finish_deferred(&mut self, st: Box<CustodianState>, end: &End, dir: &Path) -> i32 {
        let i = st.i;
        if end.code == 4 {
            let r = self.rotate_out(st, dir);
            let (code, rep) = match r {
                Ok(rep) => (0, rep),
                Err(e) => (1, json!({"party": i, "error": e})),
            };
            std::fs::write(dir.join(format!("handover_P{i}.json")), serde_json::to_string_pretty(&rep).unwrap()).unwrap();
            println!("{}", json!({"party": i, "handover": if code == 0 { "done" } else { "failed" }}));
            return code;
        }
        if let (Some((k, _)), true) = (&end.refused, flag(&self.args, "--self-handover-tape").is_some()) {
            let k = *k;
            return match self.self_handover(st, k, dir) {
                Ok((st2, rep)) => {
                    std::fs::write(dir.join(format!("self_handover_P{i}.json")), serde_json::to_string_pretty(&rep).unwrap()).unwrap();
                    println!("{}", json!({"party": i, "self_handover": "done", "redo_step": k}));
                    let a = after_self_handover(&self.args, k, self.end_step);
                    self.args = a.clone();
                    serve::serve_state(&a, self, st2, Instant::now(), 0.0, 0.0)
                }
                Err(e) => {
                    std::fs::write(dir.join(format!("self_handover_P{i}.json")), serde_json::to_string_pretty(&json!({"party": i, "error": e})).unwrap()).unwrap();
                    eprintln!("self-handover: {e}");
                    1
                }
            };
        }
        st.pt.net.shutdown();
        1
    }
}

impl Prove {
    fn finish_release(&mut self, st: Box<CustodianState>, end: &End, dir: &Path) -> Result<i32, Box<CustodianState>> {
        let i = st.i;
        if end.code == 0 && self.args.iter().any(|a| a == "--release") {
            let mut st = st;
            let r = self.release(&mut st, dir);
            st.pt.net.shutdown();
            return Ok(match r {
                Ok(_) => 0,
                Err(e) => {
                    eprintln!("release: {e}");
                    std::fs::write(dir.join(format!("release_P{i}.json")), serde_json::to_string_pretty(&json!({"party": i, "error": e})).unwrap()).unwrap();
                    1
                }
            });
        }
        Err(st)
    }
}

/// --genesis-cfg CFG.json: the public genesis W = darktrain::init(cfg) (public by design: a committed genesis file
/// with a public seed). Otherwise darkstep's --genesis-public FILE, or an owner-input genesis.
fn genesis_of(args: &[String]) -> Option<(Vec<i64>, Vec<i64>)> {
    if let Some(f) = flag(args, "--genesis-cfg") {
        let c: darktrain::Cfg = serde_json::from_str(&std::fs::read_to_string(&f).expect("genesis cfg")).expect("cfg json");
        c.validate().expect("cfg");
        return Some(darktrain::init(&c));
    }
    flag(args, "--genesis-public").map(|f| {
        let b = std::fs::read(&f).unwrap();
        let v: Vec<i64> = b.chunks_exact(8).map(|c| i64::from_le_bytes(c.try_into().unwrap())).collect();
        let h = v.len() / 2;
        (v[..h].to_vec(), v[h..].to_vec())
    })
}

/// The hook for a seat of committee `i` (serve) or a joining seat (join; its genesis roots come with the ledger).
fn prove_hook(args: &[String], i: usize, join: bool) -> Prove {
    let pf = darkstep::node::prof(&args[3..7]);
    darkproof::field::set_p(pf.t);
    let pr = profile_of(args);
    let lp = pr.ligero();
    let program = serve::program_of(args);
    // public genesis: the program pins sha256 of the genesis cfg; every custodian commits the public W itself
    // (identical roots), and that commitment is the parent of step 1
    let gcfg = flag(args, "--genesis-cfg").map(|f| std::fs::read(f).expect("genesis cfg"));
    let mut prm = params_of(&program, rs_of(args));
    let mut carry = None;
    let mut genesis = None;
    if let Some(b) = &gcfg {
        use sha2::{Digest, Sha256};
        prm.pg = Some(Sha256::digest(b).into());
        if !join {
            let (gd, w1, w2) = darkproof::run::public_weights(b).expect("genesis cfg");
            assert_eq!(gd, pf.d, "the genesis cfg's d");
            let (c, roots) = darkproof::run::public_genesis(&pr, pf.d, i, &w1, &w2, 3);
            carry = Some(c);
            genesis = Some(roots);
        }
    }
    let tlsdir = PathBuf::from(flag(args, "--tls").expect("--tls"));
    let names = serve::identity(&tlsdir, i).1.iter().map(|c| darkstep::tls::cert_fingerprint(c)).collect();
    let steps: usize = flag(args, "--steps").expect("--steps").parse().unwrap();
    let dir = PathBuf::from(&args[7]);
    let start = if args.iter().any(|a| a == "--resume") {
        serve::read_checkpoint(&dir.join(format!("ckpt_P{i}.bin"))).map(|c| c.step).unwrap_or(0)
    } else if join {
        flag(args, "--after-step").map(|k| k.parse::<usize>().unwrap() + 1).unwrap_or(0)
    } else {
        0
    };
    let resume = args.iter().any(|a| a == "--resume");
    let mut ledger = None;
    if resume && args.iter().any(|a| a == "--prove") {
        let cp = dir.join(format!("carry_P{i}.bin"));
        carry = Some(read_carry(&cp, &pr).unwrap_or_else(|e| panic!("--resume --prove: {e}")));
        let mut lg = Ledger::open(&dir.join(format!("ledger_P{i}.jsonl")), &flag(args, "--model").unwrap_or_else(|| "dl-gen6".into()), &pr, None).expect("ledger replica");
        if let Some(b) = &gcfg {
            lg.check_public_genesis(b).expect("public genesis");
        }
        ledger = Some(lg);
    }
    let model = flag(args, "--model").unwrap_or_else(|| "dl-gen6".into());
    let ch = Chain {
        me: i,
        d: pf.d,
        dir: dir.clone(),
        archive: flag(args, "--proof-archive").map(PathBuf::from),
        model: model.clone(),
        lp: pr.ligero(),
        pr: pr.clone(),
        tables: darkproof::step::tables(),
        prm,
        carry,
        genesis,
        ledger,
        gcfg: gcfg.clone(),
        names,
        chain: vec![],
    };
    let mut ch = ch;
    // public genesis: the replica exists from the start (its genesis roots are the public commitment), so that a
    // refusal before the first proof can still rotate (the self-handover)
    if ch.ledger.is_none() && ch.gcfg.is_some() && !join && args.iter().any(|a| a == "--prove") {
        if let Some(g) = ch.genesis.clone() {
            if i == 0 {
                std::fs::write(dir.join("genesis_roots.json"), hex_roots(&g)).expect("genesis roots");
            }
            ch.open_ledger(g).expect("ledger replica");
        }
    }
    Prove {
        me: i,
        on: args.iter().any(|a| a == "--prove"),
        args: args.to_vec(),
        model,
        lp,
        pr,
        tables: darkproof::step::tables(),
        prm,
        gcfg,
        ch: Some(ch),
        worker: None,
        next: None,
        end_step: start + steps,
        deferred: None,
    }
}

/// dl-custodian join: a new committee's seat (see the module doc).
fn join_main(args: &[String]) -> i32 {
    let j: usize = args[2].parse().unwrap();
    let mut pf = darkstep::node::gated(darkstep::node::prof(&args[3..7]), args);
    pf.secure_coins = true;
    pf.program = serve::program_of(args);
    let d = pf.d;
    let dir = PathBuf::from(&args[7]);
    std::fs::create_dir_all(&dir).unwrap();
    let mut hook = prove_hook(args, j, true);
    let mut run = || -> Result<Box<CustodianState>, String> {
        let after: usize = flag(args, "--after-step").ok_or("--after-step K (the old committee's last step)")?.parse().unwrap();
        let addrs: Vec<SocketAddr> = args[8..11].iter().map(|a| a.parse().unwrap()).collect();
        let tlsdir = PathBuf::from(flag(args, "--tls").ok_or("--tls")?);
        let (id, certs) = serve::identity(&tlsdir, j);
        let tls6 = PathBuf::from(flag(args, "--tls6").ok_or("--tls6 DIR6")?);
        let certs6: Vec<Vec<u8>> = (0..6).map(|x| std::fs::read(tls6.join(format!("cert6_{x}.der")))).collect::<Result<_, _>>().map_err(|e| e.to_string())?;
        if certs6[3..] != certs[..] {
            return Err("cert6_3..5 are not this committee's certificates".into());
        }
        let addrs6 = addr_list(&flag(args, "--mesh6").ok_or("--mesh6")?);
        let timeout = timeout_of(args);
        let tape = serve::read_tape(&flag(args, "--handover-tape").ok_or("--handover-tape FILE")?);
        let net3 = serve::connect_mesh(j, &addrs, flag(args, "--listen"), &id, &certs, timeout)?;
        let net6 = serve::connect_mesh(3 + j, &addrs6, flag(args, "--listen6"), &id, &certs6, timeout)?;
        // the ledger replica from the old committee: public, sent by all three, which must agree
        let copies: Vec<Vec<u8>> = (0..3).map(|o| net6.recv(o, darkstep::net::CTRL)).collect();
        if copies.iter().any(|c| c != &copies[0]) {
            return Err("the old custodians sent different ledgers".into());
        }
        hook.c().adopt_ledger(&copies[0])?;
        let (lstep, lepoch) = hook.c().ledger.as_ref().map(|l| (l.step, l.epoch)).unwrap();
        if lstep as usize != after + 1 {
            return Err(format!("the ledger's head is step {lstep}, the handover is after serve step {after} (ledger step {})", after + 1));
        }
        let new_set: Vec<String> = certs.iter().map(|c| darkstep::tls::cert_fingerprint(c)).collect();
        let rns = std::sync::Arc::new(darkstep::rns::Rns::new(pf.n, &pf.qs, pf.t));
        let common = hook.common(rns, d, pf.t, &new_set)?;
        let epoch = lepoch as i64;
        let th = std::thread::Builder::new().stack_size(64 << 20);
        // DEFER: the received replica's pending claims (the old seats discharge them through the handover)
        let pend = hook.c().ledger.as_ref().and_then(|l| l.pending.clone());
        let nc = std::thread::scope(|s| th.spawn_scoped(s, || side::new_side_e(&common, pend.as_ref(), j, net3, net6, tape, epoch + 1, 0, None)).unwrap().join())
            .map_err(|_| "new side panicked".to_string())??;
        if nc.report["mac_check"] != "ok" {
            return Err(format!("the handover's MAC check under the new key failed: {}", nc.report["mac_check"]));
        }
        save_handover_proof(&hook.args, &dir, epoch + 1, &nc.proof)?;
        // the handover tape is spent (its authenticated randoms now mask the reshared weights' MACs)
        if args.iter().any(|a| a == "--wipe-spent") {
            if let Some(f) = flag(args, "--handover-tape") {
                serve::wipe_file(Path::new(&f)).map_err(|e| format!("{f}: {e}"))?;
            }
        }
        hook.c().ledger.as_mut().unwrap().rotate(&new_set, &nc.new_roots, &nc.proof)?;
        let (hs, cer) = nc.keys.ok_or("a rotation makes a fresh key")?;
        let regs: Vec<_> = (0..3).map(|x| cer.registry(x).expect("registered key")).collect();
        let ceremony_s = nc.report.get("ceremony_seconds").and_then(|v| v.as_f64()).unwrap_or(0.0);
        let he = darkstep::node::he_from_ceremony(&pf, nc.key, regs, hs.s.clone(), hs.e.clone(), ceremony_s);
        let mut st = CustodianState::from_parts(j, pf.clone(), he, nc.party, darkhand::serve::shares_rows(&nc.w, d), after + 1);
        if let Some(p) = flag(args, "--tapes") {
            st.load_tape(serve::read_tape(&serve::step_path(args, &p, after + 1)))?;
        }
        // the carried commitment of the reshared weights beside the checkpoint: a pause before this seat's first step
        // resumes from both (serve --resume)
        let carry = joined_carry(nc.carry, nc.defer);
        write_carry(&dir.join(format!("carry_P{j}.bin")), &carry).map_err(|e| format!("carry checkpoint: {e}"))?;
        hook.c().carry = Some(carry);
        hook.next = None;
        st.checkpoint(&dir.join(format!("ckpt_P{j}.bin"))).map_err(|e| e.to_string())?;
        std::fs::write(dir.join(format!("join_P{j}.json")), serde_json::to_string_pretty(&json!({"party": j, "epoch": epoch + 1, "report": nc.report})).unwrap())
            .map_err(|e| e.to_string())?;
        Ok(st)
    };
    let t0 = Instant::now();
    match run() {
        Ok(st) => {
            let setup_s = t0.elapsed().as_secs_f64();
            let code = serve::serve_state(args, &mut hook, st, t0, 0.0, setup_s);
            hook.run_deferred(code)
        }
        Err(e) => {
            eprintln!("join: {e}");
            std::fs::write(dir.join(format!("join_P{j}.json")), serde_json::to_string_pretty(&json!({"party": j, "error": e})).unwrap()).unwrap();
            1
        }
    }
}

/// TEST ONLY: `dl-custodian test-deal CFG STEPS I DIR --genesis-cfg GEN [--program gen6] [--profile P] [--release]
/// [--public] [--split-release]`: seat I's tape from the public-seed test dealer (darkstep's Dealer, kept to seat I's entries) for STEPS
/// carried steps after a public genesis, each with its proof section, then (with --release) the release section
/// (darkproof::run::deal_release, policy mnist_policy at the genesis cfg's M), in the order a custodian consumes
/// them: DIR/tape_I.bin. With --public also the owner's broadcasts DIR/public_step<k>.bin for `dl-owner
/// --test-public`. The values are the run's own: darktrain's encoding of the owner's examples (CFG: the genesis
/// plus "data" and "seed_order").
#[cfg(feature = "test-harness")]
fn test_deal(args: &[String]) {
    let c: darktrain::Cfg = serde_json::from_str(&std::fs::read_to_string(&args[2]).expect("cfg")).expect("cfg json");
    c.validate().unwrap();
    let steps: usize = args[3].parse().unwrap();
    let i: usize = args[4].parse().unwrap();
    let dir = PathBuf::from(&args[5]);
    std::fs::create_dir_all(&dir).unwrap();
    let d = c.d;
    let pf = darkstep::node::prof(&["16384".into(), "4".into(), "175".into(), d.to_string()]);
    darkproof::field::set_p(pf.t);
    let pr = profile_of(args);
    let lp = pr.ligero();
    let program = serve::program_of(args);
    let gbytes = std::fs::read(flag(args, "--genesis-cfg").expect("--genesis-cfg")).unwrap();
    let mut prm = params_of(&program, rs_of(args));
    {
        use sha2::{Digest, Sha256};
        prm.pg = Some(Sha256::digest(&gbytes).into());
    }
    let tables = darkproof::step::tables();
    let own;
    let tb = if prm.t_lo == -128 { &tables } else { own = darkproof::step::tables_for(prm.t_lo); &own };
    let mn = darktrain::data::load(Path::new(&c.data)).unwrap();
    let c = c.with_means(&mn);
    let ord = darktrain::order(c.seed_order, mn.train.n);
    let mut dl = darkstep::tape::Dealer::new(pf.t, 3, darkstep::node::DEALER_SEED);
    dl.proof_rng = Some(pycompat::PyRandom::from_u64(1));
    dl.only = Some(i);
    dl.rs = rs_of(args);
    let mut owner = pycompat::PyRandom::from_u64(darkstep::node::OWNER_SEED);
    for k in 0..steps {
        let ex = ord[k % mn.train.n];
        let (x, y) = darktrain::encode(&c, mn.train.image(ex), mn.train.lab[ex]);
        let xm: Vec<u64> = x.iter().chain(y.iter()).map(|&v| darkstep::arith::from_i64(v, pf.t)).collect();
        let cs = darkstep::tape::deal_one_step(&mut dl, &mut owner, d, &xm, &program);
        darkstep::tape::deal_proof_section(&mut dl, darkproof::run::step_section(&lp, d, prm, prm.carried(k as u64 + 1), tb));
        if args.iter().any(|a| a == "--public") {
            std::fs::write(dir.join(format!("public_step{k}.bin")), darkstep::net::u64s_to_bytes(&cs)).unwrap();
        }
    }
    let mut rel = json!(null);
    let steps_len = dl.tapes[i].len();
    if args.iter().any(|a| a == "--release") {
        let gm = serde_json::from_slice::<Value>(&gbytes).unwrap()["release"]["M"].as_u64().expect("the genesis cfg's release.M") as usize;
        let pol = darkproof::run::mnist_policy(&gbytes, Path::new(&c.data), gm).unwrap();
        let before = dl.tapes[i].len();
        darkproof::run::deal_release(&mut dl, d, gm, pol.ncls, prm, pol.kc, &lp, &tables, &pol);
        rel = json!({"M": gm, "entries": dl.tapes[i].len() - before, "proof_section": darkproof::run::release_section(&lp, d, gm, prm, &pol)});
    }
    let write = |t: &darkstep::tape::Tape, name: String| {
        t.write_to(&mut std::io::BufWriter::new(std::fs::File::create(dir.join(name)).unwrap())).unwrap();
    };
    let t = &dl.tapes[i];
    if args.iter().any(|a| a == "--split-release") && t.len() > steps_len {
        // as in a deployment: the steps' tape and the release's (loaded only when the release starts)
        let part = |r: std::ops::Range<usize>| darkstep::tape::Tape { alpha_i: t.alpha_i, tags: t.tags[r.clone()].to_vec(), sh: t.sh[r.clone()].to_vec(), mac: t.mac[r].to_vec() };
        write(&part(0..steps_len), format!("tape_{i}.bin"));
        write(&part(steps_len..t.len()), format!("release_{i}.bin"));
    } else {
        write(t, format!("tape_{i}.bin"));
    }
    println!("{}", json!({"party": i, "steps": steps, "tape_len": dl.tapes[i].len(), "steps_len": steps_len, "release": rel}));
}

/// The run's proof profile against its tapes, before step 0 (or the first step after a resume or a join): the first
/// step's tape file (--tapes) must hold exactly the step's entries (darkprep's schedule for this program) plus the
/// proof section this profile needs (run::step_section). A chunk made for another profile is refused here instead
/// of dying after its step. A sealed tape's count is read inside its seal (serve::tape_len).
fn check_profile(args: &[String], first: usize) -> Result<(), String> {
    // no step to run (--steps 0: the release alone after a resume): no step tape to check
    if !args.iter().any(|a| a == "--prove") || flag(args, "--steps").as_deref() == Some("0") {
        return Ok(());
    }
    let Some(pat) = flag(args, "--tapes") else { return Ok(()) };
    let path = serve::step_path(args, &pat, first);
    let n = serve::tape_len(&path)?;
    let pf = darkstep::node::prof(&args[3..7]);
    darkproof::field::set_p(pf.t);
    let pr = profile_of(args);
    let lp = pr.ligero();
    let pg = serve::program_of(args);
    let prm = params_of(&pg, rs_of(&args));
    let tables = darkproof::step::tables();
    let own;
    let tb = if prm.t_lo == -128 { &tables } else { own = darkproof::step::tables_for(prm.t_lo); &own };
    let (count, want) = step_entries(&lp, pf.d, &pg, prm, tb);
    if n != want {
        let name = flag(args, "--profile").unwrap_or_else(|| "ledger".into());
        return Err(format!("{path}: {n} entries, but a step with profile {name}'s proof section ({count} triples) needs {want}: the chunk was made for another profile"));
    }
    Ok(())
}

/// A carried proved step's tape: (proof-section triples, total entries) for this program and profile.
fn step_entries(lp: &darkproof::ligero::LigParams, d: usize, pg: &Program, prm: StepParams, tb: &(Vec<u64>, Vec<u64>)) -> (usize, usize) {
    let count = darkproof::run::step_section(lp, d, prm, true, tb);
    use darkprep::schedule::*;
    let sp = StepParams { d, inputs: Inputs::Steady, trunc: [(pg.s1, pg.k1), (pg.s1, pg.k1), (pg.s2, pg.k2), (pg.s3, pg.k3)], proof_atoms: true, proof_triples: count, phase: Phase::Step, rs: prm.rs };
    (count, tags(&sp).len())
}

/// Preprocessing is single-use: a deployed custodian refuses to start without the box's consumed-preprocessing
/// registry (`--consumed-log FILE`, see darkstep::serve::read_tape_once); test builds may run without one.
fn require_consumed_log(args: &[String]) {
    match flag(args, "--consumed-log") {
        Some(l) => serve::set_consumed_log(l.into()),
        None if cfg!(feature = "test-harness") => {}
        None => {
            eprintln!("--consumed-log FILE is required: preprocessing is single-use and every tape loaded is recorded there");
            std::process::exit(2);
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(|s| s.as_str()) {
        #[cfg(feature = "test-harness")]
        Some("test-deal") => test_deal(&args),
        Some("proof-triples") => {
            // dl-custodian proof-triples N L F d [--program P]: the proof section's size after a genesis and a carried step
            let pf = darkstep::node::prof(&args[2..6]);
            darkproof::field::set_p(pf.t);
            let lp = profile_of(&args).ligero();
            let tables = darkproof::step::tables();
            let prm = params_of(&serve::program_of(&args), rs_of(&args));
            let own;
            let tb = if prm.t_lo == -128 { &tables } else { own = darkproof::step::tables_for(prm.t_lo); &own };
            let g = darkproof::run::step_section(&lp, pf.d, prm, false, tb);
            let c = darkproof::run::step_section(&lp, pf.d, prm, true, tb);
            println!("{g},{c}");
        }
        Some("step-entries") => {
            // dl-custodian step-entries N L F d [--program P] [--profile X]: a carried proved step's tape entries
            let pf = darkstep::node::prof(&args[2..6]);
            darkproof::field::set_p(pf.t);
            let lp = profile_of(&args).ligero();
            let tables = darkproof::step::tables();
            let pg = serve::program_of(&args);
            let prm = params_of(&pg, rs_of(&args));
            let own;
            let tb = if prm.t_lo == -128 { &tables } else { own = darkproof::step::tables_for(prm.t_lo); &own };
            let (c, n) = step_entries(&lp, pf.d, &pg, prm, tb);
            println!("{}", json!({"proof_triples": c, "entries": n}));
        }
        Some("close") => {
            serve::set_nat(&args);
            load_vault(&args);
            match close_main(&args) {
                Ok(r) => println!("{r}"),
                Err(e) => {
                    eprintln!("close: {e}");
                    std::process::exit(1);
                }
            }
        }
        Some("vault-init") => {
            if let Err(e) = vault_init(&args) {
                eprintln!("vault-init: {e}");
                std::process::exit(2);
            }
        }
        Some("serve") => {
            serve::set_nat(&args);
            load_vault(&args);
            require_consumed_log(&args);
            let i: usize = args[2].parse().unwrap();
            let first = if args.iter().any(|a| a == "--resume") {
                serve::read_checkpoint(&PathBuf::from(&args[7]).join(format!("ckpt_P{i}.bin"))).map(|c| c.step).unwrap_or(0)
            } else {
                0
            };
            if let Err(e) = check_profile(&args, first) {
                eprintln!("{e}");
                std::process::exit(2);
            }
            let mut hook = prove_hook(&args, i, false);
            let code = serve::serve_main_with(&args, &mut hook, genesis_of(&args));
            std::process::exit(hook.run_deferred(code));
        }
        Some("join") => {
            serve::set_nat(&args);
            load_vault(&args);
            require_consumed_log(&args);
            let after: usize = flag(&args, "--after-step").and_then(|k| k.parse().ok()).unwrap_or(0);
            if let Err(e) = check_profile(&args, after + 1) {
                eprintln!("{e}");
                std::process::exit(2);
            }
            std::process::exit(join_main(&args))
        }
        _ => {
            eprintln!("usage: dl-custodian serve|join|proof-triples ... (see the source's module doc)");
            std::process::exit(2);
        }
    }
}
