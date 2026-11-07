//! The handover hooks of `dl-custodian` as processes over pinned TLS (ledger profile, d = 64, gated T = 309, public
//! genesis, every step proved and accepted by each custodian's ledger replica):
//! - rotation: the old committee runs step 0 and hands over (--handover-at 0); three new processes (`join`) run the
//!   new ceremony, receive the reshared weights, rotate their ledger replicas and run step 1 under their own MAC key;
//!   the old seats' state files are gone and their reports say the old key no longer decrypts;
//! - self-handover after an abort: seat 1 corrupts an outer return in step 0 (test attack), all three refuse, recover
//!   from their checkpoints, rotate to the same set at epoch 1 with a new MAC key, and redo step 0, then step 1.
//! In both the revealed weights (test only) equal the plaintext twin after 2 steps, and not after 1 (control).
//! Run one at a time (`-- --test-threads=1`).
use darkstep::node::{prof, DEALER_SEED, OWNER_SEED};
use darkstep::party::Sh;
use darkstep::step::{Plain, Program};
use darkstep::tape::{Dealer, Tape};
use std::path::{Path, PathBuf};
use std::process::Command;

const A: [&str; 4] = ["16384", "4", "175", "64"];
const CFG: &[u8] = br#"{"d": 64, "hid": 64, "reps": 1, "tile": 0, "bias": false, "seed_init": 1, "a1": 0, "a2": 3}"#;

fn free_port() -> u16 {
    std::net::TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port()
}

fn ports(n: usize) -> Vec<String> {
    (0..n).map(|_| format!("127.0.0.1:{}", free_port())).collect()
}

/// A port held by a listener that never accepts: a NAT seat given it as its address must neither bind it (the bind
/// would fail) nor be dialled at it (the TLS handshake would never finish).
fn blocked() -> (std::net::TcpListener, String) {
    let l = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
    let a = format!("127.0.0.1:{}", l.local_addr().unwrap().port());
    (l, a)
}

fn write_tape(t: &Tape, p: &Path) {
    t.write_to(&mut std::io::BufWriter::new(std::fs::File::create(p).unwrap())).unwrap();
}

/// Empty each tape (same MAC key share): the next section goes to its own file.
fn cut(dl: &mut Dealer) {
    for t in dl.tapes.iter_mut() {
        *t = Tape { alpha_i: t.alpha_i, ..Default::default() };
    }
}

struct Case {
    base: PathBuf,
    d: usize,
    t: u64,
    xs: Vec<Vec<i64>>,
    c: usize,
}

/// The proof profile under test: DL_PROFILE (default "ledger"), and DL_RS=1 for the program flag RS (its tapes deal
/// K + 1 - s bits per truncation). E.g. DL_PROFILE=ledger-x2de DL_RS=1 runs every case under cut E (DEFER).
fn prof_args() -> Vec<String> {
    let mut v = vec!["--profile".to_string(), std::env::var("DL_PROFILE").unwrap_or_else(|_| "ledger".into())];
    if rs() {
        v.push("--rs".into());
    }
    // DL_EXTRA: more serve flags for every custodian (e.g. "--ret-round")
    if let Ok(x) = std::env::var("DL_EXTRA") {
        v.extend(x.split_whitespace().map(String::from));
    }
    v
}

fn rs() -> bool {
    std::env::var("DL_RS").is_ok_and(|v| v == "1")
}

impl Case {
    fn new(name: &str) -> Case {
        let pf = prof(&A.map(String::from));
        let base = std::env::temp_dir().join(format!("dl-handover-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&base);
        std::fs::create_dir_all(&base).unwrap();
        std::fs::write(base.join("genesis.json"), CFG).unwrap();
        let out = Command::new(env!("CARGO_BIN_EXE_dl-custodian")).arg("proof-triples").args(A).args(prof_args()).output().unwrap();
        let c: usize = String::from_utf8(out.stdout).unwrap().trim().split_once(',').unwrap().1.parse().unwrap();
        let xs = (0..2)
            .map(|s| {
                let mut r = pycompat::PyRandom::from_u64(3000 + s as u64);
                (0..2 * pf.d).map(|_| r.randint_i64(-7, 7)).collect()
            })
            .collect();
        Case { base, d: pf.d, t: pf.t, xs, c }
    }

    /// Deal step `s` (and its proof section) on `dl`; the owner's broadcasts.
    fn deal(&self, dl: &mut Dealer, owner: &mut pycompat::PyRandom, s: usize) -> Vec<u64> {
        dl.rs = rs();
        let xm: Vec<u64> = self.xs[s].iter().map(|&v| darkstep::arith::from_i64(v, self.t)).collect();
        let cs = darkstep::tape::deal_one_step(dl, owner, self.d, &xm, &Program::HARNESS);
        darkstep::tape::deal_proof_section(dl, self.c);
        cs
    }

    /// A seat dir with its TLS identity and the committee's certificates.
    fn seat(&self, name: &str, i: usize, ids: &[darkstep::tls::Identity], owner: &darkstep::tls::Identity) -> PathBuf {
        let own = self.base.join(name);
        std::fs::create_dir_all(own.join("D")).unwrap();
        for j in 0..3 {
            std::fs::write(own.join(format!("cert_{j}.der")), &ids[j].cert_der).unwrap();
        }
        std::fs::write(own.join("cert_owner.der"), &owner.cert_der).unwrap();
        std::fs::write(own.join(format!("tls_{i}.key")), &ids[i].key_der).unwrap();
        own
    }

    fn twin(&self, steps: usize) -> Vec<i64> {
        let (_, w1, w2) = darkproof::run::public_weights(CFG).unwrap();
        let d = self.d;
        let rows = |w: &[i64]| -> Vec<Vec<i64>> { w.chunks(d).map(|r| r.to_vec()).collect() };
        let mut pl = Plain { w1: rows(&w1), w2: rows(&w2), x: vec![], y: vec![] };
        let pg = Program { wmax: None, check_k: true, ..Program::HARNESS };
        for x in &self.xs[..steps] {
            pl.x = x[..d].to_vec();
            pl.y = x[d..].to_vec();
            let (a, b) = pl.step_prog(&pg).unwrap();
            pl.w1 = a;
            pl.w2 = b;
        }
        pl.w1.iter().chain(pl.w2.iter()).flatten().copied().collect()
    }

    fn revealed(&self, dirs: &[PathBuf], idx: &[usize]) -> Vec<i64> {
        let shares: Vec<Vec<Sh>> = dirs
            .iter()
            .zip(idx)
            .map(|(dir, i)| {
                let v = darkstep::net::bytes_to_u64s(&std::fs::read(dir.join(format!("shares_{i}.bin"))).unwrap());
                v.chunks(2).map(|c| Sh { s: c[0], m: c[1] }).collect()
            })
            .collect();
        let p = self.t;
        let cen = |v: u64| if v > p / 2 { v as i64 - p as i64 } else { v as i64 };
        (0..2 * self.d * self.d).map(|k| cen(shares.iter().fold(0, |a, s| darkstep::arith::addmod(a, s[k].s, p)))).collect()
    }
}

fn json(p: &Path) -> serde_json::Value {
    serde_json::from_str(&std::fs::read_to_string(p).unwrap_or_else(|e| panic!("{}: {e}", p.display()))).unwrap()
}

/// The owner as a thread: one session per committee (certificates), each serving the steps it asks for.
fn owner(at: &str, id: darkstep::tls::Identity, sessions: Vec<(Vec<Vec<u8>>, Vec<Vec<u64>>)>) -> std::thread::JoinHandle<()> {
    let l = std::net::TcpListener::bind(at).unwrap();
    std::thread::spawn(move || {
        for (certs, cs) in sessions {
            darkstep::serve::owner_serve(l.try_clone().unwrap(), &id, &certs, |k, _| cs.get(k).cloned().filter(|c| !c.is_empty()).ok_or(format!("no step {k}"))).unwrap();
        }
    })
}

fn run(args: Vec<String>) -> std::process::Child {
    Command::new(env!("CARGO_BIN_EXE_dl-custodian")).args(args).env("DS_THREADS", "4").spawn().unwrap()
}

fn s(v: &[&str]) -> Vec<String> {
    v.iter().map(|x| x.to_string()).collect()
}

#[test]
fn rotation_to_a_new_committee_after_step_0() {
    rotation(false, None);
}

/// Seat 0 of each committee is a NAT seat (--nat 0, --nat6 0,3): it listens on no port of its three-party mesh
/// (its address there is a port held by a listener that never accepts) and dials every peer; in the six-party mesh
/// the old and new seat 0 share the box, the old one's loopback address taking the new one's dial.
#[test]
fn rotation_with_a_nat_seat() {
    rotation(false, Some(0));
}

/// The new committee pauses (forge's nightly window) before its first step, right after the handover: each joined
/// seat checkpointed, gives its unused first tape back to the box registry and exits 3; `serve --resume` in its own
/// dir (run.py's resume_new) then runs step 1 under the new key, at epoch 1, from that checkpoint.
#[test]
fn the_new_committee_pauses_and_resumes_as_serve() {
    rotation(true, None);
}

/// "HH:MM-HH:MM" from this UTC minute to 15 minutes on.
fn window_now() -> String {
    let m = (std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_secs() / 60) % 1440;
    let f = |m: u64| format!("{:02}:{:02}", (m % 1440) / 60, m % 60);
    format!("{}-{}", f(m), f(m + 15))
}

/// `dl-custodian vault-init` for a seat dir: its file key in the uid's persistent keyring, its TLS key sealed.
fn vault_init(own: &Path, i: usize, epoch: u64) -> String {
    let o = Command::new(env!("CARGO_BIN_EXE_dl-custodian")).args(["vault-init", &i.to_string(), own.to_str().unwrap(), "--epoch", &epoch.to_string()]).output().unwrap();
    assert!(o.status.success(), "vault-init: {}", String::from_utf8_lossy(&o.stderr));
    assert!(std::fs::read(own.join(format!("tls_{i}.key"))).unwrap().starts_with(darkhand::vault::MAGIC), "the TLS key is sealed");
    std::fs::read_to_string(own.join("vault.name")).unwrap()
}

fn sealed(p: &Path) -> bool {
    std::fs::read(p).map(|b| b.starts_with(darkhand::vault::MAGIC)).unwrap_or(false)
}

/// Under the vault (Linux: the kernel's persistent keyring): every state file is sealed under the epoch's file key.
/// The old seats' keys are destroyed at the erasure (the sealed copies kept before it open under no key the uid
/// holds); the new seats' files are sealed under theirs, and after a pause `serve --resume` loads it from the
/// keyring in a new process and goes on.
#[cfg(target_os = "linux")]
#[test]
fn rotation_sealed_under_the_vault() {
    rotation_v(true, None, true);
}

/// Seat i's MP-SPDZ runtime files (relative to RT): (its secrets, in every field; what stays).
fn runtime_files(i: usize) -> (Vec<String>, Vec<String>) {
    let o = (i + 1) % 3;
    (
        vec![
            format!("Player-Data/Mascot-Secrets-p-61-519717d8-P{i}-3"),
            format!("Player-Data/Mascot-Secrets-2-128-9a50bc35-P{i}-3"),
            format!("Player-Data/Mascot-Secrets-B-64-fe992139-P{i}-3"),
            format!("Player-Data/Memory-p-P{i}"),
            format!("Player-Data/3-p-61/Player-MAC-Keys-p-P{i}"),
            format!("Player-Data/3-2-128/Player-MAC-Keys-2-P{i}"),
            format!("Persistence/Transactions-P{i}.data"),
        ],
        vec![format!("Player-Data/P{i}.pem"), format!("Player-Data/P{i}.key"), "Player-Data/PairwiseParams-0".into(), format!("Player-Data/Mascot-Secrets-p-61-519717d8-P{o}-3")],
    )
}

fn runtime(own: &Path, i: usize) -> PathBuf {
    let rt = own.join("mpspdz");
    let ram = own.join("ram-player-data");
    std::fs::create_dir_all(&rt).unwrap();
    std::fs::create_dir_all(&ram).unwrap();
    std::os::unix::fs::symlink(&ram, rt.join("Player-Data")).unwrap();
    let (a, b) = runtime_files(i);
    for f in a.iter().chain(b.iter()) {
        let p = rt.join(f);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(&p, format!("secret-or-public {f}")).unwrap();
    }
    rt
}

fn rotation(pause: bool, nat: Option<usize>) {
    rotation_v(pause, nat, false)
}

fn rotation_v(pause: bool, nat: Option<usize>, vault: bool) {
    let cs = Case::new(if vault { "rotv" } else if pause { "rotp" } else if nat.is_some() { "rotn" } else { "rot" });
    let mut vnames: Vec<String> = vec![];
    let d = cs.d;
    // the old committee's tape: step 0; the new committee's: its handover section (2 d^2 + 16 authenticated randoms)
    // and then step 1, under its own MAC key
    let mut old = Dealer::new(cs.t, 3, DEALER_SEED);
    old.proof_rng = Some(pycompat::PyRandom::from_u64(1));
    let mut om = pycompat::PyRandom::from_u64(OWNER_SEED);
    let c0 = cs.deal(&mut old, &mut om, 0);
    let mut new = Dealer::new(cs.t, 3, DEALER_SEED + 1000);
    new.proof_rng = Some(pycompat::PyRandom::from_u64(2));
    for _ in 0..2 * d * d + 2 {
        new.auth_plain();
    }
    let hand: Vec<Tape> = new.tapes.clone();
    cut(&mut new);
    let mut nm = pycompat::PyRandom::from_u64(OWNER_SEED + 1000);
    let c1 = cs.deal(&mut new, &mut nm, 1);
    assert_ne!(old.alpha, new.alpha, "the new committee has its own MAC key");
    let ids: Vec<darkstep::tls::Identity> = (0..7).map(darkstep::tls::generate).collect();
    let oid = &ids[6];
    let (oldids, newids) = (&ids[..3], &ids[3..6]);
    let mesh6 = ports(6).join(",");
    let (mut a_old, mut a_new, o_at) = (ports(3), ports(3), ports(1).remove(0));
    let mut hold = Vec::new();
    let mut natf: Vec<String> = vec![];
    if let Some(n) = nat {
        for a in [&mut a_old, &mut a_new] {
            let (l, b) = blocked();
            a[n] = b;
            hold.push(l);
        }
        natf = s(&["--nat", &n.to_string(), "--nat6", &format!("{n},{}", 3 + n)]);
    }
    let tls6 = cs.base.join("tls6");
    std::fs::create_dir_all(&tls6).unwrap();
    for j in 0..6 {
        std::fs::write(tls6.join(format!("cert6_{j}.der")), &ids[j].cert_der).unwrap();
    }
    let ow = owner(&o_at, darkstep::tls::Identity { key_der: oid.key_der.clone(), cert_der: oid.cert_der.clone() }, vec![
        (oldids.iter().map(|x| x.cert_der.clone()).collect(), vec![c0]),
        (newids.iter().map(|x| x.cert_der.clone()).collect(), vec![vec![], c1.clone()]),
    ]
    .into_iter()
    .chain(pause.then(|| (newids.iter().map(|x| x.cert_der.clone()).collect(), vec![vec![], c1.clone()])))
    .collect());
    let reg = cs.base.join("consumed_new.jsonl");
    let gen = cs.base.join("genesis.json").to_str().unwrap().to_string();
    let mut kids = Vec::new();
    let mut odirs = Vec::new();
    for i in 0..3 {
        let own = cs.seat(&format!("old{i}"), i, oldids, oid);
        write_tape(&old.tapes[i], &own.join("tape.bin"));
        let mut natf = natf.clone();
        if vault {
            vnames.push(vault_init(&own, i, 0));
            natf.extend(s(&["--vault", "--keep-erased-copy", own.join("erased").to_str().unwrap()]));
        }
        // its MP-SPDZ runtime as prep lays it out: Player-Data a symlink (into tmpfs on the boxes), every field's
        // secrets of this seat, its public files, and another party's secret (a loopback runtime holds all three)
        let rt = runtime(&own, i);
        natf.extend(s(&["--erase-runtime", rt.to_str().unwrap()]));
        let mut a = s(&["serve", &i.to_string()]);
        a.extend(s(&A));
        a.push(own.join("D").to_str().unwrap().into());
        a.extend(a_old.clone());
        a.extend(s(&["--tls", own.to_str().unwrap(), "--owner", &o_at, "--steps", "1", "--gate", "309", "--ret-primes", "2", "--timeout", "180"]));
        a.extend(s(&["--tape", own.join("tape.bin").to_str().unwrap(), "--prove", "--genesis-cfg", &gen, "--handover-at", "0"]));
        a.extend(s(&["--mesh6", &mesh6, "--tls6", tls6.to_str().unwrap()]));
        a.extend(natf.clone());
        a.extend(prof_args());
        kids.push(run(a));
        odirs.push(own);
    }
    let mut ndirs = Vec::new();
    for j in 0..3 {
        let own = cs.seat(&format!("new{j}"), j, newids, oid);
        write_tape(&hand[j], &own.join("handover.bin"));
        let mut natf = natf.clone();
        if vault {
            vnames.push(vault_init(&own, j, 1));
            natf.push("--vault".into());
        }
        write_tape(&new.tapes[j], &own.join("tape1.bin"));
        let mut a = s(&["join", &j.to_string()]);
        a.extend(s(&A));
        a.push(own.join("D").to_str().unwrap().into());
        a.extend(a_new.clone());
        a.extend(s(&["--tls", own.to_str().unwrap(), "--owner", &o_at, "--steps", "1", "--after-step", "0", "--gate", "309", "--ret-primes", "2"]));
        a.extend(s(&["--timeout", "180", "--handover-tape", own.join("handover.bin").to_str().unwrap(), "--tapes", own.join("tape1.bin").to_str().unwrap()]));
        a.extend(s(&["--prove", "--genesis-cfg", &gen, "--mesh6", &mesh6, "--tls6", tls6.to_str().unwrap(), "--test-keep-shares", "--wipe-spent"]));
        if pause {
            a.extend(s(&["--pause-utc", &window_now(), "--consumed-log", reg.to_str().unwrap()]));
        }
        a.extend(natf.clone());
        a.extend(prof_args());
        kids.push(run(a));
        ndirs.push(own);
    }
    let codes: Vec<i32> = kids.into_iter().map(|mut k| k.wait().unwrap().code().unwrap_or(-1)).collect();
    if pause {
        assert_eq!(codes, vec![0, 0, 0, 3, 3, 3], "the old seats hand over; the new ones pause before step 1");
        let r = std::fs::read_to_string(&reg).unwrap();
        assert_eq!(r.lines().filter(|l| l.contains("\"released\":true")).count(), 3, "each new seat gave its unused tape back: {r}");
        let a_res = ports(3);
        let kids: Vec<_> = (0..3)
            .map(|j| {
                let own = &ndirs[j];
                let mut a = s(&["serve", &j.to_string()]);
                a.extend(s(&A));
                a.push(own.join("D").to_str().unwrap().into());
                a.extend(a_res.clone());
                a.extend(s(&["--tls", own.to_str().unwrap(), "--owner", &o_at, "--steps", "1", "--gate", "309", "--ret-primes", "2", "--timeout", "180"]));
                a.extend(s(&["--tapes", own.join("tape1.bin").to_str().unwrap(), "--prove", "--genesis-cfg", &gen, "--test-keep-shares", "--wipe-spent", "--resume"]));
                a.extend(s(&["--consumed-log", reg.to_str().unwrap()]));
                if vault {
                    a.push("--vault".into());
                }
                a.extend(prof_args());
                run(a)
            })
            .collect();
        let codes: Vec<i32> = kids.into_iter().map(|mut k| k.wait().unwrap().code().unwrap_or(-1)).collect();
        assert_eq!(codes, vec![0; 3], "the new committee resumed as serve");
    } else {
        assert_eq!(codes, vec![0; 6], "every old and new seat exits 0");
    }
    ow.join().unwrap();
    drop(hold);
    for (i, own) in odirs.iter().enumerate() {
        let r = json(&own.join("D").join(format!("handover_P{i}.json")));
        assert_eq!(r["pre_handover_decrypts"], true, "old seat {i}: its key decrypted before the handover (control)");
        if vault {
            let e = own.join("erased");
            for f in [e.join(format!("ckpt_P{i}.bin")), e.join(format!("carry_P{i}.bin")), e.join(format!("tls_{i}.key"))] {
                assert!(sealed(&f), "old seat {i}: {} was sealed before the erasure", f.display());
            }
            let va = &r["vault_after_erasure"];
            assert_eq!(va["key_in_keyring"], false, "old seat {i}: its file key is gone from the keyring: {va}");
            assert!(darkhand::vault::Vault::load(&vnames[i]).is_err(), "old seat {i}: nothing loads its file key");
            let copies = va["sealed_copies"].as_array().unwrap();
            assert!(!copies.is_empty() && copies.iter().all(|c| c["opens_by_keyring"] == false && c["opens_by_zero_key"] == false), "{va}");
        }
        let rt = own.join("mpspdz");
        for f in runtime_files(i).0 {
            assert!(!rt.join(&f).exists(), "old seat {i}: its MP-SPDZ secret {f} was erased (--erase-runtime)");
        }
        for f in runtime_files(i).1 {
            assert!(rt.join(&f).exists(), "old seat {i}: {f} (public, or another party's) stays");
        }
        eprintln!("old seat {i} handover report: {r}");
        for f in [own.join("D").join(format!("ckpt_P{i}.bin")), own.join("D").join(format!("carry_P{i}.bin")), own.join(format!("tls_{i}.key")), own.join("tape.bin")] {
            assert!(!f.exists(), "old seat {i}: {} was wiped", f.display());
        }
    }
    for (j, own) in ndirs.iter().enumerate() {
        let st = json(&own.join("D").join(format!("step_1_P{j}.json")));
        assert_eq!(st["verdict"], "ACCEPT");
        assert_eq!(st["after_step"]["verified"], true, "new seat {j}: step 1's bundle accepted by its ledger replica");
        assert_eq!(st["after_step"]["epoch"], 1, "step 1 is proved at the new epoch");
        let lg = std::fs::read_to_string(own.join("D").join(format!("ledger_P{j}.jsonl"))).unwrap();
        assert!(lg.contains("\"kind\": \"rotate\""), "new seat {j}: the rotation is on its ledger");
        // the handover proof is kept (public), and its sha256 is the one on the ledger
        let hp = std::fs::read(own.join("D").join("handover_e1.bin")).unwrap();
        use sha2::Digest;
        assert!(lg.contains(&pycompat::repr::hex(&sha2::Sha256::digest(&hp))), "new seat {j}: handover_e1.bin is the rotated proof");
        assert!(!own.join("tape1.bin").exists(), "new seat {j}: the spent step's tape was wiped (--wipe-spent)");
        if vault {
            assert!(sealed(&own.join("D").join(format!("ckpt_P{j}.bin"))) && sealed(&own.join("D").join(format!("carry_P{j}.bin"))), "new seat {j}: its state is sealed");
            // the run is over: its file key goes too (it would expire with the keyring otherwise)
            darkhand::vault::Vault::load(&vnames[3 + j]).unwrap().destroy();
        }
    }
    let dirs: Vec<PathBuf> = ndirs.iter().map(|o| o.join("D")).collect();
    let got = cs.revealed(&dirs, &[0, 1, 2]);
    assert_ne!(got, cs.twin(1), "control: not the weights after one step");
    assert_eq!(got, cs.twin(2), "rotation after step 0, step 1 by the new committee = the twin after 2 steps");
    std::fs::remove_dir_all(&cs.base).ok();
}

#[test]
fn self_handover_after_an_abort_redoes_the_step() {
    self_handover(None);
}

/// Seat 1 is a NAT seat (--nat 1, --nat6 1,4) in the main, the recovery and the six-party mesh of its own two roles.
#[test]
fn self_handover_with_a_nat_seat() {
    self_handover(Some(1));
}

/// The self-handover under the vault: the old role destroys the epoch-0 file key; the seat reseals its TLS key and
/// its state under a new epoch-1 key (vault.name follows), which loads from the keyring.
#[cfg(target_os = "linux")]
#[test]
fn self_handover_sealed_under_the_vault() {
    self_handover_v(None, true);
}

fn self_handover(nat: Option<usize>) {
    self_handover_v(nat, false)
}

fn self_handover_v(nat: Option<usize>, vault: bool) {
    let cs = Case::new(if vault { "selfv" } else if nat.is_some() { "selfn" } else { "self" });
    let mut vnames: Vec<String> = vec![];
    let d = cs.d;
    let mut old = Dealer::new(cs.t, 3, DEALER_SEED);
    old.proof_rng = Some(pycompat::PyRandom::from_u64(1));
    let mut om = pycompat::PyRandom::from_u64(OWNER_SEED);
    let c0 = cs.deal(&mut old, &mut om, 0);
    // after the abort: a new MAC key, the handover section, then steps 0 (redone) and 1
    let mut new = Dealer::new(cs.t, 3, DEALER_SEED + 2000);
    new.proof_rng = Some(pycompat::PyRandom::from_u64(3));
    for _ in 0..2 * d * d + 2 {
        new.auth_plain();
    }
    let hand: Vec<Tape> = new.tapes.clone();
    cut(&mut new);
    let mut nm = pycompat::PyRandom::from_u64(OWNER_SEED + 2000);
    let r0 = cs.deal(&mut new, &mut nm, 0);
    let t0: Vec<Tape> = new.tapes.clone();
    cut(&mut new);
    let r1 = cs.deal(&mut new, &mut nm, 1);
    let ids: Vec<darkstep::tls::Identity> = (0..4).map(darkstep::tls::generate).collect();
    let oid = &ids[3];
    let certs: Vec<Vec<u8>> = ids[..3].iter().map(|x| x.cert_der.clone()).collect();
    let (mut a3, mut r3, ar6, o_at) = (ports(3), ports(3), ports(6).join(","), ports(1).remove(0));
    let mut hold = Vec::new();
    let mut natf: Vec<String> = vec![];
    if let Some(n) = nat {
        for a in [&mut a3, &mut r3] {
            let (l, b) = blocked();
            a[n] = b;
            hold.push(l);
        }
        natf = s(&["--nat", &n.to_string(), "--nat6", &format!("{n},{}", 3 + n)]);
    }
    let ar3 = r3.join(",");
    let ow = owner(&o_at, darkstep::tls::Identity { key_der: oid.key_der.clone(), cert_der: oid.cert_der.clone() }, vec![(certs.clone(), vec![c0]), (certs.clone(), vec![r0, r1])]);
    let gen = cs.base.join("genesis.json").to_str().unwrap().to_string();
    let mut kids = Vec::new();
    let mut dirs = Vec::new();
    for i in 0..3 {
        let own = cs.seat(&format!("seat{i}"), i, &ids[..3], oid);
        write_tape(&old.tapes[i], &own.join("tape.bin"));
        write_tape(&hand[i], &own.join("handover.bin"));
        write_tape(&t0[i], &own.join("tape2_0.bin"));
        write_tape(&new.tapes[i], &own.join("tape2_1.bin"));
        let mut a = s(&["serve", &i.to_string()]);
        a.extend(s(&A));
        a.push(own.join("D").to_str().unwrap().into());
        a.extend(a3.clone());
        a.extend(s(&["--tls", own.to_str().unwrap(), "--owner", &o_at, "--steps", "2", "--gate", "309", "--ret-primes", "2", "--timeout", "180"]));
        a.extend(s(&["--tape", own.join("tape.bin").to_str().unwrap(), "--prove", "--genesis-cfg", &gen, "--test-keep-shares"]));
        a.extend(s(&["--self-handover-tape", own.join("handover.bin").to_str().unwrap(), "--recover-mesh", &ar3, "--recover-mesh6", &ar6]));
        a.extend(s(&["--tapes2", own.join("tape2_{k}.bin").to_str().unwrap()]));
        if i == 1 {
            a.extend(s(&["--attack", "wrong_return:1"]));
        }
        // the old epoch's MP-SPDZ runtime: all of it goes at the self-handover (the seat's next key is its own)
        let rt = runtime(&own, i);
        a.extend(s(&["--erase-runtime", rt.to_str().unwrap()]));
        a.extend(natf.clone());
        if vault {
            vnames.push(vault_init(&own, i, 0));
            a.extend(s(&["--vault", "--keep-erased-copy", own.join("erased").to_str().unwrap()]));
        }
        a.extend(prof_args());
        kids.push(run(a));
        dirs.push(own.join("D"));
    }
    let codes: Vec<i32> = kids.into_iter().map(|mut k| k.wait().unwrap().code().unwrap_or(-1)).collect();
    assert_eq!(codes, vec![0, 0, 0], "all three recover and finish");
    ow.join().unwrap();
    drop(hold);
    for (i, dir) in dirs.iter().enumerate() {
        let r = json(&dir.join(format!("self_handover_P{i}.json")));
        assert_eq!(r["redo_step"], 0);
        let rt = dir.parent().unwrap().join("mpspdz");
        for f in runtime_files(i).0 {
            assert!(!rt.join(&f).exists(), "seat {i}: the old epoch's MP-SPDZ secret {f} was erased (--erase-runtime)");
        }
        for f in runtime_files(i).1 {
            assert!(rt.join(&f).exists(), "seat {i}: {f} (public, or another party's) stays");
        }
        if vault {
            let own = dir.parent().unwrap();
            let va = &r["old_role"]["vault_after_erasure"];
            assert_eq!(va["key_in_keyring"], false, "seat {i}: the epoch-0 file key is gone: {va}");
            assert!(darkhand::vault::Vault::load(&vnames[i]).is_err());
            let now = std::fs::read_to_string(own.join("vault.name")).unwrap();
            assert_ne!(now, vnames[i], "seat {i}: a new epoch's file key");
            let v = darkhand::vault::Vault::load(&now).expect("the epoch-1 key loads from the keyring");
            assert!(v.open_file(&own.join(format!("tls_{i}.key")), "tls").is_ok(), "seat {i}: its TLS key is resealed under it");
            assert!(v.open_file(&dir.join(format!("ckpt_P{i}.bin")), "ckpt").is_ok(), "seat {i}: its checkpoint is sealed under it");
            v.destroy();
        }
        assert_eq!(r["epoch"], 1);
        for k in 0..2 {
            let st = json(&dir.join(format!("step_{k}_P{i}.json")));
            assert_eq!(st["verdict"], "ACCEPT", "seat {i} step {k} (redone under the new MAC key)");
            assert_eq!(st["after_step"]["verified"], true);
            assert_eq!(st["after_step"]["epoch"], 1);
        }
        let lg = std::fs::read_to_string(dir.join(format!("ledger_P{i}.jsonl"))).unwrap();
        assert!(lg.contains("\"kind\": \"rotate\""), "seat {i}: the self-rotation is on its ledger");
    }
    let got = cs.revealed(&dirs, &[0, 1, 2]);
    assert_ne!(got, cs.twin(1), "control: not the weights after one step");
    assert_eq!(got, cs.twin(2), "abort in step 0, self-handover, steps 0 and 1 = the twin after 2 steps");
    std::fs::remove_dir_all(&cs.base).ok();
}
