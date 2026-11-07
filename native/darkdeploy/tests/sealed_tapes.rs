//! Sealed preprocessing (Linux: the kernel keyring): each seat's chunk tapes sealed under its epoch's file key with
//! the role "tape|<chunk>|<j>" (as the prep lane writes them); `--vault` custodians open them and run. Control: a
//! tape sealed under another chunk's role is refused. Run one at a time (`-- --test-threads=1`).
#![cfg(target_os = "linux")]
use darkstep::node::{prof, DEALER_SEED, OWNER_SEED};
use darkstep::step::Program;
use darkstep::tape::{Dealer, Tape};
use std::path::{Path, PathBuf};
use std::process::Command;

const A: [&str; 4] = ["16384", "4", "175", "64"];
const CFG: &[u8] = br#"{"d": 64, "hid": 64, "reps": 1, "tile": 0, "bias": false, "seed_init": 1, "a1": 0, "a2": 3}"#;

fn free_port() -> u16 {
    std::net::TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port()
}

fn write_tape(t: &Tape, p: &Path) {
    t.write_to(&mut std::io::BufWriter::new(std::fs::File::create(p).unwrap())).unwrap();
}

/// One launch of the three custodians for `steps` steps (and the owner as a thread); returns codes and stderr.
fn launch(base: &Path, ids: &[darkstep::tls::Identity], cs: &[Vec<u64>], steps: usize, extra: &[&str]) -> (Vec<i32>, Vec<String>) {
    let ports: Vec<u16> = (0..4).map(|_| free_port()).collect();
    let addrs: Vec<String> = (0..3).map(|j| format!("127.0.0.1:{}", ports[j])).collect();
    let owner_at = format!("127.0.0.1:{}", ports[3]);
    let l = std::net::TcpListener::bind(&owner_at).unwrap();
    let oid = darkstep::tls::Identity { key_der: ids[3].key_der.clone(), cert_der: ids[3].cert_der.clone() };
    let certs: Vec<Vec<u8>> = ids[..3].iter().map(|x| x.cert_der.clone()).collect();
    let cs = cs.to_vec();
    std::thread::spawn(move || darkstep::serve::owner_serve(l, &oid, &certs, |k, _| cs.get(k).cloned().ok_or("no step".into())));
    let kids: Vec<_> = (0..3)
        .map(|i| {
            let own = base.join(format!("seat{i}"));
            Command::new(env!("CARGO_BIN_EXE_dl-custodian"))
                .args(["serve", &i.to_string()])
                .args(A)
                .arg(own.join("D"))
                .args(&addrs)
                .args(["--tls", own.to_str().unwrap(), "--owner", &owner_at, "--steps", &steps.to_string(), "--gate", "309", "--ret-primes", "2"])
                .args(["--tapes", own.join(format!("ch{{c}}/step-{{j}}/tape_{i}.bin")).to_str().unwrap(), "--chunk-steps", "1", "--timeout", "30"])
                .args(["--genesis-cfg", base.join("genesis.json").to_str().unwrap()])
                .args(["--consumed-log", base.join(format!("consumed_box{}.jsonl", i.min(1))).to_str().unwrap()])
                .args(extra)
                .env("DS_THREADS", "4")
                .stderr(std::process::Stdio::piped())
                .spawn()
                .unwrap()
        })
        .collect();
    let outs: Vec<std::process::Output> = kids.into_iter().map(|k| k.wait_with_output().unwrap()).collect();
    (outs.iter().map(|o| o.status.code().unwrap_or(-1)).collect(), outs.iter().map(|o| String::from_utf8_lossy(&o.stderr).to_string()).collect())
}


/// Seat dirs under `base` with step 0's and step 1's tapes in chunks ch0 and ch1; ch0 complete, ch1 without its marker.
fn prepare(base: &Path) -> (Vec<darkstep::tls::Identity>, Vec<Vec<u64>>) {
    let pf = prof(&A.map(String::from));
    let _ = std::fs::remove_dir_all(base);
    std::fs::create_dir_all(base).unwrap();
    std::fs::write(base.join("genesis.json"), CFG).unwrap();
    let mut dl = Dealer::new(pf.t, 3, DEALER_SEED);
    let mut owner = pycompat::PyRandom::from_u64(OWNER_SEED);
    let mut cs = vec![];
    let mut tapes: Vec<Vec<Tape>> = vec![];
    for s in 0..2 {
        let mut r = pycompat::PyRandom::from_u64(4000 + s);
        let xm: Vec<u64> = (0..2 * pf.d).map(|_| darkstep::arith::from_i64(r.randint_i64(-7, 7), pf.t)).collect();
        cs.push(darkstep::tape::deal_one_step(&mut dl, &mut owner, pf.d, &xm, &Program::HARNESS));
        tapes.push(dl.tapes.clone());
        for t in dl.tapes.iter_mut() {
            *t = Tape { alpha_i: t.alpha_i, ..Default::default() };
        }
    }
    let ids: Vec<darkstep::tls::Identity> = (0..4).map(darkstep::tls::generate).collect();
    for i in 0..3 {
        let own = base.join(format!("seat{i}"));
        for j in 0..3 {
            std::fs::create_dir_all(&own).unwrap();
            std::fs::write(own.join(format!("cert_{j}.der")), &ids[j].cert_der).unwrap();
        }
        std::fs::write(own.join("cert_owner.der"), &ids[3].cert_der).unwrap();
        std::fs::write(own.join(format!("tls_{i}.key")), &ids[i].key_der).unwrap();
        for (s, ts) in tapes.iter().enumerate() {
            let sd = own.join(format!("ch{s}/step-0"));
            std::fs::create_dir_all(&sd).unwrap();
            write_tape(&ts[i], &sd.join(format!("tape_{i}.bin")));
        }
        std::fs::write(own.join(format!("ch0/chunk-P{i}.json")), b"{}").unwrap();
    }
    (ids, cs)
}

fn vault_init(own: &Path, i: usize) -> String {
    let o = Command::new(env!("CARGO_BIN_EXE_dl-custodian")).args(["vault-init", &i.to_string(), own.to_str().unwrap()]).output().unwrap();
    assert!(o.status.success(), "vault-init: {}", String::from_utf8_lossy(&o.stderr));
    std::fs::read_to_string(own.join("vault.name")).unwrap()
}

fn seal_chunk_tape(name: &str, path: &Path, role: &str) {
    let v = darkhand::vault::Vault::load(name).unwrap();
    let plain = std::fs::read(path).unwrap();
    v.seal_to(path, role, plain).unwrap();
}

#[test]
fn sealed_chunk_tapes_open_under_the_seats_keys() {
    let base: PathBuf = std::env::temp_dir().join(format!("dl-sealed-{}", std::process::id()));
    let (ids, cs) = prepare(&base);
    let mut names = vec![];
    for i in 0..3 {
        let own = base.join(format!("seat{i}"));
        std::fs::write(own.join(format!("ch1/chunk-P{i}.json")), b"{}").unwrap();
        let n = vault_init(&own, i);
        for c in 0..2 {
            let t = own.join(format!("ch{c}/step-0/tape_{i}.bin"));
            // the control: seat 2's step-1 tape sealed under chunk 0's role (a swapped file)
            let role = if i == 2 && c == 1 { "tape|ch0|0".to_string() } else { format!("tape|ch{c}|0") };
            seal_chunk_tape(&n, &t, &role);
            assert!(std::fs::read(&t).unwrap().starts_with(darkhand::vault::MAGIC));
        }
        names.push(n);
    }
    let (codes, errs) = launch(&base, &ids, &cs, 2, &["--vault"]);
    for i in 0..3 {
        let r: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(base.join(format!("seat{i}/D/step_0_P{i}.json"))).unwrap()).unwrap();
        assert_eq!(r["verdict"], "ACCEPT", "seat {i}: step 0 on its sealed tape");
        assert!(darkstep::serve::read_secret(&base.join(format!("seat{i}/D/ckpt_P{i}.bin"))).is_err(), "seat {i}: the checkpoint is sealed (no key in this process)");
    }
    assert_ne!(codes[2], 0, "control: seat 2's swapped tape is refused");
    assert!(errs[2].contains("seat") || errs[2].contains("open") || errs[2].contains("vault") || !errs[2].is_empty(), "{}", errs[2]);
    for n in names {
        darkhand::vault::Vault::load(&n).unwrap().destroy();
    }
    std::fs::remove_dir_all(&base).ok();
}

/// The profile check before step 0 reads a sealed tape's entry count inside its seal (serve::tape_len): a sealed
/// harness tape (no proof section) under --prove is refused naming its true count. Before the fix the check read the
/// AEAD's bytes as the header and named a garbage count (run13 on r7/r8, 12:35 UTC: "15416554168668176872 entries",
/// the failure this test would show on that build).
#[test]
fn the_profile_check_reads_a_sealed_tapes_count() {
    let base: PathBuf = std::env::temp_dir().join(format!("dl-sealed-prof-{}", std::process::id()));
    let (ids, cs) = prepare(&base);
    let mut names = vec![];
    let mut want = vec![];
    for i in 0..3 {
        let own = base.join(format!("seat{i}"));
        let t = own.join(format!("ch0/step-0/tape_{i}.bin"));
        let plain = std::fs::read(&t).unwrap();
        want.push(u64::from_le_bytes(plain[16..24].try_into().unwrap()));
        let n = vault_init(&own, i);
        seal_chunk_tape(&n, &t, "tape|ch0|0");
        assert!(std::fs::read(&t).unwrap().starts_with(darkhand::vault::MAGIC));
        names.push(n);
    }
    let (codes, errs) = launch(&base, &ids, &cs, 1, &["--prove", "--profile", "ledger-x2de", "--vault"]);
    for i in 0..3 {
        assert_eq!(codes[i], 2, "seat {i}: {}", errs[i]);
        assert!(errs[i].contains(&format!(": {} entries, but a step with profile ledger-x2de", want[i])), "seat {i}: {}", errs[i]);
    }
    assert!(want[0] > 0 && want[0] < 1 << 40);
    for n in names {
        darkhand::vault::Vault::load(&n).unwrap().destroy();
    }
    std::fs::remove_dir_all(&base).ok();
}
