use anyhow::{anyhow, ensure, Result};
use ed25519_dalek::SigningKey;
use resident_custody::{cshake_selective_open as opening, custody_mesh::*, random_seed};
use std::fs;
use std::os::unix::net::UnixStream;
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command as Process};
use std::time::{Duration, Instant};
use tempfile::TempDir;

struct OwnedChild {
    child: Child,
    pidfile: PathBuf,
}
impl OwnedChild {
    fn spawn(cmd: &mut Process, pidfile: PathBuf) -> Result<Self> {
        let child = cmd.spawn()?;
        let owner = Self { child, pidfile };
        fs::write(&owner.pidfile, owner.child.id().to_string())?;
        Ok(owner)
    }
    fn kill9(&mut self) -> Result<()> {
        ensure!(self.child.try_wait()?.is_none(), "child already exited");
        let pid = fs::read_to_string(&self.pidfile)?.parse::<u32>()?;
        ensure!(pid == self.child.id(), "pid mismatch");
        // The unreaped child handle pins this PID. Child::kill is SIGKILL on Unix.
        self.child.kill()?;
        ensure!(self.child.wait()?.signal() == Some(9), "expected SIGKILL");
        Ok(())
    }
    fn output(&mut self) -> Result<Outcome> {
        let deadline = Instant::now() + Duration::from_secs(30);
        let status = loop {
            if let Some(s) = self.child.try_wait()? {
                break s;
            }
            ensure!(Instant::now() < deadline, "operator timeout");
            std::thread::sleep(Duration::from_millis(3));
        };
        if !status.success() {
            return Err(anyhow!(fs::read_to_string(
                self.pidfile.with_extension("err")
            )?));
        }
        Ok(bincode::deserialize_from(fs::File::open(
            self.pidfile.with_extension("out"),
        )?)?)
    }
}
impl Drop for OwnedChild {
    fn drop(&mut self) {
        if matches!(self.child.try_wait(), Ok(None)) {
            let _ = self.child.kill();
        }
        let _ = self.child.wait();
        let _ = fs::remove_file(&self.pidfile);
    }
}

fn wait_for(mut ready: impl FnMut() -> bool) -> Result<()> {
    let deadline = Instant::now() + Duration::from_secs(8);
    while !ready() {
        ensure!(Instant::now() < deadline, "boundary timeout");
        std::thread::sleep(Duration::from_millis(4));
    }
    Ok(())
}

fn pk(k: &SigningKey) -> [u8; 32] {
    k.verifying_key().to_bytes()
}
fn sk() -> SigningKey {
    SigningKey::from_bytes(&random_seed().unwrap())
}

struct Mesh {
    children: Vec<Option<OwnedChild>>,
    sockets: Vec<PathBuf>,
    cfg: Config,
    genesis: Head,
    issuer: SigningKey,
    a: SigningKey,
    b: SigningKey,
    temp: TempDir,
}

impl Mesh {
    fn new(n: usize, t: u16) -> Result<Self> {
        // Short absolute paths also fit Darwin's sockaddr_un.
        let temp = tempfile::Builder::new().prefix("res-").tempdir_in("/tmp")?;
        let (issuer, a, b) = (sk(), sk(), sk());
        let keys: Vec<_> = (0..n).map(|_| sk()).collect();
        let cfg = Config {
            nonce: random_seed()?,
            first_operator: pk(&a),
            roster: keys.iter().map(pk).collect(),
            threshold: t,
            max_corrupt: 1,
            policy: Policy {
                issuer: pk(&issuer),
                output_bits: 264,
                output_rank: 128,
                slices: vec![(0, 32)],
            },
        };
        let secret = random_seed()?;
        let mut sockets = vec![];
        let mut heads = vec![];
        for (i, k) in keys.iter().enumerate() {
            let dir = temp.path().join(i.to_string());
            heads.push(provision(&dir, &cfg, i as u16, k, secret)?);
            sockets.push(dir.join("socket"));
        }
        ensure!(heads.iter().all(|h| h == &heads[0]), "genesis disagreement");
        for (name, k) in [("A", &a), ("B", &b)] {
            provision_operator(&temp.path().join(name), &cfg, &sockets, k, &heads[0])?;
        }
        let mut m = Self {
            children: (0..n).map(|_| None).collect(),
            sockets,
            cfg,
            genesis: heads.remove(0),
            issuer,
            a,
            b,
            temp,
        };
        for i in 0..n {
            m.start(i)?;
        }
        Ok(m)
    }
    fn dir(&self, i: usize) -> &Path {
        self.sockets[i].parent().unwrap()
    }
    fn start(&mut self, i: usize) -> Result<()> {
        let mut cmd = Process::new(env!("CARGO_BIN_EXE_custodian_node"));
        cmd.arg(self.dir(i)).arg("--test-barriers");
        self.children[i] = Some(OwnedChild::spawn(&mut cmd, self.dir(i).join("node.pid"))?);
        wait_for(|| UnixStream::connect(&self.sockets[i]).is_ok())
    }
    fn arm(&self, i: usize, phase: &str) -> Result<()> {
        Ok(fs::write(self.dir(i).join(format!("arm-{phase}")), [])?)
    }
    fn at(&self, i: usize, phase: &str) -> Result<()> {
        wait_for(|| self.dir(i).join(format!("at-{phase}")).exists())
    }
    fn crash(&mut self, i: usize, phase: &str) -> Result<()> {
        self.children[i].take().unwrap().kill9()?;
        fs::remove_file(self.dir(i).join(format!("arm-{phase}")))?;
        Ok(())
    }
    fn grant(&self, h: &Head, a: Action) -> Grant {
        Grant::issue(&self.issuer, h, a)
    }
    fn operator(&self, name: &str, op: Operation) -> Result<OwnedChild> {
        let dir = self.temp.path().join(name);
        // Keep each command file and PID distinct even for competing operators.
        let mut file = tempfile::NamedTempFile::new_in(self.temp.path())?;
        bincode::serialize_into(&mut file, &op)?;
        let (_, file) = file.keep()?;
        let mut cmd = Process::new(env!("CARGO_BIN_EXE_resident_operator"));
        cmd.arg(dir)
            .arg(&file)
            .stdout(fs::File::create(file.with_extension("out"))?)
            .stderr(fs::File::create(file.with_extension("err"))?);
        OwnedChild::spawn(&mut cmd, file.with_extension("pid"))
    }
    fn exercise(&self, name: &str, head: &Head, action: Action) -> Result<Certificate> {
        certified(
            self.operator(name, Operation::Exercise(self.grant(head, action)))?
                .output()?,
        )
    }
}
fn certified(result: Outcome) -> Result<Certificate> {
    match result {
        Outcome::Certified(c) => Ok(c),
        _ => Err(anyhow!("expected certificate")),
    }
}
fn infer(ranges: &[(u16, u16)]) -> Action {
    Action::Infer {
        ranges: ranges.to_owned(),
    }
}
fn learn(id: u64, coord: u8, value: u64) -> Action {
    let mut key = [0; 8];
    key[usize::from(coord)] = 1;
    Action::Learn {
        episode: id,
        step: GdnStep {
            key,
            value,
            beta: 1,
            gamma: 3,
        },
    }
}

#[test]
fn resident_house_move_and_crash_boundaries() -> Result<()> {
    let mut m = Mesh::new(3, 3)?;
    let mut bad = m.cfg.clone();
    bad.threshold = 2;
    assert!(bad
        .validate()
        .unwrap_err()
        .to_string()
        .contains("split-quorum"));
    let p1 = m.exercise("A", &m.genesis, learn(1, 0, 0xacab))?;
    let p2 = m.exercise("A", &p1.head, learn(2, 1, 0x0edc_ba98_7654_3210))?;
    assert!(m.exercise("A", &p2.head, learn(2, 1, 99)).is_err());
    let forgotten = m.exercise("A", &p2.head, Action::Forget { episode: 1 })?;
    let ranges = [(0, 16)];
    let opened = m.exercise("A", &forgotten.head, infer(&ranges))?;
    let (st, _) = release(&m.sockets[0], &m.cfg, &opened, &m.a, &ranges)?;
    let expected = [0u64.to_le_bytes(), 0x0edc_ba98_7654_3210u64.to_le_bytes()].concat();
    assert_eq!(st.projected_bytes, expected);
    assert_eq!(
        (opened.head.output_bits, opened.head.output_rank),
        (128, 128)
    );
    let seat_claim = random_seed()?;
    let handoff = m.grant(
        &opened.head,
        Action::Migrate {
            successor: pk(&m.b),
            seat_payment_claim: seat_claim,
        },
    );
    let offer = match m.operator("A", Operation::Offer(handoff))?.output()? {
        Outcome::Offered(p) => p,
        _ => return Err(anyhow!("missing offer")),
    };
    let old = m.temp.path().join("A");
    let snapshot = m.temp.path().join("snapshot");
    fs::create_dir(&snapshot)?;
    for f in ["seat", "cursor"] {
        fs::copy(old.join(f), snapshot.join(f))?;
    }

    // A is inside a live RPC at kill time. No vote for its competing request
    // can escape the first node's pre-WAL barrier.
    let pre_wal = fs::read(m.dir(0).join("epoch.wal"))?;
    m.arm(0, "pre")?;
    let mut active = m.operator(
        "A",
        Operation::Exercise(m.grant(&opened.head, learn(3, 2, 12))),
    )?;
    m.at(0, "pre")?;
    assert_ne!(fs::read(m.dir(0).join("epoch.wal.new"))?, pre_wal);
    active.kill9()?;
    m.crash(0, "pre")?;
    assert_eq!(fs::read(m.dir(0).join("epoch.wal"))?, pre_wal);
    m.start(0)?;

    // B holds the signed offer. Kill two signers before either vote arrives.
    m.arm(0, "wal")?;
    m.arm(1, "post")?;
    let mut interrupted = m.operator("B", Operation::Accept(offer.clone()))?;
    m.at(0, "wal")?;
    m.crash(0, "wal")?;
    assert_ne!(
        fs::read(m.dir(0).join("epoch.wal"))?,
        fs::read(m.dir(0).join("checkpoint"))?
    );
    m.at(1, "post")?;
    m.crash(1, "post")?;
    assert_eq!(
        fs::read(m.dir(1).join("epoch.wal"))?,
        fs::read(m.dir(1).join("checkpoint"))?
    );
    assert!(interrupted
        .output()
        .unwrap_err()
        .to_string()
        .contains("quorum refusal"));
    m.start(0)?;
    m.start(1)?;
    assert_eq!(
        fs::read(m.dir(0).join("epoch.wal"))?,
        fs::read(m.dir(0).join("checkpoint"))?
    );
    let moved = certified(
        m.operator("B", Operation::Accept(offer.clone()))?
            .output()?,
    )?;
    moved.verify(&m.cfg)?;
    let recovered = certified(
        m.operator("B", Operation::Accept(offer.clone()))?
            .output()?,
    )?;
    assert_eq!(bincode::serialize(&moved)?, bincode::serialize(&recovered)?);
    assert_eq!(
        (moved.head.operator_id, moved.head.seat_payment_claim),
        (pk(&m.b), seat_claim)
    );
    assert_eq!(
        (moved.head.epoch, moved.head.journal_cursor),
        (opened.head.epoch + 1, 3)
    );
    assert_eq!(moved.head.state_commitment, opened.head.state_commitment);

    // Restore the actual old files into a newly started operator's directory.
    fs::rename(&old, m.temp.path().join("dead-host"))?;
    fs::rename(snapshot, &old)?;
    let mut stale = m.operator(
        "A",
        Operation::Exercise(m.grant(&opened.head, learn(3, 2, 12))),
    )?;
    let mut live = m.operator(
        "B",
        Operation::Exercise(m.grant(&moved.head, infer(&ranges))),
    )?;
    assert!(stale.output().unwrap_err().to_string().contains("fenced"));
    let continued = certified(live.output()?)?;
    let (st, _) = release(&m.sockets[2], &m.cfg, &continued, &m.b, &ranges)?;
    assert_eq!(st.projected_bytes, expected);
    assert_eq!(
        (continued.head.output_bits, continued.head.output_rank),
        (256, 128)
    );
    assert!(release(&m.sockets[2], &m.cfg, &continued, &m.a, &ranges).is_err());
    assert!(release(&m.sockets[1], &m.cfg, &opened, &m.a, &ranges).is_err());
    assert!(m
        .exercise("A", &opened.head, infer(&ranges))
        .unwrap_err()
        .to_string()
        .contains("fenced"));
    let c = sk();
    provision_operator(&m.temp.path().join("C"), &m.cfg, &m.sockets, &c, &m.genesis)?;
    let stale_grant = m.grant(
        &opened.head,
        Action::Migrate {
            successor: pk(&c),
            seat_payment_claim: random_seed()?,
        },
    );
    let stale_offer = match m.operator("A", Operation::Offer(stale_grant))?.output()? {
        Outcome::Offered(p) => p,
        _ => return Err(anyhow!("missing restored seat's signed offer")),
    };
    let refusal = m
        .operator("C", Operation::Accept(stale_offer))?
        .output()
        .unwrap_err()
        .to_string();
    assert_eq!(refusal.matches("fenced").count(), m.sockets.len());
    // A knows the live manifest and has an exact issuer grant but lacks B's key.
    let forged = Proposal {
        command: Command::authorize(m.grant(&continued.head, learn(3, 2, 17)), &m.a, None),
        parent_certificate: Some(continued.clone()),
    };
    assert!(certify(&m.cfg, &m.sockets, &forged).is_err());
    assert!(m
        .exercise("B", &continued.head, infer(&[(16, 17)]))
        .unwrap_err()
        .to_string()
        .contains("exposure cap")); // rank only
    assert!(m
        .exercise("B", &continued.head, infer(&ranges))
        .unwrap_err()
        .to_string()
        .contains("exposure cap")); // bits only
    let mut changed_manifest = moved.clone();
    changed_manifest.head.seat_payment_claim[3] ^= 1;
    assert!(changed_manifest.verify(&m.cfg).is_err());
    let learned = m.exercise("B", &continued.head, learn(3, 2, 17))?;
    assert_eq!(learned.head.journal_cursor, 4);
    println!("mesh n=3 t=3 f=1: SIGKILL A mid-RPC, node0 pre-WAL, node0 post-WAL, node1 post-checkpoint; B recovered epoch {}, old Learn/Infer/Migrate refused, post-move bits/rank=256/128, B Learn certified epoch {}",moved.head.epoch,learned.head.epoch);
    Ok(())
}

#[test]
fn quorum_failover_and_grant_binding() -> Result<()> {
    let mut m = Mesh::new(4, 3)?;
    m.children[3].take().unwrap().kill9()?;
    let g = m.grant(&m.genesis, learn(1, 0, 5));
    let proposal = |grant| Proposal {
        command: Command::authorize(grant, &m.a, None),
        parent_certificate: None,
    };
    let mut wrong = g.clone();
    wrong.action = Action::Forget { episode: 1 };
    assert!(certify(&m.cfg, &m.sockets, &proposal(wrong)).is_err());
    let valid = proposal(g);
    let cert = certify(&m.cfg, &m.sockets, &valid)?;
    assert_eq!(cert.votes.len(), 3);
    let mut repeated = cert.clone();
    repeated.votes[1] = repeated.votes[0].clone();
    assert!(repeated.verify(&m.cfg).is_err());
    m.start(3)?;
    let all = certify(&m.cfg, &m.sockets, &valid)?;
    assert_eq!(all.votes.len(), 4);
    assert_eq!(all.head, cert.head);
    let step = |action: Action, prev: &Certificate| Proposal {
        command: Command::authorize(m.grant(&prev.head, action), &m.a, None),
        parent_certificate: Some(prev.clone()),
    };
    let overlapping = certify(&m.cfg, &m.sockets, &step(learn(2, 0, 19), &all))?;
    let forget_first = certify(
        &m.cfg,
        &m.sockets,
        &step(Action::Forget { episode: 1 }, &overlapping),
    );
    assert!(forget_first
        .unwrap_err()
        .to_string()
        .contains("nonorthogonal"));
    let forget_second = certify(
        &m.cfg,
        &m.sockets,
        &step(Action::Forget { episode: 2 }, &overlapping),
    )?;
    let observed = certify(&m.cfg, &m.sockets, &step(infer(&[(0, 8)]), &forget_second))?;
    let (st, _) = release(&m.sockets[3], &m.cfg, &observed, &m.a, &[(0, 8)])?;
    assert_eq!(st.projected_bytes, 15u64.to_le_bytes()); // tombstone retains gamma=3
    certify(
        &m.cfg,
        &m.sockets,
        &step(Action::Forget { episode: 1 }, &observed),
    )?;
    println!("mesh n=4 t=3 f=1: three signed with one SIGKILLed, fourth caught up by exact replay");
    Ok(())
}

#[test]
fn selective_open_benchmark_and_falsifiers() -> Result<()> {
    let blind = random_seed()?;
    let cell = [random_seed()?, random_seed()?].concat();
    let ranges = vec![(0, 4), (32, 36)];
    let st = opening::statement(&blind, &cell, ranges.clone())?;
    let mut sizes = vec![];
    let mut prove_ms = vec![];
    let mut verify_ms = vec![];
    let mut proof = vec![];
    for _ in 0..9 {
        let t = Instant::now();
        proof = opening::prove(&blind, &cell, &st)?;
        prove_ms.push(t.elapsed().as_secs_f64() * 1000.);
        let t = Instant::now();
        opening::verify(64, &ranges, &st, &proof)?;
        verify_ms.push(t.elapsed().as_secs_f64() * 1000.);
        sizes.push(proof.len());
    }
    sizes.sort();
    prove_ms.sort_by(f64::total_cmp);
    verify_ms.sort_by(f64::total_cmp);
    let rejected =
        |st: &opening::Statement, p: &[u8]| opening::verify(64, &st.ranges, st, p).is_err();
    let mut wrong = st.clone();
    wrong.cell_root[0] ^= 1;
    assert!(rejected(&wrong, &proof));
    let mut wrong = st.clone();
    wrong.projected_bytes[0] ^= 1;
    assert!(rejected(&wrong, &proof));
    let mut wrong = st.clone();
    wrong.ranges[0] = (1, 5);
    assert!(rejected(&wrong, &proof));
    let round_len = 96 + 32 + 4800;
    let correction = proof.len() - opening::REPETITIONS * round_len;
    for off in [0, 32, correction, correction + 96, correction + 128] {
        let mut changed = proof.clone();
        changed[off] ^= 1;
        assert!(rejected(&st, &changed));
    }
    assert!(rejected(&st, &proof[..proof.len() - 1]));
    let mut trailing = proof.clone();
    trailing.push(0);
    assert!(rejected(&st, &trailing));
    assert!(opening::verify(64, &[(1, 5), (32, 36)], &st, &proof).is_err());
    let mut hidden = cell;
    hidden[16] ^= 1;
    assert!(opening::prove(&blind, &hidden, &st).is_err());
    println!("cSHAKE256 width=64 projected=8 repetitions={} n=9 min/median/max bytes={}/{}/{} prove_ms={:.3}/{:.3}/{:.3} verify_ms={:.3}/{:.3}/{:.3} wire/statement_falsifiers=10/10 refused",
        opening::REPETITIONS,sizes[0],sizes[4],sizes[8],prove_ms[0],prove_ms[4],prove_ms[8],verify_ms[0],verify_ms[4],verify_ms[8]);
    Ok(())
}

#[test]
fn same_projection_privacy_observations() -> Result<()> {
    let mut hits = 0;
    let mut seen = std::collections::BTreeSet::new();
    let canaries = [random_seed()?, random_seed()?];
    for i in 0..32 {
        let class = i % 2;
        let cell = [[0x2a; 32], canaries[class]].concat();
        let blind = random_seed()?;
        let st = opening::statement(&blind, &cell, vec![(0, 4)])?;
        assert_eq!(st.projected_bytes, [0x2a; 4]);
        let proof = opening::prove(&blind, &cell, &st)?;
        opening::verify(64, &st.ranges, &st, &proof)?;
        assert!(seen.insert(proof[..32].to_vec()));
        for needle in [&canaries[class], &blind] {
            assert!(!proof.windows(32).any(|w| w == needle));
        }
        hits += usize::from(usize::from(proof[0] & 1) == class);
    }
    println!("privacy observations: 32 accepted fresh blinds/proofs, 0/64 whole private strings found, preselected digest-low-bit classifier {hits}/32");
    Ok(())
}

#[test]
fn keccak_padding_and_deployed_outer_hash() -> Result<()> {
    for width in [103, 104, 105, 240] {
        // private prefix + cell = 135,136,137,272
        let cell = vec![0x53; width];
        let blind = random_seed()?;
        let st = opening::statement(&blind, &cell, vec![(0, 1)])?;
        let proof = opening::prove(&blind, &cell, &st)?;
        opening::verify(width, &st.ranges, &st, &proof)?;
    }
    // Independent Go standard-library vector in research/wave12_resident_custody.
    let layout = [
        0x6b, 0x78, 0x52, 0xd6, 0x71, 0x18, 0xb7, 0xc5, 0x13, 0x46, 0xd5, 0xee, 0x0e, 0x6e, 0x0e,
        0x2a, 0x10, 0xef, 0x31, 0x6e, 0x4a, 0x75, 0x01, 0x09, 0x8d, 0xc7, 0x34, 0x26, 0x83, 0x90,
        0x0b, 0xdc,
    ];
    let c = opening::Circuit::private_cell_outer(&layout, b"seat", 300)?;
    let blind = std::array::from_fn(|i| i as u8);
    let inner: [u8; 32] = std::array::from_fn(|i| 32 + i as u8);
    assert_eq!(
        c.root(&blind, &inner),
        [
            0x22, 0x8b, 0x05, 0x97, 0x5e, 0x7f, 0xa9, 0xd7, 0xfe, 0x29, 0x4c, 0xb0, 0x39, 0x03,
            0xb2, 0xe7, 0xc7, 0x06, 0x9c, 0x6d, 0x3f, 0xf2, 0xd3, 0xc3, 0x06, 0xd5, 0x75, 0xe1,
            0xd6, 0x4c, 0x42, 0xa7
        ]
    );
    let st = opening::Statement {
        cell_root: c.root(&blind, &inner),
        ranges: vec![(3, 6)],
        projected_bytes: inner[3..6].to_vec(),
    };
    let proof = c.prove(&blind, &inner, &st)?;
    c.verify(&st.ranges, &st, &proof)?;
    assert!(opening::Circuit::private_cell_outer(&layout, b"seat", 301)?
        .verify(&st.ranges, &st, &proof)
        .is_err());
    assert!(opening::verify(32, &st.ranges, &st, &proof).is_err());
    Ok(())
}
