//! Tulip replies across a crash and a paid house move, with real processes: three custodian
//! daemons, a Tulip broker, operator stream workers, the recovery and paid-move commands.
//! Operator A answers 101 and 102 and is SIGKILLed while answering 103, at one of three
//! points. A's disk recovers its certificates, A offers the move, B accepts, the public log
//! admits it and B adopts A's outbox. Message 104 arrives under B. The broker must end with
//! exactly one reply to each of 101, 102, 103 and 104, and a restarted A from the disk image
//! at the kill must neither learn nor post.
mod common;

use anyhow::{ensure, Result};
use common::*;
use resident_custody::custody_mesh::*;
use resident_custody::house_move::*;
use resident_custody::seat_receipt::*;
use resident_custody::tulip_bridge::{self as tulip_bridge, *};
use std::ffi::OsStr;
use std::fs;
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::process::Command as Process;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};
use std::thread::JoinHandle;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Crash {
    /// After reading 103, before staging anything for it.
    BeforeQuorum,
    /// After the custodians certified Learn(103), before A recorded the certificate.
    AfterQuorum,
    AfterCursor,
    /// After the broker committed reply 103, before A recorded its receipt.
    AfterBroker,
}

impl Crash {
    fn phase(self) -> &'static str {
        match self {
            Crash::BeforeQuorum => "read",
            Crash::AfterQuorum => "certified",
            Crash::AfterBroker => "delivered",
            Crash::AfterCursor => "cursor",
        }
    }
}

const MESSAGES: [(u64, &str, &str); 4] = [
    (101, "ada", "the river is high"),
    (102, "bo", "bring the lantern"),
    (103, "cy", "the bridge holds"),
    (104, "di", "who keeps the ledger now"),
];

struct Town {
    m: Mesh,
    broker: OwnedChild,
    socket: PathBuf,
    issuer: PathBuf,
    stop: Arc<AtomicBool>,
    server: Option<JoinHandle<Result<()>>>,
}

impl Drop for Town {
    fn drop(&mut self) {
        self.stop.store(true, Ordering::Release);
        let _ = UnixStream::connect(&self.issuer);
        if let Some(server) = self.server.take() {
            server
                .join()
                .expect("issuer thread panicked")
                .expect("issuer failed");
        }
    }
}

fn town() -> Result<Town> {
    let m = Mesh::new(3, 3)?;
    let dir = m.temp.path().join("broker");
    fs::create_dir(&dir)?;
    fs::write(dir.join("config"), bincode::serialize(&m.cfg)?)?;
    let broker = OwnedChild::spawn(
        Process::new(env!("CARGO_BIN_EXE_tulip_broker")).arg(&dir),
        dir.join("broker.pid"),
    )?;
    let socket = dir.join("socket");
    wait_for(|| UnixStream::connect(&socket).is_ok())?;
    // The policy issuer is this test, as in every custody test; it signs exact Learn grants.
    let issuer = m.temp.path().join("issuer");
    let key = m.issuer.clone();
    let listener = UnixListener::bind(&issuer)?;
    let stop = Arc::new(AtomicBool::new(false));
    let flag = stop.clone();
    let server = std::thread::spawn(move || serve_issuer(listener, key, &flag));
    Ok(Town {
        m,
        broker,
        socket,
        issuer,
        stop,
        server: Some(server),
    })
}

impl Town {
    fn run(&self, seat: &str, args: &[&OsStr]) -> Result<Vec<u8>> {
        self.m.seat_process(seat, args)?.finish()
    }
    fn stream(&self, seat: &str, barriers: bool) -> Result<OwnedChild> {
        let mut args = vec![
            OsStr::new("stream"),
            self.socket.as_os_str(),
            self.issuer.as_os_str(),
        ];
        if barriers {
            args.push(OsStr::new("--test-barriers"));
        }
        self.m.seat_process(seat, &args)
    }
    fn house_move(&self, args: &[&str]) -> Result<Vec<u8>> {
        let out = Process::new(env!("CARGO_BIN_EXE_resident_house_move"))
            .current_dir(self.m.temp.path())
            .args(args)
            .output()?;
        ensure!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        Ok(out.stdout)
    }
}

fn copy_dir(from: &Path, to: &Path) -> Result<()> {
    fs::create_dir(to)?;
    for e in fs::read_dir(from)? {
        let e = e?;
        if e.file_type()?.is_file() {
            fs::copy(e.path(), to.join(e.file_name()))?;
        }
    }
    Ok(())
}

fn fenced_everywhere(err: &str, custodians: usize) -> Result<()> {
    ensure!(
        err.matches("fenced").count() == custodians,
        "expected {custodians} fenced refusals: {err}"
    );
    Ok(())
}

fn episodes(posts: &[(Receipt, Envelope)]) -> Vec<u64> {
    posts.iter().map(|(r, _)| r.episode).collect()
}

fn scenario(crash: Crash) -> Result<()> {
    let mut t = town()?;
    let m = &t.m;
    let root = m.temp.path().to_owned();
    let tulip = BrokerClient(&t.socket);
    let genesis = m.cfg.genesis();
    for &(id, who, text) in &MESSAGES[..3] {
        tulip.publish(id, who, text)?;
    }

    // A answers 101 and 102 and is killed at the armed point of 103.
    let a_dir = root.join("A");
    let arm = a_dir.join(format!("arm-{}-103", crash.phase()));
    fs::write(&arm, [])?;
    let mut a = t.stream("A", true)?;
    wait_for(|| a_dir.join(format!("at-{}-103", crash.phase())).exists())?;
    a.kill9()?;
    fs::remove_file(&arm)?;
    // Restart the broker from its WAL. The result below must survive losing its memory.
    t.broker.kill9()?;
    let dir = t.socket.parent().unwrap();
    t.broker = OwnedChild::spawn(
        Process::new(env!("CARGO_BIN_EXE_tulip_broker")).arg(dir),
        dir.join("restarted-broker.pid"),
    )?;
    wait_for(|| UnixStream::connect(&t.socket).is_ok())?;
    // State stores its Head first. Observe each durable epoch *before* recovery can vote.
    let expected = if crash == Crash::BeforeQuorum { 2 } else { 3 };
    for i in 0..3 {
        let head: Head = bincode::deserialize_from(fs::File::open(m.dir(i).join("epoch.wal"))?)?;
        ensure!(
            head.epoch == expected && head.journal_cursor == expected,
            "custodian {i} at kill"
        );
    }
    let at_kill = episodes(&tulip.posts()?);
    ensure!(
        at_kill
            == if crash == Crash::AfterBroker {
                vec![101, 102, 103]
            } else {
                vec![101, 102]
            },
        "broker at the kill: {at_kill:?}"
    );
    // A's host exactly as the kill left it, for the zombie run at the end.
    let zombie = root.join("Z");
    copy_dir(&a_dir, &zombie)?;

    // A's disk recovers: a staged Learn is certified by exact replay, nothing is posted.
    let recovered: Recovered = bincode::deserialize(&t.run("A", &[OsStr::new("recover")])?)?;
    let learned = if crash == Crash::BeforeQuorum { 2 } else { 3 };
    ensure!(
        recovered.head.epoch == learned && recovered.certificates.len() == learned as usize,
        "recovered epoch {} with {} certificates",
        recovered.head.epoch,
        recovered.certificates.len()
    );
    ensure!(episodes(&tulip.posts()?) == at_kill, "recovery posted");

    // The public log follows A's tenure; then the paid move A -> B through the CLIs.
    let log_dir = root.join("public-log");
    let mut log = ResidentLog::create(&log_dir, m.cfg.clone(), &m.genesis)?;
    for c in &recovered.certificates {
        log.follow(c)?;
    }
    drop(log);
    let receipt =
        SeatTransferReceipt::seal(seat_transfer(&m.a, pk(&m.b), resident_seat(&genesis)), &m.a)?;
    let grant = m.grant(
        &recovered.head,
        Action::Migrate {
            successor: pk(&m.b),
            seat_payment_claim: receipt.seat_root,
        },
    );
    fs::write(root.join("grant"), bincode::serialize(&grant)?)?;
    fs::write(root.join("receipt"), receipt.to_bytes()?)?;
    fs::write(root.join("admission"), bincode::serialize(&admission())?)?;
    let offer = t.house_move(&["offer", "A", "grant", "receipt"])?;
    fs::write(root.join("offer"), offer)?;
    let bundle = t.run("A", &[OsStr::new("handoff")])?;
    let handoff: Handoff = bincode::deserialize(&bundle)?;
    ensure!(
        handoff.pending.len() == usize::from(crash != Crash::BeforeQuorum) && handoff.cursor == 2,
        "handoff: cursor {} with {} pending",
        handoff.cursor,
        handoff.pending.len()
    );
    let package = t.house_move(&["accept", "B", "admission", "offer"])?;
    fs::write(root.join("package"), &package)?;
    t.house_move(&["admit", "public-log", "admission", "package"])?;

    // A tampered reply body for 103, re-signed by A, is refused against the certified Learn.
    if let Some(honest) = handoff.pending.first() {
        let mut tampered = handoff.clone();
        tampered.pending[0]
            .envelope
            .body
            .push_str(" and the toll is doubled");
        let tampered = tampered.sign(&m.a);
        fs::write(root.join("tampered"), bincode::serialize(&tampered)?)?;
        let err = t
            .run(
                "B",
                &[
                    OsStr::new("adopt"),
                    (root.join("tampered")).as_os_str(),
                    t.socket.as_os_str(),
                ],
            )
            .unwrap_err()
            .to_string();
        ensure!(
            err.contains("reply does not match the certified Learn"),
            "{err}"
        );
        let mut body = honest.clone();
        body.envelope.body = tampered.pending[0].envelope.body.clone();
        ensure!(body.verify(&m.cfg).is_err() && honest.verify(&m.cfg).is_ok());
    }
    fs::write(root.join("handoff"), &bundle)?;
    t.run(
        "B",
        &[
            OsStr::new("adopt"),
            root.join("handoff").as_os_str(),
            t.socket.as_os_str(),
        ],
    )?;

    // A retry after a lost adopt acknowledgment is idempotent.
    t.run(
        "B",
        &[
            OsStr::new("adopt"),
            root.join("handoff").as_os_str(),
            t.socket.as_os_str(),
        ],
    )?;
    if let Some(reply) = handoff.pending.first() {
        let stale = Post::sign(reply.clone(), handoff.head.clone(), &m.a);
        ensure!(tulip
            .post(&stale)
            .unwrap_err()
            .to_string()
            .contains("fenced: stale seat"));
    }

    // 104 arrives under B. B delivers what A left and answers the rest.
    let (id, who, text) = MESSAGES[3];
    tulip.publish(id, who, text)?;
    let deliveries: Vec<Delivery> = bincode::deserialize(&t.stream("B", false)?.finish()?)?;
    let shape: Vec<(u64, bool)> = deliveries
        .iter()
        .map(|d| (d.receipt.episode, d.replayed))
        .collect();
    ensure!(
        shape == [(103, crash == Crash::AfterBroker), (104, false)],
        "B delivered {shape:?}"
    );

    // Exactly one reply to each message, each the deterministic envelope, under its key.
    let posts = tulip.posts()?;
    let frames = tulip.read(0)?;
    ensure!(
        episodes(&posts) == [101, 102, 103, 104],
        "{:?}",
        episodes(&posts)
    );
    for ((r, env), f) in posts.iter().zip(&frames) {
        ensure!(
            *env == Envelope::reply(&genesis, f)
                && r.key == idempotency_key(&genesis, f.message_id)
        );
    }

    // The public log and the custodians agree: four Learns, one per message, under B.
    let mut log = ResidentLog::open(&log_dir)?;
    for d in &deliveries {
        if d.reply.certificate.head.epoch > log.follower().head().epoch {
            log.follow(&d.reply.certificate)?;
        }
    }
    let last = &deliveries.last().unwrap().reply.certificate;
    ensure!(log.follower().head() == &last.head && last.head.operator_id == pk(&m.b));
    let (_, header) = open_header(&m.sockets[0], &m.cfg, last, &m.b)?;
    ensure!(
        header
            == JournalHeader {
                cursor: 4,
                told: 4,
                ..Default::default()
            },
        "{header:?}"
    );

    // B posting 103 again gets the original receipt. A changed body is refused against the
    // certified Learn before its key is consulted.
    let reply103 = deliveries[0].reply.clone();
    let (again, replayed) = tulip.post(&Post::sign(reply103.clone(), last.clone(), &m.b))?;
    ensure!(replayed && again == posts[2].0 && tulip.lookup(again.key)? == Some(again.clone()));
    let mut forged = reply103;
    forged.envelope.body.push_str(" and the toll is doubled");
    let err = tulip
        .post(&Post::sign(forged, last.clone(), &m.b))
        .unwrap_err()
        .to_string();
    ensure!(
        err.contains("reply does not match the certified Learn"),
        "{err}"
    );
    ensure!(
        tulip.lookup(idempotency_key(&genesis, 105))?.is_none(),
        "an unanswered key holds a receipt"
    );

    // The zombie: A restarted from its disk image at the kill. It first flushes its stale
    // outbox, which fails at all three custodians or at the broker's seat fence, then tries
    // to learn 104 over its stale head.
    let flush = t.stream("Z", false)?.finish().unwrap_err().to_string();
    match crash {
        Crash::AfterBroker | Crash::AfterCursor => {
            ensure!(flush.contains("fenced: stale seat"), "{flush}")
        }
        _ => fenced_everywhere(&flush, 3)?,
    }
    let zombie_head = match fs::read(zombie.join("cursor"))
        .map(|b| bincode::deserialize::<Option<Certificate>>(&b))??
    {
        Some(c) => c.head,
        None => m.genesis.clone(),
    };
    let frame104 = frames[3].clone();
    let learn104 = m.grant(
        &zombie_head,
        tulip_bridge::learn(&frame104, &Envelope::reply(&genesis, &frame104)),
    );
    let relearn = m
        .operator("Z", Operation::Exercise(learn104))?
        .output()
        .unwrap_err()
        .to_string();
    fenced_everywhere(&relearn, 3)?;
    for i in 0..3 {
        let log = fs::read_to_string(m.dir(i).join("obend-steps.log"))?;
        ensure!(
            log.lines().last().and_then(|l| l.split_whitespace().next()) == Some("2"),
            "custodian {i} did not record Obend StaleParent"
        );
    }
    ensure!(
        episodes(&tulip.posts()?) == [101, 102, 103, 104],
        "zombie posted"
    );
    println!(
        "{crash:?}: broker at kill {at_kill:?}; recovered epoch {}; handoff pending {}; B delivered {shape:?}; broker replies {:?}\n  zombie outbox flush: {}\n  zombie Learn(104): {}",
        recovered.head.epoch,
        handoff.pending.len(),
        episodes(&posts),
        flush.lines().next().unwrap_or(""),
        relearn.lines().next().unwrap_or("")
    );
    Ok(())
}

#[test]
fn crash_before_quorum_learn() -> Result<()> {
    scenario(Crash::BeforeQuorum)
}

#[test]
fn crash_after_quorum_before_broker() -> Result<()> {
    scenario(Crash::AfterQuorum)
}

#[test]
fn crash_after_broker_before_ack() -> Result<()> {
    scenario(Crash::AfterBroker)
}

#[test]
fn crash_after_seat_cursor_before_outbox_certificate() -> Result<()> {
    scenario(Crash::AfterCursor)
}
