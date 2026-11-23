//! A resident moves from operator A to operator B across three live custodian daemons:
//! a DreggNet v1 seat receipt, an Obend-latched quorum succession, the journal header proved
//! by a cSHAKE256 opening, admission into a public log's own latch, and A's restored
//! snapshot fenced. Then twelve cross-layer attacks, each with the refusal it must meet.
//!
//! Set `OBEND_BELTLATCH_EXE` to a `cake --pancake` build of Obend's `beltLatch` and every
//! custodian runs each latch step natively as well, failing closed on any difference.
mod common;

use anyhow::{anyhow, bail, ensure, Result};
use common::*;
use ed25519_dalek::{Signer, SigningKey};
use resident_custody::custody_mesh::*;
use resident_custody::house_move::*;
use resident_custody::obend_latch_abi::{self as obend, StateWords, Status};
use resident_custody::random_seed;
use resident_custody::seat_receipt::*;
use sha2::{Digest as _, Sha256};
use std::fs;
use std::path::PathBuf;
use std::process::Command as Process;
use std::time::Instant;

const ASSET: Bytes32 = [0xcd; 32];
const CAP: u64 = 10_000;
const PRIME: u128 = (1 << 61) - 1;

fn claim(seat: Bytes32, pi: &str, event: &str, amount: u64) -> PaymentClaim {
    PaymentClaim {
        event_id: event.into(),
        event_type: "payment_intent.succeeded".into(),
        payment_intent_id: pi.into(),
        customer_seat: seat,
        amount_minor: amount,
        currency: "usd".into(),
        payload_sha256: sha256(event.as_bytes()),
        stripe_timestamp: 1_763_900_000,
        stripe_v1: sha256(pi.as_bytes()),
        mint_idempotency_key: payment_nullifier(&ASSET, pi),
    }
}

/// The resident's paid seat: one provisional and one settled payment.
fn seat_transfer(source: &SigningKey, target: Bytes32, seat: Bytes32) -> SeatTransfer {
    let credit = |c: PaymentClaim, remaining_minor, backing| TransferredCredit {
        mint: MintReceipt::new(&c, MintReceipt::expected_effect(&c)).unwrap(),
        claim: c,
        remaining_minor,
        backing,
    };
    SeatTransfer {
        source_operator_id: pk(source),
        target_operator_id: target,
        transfer_epoch: 1,
        asset: ASSET,
        customer_seat: seat,
        credits: vec![
            credit(
                claim(seat, "pi_tulip_1", "evt_1", 2_500),
                1_800,
                CreditBacking::Provisional,
            ),
            credit(
                claim(seat, "pi_tulip_2", "evt_2", 4_000),
                4_000,
                CreditBacking::Settled {
                    deposit_sha256: sha256(b"bank-deposit-2"),
                },
            ),
        ],
        unsettled_provisional_minor: 2_500,
        reversal_deficit_minor: 0,
        operator_reserve_cap_minor: CAP,
    }
}

fn admission() -> SeatAdmission {
    SeatAdmission {
        asset: ASSET,
        currency: "usd".into(),
        epoch_floor: 0,
        max_reserve_cap_minor: CAP,
    }
}

/// A receipt sealed over transfer JSON the caller edited, so its signature is valid for
/// exactly those bytes. With no edit this is byte-identical to `SeatTransferReceipt::seal`.
fn seal_json(transfer_json: &str, key: &SigningKey) -> Result<(Vec<u8>, Bytes32)> {
    let mut h = Sha256::new();
    h.update(b"dreggnet-seat-handoff-v1\0");
    h.update(transfer_json.as_bytes());
    let root: Bytes32 = h.finalize().into();
    let receipt = format!(
        "{{\"transfer\":{transfer_json},\"seat_root\":{},\"signature\":\"{}\"}}",
        serde_json::to_string(&root)?,
        hex::encode(key.sign(&root).to_bytes())
    );
    Ok((receipt.into_bytes(), root))
}

/// Every custodian key signs `head`'s Obend record: what an equivocating quorum certifies.
fn forge(m: &Mesh, head: Head) -> Result<Certificate> {
    let votes = m
        .keys
        .iter()
        .enumerate()
        .map(|(i, k)| Vote::sign(k, i as u16, &head))
        .collect::<Result<_>>()?;
    Ok(Certificate { head, votes })
}

/// The Migrate successor of `parent` exactly as `State::advance` builds it, forged.
fn forge_move(
    m: &Mesh,
    parent: &Certificate,
    successor: &SigningKey,
    seat_payment_claim: Bytes32,
) -> Result<(Command, Certificate)> {
    let grant = m.grant(
        &parent.head,
        Action::Migrate {
            successor: pk(successor),
            seat_payment_claim,
        },
    );
    let command = Command::authorize(grant, &m.a, Some(successor));
    let mut head = parent.head.clone();
    head.operator_id = pk(successor);
    head.seat_payment_claim = seat_payment_claim;
    head.change = command.id();
    head.parent_commitment = head_root(&parent.head);
    head.epoch += 1;
    Ok((command, forge(m, head)?))
}

fn fenced_everywhere(err: anyhow::Error, custodians: usize) -> Result<()> {
    let text = err.to_string();
    ensure!(
        text.matches("fenced").count() == custodians,
        "expected {custodians} fenced refusals: {text}"
    );
    Ok(())
}

/// Operator A's tenure, ending at a certified Infer head.
struct Tenure {
    m: Mesh,
    log_dir: PathBuf,
    /// Journal header opened at cursor 3, before the Forget.
    early_header: HeaderOpening,
    opened: Certificate,
    w0_view: Vec<u8>,
    certs: Vec<Certificate>,
}

fn tenure() -> Result<Tenure> {
    let m = Mesh::new(3, 3)?;
    let log_dir = m.temp.path().join("public-log");
    let mut log = ResidentLog::create(&log_dir, m.cfg.clone(), &m.genesis)?;
    let mut certs: Vec<Certificate> = vec![];
    let mut head = m.genesis.clone();
    // Tulip message ids are episode ids.
    for action in [
        learn_as(101, Provenance::Experienced, 0, 0xacab),
        learn_as(102, Provenance::Told, 1, 0x0edc_ba98_7654_3210),
        learn_as(103, Provenance::Inferred, 2, 7),
    ] {
        let c = m.exercise("A", &head, action)?;
        log.follow(&c)?;
        head = c.head.clone();
        certs.push(c);
    }
    let (early_header, h) = open_header(&m.sockets[1], &m.cfg, certs.last().unwrap(), &m.a)?;
    assert_eq!(
        h,
        JournalHeader {
            cursor: 3,
            experienced: 1,
            told: 1,
            inferred: 1,
            forgotten: 0
        }
    );
    let forgot = m.exercise("A", &head, Action::Forget { episode: 101 })?;
    log.follow(&forgot)?;
    let opened = m.exercise("A", &forgot.head, infer(&[(0, 16)]))?;
    log.follow(&opened)?;
    let (st, _) = release(&m.sockets[0], &m.cfg, &opened, &m.a, &[(0, 16)])?;
    // Forgetting 101 removed its whole decayed contribution; 102 decayed once, by 103.
    let w1 = (3 * u128::from(0x0edc_ba98_7654_3210u64) % PRIME) as u64;
    assert_eq!(
        st.projected_bytes,
        [0u64.to_le_bytes(), w1.to_le_bytes()].concat()
    );
    certs.extend([forgot, opened.clone()]);
    Ok(Tenure {
        m,
        log_dir,
        early_header,
        opened,
        w0_view: st.projected_bytes,
        certs,
    })
}

struct Moved {
    pkg: ResidentMigrationPackage,
    wire: Vec<u8>,
    /// The public log's latch and head before admission.
    parent_log: (StateWords, Head),
    phases: Vec<(&'static str, f64)>,
}

/// The timed move: from A sealing the seat to the public log's durable admission and A's
/// restored snapshot refused by every custodian.
fn house_move(t: &mut Tenure) -> Result<Moved> {
    let m = &t.m;
    let seat = resident_seat(&m.cfg.genesis());
    let root = m.temp.path();
    let a_dir = root.join("A");
    let snapshot = m.temp.path().join("A-snapshot");
    fs::create_dir(&snapshot)?;
    for f in ["seat", "cursor"] {
        fs::copy(a_dir.join(f), snapshot.join(f))?;
    }
    let prior = ResidentLog::open(&t.log_dir)?;
    let parent_log = (*prior.follower().latch(), prior.follower().head().clone());
    drop(prior);
    fs::write(root.join("admission"), bincode::serialize(&admission())?)?;
    let cli = |args: &[&str]| -> Result<Vec<u8>> {
        let out = Process::new(env!("CARGO_BIN_EXE_resident_house_move"))
            .current_dir(root)
            .args(args)
            .output()?;
        ensure!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        Ok(out.stdout)
    };
    let mut phases = vec![];
    let start = Instant::now();
    let mut last = start;
    let mut mark = |name| {
        let now = Instant::now();
        phases.push((name, (now - last).as_secs_f64() * 1e3));
        last = now;
    };

    // A seals the paid seat for B; the issuer grants exactly that Migrate; A offers it.
    let receipt = SeatTransferReceipt::seal(seat_transfer(&m.a, pk(&m.b), seat), &m.a)?;
    let receipt_bytes = receipt.to_bytes()?;
    let grant = m.grant(
        &t.opened.head,
        Action::Migrate {
            successor: pk(&m.b),
            seat_payment_claim: receipt.seat_root,
        },
    );
    fs::write(root.join("grant"), bincode::serialize(&grant)?)?;
    fs::write(root.join("receipt"), receipt_bytes)?;
    let offer = cli(&["offer", "A", "grant", "receipt"])?;
    fs::write(root.join("offer"), offer)?;
    mark("A seals seat receipt, offers Migrate");

    let wire = cli(&["accept", "B", "admission", "offer"])?;
    fs::write(root.join("package"), &wire)?;
    mark("B checks seat, certifies succession and verifies header");

    cli(&["admit", "public-log", "admission", "package"])?;
    mark("public log admits package");

    // A's host is restored from its pre-move snapshot and tries to keep living.
    fs::rename(&a_dir, m.temp.path().join("A-dead-host"))?;
    fs::rename(&snapshot, &a_dir)?;
    let stale = m.grant(&t.opened.head, learn_as(104, Provenance::Experienced, 3, 9));
    fenced_everywhere(
        m.operator("A", Operation::Exercise(stale))?
            .output()
            .unwrap_err(),
        m.sockets.len(),
    )?;
    mark("restored A Learn fenced (3 daemons)");
    phases.push(("total", start.elapsed().as_secs_f64() * 1e3));
    Ok(Moved {
        pkg: ResidentMigrationPackage::from_bytes(&wire)?,
        wire,
        parent_log,
        phases,
    })
}

fn print_phases(phases: &[(&str, f64)]) {
    for (name, ms) in phases {
        println!("  {ms:9.3} ms  {name}");
    }
}

fn refusal(r: Result<Admitted, Refusal>) -> Refusal {
    match r {
        Ok(a) => panic!("admitted epoch {}", a.head.epoch),
        Err(r) => r,
    }
}

#[test]
fn full_resident_house_move() -> Result<()> {
    let native = std::env::var_os(obend::NATIVE_ENV).is_some();
    let mut t = tenure()?;
    let moved = house_move(&mut t)?;
    println!(
        "house move A -> B, 3 custodian daemons, Obend native differential {}",
        if native { "on" } else { "off" }
    );
    print_phases(&moved.phases);
    let pkg = &moved.pkg;
    let mut public_log = ResidentLog::open(&t.log_dir)?;
    let new_head = public_log.follower().head().clone();
    assert_eq!(new_head, pkg.succession.head);
    assert_eq!(
        pkg.header.journal,
        JournalHeader {
            cursor: 4,
            experienced: 1,
            told: 1,
            inferred: 1,
            forgotten: 1
        }
    );
    assert_eq!(new_head.operator_id, pk(&t.m.b));
    assert_eq!(
        serde_json::from_slice::<SeatTransferReceipt>(&pkg.seat_receipt)?.seat_root,
        new_head.seat_payment_claim
    );
    assert_eq!(*public_log.follower().latch(), latch_state(&new_head));
    assert_eq!(
        bincode::serialized_size(&pkg.header)?,
        96 + pkg.header.proof.len() as u64
    );
    assert!(bincode::serialized_size(&pkg.header)? <= 91_000);
    println!(
        "package {} bytes: header proof {} bytes, seat receipt {} bytes",
        moved.wire.len(),
        pkg.header.proof.len(),
        pkg.seat_receipt.len()
    );
    // W0 continuity: B's first release is A's last one, byte for byte, with the forgotten
    // coordinate still zero, and the exposure ledger carried rather than reset.
    let b_dir = t.m.temp.path().join("B");
    let infer_b = certified(operate(
        &b_dir,
        Operation::Exercise(t.m.grant(&new_head, infer(&[(0, 16)]))),
    )?)?;
    public_log.follow(&infer_b)?;
    let (st, _) = release(&t.m.sockets[1], &t.m.cfg, &infer_b, &t.m.b, &[(0, 16)])?;
    assert_eq!(st.projected_bytes, t.w0_view);
    assert_eq!(
        (infer_b.head.output_bits, infer_b.head.output_rank),
        (256, 128)
    );

    let honest_root = serde_json::from_slice::<SeatTransferReceipt>(&pkg.seat_receipt)?.seat_root;
    let seat = resident_seat(&t.m.cfg.genesis());
    let c = sk();
    let mut table = std::collections::BTreeMap::<u8, (&str, String)>::new();

    // Package-level attacks against a replica of the public log at the parent head.
    {
        let m = &t.m;
        // The forging helper reproduces the honest move bit for bit, so each forged package
        // below differs from the honest one only where its attack says.
        let (cmd, cert) = forge_move(m, &t.opened, &m.b, honest_root)?;
        assert_eq!(
            bincode::serialize(&cert)?,
            bincode::serialize(&pkg.succession)?
        );
        assert_eq!(bincode::serialize(&cmd)?, bincode::serialize(&pkg.command)?);
        let honest_json =
            String::from_utf8(serde_json::to_vec(&seat_transfer(&m.a, pk(&m.b), seat))?)?;
        assert_eq!(seal_json(&honest_json, &m.a)?.0, pkg.seat_receipt);

        let replica = || {
            let (latch, head) = moved.parent_log.clone();
            Follower::recover(m.cfg.clone(), latch, head).unwrap()
        };
        let admit = |p: &ResidentMigrationPackage| replica().admit(&admission(), p, |_, _| Ok(()));
        assert_eq!(admit(pkg).map_err(|r| anyhow!("{r}"))?.head, new_head);
        let with = |f: &dyn Fn(&mut ResidentMigrationPackage) -> Result<()>| -> Result<ResidentMigrationPackage> {
            let mut p = pkg.clone();
            f(&mut p)?;
            Ok(p)
        };
        // The receipt, and a forged Migrate that certifies exactly its seat root.
        let rebound = |receipt: Vec<u8>, root: Bytes32| {
            with(&|p| {
                let (command, succession) = forge_move(m, &t.opened, &m.b, root)?;
                p.seat_receipt = receipt.clone();
                p.command = command;
                p.succession = succession;
                Ok(())
            })
        };

        // 1. A disputed payment cannot be carried: DreggNet's decoder has no such backing.
        let (receipt, root) = seal_json(
            &honest_json.replacen("\"Provisional\"", "\"Disputed\"", 1),
            &m.a,
        )?;
        let r = refusal(admit(&rebound(receipt, root)?));
        assert!(
            matches!(r, Refusal::Seat(TransferError::Malformed(_))),
            "{r}"
        );
        table.insert(1, ("disputed seat receipt", r.to_string()));

        // 2. Exposure above the reserve cap.
        let mut over = seat_transfer(&m.a, pk(&m.b), seat);
        over.reversal_deficit_minor = CAP;
        let sealed = SeatTransferReceipt::seal(over, &m.a)?;
        let r = refusal(admit(&rebound(sealed.to_bytes()?, sealed.seat_root)?));
        assert!(
            matches!(r, Refusal::Seat(TransferError::UnbackedReserve)),
            "{r}"
        );
        table.insert(2, ("over-cap seat receipt", r.to_string()));

        // 3. The paid seat names an operator other than the custody successor.
        let sealed = SeatTransferReceipt::seal(seat_transfer(&m.a, pk(&c), seat), &m.a)?;
        let r = refusal(admit(&rebound(sealed.to_bytes()?, sealed.seat_root)?));
        assert!(
            matches!(r, Refusal::Seat(TransferError::WrongOperator)),
            "{r}"
        );
        table.insert(3, ("wrong target_operator", r.to_string()));

        // 4. An equivocating quorum certifies a sibling of the logged parent and moves from it.
        let mut sibling = t.opened.head.clone();
        sibling.change = random_seed()?;
        let sibling = forge(m, sibling)?;
        let (command, succession) = forge_move(m, &sibling, &m.b, honest_root)?;
        let forked = with(&|p| {
            p.parent = sibling.clone();
            p.command = command.clone();
            p.succession = succession.clone();
            Ok(())
        })?;
        let r = refusal(admit(&forked));
        assert!(matches!(r, Refusal::Latch(Status::ParentFork)), "{r}");
        table.insert(4, ("BeltLatch parent-digest fork", r.to_string()));

        // 5. The successor head claims another policy under the same genesis.
        let drifted = with(&|p| {
            let mut head = p.succession.head.clone();
            head.policy_hash = random_seed()?;
            p.succession = forge(m, head)?;
            Ok(())
        })?;
        let r = refusal(admit(&drifted));
        assert!(matches!(r, Refusal::Latch(Status::PolicyDrift)), "{r}");
        table.insert(5, ("policy-digest drift", r.to_string()));

        // 7. One byte of the opened header (the cursor) is edited.
        let tampered = with(&|p| {
            p.header.journal.cursor ^= 1;
            Ok(())
        })?;
        let r = refusal(admit(&tampered));
        assert!(
            matches!(&r, Refusal::Opening(e) if e == "cut-and-choose transcript"),
            "{r}"
        );
        table.insert(7, ("tampered cSHAKE256 projection", r.to_string()));

        // 8. A genuine header from an earlier world root (cursor 3) replayed into the package.
        let replayed = with(&|p| {
            p.header = t.early_header.clone();
            Ok(())
        })?;
        let r = refusal(admit(&replayed));
        assert!(
            matches!(&r, Refusal::Opening(e) if e == "world membership"),
            "{r}"
        );
        table.insert(8, ("replayed Tulip journal cursor", r.to_string()));

        // 12. A valid A -> B receipt for another resident's seat, shipped with the honest
        // move; and rebound into a forged move, where the seat itself is wrong.
        let other = SeatTransferReceipt::seal(
            seat_transfer(&m.a, pk(&m.b), resident_seat(&random_seed()?)),
            &m.a,
        )?;
        let transplant = with(&|p| {
            p.seat_receipt = other.to_bytes()?;
            Ok(())
        })?;
        let r = refusal(admit(&transplant));
        assert!(
            matches!(
                r,
                Refusal::SeatBinding("receipt seat root is not the certified seat claim")
            ),
            "{r}"
        );
        let r2 = refusal(admit(&rebound(other.to_bytes()?, other.seat_root)?));
        assert!(
            matches!(
                r2,
                Refusal::SeatBinding("seat does not belong to this resident")
            ),
            "{r2}"
        );
        table.insert(
            12,
            ("seat receipt transplant", format!("{r}; rebound: {r2}")),
        );
    }

    // 6. Missing persistAck, both sides. A custodian whose WAL write fails steps Obend with
    // persistAck = 0, gets MissingAck, casts no vote and exits; nothing reached its WAL.
    fs::write(t.m.dir(0).join("fail-wal"), [])?;
    let wal = fs::read(t.m.dir(0).join("epoch.wal"))?;
    let learn104 =
        t.m.grant(&infer_b.head, learn_as(104, Provenance::Experienced, 3, 9));
    let err = operate(&b_dir, Operation::Exercise(learn104.clone())).unwrap_err();
    assert!(err.to_string().contains("quorum refusal"), "{err}");
    let steps = fs::read_to_string(t.m.dir(0).join("obend-steps.log"))?;
    assert!(steps.lines().last().unwrap().starts_with("6 0 "), "{steps}");
    assert_eq!(fs::read(t.m.dir(0).join("epoch.wal"))?, wal);
    fs::remove_file(t.m.dir(0).join("fail-wal"))?;
    let mut node0 = t.m.children[0].take().unwrap();
    let mut exited = None;
    for _ in 0..400 {
        exited = node0.try_status()?;
        if exited.is_some() {
            break;
        }
        std::thread::sleep(std::time::Duration::from_millis(5));
    }
    assert!(!exited
        .expect("custodian 0 exited after its failed persist")
        .success());
    drop(node0);
    t.m.start(0)?;
    // The same signed Learn completes: custodian 0 binds it fresh, 1 and 2 replay.
    let learned104 = certified(operate(&b_dir, Operation::Exercise(learn104))?)?;

    let m = &t.m;
    // A failed publication exposes no new epoch. The next process can admit the same package.
    let log_dir = m.temp.path().join("cli-log");
    let cli = |args: &[&std::ffi::OsStr]| {
        Process::new(env!("CARGO_BIN_EXE_resident_house_move"))
            .args(args)
            .output()
    };
    let file = |name: &str, bytes: Vec<u8>| -> Result<PathBuf> {
        let p = m.temp.path().join(name);
        fs::write(&p, bytes)?;
        Ok(p)
    };
    let cfg_file = file("cfg.bin", bincode::serialize(&m.cfg)?)?;
    let genesis_file = file("genesis.bin", bincode::serialize(&m.genesis)?)?;
    let out = cli(&[
        "init".as_ref(),
        log_dir.as_os_str(),
        cfg_file.as_os_str(),
        genesis_file.as_os_str(),
    ])?;
    ensure!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    for (i, cert) in t.certs.iter().enumerate() {
        let f = file(&format!("cert{i}.bin"), bincode::serialize(cert)?)?;
        let out = cli(&["follow".as_ref(), log_dir.as_os_str(), f.as_os_str()])?;
        ensure!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
    }
    let adm_file = file("admission.bin", bincode::serialize(&admission())?)?;
    let pkg_file = file("package.bin", moved.wire.clone())?;
    let admit_args = [
        "admit".as_ref(),
        log_dir.as_os_str(),
        adm_file.as_os_str(),
        pkg_file.as_os_str(),
    ];
    let epoch_file = log_dir.join(format!("epoch-{:016x}", new_head.epoch));
    let before = fs::read_dir(&log_dir)?.count();
    {
        // A directory at the temporary filename forces a write failure even as root.
        let pending = log_dir.join("pending");
        fs::create_dir(&pending)?;
        let out = cli(&admit_args)?;
        let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
        assert_eq!(out.status.code(), Some(2), "{stderr}");
        assert!(stderr.contains("MissingAck (code 6)"), "{stderr}");
        assert!(!epoch_file.try_exists()?);
        assert_eq!(
            ResidentLog::open(&log_dir)?.follower().head(),
            &t.opened.head
        );
        fs::remove_dir(pending)?;
        table.insert(
            6,
            (
                "missing persist_ack",
                format!(
                    "custodian 0 logged Obend MissingAck with persistAck 0, cast no vote: quorum refusal; public log process: exit 2, {}",
                    stderr.trim()
                ),
            ),
        );
    }
    let out = cli(&admit_args)?;
    ensure!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(fs::read_dir(&log_dir)?.count(), before + 1);
    let saved: (StateWords, Head, Vec<u8>) = bincode::deserialize(&fs::read(epoch_file)?)?;
    assert_eq!(
        saved,
        (latch_state(&new_head), new_head.clone(), moved.wire.clone())
    );
    assert_eq!(ResidentLog::open(&log_dir)?.follower().head(), &new_head);
    let line = String::from_utf8(out.stdout)?;
    assert!(
        line.starts_with(&format!("admitted epoch {}", new_head.epoch)),
        "{line}"
    );
    println!("public log process: {}", line.trim());

    // 9-11. The restored A snapshot. Its Learn was refused inside the timed move.
    table.insert(
        9,
        (
            "restored Operator A Learn",
            "fenced at 3/3 custodians".into(),
        ),
    );
    let a_dir = m.temp.path().join("A");
    let stale_infer = m.grant(&t.opened.head, infer(&[(0, 8)]));
    fenced_everywhere(
        operate(&a_dir, Operation::Exercise(stale_infer)).unwrap_err(),
        3,
    )?;
    table.insert(
        10,
        (
            "restored Operator A Infer",
            "fenced at 3/3 custodians".into(),
        ),
    );
    provision_operator(&m.temp.path().join("C"), &m.cfg, &m.sockets, &c, &m.genesis)?;
    let to_c = m.grant(
        &t.opened.head,
        Action::Migrate {
            successor: pk(&c),
            seat_payment_claim: random_seed()?,
        },
    );
    let offer_c = match operate(&a_dir, Operation::Offer(to_c))? {
        Outcome::Offered(p) => p,
        other => bail!("expected an offer, got {other:?}"),
    };
    fenced_everywhere(
        operate(&m.temp.path().join("C"), Operation::Accept(offer_c)).unwrap_err(),
        3,
    )?;
    table.insert(
        11,
        (
            "restored Operator A Migrate",
            "fenced at 3/3 custodians".into(),
        ),
    );

    println!("{} cross-layer attacks, all refused:", table.len());
    for (i, (name, why)) in &table {
        println!("  {i:2}. {name}: {why}");
    }
    assert_eq!(
        table.keys().copied().collect::<Vec<_>>(),
        (1..=12).collect::<Vec<_>>()
    );

    // The admitted package is not admitted twice; the log never extends A's head again.
    let r = refusal(public_log.admit(&admission(), &moved.wire));
    assert!(matches!(r, Refusal::Latch(Status::StaleParent)), "{r}");

    // Tulip continuity under B. The backlog replays every message A handled, the forgotten
    // one included, then a new one; only unjournaled messages are learned, so only they get
    // replies.
    public_log.follow(&learned104)?;
    let mut head = learned104.head.clone();
    let mut replied = vec![104];
    for (id, provenance, coord) in [
        (101, Provenance::Experienced, 0),
        (102, Provenance::Told, 1),
        (103, Provenance::Inferred, 2),
        (104, Provenance::Experienced, 3),
        (105, Provenance::Told, 4),
    ] {
        let g = m.grant(&head, learn_as(id, provenance, coord, 11));
        match operate(&b_dir, Operation::Exercise(g)) {
            Ok(Outcome::Certified(c)) => {
                public_log.follow(&c)?;
                head = c.head.clone();
                replied.push(id);
            }
            Ok(other) => bail!("unexpected {other:?}"),
            Err(e) => ensure!(
                e.to_string().matches("duplicate episode").count() == 3,
                "{e}"
            ),
        }
    }
    assert_eq!(replied, [104, 105]);
    // A's disclosure carried over: fresh coordinates after B's Learns exceed the rank cap.
    let err = operate(
        &b_dir,
        Operation::Exercise(m.grant(&head, infer(&[(0, 8)]))),
    )
    .unwrap_err();
    assert_eq!(
        err.to_string().matches("cumulative exposure cap").count(),
        3,
        "{err}"
    );
    let last = public_log.follower().head().clone();
    assert_eq!(last, head);
    let last_cert = certified(operate(
        &b_dir,
        Operation::Exercise(m.grant(&head, learn_as(106, Provenance::Inferred, 5, 13))),
    )?)?;
    public_log.follow(&last_cert)?;
    let (_, final_header) = open_header(&m.sockets[0], &m.cfg, &last_cert, &m.b)?;
    assert_eq!(
        final_header,
        JournalHeader {
            cursor: 7,
            experienced: 2,
            told: 2,
            inferred: 2,
            forgotten: 1
        }
    );
    println!("Tulip resume under B: replied to {replied:?}; 101, 102, 103 and the second 104 refused as duplicate episodes at 3/3; post-learn Infer refused by the carried exposure cap at 3/3; header {final_header:?}");

    // Every custodian step went through the Obend ABI, and natively too when configured.
    for i in 0..m.sockets.len() {
        let log = fs::read_to_string(m.dir(i).join("obend-steps.log"))?;
        let mut counts = [0usize; 7];
        for line in log.lines() {
            let mut f = line.split(' ');
            counts[f.next().unwrap().parse::<usize>()?] += 1;
            assert_eq!(f.nth(1), Some(if native { "1" } else { "0" }));
        }
        println!(
            "custodian {i}: {} Obend steps, by status 0..6 {counts:?}, native {}",
            log.lines().count(),
            if native { "on every step" } else { "off" }
        );
    }
    assert_eq!(*public_log.follower().latch(), latch_state(&last_cert.head));
    Ok(())
}

#[test]
fn paid_move_from_genesis_through_cli() -> Result<()> {
    let m = Mesh::new(3, 3)?;
    let root = m.temp.path();
    let receipt = SeatTransferReceipt::seal(
        seat_transfer(&m.a, pk(&m.b), resident_seat(&m.cfg.genesis())),
        &m.a,
    )?;
    let grant = m.grant(
        &m.genesis,
        Action::Migrate {
            successor: pk(&m.b),
            seat_payment_claim: receipt.seat_root,
        },
    );
    let cli = |cmd: &str, dir: &str, first: &str, second: &str| {
        Process::new(env!("CARGO_BIN_EXE_resident_house_move"))
            .current_dir(root)
            .args([cmd, dir, first, second])
            .output()
    };
    fs::write(root.join("receipt"), receipt.to_bytes()?)?;
    fs::write(root.join("grant"), bincode::serialize(&grant)?)?;
    let offer = cli("offer", "A", "grant", "receipt")?;
    ensure!(
        offer.status.success(),
        "{}",
        String::from_utf8_lossy(&offer.stderr)
    );
    fs::write(root.join("offer"), offer.stdout)?;
    let mut policy = admission();
    policy.max_reserve_cap_minor = 0;
    fs::write(root.join("policy"), bincode::serialize(&policy)?)?;
    let refused = cli("accept", "B", "policy", "offer")?;
    assert!(!refused.status.success());
    assert!(String::from_utf8_lossy(&refused.stderr).contains("unbacked reserve"));
    for i in 0..3 {
        assert!(fs::read(m.dir(i).join("obend-steps.log"))?.is_empty());
    }
    let mut log = ResidentLog::create(&root.join("log"), m.cfg.clone(), &m.genesis)?;
    fs::write(root.join("policy"), bincode::serialize(&admission())?)?;
    let accepted = cli("accept", "B", "policy", "offer")?;
    ensure!(
        accepted.status.success(),
        "{}",
        String::from_utf8_lossy(&accepted.stderr)
    );
    let first = log.admit(&admission(), &accepted.stdout)?;
    assert_eq!(first.head.epoch, 1);
    let retry = cli("accept", "B", "policy", "offer")?;
    ensure!(
        retry.status.success(),
        "{}",
        String::from_utf8_lossy(&retry.stderr)
    );
    let pkg = ResidentMigrationPackage::from_bytes(&retry.stdout)?;
    assert_eq!(pkg.succession.head, first.head);
    assert_eq!(pkg.header.verify(&first.head)?, JournalHeader::default());
    assert!(matches!(
        log.admit(&admission(), &retry.stdout),
        Err(Refusal::Latch(Status::StaleParent))
    ));
    Ok(())
}

#[test]
#[ignore = "serial wall-clock benchmark"]
fn house_move_latency() -> Result<()> {
    let runs: usize = std::env::var("HOUSE_MOVE_RUNS").map_or(Ok(11), |v| v.parse())?;
    ensure!(runs > 0 && runs % 2 == 1, "use a positive odd sample count");
    let mut samples: Vec<Vec<(&str, f64)>> = vec![];
    for _ in 0..runs {
        let mut t = tenure()?;
        samples.push(house_move(&mut t)?.phases);
    }
    println!(
        "{runs} house moves, fresh 3-daemon mesh each, native differential {}",
        if std::env::var_os(obend::NATIVE_ENV).is_some() {
            "on"
        } else {
            "off"
        }
    );
    let mut medians = vec![];
    for i in 0..samples[0].len() {
        let mut v: Vec<f64> = samples.iter().map(|s| s[i].1).collect();
        v.sort_by(f64::total_cmp);
        println!(
            "  min {:8.3}  median {:8.3}  max {:8.3} ms  {}",
            v[0],
            v[runs / 2],
            v[runs - 1],
            samples[0][i].0
        );
        medians.push(v[runs / 2]);
    }
    assert!(
        *medians.last().unwrap() < 120.0,
        "median house move exceeded 120 ms"
    );
    Ok(())
}
