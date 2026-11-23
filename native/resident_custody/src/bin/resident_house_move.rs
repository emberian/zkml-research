//! A public log for one resident: an Obend latch on disk, stepped by certified successions
//! and admitted migration packages. The admitted input is appended and synced, then the latch
//! file is replaced; that write's outcome is the request's `persistAck`.
use anyhow::{bail, Context, Result};
use fs2::FileExt;
use resident_custody::custody_mesh::{Certificate, Config, Head};
use resident_custody::house_move::{Follower, ResidentMigrationPackage, SeatAdmission};
use resident_custody::obend_latch_abi::StateWords;
use std::fs::{self, File, OpenOptions};
use std::io::Write;
use std::path::Path;

const USAGE: &str = "usage: resident_house_move init LOG CONFIG GENESIS | follow LOG CERTIFICATE | admit LOG ADMISSION PACKAGE";

fn load<T: serde::de::DeserializeOwned>(path: &Path) -> Result<T> {
    let file = File::open(path).with_context(|| path.display().to_string())?;
    Ok(bincode::deserialize_from(file)?)
}

fn replace(dir: &Path, name: &str, bytes: &[u8]) -> Result<()> {
    let tmp = dir.join(format!("{name}.new"));
    let mut f = File::create(&tmp)?;
    f.write_all(bytes)?;
    f.sync_all()?;
    fs::rename(&tmp, dir.join(name))?;
    File::open(dir)?.sync_all()?;
    Ok(())
}

fn persist(log: &Path, input: &[u8], latch: &StateWords, head: &Head) -> Result<()> {
    let mut admitted = OpenOptions::new()
        .create(true)
        .append(true)
        .open(log.join("admitted"))?;
    admitted.write_all(&(input.len() as u64).to_le_bytes())?;
    admitted.write_all(input)?;
    admitted.sync_all()?;
    replace(log, "latch", &bincode::serialize(&(latch, head))?)
}

fn main() -> Result<()> {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    let cmd = args.first().and_then(|a| a.to_str()).context(USAGE)?;
    let log = Path::new(args.get(1).context(USAGE)?);
    if cmd == "init" && args.len() == 4 {
        let cfg: Config = load(Path::new(&args[2]))?;
        let genesis: Head = load(Path::new(&args[3]))?;
        let follower = Follower::genesis(cfg.clone(), &genesis)?;
        fs::create_dir(log)?;
        replace(log, "config", &bincode::serialize(&cfg)?)?;
        persist(log, &[], follower.latch(), follower.head())?;
        println!("provisioned genesis {}", hex::encode(genesis.genesis_id));
        return Ok(());
    }
    if !matches!((cmd, args.len()), ("follow", 3) | ("admit", 4)) {
        bail!(USAGE);
    }
    let lock = OpenOptions::new()
        .create(true)
        .truncate(false)
        .write(true)
        .open(log.join("lock"))?;
    lock.try_lock_exclusive().context("log in use")?;
    let cfg: Config = load(&log.join("config"))?;
    let (latch, head): (StateWords, Head) = load(&log.join("latch"))?;
    let mut follower = Follower::recover(cfg, latch, head)?;
    let input = fs::read(args.last().unwrap())?;
    let outcome = if cmd == "follow" {
        let cert: Certificate = bincode::deserialize(&input)?;
        follower
            .follow(&cert, |l, h| persist(log, &input, l, h))
            .map(|()| format!("followed epoch {}", cert.head.epoch))
    } else {
        let admission: SeatAdmission = load(Path::new(&args[2]))?;
        ResidentMigrationPackage::from_bytes(&input)
            .and_then(|pkg| follower.admit(&admission, &pkg, |l, h| persist(log, &input, l, h)))
            .map(|a| {
                format!(
                    "admitted epoch {} operator {} seat_root {} cursor {} experienced {} told {} inferred {} forgotten {}",
                    a.head.epoch,
                    hex::encode(a.head.operator_id),
                    hex::encode(a.receipt.seat_root),
                    a.header.cursor,
                    a.header.experienced,
                    a.header.told,
                    a.header.inferred,
                    a.header.forgotten
                )
            })
    };
    match outcome {
        Ok(line) => println!("{line}"),
        Err(refusal) => {
            eprintln!("refused: {refusal}");
            std::process::exit(2);
        }
    }
    Ok(())
}
