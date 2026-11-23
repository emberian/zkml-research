//! A durable public admission log for one resident.
use anyhow::{bail, ensure, Context, Result};
use bincode::Options;
use resident_custody::custody_mesh::{
    accept_paid_move, offer_paid_move, Certificate, Config, Head,
};
use resident_custody::house_move::{ResidentLog, SeatAdmission};
use std::fs::File;
use std::io::Read;
use std::path::Path;

const USAGE: &str = "usage: resident_house_move init LOG CONFIG GENESIS | follow LOG CERTIFICATE | admit LOG ADMISSION PACKAGE | offer OPERATOR GRANT RECEIPT | accept OPERATOR ADMISSION OFFER";

fn read(path: &Path) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    File::open(path)
        .with_context(|| path.display().to_string())?
        .take((1 << 20) + 1)
        .read_to_end(&mut bytes)?;
    ensure!(bytes.len() <= 1 << 20, "input too large");
    Ok(bytes)
}

fn load<T: serde::de::DeserializeOwned>(path: &Path) -> Result<T> {
    Ok(bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_limit(1 << 20)
        .reject_trailing_bytes()
        .deserialize(&read(path)?)?)
}

fn main() -> Result<()> {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    let cmd = args.first().and_then(|a| a.to_str()).context(USAGE)?;
    let log = Path::new(args.get(1).context(USAGE)?);
    if cmd == "offer" && args.len() == 4 {
        let offer = offer_paid_move(log, load(Path::new(&args[2]))?, read(Path::new(&args[3]))?)?;
        bincode::serialize_into(std::io::stdout().lock(), &offer)?;
        return Ok(());
    }
    if cmd == "accept" && args.len() == 4 {
        let pkg = accept_paid_move(log, load(Path::new(&args[3]))?, &load(Path::new(&args[2]))?)?;
        bincode::serialize_into(std::io::stdout().lock(), &pkg)?;
        return Ok(());
    }
    if cmd == "init" && args.len() == 4 {
        let cfg: Config = load(Path::new(&args[2]))?;
        let genesis: Head = load(Path::new(&args[3]))?;
        ResidentLog::create(log, cfg, &genesis)?;
        println!("provisioned genesis {}", hex::encode(genesis.genesis_id));
        return Ok(());
    }
    if !matches!((cmd, args.len()), ("follow", 3) | ("admit", 4)) {
        bail!(USAGE);
    }
    let mut journal = ResidentLog::open(log)?;
    let path = Path::new(args.last().unwrap());
    let outcome = if cmd == "follow" {
        let cert: Certificate = load(path)?;
        journal
            .follow(&cert)
            .map(|()| format!("followed epoch {}", cert.head.epoch))
    } else {
        let admission: SeatAdmission = load(Path::new(&args[2]))?;
        journal.admit(&admission, &read(path)?)
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
