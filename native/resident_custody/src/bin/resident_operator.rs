//! One operator seat: a single custody operation, or the Tulip stream worker and its handoff.
use anyhow::{bail, Context, Result};
use resident_custody::custody_mesh::{operate, Operation};
use resident_custody::tulip_bridge::{self as tulip, Handoff};
use std::fs::File;
use std::path::Path;

const USAGE: &str = "usage: resident_operator SEAT run OPERATION | stream BROKER ISSUER [--test-barriers] | recover | handoff | adopt HANDOFF BROKER";

fn out(t: &impl serde::Serialize) -> Result<()> {
    Ok(bincode::serialize_into(std::io::stdout().lock(), t)?)
}

fn main() -> Result<()> {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    let seat = Path::new(args.first().context(USAGE)?);
    let cmd = args.get(1).context(USAGE)?.to_str().unwrap_or("");
    let arg = |i: usize| -> Result<&Path> { Ok(Path::new(args.get(i).context(USAGE)?)) };
    match (cmd, args.len()) {
        ("run", 3) => {
            let operation: Operation = bincode::deserialize_from(File::open(arg(2)?)?)?;
            out(&operate(seat, operation)?)
        }
        ("stream", 4 | 5) => {
            let barriers = match args.get(4).map(|a| a.to_str()) {
                None => false,
                Some(Some("--test-barriers")) => true,
                _ => bail!(USAGE),
            };
            out(&tulip::stream(seat, arg(2)?, arg(3)?, barriers)?)
        }
        ("recover", 2) => out(&tulip::recover(seat)?),
        ("handoff", 2) => out(&tulip::handoff(seat)?),
        ("adopt", 4) => {
            let h: Handoff = bincode::deserialize_from(File::open(arg(2)?)?)?;
            tulip::adopt(seat, &h, arg(3)?)
        }
        (_, 2) => {
            let operation: Operation = bincode::deserialize_from(File::open(arg(1)?)?)?;
            out(&operate(seat, operation)?)
        }
        _ => bail!(USAGE),
    }
}
