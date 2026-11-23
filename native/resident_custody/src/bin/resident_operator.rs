use anyhow::{Context, Result};
use resident_custody::custody_mesh::{operate, Operation};
use std::fs::File;
use std::path::Path;

fn main() -> Result<()> {
    let mut args = std::env::args_os().skip(1);
    let seat = args
        .next()
        .context("usage: resident_operator SEAT OPERATION")?;
    let task = args.next().context("missing operation file")?;
    let operation: Operation = bincode::deserialize_from(File::open(task)?)?;
    let result = operate(Path::new(&seat), operation)?;
    bincode::serialize_into(std::io::stdout().lock(), &result)?;
    Ok(())
}
