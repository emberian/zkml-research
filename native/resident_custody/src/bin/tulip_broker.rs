//! The Tulip town stream and outbox broker of one resident.
use anyhow::{ensure, Context, Result};
use std::path::Path;
fn main() -> Result<()> {
    let mut args = std::env::args_os().skip(1);
    let dir = args.next().context("usage: tulip_broker DIR")?;
    ensure!(args.next().is_none(), "unknown option");
    resident_custody::tulip_bridge::serve_broker(Path::new(&dir))
}
