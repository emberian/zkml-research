use anyhow::{ensure, Context, Result};
use std::path::Path;
fn main() -> Result<()> {
    let mut args = std::env::args_os().skip(1);
    let dir = args
        .next()
        .context("usage: custodian_node DIR [--test-barriers]")?;
    let mode = args.next();
    ensure!(
        mode.as_deref().is_none_or(|m| m == "--test-barriers") && args.next().is_none(),
        "unknown option"
    );
    resident_custody::custody_mesh::serve(Path::new(&dir), mode.is_some())
}
