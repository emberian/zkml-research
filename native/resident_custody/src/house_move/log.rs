//! Each committed epoch is one file containing its latch, head and admitted wire input.
//! A reader can see the old epoch or the complete new one across a crash.
use super::{Admitted, Follower, Refusal, ResidentMigrationPackage, SeatAdmission};
use crate::custody_mesh::{Certificate, Config, Head};
use crate::obend_latch_abi::StateWords;
use anyhow::{ensure, Context, Result};
use fs2::FileExt;
use std::fs::{self, File, OpenOptions};
use std::io::{Seek, Write};
use std::path::{Path, PathBuf};

pub struct ResidentLog {
    dir: PathBuf,
    _lock: File,
    follower: Follower,
}

fn lock(dir: &Path) -> Result<File> {
    let lock = OpenOptions::new()
        .create(true)
        .truncate(false)
        .write(true)
        .open(dir.join("lock"))?;
    lock.try_lock_exclusive().context("log in use")?;
    Ok(lock)
}

fn publish(dir: &Path, name: &str, bytes: &[u8]) -> Result<()> {
    let path = dir.join(name);
    ensure!(
        !path.try_exists()?,
        "log entry already exists; reopen the log"
    );
    let tmp = dir.join("pending");
    let mut file = File::create(&tmp)?;
    file.write_all(bytes)?;
    file.sync_all()?;
    fs::rename(tmp, path)?;
    File::open(dir)?.sync_all()?;
    Ok(())
}

fn persist(dir: &Path, input: &[u8], latch: &StateWords, head: &Head) -> Result<()> {
    publish(
        dir,
        &format!("epoch-{:016x}", head.epoch),
        &bincode::serialize(&(latch, head, input))?,
    )
}

impl ResidentLog {
    pub fn create(dir: &Path, cfg: Config, genesis: &Head) -> Result<Self> {
        let follower = Follower::genesis(cfg.clone(), genesis)?;
        fs::create_dir(dir)?;
        let guard = lock(dir)?;
        publish(dir, "config", &bincode::serialize(&cfg)?)?;
        persist(dir, &[], follower.latch(), genesis)?;
        File::open(dir.join(".."))?.sync_all()?;
        Ok(Self {
            dir: dir.to_owned(),
            _lock: guard,
            follower,
        })
    }

    pub fn open(dir: &Path) -> Result<Self> {
        let guard = lock(dir)?;
        File::open(dir)?.sync_all()?;
        let cfg: Config = bincode::deserialize_from(File::open(dir.join("config"))?)?;
        let mut latest = None;
        for entry in fs::read_dir(dir)? {
            let name = entry?.file_name();
            if let Some(suffix) = name.to_str().and_then(|s| s.strip_prefix("epoch-")) {
                let epoch = u64::from_str_radix(suffix, 16)?;
                ensure!(format!("{epoch:016x}") == suffix, "invalid epoch filename");
                latest = latest.max(Some(epoch));
            }
        }
        let epoch = latest.context("no committed genesis")?;
        let mut file = File::open(dir.join(format!("epoch-{epoch:016x}")))?;
        let (latch, head): (StateWords, Head) = bincode::deserialize_from(&mut file)?;
        ensure!(head.epoch == epoch, "epoch file and head disagree");
        let input_len: u64 = bincode::deserialize_from(&mut file)?;
        ensure!(
            file.metadata()?.len().checked_sub(file.stream_position()?) == Some(input_len),
            "incomplete committed input"
        );
        let follower = Follower::recover(cfg, latch, head)?;
        Ok(Self {
            dir: dir.to_owned(),
            _lock: guard,
            follower,
        })
    }

    pub fn follower(&self) -> &Follower {
        &self.follower
    }

    pub fn follow(&mut self, cert: &Certificate) -> Result<(), Refusal> {
        let input = bincode::serialize(cert).map_err(|e| Refusal::Malformed(e.to_string()))?;
        self.follower
            .follow(cert, |l, h| persist(&self.dir, &input, l, h))
    }

    pub fn admit(&mut self, policy: &SeatAdmission, input: &[u8]) -> Result<Admitted, Refusal> {
        let pkg = ResidentMigrationPackage::from_bytes(input)?;
        self.follower
            .admit(policy, &pkg, |l, h| persist(&self.dir, input, l, h))
    }
}
