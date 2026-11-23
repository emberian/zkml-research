//! Live custodian mesh harness shared by the resident custody integration tests.
#![allow(dead_code)]

use anyhow::{anyhow, ensure, Result};
use ed25519_dalek::SigningKey;
use resident_custody::{custody_mesh::*, random_seed};
use std::fs;
use std::os::unix::net::UnixStream;
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command as Process};
use std::time::{Duration, Instant};
use tempfile::TempDir;

pub struct OwnedChild {
    child: Child,
    pidfile: PathBuf,
}
impl OwnedChild {
    pub fn spawn(cmd: &mut Process, pidfile: PathBuf) -> Result<Self> {
        let child = cmd.spawn()?;
        let owner = Self { child, pidfile };
        fs::write(&owner.pidfile, owner.child.id().to_string())?;
        Ok(owner)
    }
    pub fn kill9(&mut self) -> Result<()> {
        ensure!(self.child.try_wait()?.is_none(), "child already exited");
        let pid = fs::read_to_string(&self.pidfile)?.parse::<u32>()?;
        ensure!(pid == self.child.id(), "pid mismatch");
        // The unreaped child handle pins this PID. Child::kill is SIGKILL on Unix.
        self.child.kill()?;
        ensure!(self.child.wait()?.signal() == Some(9), "expected SIGKILL");
        Ok(())
    }
    pub fn try_status(&mut self) -> Result<Option<std::process::ExitStatus>> {
        Ok(self.child.try_wait()?)
    }
    pub fn output(&mut self) -> Result<Outcome> {
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

pub fn wait_for(mut ready: impl FnMut() -> bool) -> Result<()> {
    let deadline = Instant::now() + Duration::from_secs(8);
    while !ready() {
        ensure!(Instant::now() < deadline, "boundary timeout");
        std::thread::sleep(Duration::from_millis(4));
    }
    Ok(())
}

pub fn pk(k: &SigningKey) -> [u8; 32] {
    k.verifying_key().to_bytes()
}
pub fn sk() -> SigningKey {
    SigningKey::from_bytes(&random_seed().unwrap())
}

pub struct Mesh {
    pub children: Vec<Option<OwnedChild>>,
    pub sockets: Vec<PathBuf>,
    pub cfg: Config,
    pub genesis: Head,
    pub issuer: SigningKey,
    pub a: SigningKey,
    pub b: SigningKey,
    /// Custodian signing keys, roster order. Only tests that model an equivocating quorum use them.
    pub keys: Vec<SigningKey>,
    pub temp: TempDir,
}

impl Mesh {
    pub fn new(n: usize, t: u16) -> Result<Self> {
        // Short absolute paths also fit Darwin's sockaddr_un. RESIDENT_MESH_DIR moves the mesh
        // off /tmp, which is a tmpfs on some hosts, where fsync costs nothing.
        let root = std::env::var_os("RESIDENT_MESH_DIR").unwrap_or_else(|| "/tmp".into());
        let temp = tempfile::Builder::new().prefix("res-").tempdir_in(root)?;
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
            keys,
            temp,
        };
        for i in 0..n {
            m.start(i)?;
        }
        Ok(m)
    }
    pub fn dir(&self, i: usize) -> &Path {
        self.sockets[i].parent().unwrap()
    }
    pub fn start(&mut self, i: usize) -> Result<()> {
        let mut cmd = Process::new(env!("CARGO_BIN_EXE_custodian_node"));
        cmd.arg(self.dir(i)).arg("--test-barriers");
        self.children[i] = Some(OwnedChild::spawn(&mut cmd, self.dir(i).join("node.pid"))?);
        wait_for(|| UnixStream::connect(&self.sockets[i]).is_ok())
    }
    pub fn arm(&self, i: usize, phase: &str) -> Result<()> {
        Ok(fs::write(self.dir(i).join(format!("arm-{phase}")), [])?)
    }
    pub fn at(&self, i: usize, phase: &str) -> Result<()> {
        wait_for(|| self.dir(i).join(format!("at-{phase}")).exists())
    }
    pub fn crash(&mut self, i: usize, phase: &str) -> Result<()> {
        self.children[i].take().unwrap().kill9()?;
        fs::remove_file(self.dir(i).join(format!("arm-{phase}")))?;
        Ok(())
    }
    pub fn grant(&self, h: &Head, a: Action) -> Grant {
        Grant::issue(&self.issuer, h, a)
    }
    pub fn operator(&self, name: &str, op: Operation) -> Result<OwnedChild> {
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
    pub fn exercise(&self, name: &str, head: &Head, action: Action) -> Result<Certificate> {
        certified(
            self.operator(name, Operation::Exercise(self.grant(head, action)))?
                .output()?,
        )
    }
}
pub fn certified(result: Outcome) -> Result<Certificate> {
    match result {
        Outcome::Certified(c) => Ok(c),
        _ => Err(anyhow!("expected certificate")),
    }
}
pub fn infer(ranges: &[(u16, u16)]) -> Action {
    Action::Infer {
        ranges: ranges.to_owned(),
    }
}
pub fn learn(id: u64, coord: u8, value: u64) -> Action {
    learn_as(id, Provenance::Experienced, coord, value)
}
/// A unit-key GDN step on one coordinate, so steps on distinct coordinates are orthogonal.
pub fn learn_as(id: u64, provenance: Provenance, coord: u8, value: u64) -> Action {
    let mut key = [0; 8];
    key[usize::from(coord)] = 1;
    Action::Learn {
        episode: id,
        provenance,
        step: GdnStep {
            key,
            value,
            beta: 1,
            gamma: 3,
        },
    }
}

