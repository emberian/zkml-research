//! One durable vote per epoch. A transition needs a certified parent, a
//! policy issuer's exact-action grant, and the active operator's signature.
use crate::belt_latch_kernel::*;
use crate::cshake_selective_open as opening;
use crate::{digest, Digest};
use anyhow::{anyhow, bail, ensure, Context, Result};
use bincode::Options;
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use fs2::FileExt;
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use std::collections::BTreeSet;
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::os::unix::fs::DirBuilderExt;
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::time::Duration;

pub const CELL_BYTES: usize = 64;
const FRAME: usize = 8 << 20;
type Bytes = Vec<u8>;

fn hash<T: Serialize>(domain: &[u8], t: &T) -> Digest {
    digest(
        domain,
        &[&bincode::serialize(t).expect("serializable protocol type")],
    )
}

fn key(pk: Digest) -> Result<VerifyingKey> {
    let k = VerifyingKey::from_bytes(&pk)?;
    ensure!(!k.is_weak(), "weak Ed25519 key");
    Ok(k)
}

fn signature(sk: &SigningKey, domain: &[u8], t: &impl Serialize) -> Bytes {
    sk.sign(&hash(domain, t)).to_bytes().to_vec()
}

fn verify_sig(pk: Digest, domain: &[u8], t: &impl Serialize, sig: &[u8]) -> Result<()> {
    key(pk)?.verify_strict(&hash(domain, t), &Signature::from_slice(sig)?)?;
    Ok(())
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Policy {
    pub issuer: Digest,
    pub output_bits: u64,
    pub output_rank: u64,
    pub slices: Vec<(u16, u16)>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Config {
    pub nonce: Digest,
    pub first_operator: Digest,
    pub roster: Vec<Digest>,
    pub threshold: u16,
    pub max_corrupt: u16,
    pub policy: Policy,
}

impl Config {
    pub fn validate(&self) -> Result<()> {
        let n = self.roster.len();
        let t = usize::from(self.threshold);
        let f = usize::from(self.max_corrupt);
        ensure!(
            n <= u16::MAX as usize && f < n && t <= n && 2 * t > n + f,
            "split-quorum configuration: require 2t > n + f"
        );
        ensure!(
            self.roster.iter().collect::<BTreeSet<_>>().len() == n,
            "duplicate custodian"
        );
        for &pk in &self.roster {
            key(pk)?;
        }
        key(self.first_operator)?;
        key(self.policy.issuer)?;
        opening::check_ranges(CELL_BYTES, &self.policy.slices)?;
        Ok(())
    }
    pub fn genesis(&self) -> Digest {
        hash(b"mesh genesis", self)
    }
}

// This complete head is the signed migration manifest. parent_commitment
// chains all preceding heads and change binds the chosen transition.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Head {
    pub genesis_id: Digest,
    pub epoch: u64,
    pub state_commitment: Digest,
    pub policy_hash: Digest,
    pub journal_cursor: u64,
    pub seat_payment_claim: Digest,
    pub operator_id: Digest,
    pub parent_commitment: Digest,
    pub change: Digest,
    pub output_bits: u64,
    pub output_rank: u64,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum Action {
    Learn {
        episode: u64,
        step: GdnStep,
    },
    Infer {
        ranges: Vec<(u16, u16)>,
    },
    Forget {
        episode: u64,
    },
    Migrate {
        successor: Digest,
        seat_payment_claim: Digest,
    },
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Grant {
    pub parent: Head,
    pub action: Action,
    pub issuer_signature: Bytes,
}

impl Grant {
    pub fn issue(issuer: &SigningKey, parent: &Head, action: Action) -> Self {
        let issuer_signature = signature(issuer, b"exact capability", &(parent, &action));
        Self {
            parent: parent.clone(),
            action,
            issuer_signature,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Command {
    pub grant: Grant,
    pub operator_signature: Bytes,
    pub successor_signature: Option<Bytes>,
}

impl Command {
    pub fn authorize(grant: Grant, operator: &SigningKey, successor: Option<&SigningKey>) -> Self {
        let operator_signature = signature(operator, b"exercise grant", &grant);
        let successor_signature =
            successor.map(|s| signature(s, b"accept signed move", &(&grant, &operator_signature)));
        Self {
            grant,
            operator_signature,
            successor_signature,
        }
    }
    fn authenticate(&self, cfg: &Config) -> Result<()> {
        let g = &self.grant;
        verify_sig(
            cfg.policy.issuer,
            b"exact capability",
            &(&g.parent, &g.action),
            &g.issuer_signature,
        )?;
        verify_sig(
            g.parent.operator_id,
            b"exercise grant",
            g,
            &self.operator_signature,
        )?;
        match (&g.action, &self.successor_signature) {
            (Action::Migrate { successor, .. }, Some(sig)) => {
                ensure!(*successor != g.parent.operator_id, "same successor");
                verify_sig(
                    *successor,
                    b"accept signed move",
                    &(g, &self.operator_signature),
                    sig,
                )
            }
            (Action::Migrate { .. }, None) => bail!("missing successor acceptance"),
            (_, Some(_)) => bail!("unexpected successor acceptance"),
            (_, None) => Ok(()),
        }
    }
    fn id(&self) -> Digest {
        hash(b"transition", self)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Vote {
    pub signer: u16,
    pub signature: Bytes,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Certificate {
    pub head: Head,
    pub votes: Vec<Vote>,
}

impl Certificate {
    pub fn verify(&self, cfg: &Config) -> Result<()> {
        cfg.validate()?;
        ensure!(
            self.head.genesis_id == cfg.genesis()
                && self.head.policy_hash == hash(b"policy", &cfg.policy),
            "foreign manifest"
        );
        ensure!(
            self.votes.len() >= usize::from(cfg.threshold) && self.votes.len() <= cfg.roster.len(),
            "insufficient or excessive quorum"
        );
        let mut seen = BTreeSet::new();
        for v in &self.votes {
            ensure!(seen.insert(v.signer), "duplicate signer");
            let pk = cfg
                .roster
                .get(usize::from(v.signer))
                .context("unknown signer")?;
            verify_sig(*pk, b"durable epoch", &self.head, &v.signature)?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Proposal {
    pub command: Command,
    pub parent_certificate: Option<Certificate>,
}

/// One d_v=1, d_k=8 fast-weight update over the Mersenne prime.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct GdnStep {
    pub key: [u64; 8],
    pub value: u64,
    pub gamma: u64,
    pub beta: u64,
}
const PRIME: u64 = (1 << 61) - 1;
fn mul(a: u64, b: u64) -> u64 {
    (u128::from(a) * u128::from(b) % u128::from(PRIME)) as u64
}
fn dot(a: &[u64; 8], b: &[u64; 8]) -> u64 {
    a.iter()
        .zip(b)
        .fold(0, |s, (&x, &y)| (s + mul(x, y)) % PRIME)
}
impl GdnStep {
    fn validate(&self) -> Result<()> {
        ensure!(
            self.key
                .iter()
                .chain([&self.value, &self.gamma, &self.beta])
                .all(|&x| x < PRIME),
            "noncanonical field input"
        );
        Ok(())
    }
    fn delta(&self, weights: &[u64; 8]) -> [u64; 8] {
        let residual = (self.value + PRIME - dot(weights, &self.key)) % PRIME;
        let scale = mul(self.beta, residual);
        self.key.map(|k| mul(scale, k))
    }
    fn apply(&self, w: &mut [u64; 8], delta: [u64; 8]) {
        for (coord, d) in w.iter_mut().zip(delta) {
            *coord = (mul(self.gamma, *coord) + d) % PRIME;
        }
    }
}
#[derive(Clone, Serialize, Deserialize)]
struct Episode {
    id: u64,
    step: GdnStep,
    delta: [u64; 8],
    forgotten: bool,
}

#[derive(Clone, Serialize, Deserialize)]
struct State {
    head: Head,
    history: Vec<Episode>,
    weights: [u64; 8],
    // Coordinates observed since the last weight change. Across versions,
    // charge fresh rank conservatively, retaining the lifetime total.
    observed: [u64; 8],
    blinding_key: Digest,
    blind: Digest,
    releasable: Option<Vec<(u16, u16)>>,
}

impl State {
    fn genesis(cfg: &Config, secret: Digest) -> Self {
        let genesis_id = cfg.genesis();
        let blind = digest(b"genesis blind", &[&secret, &genesis_id]);
        let head = Head {
            genesis_id,
            epoch: 0,
            state_commitment: opening::root(&blind, &[0; CELL_BYTES]),
            policy_hash: hash(b"policy", &cfg.policy),
            journal_cursor: 0,
            seat_payment_claim: [0; 32],
            operator_id: cfg.first_operator,
            parent_commitment: [0; 32],
            change: [0; 32],
            output_bits: 0,
            output_rank: 0,
        };
        Self {
            head,
            history: vec![],
            weights: [0; 8],
            observed: [0; 8],
            blinding_key: secret,
            blind,
            releasable: None,
        }
    }
    fn cell(&self) -> Vec<u8> {
        self.weights.iter().flat_map(|w| w.to_le_bytes()).collect()
    }

    fn replay(&self) -> Result<[u64; 8]> {
        let mut model = [0; 8];
        for e in &self.history {
            e.step.validate()?;
            let delta = if e.forgotten {
                [0; 8]
            } else {
                e.step.delta(&model)
            };
            e.step.apply(&mut model, delta);
        }
        Ok(model)
    }

    fn charge(&mut self, p: &Policy, ranges: &[(u16, u16)]) -> Result<()> {
        let bytes = opening::check_ranges(CELL_BYTES, ranges)?;
        ensure!(bytes > 0, "empty inference");
        let mut new_rank = 0;
        for &(a, b) in ranges {
            ensure!(
                p.slices.iter().any(|&(s, e)| s <= a && b <= e),
                "slice outside policy"
            );
            for pos in a..b {
                let word = &mut self.observed[usize::from(pos / 8)];
                let mask = 255u64 << (8 * (pos % 8));
                new_rank += u64::from((mask & !*word).count_ones());
                *word |= mask;
            }
        }
        self.head.output_rank = self
            .head
            .output_rank
            .checked_add(new_rank)
            .context("rank overflow")?;
        self.head.output_bits = self
            .head
            .output_bits
            .checked_add(8 * bytes as u64)
            .context("bit overflow")?;
        ensure!(
            self.head.output_rank <= p.output_rank && self.head.output_bits <= p.output_bits,
            "cumulative exposure cap"
        );
        self.releasable = Some(ranges.to_owned());
        Ok(())
    }

    fn advance(&self, cfg: &Config, cmd: &Command) -> Result<Self> {
        ensure!(
            cmd.grant.parent == self.head,
            "fenced: stale parent or operator"
        );
        let mut s = self.clone();
        s.releasable = None;
        let action = &cmd.grant.action;
        match action {
            Action::Learn { episode, step } => {
                step.validate()?;
                ensure!(
                    !s.history.iter().any(|e| e.id == *episode),
                    "duplicate episode"
                );
                let delta = step.delta(&s.weights);
                step.apply(&mut s.weights, delta);
                s.history.push(Episode {
                    id: *episode,
                    step: step.clone(),
                    delta,
                    forgotten: false,
                });
            }
            Action::Forget { episode } => {
                let pos = s
                    .history
                    .iter()
                    .position(|e| e.id == *episode && !e.forgotten)
                    .context("no live episode")?;
                let (before, after) = s.history.split_at_mut(pos + 1);
                let e = &mut before[pos];
                let mut decay = 1;
                for later in after {
                    ensure!(
                        later.forgotten || dot(&e.step.key, &later.step.key) == 0,
                        "nonorthogonal later episode"
                    );
                    decay = mul(decay, later.step.gamma);
                }
                for (w, d) in s.weights.iter_mut().zip(e.delta) {
                    *w = (*w + PRIME - mul(d, decay)) % PRIME;
                }
                e.forgotten = true;
            }
            Action::Infer { ranges } => s.charge(&cfg.policy, ranges)?,
            Action::Migrate {
                successor,
                seat_payment_claim,
            } => {
                s.head.operator_id = *successor;
                s.head.seat_payment_claim = *seat_payment_claim;
            }
        }
        s.head.change = cmd.id();
        if matches!(action, Action::Learn { .. } | Action::Forget { .. }) {
            ensure!(s.weights == s.replay()?, "W0 replay mismatch");
            s.head.journal_cursor += 1;
            s.blind = digest(b"cell blind", &[&s.blinding_key, &s.head.change]);
            s.head.state_commitment = opening::root(&s.blind, &s.cell());
            s.observed = [0; 8];
        }
        s.head.parent_commitment = hash(b"parent", &self.head);
        s.head.epoch += 1;
        Ok(s)
    }
}

#[derive(Clone, Serialize, Deserialize)]
struct Identity {
    cfg: Config,
    signer: u16,
    secret: Digest,
    initial: Head,
}

fn atomic(dir: &Path, name: &str, value: &impl Serialize) -> Result<()> {
    write_slot(dir, name, value, false)
}
fn write_slot(
    dir: &Path,
    name: &str,
    value: &impl Serialize,
    pause_before_rename: bool,
) -> Result<()> {
    let tmp = dir.join(format!("{name}.new"));
    let mut file = File::create(&tmp)?;
    bincode::serialize_into(&mut file, value)?;
    file.sync_all()?;
    barrier(dir, pause_before_rename, "pre")?;
    fs::rename(tmp, dir.join(name))?;
    File::open(dir)?.sync_all()?;
    Ok(())
}

pub fn provision(
    dir: &Path,
    cfg: &Config,
    signer: u16,
    key: &SigningKey,
    shared_blinding_key: Digest,
) -> Result<Head> {
    cfg.validate()?;
    ensure!(
        cfg.roster.get(usize::from(signer)) == Some(&key.verifying_key().to_bytes()),
        "wrong node key"
    );
    fs::DirBuilder::new().mode(0o700).create(dir)?;
    let state = State::genesis(cfg, shared_blinding_key);
    atomic(dir, "epoch.wal", &state)?;
    atomic(dir, "checkpoint", &state)?;
    atomic(
        dir,
        "identity",
        &Identity {
            cfg: cfg.clone(),
            signer,
            secret: key.to_bytes(),
            initial: state.head.clone(),
        },
    )?;
    File::open(dir.parent().context("missing parent directory")?)?.sync_all()?;
    Ok(state.head)
}

fn load<T: DeserializeOwned>(dir: &Path, name: &str) -> Result<T> {
    Ok(bincode::deserialize_from(File::open(dir.join(name))?)?)
}

#[derive(Serialize, Deserialize)]
pub enum Request {
    Bind(Proposal),
    Release {
        certificate: Certificate,
        operator_signature: Bytes,
    },
}
#[derive(Serialize, Deserialize)]
pub enum Answer {
    Vote(Head, Vote),
    Opening(opening::Statement, Bytes),
    Refused(String),
}

fn recv<T: DeserializeOwned>(stream: &mut UnixStream) -> Result<T> {
    let mut size = [0; 4];
    stream.read_exact(&mut size)?;
    let n = u32::from_be_bytes(size) as usize;
    ensure!(n <= FRAME, "frame too large");
    let mut buf = vec![0; n];
    stream.read_exact(&mut buf)?;
    Ok(bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_limit(FRAME as u64)
        .reject_trailing_bytes()
        .deserialize(&buf)?)
}
fn send(stream: &mut UnixStream, t: &impl Serialize) -> Result<()> {
    let buf = bincode::serialize(t)?;
    ensure!(buf.len() <= FRAME, "frame too large");
    stream.write_all(&(buf.len() as u32).to_be_bytes())?;
    stream.write_all(&buf)?;
    Ok(())
}
fn timeouts(s: &UnixStream) -> Result<()> {
    let timeout = Some(Duration::from_secs(10));
    s.set_read_timeout(timeout)?;
    s.set_write_timeout(timeout)?;
    Ok(())
}

pub fn rpc(path: &Path, req: &Request) -> Result<Answer> {
    let mut s = UnixStream::connect(path)?;
    timeouts(&s)?;
    send(&mut s, req)?;
    match recv(&mut s)? {
        Answer::Refused(reason) => bail!("{reason}"),
        answer => Ok(answer),
    }
}

pub fn certify(cfg: &Config, sockets: &[PathBuf], proposal: &Proposal) -> Result<Certificate> {
    cfg.validate()?;
    let req = Request::Bind(proposal.clone());
    let mut groups = std::collections::BTreeMap::<Digest, Certificate>::new();
    let mut errors = vec![];
    for socket in sockets {
        match rpc(socket, &req) {
            Ok(Answer::Vote(head, v)) => {
                let checked = (|| -> Result<()> {
                    ensure!(
                        head.genesis_id == cfg.genesis()
                            && head.change == proposal.command.id()
                            && head.epoch
                                == proposal
                                    .command
                                    .grant
                                    .parent
                                    .epoch
                                    .checked_add(1)
                                    .context("epoch")?
                            && head.parent_commitment
                                == hash(b"parent", &proposal.command.grant.parent),
                        "unexpected vote"
                    );
                    let pk = cfg
                        .roster
                        .get(usize::from(v.signer))
                        .context("unknown signer")?;
                    verify_sig(*pk, b"durable epoch", &head, &v.signature)?;
                    let group = groups.entry(hash(b"parent", &head)).or_insert(Certificate {
                        head,
                        votes: vec![],
                    });
                    ensure!(
                        !group.votes.iter().any(|x| x.signer == v.signer),
                        "duplicate signer"
                    );
                    group.votes.push(v);
                    Ok(())
                })();
                if let Err(e) = checked {
                    errors.push(e.to_string());
                }
            }
            Err(e) => errors.push(e.to_string()),
            _ => errors.push("unexpected response".into()),
        }
    }
    for cert in groups.into_values() {
        if cert.verify(cfg).is_ok() {
            return Ok(cert);
        }
    }
    bail!("quorum refusal: {}", errors.join(", "))
}

pub fn release(
    socket: &Path,
    cfg: &Config,
    cert: &Certificate,
    operator: &SigningKey,
    ranges: &[(u16, u16)],
) -> Result<(opening::Statement, Bytes)> {
    cert.verify(cfg)?;
    let req = Request::Release {
        certificate: cert.clone(),
        operator_signature: signature(operator, b"release certified output", &cert.head),
    };
    if let Answer::Opening(st, proof) = rpc(socket, &req)? {
        ensure!(
            st.cell_root == cert.head.state_commitment,
            "uncertified cell commitment"
        );
        opening::verify(CELL_BYTES, ranges, &st, &proof)?;
        Ok((st, proof))
    } else {
        bail!("expected projection")
    }
}

// Block only when the local test controller has armed this exact boundary.
// SIGKILL is delivered externally by the owner of the Child handle.
fn barrier(dir: &Path, enabled: bool, phase: &str) -> Result<()> {
    if enabled && dir.join(format!("arm-{phase}")).try_exists()? {
        fs::write(dir.join(format!("at-{phase}")), [])?;
        while dir.join(format!("arm-{phase}")).try_exists()? {
            std::thread::sleep(Duration::from_millis(5));
        }
    }
    Ok(())
}

fn latch_request(epoch: u64, id: Digest, persist_ok: bool) -> BeltLatchBindRequest {
    BeltLatchBindRequest {
        epoch,
        msg_digest: id,
        retry_salt: [0; 32],
        digits: BeltLatchDigits {
            len: 0,
            row0: [0; 32],
            row1: [0; 32],
            row2: [0; 32],
            row3: [0; 32],
        },
        persist_ok,
    }
}

fn latch(head: &Head) -> Result<BeltLatchKernel> {
    let r = latch_request(head.epoch, head.change, true);
    BeltLatchKernel::recover(
        BELT_LATCH_MAX_CAPACITY_LIMIT,
        head.epoch + 1,
        true,
        BeltLatchKernelRecord {
            epoch: r.epoch,
            msg_digest: r.msg_digest,
            retry_salt: r.retry_salt,
            digits: r.digits,
        },
    )
    .map_err(|e| anyhow!("recover: {e:?}"))
}

struct Node {
    dir: PathBuf,
    identity: Identity,
    state: State,
    key: SigningKey,
    barriers: bool,
}

impl Node {
    fn prepare(&self, p: &Proposal) -> Result<Option<State>> {
        let cmd = &p.command;
        cmd.authenticate(&self.identity.cfg)?;
        let parent = &cmd.grant.parent;
        match &p.parent_certificate {
            None => ensure!(parent == &self.identity.initial, "uncertified parent"),
            Some(cert) => {
                cert.verify(&self.identity.cfg)?;
                ensure!(cert.head == *parent, "wrong parent certificate");
            }
        }
        let epoch = parent.epoch.checked_add(1).context("epoch overflow")?;
        if epoch <= self.state.head.epoch {
            // The kernel resolves all consumed/in-flight requests before
            // consulting persistence. No bytes were written on this path.
            let (_, result) = latch(&self.state.head)?.bind(latch_request(epoch, cmd.id(), false));
            ensure!(
                result == Ok(BeltLatchBindOutcome::Replay),
                "fenced: {result:?}"
            );
            return Ok(None);
        }
        ensure!(
            epoch == self.state.head.epoch + 1 && epoch < BELT_LATCH_MAX_CAPACITY_LIMIT,
            "fenced: non-successor epoch"
        );
        Ok(Some(self.state.advance(&self.identity.cfg, cmd)?))
    }

    fn persist(&mut self, next: State) -> Result<()> {
        let previous = latch(&self.state.head)?;
        let io = (|| -> Result<()> {
            write_slot(&self.dir, "epoch.wal", &next, self.barriers)?;
            barrier(&self.dir, self.barriers, "wal")?;
            atomic(&self.dir, "checkpoint", &next)
        })();
        let (kernel, result) =
            previous.bind(latch_request(next.head.epoch, next.head.change, io.is_ok()));
        io.context("durable bind failed; exit and recover the WAL")?;
        ensure!(
            result == Ok(BeltLatchBindOutcome::Fresh) && kernel.next_epoch() == next.head.epoch + 1,
            "latch disagrees with durable successor"
        );
        self.state = next;
        barrier(&self.dir, self.barriers, "post")
    }
    fn answer(&mut self, req: Request) -> Result<Answer> {
        match req {
            Request::Bind(p) => {
                match self.prepare(&p) {
                    Err(e) => return Ok(Answer::Refused(e.to_string())),
                    Ok(None) => {}
                    Ok(Some(next)) => self.persist(next)?,
                }
                Ok(Answer::Vote(
                    self.state.head.clone(),
                    Vote {
                        signer: self.identity.signer,
                        signature: signature(&self.key, b"durable epoch", &self.state.head),
                    },
                ))
            }
            Request::Release {
                certificate,
                operator_signature,
            } => {
                let result = (|| -> Result<Answer> {
                    certificate.verify(&self.identity.cfg)?;
                    ensure!(certificate.head == self.state.head, "fenced release");
                    verify_sig(
                        self.state.head.operator_id,
                        b"release certified output",
                        &self.state.head,
                        &operator_signature,
                    )?;
                    let ranges = self
                        .state
                        .releasable
                        .clone()
                        .context("no inference grant")?;
                    let cell = self.state.cell();
                    let st = opening::statement(&self.state.blind, &cell, ranges)?;
                    ensure!(
                        st.cell_root == self.state.head.state_commitment,
                        "corrupt checkpoint"
                    );
                    let proof = opening::prove(&self.state.blind, &cell, &st)?;
                    Ok(Answer::Opening(st, proof))
                })();
                Ok(result.unwrap_or_else(|e| Answer::Refused(e.to_string())))
            }
        }
    }
}

pub fn serve(dir: &Path, barriers: bool) -> Result<()> {
    let lock = OpenOptions::new()
        .create(true)
        .truncate(false)
        .write(true)
        .open(dir.join("lock"))?;
    lock.try_lock_exclusive()
        .context("custodian directory already in use")?;
    let identity: Identity = load(dir, "identity")?;
    identity.cfg.validate()?;
    let key = SigningKey::from_bytes(&identity.secret);
    ensure!(
        identity.cfg.roster.get(usize::from(identity.signer))
            == Some(&key.verifying_key().to_bytes()),
        "identity mismatch"
    );
    let state: State = load(dir, "epoch.wal")?;
    ensure!(
        state.head.genesis_id == identity.cfg.genesis()
            && state.head.epoch < BELT_LATCH_MAX_CAPACITY_LIMIT
            && state.head.state_commitment == opening::root(&state.blind, &state.cell())
            && state.replay()? == state.weights,
        "corrupt WAL"
    );
    // Redo even when the previous process died between WAL and snapshot.
    atomic(dir, "checkpoint", &state)?;
    let socket = dir.join("socket");
    if socket.try_exists()? {
        fs::remove_file(&socket)?;
    }
    let listener = UnixListener::bind(socket)?;
    let mut node = Node {
        dir: dir.to_owned(),
        identity,
        state,
        key,
        barriers,
    };
    for stream in listener.incoming() {
        let mut stream = stream?;
        if timeouts(&stream).is_err() {
            continue;
        }
        if let Ok(req) = recv(&mut stream) {
            // A persistence error exits the process before any vote can
            // escape. A disconnected client can safely retry its command.
            let reply = node.answer(req)?;
            let _ = send(&mut stream, &reply);
        }
    }
    Ok(())
}

/// Private local operator storage. A restored copy carries credentials and
/// a cursor. Only the custodians can certify a successor to that cursor.
#[derive(Serialize, Deserialize)]
struct Seat {
    cfg: Config,
    sockets: Vec<PathBuf>,
    secret: Digest,
    genesis: Head,
}

pub fn provision_operator(
    dir: &Path,
    cfg: &Config,
    sockets: &[PathBuf],
    key: &SigningKey,
    genesis: &Head,
) -> Result<()> {
    cfg.validate()?;
    ensure!(
        genesis.epoch == 0 && genesis.genesis_id == cfg.genesis(),
        "wrong genesis"
    );
    fs::DirBuilder::new().mode(0o700).create(dir)?;
    atomic(
        dir,
        "seat",
        &Seat {
            cfg: cfg.clone(),
            sockets: sockets.to_vec(),
            secret: key.to_bytes(),
            genesis: genesis.clone(),
        },
    )?;
    atomic(dir, "cursor", &Option::<Certificate>::None)
}

#[derive(Serialize, Deserialize)]
pub enum Operation {
    Exercise(Grant),
    Offer(Grant),
    Accept(Proposal),
}

#[derive(Debug, Serialize, Deserialize)]
pub enum Outcome {
    Certified(Certificate),
    Offered(Proposal),
}

pub fn operate(dir: &Path, op: Operation) -> Result<Outcome> {
    let lock = OpenOptions::new()
        .create(true)
        .truncate(false)
        .write(true)
        .open(dir.join("lock"))?;
    lock.try_lock_exclusive()?;
    let seat: Seat = load(dir, "seat")?;
    let key = SigningKey::from_bytes(&seat.secret);
    let cursor: Option<Certificate> = load(dir, "cursor")?;
    let parent = cursor.as_ref().map(|c| &c.head).unwrap_or(&seat.genesis);
    let offer = matches!(op, Operation::Offer(_));
    let proposal = match op {
        Operation::Exercise(g) | Operation::Offer(g) => {
            ensure!(
                g.parent.operator_id == key.verifying_key().to_bytes(),
                "operator cursor or key mismatch"
            );
            ensure!(
                matches!(g.action, Action::Migrate { .. }) == offer,
                "migration needs successor acceptance"
            );
            verify_sig(
                seat.cfg.policy.issuer,
                b"exact capability",
                &(&g.parent, &g.action),
                &g.issuer_signature,
            )?;
            Proposal {
                command: Command::authorize(g, &key, None),
                parent_certificate: cursor.clone(),
            }
        }
        Operation::Accept(mut p) => {
            let g = &p.command.grant;
            ensure!(
                matches!(g.action,Action::Migrate{successor,..} if successor==key.verifying_key().to_bytes()),
                "wrong successor"
            );
            match &p.parent_certificate {
                Some(c) => {
                    c.verify(&seat.cfg)?;
                    ensure!(c.head == g.parent, "wrong manifest");
                }
                None => ensure!(g.parent == seat.genesis, "unsigned manifest"),
            }
            p.command.successor_signature = Some(signature(
                &key,
                b"accept signed move",
                &(g, &p.command.operator_signature),
            ));
            p.command.authenticate(&seat.cfg)?;
            p
        }
    };
    if let Some(c) = cursor
        .as_ref()
        .filter(|c| c.head.change == proposal.command.id())
    {
        c.verify(&seat.cfg)?;
        return Ok(Outcome::Certified(c.clone()));
    }
    if matches!(proposal.command.grant.action, Action::Migrate { .. }) && !offer {
        ensure!(
            proposal.command.grant.parent.epoch >= parent.epoch,
            "old handoff"
        );
    } else {
        ensure!(
            proposal.command.grant.parent == *parent,
            "stale operator cursor"
        );
    }
    if offer {
        return Ok(Outcome::Offered(proposal));
    }
    let cert = certify(&seat.cfg, &seat.sockets, &proposal)?;
    atomic(dir, "cursor", &Some(&cert))?;
    Ok(Outcome::Certified(cert))
}
