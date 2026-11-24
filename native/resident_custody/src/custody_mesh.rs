//! One durable vote per epoch. A transition needs a certified parent, a
//! policy issuer's exact-action grant, and the active operator's signature.
//!
//! Every custodian transition runs two latch kernels. Obend's proved `stepBeltLatch`
//! (`obend_latch_abi`) holds the installed head as genesis, epoch, `head_root` and policy and
//! decides whether a proposal extends it; the qsag kernel (`belt_latch_kernel`) decides
//! idempotent replay. Their outcomes must agree as `Node::prepare` and `Node::persist` state,
//! and a vote authenticates the Obend record with `persistAck = 1` in the mesh signature domain.
use crate::belt_latch_kernel::*;
use crate::cshake_selective_open as opening;
use crate::obend_latch_abi::{self as obend, NativeBeltLatch, RequestWords, StateWords, Status};
use crate::trie_opening::{Branch, Path as TriePath};
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

pub(crate) fn signature(sk: &SigningKey, domain: &[u8], t: &impl Serialize) -> Bytes {
    sk.sign(&hash(domain, t)).to_bytes().to_vec()
}

pub(crate) fn verify_sig(pk: Digest, domain: &[u8], t: &impl Serialize, sig: &[u8]) -> Result<()> {
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
    pub fn policy_hash(&self) -> Digest {
        hash(b"policy", &self.policy)
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

/// The digest an Obend latch installs for `head`, and the `parent_commitment` of its child.
pub fn head_root(head: &Head) -> Digest {
    hash(b"parent", head)
}

/// The 14 Obend latch words once `head` is installed.
pub fn latch_state(head: &Head) -> StateWords {
    obend::LatchState {
        initialized: 1,
        genesis: obend::limbs(&head.genesis_id),
        epoch: head.epoch,
        digest: obend::limbs(&head_root(head)),
        policy: obend::limbs(&head.policy_hash),
    }
    .to_words()
}

/// The Obend request that installs `head` over the head its `parent_commitment` names.
/// These 19 words are the payload authenticated by each vote for `head`.
pub fn succession_request(head: &Head, persist_ack: bool) -> Result<RequestWords> {
    Ok(obend::LatchRequest {
        genesis: obend::limbs(&head.genesis_id),
        parent_epoch: head
            .epoch
            .checked_sub(1)
            .context("the genesis head has no succession")?,
        next_epoch: head.epoch,
        parent: obend::limbs(&head.parent_commitment),
        next_digest: obend::limbs(&head_root(head)),
        policy: obend::limbs(&head.policy_hash),
        persist_ack: u64::from(persist_ack),
    }
    .to_words())
}

/// A request for a child of `parent` before the child exists. The kernel reads `nextDigest`
/// only to install it, so the probe refuses exactly where the child's own request will.
fn probe_request(parent: &Head) -> Result<RequestWords> {
    Ok(obend::LatchRequest {
        genesis: obend::limbs(&parent.genesis_id),
        parent_epoch: parent.epoch,
        next_epoch: parent.epoch.checked_add(1).context("epoch overflow")?,
        parent: obend::limbs(&head_root(parent)),
        next_digest: [0; 4],
        policy: obend::limbs(&parent.policy_hash),
        persist_ack: 1,
    }
    .to_words())
}

fn vote_message(head: &Head) -> Result<Bytes> {
    Ok(obend::request_bytes(&succession_request(head, true)?).to_vec())
}

/// Origin of a journaled Tulip episode, as the resident's event memory tags it.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum Provenance {
    Experienced,
    Told,
    Inferred,
}

/// The public part of the resident's journal cell, bytes `[0, HEADER_BYTES)`: 24 bytes of
/// [`resident_identity`], the journal cursor, and the journaled counts by provenance plus
/// forgotten episodes. Bytes `[HEADER_BYTES, 64)` hold the private Tulip journal chain.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct JournalHeader {
    pub cursor: u64,
    pub experienced: u32,
    pub told: u32,
    pub inferred: u32,
    pub forgotten: u32,
}

pub const HEADER_BYTES: u16 = 48;
// Fixed bincode fields (sibling, root, journal and proof length) plus the 64-byte
// cell circuit's worst-case proof. Pinned by worst_case_wire_budget.
pub(crate) const MAX_HEADER_WIRE: u64 = 96 + 86_832;
const IDENTITY_BYTES: usize = 24;

/// The resident identity a journal header carries: its genesis and its policy.
pub fn resident_identity(genesis_id: &Digest, policy_hash: &Digest) -> Digest {
    digest(b"resident header identity", &[genesis_id, policy_hash])
}

impl JournalHeader {
    pub fn public_bytes(&self, identity: &Digest) -> [u8; HEADER_BYTES as usize] {
        let mut out = [0; HEADER_BYTES as usize];
        out[..IDENTITY_BYTES].copy_from_slice(&identity[..IDENTITY_BYTES]);
        out[24..32].copy_from_slice(&self.cursor.to_le_bytes());
        for (i, n) in [self.experienced, self.told, self.inferred, self.forgotten]
            .into_iter()
            .enumerate()
        {
            out[32 + 4 * i..36 + 4 * i].copy_from_slice(&n.to_le_bytes());
        }
        out
    }
}

/// Leaf paths of the two-cell world trie under `Head::state_commitment`. The first path bit
/// orders the leaves and each leaf digest commits to its whole 65-byte path.
pub const W0_PATH: TriePath = [0; 65];
pub const JOURNAL_PATH: TriePath = {
    let mut p = [0; 65];
    p[0] = 0x80;
    p
};

fn leaf(path: &TriePath, cell_root: &Digest) -> Digest {
    Branch {
        path,
        siblings: &[],
    }
    .root(cell_root)
    .expect("canonical leaf path")
}

/// The journal header proved inside a certified world root. Its only sibling is the W0 leaf,
/// a commitment under a private blind, so the opening carries no witness.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct HeaderOpening {
    pub w0_leaf: Digest,
    pub cell_root: Digest,
    pub journal: JournalHeader,
    pub proof: Bytes,
}

impl HeaderOpening {
    /// The header of `head`: membership of the journal cell in its world root, the cSHAKE256
    /// projection of exactly `[0, HEADER_BYTES)`, its identity and its cursor.
    pub fn verify(&self, head: &Head) -> Result<JournalHeader> {
        let identity = resident_identity(&head.genesis_id, &head.policy_hash);
        let statement = opening::Statement {
            cell_root: self.cell_root,
            ranges: vec![(0, HEADER_BYTES)],
            projected_bytes: self.journal.public_bytes(&identity).to_vec(),
        };
        Branch {
            path: &JOURNAL_PATH,
            siblings: &[self.w0_leaf],
        }
        .verify(
            &head.state_commitment,
            CELL_BYTES,
            &[(0, HEADER_BYTES)],
            &statement,
            &self.proof,
        )?;
        ensure!(
            self.journal.cursor == head.journal_cursor,
            "journal cursor disagrees with the certified head"
        );
        Ok(self.journal)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum Action {
    Learn {
        episode: u64,
        provenance: Provenance,
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
    /// A Learn whose certified command also binds its outgoing reply. Appended to preserve
    /// the bincode tags and signatures of existing custody operations.
    LearnWithReply {
        episode: u64,
        provenance: Provenance,
        step: GdnStep,
        reply: Digest,
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
        let command = Self {
            grant,
            operator_signature,
            successor_signature: None,
        };
        match successor {
            Some(s) => command.accept(s),
            None => command,
        }
    }
    /// The successor's acceptance of an offered move.
    pub fn accept(mut self, successor: &SigningKey) -> Self {
        self.successor_signature = Some(signature(
            successor,
            b"accept signed move",
            &(&self.grant, &self.operator_signature),
        ));
        self
    }
    pub fn authenticate(&self, cfg: &Config) -> Result<()> {
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
    pub fn id(&self) -> Digest {
        hash(b"transition", self)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Vote {
    pub signer: u16,
    pub signature: Bytes,
}

impl Vote {
    /// Sign the mesh's domain-separated digest of the encoded request with `persistAck = 1`.
    /// The daemon calls this after durable acceptance or an exact WAL-backed replay.
    pub fn sign(key: &SigningKey, signer: u16, head: &Head) -> Result<Self> {
        Ok(Self {
            signer,
            signature: signature(key, b"durable epoch", &vote_message(head)?),
        })
    }
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
            self.head.genesis_id == cfg.genesis() && self.head.policy_hash == cfg.policy_hash(),
            "foreign manifest"
        );
        ensure!(
            self.votes.len() >= usize::from(cfg.threshold) && self.votes.len() <= cfg.roster.len(),
            "insufficient or excessive quorum"
        );
        let message = vote_message(&self.head)?;
        let mut seen = BTreeSet::new();
        for v in &self.votes {
            ensure!(seen.insert(v.signer), "duplicate signer");
            let pk = cfg
                .roster
                .get(usize::from(v.signer))
                .context("unknown signer")?;
            verify_sig(*pk, b"durable epoch", &message, &v.signature)?;
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
    journal: JournalHeader,
    // Hash chain over every journal entry, in order. Its first 16 bytes are the private
    // part of the journal cell.
    chain: Digest,
    journal_blind: Digest,
    releasable: Option<Vec<(u16, u16)>>,
}

impl State {
    fn genesis(cfg: &Config, secret: Digest) -> Self {
        let genesis_id = cfg.genesis();
        let head = Head {
            genesis_id,
            epoch: 0,
            state_commitment: [0; 32],
            policy_hash: cfg.policy_hash(),
            journal_cursor: 0,
            seat_payment_claim: [0; 32],
            operator_id: cfg.first_operator,
            parent_commitment: [0; 32],
            change: [0; 32],
            output_bits: 0,
            output_rank: 0,
        };
        let mut s = Self {
            head,
            history: vec![],
            weights: [0; 8],
            observed: [0; 8],
            blinding_key: secret,
            blind: digest(b"genesis blind", &[&secret, &genesis_id]),
            journal: JournalHeader::default(),
            chain: digest(b"tulip journal", &[&genesis_id]),
            journal_blind: digest(b"genesis journal blind", &[&secret, &genesis_id]),
            releasable: None,
        };
        s.head.state_commitment = s.world_root();
        s
    }
    fn cell(&self) -> Vec<u8> {
        self.weights.iter().flat_map(|w| w.to_le_bytes()).collect()
    }
    fn journal_cell(&self) -> Vec<u8> {
        let identity = resident_identity(&self.head.genesis_id, &self.head.policy_hash);
        let mut cell = self.journal.public_bytes(&identity).to_vec();
        cell.extend_from_slice(&self.chain[..CELL_BYTES - usize::from(HEADER_BYTES)]);
        cell
    }
    fn w0_leaf(&self) -> Digest {
        leaf(&W0_PATH, &opening::root(&self.blind, &self.cell()))
    }
    fn journal_leaf(&self) -> Digest {
        leaf(
            &JOURNAL_PATH,
            &opening::root(&self.journal_blind, &self.journal_cell()),
        )
    }
    fn world_root(&self) -> Digest {
        Branch {
            path: &W0_PATH,
            siblings: &[self.journal_leaf()],
        }
        .root(&opening::root(&self.blind, &self.cell()))
        .expect("canonical leaf path")
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
            Action::Learn {
                episode,
                provenance,
                step,
            }
            | Action::LearnWithReply {
                episode,
                provenance,
                step,
                ..
            } => {
                step.validate()?;
                // Forgotten episodes stay in the history, so this also refuses resurrection.
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
                let count = match provenance {
                    Provenance::Experienced => &mut s.journal.experienced,
                    Provenance::Told => &mut s.journal.told,
                    Provenance::Inferred => &mut s.journal.inferred,
                };
                *count = count.checked_add(1).context("journal count overflow")?;
                let payload = match action {
                    Action::LearnWithReply { reply, .. } => {
                        bincode::serialize(&(provenance, step, reply))?
                    }
                    _ => bincode::serialize(&(provenance, step))?,
                };
                s.chain = digest(
                    b"tulip journal learn",
                    &[&s.chain, &episode.to_le_bytes(), &payload],
                );
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
                s.journal.forgotten = s
                    .journal
                    .forgotten
                    .checked_add(1)
                    .context("journal count overflow")?;
                s.chain = digest(b"tulip journal forget", &[&s.chain, &episode.to_le_bytes()]);
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
        if matches!(
            action,
            Action::Learn { .. } | Action::LearnWithReply { .. } | Action::Forget { .. }
        ) {
            ensure!(s.weights == s.replay()?, "W0 replay mismatch");
            s.head.journal_cursor += 1;
            s.journal.cursor = s.head.journal_cursor;
            s.blind = digest(b"cell blind", &[&s.blinding_key, &s.head.change]);
            s.journal_blind = digest(b"journal blind", &[&s.blinding_key, &s.head.change]);
            s.head.state_commitment = s.world_root();
            s.observed = [0; 8];
        }
        s.head.parent_commitment = head_root(&self.head);
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
    file.write_all(&bincode::serialize(value)?)?;
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

#[allow(clippy::large_enum_variant)] // one message per request
#[derive(Serialize, Deserialize)]
pub enum Request {
    Bind(Proposal),
    Release {
        certificate: Certificate,
        operator_signature: Bytes,
    },
    Header {
        certificate: Certificate,
        operator_signature: Bytes,
    },
}
#[derive(Serialize, Deserialize)]
pub enum Answer {
    Vote(Head, Vote),
    /// A W0 projection, the journal leaf it needs as sibling, and the proof.
    Opening(opening::Statement, Digest, Bytes),
    Header(HeaderOpening),
    Refused(String),
}

pub(crate) fn recv<T: DeserializeOwned>(stream: &mut UnixStream) -> Result<T> {
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
pub(crate) fn send(stream: &mut UnixStream, t: &impl Serialize) -> Result<()> {
    let buf = bincode::serialize(t)?;
    ensure!(buf.len() <= FRAME, "frame too large");
    stream.write_all(&(buf.len() as u32).to_be_bytes())?;
    stream.write_all(&buf)?;
    Ok(())
}
pub(crate) fn timeouts(s: &UnixStream) -> Result<()> {
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
    // Custodians are asked in roster order. Racing proposals for one epoch then meet first at
    // custodian 0, and a proposer stalled there has bound no other custodian.
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
                            && head.parent_commitment == head_root(&proposal.command.grant.parent),
                        "unexpected vote"
                    );
                    let pk = cfg
                        .roster
                        .get(usize::from(v.signer))
                        .context("unknown signer")?;
                    verify_sig(*pk, b"durable epoch", &vote_message(&head)?, &v.signature)?;
                    let group = groups.entry(head_root(&head)).or_insert(Certificate {
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
    if let Answer::Opening(st, journal_leaf, proof) = rpc(socket, &req)? {
        Branch {
            path: &W0_PATH,
            siblings: &[journal_leaf],
        }
        .verify(&cert.head.state_commitment, CELL_BYTES, ranges, &st, &proof)?;
        Ok((st, proof))
    } else {
        bail!("expected projection")
    }
}

/// Ask one custodian for the journal header of the certified head. Only that head's operator
/// may ask; the header is public, so this releases nothing the exposure policy meters.
pub fn open_header(
    socket: &Path,
    cfg: &Config,
    cert: &Certificate,
    operator: &SigningKey,
) -> Result<(HeaderOpening, JournalHeader)> {
    cert.verify(cfg)?;
    let opened = request_header(
        socket,
        cert,
        signature(operator, b"release resident header", &cert.head),
    )?;
    let header = opened.verify(&cert.head)?;
    Ok((opened, header))
}

fn request_header(
    socket: &Path,
    cert: &Certificate,
    operator_signature: Bytes,
) -> Result<HeaderOpening> {
    let req = Request::Header {
        certificate: cert.clone(),
        operator_signature,
    };
    match rpc(socket, &req)? {
        Answer::Header(opened) => Ok(opened),
        _ => bail!("expected header opening"),
    }
}

// Block only when the local test controller has armed this exact boundary.
// SIGKILL is delivered externally by the owner of the Child handle.
pub(crate) fn barrier(dir: &Path, enabled: bool, phase: &str) -> Result<()> {
    if enabled && dir.join(format!("arm-{phase}")).try_exists()? {
        fs::write(dir.join(format!("at-{phase}")), [])?;
        while dir.join(format!("arm-{phase}")).try_exists()? {
            std::thread::sleep(Duration::from_millis(5));
        }
    }
    Ok(())
}

fn qsag_request(epoch: u64, id: Digest, persist_ok: bool) -> BeltLatchBindRequest {
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

fn qsag_latch(head: &Head) -> Result<BeltLatchKernel> {
    let r = qsag_request(head.epoch, head.change, true);
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
    /// The Obend latch buffer for `state.head`, provisioned from the WAL at start.
    latch: StateWords,
    native: Option<NativeBeltLatch>,
    steps: File,
    key: SigningKey,
    barriers: bool,
    /// The checkpoint trails the WAL until the vote has been sent.
    stale_checkpoint: bool,
}

impl Node {
    /// One Obend `stepBeltLatch` over `words`, also run by the native kernel when one is
    /// configured. Every step is logged as `status ack native`.
    fn obend(&self, words: &mut StateWords, request: &RequestWords) -> Result<Status> {
        let code = match &self.native {
            Some(native) => native.differential(words, request)?,
            None => obend::step_words(words, request),
        };
        writeln!(
            &self.steps,
            "{code} {} {}",
            request[obend::request::PERSIST_ACK],
            u8::from(self.native.is_some())
        )?;
        Status::from_code(code).context("unknown Obend status")
    }

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
        // Obend decides whether `parent` is the installed head. No bytes were written yet.
        let mut probe = self.latch;
        let status = self.obend(&mut probe, &probe_request(parent)?)?;
        let epoch = parent.epoch + 1;
        match status {
            Status::Accepted => {
                // Accepted means `parent` hashes to the installed head, the qsag fresh case.
                ensure!(
                    epoch == self.state.head.epoch + 1 && epoch < BELT_LATCH_MAX_CAPACITY_LIMIT,
                    "latch disagreement: Obend accepted a non-successor epoch"
                );
                Ok(Some(self.state.advance(&self.identity.cfg, cmd)?))
            }
            Status::StaleParent if epoch <= self.state.head.epoch => {
                // A consumed parent. Only the exact installed transition is replayed; the
                // qsag kernel resolves it before consulting persistence.
                let (_, result) =
                    qsag_latch(&self.state.head)?.bind(qsag_request(epoch, cmd.id(), false));
                ensure!(
                    result == Ok(BeltLatchBindOutcome::Replay),
                    "fenced: Obend {status:?}, qsag {result:?}"
                );
                ensure!(
                    self.state.head.parent_commitment == head_root(parent),
                    "latch disagreement: replayed change over another parent"
                );
                Ok(None)
            }
            refused => bail!("fenced: Obend {refused:?} (code {})", refused.code()),
        }
    }

    fn persist(&mut self, next: State) -> Result<()> {
        let previous = qsag_latch(&self.state.head)?;
        // persistAck is exactly the durability of the WAL record, which recovery reads.
        let io = (|| -> Result<()> {
            if self.barriers && self.dir.join("fail-wal").try_exists()? {
                bail!("injected WAL failure");
            }
            write_slot(&self.dir, "epoch.wal", &next, self.barriers)?;
            barrier(&self.dir, self.barriers, "wal")
        })();
        let ack = io.is_ok();
        let (kernel, qsag) = previous.bind(qsag_request(next.head.epoch, next.head.change, ack));
        let mut words = self.latch;
        let status = self.obend(&mut words, &succession_request(&next.head, ack)?)?;
        // The two kernels must tell the same story: a fresh qsag binding is an accepted
        // succession, a failed persist poisons qsag and is Obend's missing acknowledgment.
        match (status, qsag) {
            (Status::Accepted, Ok(BeltLatchBindOutcome::Fresh)) => {}
            (Status::MissingAck, Err(BeltLatchKernelError::WalPersistFailed)) => {
                ensure!(words == self.latch, "Obend refusal changed the latch");
                return io
                    .context("durable bind failed, Obend MissingAck; exit and recover the WAL");
            }
            other => bail!("latch disagreement on a durable successor: {other:?}"),
        }
        ensure!(
            words == latch_state(&next.head) && kernel.next_epoch() == next.head.epoch + 1,
            "latch disagrees with durable successor"
        );
        self.latch = words;
        self.state = next;
        self.stale_checkpoint = true;
        Ok(())
    }
    /// The checkpoint is a copy of the WAL that recovery never reads, so it is written after
    /// the vote is on its way, off the acknowledgment path.
    fn checkpoint(&mut self) -> Result<()> {
        if std::mem::take(&mut self.stale_checkpoint) {
            // This diagnostic copy is replaceable. Recovery unconditionally rebuilds
            // it from the fsynced WAL before listening, including after power loss.
            let tmp = self.dir.join("checkpoint.new");
            fs::write(&tmp, bincode::serialize(&self.state)?)?;
            fs::rename(tmp, self.dir.join("checkpoint"))?;
            barrier(&self.dir, self.barriers, "post")?;
        }
        Ok(())
    }
    fn bind(&mut self, p: Proposal) -> Result<Answer> {
        match self.prepare(&p) {
            Err(e) => return Ok(Answer::Refused(e.to_string())),
            Ok(None) => {}
            Ok(Some(next)) => self.persist(next)?,
        }
        Ok(Answer::Vote(
            self.state.head.clone(),
            Vote::sign(&self.key, self.identity.signer, &self.state.head)?,
        ))
    }

    fn release(&self, certificate: Certificate, operator_signature: Bytes) -> Result<Answer> {
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
        let journal_leaf = self.state.journal_leaf();
        // The branch binding refuses a checkpoint whose cells miss the root.
        let proof = Branch {
            path: &W0_PATH,
            siblings: &[journal_leaf],
        }
        .prove(
            &self.state.head.state_commitment,
            &self.state.blind,
            &cell,
            &st,
        )?;
        Ok(Answer::Opening(st, journal_leaf, proof))
    }

    fn header_job(
        &self,
        certificate: Certificate,
        operator_signature: Bytes,
    ) -> Result<impl FnOnce() -> Result<Answer> + Send + 'static> {
        certificate.verify(&self.identity.cfg)?;
        ensure!(certificate.head == self.state.head, "fenced header");
        verify_sig(
            self.state.head.operator_id,
            b"release resident header",
            &self.state.head,
            &operator_signature,
        )?;
        // Authorization and the snapshot are taken together in the serialized server loop.
        // The worker owns only the witness for this public header.
        let cell = self.state.journal_cell();
        let journal = self.state.journal;
        let blind = self.state.journal_blind;
        let world = self.state.head.state_commitment;
        let w0_leaf = self.state.w0_leaf();
        Ok(move || {
            let st = opening::statement(&blind, &cell, vec![(0, HEADER_BYTES)])?;
            let branch = Branch {
                path: &JOURNAL_PATH,
                siblings: &[w0_leaf],
            };
            let proof = branch.prove(&world, &blind, &cell, &st)?;
            Ok(Answer::Header(HeaderOpening {
                w0_leaf,
                cell_root: st.cell_root,
                journal,
                proof,
            }))
        })
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
            && state.head.state_commitment == state.world_root()
            && state.journal.cursor == state.head.journal_cursor
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
        latch: latch_state(&state.head),
        state,
        native: NativeBeltLatch::from_env(dir.join("obend-record")),
        steps: OpenOptions::new()
            .create(true)
            .append(true)
            .open(dir.join("obend-steps.log"))?,
        key,
        barriers,
        stale_checkpoint: false,
    };
    let mut worker: Option<std::thread::JoinHandle<()>> = None;
    for stream in listener.incoming() {
        let mut stream = stream?;
        if timeouts(&stream).is_err() {
            continue;
        }
        if let Ok(req) = recv(&mut stream) {
            // A WAL error exits the process before any vote can escape. A
            // disconnected client can safely retry its command.
            let refused = |e: anyhow::Error| Answer::Refused(e.to_string());
            let reply = match req {
                Request::Bind(p) => node.bind(p)?,
                Request::Release {
                    certificate,
                    operator_signature,
                } => node
                    .release(certificate, operator_signature)
                    .unwrap_or_else(refused),
                Request::Header {
                    certificate,
                    operator_signature,
                } => match node.header_job(certificate, operator_signature) {
                    Err(e) => refused(e),
                    Ok(_) if worker.as_ref().is_some_and(|w| !w.is_finished()) => {
                        Answer::Refused("header prover busy".into())
                    }
                    Ok(job) => {
                        worker = Some(
                            std::thread::Builder::new()
                                .name("journal-proof".into())
                                .spawn(move || {
                                    let _ = send(&mut stream, &job().unwrap_or_else(refused));
                                })?,
                        );
                        continue;
                    }
                },
            };
            let _ = send(&mut stream, &reply);
            drop(stream);
            // A checkpoint error also exits; recovery rewrites it from the WAL.
            node.checkpoint()?;
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

/// An operator seat as read from disk: its resident, key and last certified head.
pub(crate) struct SeatView {
    pub(crate) cfg: Config,
    pub(crate) key: SigningKey,
    pub(crate) genesis: Head,
    pub(crate) cursor: Option<Certificate>,
}

impl SeatView {
    pub(crate) fn open(dir: &Path) -> Result<Self> {
        let seat: Seat = load(dir, "seat")?;
        Ok(Self {
            key: SigningKey::from_bytes(&seat.secret),
            cfg: seat.cfg,
            genesis: seat.genesis,
            cursor: load(dir, "cursor")?,
        })
    }
    pub(crate) fn head(&self) -> &Head {
        self.cursor.as_ref().map_or(&self.genesis, |c| &c.head)
    }
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

#[allow(clippy::large_enum_variant)] // one message per request
#[derive(Serialize, Deserialize)]
pub enum Operation {
    Exercise(Grant),
    Offer(Grant),
    Accept(Proposal),
}

#[allow(clippy::large_enum_variant)] // one message per request
#[derive(Debug, Serialize, Deserialize)]
pub enum Outcome {
    Certified(Certificate),
    Offered(Proposal),
}

pub fn operate(dir: &Path, op: Operation) -> Result<Outcome> {
    operate_with(dir, op, |_| Ok(()))
}

/// [`operate`], running `after_quorum` once the custodians certified a fresh successor and
/// before this seat records it. A crash there leaves the quorum ahead of the seat; the same
/// signed command recovers the certificate by exact replay.
pub(crate) fn operate_with(
    dir: &Path,
    op: Operation,
    after_quorum: impl FnOnce(&Certificate) -> Result<()>,
) -> Result<Outcome> {
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
            p.command = p.command.accept(&key);
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
    after_quorum(&cert)?;
    atomic(dir, "cursor", &Some(&cert))?;
    Ok(Outcome::Certified(cert))
}

/// A's paid offer authorizes fetching the public header from the parent while B acquires
/// the quorum. A move preserves the world root, so B can verify that proof against its successor.
#[derive(Clone, Serialize, Deserialize)]
pub struct PaidMoveOffer {
    pub proposal: Proposal,
    pub seat_receipt: Vec<u8>,
    header_signature: Bytes,
}

pub fn offer_paid_move(dir: &Path, grant: Grant, seat_receipt: Vec<u8>) -> Result<PaidMoveOffer> {
    let seat: Seat = load(dir, "seat")?;
    let key = SigningKey::from_bytes(&seat.secret);
    let header_signature = signature(&key, b"release resident header", &grant.parent);
    let Outcome::Offered(proposal) = operate(dir, Operation::Offer(grant))? else {
        bail!("expected migration offer");
    };
    Ok(PaidMoveOffer {
        proposal,
        seat_receipt,
        header_signature,
    })
}

pub fn accept_paid_move(
    dir: &Path,
    offer: PaidMoveOffer,
    admission: &crate::house_move::SeatAdmission,
) -> Result<crate::house_move::ResidentMigrationPackage> {
    let seat: Seat = load(dir, "seat")?;
    let key = SigningKey::from_bytes(&seat.secret);
    let proposal = offer.proposal;
    let command = proposal.command.clone().accept(&key);
    command.authenticate(&seat.cfg)?;
    let Action::Migrate {
        successor,
        seat_payment_claim,
    } = command.grant.action
    else {
        bail!("expected Migrate");
    };
    admission.verify_for(
        &offer.seat_receipt,
        &command.grant.parent,
        successor,
        seat_payment_claim,
    )?;
    let parent = proposal
        .parent_certificate
        .clone()
        .unwrap_or_else(|| Certificate {
            head: seat.genesis.clone(),
            votes: vec![],
        });
    crate::house_move::check_package_capacity(
        &parent,
        &command,
        &offer.seat_receipt,
        seat.cfg.roster.len(),
    )?;
    let socket = seat.sockets.last().context("empty custodian roster")?;
    let (successor, opening) = std::thread::scope(|scope| -> Result<_> {
        let opening = proposal.parent_certificate.as_ref().map(|_| {
            scope.spawn(|| -> Result<_> {
                let proof = request_header(socket, &parent, offer.header_signature)?;
                proof.verify(&parent.head)?;
                Ok(proof)
            })
        });
        let Outcome::Certified(cert) = operate(dir, Operation::Accept(proposal))? else {
            bail!("expected succession certificate");
        };
        Ok((cert, opening.and_then(|t| t.join().ok()?.ok())))
    })?;
    // The prover transcript and header projection depend on these four head fields.
    // The parent opening was verified while the operator was collecting votes.
    ensure!(
        successor.head.genesis_id == parent.head.genesis_id
            && successor.head.policy_hash == parent.head.policy_hash
            && successor.head.state_commitment == parent.head.state_commitment
            && successor.head.journal_cursor == parent.head.journal_cursor,
        "migration changed memory"
    );
    let header = match opening {
        Some(header) => header,
        // An exact retry can arrive after the parent was consumed. The successor now
        // authorizes the same opening. Also use this route for a move from genesis.
        _ => {
            seat.sockets
                .iter()
                .find_map(|s| open_header(s, &seat.cfg, &successor, &key).ok())
                .context("no custodian served the certified successor header")?
                .0
        }
    };
    Ok(crate::house_move::ResidentMigrationPackage {
        parent,
        command,
        succession: successor,
        header,
        seat_receipt: offer.seat_receipt,
    })
}
