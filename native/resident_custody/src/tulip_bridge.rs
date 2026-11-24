//! Tulip delivery for a custodied resident across operator crashes and paid house moves.
//!
//! Every inbound town frame gets one reply envelope, a pure function of the resident and the
//! frame. The operator stages the envelope with its exact signed Learn in a write-ahead
//! outbox before proposing it. The custodian quorum certifies a Learn that names the
//! envelope's digest, and the broker accepts a post only with that certificate and a seat
//! signature. It keys every post by cSHAKE256 under [`OUTBOX_DOMAIN`] of the genesis, the
//! episode and the reply slot, returns the original receipt for a repeated key, refuses a
//! different body under it, and refuses a seat older than the newest it has seen.
//!
//! On a move, the source signs a [`Handoff`] of its certified, undelivered replies. The
//! successor checks each against its certificate and the handoff's delivered prefix against
//! the broker, then delivers what remains. A crash at any point leaves either a staged Learn,
//! which the same signed command certifies by exact replay, or a certified reply, which the
//! broker deduplicates.
use crate::custody_mesh::{
    barrier, head_root, operate_with, recv, send, signature, timeouts, verify_sig, Action,
    Certificate, Command, Config, GdnStep, Grant, Head, Operation, Outcome, Provenance, SeatView,
};
use crate::{digest, Digest};
use anyhow::{bail, ensure, Context, Result};
use ed25519_dalek::SigningKey;
use fs2::FileExt;
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use sha3::digest::{ExtendableOutput, Update, XofReader};
use sha3::{CShake256, CShake256Core};
use std::collections::BTreeMap;
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::Path;

/// cSHAKE256 customization of outbox idempotency keys.
pub const OUTBOX_DOMAIN: &[u8] = b"tulip.resident.outbox.v1";
/// An episode has exactly one reply.
const REPLY_SLOT: u32 = 0;
const RECORD_LIMIT: usize = 4 << 20;

/// One inbound message of the town stream.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Frame {
    pub seq: u64,
    pub message_id: u64,
    pub sender: String,
    pub content: String,
}

/// The resident's reply to one frame. Tulip message IDs are episode IDs.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Envelope {
    pub genesis: Digest,
    pub episode: u64,
    /// Sequence number of the frame answered.
    pub in_reply_to: u64,
    pub body: String,
}

pub fn idempotency_key(genesis: &Digest, episode: u64) -> Digest {
    let mut h = CShake256::from_core(CShake256Core::new(OUTBOX_DOMAIN));
    h.update(genesis);
    h.update(&episode.to_le_bytes());
    h.update(&REPLY_SLOT.to_le_bytes());
    let mut out = [0; 32];
    XofReader::read(&mut h.finalize_xof(), &mut out);
    out
}

impl Envelope {
    /// The deterministic reply to `frame`.
    pub fn reply(genesis: &Digest, frame: &Frame) -> Self {
        let heard = digest(b"tulip inbound content", &[frame.content.as_bytes()]);
        Self {
            genesis: *genesis,
            episode: frame.message_id,
            in_reply_to: frame.seq,
            body: format!(
                "re #{} from {}: heard {}",
                frame.message_id,
                frame.sender,
                hex::encode(&heard[..8])
            ),
        }
    }
    pub fn digest(&self) -> Digest {
        digest(
            b"tulip outbound reply",
            &[&bincode::serialize(self).expect("serializable envelope")],
        )
    }
    pub fn key(&self) -> Digest {
        idempotency_key(&self.genesis, self.episode)
    }
}

/// The fast-weight step a frame teaches: a unit key on one of the eight coordinates.
pub fn step_for(frame: &Frame) -> GdnStep {
    let h = digest(b"tulip inbound step", &[frame.content.as_bytes()]);
    let mut key = [0; 8];
    key[(frame.message_id % 8) as usize] = 1;
    GdnStep {
        key,
        value: u64::from_le_bytes(h[..8].try_into().unwrap()) >> 4,
        gamma: 3,
        beta: 1,
    }
}

/// The Learn that answers `frame` with `reply`.
pub fn learn(frame: &Frame, reply: &Envelope) -> Action {
    Action::LearnWithReply {
        episode: frame.message_id,
        provenance: Provenance::Told,
        step: step_for(frame),
        reply: reply.digest(),
    }
}

/// The broker's acknowledgment of one accepted post.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Receipt {
    pub post: u64,
    pub key: Digest,
    pub episode: u64,
    pub reply: Digest,
}

/// A reply with the quorum certificate of the Learn that committed to it.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CertifiedReply {
    pub envelope: Envelope,
    pub command: Command,
    pub certificate: Certificate,
}

impl CertifiedReply {
    pub fn verify(&self, cfg: &Config) -> Result<()> {
        self.certificate.verify(cfg)?;
        ensure!(
            self.certificate.head.change == self.command.id(),
            "certificate is not for this command"
        );
        self.command.authenticate(cfg)?;
        match &self.command.grant.action {
            Action::LearnWithReply { episode, reply, .. } if *episode == self.envelope.episode => {
                ensure!(
                    *reply == self.envelope.digest(),
                    "reply does not match the certified Learn"
                )
            }
            _ => bail!("not the certified Learn of this episode"),
        }
        ensure!(
            self.envelope.genesis == cfg.genesis(),
            "reply of another resident"
        );
        Ok(())
    }
}

/// A certified reply delivered under the poster's current seat.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Post {
    pub reply: CertifiedReply,
    /// The poster's newest certified head.
    pub seat: Certificate,
    pub signature: Vec<u8>,
}

impl Post {
    pub fn sign(reply: CertifiedReply, seat: Certificate, key: &SigningKey) -> Self {
        let signature = signature(
            key,
            b"tulip outbound post",
            &(reply.envelope.key(), &seat.head),
        );
        Self {
            reply,
            seat,
            signature,
        }
    }
    fn check(&self, cfg: &Config) -> Result<Digest> {
        self.reply.verify(cfg)?;
        self.seat.verify(cfg)?;
        ensure!(
            self.seat.head.epoch >= self.reply.certificate.head.epoch,
            "seat is older than its reply"
        );
        let key = self.reply.envelope.key();
        verify_sig(
            self.seat.head.operator_id,
            b"tulip outbound post",
            &(key, &self.seat.head),
            &self.signature,
        )?;
        Ok(key)
    }
}

/// An append-only file of length-prefixed, BLAKE3-checked records, fsynced per append. A torn
/// tail is cut on open.
struct Log(File);

impl Log {
    fn open<T: DeserializeOwned>(path: &Path) -> Result<(Self, Vec<T>)> {
        let fresh = !path.try_exists()?;
        let mut file = OpenOptions::new()
            .create(true)
            .read(true)
            .append(true)
            .open(path)?;
        if fresh {
            File::open(path.parent().context("log directory")?)?.sync_all()?;
        }
        let mut bytes = vec![];
        file.read_to_end(&mut bytes)?;
        let mut records = vec![];
        let mut at = 0;
        while let Some((record, n)) = Self::parse(&bytes[at..])? {
            records.push(record);
            at += n;
        }
        if at < bytes.len() {
            file.set_len(at as u64)?;
            file.sync_all()?;
        }
        Ok((Self(file), records))
    }
    fn parse<T: DeserializeOwned>(bytes: &[u8]) -> Result<Option<(T, usize)>> {
        let Some(length) = bytes.get(..4) else {
            return Ok(None);
        };
        let n = u32::from_le_bytes(length.try_into()?) as usize;
        ensure!(n <= RECORD_LIMIT, "invalid WAL record length");
        let Some(body) = bytes.get(36..36 + n) else {
            return Ok(None);
        };
        ensure!(
            blake3::hash(body).as_bytes() == &bytes[4..36],
            "WAL checksum mismatch"
        );
        Ok(Some((bincode::deserialize(body)?, 36 + n)))
    }
    fn append(&mut self, record: &impl Serialize) -> Result<()> {
        let body = bincode::serialize(record)?;
        ensure!(body.len() <= RECORD_LIMIT, "record too large");
        let mut bytes = (body.len() as u32).to_le_bytes().to_vec();
        bytes.extend(blake3::hash(&body).as_bytes());
        bytes.extend(body);
        self.0.write_all(&bytes)?;
        self.0.sync_all()?;
        Ok(())
    }
}

fn lock(path: &Path) -> Result<File> {
    let f = OpenOptions::new()
        .create(true)
        .truncate(false)
        .write(true)
        .open(path)?;
    f.try_lock_exclusive()
        .with_context(|| format!("{} in use", path.display()))?;
    Ok(f)
}

fn call<Q: Serialize, A: DeserializeOwned>(socket: &Path, req: &Q) -> Result<A> {
    let mut s = UnixStream::connect(socket).with_context(|| socket.display().to_string())?;
    timeouts(&s)?;
    send(&mut s, req)?;
    recv(&mut s)
}

fn listen(socket: &Path) -> Result<UnixListener> {
    if socket.try_exists()? {
        fs::remove_file(socket)?;
    }
    Ok(UnixListener::bind(socket)?)
}

#[derive(Serialize, Deserialize)]
enum BrokerRecord {
    Inbound(Frame),
    Accepted {
        receipt: Receipt,
        envelope: Envelope,
        seat: u64,
    },
    /// The seat fence advanced without a new post.
    Seat(u64),
}

#[derive(Serialize, Deserialize)]
pub enum BrokerRequest {
    Publish {
        message_id: u64,
        sender: String,
        content: String,
    },
    Read {
        after: u64,
    },
    Post(Box<Post>),
    Fence(Box<Certificate>),
    Lookup {
        key: Digest,
    },
    Posts,
}

#[derive(Serialize, Deserialize)]
pub enum BrokerAnswer {
    Fenced,
    Frame(Frame),
    Frames(Vec<Frame>),
    Receipt { receipt: Receipt, replayed: bool },
    Found(Option<Receipt>),
    Posts(Vec<(Receipt, Envelope)>),
    Refused(String),
}

/// The town stream and outbound posts of one resident, in one durable log.
struct Broker {
    cfg: Config,
    log: Log,
    frames: Vec<Frame>,
    posts: Vec<(Receipt, Envelope)>,
    by_key: BTreeMap<Digest, usize>,
    fence: u64,
}

impl Broker {
    fn apply(&mut self, r: BrokerRecord) {
        match r {
            BrokerRecord::Inbound(f) => self.frames.push(f),
            BrokerRecord::Accepted {
                receipt,
                envelope,
                seat,
            } => {
                self.by_key.insert(receipt.key, self.posts.len());
                self.posts.push((receipt, envelope));
                self.fence = self.fence.max(seat);
            }
            BrokerRecord::Seat(epoch) => self.fence = self.fence.max(epoch),
        }
    }
    fn commit(&mut self, r: BrokerRecord) -> Result<()> {
        self.log.append(&r)?;
        self.apply(r);
        Ok(())
    }
    fn post(&mut self, post: &Post) -> Result<BrokerAnswer> {
        let key = match post.check(&self.cfg) {
            Ok(k) => k,
            Err(e) => return Ok(BrokerAnswer::Refused(format!("unauthenticated reply: {e}"))),
        };
        let env = &post.reply.envelope;
        if !self
            .frames
            .iter()
            .any(|f| f.message_id == env.episode && f.seq == env.in_reply_to)
        {
            return Ok(BrokerAnswer::Refused("reply to an unknown message".into()));
        }
        let epoch = post.seat.head.epoch;
        if epoch < self.fence {
            return Ok(BrokerAnswer::Refused(format!(
                "fenced: stale seat at epoch {epoch}, broker has seen epoch {}",
                self.fence
            )));
        }
        if let Some(&i) = self.by_key.get(&key) {
            let (receipt, envelope) = self.posts[i].clone();
            if envelope != *env {
                return Ok(BrokerAnswer::Refused(
                    "a different reply holds this idempotency key".into(),
                ));
            }
            if epoch > self.fence {
                self.commit(BrokerRecord::Seat(epoch))?;
            }
            return Ok(BrokerAnswer::Receipt {
                receipt,
                replayed: true,
            });
        }
        let receipt = Receipt {
            post: self.posts.len() as u64 + 1,
            key,
            episode: env.episode,
            reply: env.digest(),
        };
        self.commit(BrokerRecord::Accepted {
            receipt: receipt.clone(),
            envelope: env.clone(),
            seat: epoch,
        })?;
        Ok(BrokerAnswer::Receipt {
            receipt,
            replayed: false,
        })
    }
    fn handle(&mut self, req: BrokerRequest) -> Result<BrokerAnswer> {
        Ok(match req {
            BrokerRequest::Publish {
                message_id,
                sender,
                content,
            } => {
                if self.frames.iter().any(|f| f.message_id == message_id) {
                    return Ok(BrokerAnswer::Refused("duplicate message id".into()));
                }
                let frame = Frame {
                    seq: self.frames.len() as u64 + 1,
                    message_id,
                    sender,
                    content,
                };
                let record = BrokerRecord::Inbound(frame.clone());
                if bincode::serialized_size(&record)? > RECORD_LIMIT as u64 {
                    return Ok(BrokerAnswer::Refused("inbound frame too large".into()));
                }
                self.commit(record)?;
                BrokerAnswer::Frame(frame)
            }
            BrokerRequest::Read { after } => {
                let start = usize::try_from(after).unwrap_or(usize::MAX);
                let mut page = vec![];
                let mut bytes = 0;
                for f in self.frames.get(start..).unwrap_or_default() {
                    let size = bincode::serialized_size(f)? as usize;
                    if bytes + size > RECORD_LIMIT {
                        break;
                    }
                    page.push(f.clone());
                    bytes += size;
                }
                BrokerAnswer::Frames(page)
            }
            BrokerRequest::Fence(seat) => {
                if let Err(err) = seat.verify(&self.cfg) {
                    return Ok(BrokerAnswer::Refused(err.to_string()));
                }
                if seat.head.epoch < self.fence {
                    return Ok(BrokerAnswer::Refused("stale seat fence".into()));
                }
                if seat.head.epoch > self.fence {
                    self.commit(BrokerRecord::Seat(seat.head.epoch))?;
                }
                BrokerAnswer::Fenced
            }
            BrokerRequest::Post(post) => self.post(&post)?,
            BrokerRequest::Lookup { key } => {
                BrokerAnswer::Found(self.by_key.get(&key).map(|&i| self.posts[i].0.clone()))
            }
            BrokerRequest::Posts => BrokerAnswer::Posts(self.posts.clone()),
        })
    }
}

/// Serve the broker in `dir`, which holds the resident's `config`. Requests are serialized
/// and every state change is durable before its answer is sent.
pub fn serve_broker(dir: &Path) -> Result<()> {
    let _lock = lock(&dir.join("lock"))?;
    let cfg: Config = bincode::deserialize(&fs::read(dir.join("config"))?)?;
    cfg.validate()?;
    let (log, records) = Log::open(&dir.join("broker.log"))?;
    let mut broker = Broker {
        cfg,
        log,
        frames: vec![],
        posts: vec![],
        by_key: BTreeMap::new(),
        fence: 0,
    };
    for r in records {
        broker.apply(r);
    }
    let listener = listen(&dir.join("socket"))?;
    for stream in listener.incoming() {
        let mut stream = stream?;
        if timeouts(&stream).is_err() {
            continue;
        }
        if let Ok(req) = recv(&mut stream) {
            // A failed append exits before any answer escapes.
            let answer = broker.handle(req)?;
            let _ = send(&mut stream, &answer);
        }
    }
    Ok(())
}

/// A client of a broker socket.
pub struct BrokerClient<'a>(pub &'a Path);

impl BrokerClient<'_> {
    fn call(&self, req: BrokerRequest) -> Result<BrokerAnswer> {
        match call(self.0, &req)? {
            BrokerAnswer::Refused(why) => bail!("broker refused: {why}"),
            a => Ok(a),
        }
    }
    pub fn publish(&self, message_id: u64, sender: &str, content: &str) -> Result<Frame> {
        match self.call(BrokerRequest::Publish {
            message_id,
            sender: sender.into(),
            content: content.into(),
        })? {
            BrokerAnswer::Frame(f) => Ok(f),
            _ => bail!("unexpected broker answer"),
        }
    }
    pub fn read(&self, mut after: u64) -> Result<Vec<Frame>> {
        let mut frames = Vec::new();
        loop {
            let BrokerAnswer::Frames(page) = self.call(BrokerRequest::Read { after })? else {
                bail!("unexpected broker answer");
            };
            let Some(last) = page.last() else {
                return Ok(frames);
            };
            ensure!(last.seq > after, "stream page did not advance");
            after = last.seq;
            frames.extend(page);
        }
    }
    /// The receipt, and whether the broker already held it.
    pub fn post(&self, post: &Post) -> Result<(Receipt, bool)> {
        match self.call(BrokerRequest::Post(Box::new(post.clone())))? {
            BrokerAnswer::Receipt { receipt, replayed } => Ok((receipt, replayed)),
            _ => bail!("unexpected broker answer"),
        }
    }
    pub fn lookup(&self, key: Digest) -> Result<Option<Receipt>> {
        match self.call(BrokerRequest::Lookup { key })? {
            BrokerAnswer::Found(r) => Ok(r),
            _ => bail!("unexpected broker answer"),
        }
    }
    pub fn posts(&self) -> Result<Vec<(Receipt, Envelope)>> {
        match self.call(BrokerRequest::Posts)? {
            BrokerAnswer::Posts(p) => Ok(p),
            _ => bail!("unexpected broker answer"),
        }
    }
}

#[derive(Serialize, Deserialize)]
struct GrantRequest {
    parent: Head,
    action: Action,
}

#[derive(Serialize, Deserialize)]
enum GrantAnswer {
    Granted(Box<Grant>),
    Refused(String),
}

/// Serve exact Learn grants from the policy issuer's key. Other actions are refused here.
pub fn serve_issuer(
    listener: UnixListener,
    issuer: SigningKey,
    stop: &std::sync::atomic::AtomicBool,
) -> Result<()> {
    for stream in listener.incoming() {
        let mut stream = stream?;
        if stop.load(std::sync::atomic::Ordering::Acquire) {
            break;
        }
        if timeouts(&stream).is_err() {
            continue;
        }
        if let Ok(GrantRequest { parent, action }) = recv(&mut stream) {
            let answer = if matches!(action, Action::LearnWithReply { .. }) {
                GrantAnswer::Granted(Box::new(Grant::issue(&issuer, &parent, action)))
            } else {
                GrantAnswer::Refused("this issuer grants Learn only".into())
            };
            let _ = send(&mut stream, &answer);
        }
    }
    Ok(())
}

pub fn request_grant(socket: &Path, parent: &Head, action: Action) -> Result<Grant> {
    match call(
        socket,
        &GrantRequest {
            parent: parent.clone(),
            action,
        },
    )? {
        GrantAnswer::Granted(g) => Ok(*g),
        GrantAnswer::Refused(why) => bail!("issuer refused: {why}"),
    }
}

#[derive(Serialize, Deserialize)]
enum OutboxRecord {
    /// Written before the Learn is proposed.
    Staged {
        envelope: Envelope,
        command: Box<Command>,
    },
    Certified {
        episode: u64,
        certificate: Box<Certificate>,
    },
    Delivered {
        episode: u64,
        receipt: Receipt,
    },
    /// A predecessor's handoff, verified.
    Adopted {
        handoff: Digest,
        cursor: u64,
        pending: Vec<CertifiedReply>,
    },
}

struct Entry {
    envelope: Envelope,
    command: Command,
    certificate: Option<Certificate>,
    receipt: Option<Receipt>,
}

/// The operator's write-ahead outbox, `outbox.wal` beside its seat.
pub struct Outbox {
    log: Log,
    _lock: File,
    adopted: Option<Digest>,
    entries: BTreeMap<u64, Entry>,
    /// Every frame up to this sequence number has a delivered reply.
    cursor: u64,
}

impl Outbox {
    pub fn open(seat: &Path) -> Result<Self> {
        let _lock = lock(&seat.join("outbox.lock"))?;
        let (log, records) = Log::open(&seat.join("outbox.wal"))?;
        let mut o = Self {
            log,
            _lock,
            adopted: None,
            entries: BTreeMap::new(),
            cursor: 0,
        };
        for r in records {
            o.apply(r);
        }
        Ok(o)
    }
    fn apply(&mut self, r: OutboxRecord) {
        match r {
            OutboxRecord::Staged { envelope, command } => {
                self.entries.insert(
                    envelope.episode,
                    Entry {
                        envelope,
                        command: *command,
                        certificate: None,
                        receipt: None,
                    },
                );
            }
            OutboxRecord::Certified {
                episode,
                certificate,
            } => {
                if let Some(e) = self.entries.get_mut(&episode) {
                    e.certificate = Some(*certificate);
                }
            }
            OutboxRecord::Delivered { episode, receipt } => {
                if let Some(e) = self.entries.get_mut(&episode) {
                    self.cursor = self.cursor.max(e.envelope.in_reply_to);
                    e.receipt = Some(receipt);
                }
            }
            OutboxRecord::Adopted {
                handoff,
                cursor,
                pending,
            } => {
                self.adopted = Some(handoff);
                self.cursor = self.cursor.max(cursor);
                for r in pending {
                    self.entries.insert(
                        r.envelope.episode,
                        Entry {
                            envelope: r.envelope,
                            command: r.command,
                            certificate: Some(r.certificate),
                            receipt: None,
                        },
                    );
                }
            }
        }
    }
    fn record(&mut self, r: OutboxRecord) -> Result<()> {
        self.log.append(&r)?;
        self.apply(r);
        Ok(())
    }
    /// Episodes without a delivery receipt, in stream order.
    fn pending(&self) -> Vec<u64> {
        let mut p: Vec<_> = self
            .entries
            .values()
            .filter(|e| e.receipt.is_none())
            .map(|e| (e.envelope.in_reply_to, e.envelope.episode))
            .collect();
        p.sort_unstable();
        p.into_iter().map(|(_, e)| e).collect()
    }
    /// Certificates of every Learn this outbox holds, in stream order.
    fn certificates(&self) -> Vec<Certificate> {
        let mut c: Vec<_> = self
            .entries
            .values()
            .filter_map(|e| Some((e.envelope.in_reply_to, e.certificate.clone()?)))
            .collect();
        c.sort_by_key(|(s, _)| *s);
        c.into_iter().map(|(_, c)| c).collect()
    }
}

/// One reply delivered by a stream run.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Delivery {
    pub receipt: Receipt,
    /// The broker already held this reply.
    pub replayed: bool,
    pub reply: CertifiedReply,
}

/// Certify a staged Learn. The signed command is exact, so after a crash the custodians either
/// bind it fresh or replay its installed certificate.
fn certify(seat: &Path, outbox: &mut Outbox, episode: u64, barriers: bool) -> Result<()> {
    let e = &outbox.entries[&episode];
    if e.certificate.is_some() {
        return Ok(());
    }
    let id = e.command.id();
    let Outcome::Certified(cert) =
        operate_with(seat, Operation::Exercise(e.command.grant.clone()), |_| {
            barrier(seat, barriers, &format!("certified-{episode}"))
        })?
    else {
        bail!("expected a Learn certificate");
    };
    ensure!(cert.head.change == id, "certified another command");
    barrier(seat, barriers, &format!("cursor-{episode}"))?;
    outbox.record(OutboxRecord::Certified {
        episode,
        certificate: Box::new(cert),
    })
}

fn deliver(
    seat: &Path,
    broker: &BrokerClient,
    outbox: &mut Outbox,
    episode: u64,
    barriers: bool,
) -> Result<Delivery> {
    let e = &outbox.entries[&episode];
    let reply = CertifiedReply {
        envelope: e.envelope.clone(),
        command: e.command.clone(),
        certificate: e.certificate.clone().context("uncertified reply")?,
    };
    let view = SeatView::open(seat)?;
    let current = view.cursor.clone().context("seat has no certified head")?;
    let (receipt, replayed) = broker.post(&Post::sign(reply.clone(), current, &view.key))?;
    barrier(seat, barriers, &format!("delivered-{episode}"))?;
    outbox.record(OutboxRecord::Delivered {
        episode,
        receipt: receipt.clone(),
    })?;
    Ok(Delivery {
        receipt,
        replayed,
        reply,
    })
}

/// Finish what an earlier run left, then answer every frame after the outbox cursor: stage,
/// certify, deliver. With `barriers`, an armed `arm-<phase>-<episode>` file in the seat holds
/// the worker at `read`, `certified` (after quorum), `cursor` (after the seat cursor) or
/// `delivered` (after the broker's receipt, before the outbox's).
pub fn stream(seat: &Path, broker: &Path, issuer: &Path, barriers: bool) -> Result<Vec<Delivery>> {
    let mut outbox = Outbox::open(seat)?;
    let client = BrokerClient(broker);
    let mut out = vec![];
    for episode in outbox.pending() {
        certify(seat, &mut outbox, episode, barriers)?;
        out.push(deliver(seat, &client, &mut outbox, episode, barriers)?);
    }
    for frame in client.read(outbox.cursor)? {
        if outbox.entries.contains_key(&frame.message_id) {
            continue;
        }
        barrier(seat, barriers, &format!("read-{}", frame.message_id))?;
        let view = SeatView::open(seat)?;
        let envelope = Envelope::reply(&view.cfg.genesis(), &frame);
        let grant = request_grant(issuer, view.head(), learn(&frame, &envelope))?;
        let command = Command::authorize(grant, &view.key, None);
        outbox.record(OutboxRecord::Staged {
            envelope,
            command: Box::new(command),
        })?;
        certify(seat, &mut outbox, frame.message_id, barriers)?;
        out.push(deliver(
            seat,
            &client,
            &mut outbox,
            frame.message_id,
            barriers,
        )?);
    }
    Ok(out)
}

/// What a recovered seat holds before it offers a move.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Recovered {
    pub head: Head,
    /// Every Learn certificate in the outbox, in stream order.
    pub certificates: Vec<Certificate>,
}

/// Certify every staged Learn without delivering anything.
pub fn recover(seat: &Path) -> Result<Recovered> {
    let mut outbox = Outbox::open(seat)?;
    for episode in outbox.pending() {
        certify(seat, &mut outbox, episode, false)?;
    }
    Ok(Recovered {
        head: SeatView::open(seat)?.head().clone(),
        certificates: outbox.certificates(),
    })
}

/// The source operator's certified, undelivered replies at its last certified head.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Handoff {
    pub head: Certificate,
    pub cursor: u64,
    pub pending: Vec<CertifiedReply>,
    pub signature: Vec<u8>,
}

impl Handoff {
    fn body(&self) -> (&Certificate, u64, &Vec<CertifiedReply>) {
        (&self.head, self.cursor, &self.pending)
    }
    pub fn sign(mut self, key: &SigningKey) -> Self {
        self.signature = signature(key, b"tulip outbox handoff", &self.body());
        self
    }
}

pub fn handoff(seat: &Path) -> Result<Handoff> {
    let outbox = Outbox::open(seat)?;
    let view = SeatView::open(seat)?;
    let pending = outbox
        .pending()
        .into_iter()
        .map(|episode| {
            let e = &outbox.entries[&episode];
            Ok(CertifiedReply {
                envelope: e.envelope.clone(),
                command: e.command.clone(),
                certificate: e
                    .certificate
                    .clone()
                    .context("a staged Learn is uncertified; recover first")?,
            })
        })
        .collect::<Result<_>>()?;
    Ok(Handoff {
        head: view.cursor.clone().context("no certified head")?,
        cursor: outbox.cursor,
        pending,
        signature: vec![],
    }
    .sign(&view.key))
}

/// Adopt a predecessor's handoff into this seat's fresh outbox, right after accepting the move.
pub fn adopt(seat: &Path, h: &Handoff, broker: &Path) -> Result<()> {
    let view = SeatView::open(seat)?;
    let cfg = &view.cfg;
    h.head.verify(cfg)?;
    verify_sig(
        h.head.head.operator_id,
        b"tulip outbox handoff",
        &h.body(),
        &h.signature,
    )
    .context("handoff signature")?;
    let mut outbox = Outbox::open(seat)?;
    let handoff = digest(b"adopted Tulip handoff", &[&h.signature]);
    if outbox.adopted == Some(handoff) {
        return Ok(());
    }
    let mine = view.cursor.as_ref().context("accept the move first")?;
    ensure!(
        mine.head.parent_commitment == head_root(&h.head.head)
            && mine.head.operator_id == view.key.verifying_key().to_bytes()
            && mine.head.operator_id != h.head.head.operator_id,
        "handoff is not from the parent of this seat's move"
    );
    let client = BrokerClient(broker);
    let frames = client.read(0)?;
    ensure!(
        h.cursor <= frames.len() as u64,
        "handoff cursor beyond stream"
    );
    for f in &frames[..h.cursor as usize] {
        ensure!(
            client
                .lookup(idempotency_key(&cfg.genesis(), f.message_id))?
                .is_some(),
            "handoff counts message {} as answered, but the broker holds no reply",
            f.message_id
        );
    }
    for (i, r) in h.pending.iter().enumerate() {
        r.verify(cfg)?;
        let frame = frames
            .get(h.cursor as usize + i)
            .context("pending reply beyond stream")?;
        ensure!(
            r.certificate.head.epoch <= h.head.head.epoch
                && r.envelope == Envelope::reply(&cfg.genesis(), frame),
            "pending replies must follow the delivered stream prefix"
        );
    }
    ensure!(
        outbox.adopted.is_none() && outbox.entries.is_empty() && outbox.cursor == 0,
        "outbox already in use"
    );
    ensure!(
        matches!(
            client.call(BrokerRequest::Fence(Box::new(mine.clone())))?,
            BrokerAnswer::Fenced
        ),
        "unexpected fence acknowledgment"
    );
    outbox.record(OutboxRecord::Adopted {
        handoff,
        cursor: h.cursor,
        pending: h.pending.clone(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wal_recovers_an_incomplete_tail_and_preserves_corruption_for_inspection() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("test.wal");
        let (mut log, _) = Log::open::<u64>(&path)?;
        log.append(&123_u64)?;
        let first = log.0.metadata()?.len() as usize;
        log.append(&456_u64)?;
        drop(log);
        let complete = fs::read(&path)?;
        for length in first..complete.len() {
            fs::write(&path, &complete[..length])?;
            assert_eq!(Log::open::<u64>(&path)?.1, [123]);
            assert_eq!(fs::read(&path)?, complete[..first]);
        }
        let mut damaged = complete;
        damaged[4] ^= 1;
        fs::write(&path, &damaged)?;
        assert!(Log::open::<u64>(&path).is_err());
        assert_eq!(fs::read(path)?, damaged);
        Ok(())
    }
}
