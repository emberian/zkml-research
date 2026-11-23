//! Word ABI of Obend's proved Pancake `stepBeltLatch` transition.
//!
//! Ground truth (Obend `25dd6789`, unchanged at `3543a3b6`):
//! `obend/lean/Obend/Lower/Pancake/BeltLatch.lean`, the emitted `beltLatch.pnk`, its native
//! driver `beltLatch.c`, and the 21 comparisons of `lean/tests/metasystem/PancakeBeltLatchTest.lean`.
//!
//! `stepBeltLatch(current, candidate)` reads a 14-word state and a 19-word request
//! (`readState`, `readRequest`), returns `Status.code`, and on acceptance stores the five words
//! `epoch, digest[0..4]` read from one snapshot of the request (`storeHead`). No other word
//! changes (`pancakeBeltLatch_frame`) and a refusal changes nothing
//! (`pancakeBeltLatch_refusal_preserves_state`). Once a parent epoch has advanced, no competing
//! child of it is accepted again (`accepted_parent_consumed`).
//!
//! A 32-byte digest enters the ABI as four little-endian limbs, limb `i` being bytes `8i..8i+8`.
//! The driver reads and writes little-endian words, so on its x86-64 target the memory image of
//! the four limbs is the digest itself.
use anyhow::{ensure, Context, Result};
use std::path::PathBuf;
use std::process::Command;

pub const STATE_WORDS: usize = 14;
pub const REQUEST_WORDS: usize = 19;
/// `beltLatch RECORD` input: the state words, then the request words.
pub const RECORD_BYTES: usize = 8 * (STATE_WORDS + REQUEST_WORDS);
/// `beltLatch RECORD` output: the status word, then both buffers after the call.
pub const OUTPUT_BYTES: usize = 8 + RECORD_BYTES;

pub type StateWords = [u64; STATE_WORDS];
pub type RequestWords = [u64; REQUEST_WORDS];
pub type Digest4 = [u64; 4];

/// Word offsets of `readState`.
pub mod state {
    pub const INITIALIZED: usize = 0;
    pub const GENESIS: usize = 1;
    pub const EPOCH: usize = 5;
    pub const DIGEST: usize = 6;
    pub const POLICY: usize = 10;
}

/// Word offsets of `readRequest`.
pub mod request {
    pub const GENESIS: usize = 0;
    pub const PARENT_EPOCH: usize = 4;
    pub const NEXT_EPOCH: usize = 5;
    pub const PARENT: usize = 6;
    pub const NEXT_DIGEST: usize = 10;
    pub const POLICY: usize = 14;
    pub const PERSIST_ACK: usize = 18;
}

/// `Status`, with `Status.code` as the discriminant.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u64)]
pub enum Status {
    Accepted = 0,
    GenesisMismatch = 1,
    StaleParent = 2,
    NonIncreasing = 3,
    ParentFork = 4,
    PolicyDrift = 5,
    MissingAck = 6,
}

impl Status {
    pub const ALL: [Status; 7] = [
        Status::Accepted,
        Status::GenesisMismatch,
        Status::StaleParent,
        Status::NonIncreasing,
        Status::ParentFork,
        Status::PolicyDrift,
        Status::MissingAck,
    ];
    pub const fn code(self) -> u64 {
        self as u64
    }
    pub fn from_code(code: u64) -> Option<Self> {
        Self::ALL.get(usize::try_from(code).ok()?).copied()
    }
}

pub fn limbs(d: &[u8; 32]) -> Digest4 {
    std::array::from_fn(|i| u64::from_le_bytes(d[8 * i..8 * i + 8].try_into().unwrap()))
}

pub fn digest_bytes(l: &Digest4) -> [u8; 32] {
    let mut out = [0; 32];
    for (chunk, w) in out.chunks_exact_mut(8).zip(l) {
        chunk.copy_from_slice(&w.to_le_bytes());
    }
    out
}

/// `State`. Field order is the word order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LatchState {
    pub initialized: u64,
    pub genesis: Digest4,
    pub epoch: u64,
    pub digest: Digest4,
    pub policy: Digest4,
}

/// `Request`. Field order is the word order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LatchRequest {
    pub genesis: Digest4,
    pub parent_epoch: u64,
    pub next_epoch: u64,
    pub parent: Digest4,
    pub next_digest: Digest4,
    pub policy: Digest4,
    pub persist_ack: u64,
}

fn put(words: &mut [u64], at: usize, d: &Digest4) {
    words[at..at + 4].copy_from_slice(d);
}
fn get(words: &[u64], at: usize) -> Digest4 {
    words[at..at + 4].try_into().unwrap()
}

impl LatchState {
    pub fn to_words(&self) -> StateWords {
        let mut w = [0; STATE_WORDS];
        w[state::INITIALIZED] = self.initialized;
        put(&mut w, state::GENESIS, &self.genesis);
        w[state::EPOCH] = self.epoch;
        put(&mut w, state::DIGEST, &self.digest);
        put(&mut w, state::POLICY, &self.policy);
        w
    }
    pub fn from_words(w: &StateWords) -> Self {
        Self {
            initialized: w[state::INITIALIZED],
            genesis: get(w, state::GENESIS),
            epoch: w[state::EPOCH],
            digest: get(w, state::DIGEST),
            policy: get(w, state::POLICY),
        }
    }
}

impl LatchRequest {
    pub fn to_words(&self) -> RequestWords {
        let mut w = [0; REQUEST_WORDS];
        put(&mut w, request::GENESIS, &self.genesis);
        w[request::PARENT_EPOCH] = self.parent_epoch;
        w[request::NEXT_EPOCH] = self.next_epoch;
        put(&mut w, request::PARENT, &self.parent);
        put(&mut w, request::NEXT_DIGEST, &self.next_digest);
        put(&mut w, request::POLICY, &self.policy);
        w[request::PERSIST_ACK] = self.persist_ack;
        w
    }
    pub fn from_words(w: &RequestWords) -> Self {
        Self {
            genesis: get(w, request::GENESIS),
            parent_epoch: w[request::PARENT_EPOCH],
            next_epoch: w[request::NEXT_EPOCH],
            parent: get(w, request::PARENT),
            next_digest: get(w, request::NEXT_DIGEST),
            policy: get(w, request::POLICY),
            persist_ack: w[request::PERSIST_ACK],
        }
    }
}

/// `stepBeltLatch` on structured values, branch for branch.
pub fn step(s: &LatchState, r: &LatchRequest) -> (Status, LatchState) {
    if s.initialized == 1 && s.genesis == r.genesis {
        if s.epoch == r.parent_epoch {
            if s.epoch < r.next_epoch {
                if s.digest == r.parent {
                    if s.policy == r.policy {
                        if r.persist_ack == 1 {
                            let next = LatchState {
                                epoch: r.next_epoch,
                                digest: r.next_digest,
                                ..*s
                            };
                            (Status::Accepted, next)
                        } else {
                            (Status::MissingAck, *s)
                        }
                    } else {
                        (Status::PolicyDrift, *s)
                    }
                } else {
                    (Status::ParentFork, *s)
                }
            } else {
                (Status::NonIncreasing, *s)
            }
        } else {
            (Status::StaleParent, *s)
        }
    } else {
        (Status::GenesisMismatch, *s)
    }
}

/// The emitted `beltLatch.pnk` over caller-owned buffers: the same loads in the same order,
/// the unsigned `<+` epoch test, and one five-word store taken from the request snapshot.
pub fn step_words(current: &mut StateWords, candidate: &RequestWords) -> u64 {
    let (c, r) = (current, candidate);
    if c[0] != 1 {
        return 1;
    }
    for i in 0..4 {
        if c[1 + i] != r[i] {
            return 1;
        }
    }
    if c[5] != r[4] {
        return 2;
    }
    if c[5] >= r[5] {
        return 3;
    }
    for i in 0..4 {
        if c[6 + i] != r[6 + i] {
            return 4;
        }
    }
    for i in 0..4 {
        if c[10 + i] != r[14 + i] {
            return 5;
        }
    }
    if r[18] != 1 {
        return 6;
    }
    let head = [r[5], r[10], r[11], r[12], r[13]];
    c[5..10].copy_from_slice(&head);
    0
}

/// `bytes (stateWords s ++ requestWords r)`: the driver's 264-byte input record.
pub fn record_bytes(current: &StateWords, candidate: &RequestWords) -> [u8; RECORD_BYTES] {
    let mut out = [0; RECORD_BYTES];
    for (chunk, w) in out.chunks_exact_mut(8).zip(current.iter().chain(candidate)) {
        chunk.copy_from_slice(&w.to_le_bytes());
    }
    out
}

/// The request words alone, little-endian, used as the payload of a custody vote.
pub fn request_bytes(candidate: &RequestWords) -> [u8; 8 * REQUEST_WORDS] {
    let mut out = [0; 8 * REQUEST_WORDS];
    for (chunk, w) in out.chunks_exact_mut(8).zip(candidate) {
        chunk.copy_from_slice(&w.to_le_bytes());
    }
    out
}

/// `bytes ([v.code] ++ stateWords next ++ requestWords r)`: what the driver must print.
pub fn output_bytes(code: u64, next: &StateWords, candidate: &RequestWords) -> [u8; OUTPUT_BYTES] {
    let mut out = [0; OUTPUT_BYTES];
    out[..8].copy_from_slice(&code.to_le_bytes());
    out[8..].copy_from_slice(&record_bytes(next, candidate));
    out
}

pub fn parse_output(bytes: &[u8]) -> Result<(u64, StateWords, RequestWords)> {
    ensure!(bytes.len() == OUTPUT_BYTES, "expected {OUTPUT_BYTES} output bytes, got {}", bytes.len());
    let words: Vec<u64> = bytes
        .chunks_exact(8)
        .map(|c| u64::from_le_bytes(c.try_into().unwrap()))
        .collect();
    Ok((
        words[0],
        words[1..1 + STATE_WORDS].try_into().unwrap(),
        words[1 + STATE_WORDS..].try_into().unwrap(),
    ))
}

/// Environment variable naming a `cake --pancake` build of `beltLatch.pnk` linked with `beltLatch.c`.
pub const NATIVE_ENV: &str = "OBEND_BELTLATCH_EXE";

/// The CakeML-compiled kernel, driven one record per process as `PancakeBeltLatchTest.verifyNative` does.
pub struct NativeBeltLatch {
    exe: PathBuf,
    record: PathBuf,
}

impl NativeBeltLatch {
    /// `record` is a scratch file the caller owns exclusively.
    pub fn new(exe: impl Into<PathBuf>, record: impl Into<PathBuf>) -> Self {
        Self {
            exe: exe.into(),
            record: record.into(),
        }
    }
    pub fn from_env(record: impl Into<PathBuf>) -> Option<Self> {
        std::env::var_os(NATIVE_ENV).map(|exe| Self::new(exe, record))
    }
    pub fn run(&self, current: &StateWords, candidate: &RequestWords) -> Result<(u64, StateWords, RequestWords)> {
        std::fs::write(&self.record, record_bytes(current, candidate))?;
        let out = Command::new(&self.exe)
            .arg(&self.record)
            .output()
            .with_context(|| format!("running {}", self.exe.display()))?;
        ensure!(
            out.status.success(),
            "native beltLatch {}: {}",
            out.status,
            String::from_utf8_lossy(&out.stderr)
        );
        parse_output(&out.stdout)
    }
    /// Run one step natively and in Rust. Both must return the same status and leave both
    /// buffers word-for-word identical.
    pub fn differential(&self, current: &mut StateWords, candidate: &RequestWords) -> Result<u64> {
        let mut next = *current;
        let code = step_words(&mut next, candidate);
        let native = self.run(current, candidate)?;
        ensure!(
            native == (code, next, *candidate),
            "native beltLatch disagrees: native {:?}, rust {:?}",
            native,
            (code, next, *candidate)
        );
        *current = next;
        Ok(code)
    }
}

/// The 21 comparisons of `PancakeBeltLatchTest.vectors`, with the statuses its `#guard` checks.
pub fn conformance_vectors() -> Vec<(LatchState, LatchRequest, Status)> {
    let initial = LatchState {
        initialized: 1,
        genesis: [0xa2d3739942c82117, 2, 3, 4],
        epoch: 0x7fffffffffffffff,
        digest: [5, 6, 7, 0xb71133f0c627d9ae],
        policy: [9, 10, 11, 12],
    };
    let advance = LatchRequest {
        genesis: initial.genesis,
        parent_epoch: initial.epoch,
        next_epoch: 0x8000000000000000,
        parent: initial.digest,
        next_digest: [13, 14, 15, 0xfedcba9876543210],
        policy: initial.policy,
        persist_ack: 1,
    };
    let flip = |d: Digest4| -> Vec<Digest4> {
        (0..4)
            .map(|i| {
                let mut e = d;
                e[i] ^= 1;
                e
            })
            .collect()
    };
    let after = step(&initial, &advance).1;
    let last = LatchRequest {
        parent_epoch: after.epoch,
        parent: after.digest,
        next_epoch: u64::MAX,
        ..advance
    };
    let mut v = vec![
        (initial, advance, Status::Accepted),
        (after, advance, Status::StaleParent),
        (after, last, Status::Accepted),
        (
            step(&after, &last).1,
            LatchRequest {
                parent_epoch: u64::MAX,
                next_epoch: 0,
                ..last
            },
            Status::NonIncreasing,
        ),
        (
            initial,
            LatchRequest {
                next_epoch: initial.epoch,
                ..advance
            },
            Status::NonIncreasing,
        ),
        (initial, LatchRequest { persist_ack: 0, ..advance }, Status::MissingAck),
        (initial, LatchRequest { persist_ack: 2, ..advance }, Status::MissingAck),
        (LatchState { initialized: 0, ..initial }, advance, Status::GenesisMismatch),
        (LatchState { initialized: 2, ..initial }, advance, Status::GenesisMismatch),
    ];
    for d in flip(advance.genesis) {
        v.push((initial, LatchRequest { genesis: d, ..advance }, Status::GenesisMismatch));
    }
    for d in flip(advance.parent) {
        v.push((initial, LatchRequest { parent: d, ..advance }, Status::ParentFork));
    }
    for d in flip(advance.policy) {
        v.push((initial, LatchRequest { policy: d, ..advance }, Status::PolicyDrift));
    }
    v
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Each vector's status is the one the Lean test guards; the successor buffers are those
    /// `pancakeBeltLatch_correct` fixes: the incoming state on refusal, and on acceptance the
    /// state with exactly words 5..9 replaced by `nextEpoch, nextDigest`.
    #[test]
    fn lean_conformance_vectors() {
        let vectors = conformance_vectors();
        assert_eq!(vectors.len(), 21);
        let mut statuses = std::collections::BTreeSet::new();
        const LEAN: &[u8; 21 * (RECORD_BYTES + OUTPUT_BYTES)] =
            include_bytes!("../tests/fixtures/belt_latch_records.bin");
        for ((s, r, want), fixture) in vectors.iter().zip(LEAN.chunks_exact(RECORD_BYTES + OUTPUT_BYTES)) {
            let (status, next) = step(s, r);
            assert_eq!(status, *want);
            let mut words = s.to_words();
            let req = r.to_words();
            assert_eq!(record_bytes(&words, &req).as_slice(), &fixture[..RECORD_BYTES]);
            assert_eq!(step_words(&mut words, &req), want.code());
            assert_eq!(words, next.to_words());
            let mut expected = s.to_words();
            if *want == Status::Accepted {
                expected[5] = r.next_epoch;
                expected[6..10].copy_from_slice(&r.next_digest);
            }
            assert_eq!(words, expected);
            let out = output_bytes(status.code(), &words, &req);
            assert_eq!(out.as_slice(), &fixture[RECORD_BYTES..]);
            assert_eq!(parse_output(&out).unwrap(), (want.code(), words, req));
            statuses.insert(*want);
        }
        assert_eq!(statuses.len(), 7, "every status code is exercised");
    }

    /// Single-word mutations of a valid pair, both transliterations, every word position.
    #[test]
    fn word_and_structured_kernels_agree_under_mutation() {
        let (s, r, _) = conformance_vectors()[0];
        let flips = [1u64, 1 << 63, u64::MAX, 0x0123_4567_89ab_cdef];
        let mut seen = std::collections::BTreeSet::new();
        for (sw, rw) in (0..STATE_WORDS).map(|i| (Some(i), None)).chain((0..REQUEST_WORDS).map(|i| (None, Some(i)))) {
            for f in flips {
                let mut state = s.to_words();
                let mut req = r.to_words();
                if let Some(i) = sw {
                    state[i] ^= f;
                }
                if let Some(i) = rw {
                    req[i] ^= f;
                }
                let (status, next) = step(&LatchState::from_words(&state), &LatchRequest::from_words(&req));
                let before = state;
                let code = step_words(&mut state, &req);
                assert_eq!(code, status.code());
                assert_eq!(state, next.to_words());
                if status != Status::Accepted {
                    assert_eq!(state, before);
                } else {
                    assert_eq!((&state[..5], &state[10..]), (&before[..5], &before[10..]));
                }
                seen.insert(status);
            }
        }
        assert_eq!(seen.len(), 7);
    }

    /// Pairs for the native comparison: the 21 Lean vectors, every single-word mutation of an
    /// accepted pair, and pseudorandom pairs whose request words each either copy the state's
    /// matching word or not, so every branch is reached.
    fn differential_vectors(random: usize) -> Vec<(StateWords, RequestWords)> {
        let mut v: Vec<_> = conformance_vectors()
            .iter()
            .map(|(s, r, _)| (s.to_words(), r.to_words()))
            .collect();
        let (s, r) = v[0];
        for i in 0..STATE_WORDS + REQUEST_WORDS {
            for f in [1u64, 1 << 63, u64::MAX, 0x0123_4567_89ab_cdef] {
                let (mut s, mut r) = (s, r);
                if i < STATE_WORDS {
                    s[i] ^= f;
                } else {
                    r[i - STATE_WORDS] ^= f;
                }
                v.push((s, r));
            }
        }
        let mut x = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = move || {
            x ^= x << 7;
            x ^= x >> 9;
            x
        };
        // Request word -> the state word an accepting request copies.
        let pairs = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (6, 6), (7, 7), (8, 8), (9, 9), (14, 10), (15, 11), (16, 12), (17, 13)];
        for _ in 0..random {
            let mut s: StateWords = std::array::from_fn(|_| next());
            s[0] = if next() % 8 == 0 { next() % 3 } else { 1 };
            let mut r: RequestWords = std::array::from_fn(|_| next());
            for (ri, si) in pairs {
                if next() % 16 != 0 {
                    r[ri] = s[si];
                }
            }
            if next() % 4 != 0 {
                r[5] = s[5].wrapping_add(next() % 3);
            }
            r[18] = if next() % 8 == 0 { next() % 3 } else { 1 };
            v.push((s, r));
        }
        v
    }

    /// `PancakeBeltLatchTest.verifyNative`, with this crate as the reference: each 264-byte
    /// record goes through the CakeML build and its 272-byte output must equal Rust's.
    #[test]
    #[ignore = "needs OBEND_BELTLATCH_EXE, a cake --pancake build of Obend's beltLatch.pnk"]
    fn native_beltlatch_parity() -> Result<()> {
        let exe = std::env::var_os(NATIVE_ENV).context("set OBEND_BELTLATCH_EXE")?;
        let dir = std::env::temp_dir().join(format!("beltlatch-parity-{}", std::process::id()));
        std::fs::create_dir_all(&dir)?;
        let native = NativeBeltLatch::new(exe, dir.join("record"));
        let vectors = differential_vectors(4000);
        let mut statuses = [0usize; 7];
        for (i, (s, r)) in vectors.iter().enumerate() {
            let mut words = *s;
            let code = step_words(&mut words, r);
            let (ncode, nstate, nreq) = native.run(s, r)?;
            ensure!(
                output_bytes(ncode, &nstate, &nreq) == output_bytes(code, &words, r),
                "vector {i}: native ({ncode}, {nstate:?}) rust ({code}, {words:?})"
            );
            if i < 21 {
                ensure!(code == conformance_vectors()[i].2.code(), "Lean status, vector {i}");
            }
            statuses[code as usize] += 1;
        }
        std::fs::remove_dir_all(&dir)?;
        println!(
            "{} native comparisons (21 Lean vectors, {} single-word mutations, 4000 pseudorandom): status, 14 state words, 19 request words identical; by status 0..6 {statuses:?}",
            vectors.len(),
            33 * 4
        );
        ensure!(statuses.iter().all(|&n| n > 0));
        Ok(())
    }

    #[test]
    fn digest_limbs_are_the_little_endian_memory_image() {
        let d: [u8; 32] = std::array::from_fn(|i| i as u8);
        let l = limbs(&d);
        assert_eq!(l[0], 0x0706050403020100);
        assert_eq!(digest_bytes(&l), d);
        let mut words = [0; REQUEST_WORDS];
        words[request::PARENT..request::PARENT + 4].copy_from_slice(&l);
        assert_eq!(&request_bytes(&words)[8 * request::PARENT..8 * request::PARENT + 32], &d);
    }
}
