//! Transition kernel of the durable belt latch (`qsag-core::belt_latch::BeltLatch`).
//!
//! `BeltLatch::bind` decides between a fresh binding, an idempotent replay and a refusal,
//! and only then touches the write-ahead log. This module is that decision with the log
//! removed: the outcome of the durable write is an explicit input (`persist_ok`), and the
//! state is the pair the log stores (`next_epoch`, the in-flight record) plus the poison flag.
//! The branch order and every error are those of `BeltLatch::latched_salt` followed by
//! `BeltLatch::bind`.
//!
//! Differences from the production type, all representational:
//! * the capacity is held as the exclusive epoch limit `2^capacity_log2` instead of its
//!   logarithm (`2 <= limit <= 2^62`, the image of `1 <= capacity_log2 <= 62`);
//! * the digit vector is a length and four 32-byte rows (at most 128 digits, zero padded),
//!   which is injective on vectors of that length;
//! * the window test `epoch > next_epoch + MAX_EPOCH_JUMP` is written as
//!   `epoch - next_epoch > MAX_EPOCH_JUMP`, which is the same predicate once
//!   `epoch >= next_epoch` has been established and cannot overflow.
//!
//! Echo construction and verification, and the log's own MAC, are not part of this kernel.

use crate::tower::ct_eq_bytes32;

/// Largest distance above the high-water mark at which a fresh epoch may be bound.
pub const BELT_LATCH_MAX_EPOCH_JUMP: u64 = 64;

/// Largest exclusive epoch limit (`2^62`).
pub const BELT_LATCH_MAX_CAPACITY_LIMIT: u64 = 1u64 << 62;

/// Largest digit vector the four rows can hold. The kernel compares digit vectors and never
/// interprets them, so it does not enforce this bound; callers embedding a `Vec<u8>` must.
pub const BELT_LATCH_MAX_DIGITS: u8 = 128;

/// Base-`w` digits whose chain nodes an epoch may reveal: `len` digits in row-major order,
/// unused positions zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BeltLatchDigits {
    pub len: u8,
    pub row0: [u8; 32],
    pub row1: [u8; 32],
    pub row2: [u8; 32],
    pub row3: [u8; 32],
}

/// Equality of two digit vectors.
#[inline]
pub const fn belt_latch_digits_eq(a: &BeltLatchDigits, b: &BeltLatchDigits) -> bool {
    if a.len != b.len {
        return false;
    }
    if !ct_eq_bytes32(&a.row0, &b.row0) {
        return false;
    }
    if !ct_eq_bytes32(&a.row1, &b.row1) {
        return false;
    }
    if !ct_eq_bytes32(&a.row2, &b.row2) {
        return false;
    }
    ct_eq_bytes32(&a.row3, &b.row3)
}

/// The durable binding of one epoch (`BeltLatchRecord`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BeltLatchKernelRecord {
    pub epoch: u64,
    pub msg_digest: [u8; 32],
    pub retry_salt: [u8; 32],
    pub digits: BeltLatchDigits,
}

/// Refusals of [`BeltLatchKernel::bind`]; the names are those of `BeltLatchError`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BeltLatchKernelError {
    /// The epoch limit is below 2 or above `2^62`, or the recovered state is not one the
    /// latch can have written.
    InvalidCapacity,
    /// The epoch is at or beyond the key's capacity.
    Exhausted,
    /// The epoch is in flight for a different message digest.
    EpochAlreadyBound,
    /// The epoch is in flight with a different salt.
    RetrySaltMismatch,
    /// The epoch is in flight with different digits.
    DigitsMismatch,
    /// The epoch was bound earlier and is no longer the in-flight record.
    EpochConsumed,
    /// A fresh epoch lies more than [`BELT_LATCH_MAX_EPOCH_JUMP`] above the high-water mark.
    EpochJumpTooLarge,
    /// An earlier persist failed.
    WalPoisoned,
    /// The durable write of this binding failed; the latch is now poisoned.
    WalPersistFailed,
}

/// Outcome of an accepted bind (`BindOutcome`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BeltLatchBindOutcome {
    /// A new epoch was persisted.
    Fresh,
    /// The in-flight record already equals the request; nothing was written.
    Replay,
}

/// One bind request together with what the log answered.
#[derive(Clone, Copy)]
pub struct BeltLatchBindRequest {
    pub epoch: u64,
    pub msg_digest: [u8; 32],
    pub retry_salt: [u8; 32],
    pub digits: BeltLatchDigits,
    /// Result of `DurableWal::sync_persist` for this request. Read only on the fresh path,
    /// after every check has passed, exactly where production calls the log.
    pub persist_ok: bool,
}

/// Latch state: what the log holds, the capacity, and the poison flag. Not `Clone`.
pub struct BeltLatchKernel {
    capacity_limit: u64,
    next_epoch: u64,
    has_in_flight: bool,
    in_flight: BeltLatchKernelRecord,
    wal_poisoned: bool,
}

const fn belt_latch_empty_record() -> BeltLatchKernelRecord {
    BeltLatchKernelRecord {
        epoch: 0,
        msg_digest: [0u8; 32],
        retry_salt: [0u8; 32],
        digits: BeltLatchDigits {
            len: 0,
            row0: [0u8; 32],
            row1: [0u8; 32],
            row2: [0u8; 32],
            row3: [0u8; 32],
        },
    }
}

impl BeltLatchKernel {
    /// A latch over an unwritten log (`BeltLatchState::default()`).
    pub const fn new_empty(capacity_limit: u64) -> Result<BeltLatchKernel, BeltLatchKernelError> {
        if capacity_limit < 2 {
            return Err(BeltLatchKernelError::InvalidCapacity);
        }
        if capacity_limit > BELT_LATCH_MAX_CAPACITY_LIMIT {
            return Err(BeltLatchKernelError::InvalidCapacity);
        }
        Ok(BeltLatchKernel {
            capacity_limit,
            next_epoch: 0,
            has_in_flight: false,
            in_flight: belt_latch_empty_record(),
            wal_poisoned: false,
        })
    }

    /// A latch recovered from a log holding `next_epoch` and `in_flight`. Recovery clears
    /// the poison flag, as constructing a new `BeltLatch` does. States the latch cannot
    /// have written (a high-water mark above the limit, or an in-flight epoch at or above
    /// the high-water mark) are refused.
    pub const fn recover(
        capacity_limit: u64,
        next_epoch: u64,
        has_in_flight: bool,
        in_flight: BeltLatchKernelRecord,
    ) -> Result<BeltLatchKernel, BeltLatchKernelError> {
        if capacity_limit < 2 {
            return Err(BeltLatchKernelError::InvalidCapacity);
        }
        if capacity_limit > BELT_LATCH_MAX_CAPACITY_LIMIT {
            return Err(BeltLatchKernelError::InvalidCapacity);
        }
        if next_epoch > capacity_limit {
            return Err(BeltLatchKernelError::InvalidCapacity);
        }
        if has_in_flight {
            if in_flight.epoch >= next_epoch {
                return Err(BeltLatchKernelError::InvalidCapacity);
            }
        }
        Ok(BeltLatchKernel {
            capacity_limit,
            next_epoch,
            has_in_flight,
            in_flight,
            wal_poisoned: false,
        })
    }

    pub const fn next_epoch(&self) -> u64 {
        self.next_epoch
    }

    pub const fn capacity_limit(&self) -> u64 {
        self.capacity_limit
    }

    pub const fn has_in_flight(&self) -> bool {
        self.has_in_flight
    }

    pub const fn in_flight(&self) -> BeltLatchKernelRecord {
        self.in_flight
    }

    pub const fn is_wal_poisoned(&self) -> bool {
        self.wal_poisoned
    }

    /// `BeltLatch::bind`: persist the binding of `req.epoch`, or confirm that the identical
    /// binding is in flight. A failed persist poisons the latch and binds nothing.
    pub const fn bind(
        self,
        req: BeltLatchBindRequest,
    ) -> (
        BeltLatchKernel,
        Result<BeltLatchBindOutcome, BeltLatchKernelError>,
    ) {
        if self.wal_poisoned {
            return (self, Err(BeltLatchKernelError::WalPoisoned));
        }
        if self.has_in_flight {
            if self.in_flight.epoch == req.epoch {
                if !ct_eq_bytes32(&self.in_flight.msg_digest, &req.msg_digest) {
                    return (self, Err(BeltLatchKernelError::EpochAlreadyBound));
                }
                if !ct_eq_bytes32(&self.in_flight.retry_salt, &req.retry_salt) {
                    return (self, Err(BeltLatchKernelError::RetrySaltMismatch));
                }
                if !belt_latch_digits_eq(&self.in_flight.digits, &req.digits) {
                    return (self, Err(BeltLatchKernelError::DigitsMismatch));
                }
                return (self, Ok(BeltLatchBindOutcome::Replay));
            }
        }
        if req.epoch < self.next_epoch {
            return (self, Err(BeltLatchKernelError::EpochConsumed));
        }
        if req.epoch >= self.capacity_limit {
            return (self, Err(BeltLatchKernelError::Exhausted));
        }
        if req.epoch - self.next_epoch > BELT_LATCH_MAX_EPOCH_JUMP {
            return (self, Err(BeltLatchKernelError::EpochJumpTooLarge));
        }
        if !req.persist_ok {
            let poisoned = BeltLatchKernel {
                capacity_limit: self.capacity_limit,
                next_epoch: self.next_epoch,
                has_in_flight: self.has_in_flight,
                in_flight: self.in_flight,
                wal_poisoned: true,
            };
            return (poisoned, Err(BeltLatchKernelError::WalPersistFailed));
        }
        let next = BeltLatchKernel {
            capacity_limit: self.capacity_limit,
            next_epoch: req.epoch + 1,
            has_in_flight: true,
            in_flight: BeltLatchKernelRecord {
                epoch: req.epoch,
                msg_digest: req.msg_digest,
                retry_salt: req.retry_salt,
                digits: req.digits,
            },
            wal_poisoned: false,
        };
        (next, Ok(BeltLatchBindOutcome::Fresh))
    }
}
