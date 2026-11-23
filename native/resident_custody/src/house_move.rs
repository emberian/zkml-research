//! A resident moving from one operator to another, as one witness-free bundle, and the
//! public verifier that admits it.
//!
//! [`ResidentMigrationPackage`] carries the DreggNet v1 seat receipt the source operator
//! sealed, the quorum-certified parent head, the exact Migrate command, the certified
//! successor head, and the journal header proved inside the successor's world root.
//!
//! [`Follower`] is a public log's own Obend latch over one resident: the 14 words of
//! `stepBeltLatch`, provisioned at genesis and stepped once per certified succession. A
//! package is checked against that latch before any signature, so a forked parent, a drifted
//! policy, a stale or replayed head and a foreign resident are refused with the kernel's own
//! status. The log's durable write is the request's `persistAck`.
//!
//! The billing and custody identities are the same Ed25519 keys: the receipt's source must
//! be the parent's operator and its target the successor's, its `seat_root` must be the
//! certified `seat_payment_claim`, and its seat must be the one derived from the resident's
//! genesis.
use crate::custody_mesh::{
    head_root, latch_state, succession_request, Action, Certificate, Command, Config, Head,
    HeaderOpening, JournalHeader,
};
use crate::obend_latch_abi::{self as obend, RequestWords, StateWords, Status};
use crate::seat_receipt::{AdmissionPolicy, Bytes32, SeatTransferReceipt, TransferError};
use crate::{digest, Digest};
use anyhow::ensure;
use serde::{Deserialize, Serialize};
use std::fmt;

/// The DreggNet customer seat that pays for the resident with this genesis.
pub fn resident_seat(genesis_id: &Digest) -> Bytes32 {
    digest(b"resident seat", &[genesis_id])
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ResidentMigrationPackage {
    /// DreggNet v1 receipt JSON, byte for byte as the source operator sealed it.
    pub seat_receipt: Vec<u8>,
    /// The head the source operator held.
    pub parent: Certificate,
    /// Issuer's exact Migrate grant, the source's exercise and the successor's acceptance.
    pub command: Command,
    /// The successor head. Every vote signs its Obend request with `persistAck = 1`.
    pub succession: Certificate,
    pub header: HeaderOpening,
}

pub(crate) const PACKAGE_LIMIT: u64 = 1 << 20;

/// Refuse a paid offer before consuming its parent if the assembled package could
/// exceed the public decoder's limit. Certificates carry at most one vote per signer.
pub(crate) fn check_package_capacity(
    parent: &Certificate,
    command: &Command,
    receipt: &[u8],
    roster: usize,
) -> anyhow::Result<()> {
    use crate::custody_mesh::{Vote, MAX_HEADER_WIRE};
    let empty = Certificate {
        head: parent.head.clone(),
        votes: vec![],
    };
    let vote = Vote {
        signer: 0,
        signature: vec![0; 64],
    };
    let max = bincode::serialized_size(parent)?
        + bincode::serialized_size(command)?
        + bincode::serialized_size(receipt)?
        + bincode::serialized_size(&empty)?
        + roster as u64 * bincode::serialized_size(&vote)?
        + MAX_HEADER_WIRE;
    ensure!(
        max <= PACKAGE_LIMIT,
        "paid offer exceeds migration package budget"
    );
    Ok(())
}

impl ResidentMigrationPackage {
    pub fn to_bytes(&self) -> anyhow::Result<Vec<u8>> {
        ensure!(
            bincode::serialized_size(self)? <= PACKAGE_LIMIT,
            "migration package exceeds wire limit"
        );
        Ok(bincode::serialize(self)?)
    }
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Refusal> {
        use bincode::Options;
        bincode::DefaultOptions::new()
            .with_fixint_encoding()
            .with_limit(PACKAGE_LIMIT)
            .reject_trailing_bytes()
            .deserialize(bytes)
            .map_err(|e| Refusal::Malformed(e.to_string()))
    }
}

/// What the successor accepts from the billing side, beyond the identities the heads fix.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SeatAdmission {
    pub asset: Bytes32,
    pub currency: String,
    pub epoch_floor: u64,
    pub max_reserve_cap_minor: u64,
}

impl SeatAdmission {
    pub(crate) fn verify_for(
        &self,
        wire: &[u8],
        parent: &Head,
        target: Digest,
        claim: Digest,
    ) -> Result<SeatTransferReceipt, Refusal> {
        let receipt = SeatTransferReceipt::verify(
            wire,
            &AdmissionPolicy {
                issuer: parent.operator_id,
                target,
                asset: self.asset,
                currency: &self.currency,
                epoch_floor: self.epoch_floor,
                max_reserve_cap_minor: self.max_reserve_cap_minor,
            },
        )
        .map_err(Refusal::Seat)?;

        // 4. The receipt is the one the quorum certified, for this resident's seat.
        if receipt.seat_root != claim {
            return Err(Refusal::SeatBinding(
                "receipt seat root is not the certified seat claim",
            ));
        }
        if receipt.transfer.customer_seat != resident_seat(&parent.genesis_id) {
            return Err(Refusal::SeatBinding(
                "seat does not belong to this resident",
            ));
        }

        Ok(receipt)
    }
}

/// Why a certificate or package was not admitted. `Latch` carries the Obend status.
#[derive(Debug)]
pub enum Refusal {
    Malformed(String),
    Latch(Status),
    Certificate(String),
    Command(&'static str),
    Seat(TransferError),
    SeatBinding(&'static str),
    Continuity(&'static str),
    Opening(String),
}

impl fmt::Display for Refusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Malformed(e) => write!(f, "malformed: {e}"),
            Self::Latch(s) => write!(f, "Obend latch refused: {s:?} (code {})", s.code()),
            Self::Certificate(e) => write!(f, "certificate: {e}"),
            Self::Command(e) => write!(f, "command: {e}"),
            Self::Seat(e) => write!(f, "seat receipt: {e}"),
            Self::SeatBinding(e) => write!(f, "seat binding: {e}"),
            Self::Continuity(e) => write!(f, "continuity: {e}"),
            Self::Opening(e) => write!(f, "header opening: {e}"),
        }
    }
}

impl std::error::Error for Refusal {}

#[derive(Clone, Debug)]
pub struct Admitted {
    pub head: Head,
    pub receipt: SeatTransferReceipt,
    pub header: JournalHeader,
}

/// A public log's Obend latch and the head it installed.
pub struct Follower {
    cfg: Config,
    latch: StateWords,
    head: Head,
}

impl Follower {
    /// Provision the latch at the resident's genesis head.
    pub fn genesis(cfg: Config, genesis: &Head) -> anyhow::Result<Self> {
        cfg.validate()?;
        ensure!(
            genesis.epoch == 0
                && genesis.genesis_id == cfg.genesis()
                && genesis.policy_hash == cfg.policy_hash()
                && genesis.operator_id == cfg.first_operator
                && genesis.parent_commitment == [0; 32]
                && genesis.change == [0; 32]
                && genesis.seat_payment_claim == [0; 32]
                && (
                    genesis.output_bits,
                    genesis.output_rank,
                    genesis.journal_cursor
                ) == (0, 0, 0),
            "not this resident's genesis head"
        );
        Ok(Self {
            latch: latch_state(genesis),
            head: genesis.clone(),
            cfg,
        })
    }

    /// Resume from durable state written by an earlier `persist`.
    pub fn recover(cfg: Config, latch: StateWords, head: Head) -> anyhow::Result<Self> {
        cfg.validate()?;
        ensure!(
            latch == latch_state(&head)
                && head.genesis_id == cfg.genesis()
                && head.policy_hash == cfg.policy_hash(),
            "latch and head disagree"
        );
        Ok(Self { cfg, latch, head })
    }

    pub fn latch(&self) -> &StateWords {
        &self.latch
    }
    pub fn head(&self) -> &Head {
        &self.head
    }

    /// The Obend request for `cert`, provided the latch accepts it with `persistAck = 1` and
    /// the quorum signed it.
    fn check(&self, cert: &Certificate) -> Result<RequestWords, Refusal> {
        let record =
            succession_request(&cert.head, true).map_err(|e| Refusal::Malformed(e.to_string()))?;
        let mut trial = self.latch;
        match Status::from_code(obend::step_words(&mut trial, &record)) {
            Some(Status::Accepted) => {}
            Some(refused) => return Err(Refusal::Latch(refused)),
            None => return Err(Refusal::Malformed("unknown Obend status".into())),
        }
        cert.verify(&self.cfg)
            .map_err(|e| Refusal::Certificate(e.to_string()))?;
        Ok(record)
    }

    /// Persist the successor latch words and head, then step the latch with the outcome as
    /// `persistAck`. A failed persist is Obend's `MissingAck` and leaves the latch unchanged.
    fn install(
        &mut self,
        head: &Head,
        mut record: RequestWords,
        persist: impl FnOnce(&StateWords, &Head) -> anyhow::Result<()>,
    ) -> Result<(), Refusal> {
        let mut next = self.latch;
        obend::step_words(&mut next, &record);
        record[obend::request::PERSIST_ACK] = u64::from(persist(&next, head).is_ok());
        match Status::from_code(obend::step_words(&mut self.latch, &record)) {
            Some(Status::Accepted) => {
                debug_assert_eq!(self.latch, next);
                self.head = head.clone();
                Ok(())
            }
            Some(refused) => Err(Refusal::Latch(refused)),
            None => Err(Refusal::Malformed("unknown Obend status".into())),
        }
    }

    /// Follow one certified succession that keeps the operator and seat.
    pub fn follow(
        &mut self,
        cert: &Certificate,
        persist: impl FnOnce(&StateWords, &Head) -> anyhow::Result<()>,
    ) -> Result<(), Refusal> {
        let record = self.check(cert)?;
        if cert.head.operator_id != self.head.operator_id
            || cert.head.seat_payment_claim != self.head.seat_payment_claim
        {
            return Err(Refusal::Continuity(
                "an operator change is admitted only as a migration package",
            ));
        }
        self.install(&cert.head, record, persist)
    }

    /// Admit a migration package over the installed head.
    pub fn admit(
        &mut self,
        admission: &SeatAdmission,
        pkg: &ResidentMigrationPackage,
        persist: impl FnOnce(&StateWords, &Head) -> anyhow::Result<()>,
    ) -> Result<Admitted, Refusal> {
        let (parent, next) = (&pkg.parent.head, &pkg.succession.head);
        // 1. The exact Obend succession over this log's latch, then its quorum.
        let record = self.check(&pkg.succession)?;
        if next.parent_commitment != head_root(parent) {
            return Err(Refusal::Continuity(
                "succession does not extend the packaged parent",
            ));
        }
        if parent.epoch == 0 {
            if *parent != self.head || !pkg.parent.votes.is_empty() {
                return Err(Refusal::Continuity("expected the provisioned genesis"));
            }
        } else {
            pkg.parent
                .verify(&self.cfg)
                .map_err(|e| Refusal::Certificate(e.to_string()))?;
        }

        // 2. The certified change is this Migrate, authorized by issuer, source and successor.
        let cmd = &pkg.command;
        if next.change != cmd.id() || cmd.grant.parent != *parent {
            return Err(Refusal::Command("certified change is not this command"));
        }
        match &cmd.grant.action {
            Action::Migrate {
                successor,
                seat_payment_claim,
            } if *successor == next.operator_id
                && *seat_payment_claim == next.seat_payment_claim => {}
            _ => return Err(Refusal::Command("not the certified Migrate")),
        }
        cmd.authenticate(&self.cfg)
            .map_err(|_| Refusal::Command("Migrate signatures"))?;

        // 3. DreggNet's own admission rules, with the custody identities as issuer and target.
        let receipt = admission.verify_for(
            &pkg.seat_receipt,
            parent,
            next.operator_id,
            next.seat_payment_claim,
        )?;

        // 5. A move carries the resident unchanged: W0 and journal, cursor, exposure ledger.
        if next.state_commitment != parent.state_commitment
            || next.journal_cursor != parent.journal_cursor
        {
            return Err(Refusal::Continuity(
                "migration changed the resident's memory",
            ));
        }
        if (next.output_bits, next.output_rank) != (parent.output_bits, parent.output_rank) {
            return Err(Refusal::Continuity("migration changed the exposure ledger"));
        }

        // 6. The journal header inside the successor's world root.
        let header = pkg
            .header
            .verify(next)
            .map_err(|e| Refusal::Opening(e.to_string()))?;

        // 7. Durable admission, then the latch.
        self.install(next, record, persist)?;
        Ok(Admitted {
            head: next.clone(),
            receipt,
            header,
        })
    }
}

mod log;
pub use log::ResidentLog;
