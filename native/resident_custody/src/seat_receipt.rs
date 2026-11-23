//! DreggNet v1 seat transfer receipts, byte-compatible with `dreggnet-billing::handoff`.
//!
//! Ground truth is DreggNet `1d4fad6` (`billing/src/handoff.rs` and the codecs it uses from
//! `billing/src/reserve/mod.rs`). The types, field order, serde attributes, domains, check
//! order and refusal variants below are that code's. The `dreggnet_v1_golden_vector` test
//! reproduces the SHA-256 that DreggNet's own
//! `v1_wire_encoding_is_byte_identical_to_the_original_verifier` pins for its fixture, so a
//! receipt sealed here verifies there and conversely.
//!
//! Only the two transferable backings exist on the wire. DreggNet's exporter refuses a seat
//! with any disputed or reversed payment (`SeatNotTransferable`), and a receipt naming another
//! backing does not decode (`Malformed`).
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};
use std::collections::BTreeSet;
use std::fmt;

pub type Bytes32 = [u8; 32];

const SEAT_ROOT_DOMAIN: &[u8] = b"dreggnet-seat-handoff-v1\0";
const MINT_COMMITMENT_DOMAIN: &[u8] = b"dreggnet-stripe-mirror-mint-v1\0";

/// The Stripe event types that fund credit.
pub const FUNDING_EVENT_TYPES: [&str; 2] = ["payment_intent.succeeded", "charge.succeeded"];

pub fn sha256(bytes: &[u8]) -> Bytes32 {
    Sha256::digest(bytes).into()
}

/// BLAKE3 key derivation with context `dregg-stripe-payment-v1` over `asset ‖ payment_intent_id`.
pub fn payment_nullifier(asset: &Bytes32, payment_intent_id: &str) -> Bytes32 {
    let mut h = blake3::Hasher::new_derive_key("dregg-stripe-payment-v1");
    h.update(asset);
    h.update(payment_intent_id.as_bytes());
    *h.finalize().as_bytes()
}

fn commitment(domain: &[u8], value: &impl Serialize) -> serde_json::Result<Bytes32> {
    let mut h = Sha256::new();
    h.update(domain);
    h.update(serde_json::to_vec(value)?);
    Ok(h.finalize().into())
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PaymentClaim {
    pub event_id: String,
    pub event_type: String,
    pub payment_intent_id: String,
    pub customer_seat: Bytes32,
    pub amount_minor: u64,
    pub currency: String,
    pub payload_sha256: Bytes32,
    pub stripe_timestamp: u64,
    pub stripe_v1: Bytes32,
    pub mint_idempotency_key: Bytes32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MintEffect {
    pub target: Bytes32,
    pub slot: u32,
    pub amount: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MintReceipt {
    pub target: Bytes32,
    pub slot: u32,
    pub amount: u64,
    pub commitment: Bytes32,
}

impl MintReceipt {
    pub fn new(claim: &PaymentClaim, effect: MintEffect) -> serde_json::Result<Self> {
        let MintEffect {
            target,
            slot,
            amount,
        } = effect;
        Ok(Self {
            target,
            slot,
            amount,
            commitment: commitment(MINT_COMMITMENT_DOMAIN, &(claim, target, slot, amount))?,
        })
    }
    pub fn expected_effect(claim: &PaymentClaim) -> MintEffect {
        MintEffect {
            target: claim.customer_seat,
            slot: 0,
            amount: claim.amount_minor,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CreditBacking {
    Provisional,
    Settled { deposit_sha256: Bytes32 },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TransferredCredit {
    pub claim: PaymentClaim,
    pub mint: MintReceipt,
    pub remaining_minor: u64,
    pub backing: CreditBacking,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SeatTransfer {
    pub source_operator_id: Bytes32,
    pub target_operator_id: Bytes32,
    pub transfer_epoch: u64,
    pub asset: Bytes32,
    pub customer_seat: Bytes32,
    pub credits: Vec<TransferredCredit>,
    pub unsettled_provisional_minor: u64,
    pub reversal_deficit_minor: u64,
    pub operator_reserve_cap_minor: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SeatTransferReceipt {
    pub transfer: SeatTransfer,
    pub seat_root: Bytes32,
    pub signature: String,
}

#[derive(Clone, Copy, Debug)]
pub struct AdmissionPolicy<'a> {
    pub issuer: Bytes32,
    pub target: Bytes32,
    pub asset: Bytes32,
    pub currency: &'a str,
    pub epoch_floor: u64,
    pub max_reserve_cap_minor: u64,
}

/// `TransferError`, variant for variant.
#[derive(Debug)]
pub enum TransferError {
    Malformed(serde_json::Error),
    SignerMismatch,
    WrongOperator,
    WrongAsset,
    StaleEpoch { epoch: u64, floor: u64 },
    SeatRootMismatch,
    InvalidIssuerKey,
    InvalidSignature,
    InvalidTargetKey,
    EmptySeat,
    SeatOrCurrencyMismatch,
    InvalidPayment,
    InvalidCredit,
    MintCommitment,
    Overflow,
    EmptyBalance,
    UnderstatedExposure,
    UnbackedReserve,
}

impl From<serde_json::Error> for TransferError {
    fn from(e: serde_json::Error) -> Self {
        Self::Malformed(e)
    }
}

impl fmt::Display for TransferError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Malformed(e) => write!(f, "malformed seat transfer receipt: {e}"),
            Self::SignerMismatch => f.write_str("signing key is not the transfer's source operator"),
            Self::WrongOperator => f.write_str("wrong handoff operator"),
            Self::WrongAsset => f.write_str("wrong asset"),
            Self::StaleEpoch { epoch, floor } => write!(f, "stale epoch {epoch} (floor {floor})"),
            Self::SeatRootMismatch => f.write_str("seat root mismatch"),
            Self::InvalidIssuerKey => f.write_str("invalid issuer key"),
            Self::InvalidSignature => f.write_str("invalid issuer signature"),
            Self::InvalidTargetKey => f.write_str("invalid target key"),
            Self::EmptySeat => f.write_str("empty seat"),
            Self::SeatOrCurrencyMismatch => f.write_str("seat or currency mismatch"),
            Self::InvalidPayment => f.write_str("missing or repeated payment"),
            Self::InvalidCredit => f.write_str("invalid credit"),
            Self::MintCommitment => f.write_str("invalid substrate mint commitment"),
            Self::Overflow => f.write_str("arithmetic overflow"),
            Self::EmptyBalance => f.write_str("empty balance"),
            Self::UnderstatedExposure => f.write_str("understated provisional exposure"),
            Self::UnbackedReserve => f.write_str("unbacked reserve claim"),
        }
    }
}

impl std::error::Error for TransferError {}

impl SeatTransfer {
    pub fn seat_root(&self) -> Result<Bytes32, TransferError> {
        Ok(commitment(SEAT_ROOT_DOMAIN, self)?)
    }
}

impl SeatTransferReceipt {
    pub fn seal(transfer: SeatTransfer, signer: &SigningKey) -> Result<Self, TransferError> {
        if transfer.source_operator_id != signer.verifying_key().to_bytes() {
            return Err(TransferError::SignerMismatch);
        }
        let seat_root = transfer.seat_root()?;
        Ok(Self {
            transfer,
            seat_root,
            signature: hex::encode(signer.sign(&seat_root).to_bytes()),
        })
    }

    pub fn to_bytes(&self) -> Result<Vec<u8>, TransferError> {
        Ok(serde_json::to_vec(self)?)
    }

    pub fn verify(bytes: &[u8], policy: &AdmissionPolicy<'_>) -> Result<Self, TransferError> {
        let receipt: Self = serde_json::from_slice(bytes)?;
        receipt.check(policy)?;
        Ok(receipt)
    }

    fn check(&self, policy: &AdmissionPolicy<'_>) -> Result<(), TransferError> {
        let t = &self.transfer;
        if t.source_operator_id != policy.issuer
            || t.target_operator_id != policy.target
            || policy.target == policy.issuer
        {
            return Err(TransferError::WrongOperator);
        }
        if t.asset != policy.asset {
            return Err(TransferError::WrongAsset);
        }
        if t.transfer_epoch <= policy.epoch_floor {
            return Err(TransferError::StaleEpoch {
                epoch: t.transfer_epoch,
                floor: policy.epoch_floor,
            });
        }
        if self.seat_root != t.seat_root()? {
            return Err(TransferError::SeatRootMismatch);
        }
        let issuer =
            VerifyingKey::from_bytes(&policy.issuer).map_err(|_| TransferError::InvalidIssuerKey)?;
        let mut signature = [0u8; 64];
        hex::decode_to_slice(&self.signature, &mut signature)
            .map_err(|_| TransferError::InvalidSignature)?;
        issuer
            .verify_strict(&self.seat_root, &Signature::from_bytes(&signature))
            .map_err(|_| TransferError::InvalidSignature)?;
        if VerifyingKey::from_bytes(&policy.target).map_or(true, |k| k.is_weak()) {
            return Err(TransferError::InvalidTargetKey);
        }
        if t.credits.is_empty() {
            return Err(TransferError::EmptySeat);
        }
        let mut intents = BTreeSet::new();
        let mut events = BTreeSet::new();
        let mut provisional = 0u64;
        let mut remaining = 0u64;
        for credit in &t.credits {
            let c = &credit.claim;
            if c.customer_seat != t.customer_seat || c.currency != policy.currency {
                return Err(TransferError::SeatOrCurrencyMismatch);
            }
            if !FUNDING_EVENT_TYPES.contains(&c.event_type.as_str())
                || c.event_id.is_empty()
                || c.payment_intent_id.is_empty()
                || !intents.insert(&c.payment_intent_id)
                || !events.insert(&c.event_id)
            {
                return Err(TransferError::InvalidPayment);
            }
            if c.amount_minor == 0 || credit.remaining_minor > c.amount_minor {
                return Err(TransferError::InvalidCredit);
            }
            if payment_nullifier(&t.asset, &c.payment_intent_id) != c.mint_idempotency_key
                || credit.mint != MintReceipt::new(c, MintReceipt::expected_effect(c))?
            {
                return Err(TransferError::MintCommitment);
            }
            if credit.backing == CreditBacking::Provisional {
                provisional = provisional
                    .checked_add(c.amount_minor)
                    .ok_or(TransferError::Overflow)?;
            }
            remaining = remaining
                .checked_add(credit.remaining_minor)
                .ok_or(TransferError::Overflow)?;
        }
        if remaining == 0 {
            return Err(TransferError::EmptyBalance);
        }
        if provisional > t.unsettled_provisional_minor {
            return Err(TransferError::UnderstatedExposure);
        }
        if t.operator_reserve_cap_minor > policy.max_reserve_cap_minor
            || t.unsettled_provisional_minor
                .checked_add(t.reversal_deficit_minor)
                .is_none_or(|exposure| exposure > t.operator_reserve_cap_minor)
        {
            return Err(TransferError::UnbackedReserve);
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ASSET: Bytes32 = [3; 32];
    const SEAT: Bytes32 = [4; 32];

    fn source_key() -> SigningKey {
        SigningKey::from_bytes(&[11; 32])
    }
    fn target() -> Bytes32 {
        SigningKey::from_bytes(&[22; 32]).verifying_key().to_bytes()
    }
    fn claim(pi: &str, event: &str, amount: u64) -> PaymentClaim {
        PaymentClaim {
            event_id: event.into(),
            event_type: "payment_intent.succeeded".into(),
            payment_intent_id: pi.into(),
            customer_seat: SEAT,
            amount_minor: amount,
            currency: "usd".into(),
            payload_sha256: sha256(b"payload"),
            stripe_timestamp: 1,
            stripe_v1: sha256(b"v1"),
            mint_idempotency_key: payment_nullifier(&ASSET, pi),
        }
    }
    fn credit(claim: PaymentClaim, remaining_minor: u64, backing: CreditBacking) -> TransferredCredit {
        TransferredCredit {
            mint: MintReceipt::new(&claim, MintReceipt::expected_effect(&claim)).unwrap(),
            claim,
            remaining_minor,
            backing,
        }
    }
    /// DreggNet `billing/tests/handoff.rs::transfer`, field for field.
    fn transfer() -> SeatTransfer {
        SeatTransfer {
            source_operator_id: source_key().verifying_key().to_bytes(),
            target_operator_id: target(),
            transfer_epoch: 2,
            asset: ASSET,
            customer_seat: SEAT,
            credits: vec![
                credit(claim("pi_x", "evt_x", 75), 50, CreditBacking::Provisional),
                credit(
                    claim("pi_y", "evt_y", 40),
                    40,
                    CreditBacking::Settled {
                        deposit_sha256: sha256(b"bank-deposit-y"),
                    },
                ),
            ],
            unsettled_provisional_minor: 75,
            reversal_deficit_minor: 25,
            operator_reserve_cap_minor: 100,
        }
    }
    fn policy() -> AdmissionPolicy<'static> {
        AdmissionPolicy {
            issuer: source_key().verifying_key().to_bytes(),
            target: target(),
            asset: ASSET,
            currency: "usd",
            epoch_floor: 1,
            max_reserve_cap_minor: 100,
        }
    }

    /// The digest DreggNet pins in `v1_wire_encoding_is_byte_identical_to_the_original_verifier`
    /// (`billing/tests/handoff.rs` at `1d4fad6`) for the receipt its fixture seals.
    #[test]
    fn dreggnet_v1_golden_vector() {
        let bytes = SeatTransferReceipt::seal(transfer(), &source_key())
            .unwrap()
            .to_bytes()
            .unwrap();
        assert_eq!(
            hex::encode(sha256(&bytes)),
            "18a1d5bc50e9b133a5176dd7fb0c8e79bcbccf3600fa1d0a5d4c9308b2895174"
        );
        let receipt = SeatTransferReceipt::verify(&bytes, &policy()).unwrap();
        assert_eq!(receipt.transfer, transfer());
    }

    #[test]
    fn refusals_match_dreggnet_variants() {
        let bytes = SeatTransferReceipt::seal(transfer(), &source_key())
            .unwrap()
            .to_bytes()
            .unwrap();
        let with = |f: fn(&mut AdmissionPolicy<'static>)| {
            let mut p = policy();
            f(&mut p);
            SeatTransferReceipt::verify(&bytes, &p).unwrap_err()
        };
        assert!(matches!(
            with(|p| p.target = SigningKey::from_bytes(&[33; 32]).verifying_key().to_bytes()),
            TransferError::WrongOperator
        ));
        assert!(matches!(with(|p| p.asset = [9; 32]), TransferError::WrongAsset));
        assert!(matches!(
            with(|p| p.epoch_floor = 2),
            TransferError::StaleEpoch { epoch: 2, floor: 2 }
        ));
        assert!(matches!(with(|p| p.currency = "eur"), TransferError::SeatOrCurrencyMismatch));
        assert!(matches!(
            with(|p| p.max_reserve_cap_minor = 99),
            TransferError::UnbackedReserve
        ));
        let text = String::from_utf8(bytes).unwrap();
        let disputed = text.replacen("\"Provisional\"", "\"Disputed\"", 1);
        assert_ne!(disputed, text);
        assert!(matches!(
            SeatTransferReceipt::verify(disputed.as_bytes(), &policy()),
            Err(TransferError::Malformed(_))
        ));
    }
}
