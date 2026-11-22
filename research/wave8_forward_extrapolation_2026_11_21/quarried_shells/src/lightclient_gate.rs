//! `S11`-hardened Electra & CometBFT light-client header admission gates, SSZ Merkle branch
//! verification, two-level ICS-23 Cosmos `bank` membership envelope verification, and sealed
//! `ProvenForeignHolding` construction (closing `S8` and `S11`).
//!
//! Quarried cleanly from `breadstuffs/eth-lightclient/src/{lib.rs,ssz.rs,finality.rs,store.rs}`
//! and `breadstuffs/cosmos-lightclient/src/{lib.rs,bank.rs,verified_gate.rs}` with zero legacy
//! crate dependencies.

// ---------------------------------------------------------------------------
// Pure-Rust FIPS 180-4 SHA-256 (zero external crate dependency)
// ---------------------------------------------------------------------------

const SHA256_K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

const SHA256_H0: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// Compute FIPS 180-4 SHA-256 of `data`.
pub fn sha256(data: &[u8]) -> [u8; 32] {
    let mut h = SHA256_H0;
    let bit_len = (data.len() as u64).wrapping_mul(8);
    let mut padded = Vec::with_capacity((data.len() + 9 + 63) & !63);
    padded.extend_from_slice(data);
    padded.push(0x80);
    while (padded.len() % 64) != 56 {
        padded.push(0);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());

    for block in padded.chunks_exact(64) {
        let mut w = [0u32; 64];
        for i in 0..16 {
            w[i] = u32::from_be_bytes([
                block[4 * i],
                block[4 * i + 1],
                block[4 * i + 2],
                block[4 * i + 3],
            ]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(SHA256_K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);

            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }
        h[0] = h[0].wrapping_add(a);
        h[1] = h[1].wrapping_add(b);
        h[2] = h[2].wrapping_add(c);
        h[3] = h[3].wrapping_add(d);
        h[4] = h[4].wrapping_add(e);
        h[5] = h[5].wrapping_add(f);
        h[6] = h[6].wrapping_add(g);
        h[7] = h[7].wrapping_add(hh);
    }

    let mut out = [0u8; 32];
    for (i, word) in h.iter().enumerate() {
        out[4 * i..4 * i + 4].copy_from_slice(&word.to_be_bytes());
    }
    out
}

/// `SHA-256(a || b)` — SSZ Merkle internal node hash (`eth-lightclient/src/ssz.rs:18`).
pub fn sha256_pair(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32] {
    let mut buf = [0u8; 64];
    buf[..32].copy_from_slice(a);
    buf[32..].copy_from_slice(b);
    sha256(&buf)
}

/// SSZ `is_valid_merkle_branch` (`eth-lightclient/src/ssz.rs:130`).
pub fn is_valid_merkle_branch(
    leaf: &[u8; 32],
    branch: &[[u8; 32]],
    index: u64,
    root: &[u8; 32],
) -> bool {
    let mut value = *leaf;
    for (i, node) in branch.iter().enumerate() {
        if (index >> i) & 1 == 1 {
            value = sha256_pair(node, &value);
        } else {
            value = sha256_pair(&value, node);
        }
    }
    &value == root
}

// ---------------------------------------------------------------------------
// Electra S11-Hardened Light-Client Header Gate
// ---------------------------------------------------------------------------

pub const SYNC_COMMITTEE_SIZE: usize = 512;
pub const SLOTS_PER_SYNC_COMMITTEE_PERIOD: u64 = 8192;
pub const FINALIZED_ROOT_DEPTH_ALTAIR: usize = 6;
pub const FINALIZED_ROOT_DEPTH_ELECTRA: usize = 7;
pub const FINALIZED_ROOT_SUBTREE_INDEX: u64 = 41;
pub const EXECUTION_PAYLOAD_DEPTH: usize = 4;
pub const EXECUTION_PAYLOAD_SUBTREE_INDEX: u64 = 9;

/// Derive the Ethereum sync-committee period directly from the slot (closing `S11`).
pub fn period_of_slot(slot: u64) -> u64 {
    slot / SLOTS_PER_SYNC_COMMITTEE_PERIOD
}

/// Domain-separated 32-bit fork digest binding `(chain_id, fork_version, genesis_validators_root)`.
pub fn compute_fork_digest(
    chain_id: u64,
    fork_version: [u8; 4],
    genesis_validators_root: &[u8; 32],
) -> u32 {
    let mut preimage = Vec::with_capacity(64);
    preimage.extend_from_slice(b"OBEND.LC.ETH.FORK_DIGEST/v1");
    preimage.extend_from_slice(&chain_id.to_be_bytes());
    preimage.extend_from_slice(&fork_version);
    preimage.extend_from_slice(genesis_validators_root);
    let d = sha256(&preimage);
    u32::from_be_bytes([d[0], d[1], d[2], d[3]])
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EthTrustAnchor {
    pub expected_chain_id: u64,
    pub expected_fork_digest: u32,
    pub current_period: u64,
    pub trusted_attested_slot: u64,
    pub trusted_finalized_slot: u64,
    pub max_staleness: u64,
    pub max_clock_drift: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EthHeaderUpdate {
    pub chain_id: u64,
    pub fork_digest: u32,
    pub attested_slot: u64,
    pub signature_slot: u64,
    pub finalized_slot: u64,
    pub attested_time: u64,
    pub committee_len: usize,
    pub bits_len: usize,
    pub participant_count: usize,
    pub bls_agg_ok: bool,
    pub attested_state_root: [u8; 32],
    pub finalized_beacon_root: [u8; 32],
    pub finality_branch: Vec<[u8; 32]>,
    pub finalized_body_root: [u8; 32],
    pub execution_payload_root: [u8; 32],
    pub execution_branch: Vec<[u8; 32]>,
    pub execution_state_root: [u8; 32],
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EthGateError {
    ChainIdMismatch,
    ForkDigestMismatch,
    PeriodMismatch,
    FutureSlotSpoof,
    FinalizedAfterAttested,
    FinalizedHeightRollback,
    NonMonotonicAttestedSlot,
    StaleHeader,
    FutureTimestampSpoof,
    WrongCommitteeSize,
    WrongBitfieldLength,
    ZeroParticipants,
    InsufficientParticipation,
    BadBlsSignature,
    BadFinalityBranch,
    BadExecutionBranch,
}

/// Sealed, unforgeable verified Ethereum finalized header (private fields; only
/// [`verify_eth_header_s11`] can construct one — closing `S8`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedEthHeader {
    chain_id: u64,
    fork_digest: u32,
    attested_slot: u64,
    signature_slot: u64,
    finalized_slot: u64,
    execution_state_root: [u8; 32],
}

impl VerifiedEthHeader {
    pub fn chain_id(&self) -> u64 {
        self.chain_id
    }
    pub fn fork_digest(&self) -> u32 {
        self.fork_digest
    }
    pub fn attested_slot(&self) -> u64 {
        self.attested_slot
    }
    pub fn signature_slot(&self) -> u64 {
        self.signature_slot
    }
    pub fn finalized_slot(&self) -> u64 {
        self.finalized_slot
    }
    pub fn execution_state_root(&self) -> [u8; 32] {
        self.execution_state_root
    }
}

/// `S11`-hardened Ethereum Electra light-client header admission gate with real SSZ Merkle
/// branch checks, mirroring `Minidregg.Assurance.LightClientAndViewLens.verifyEthHeaderS11`.
pub fn verify_eth_header_s11(
    anchor: &EthTrustAnchor,
    u: &EthHeaderUpdate,
    host_now: u64,
) -> Result<VerifiedEthHeader, EthGateError> {
    if u.chain_id != anchor.expected_chain_id {
        return Err(EthGateError::ChainIdMismatch);
    }
    if u.fork_digest != anchor.expected_fork_digest {
        return Err(EthGateError::ForkDigestMismatch);
    }
    if u.signature_slot < u.attested_slot {
        return Err(EthGateError::FutureSlotSpoof);
    }
    if period_of_slot(u.signature_slot) != anchor.current_period {
        return Err(EthGateError::PeriodMismatch);
    }
    if u.attested_slot < u.finalized_slot {
        return Err(EthGateError::FinalizedAfterAttested);
    }
    if u.finalized_slot < anchor.trusted_finalized_slot {
        return Err(EthGateError::FinalizedHeightRollback);
    }
    if u.attested_slot <= anchor.trusted_attested_slot {
        return Err(EthGateError::NonMonotonicAttestedSlot);
    }
    if host_now > u.attested_time.saturating_add(anchor.max_staleness) {
        return Err(EthGateError::StaleHeader);
    }
    if u.attested_time > host_now.saturating_add(anchor.max_clock_drift) {
        return Err(EthGateError::FutureTimestampSpoof);
    }
    if u.committee_len != SYNC_COMMITTEE_SIZE {
        return Err(EthGateError::WrongCommitteeSize);
    }
    if u.bits_len != SYNC_COMMITTEE_SIZE {
        return Err(EthGateError::WrongBitfieldLength);
    }
    if u.participant_count == 0 {
        return Err(EthGateError::ZeroParticipants);
    }
    if u.participant_count.saturating_mul(3) < SYNC_COMMITTEE_SIZE * 2 {
        return Err(EthGateError::InsufficientParticipation);
    }
    if !u.bls_agg_ok {
        return Err(EthGateError::BadBlsSignature);
    }
    let fin_depth_ok = u.finality_branch.len() == FINALIZED_ROOT_DEPTH_ALTAIR
        || u.finality_branch.len() == FINALIZED_ROOT_DEPTH_ELECTRA;
    let fin_branch_ok = fin_depth_ok
        && is_valid_merkle_branch(
            &u.finalized_beacon_root,
            &u.finality_branch,
            FINALIZED_ROOT_SUBTREE_INDEX,
            &u.attested_state_root,
        );
    if !fin_branch_ok {
        return Err(EthGateError::BadFinalityBranch);
    }
    let exec_branch_ok = u.execution_branch.len() == EXECUTION_PAYLOAD_DEPTH
        && is_valid_merkle_branch(
            &u.execution_payload_root,
            &u.execution_branch,
            EXECUTION_PAYLOAD_SUBTREE_INDEX,
            &u.finalized_body_root,
        );
    if !exec_branch_ok {
        return Err(EthGateError::BadExecutionBranch);
    }
    Ok(VerifiedEthHeader {
        chain_id: u.chain_id,
        fork_digest: u.fork_digest,
        attested_slot: u.attested_slot,
        signature_slot: u.signature_slot,
        finalized_slot: u.finalized_slot,
        execution_state_root: u.execution_state_root,
    })
}

// ---------------------------------------------------------------------------
// CometBFT S11-Hardened Light-Client Gate + Two-Level ICS-23 Envelope Verifier
// ---------------------------------------------------------------------------

pub const COSMOS_CHAIN_TAG: u8 = 2;
pub const EVM_CHAIN_TAG: u8 = 1;
pub const BANK_STORE_KEY: &[u8] = b"bank";
pub const BALANCES_PREFIX: u8 = 0x02;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CometTrustAnchor {
    pub expected_chain_id: String,
    pub expected_fork_digest: u32,
    pub trusted_height: u64,
    pub trusted_header_time: u64,
    pub trusting_period: u64,
    pub max_staleness: u64,
    pub max_clock_drift: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CometHeaderUpdate {
    pub chain_id: String,
    pub fork_digest: u32,
    pub height: u64,
    pub header_time: u64,
    pub app_hash: [u8; 32],
    pub epoch_bind_ok: bool,
    pub self_bind_ok: bool,
    pub commit_matches_header: bool,
    pub total_power: u64,
    pub signed_power: u64,
    pub trusted_total_power: u64,
    pub trusted_signed_power: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CometAdvanceMode {
    Adjacent,
    Skipping,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CometGateError {
    ChainIdMismatch,
    ForkDigestMismatch,
    NonIncreasingHeight,
    TrustedStateExpired,
    StaleHeader,
    NonMonotonicTime,
    FutureTimestampSpoof,
    BadCommitBinding,
    BadSelfBinding,
    ZeroTotalPower,
    InsufficientVotingPower,
    BadEpochBinding,
    ZeroTrustedPower,
    InsufficientTrustOverlap,
}

/// Sealed, unforgeable verified CometBFT header (private fields; only
/// [`verify_comet_header_s11`] can construct one).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedCometHeader {
    chain_id: String,
    fork_digest: u32,
    height: u64,
    header_time: u64,
    app_hash: [u8; 32],
    mode: CometAdvanceMode,
}

impl VerifiedCometHeader {
    pub fn chain_id(&self) -> &str {
        &self.chain_id
    }
    pub fn fork_digest(&self) -> u32 {
        self.fork_digest
    }
    pub fn height(&self) -> u64 {
        self.height
    }
    pub fn header_time(&self) -> u64 {
        self.header_time
    }
    pub fn app_hash(&self) -> [u8; 32] {
        self.app_hash
    }
    pub fn mode(&self) -> CometAdvanceMode {
        self.mode
    }
}

/// `S11`-hardened CometBFT adjacent & skipping header admission gate, mirroring
/// `Minidregg.Assurance.LightClientAndViewLens.verifyCometHeaderS11`.
pub fn verify_comet_header_s11(
    anchor: &CometTrustAnchor,
    u: &CometHeaderUpdate,
    host_now: u64,
) -> Result<VerifiedCometHeader, CometGateError> {
    if u.chain_id != anchor.expected_chain_id {
        return Err(CometGateError::ChainIdMismatch);
    }
    if u.fork_digest != anchor.expected_fork_digest {
        return Err(CometGateError::ForkDigestMismatch);
    }
    if u.height <= anchor.trusted_height {
        return Err(CometGateError::NonIncreasingHeight);
    }
    if host_now >= anchor.trusted_header_time.saturating_add(anchor.trusting_period) {
        return Err(CometGateError::TrustedStateExpired);
    }
    if host_now > u.header_time.saturating_add(anchor.max_staleness) {
        return Err(CometGateError::StaleHeader);
    }
    if u.header_time <= anchor.trusted_header_time {
        return Err(CometGateError::NonMonotonicTime);
    }
    if u.header_time > host_now.saturating_add(anchor.max_clock_drift) {
        return Err(CometGateError::FutureTimestampSpoof);
    }
    if !u.commit_matches_header {
        return Err(CometGateError::BadCommitBinding);
    }
    if !u.self_bind_ok {
        return Err(CometGateError::BadSelfBinding);
    }
    if u.total_power == 0 {
        return Err(CometGateError::ZeroTotalPower);
    }
    if (u.signed_power as u128) * 3 <= (u.total_power as u128) * 2 {
        return Err(CometGateError::InsufficientVotingPower);
    }
    let mode = if u.height == anchor.trusted_height.saturating_add(1) {
        if !u.epoch_bind_ok {
            return Err(CometGateError::BadEpochBinding);
        }
        CometAdvanceMode::Adjacent
    } else {
        if u.trusted_total_power == 0 {
            return Err(CometGateError::ZeroTrustedPower);
        }
        if (u.trusted_signed_power as u128) * 3 <= (u.trusted_total_power as u128) {
            return Err(CometGateError::InsufficientTrustOverlap);
        }
        CometAdvanceMode::Skipping
    };
    Ok(VerifiedCometHeader {
        chain_id: u.chain_id.clone(),
        fork_digest: u.fork_digest,
        height: u.height,
        header_time: u.header_time,
        app_hash: u.app_hash,
        mode,
    })
}

// ---------------------------------------------------------------------------
// Two-Level ICS-23 Existence Proof Envelope & Sealed ProvenForeignHolding (S8)
// ---------------------------------------------------------------------------

/// ICS-23 leaf hashing operation (IAVL / Tendermint simple-merkle SHA-256 layout):
/// `SHA-256(prefix || varint(key.len()) || key || varint(val_bytes.len()) || val_bytes)`
/// where `val_bytes = SHA-256(value)` when `prehash_value` is true.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ics23LeafOp {
    pub prefix: Vec<u8>,
    pub prehash_value: bool,
}

/// ICS-23 inner-node hashing operation: `SHA-256(prefix || child_hash || suffix)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ics23InnerOp {
    pub prefix: Vec<u8>,
    pub suffix: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ics23ExistenceProof {
    pub key: Vec<u8>,
    pub value: Vec<u8>,
    pub leaf: Ics23LeafOp,
    pub path: Vec<Ics23InnerOp>,
}

/// Two-level Cosmos multistore proof: `key -> value` inside `store_key` (`bank`) root,
/// and `store_key -> store_root` inside `header.app_hash`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ics23TwoLevelProof {
    pub store_key: Vec<u8>,
    pub store_root: [u8; 32],
    pub sub_proof: Ics23ExistenceProof,
    pub root_proof: Ics23ExistenceProof,
}

fn push_uvarint(buf: &mut Vec<u8>, mut n: usize) {
    loop {
        let mut byte = (n & 0x7f) as u8;
        n >>= 7;
        if n != 0 {
            byte |= 0x80;
        }
        buf.push(byte);
        if n == 0 {
            break;
        }
    }
}

pub fn compute_ics23_root(proof: &Ics23ExistenceProof) -> [u8; 32] {
    let mut leaf_preimage = Vec::with_capacity(proof.leaf.prefix.len() + proof.key.len() + 48);
    leaf_preimage.extend_from_slice(&proof.leaf.prefix);
    push_uvarint(&mut leaf_preimage, proof.key.len());
    leaf_preimage.extend_from_slice(&proof.key);
    if proof.leaf.prehash_value {
        let vh = sha256(&proof.value);
        push_uvarint(&mut leaf_preimage, vh.len());
        leaf_preimage.extend_from_slice(&vh);
    } else {
        push_uvarint(&mut leaf_preimage, proof.value.len());
        leaf_preimage.extend_from_slice(&proof.value);
    }
    let mut acc = sha256(&leaf_preimage);
    for inner in &proof.path {
        let mut buf = Vec::with_capacity(inner.prefix.len() + 32 + inner.suffix.len());
        buf.extend_from_slice(&inner.prefix);
        buf.extend_from_slice(&acc);
        buf.extend_from_slice(&inner.suffix);
        acc = sha256(&buf);
    }
    acc
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnvelopeError {
    StoreKeyMismatch,
    SubProofRootMismatch,
    MultiStoreRootMismatch,
    NotBankStore,
    NotBalanceKey,
    MalformedKey,
    BadAddressLength(usize),
    BadDenom,
    MalformedAmount,
    AmountOverflow,
}

/// Verify a two-level ICS-23 existence proof against an authenticated `app_hash`.
pub fn verify_two_level_ics23(
    expected_app_hash: &[u8; 32],
    proof: &Ics23TwoLevelProof,
) -> Result<(), EnvelopeError> {
    if proof.root_proof.key != proof.store_key {
        return Err(EnvelopeError::StoreKeyMismatch);
    }
    if proof.root_proof.value.as_slice() != proof.store_root.as_slice() {
        return Err(EnvelopeError::SubProofRootMismatch);
    }
    if compute_ics23_root(&proof.sub_proof) != proof.store_root {
        return Err(EnvelopeError::SubProofRootMismatch);
    }
    if &compute_ics23_root(&proof.root_proof) != expected_app_hash {
        return Err(EnvelopeError::MultiStoreRootMismatch);
    }
    Ok(())
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedBankBalance {
    pub address: Vec<u8>,
    pub denom: String,
    pub amount: u128,
}

/// Fail-closed Cosmos SDK `bank` balances-prefix (`0x02 || len || addr || denom`) decoder,
/// quarried from `breadstuffs/cosmos-lightclient/src/bank.rs`.
pub fn decode_bank_balance_kv(
    store_key: &[u8],
    key: &[u8],
    value: &[u8],
) -> Result<DecodedBankBalance, EnvelopeError> {
    if store_key != BANK_STORE_KEY {
        return Err(EnvelopeError::NotBankStore);
    }
    if key.len() < 3 {
        return Err(EnvelopeError::MalformedKey);
    }
    if key[0] != BALANCES_PREFIX {
        return Err(EnvelopeError::NotBalanceKey);
    }
    let addr_len = key[1] as usize;
    if addr_len == 0 || addr_len > 32 {
        return Err(EnvelopeError::BadAddressLength(addr_len));
    }
    if key.len() < 2 + addr_len + 3 {
        return Err(EnvelopeError::MalformedKey);
    }
    let address = key[2..2 + addr_len].to_vec();
    let denom_bytes = &key[2 + addr_len..];
    let denom = std::str::from_utf8(denom_bytes)
        .map_err(|_| EnvelopeError::BadDenom)?
        .to_owned();
    let mut chars = denom.chars();
    let first_ok = chars.next().is_some_and(|c| c.is_ascii_alphabetic());
    let rest_ok = denom.len() >= 3
        && denom.len() <= 128
        && chars.all(|c| c.is_ascii_alphanumeric() || matches!(c, '/' | ':' | '.' | '_' | '-'));
    if !first_ok || !rest_ok {
        return Err(EnvelopeError::BadDenom);
    }
    if value.is_empty() || !value.iter().all(|b| b.is_ascii_digit()) {
        return Err(EnvelopeError::MalformedAmount);
    }
    if value.len() > 1 && value[0] == b'0' {
        return Err(EnvelopeError::MalformedAmount);
    }
    let s = std::str::from_utf8(value).map_err(|_| EnvelopeError::MalformedAmount)?;
    let amount = s.parse::<u128>().map_err(|_| EnvelopeError::AmountOverflow)?;
    Ok(DecodedBankBalance {
        address,
        denom,
        amount,
    })
}

/// Domain-separated 32-byte asset ID (`cosmos-lightclient/src/bank.rs:160`).
pub fn cosmos_denom_asset_id(denom: &str) -> [u8; 32] {
    let mut buf = Vec::with_capacity(22 + denom.len());
    buf.extend_from_slice(b"dregg-cosmos-denom-v1:");
    buf.extend_from_slice(denom.as_bytes());
    sha256(&buf)
}

/// Sealed, light-client-proven foreign holding (`S8` closed: private fields, `chain_id` derived
/// strictly from the verified header rather than caller input, and `consensus_proven` is
/// unconditionally `true` by construction).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenForeignHolding {
    chain_tag: u8,
    chain_id: String,
    holder: [u8; 32],
    asset: [u8; 32],
    amount: u128,
    snapshot_height: u64,
    consensus_proven: bool,
}

impl ProvenForeignHolding {
    pub fn chain_tag(&self) -> u8 {
        self.chain_tag
    }
    pub fn chain_id(&self) -> &str {
        &self.chain_id
    }
    pub fn holder(&self) -> [u8; 32] {
        self.holder
    }
    pub fn asset(&self) -> [u8; 32] {
        self.asset
    }
    pub fn amount(&self) -> u128 {
        self.amount
    }
    pub fn snapshot_height(&self) -> u64 {
        self.snapshot_height
    }
    pub fn consensus_proven(&self) -> bool {
        self.consensus_proven
    }
}

/// Verify a two-level ICS-23 `bank` balance proof under a [`VerifiedCometHeader`] and mint a
/// sealed [`ProvenForeignHolding`] bound to the verified header's own `chain_id` and `height`.
pub fn verify_cosmos_bank_balance_envelope(
    header: &VerifiedCometHeader,
    proof: &Ics23TwoLevelProof,
) -> Result<ProvenForeignHolding, EnvelopeError> {
    verify_two_level_ics23(&header.app_hash(), proof)?;
    let bal = decode_bank_balance_kv(
        &proof.store_key,
        &proof.sub_proof.key,
        &proof.sub_proof.value,
    )?;
    let mut holder = [0u8; 32];
    holder[32 - bal.address.len()..].copy_from_slice(&bal.address);
    Ok(ProvenForeignHolding {
        chain_tag: COSMOS_CHAIN_TAG,
        chain_id: header.chain_id().to_owned(),
        holder,
        asset: cosmos_denom_asset_id(&bal.denom),
        amount: bal.amount,
        snapshot_height: header.height(),
        consensus_proven: true,
    })
}
