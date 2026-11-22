# w10 — Real Asymmetric Crypto & Spec-Exact Mainnet/Silicon Wire Gates in `obend`

**Branch / Worktree:** `w10-real-crypto-curves` (`crates/obend-oracles-e2ee`, `crates/obend-lightclients`)
**Constraints:** `#![forbid(unsafe_code)]`, **zero external crate dependencies** in both crates, zero boolean signature flags (`sig_verified`, `bls_agg_ok`, `*_sig_ok`), zero synthetic `OBEND.LC.*` / `OBEND.TEE.*` signed wire preimages.

## 1. Pure-Rust Asymmetric Primitives (`0` External Crates)

- **Limb & Montgomery Arithmetic (`bigint.rs`, `sha512.rs`):** `[DERIVED]` Fixed-width `[u64; N]` CIOS Montgomery multiplication, inversion, strict canonical big-endian field/scalar decoding (`from_be_strict` rejecting `>= p` and `r = 0` / `s >= n`), and FIPS 180-4 SHA-384 / SHA-512 + RFC 4231 HMAC.
- **ECDSA P-256 & P-384 + RSA-2048/3072/4096 + Ed25519 (`obend-oracles-e2ee/src/{curves,rsa,ed25519}.rs`):**
  - `[SOURCE]` FIPS 186-5 Short-Weierstrass Jacobian `secp256r1` & `secp384r1` (`on_curve`, `PointAtInfinity`, strict DER `Ecdsa-Sig-Value` & fixed-width IEEE P1363 `r || s`); RFC 8017 §8.1.2 / §8.2.2 `RSASSA-PKCS1-v1_5` (exact `EM` comparison blocking Bleichenbacher `e = 3` trailing-garbage forgery) and `RSASSA-PSS` (`MGF1`, `sLen = hLen`, RFC 4055 §2.1 `NULL`/absent SHA-2 params & explicit/default `trailerField = 1`); RFC 8032 §5.1.7 `Ed25519` `verify_strict` (canonical `y < p`, canonical `S < L`, `[8]A != O` & `[8]R != O`).
  - `[EXECUTED]` `crypto_kat_wycheproof.rs` passes `9/9` Wycheproof + pyca suites (`ECDSA-P256/P384` DER & P1363, `RSA-PSS-2048/4096`, `RSA-PKCS1-2048`, `Ed25519`).
- **BLS12-381 Pairing & IETF PoP Signatures (`obend-lightclients/src/bls12_381.rs`):**
  - `[SOURCE]` Full `Fp -> Fp2 -> Fp6 -> Fp12` sextic tower, strict ZCash 48B `G1` / 96B `G2` decompression with mandatory order-`r` subgroup checks, RFC 9380 §8.8.2 `BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_` (`expand_message_xmd` + Simplified SWU + Wahby–Boneh 3-isogeny + cofactor clearing), optimal-ate Miller loop (`|x| = 0xd201000000010000`, negative `x` conjugation), cyclotomic final exponentiation, and `fast_aggregate_verify` rejecting empty pubkey sets, identity keys, rogue-cancelled identity `agg_pk`, and off-subgroup/identity `G2` signatures.
  - `[EXECUTED]` Passes RFC 9380 Appendix J.10.1 `hash_to_g2` KATs and Ethereum `bls-signatures` `Verify` / `AggregateVerify` / `FastAggregateVerify` KATs (`20/20` unit tests).

## 2. Spec-Exact Mainnet & Live-Silicon Signed Wire Formats

- `[REFUTED: pre-audit w10 draft]` Wrapping real curve math around custom `"OBEND.LC.*"` / `"OBEND.TEE.*"` domain-tagged structs still rejects 100% of real mainnet headers and hardware quotes. All five signed wire formats were replaced with exact upstream binary/CBOR/XML specifications:
  1. **Ethereum Electra (`obend-lightclients/src/lib.rs`):** `[SOURCE]` Consensus-Spec SSZ `BeaconBlockHeader::hash_tree_root` (8-leaf SHA-256 tree), `ForkData` / `ForkDigest = fork_data_root[0..4]`, `DOMAIN_SYNC_COMMITTEE = 0x07000000`, `SigningData = sha256(header_root || domain)`, and 512-key `SyncCommittee` SSZ commitment checked against `trusted_sync_committee_root` *prior* to `[r]P` subgroup checks (anti-DoS), followed by `bls12_381::fast_aggregate_verify` and depth-7 Electra finality + depth-4 17-field `ExecutionPayloadHeader` Merkle branches.
  2. **CometBFT (`obend-lightclients/src/lib.rs`):** `[SOURCE]` RFC 6962 / Tendermint `merkle.HashFromByteSlices` (`0x00 || leaf`, `0x01 || L || R`, largest power-of-2 split `k < n`) over Protobuf `SimpleValidator` leaves (`ValidatorSet::Hash()`) and 14-field `tendermint.types.Header` (`Header::Hash()`), plus varint-framed Protobuf `CanonicalVote` (`PrecommitType = 2`, `sfixed64` height/round, `CanonicalBlockID` omitted on nil vote, `Timestamp`, `chain_id`) verified under `ed25519::verify_strict` summing verified voting power `> 2/3 * total_power`.
  3. **RFC 5280 X.509 / CRL / RFC 6960 OCSP (`obend-oracles-e2ee/src/tee.rs`):** `[SOURCE]` Private-field `CertRecord::from_der`, `AmdSnpCrl::from_der`, and `NvidiaOcspResponse::from_der` (supporting `serialNumber = 0` for AMD VCEKs, `UTCTime` & pre/post-2050 `GeneralizedTime`, OCSP-only EKU leaf isolation, and both 20B SHA-1 RFC 6960 `ResponderID.byKey` & 32B SHA-256 key hashes).
  4. **AWS Nitro Enclaves (`tee.rs`):** `[SOURCE]` RFC 9052 CBOR `COSE_Sign1` (`["Signature1", h'a1013822', h'', payload]`, empty unprotected header `{}` enforced, `ES384` 96B `r || s`) + definite & NSM indefinite (`0xbf..0xff`) CBOR `AttestationDocument` (`PCR0..31` width validation, cert chain verified at both `doc.timestamp` and `now_secs`).
  5. **AMD SEV-SNP (`tee.rs`):** `[SOURCE]` `1184`-byte (`0x4A0`) ABI Table 21–23 `ATTESTATION_REPORT` (versions `2`/`3`/`5`, `ECDSA-P384-SHA384` over `report[0x000..0x2A0]`, 72B LE zero-padded `r`/`s` @ `0x2A0..0x330`), AMD KDS VCEK OIDs (`1.3.6.1.4.1.3704.1.3.{1,2,3,8,9}` + `.1.4` 64B/8B `hwID`), and mandatory ARK-signed DER CRL.
  6. **Intel TDX DCAP v4/v5 & NVIDIA Hopper/Blackwell (`tee.rs`):** `[SOURCE]` `48`B `QuoteHeader` + `584`/`648`B `TDQuoteBody` + `Ecdsa256BitQuoteAuthData` (`384`B non-debug SGX `EnclaveReportBody` signed by PCK leaf with `report_data[0..32] == SHA-256(att_pk_64 || qe_auth_data)` + `att_pk_64` quote signature); SPDM 1.1 `GET_MEASUREMENTS` + nested DICE `FWID` + ISO 19770-2 SWID XML with W3C Canonical XML 1.1 & XML-DSig `ecdsa-sha384` (`VerifiedSwidRim` sealed).

## 3. Executed Verification & Live Captures (`hbox --release`, `-D warnings`)

- `[EXECUTED]` `RUSTFLAGS="-D warnings" cargo test --release --offline -p obend-oracles-e2ee -p obend-lightclients` on `hbox`: **`66/66` tests pass (`0` warnings)**:
  - **Mainnet Ethereum KAT:** Post-Electra slot `14,749,306` -> finalized slot `14,749,216` -> execution block `25,512,833` + Deneb `ForkDigest = 0x6a95a1a9`.
  - **Mainnet Cosmos Hub KAT:** `cosmoshub-4` height `31,989,761` `Header::Hash()` (`36511a7b...`) + validator[0] live Ed25519 `CanonicalVote` signature.
  - **Live Silicon Captures (`tests/vectors/tee/`):** AWS Nitro `c5.xlarge` `nitro_att.bin`, Chutes Intel TDX v4 `chutes_tdx_quote.bin`, AMD KDS Genoa RSA-4096-PSS `amd_genoa_cert_chain.pem`, and NVIDIA Hopper `GH100` VBIOS `96.00.9F.00.01` `.swidtag` (`4`-cert CoRIM PKI + XML-DSig `ecdsa-sha384`).
- `[EXECUTED]` `gpt-6.2-astra` audit remediated: Nitro `now_secs` cert-expiry & `{}` unprotected header, OCSP-only EKU isolation, VCEK serial `0` / omitted `KeyUsage` / Turin 8B `hwID`, RFC 6960 20B `byKey`, nested DICE `FWID`, sealed `VerifiedSwidRim`, XML CRLF & PI handling, HTTP non-framing header-value redaction, E2EE TEE freshness, and Ethereum pre-subgroup SSZ root check.

## 4. Open Collateral Seams

- `[OPEN]` **Intel PCS signed JSON collateral (`TCBInfo` + `QEIdentity` + PCK CRL):** `verify_intel_tdx` verifies the full `Root -> PCK -> QE -> AK -> Quote` chain and refuses debug TD/QE attributes, but accepts caller-evaluated `tcb_status` against policy; cryptographic ingestion of Intel PCS v4 JSON collateral is tracked for follow-up.
- `[OPEN]` **TLSNotary MPC `SessionHeader` wire presentation:** `tlsn_e2ee.rs` verifies real `P-256`/`Ed25519` notary signatures over `OBEND.TLSN.NOTARY_ATTESTATION/v1` envelopes; native `tlsn` BCS `SessionHeader` + Merkle commitment verification requires upstream presentation-format pinning.
- `[OPEN]` **Ethereum Fulu BPO `ForkDigest` mask & CometBFT ZIP-215:** `compute_fork_digest` implements Altair..Electra `ForkData[0..4]`; Fulu BPO schedule XOR-masking and CometBFT ZIP-215 cofactor-multiplied Ed25519 edge cases remain separate consensus-upgrade items.
