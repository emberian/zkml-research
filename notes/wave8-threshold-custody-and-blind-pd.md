# Wave 8 (`G10` / `L6`): Multi-Party Hybrid-PQ Threshold Custody, Persisted `C8` Gate, and `GMask61`-Blinded `R_PD`

**Metered search ledger:** `Scry: 0` · `Kagi: 0` · `eprint.iacr.org fetches: 0` (local codebase + read-only donor quarry only).

## 1. Donor Quarry & Retirements

- `[SOURCE: /Users/ember/dev/breadstuffs/fhegg-fhe/src/threshold/quorum.rs:1-420]` Legacy `quorum` proved `t < n` bivariate VSS over `R_q`, per-recipient sealed envelopes, and Shamir Lagrange partial decryption, but anchored shares to Shor-broken Ristretto Pedersen commitments (`12,288` points/row) and ~2 min Bulletproofs.
- `[SOURCE: /Users/ember/dev/breadstuffs/fhegg-fhe/src/threshold/distributed_relin.rs:1-225]` Legacy `distributed_relin` implemented 2-round Mouchet et al. Protocol 2 gadget key generation with ephemeral `u_i` zeroized on `Drop`.
- `[SOURCE: /Users/ember/dev/obend/lean/Obend/Polis/PqThresholdCustody.lean:1-310]` `PqThresholdCustody` established strict `NoSingleViewer >= 2`, `epoch != 0`, monotone epoch latching (`stepEpochLatch`), and crash-consistent single-open custody (`GrainCustodyHost`).
- `[SOURCE: native/darkvfhe/src/dark_gdn.rs:124-289]` Prior `darkvfhe` simulated `n`-of-`n` shares from one `master_seed: [u8; 32]` (`R1-4`) and opened `PdSuccinctProof` directly on unmasked secret-share polynomials (`s_j(r)`, `e_j(r)`) at `dark_gdn.rs:263`, leaking a fresh $\mathbb{F}_{p_0}$-linear functional of $s_j$ per opening.

## 2. Cryptographic & Systems Closures (`native/darkvfhe/src/threshold_custody.rs`)

1. **Zero-Dealer `t < n` (`2 <= t < n`, `2t > n`, `NoSingleViewer >= 2`) DKG & 2-Round Relin (`L6` R1-4 closed) `[DERIVED]`:**
   - Enrolled committee (`EnrolledThresholdRoster`) enforces `2 <= t < n` and strict majority quorum intersection $2t > n$ (`|Q_1 \cap Q_2| \ge 2t - n \ge 1`), authenticating messages under a hybrid **RFC 8032 Ed25519 + stateful SHA-256 Merkle-Lamport PQ** signature (`HybridPqSignature`) and sealing peer-to-peer shares via ephemeral+static Edwards DH + SHA-256 stream + Encrypt-then-MAC (`seal_to_peer`).
   - Every custodian independently samples secret polynomial $s_d \in \{-1,0,1\}^N$ and bivariate VSS coefficients from OS `/dev/urandom` (`0` central dealer secret), commits shares via **post-quantum BDLOP Ring-LWE/SIS homomorphic commitments** $\mathrm{Com}(m; r_1, e_0, e_1) = (a_1 r_1 + a_2 e_1 + e_0,\; b_1 r_1 + e_1 + m) \bmod Q_p$ (`|r_1|, |e_0|, |e_1| \le 8`, derived from a 2-round commit-reveal CRP seed), verifies pairwise symmetry $F_d(i, j) = F_d(j, i)$ with ordered broadcast-list binding (`VerifiedCrossCheckReceipt`), and runs one-shot 2-round distributed relinearization (`DistributedRelinDealer`, consuming `self` in Round 2 after locally reconstructing verified Round-1 shares and zeroizing $s_d, u_m$ on `Drop`).
2. **Persist-Before-Share `C8` `OpeningAuthorization` + `WhirPcs61` Compute Gate (`G10`) `[DERIVED]`:**
   - `partial_decrypt_relinearized_ct2_gated` refuses share computation unless given: (a) a $t$-quorum hybrid-PQ-signed `OpeningAuthorization` binding `(dkg_transcript_digest, epoch != 0, sequence, policy_digest, ct_commitment, compute_proof_digest, refresh_cadence, turns_since_refresh, selected_parties)` with `refresh_cadence == 1 && turns_since_refresh == 0` enforced in `tvd_40b_strict_mode`, AND (b) standalone-verified `WhirPcs61` (`DVFHEWH1`) compute provenance (`verify_hoisted_whir_bytes` + `relinearize_ct3 == target_ct2`).
   - Before touching `s_shamir_rns`, `PersistentCustodyAuditLog` acquires an exclusive non-blocking `flock`, enforces monotone `high_water_epoch` and single-open replay sets over `(ct_commitment, raw_ct_handle, effective_ct_handle)`, fsync-appends a 180-byte SHA-256 hash-chained record (fsyncing parent dir at genesis), refuses missing or torn logs on `reopen_existing` (`CAP-07`), and permanently poisons the custodian on any I/O or reload failure.
3. **`GMask61`-Blinded Partial Decryption (`WhirBlindPdProof`, Retiring `PdSuccinctProof` `R_PD` Leak) `[DERIVED]`:**
   - Commits `(s_{i,0..3}` [`ExactGarner15` zero-slack `[0, q_k)`], `R_1, E_0, E_1`, `e_{sh,i} = e_i + E`, complement `e_{rev,i} = 2E - e_{sh,i}` + 2 boolean carries, 4 OS-rejection-sampled uniform mask rows $(\mu_{s,0..3}, \mu_e) \in (\mathbb{F}_{p_0}^N)^4$, 9 zero-wrap `RingModQkInstance` gadgets (`< 2^{58} < p_0/2`), and `D1b` multiplicities) inside a single fresh `WhirCommittedPcs61` (`319` slots at $N=8192$; $130.1\text{b}$ BCIKS20 / $144.5\text{b}$ DKT24).
   - Proves exact integer smudge bound $e_{sh,i} + e_{rev,i} = 2E \implies |e_i|_\infty \le E$ (`3 \times 40$-bit pair-carry claims $< 2^{41} \ll p_0/2$), BDLOP transcript anchor binding $(T_{0,i}, T_{1,i})$, and $d_{i,k} \equiv \lambda_{i,S,k} c'_{1,k} s_{i,k} + e_i \pmod{X^N+1, q_k}$.
   - Because $r_0^0 = 1 \neq 0$ for every $r_0 \in \mathbb{F}_{p_0}$ and $(\mu_{s,0..3}, \mu_e)$ is rejection-sampled directly from `/dev/urandom` (`0` PRG seed bottleneck, `0` modular bias), the `R_PD` evaluation map $(\mu_{s,0..3}, \mu_e) \mapsto \text{BlindedRPdEvals} \in \mathbb{F}_{p_0}^4$ has rank $4$ and **exact $\mathrm{TVD} = 0$** (`dark_gdn.rs:263` linear evaluation disclosure closed).

## 3. Executed Verification, Benchmarks (`N = 8192`), & Cross-Audit

- **Command `[EXECUTED]`:**
  `CARGO_TARGET_DIR=/Users/ember/dev/zkml-research/native/target-w8-thresh cargo test --manifest-path /Users/ember/dev/zkml-research/native/Cargo.toml --release -p darkvfhe --test threshold_c8_blind_pd -- --nocapture`
  -> `exit 0`, `0` warnings (`#![deny(warnings)]` in both owned Rust files), `4/4` test suites passed (`130.41 s`).
- **Deployed `N = 8192, Q_p (L=3 \times 61\text{b}), ExactGarner15` Measurements `[EXECUTED]`:**

| Committee | `DKG` (Bivariate-VSS + BDLOP) | `DistRelin` (2-round) | `HoistedWhirProve` (`DVFHEWH1`) | `BlindPdProve` / party | `WhirBlindPdProof` Wire | `BlindPdVerify` (1 share) | Quorum Verify + Combine | Plaintext `max\|diff\|` |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `2-of-3` (`NoSingleViewer=2`, 1 offline) | `2,091.32 ms` | `12,852.13 ms` | `1,051.24 ms` (`532.42 KiB`) | `3,566.30 ms` | `603.01 KiB` (`617,482 B`) | `1,613.46 ms` | `5,803.75 ms` | `0` |
| `3-of-5` (`NoSingleViewer=3`, `[0,2]` offline) | `4,086.68 ms` | `21,178.44 ms` | *(persistent `Enc(W)`)* | `3,517.80 ms` | `603.01 KiB` (`617,486 B`) | — | `6,707.99 ms` | `0` |

- **`15/15` Adversarial Falsifiers Refused `[EXECUTED]`:** (1) `t<2` / `t>=n` / `2t<=n`; (2) corrupted private VSS row; (3) bivariate dealer equivocation $F(i,j)\neq F(j,i)$; (4) rerouted/tampered confidential envelope; (5) `epoch == 0`; (6) `R_refresh > 1` in `tvd_40b_strict_mode`; (7) wrong `policy_digest`; (8) under-quorum or tampered PQ signature; (9) corrupted `WhirPcs61` compute proof (`0` audit-log pollution) & forged relin `Ct`; (10) `stale_epoch`; (11) `double_open` across custodian disk restart + fresh mask; (12) torn audit-log tail (`CorruptedAuditLog` + permanent `AuditLogPoisoned`); (13) tampered `partial_rns` & detached `auth_statement_digest`; (14) `+1`-tampered `BlindedRPdEvals`; (15) wrong share $s'_0 \neq s_0$, verifier-side BDLOP anchor tamper, and verifier-side $|e| = E + 1$ (`e_sh = 2E + 1`) rejection.
- **Single-Pass `Codex gpt-6.2-astra` Audit `[EXECUTED]`:** Caught and fixed in-place: per-chunk LogUp `active_len`/`depth` pinning, exact verifier-side $e_{sh} + e_{rev} = 2E$ upper bound (closing $2E+1$ endpoint), `auth_statement_digest` + canonical `VerifiedThresholdDkgTranscript` integrity binding, `/dev/urandom` rejection-sampled mask rows, `u32` cadence fields, exclusive `flock` + torn-log poisoning, `VerifiedCrossCheckReceipt` broadcast-digest binding, and one-shot `DistributedRelinDealer`.
- **Refutations & Open Seam:**
  - `[REFUTED: unmasked key-PCS reuse for HVZK R_PD]` Re-opening one static unmasked secret-share commitment across ciphertexts leaks $s_i(r)$ via `SlotLinearClaim::rhs`; fresh per-opening `WhirCommittedPcs61` + BDLOP anchor + OS mask rows closes `R_PD` linear evaluation disclosure (`TVD = 0`).
  - `[OPEN]` While `BlindedRPdEvals` + `GMask61` achieves `TVD = 0` on `R_PD` random-point evaluations and WHIR sumcheck rounds, the read-only donor `logup_gkr.rs` serializes unmasked GKR `FractionTreeProof` child denominators over digit chunks; full proof-wide HVZK requires masking `logup_gkr.rs` layer evaluations before exposing `WhirBlindPdProof` outside the committee combine boundary, and active-dishonest distributed relin requires adding zero-knowledge proofs of well-formedness to `RelinRound1Share`/`RelinRound2Share`.

## 4. Proposed Maintainer Folds (Unedited Here)

- **`docs/VERDICTS.md`:** Mark Gate `G10` / `L6` (`R1-4`, `C8`, `PdSuccinctProof` `R_PD` leak) closed in `darkvfhe::threshold_custody` (`2-of-3` & `3-of-5` at `N=8192`, `603.01 KiB` `WhirBlindPdProof`, `15/15` adversarial refusals), tracking `logup_gkr.rs` fraction-tree denominator masking as the remaining transcript-HVZK follow-up.
- **`notes/README.md`:** Index `notes/wave8-threshold-custody-and-blind-pd.md` under Wave 8 (`G10` Threshold Custody & Blind `R_PD`).
