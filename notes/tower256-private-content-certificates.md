# Private-Witness `Tower256` + `cSHAKE256` Content Certificates: Lean 4.35.0 Soundness/Hiding & Native Multi-KB Prover

**Date:** 2026-11-21 · **Lane:** `mini-tower256-zkcert` (`real_systems_wave_2026_11_21`, audited by `zkcert-neon-audit`)  
**Verification Script (`[EXECUTED]`):** [build_and_verify.sh](file:///Users/ember/dev/zkml-research/research/real_systems_wave_2026_11_21/formal_zkcert/build_and_verify.sh) (`exit 0`, Lean `v4.35.0` + `scripts/check-import-boundary.sh` + `--release` Rust conformance/audit tests).  
**Authored Artifacts (`[EXECUTED]`):** [Tower256PrivateContentCert.lean](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean) (`1,951` lines), [Tower256PrivateCertConformance.lean](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateCertConformance.lean) (`128` lines), [tower256_private_cert_conformance.json](file:///Users/ember/dev/minidregg/prover/testdata/tower256_private_cert_conformance.json), [tower256_private_cert.rs](file:///Users/ember/dev/minidregg/prover/src/tower256_private_cert.rs) (`2,609` lines), [prove_private_cert.rs](file:///Users/ember/dev/minidregg/prover/src/bin/prove_private_cert.rs) (`275` lines), [tower256_private_cert.rs (tests)](file:///Users/ember/dev/minidregg/prover/tests/tower256_private_cert.rs) (`550` lines).

---

## 0. What Moved (`[SOURCE]`, `[DERIVED]`, `[EXECUTED]`)

In `minidregg`, [Tower256ContentCert.lean](file:///Users/ember/dev/minidregg/Compiler/Tower256ContentCert.lean#L18-L45) (`:18`, `:25-45`, `:484-490`, `:618`, implementing [LEAF-PROVER-DECISION.md](file:///Users/ember/dev/zkml-research/docs/LEAF-PROVER-DECISION.md#L240-L276) §6.2; `[SOURCE: implementation & design doc read in full]`) had two explicit limitations:
1. **`fullDisclosure` receipt:** `Receipt` carried `table : DfaTable` and `word : List UInt8` in the clear (`:484-490`), leaking the entire secret document and dense `256 · |Q|` transition table.
2. **`.accept`-only claims:** `ClaimData.count n` and `ClaimData.bound lo hi` were refused (`:18`, `:618`).

This lane closes both gaps end-to-end across Lean 4.35.0 (`0 sorry`, `0 axiom`, `0 native_decide`, `0 #guard`, `0` compiler warnings, `14` `#guard_msgs`-pinned `#print axioms`) and native Rust (`0` compiler warnings, byte-for-byte Lean conformance, real-file CLI `prove_private_cert`, zero-leakage slice audit, and sub-`215 ms` multi-KB proving):

| Component | Artifact | Lines | Pins / Tests | Measured Result (`[EXECUTED]`) |
|---|---|---:|---:|---|
| Private cert controller, hiding & soundness | [Tower256PrivateContentCert.lean](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean) | 1,951 | 13 `#print axioms` | Kernel-verified in `8.40s` (`[propext, Classical.choice, Quot.sound]` max; `runCount_eq_traceFrom_countP` choice-free) |
| Separated `#eval` conformance emitter | [Tower256PrivateCertConformance.lean](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateCertConformance.lean) | 128 | 1 `#print axioms` + 4 vectors | Emits `.accept true`, `.accept false`, `.count 2`, `.bound 1 3` + checks 4 negative mutants via `checkPrivate` |
| Native `Tower256` prover, verifier & LCH NTT | [tower256_private_cert.rs](file:///Users/ember/dev/minidregg/prover/src/tower256_private_cert.rs) | 2,609 | 3 unit + 3 integration suites | `71.8×` prover speedup via L1-table `fast_mul256`/`fast_square256`, $\mathbb{F}_2$-linear LCH NTT, & `CShake256Core` midstate clone |
| Multi-KB CLI (`prove`, `verify`, `audit`, `bench`) | [prove_private_cert.rs](file:///Users/ember/dev/minidregg/prover/src/bin/prove_private_cert.rs) | 275 | CLI E2E + slice scanner | `1 KiB` `13.7 ms`, `4 KiB` `51.4 ms`, `16 KiB` `210.5 ms` prove; `0.80–1.27 ms` verify; **`0` leaked `≥6B` slices** |

---

## 1. Kernel-Verified Lean 4.35.0 Theorems (`[DERIVED]`, `[EXECUTED]`)

### 1.1 Salted `C8` Content Commitment, Constructive Collision Extraction & Per-Leaf Hiding

- **Exact `C8` Leaf Bijection & Salted Binding (`[EXECUTED]`):** [Salt248](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean#L197) (`Fin (2^248)`) packs with `b : UInt8` into `C8` (`Coordinate 8` / `GF(2^256)`) via [packSaltedLeaf](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean#L213) (`lane 0` low byte = `b`, upper 31 bytes = `s`), forming the exact equivalence [saltedLeafEquiv](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean#L256) (`UInt8 × Salt248 ≃ C8`, kernel-tested by [leafPacking_kernel_teeth](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean#L1902)). [saltedContentCommit](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean#L285) commits `(w, salts)` under `cSHAKE256` `cubeRoot merkleDomainsC codecC`, and [saltedRoot_eq_or_collision](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean#L333) proves equal-length salted records sharing one root either satisfy `w₁ = w₂ ∧ s₁ = s₂` or collide at the explicit `Frames` computed by `saltedCollisionFrames` (never an existential over `cSHAKE256`, which pigeonhole would inhabit trivially; `[SOURCE: docs/LEAF-PROVER-DECISION.md §6.2 L260-262]`).
- **Top-Down Path Collision Extractor (`[EXECUTED]`):** [pathCollision](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean#L85) and [recompute_eq_or_pathCollision](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean#L115) prove any accepted sibling path opening `v` against `cubeRoot domains codec col` either satisfies `v = col addr` or exposes an input-pinned `FramedXofCollision cshake w.customization w.left w.right`.
- **Unopened-Leaf Salt Uniformity & Concrete `cshakeC` Mask Hiding (`[DERIVED]`, `[EXECUTED]`):**
  1. [unopened_salted_leaf_oracle_hiding](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean#L394) & [unopened_salted_leaf_rom_prob_eq](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean#L444): for any `b₀, b₁ : UInt8` and fresh `s₀ : Salt248` at unopened address `idx`, precomposing leaf oracle `L : C8 → D` with the involution `Equiv.swap (packSaltedLeaf b₀ s₀) (packSaltedLeaf b₁ s₀)` preserves all other leaf digests and yields **identical** `BindingGame.prob` root distributions for every `rt : D`.
  2. [unopened_keyed_salt_prob_eq](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean#L467): any salt-bijective leaf digest family produces identical root probability over uniform `Salt248`.
  3. [maskedCubeRootPreimageEquiv](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean#L504) & [maskedCubeRoot_prob_eq](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean#L527): on the **concrete `cshakeC` Merkle tree** (zero ROM assumption), characteristic-2 masking `addC payload mask` (`blindTraceEval`) induces an exact bijection `m ↦ addC m (addC p₀ p₁)` on `C8` masks preserving preimage cardinality and `BindingGame.prob` for every `p₀, p₁ : C8` and `rt : Digest`.

### 1.2 All Three `ClaimData` Modes & Root-Only `PrivateReceipt` Soundness

- **`.accept`, `.count`, and `.bound` (`[EXECUTED]`):** [Dfaops.runCount](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean#L553) counts byte positions whose transition lands in `t.accepting`, proved equal to `(t.traceFrom t.initial w).countP ...` in [Dfaops.runCount_eq_traceFrom_countP](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean#L585). [Dfaops.satisfiesClaim](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean#L611) decides `.accept b`, `.count n`, and `.bound lo hi`, witnessed with positive and negative teeth on `noSkDash` (`neg(any* · "sk-" · any*)`) and `countAB` in [claimModes_kernel_teeth](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean#L1862).
- **Masked Trace, `Tower256SuccinctCheck` Weld, & `checkPrivate` (`[EXECUTED]`):** Each [TraceRow](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean#L636) packs `(byte, state16, next16, cumCount32, mask184)` into `C8` ([unpackTraceRow_packTraceRow](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean#L689)) under `traceRoot`. Level-0 FRI evaluations use [blindTraceEval](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean#L742) (`rowPayloadC r ⊕ cSHAKE256(rowMaskCustomization, r.mask)`), extended at rate `≤ 1/2` (`max 1 (depthOf recordLength) < friEll ≤ 24`) and checked by `Tower256SuccinctCheck.check` ([checkPrivate](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean#L970)) alongside `AutomatonHeader` authentication, `BoundaryOpenings`, and `stepQueries` Fiat–Shamir `StepOpening`s.
- **Soundness, Non-Vacuity, & Sampling Law (`[EXECUTED]`):**
  - [allStepsValid_implies_satisfiesClaim](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean#L1046) & [invalid_claim_forces_bad_step](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean#L1085): any false claim with valid boundaries forces `∃ i < |w|, ¬ StepValidAt t w rows i`.
  - [checkPrivate_sound_or_collision](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean#L1263): an accepted `PrivateReceipt` either satisfies `PrivateHolds stmt t w salts` + Selvage's `IdealAccept` + level-0 FRI endpoint welds on `T`, or hits `StepSamplingMiss`, or exposes an explicit path/tree-pinned `PrivateCertCollision`.
  - [checkPrivate_premises_inhabited](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean#L1521) proves joint non-vacuity of all premises on any well-formed non-empty `DfaTable` and word; [step_sampling_miss_prob_eq](file:///Users/ember/dev/minidregg/Compiler/Tower256PrivateContentCert.lean#L1565) proves `BindingGame.prob` of missing `badIdx : Fin L` across `q` uniform draws equals `(((L : ℝ) - 1) / L) ^ q`.
- **Neon Vacuity & Fiat–Shamir Audit (`[EXECUTED]`):** Read-only audit by `zkcert-neon-audit` caught and repaired five concrete hardening items folded into Lean and Rust: (1) replaced unary `encodeLength` on `recordLength`/`ClaimData`/query indices with constant-width 32B `natCoordBytes` (`:849`), eliminating an OOM/DoS vector on large `Bound.hi` and cutting Keccak-f calls; (2) bound `friEll`, `friRounds`, `friQueries`, `stepQueries` into `privateStatementBytes` (`:859`); (3) wrapped `roots` and `challenges` in separate `envelope` frames and omitted `finalCoeffs` (already bound by `roots[m]`) in `stepTranscriptPrefix` (`:894`); (4) enforced canonical empty `nextRow`/`nextTracePath` at `idx + 1 = recordLength` (`:940`); and (5) capped `friEll ≤ 24` and `recordLength ≤ 2^32` (`:973-976`).

---

## 2. Native Rust Prover, Conformance, Multi-KB Benchmarks & Zero-Leakage Audit (`[EXECUTED]`)

- **Algorithmic & Arithmetic Acceleration (`[DERIVED]`, `[EXECUTED]`):** Replacing $O(N^2)$ Lagrange interpolation with an $O(N \log N)$ `Tower256` LCH Novel-Basis Additive NTT (`ntt_inverse_in_place` + `ntt_forward_in_place` in [tower256_private_cert.rs:885-985](file:///Users/ember/dev/minidregg/prover/src/tower256_private_cert.rs#L885-L985)), L1-table Fan–Paar `fast_mul256` (`81` vs `6,561` recursive steps) + byte-linear `fast_square256` (`32` table XORs, `:506-673`), $\mathbb{F}_2$-linear subspace tabulation (`:1290-1325`), bottom-up `CubeMerkleTree` (`0` extra hashes per path, `:729-803`), and `CShake256Core` customization midstate cloning (`:675-723`) cut `16 KiB` proving from `15,436 ms` to **`210.51 ms` (`73.3×` speedup)**.
- **Lean-to-Rust Conformance & Planted Attack Suite (`[EXECUTED]`):** `lean_authored_conformance_vectors_match_byte_for_byte` ([tower256_private_cert.rs:89-191](file:///Users/ember/dev/minidregg/prover/tests/tower256_private_cert.rs#L89-L191)) verifies bit-exact equality between Lean `#eval` and Rust on `saltedContentCommit`, `deltaCommit`, `automatonCommit`, `traceRoot`, `friInitialRoot`, `friReceipt` wire bytes, and Fiat–Shamir `derivedStepIndex` across all 4 vectors. `multi_kb_case_a_zero_leakage_audit_and_planted_attacks` (`:194-424`) and `cli_prove_verify_and_audit_real_file_end_to_end` (`:427-550`) verify conjunctive `L1` welding over a shared `saltedContentCommit` root (`Absent("sk-")` + `Bound(1, 50)` + `Count` on realistic `Hermes`/`.env` documents containing 6 secret credentials), **0** leaked `≥ 6`-byte document slices across the entire serialized receipt buffer, and deterministic rejection of 1-byte `"sx-live"` → `"sk-live"` secret injection, forged `.accept`/`.count`/`.bound` claims, backdoored `DfaTable`s, and mutated FRI/step bytes.

```text
$ bash research/real_systems_wave_2026_11_21/formal_zkcert/build_and_verify.sh && \
  CARGO_TARGET_DIR=/Users/ember/dev/minidregg/prover/target-zkcert \
  /Users/ember/dev/minidregg/prover/target-zkcert/release/prove_private_cert bench
  [TARGET    8.40s] Compiler.Tower256PrivateContentCert -> rc=0
  [TARGET 1088.69s] Compiler.Tower256PrivateCertConformance -> rc=0
test lean_authored_conformance_vectors_match_byte_for_byte ... ok
test cli_prove_verify_and_audit_real_file_end_to_end ... ok
test multi_kb_case_a_zero_leakage_audit_and_planted_attacks ... ok
```

| Document Size | Policy + Claim (`fri_queries=6, step_queries=8`) | Prove (`ms`) | Verify (`ms`) | Prover `Keccak-f` | Verifier `Keccak-f` | Receipt Bytes | Leaked `≥6B` / `≥8B` Slices |
|---:|---|---:|---:|---:|---:|---:|---:|
| `1,024 B` | `Absent("sk-")` `[.accept true]` | `13.72` | `0.80` | `31,456` | `2,830` | `30,977 B` (`30.25 KiB`) | `0` / `0` |
| `1,024 B` | `Markers(TODO\|RULE)` `[.bound 1..200]` | `16.52` | `0.81` | `43,788` | `2,914` | `31,618 B` (`30.88 KiB`) | `0` / `0` |
| `4,096 B` | `Absent("sk-")` `[.accept true]` | `51.41` | `1.08` | `111,542` | `3,548` | `38,899 B` (`37.99 KiB`) | `0` / `0` |
| `4,096 B` | `Markers(TODO\|RULE)` `[.bound 1..200]` | `54.47` | `1.04` | `123,877` | `3,635` | `39,541 B` (`38.61 KiB`) | `0` / `0` |
| `16,384 B` | `Absent("sk-")` `[.accept true]` | `210.51` | `1.23` | `431,272` | `4,342` | `47,625 B` (`46.51 KiB`) | `0` / `0` |
| `16,384 B` | `Markers(TODO\|RULE)` `[.bound 1..200]` | `212.94` | `1.27` | `443,602` | `4,424` | `48,251 B` (`47.12 KiB`) | `0` / `0` |

---

## 3. Honest Scope, Residual Boundaries (`[OPEN]`), & Proposed Maintainer Folds

- **Unopened Hiding vs Sampled Step Disclosure (`[DERIVED]`, `[OPEN]`):** Every unopened index `i ∉ {0, L - 1} ∪ {derivedStepIndex u}` leaks **zero** information in `PrivateReceipt`: `saltedContentCommit` hides `w[i]` with 248-bit random salt (`unopened_salted_leaf_rom_prob_eq`), `traceCommit` hides `rows[i]` with 184-bit `RowMask`, and `friReceipt` pair openings reveal only `blindTraceEval` (`maskedCubeRoot_prob_eq`). At the `2` endpoints (`0`, `L - 1`) and `stepQueries` Fiat–Shamir step indices, `BoundaryOpenings`/`StepOpening` open the individual byte/row (`≤ 2 + stepQueries` single positions, yielding `0` leaked `≥ 6`-byte slices on `1–16 KiB` structured configs). Eliminating even single-byte disclosure at those `2 + stepQueries` indices and driving transition soundness from `((L - 1) / L) ^ stepQueries` (`step_sampling_miss_prob_eq`) to `2^-100` without `O(L)` step openings requires replacing sampled leaf step checks with an algebraic `Tower256` AIR/zerocheck + `BinaryShout` lookup quotient polynomial before FRI (`[OPEN]`, matching [LEAF-PROVER-DECISION.md:187, 273-276](file:///Users/ember/dev/zkml-research/docs/LEAF-PROVER-DECISION.md#L273-L276)).
- **Metered Search & Corpus Ledger:** `0` `eprint.iacr.org` downloads, `0` `scry.py` queries, `0` `kagi.py` queries; all references read from local `zkml-research` and `minidregg`.
- **Proposed Maintainer Folds (Not Edited Here):**
  1. **`minidregg/Compiler.lean`:** Add `import Compiler.Tower256PrivateContentCert` (keep `Compiler.Tower256PrivateCertConformance` out of `Compiler.lean` so `#eval` file IO only runs on explicit conformance regeneration).
  2. **`docs/LEAF-PROVER-DECISION.md` §6.2 & `docs/VERDICTS.md`:** Record `Tower256PrivateContentCert` (`saltedContentCommit`, `.accept`/`.count`/`.bound`, root-only `PrivateReceipt` + native `prove_private_cert` `51.4 ms` at `4 KiB`), noting the remaining `[OPEN]` algebraic transition-quotient / `BinaryShout` upgrade for `2^-100` zero-step-leakage soundness.
