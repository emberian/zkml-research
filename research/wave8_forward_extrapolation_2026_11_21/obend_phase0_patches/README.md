# Obend Phase-0 Security Gates Patchkit (`G1`, `G2`, `G3`, `G5`)

Drop-in Lean `v4.35.0` patchkit and overlay bundle closing the four `obend`-scoped Phase-0 security gates from Wave-8 (`CAP-01`, `CAP-03`, `CAP-04` + `CAP-06`, and `CAP-09`).

## 1. Contents & Worktree Commits

All four patches in `patches/` use uniform `obend` repository-root paths (`a/lean/...` → `b/lean/...`) and apply cleanly with `git apply -p1` from the `obend` root:

| Patch | Gate / Defect | Worktree Branch | Commit SHA | Scope |
| --- | --- | --- | --- | --- |
| `patches/0001-G1-linear-custody.patch` | **`G1` (`CAP-01`)**: `Ty.bearsCustody` + `mustBeLinear` linear custody binding across `validContext`, `ArmsTyping`, `SplitSpine`, `Coerce`, `Prepare`, and `PrepareChecks` (`bearsCustody_congr`) | `revival-g1-g2-core-floors` | `7d943691f17d1c02a6a26f22bce7ac9ab0a7096b` | 22 files (`+846 / -155`) |
| `patches/0002-G2-floor-polarity.patch` | **`G2` (`CAP-03`)**: Explicit `FloorPolicy` sign polarity (`creditLimit`, `minReserve`, `issuerWell`) + `AccountKind.member` in `Ledger/Floors.lean` and callers | `revival-g1-g2-core-floors` (`HEAD~1`) | `dd8111b3d9fa0f7e43f4183a39ef0957eddbc010` | 6 files (`+247 / -68`) |
| `patches/0003-G3-captp-digest256-epoch.patch` | **`G3` (`CAP-04` + `CAP-06`)**: 256-bit `Digest256` `SwissNum` / `handoffNonce` / `PendingId` / `SortedDigestSet` + nonzero `msgEpoch != 0` in `Polis/CapTP.lean`, `JointCoReceipt.lean`, `Escrow.lean`, `GradedSessionMetatheory.lean` | `revival-g3-captp-digest256` | `e83902e93a71896c187eb3b2fdefd7fb5a3a6499` | 6 files (`+260 / -91`) |
| `patches/0004-G5-simplex-n-minus-f.patch` | **`G5` (`CAP-09`)**: Parameterized `n - f` quorum (`quorumSize n f = n - f`, `3 * f + 1 ≤ n`) replacing hardcoded `2 * f + 1` in `Consensus/Simplex.lean` and `Finality.lean` | `revival-g5-simplex-quorum` | `d775415d5afb1c2b2e7b8e8cc2d3b330f3d92aba` | 4 files (`+166 / -99`) |

Companion directories:
- `overlay/G1/`, `overlay/G2/`, `overlay/G3/`, `overlay/G5/`: full post-patch copies of modified files for each gate.
- `teeth/G1Teeth.lean`, `teeth/G2Teeth.lean`, `teeth/G3Teeth.lean`, `teeth/G5Teeth.lean`: mutation-killing `#tooth` witnesses paired with each gate's soundness theorems.

## 2. Applying Patches

From a clean `obend` checkout at base `bc87ece8` (or cherry-picking `G1` + `G3` onto `dev` after Batch-1 `G2` + `G5`):

```bash
# Dry-run check from obend repo root:
git -C /path/to/obend apply --check -p1 \
  patches/0002-G2-floor-polarity.patch \
  patches/0004-G5-simplex-n-minus-f.patch \
  patches/0001-G1-linear-custody.patch \
  patches/0003-G3-captp-digest256-epoch.patch

# Apply:
git -C /path/to/obend apply -p1 \
  patches/0002-G2-floor-polarity.patch \
  patches/0004-G5-simplex-n-minus-f.patch \
  patches/0001-G1-linear-custody.patch \
  patches/0003-G3-captp-digest256-epoch.patch
```

## 3. Static Lint & Remote Linux (`bb2`) Verification Commands

**Never run `lake` or `lean` locally on macOS for `obend`.** Run static lint via `obb` locally and run Lean `v4.35.0` verification on `bb2` under `SWARM_MEM_MAX=12G`:

```bash
# 1. Local static lint (0 findings in modified files; 510 total matching baseline dev):
/Users/ember/dev/obebuilder/target/release/obb lint --repo /path/to/obend \
  --strict --strict-expose --strict-harnesses --json

# 2. Remote G1 + G2 cone verification on bb2 (282 jobs, exit 0):
ssh build@bb2 'cd /path/to/obend/lean && export PATH=$HOME/.elan/bin:$PATH && \
  SWARM_MEM_MAX=12G swarm-build timeout --kill-after=10s 600s lake build \
  Obend.Core.Ty Obend.Core.Check Obend.Core.Bidirectional \
  Obend.Core.Proofs.Preservation Obend.Core.Proofs.BidirectionalCompleteness \
  Obend.Core.Proofs.SubjectReduction Obend.Core.Proofs.CheckerTransport \
  Obend.Core.Proofs.TypedSubstitution Obend.Core.Proofs.Conservation \
  Obend.Core.Proofs.FillTyping Obend.Core.Proofs.Splice Obend.Core.Proofs.Force \
  Obend.Core.Canonicity Obend.Core.GradedCoreWeld Obend.Core.Code \
  Obend.Elab.Coerce Obend.Elab.Prepare Obend.Elab.Proofs.PrepareChecks \
  Obend.Equiv.EffectHandlers Obend.Equiv.LogicalRelation Obend.Law.Proofs.Typing \
  Obend.Spec.BidirectionalSurfaceElab Obend.Spec.FrontEnd Obend.Vault.FormCheck \
  Obend.Slot.Core4 Obend.Slot.Budget Obend.Teeth.Core.LinearTeeth \
  Obend.Teeth.Core.CheckTeeth Obend.Ledger.Floors Obend.Ledger.Seat \
  extracted.CoerceProbesTest metasystem.CoreMetatheoryElevationTest \
  metasystem.GradedSessionAndSurfaceElabTest'

# 3. Remote G3 CapTP + Polis/Vault/Ledger slice verification on bb2 (439 jobs, exit 0):
ssh build@bb2 'cd /path/to/obend/lean && export PATH=$HOME/.elan/bin:$PATH && \
  SWARM_MEM_MAX=12G swarm-build timeout --kill-after=10s 600s lake build \
  Obend.Polis.CapTP Obend.Polis.JointCoReceipt Obend.Core.GradedSessionMetatheory \
  Obend.Vault.Escrow Obend.Polis.HouyhnhnmTurn Obend.Polis.GrainCustodyHost \
  Obend.Polis.GrainPowerbox Obend.Polis.PqThresholdCustody \
  Obend.Polis.DecentralizedRulesMesh Obend.Vault.UnifiedDeos Obend.Ledger.Seat \
  metasystem.HouyhnhnmCapTpMonitorTest metasystem.GradedSessionAndSurfaceElabTest \
  metasystem.DistributedPredicatesAndCoReceiptTest metasystem.CustodyPowerboxWireParityTest \
  metasystem.GrainPowerboxMembraneTest metasystem.ZoeSeatSettlementTest \
  metasystem.VerifiableCredentialsAndTraceTest'

# 4. Remote G5 Simplex quorum + metasystem seam tests on bb2 (418 jobs, exit 0):
ssh build@bb2 'cd /path/to/obend/lean && export PATH=$HOME/.elan/bin:$PATH && \
  SWARM_MEM_MAX=12G swarm-build timeout --kill-after=10s 600s lake build \
  Obend.Consensus.Simplex Obend.Consensus.Finality Obend.Apps.SovereignDrex \
  Obend.Teeth.Extracted.CoreTeeth metasystem.InnerSeamWeldTest \
  metasystem.SimplexLivenessAndOutboxTest metasystem.DeosSimplexOutboxSeamTest'
```
