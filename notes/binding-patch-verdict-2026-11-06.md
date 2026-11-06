# Verdict on Astra's `binding-term.patch`, read against minidregg's live path (2026-11-06)

Patch: `notes/astra/binding-term.patch` (SHA-256 `94b94700…de534`), reviewed independently by
Astra's governance lane (`notes/astra/binding/review.md`). I read the patch, the design note and
that review, and checked it against minidregg `origin/main` `a37e28146` (2026-11-05), not the
`c4ecabe0f` baseline it was written for. Tags as elsewhere.

## Applies cleanly to today's tree

[MEASURED] `git apply --check` passes on `a37e28146`. After applying, all five files hash to the
reviewed SHA-256s (`BindingGame e48cbb59…`, `BindingBudget 46ed39e7…`, `Commitment 28c453a7…`,
`AuditSampling 81ff2f5d…`, `CollisionResistanceROM ed5da9b5…`), so none of the three touched
files moved in the 144 commits since the baseline. The import closure of the two new modules is
14 Selvage files plus Mathlib; nothing from `Compiler/`, `Theory/` or the native kernels.

## What the live path already does

[READ] `Compiler/Tower256AdditiveFriRawController.lean:421`
`accepts_ideal_or_receiptCollision`: an accepted raw receipt is either an `IdealAccept` of
Selvage's identity-committed FRI, or it yields a `ReceiptCollision`, an exact leaf- or
node-level `FramedXofCollision` located at a named round `j` and query `a`. No probability, no
ROM, no binding field. For a fixed unkeyed hash (cSHAKE256 is fixed by ruling) this is the
right form: the theorem is unconditional, and the "security" content is that nobody can
exhibit a cSHAKE collision (Rogaway's human-ignorance framing, 2006/281).

## Verdict per piece

| piece | verdict | reason |
|---|---|---|
| comment corrections in `Commitment`, `CollisionResistanceROM`, `AuditSampling` | **ACCEPT** | They retire the false claim that a short-root sponge realizes `BindingCommitment` (critique W4). Accurate as written. |
| `prob`, `mean`, `prob_or`, `prob_true`, `mean_bad_transfer` | **ACCEPT** | Finite algebra. `prob_true` under `[Nonempty Ω]` closes the empty-space vacuity Astra's reviewer found. |
| `cert_and`, `receipt_and` | **ACCEPT** | These are the right composition laws for CERTIFICATES L1 and P7. `hb` is only a probability bound on the actual subjects' collision event, so it can be discharged by the live path's explicit-collision extractor without any game. |
| `Experiment`, `SecureAt`, `cert_and_of_game`, `advantage_reduction` | **ACCEPT as an interface, do not instantiate for cSHAKE with an unrestricted `Code`** | For a fixed compressing hash, a constant program that outputs a known collision exists mathematically. `SecureAt … ε` with `ε < 1` over all codes is then false, and a theorem using it would be vacuous. Astra's design note says this (§"The repair", ¶2). The live path should use `cert_and` with `εb := prob[the constructive reduction outputs a cSHAKE collision]` and never assume `SecureAt` for a fixed hash. |
| `bindLeg_of_history_game` vs `leakage_of_global_game` | **ACCEPT; use the global route** | The rare-history countermodel is correct and is the most useful thing in the patch for the audit theorem: a global collision bound does not give `Round.BindLeg`'s every-history premise. For audit receipts over cSHAKE roots the global finite-horizon route `b/q + M·ε` is the honest one. |
| `ComputationalBinding.flat_binding_advantage` over `roScheme` | **ACCEPT, low value for the live path** | It prices the flat ROM scheme. The live path is Merkle over cSHAKE, already reduced to a framed collision by `Tower256CshakeMerkleBinding`. |

## What I would add (not in the patch)

1. **`cert_and_of_collisionExtractor`**: `cert_and` specialized so `hb` is supplied by a
   deterministic map from the two extracted subjects to a `FramedXofCollision`, i.e. the live
   path's form. Then the certificate algebra's binding term is "probability that this explicit
   reduction outputs a cSHAKE collision", with no adversary class quantified. This is the
   statement the certificate leaves on Tower256 (LEAF-PROVER-DECISION option 3) consume.
2. **A vacuity tooth for `SecureAt` at a fixed hash**: a lemma that `SecureAt` with `ε < 1`
   fails for any non-injective fixed `commit` once the code class contains constants. It turns
   the design-note warning into a theorem, so nobody instantiates it for cSHAKE by accident.

## Application

[MEASURED] The two new modules build against `a37e28146`'s sources. Their import closure is 16
Selvage modules plus Mathlib, built fresh on hbox under `swarm-build` with 0 errors.
`scripts/check-import-boundary.sh` passes with the new files staged. The patch is applied
verbatim on minidregg branch **`lane/binding-term` @ `049bfc450`** (pushed). Its only addition
is two import lines in the `Selvage.lean` umbrella; without them the new modules would be
orphans that `lake build` never compiles. The two additions proposed above are not written yet.
