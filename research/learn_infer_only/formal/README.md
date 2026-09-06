# Formal handback

[EXECUTED current combined proposal] The latest passed set is **49 modules / 651
exact theorem pins**, with all four umbrellas, actual patch application/content
comparison and both import-boundary instruments. The combined patch is
[minidregg-combined-resident-651.patch](integration/minidregg-combined-resident-651.patch),
SHA256 `9398b530f3640d5f279c4f3958ccf57abcbb113f43ca608825ca41d935ed8e42`.
See [run_011/report.json](../experiments/integration/results/run_011/report.json)
and [integration index](integration/README.md) for selected sources and exact
commands. Companion files, HEAD and dirty status stayed unchanged. Existing
dependency oleans were reused; no clean whole-tree build is claimed.

[DERIVED application scope] Apply one compatible combined proposal, not every
historical patch in sequence. The 651-pin set includes context/restore, policy
and distribution, durable Bool/EMA/window, conditional HE noise, generic
contextual receipts, live BFV source/target certificates and compiler
simplification. It remains a proposal for maintainer application. Its proof
assumptions do not establish private release, a lawful Rust codec, arbitrary
mixed-journal scheduling, quantum security or a complete resident.

## Historical first-tranche description

[DERIVED artifact boundary] These two source files are a proposed minidregg patch,
kept here for review. `minidregg-resident-release.patch` adds the modules and imports
both from `Assurance.lean`. It must be folded by the maintainer. No companion source
was edited, no patch was applied there, and no deployment claim follows from these
proofs. The actual proof checks and source hashes live in `../experiments/results/`.

## Statements and nonvacuity

| Proposed source / theorem | Statement and scope |
|---|---|
| [DERIVED] `Assurance/ResidentReleaseContext.lean:56`, `contextScheme` | Extends the existing binding carrier with exact Context in its root. Instantiated at `idealCommitment`, so its premise is inhabited without a custom axiom. |
| [DERIVED] `:108`, `context_binding` | Every accepted wrapper receipt names the independently selected exact Context. |
| [DERIVED] `:118`, `arithmetic_binding`; `:127`, `bad_release_implies_bad_descriptor` | Explicit boundary/program/randomness-rule checks plus a satisfying descriptor force `next=output=(parent+command) mod 2^256`. After wrapper acceptance, wrong arithmetic implies the existing descriptor is false. |
| [DERIVED] `:143`, `context_receipt_price` | Imports the existing fixed-context classical-ROM error `(t+14)*4160/2013265921^6`, through `stage0Receipt_price (S c)`. No new rate, private-state extractor or multi-context composition is proved. |
| [DERIVED] `:180`, `honest_context_receipt`; `:252`, `concrete_oracle_receipt_inhabited` | An accepted real Stage-0 FS receipt exists for every in-range public addition and for the new concrete cSHAKE oracle at 1+2. This is theorem-level completeness, not an executed prover benchmark. |
| [DERIVED] `:231`, `rootBytes_injective`; `:246`, `context_query_encoding_injective` | Existing prefix codecs encode all context fields and the word unambiguously; the encoded query is injective. Hash injectivity is neither assumed nor concluded. |
| [DERIVED] `:133`, `wrong_context_refused`; `:138`, `wrong_next_not_linked`; `:261`, `recipient_substitution_refused` | Refusal teeth on the same evidence carrier, including altering an accepted receipt's recipient. |
| [DERIVED] `Assurance/ResidentRestoreFinality.lean:101`, `accepted_current` | Accepted manifest/candidate agrees with the independent current prefix, genesis and head. |
| [DERIVED] `:109`, `restore_replay_refused`; `:119`, `consumed_parent_refused` | Replaying after `advance` is refused even if the transition was a no-op. Reusing any spent token is also refused using the existing durable consumption theorem. |
| [DERIVED] `:135`, `context_unique_at_slot` | Under the actual `PrefixDiscipline`, two checked candidates at the same slot have equal entire Context events; invokes the existing finality theorem. |
| [DERIVED] `:145`, `authorized_step` | Combines currentness, receipt context and arithmetic forcing, conditional on the descriptor holding. Does not turn probabilistic FS soundness into unconditional per-proof soundness. |
| [DERIVED] `Closed.honest_accepted`, `Closed.nontrivial_arithmetic_witness` | Actual finality checker and accepted FS receipt inhabit the composition; public state changes from 1 to 3. |
| [DERIVED] `Closed.finality_survives_restore`, `Closed.restored_manifest_refused`, `Closed.authority_rollback_reaccepts` | Finality alone still accepts the old certificate; intact authority rejects a fresh release; rolling back that authority re-enables authorization. |

[DERIVED probability scope] The wrapper's bad arithmetic event is a subset of a
base-FS accepting false-descriptor event for a fixed context. Applying the imported
price additionally requires that the wrapper adversary fit the same fixed-context,
query-bounded classical-ROM experiment. No theorem here prices an adaptive sequence
of context changes, a concrete hash attack, QROM, signatures, storage failures or
private-release security. These are not silently assigned zero error.

## Residuals a reviewer should keep visible

[OPEN: RELEASE-hiding / NoSurvivingReadAll] The word and initial/next values are public;
the ideal root even repeats the full word. No cryptographic state privacy, masked
witness, key erasure result or sealed program is supplied. The SFE symbolic model is
not a hidden-state instantiation of these receipt proofs.

[OPEN: recipient and randomness realization] `delivery` is a public pair whose first
projection is the named recipient, not authenticated encryption or confidential
transport. `Linked` restricts the witness to program 0/version 1 (EVM addition) and
deterministic randomness rule/commitment `(0,0)`. Fields for a rule and commitment
are present and bound, but fresh secret entropy and a proof tying it to private
computation remain absent. Merely hashing arbitrary seed metadata would not fill
that gap; the Python selection-bias witness explains why.

[OPEN: runtime continuity] The adapter checks the existing `FinalityGate` and calls
the existing `Snapshot.install`/freshness check. It has no state-decryption field.
The closed witness has empty `rootWrites` and therefore is NOT a successful full
`Intent.preflight`/DataIntent transaction. Next integration must bind current/post
state to materialized roots, carry the semantic proof through that path, and refine
the atomic check/install/delivery protocol. The external authority must survive
host rollback. Tokens are derived from genesis and slot, not supplied as arbitrary
caller nonces. This orders fresh releases; it does not impose a global query quota
or prevent local copies. A quota would also live in the independent authority.

[OPEN: policy and consensus realization] `Authority.policy` is an explicit predicate
slot, with a nonempty concrete toy instance checking program/version/authorization/
recipient. It is not a proof of real authorization signatures or of the intended
policy's semantics. `PrefixDiscipline` is the existing cross-epoch assumption; a
quorum-shaped voter list alone does not imply it. Availability is separate.

## Reproduction and handback

[EXECUTED workflow] Run from `/Users/ember/dev/zkml-research`:

```sh
python3 research/learn_infer_only/experiments/run_audits.py
python3 research/learn_infer_only/experiments/check_formal.py
python3 research/learn_infer_only/experiments/review_patch.py
```

[DERIVED workflow] `check_formal.py` writes only to this research area's ignored
`formal/build`, with symlinks to existing companion artifacts for namespace lookup.
It refuses to write output through a symlink and stops after a failed dependency
check. `review_patch.py` creates the patch, stages a copy of the existing Assurance
umbrella with the new imports, checks that umbrella, invokes the existing import-
boundary script read-only, and runs `git apply --check` in the companion. It does
not apply the patch. This is an umbrella elaboration against existing dependency
oleans, not `lake build Minidregg` from clean sources and not the earlier 8,881-job run.

[EXECUTED development record] All compilation attempts are kept as numbered
`lean_*.json` files. Earlier failures include namespace/Bool-lemma spelling,
elaboration recursion on the concrete word, a terminated slow elaboration, and a
dependent-file attempt against an older successful staged olean. The harness was
then changed to stop after a dependency failure. Only the final source-matching
successful checks and `patch_review.json` establish the delivered build result.
The 31 axiom inventories are pinned with `#guard_msgs`; they use subsets of
`propext`, `Classical.choice`, `Quot.sound`, with no custom axioms or `sorryAx`.

[SOURCE] The existing `Theory/PrivateTrace.lean` and `Assurance/ReleaseGateRouting.lean`
are cited in `../SOURCES.md` rather than copied/re-proved. No Theory or Selvage
import boundary is changed by this patch.
# Autonomous swarm integration checkpoint

[EXECUTED successor] The EMA extension also passes: 16 modules, 265 exact pins,
all four umbrellas and combined patch application, with unchanged source hashes.
Use [minidregg-combined-resident-265.patch](integration/minidregg-combined-resident-265.patch),
SHA256 `5da935fd45db2a8c196fd2333df8b0ae757001dd33fdd831d7b50787060113ff`,
and [integration report](../experiments/integration/REPORT.md). It includes the
baseline below plus four canonical signed-byte EMA modules. The baseline and its
executable integer-check outputs remain preserved; do not apply both combined patches.

[EXECUTED, 2026-09-06] The combined baseline now passes: 12 proposed modules,
217 exact axiom pins, all four umbrella modules, both integer executable checks,
combined patch application/exact-content comparison and import-boundary scripts.
The check copied 524 current companion Lean sources into an isolated source tree;
selected proof elaboration used existing dependency oleans. Companion source hashes,
HEAD and dirty status were unchanged. This is not a clean whole-tree rebuild.

[EXECUTED] Baseline combined patch:
[minidregg-combined-resident-217.patch](integration/minidregg-combined-resident-217.patch),
SHA256 `cba1e801dcc5fcd8578a934f131de2866b0a9a5c755f2ea3eeaf35d01b65ab6e`.
Exact commands and result:
[run_001/report.json](../experiments/integration/results/run_001/report.json).
The patch contains first-tranche context/restore, policy evolution, materialized
durable integration/collision, randomness/adaptive-context/collected-receipt
composition, BFV integer/live-source refinement and integer certificate emission.
It combines independently rooted umbrella additions without rewriting those lane
patches. Apply this combined patch OR its compatible constituent changes, not both.

[EXECUTED historical scope] Compiler optimization/source-certificate extensions
subsequently entered the 371/499-pin passes above. EMA is in the 265-pin successor,
not the 217-pin baseline. The historical
first-tranche description below retains its own scope; current lane notes and
STATUS.md name the successive stronger witnesses and remaining gaps.
