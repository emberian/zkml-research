# BaseFold's RBR seam — status, and the ambiguity the completeness lane left open

Lane record, 2026-08-14. Repo `~/dev/minidregg`, branch `main`.

## 0. The brief was stale by a night, and that is the first finding

The brief I was given was written against `7959941` ("selvage: the multilinear
opening's completeness cone, on the fold we already had") and scoped S3 (the degree-2
honest sumcheck family) and S4 (the `RbrKnowledgeSoundness` instance) as the remaining
deliverable. **Both landed overnight, along with four layers past them.** Verified at
source, not from a summary:

| object | file | status |
|---|---|---|
| S3 — degree-2 honest sumcheck family | `Selvage/QuadraticSumcheck.lean` | LANDED |
| S4 — generic sumcheck RBR instance | `Selvage/SumcheckRbr.lean` | LANDED |
| S4 — BaseFold's instantiation | `Selvage/BaseFoldRbr.lean` (`basefoldSumcheckRbr`) | LANDED |
| the braid on one challenge stream | `Selvage/BaseFoldBraid.lean` | LANDED |
| full-word IOR verifier + soundness | `Selvage/BaseFoldIor.lean` | LANDED |
| sampled-commitment layer | `Selvage/BaseFoldCommittedIor.lean` | LANDED |
| raw opening checks, equivocation exposed | `Selvage/BaseFoldRawCommittedIor.lean` | LANDED |
| claim seam over the existing vector commitment | `Selvage/MultilinearCommitment.lean` | LANDED |
| Poseidon2 / BCS / FS alphabet | `Selvage/BaseFoldBcs*.lean` | IN FLIGHT (live lane) |

The landscape verdict the brief relayed held: no new commitment abstraction was built.
`Selvage/Commitment.lean`'s `OpeningScheme` is reused unchanged and
`MleEvalClaim = (root, point, value)` sits above it.

## 1. The two-commitment ambiguity: CLOSED

`BaseFoldCompleteness.raw_commit_terminal_differs_f5` is the specification the brief
handed me: two commitments of the "same" one-variable F₅ data, both passing the entire
low-degree descent at every challenge, terminating at `4` and at `2`.

**It is not an ambiguity, and now that is a theorem rather than an argument.** The raw
word is not junk and not a forgery — it is an *honest* commitment to a **different**
table. `rawPoly = 1 + 2X` reads the value table `[1,2]` as coefficients; the Möbius
packing of `[1,2]` is `1 + X`. Both are in the degree window, so both have a definite
table (`basefold_terminal_word_eq`), and the raw one's table is `[1,3]`, whose MLE at
`3` genuinely is `2`. Two descents, two statements — not two answers to one.

Landed this lane (all `#print axioms`-pinned to `propext, Classical.choice, Quot.sound`):

- **`basefoldExactClaim_value_unique`** (`Selvage/BaseFoldIor.lean`) — the general
  statement: two strict BaseFold claims over the **same** top word and point carry the
  **same** value, as soon as the commitment domain holds the degree window. Nothing
  probabilistic: interpolant uniqueness on the domain (`eq_of_degreeLT_of_agree`) plus
  Möbius injectivity. This is what "acceptance pins the value" means once the word is
  fixed.
- **`BaseFoldIorExample.raw_commit_exact_claim_f5`** — the raw commitment *is* a strict
  claim, at `2`.
- ⭐ **`BaseFoldIorExample.raw_commit_not_exact_claim_at_honest_f5`** — and therefore
  it is **not** a claim at the honest value `4`. Deterministic; no challenge, no
  probability.
- ⭐ **`BaseFoldIorExample.raw_commit_wrong_value_bound_f5`** — against an adaptive
  degree-2 prover, the assembled IOR accepts the raw commitment *as an opening to `4`*
  on at most `2` challenges in `5`. Contrast with completeness, which accepts its
  descent at **every** challenge. That is exactly the boundary crossed.
- **`MleEvalClaimExample.raw_root_ne_honest_root_f5`** (`Selvage/MultilinearCommitment.lean`)
  — at the root layer: the two words have **different roots**, so
  `MleEvalClaim.value_unique` is never asked to reconcile them. One root with two values
  would be a break; that is precisely what `value_unique` forbids.

So the pinning has two independent halves, and both are theorems:
**root → word** is commitment binding (`basefoldWord_injective`, and downstream
`[COMMIT-CR]`); **word → value** is `basefoldExactClaim_value_unique`.

## 2. The S4 instance was an island. It is now compiled

`basefoldSumcheckRbr` had **zero consumers** — grep across `Selvage/`, `Assurance/`,
`Compiler/` found it referenced only in the file that defines it, while the deployed
soundness path to the zkML ledger (`Assurance/ZkmlMatmulBaseFold.lean`) ran through the
*operational* bound `basefoldIor_exact_sound` instead. A native Def-4.2 object with no
consumer is a formalization nobody's error bar depends on.

Landed: **`basefoldSumcheck_fs_sound`** (`Selvage/BaseFoldRbr.lean`) — the instance fed
to Selvage's unconditional Fiat–Shamir keystone (`fsKeystone_proved.sound`, discharged
from [OB-2a] in `Selvage/Depth.lean`), giving straightline, loss-free FS soundness with
the grinding factor named: a `t`-query ROM adversary claiming a wrong total and having
its FS-compiled transcript accepted succeeds with probability at most `(t + m)·2/|F|`.
`BaseFoldRbrExample.fs_sound_f5` computes it on the landed F₅ instance: `(t + 1)·2/5`.

## 3. What is NOT proved — read this before quoting anything above

1. **`W = Unit`.** `sumcheckReduction`'s witness type is `Unit` and its extractor is
   `fun _ _ _ => ()`. So `RbrKnowledgeSoundness` and `FsStraightlineKnowledgeSoundness`
   at this leg are round-by-round / straightline **soundness with a trivial extractor**,
   not extraction of the committed multilinear. The source relation is
   `claimedValue = mle table z`, a statement predicate. Anyone reading
   "knowledge-soundness instance" as "the table can be extracted" is reading it wrong;
   extraction lives at the commitment layer (`MleEvalClaim` + Merkle binding +
   `[COMMIT-CR]`), and is not composed with this leg by a theorem.
2. **The RS/proximity leg is not product-composed into the knowledge state.** The
   `2/|F|` per round prices the sumcheck only. The FRI query/Merkle costs are accounted
   separately in `BaseFoldCommittedIor` / `BaseFoldRawCommittedIor`
   (`m·3/|F| + (1−τ)^q`) and are *not* absorbed into the RBR error field.
3. **Two parallel accountings of the same leg now exist** — the operational IOR bound
   (`basefoldIor_wrong_value_sound`, via the adaptive union bound) and the native RBR
   instance (via `sumcheckRbrKnowledgeSound`). They agree today at `m·2/|F|`. Two shapes
   that agree today are two shapes that will disagree later; one of them should be
   derived from the other or deleted. Flagged, not unilaterally collapsed — the RBR
   route is the one that composes, so the IOR bound is the candidate to re-derive.
4. **No `sorry` in any of the above**, and no named-obligation `Prop` was needed: every
   statement in §1 and §2 is proved.

## 4. Build evidence

- `lake build Selvage.BaseFoldIor`, `Selvage.MultilinearCommitment`,
  `Selvage.BaseFoldRbr` — green, including every `#guard_msgs`-pinned `#print axioms`
  (a `sorryAx` or an extra axiom fails the build, not a review).
- `scripts/check-import-boundary.sh` — PASS (Selvage imports stay within
  Mathlib/Theory/Selvage; the two imports added, `Selvage.OutOfDomain` and
  `Selvage.FiatShamir`, introduce no cycle).
- `scripts/check-proof-hygiene.sh` — PASS (459 tracked Lean files, 167 guarded axiom
  footprints).
- Full `lake build Selvage` — see §5; my files are green, the tree is red at a
  concurrent lane's file.

## 5. ⚠ HEAD was red while I worked, in a live lane's file

`Selvage/BaseFoldBcsQuerySamplingJoint.lean` failed to build at `69a2ecd`, and the
failure is worth naming because of its shape:

```
error: Selvage/BaseFoldBcsQuerySamplingJoint.lean:206:54: unexpected token 'set_option'; expected 'lemma'
...
'…acceptedSeedRawCommittedIor_coherent_exact_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

A **parse** error truncated a declaration, and the theorem downstream of it elaborated
with `sorry` placeholders in its *statement* — the printed signature reads
`… ≤ ↑m * (3 / sorry) + (1 - tau) ^ queryCount + sorry`. The `#guard_msgs`-pinned
`#print axioms` **caught it** (that is the mechanism working exactly as intended: the
axiom pin went red on `sorryAx`). Two commits landed on that file while I was building,
so a lane is live on it; I left it alone. It is not downstream of anything I touched.
Anyone reading a *green* claim about `acceptedSeedRawCommittedIor_coherent_exact_sound`
should re-check it at whatever commit that lane settles on.

I hit the same syntax trap once myself: `omit … in` (like `set_option … in`) must
precede the docstring, not sit between the docstring and the theorem.
