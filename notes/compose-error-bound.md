# `ComposeErrorBound`: the aside was right, and the obligation is MIS-STATED

Lane note, 2026-09-05. `HeteroCompositionSuccinct` (e3be707) left the aside
"`ComposeErrorBound` (`Selvage/HeteroComposition.lean:235`) is provable from `err_nonneg`
alone"; `docs/FORMAL_STATUS_AND_NEXT_PROOFS.md:44` lists it and `ComposeFixedPoint` as
named obligations of the accumulation/heterogeneous-composition row. Decide, as theorems.

## The statements, copied

`Selvage/HeteroComposition.lean:229-235` — docstring: "*the composed knowledge error of a
heterogeneous rung is at most the sum of the two systems' errors*", plus the ⚠ that it is
NOT implied by `OB2_depth_composition_nonneg` (`Depth.lean:1875`).

```lean
def ComposeErrorBound : Prop :=
  ∀ (A B : ProofSystem) (_ : VerifierEmbedding A B),
    KnowledgeSound B → ∀ ε, ε = A.err + B.err → 0 ≤ ε
```

`:237-244` — docstring: "*unbounded IVC requires a self-embedding, and a one-way embedding
does not supply one … stated as the existence demand `ivc_tower_sound` consumes*".

```lean
def ComposeFixedPoint (B : ProofSystem) : Prop :=
  Nonempty (SelfEmbedding B) ∧ KnowledgeSound B
```

`err_nonneg` is `ProofSystem`'s own field (`HeteroComposition.lean:61`, `0 ≤ err`); the
tree's other `herr_nonneg`s (`CorrelatedAgreement`, `ReedSolomon`, `AccSound`,
`JohnsonRegime`, `SubUdSeam`, `Depth:338`) are an unrelated hypothesis on
proximity-generator error functions. **Consumers of either obligation: none** — grep over
`Selvage/`+`Assurance/` finds only the definition site, the header at `:39`, the
`Selvage.lean` import comment, `GOAL.md:48`, and the docs row.

## Verdict

**`ComposeErrorBound`: MIS-STATED.** Trivial *and* wrong-shaped — the `Prop`'s conclusion
is `0 ≤ A.err + B.err`, an arithmetic fact about two `err` fields. It never mentions the
composed system, its verifier, or its failure event. Proved:

- `composeErrorBound_of_err_nonneg : ComposeErrorBound` — `rintro A B - - ε rfl;
  exact add_nonneg A.err_nonneg B.err_nonneg`. Both hypotheses discarded.
- `composeErrorBound_ignores_hypotheses` / `_of_ignoring` — the body holds for two
  *arbitrary unrelated* systems and that hypothesis-free form implies the obligation.
- `composeErrorBound_body_at_unembeddable` — the body holds at
  `(strictSystem, widenedSystem)`, the pair `widened_relation_refuses_embedding` proves
  admits **no** `VerifierEmbedding`.
- `composeErrorBound_trivial_witness` — the vacuity witness, at `flatSystem 1` (accepts
  everything, relation holds of nothing, `err = 1` = the max a probability can be) embedded
  into its `verifierRelationSystem`: embedding exists, target is `KnowledgeSound`,
  conclusion `0 ≤ 1 + 1` holds, and the composed rung is knowledge-sound at **no** statement
  (`composeSystem_flat_not_knowledgeSound`).

**`ComposeFixedPoint`: NEITHER trivial nor mis-stated — it stays.** Parametrised by `B`,
with both teeth: `composeFixedPoint_trivial_witness : ComposeFixedPoint trivialSystem`
(satisfiable) and `composeFixedPoint_refutable b : ¬ ComposeFixedPoint (accBcsSystem_F5 b
oneOracle)` (refutable, via `accBcsSystem_F5_not_knowledgeSound`). What is loose is only
listing it as an obligation without naming the `B`.

## The honest statement

`err` is an uninterpreted `ℝ` whose only tie to anything is `0 ≤ err`, so *every* `Prop`
relating `err` fields of abstract `ProofSystem`s is either arithmetic (vacuous, as above)
or false (`err` can be set anywhere). The honest statement has to give `err` a **semantics**
first. Weakest one that supports a union bound: `EventMeasure Ω` — nonnegative, monotone,
subadditive `μ : (Ω → Prop) → ℝ` on the adversary's coin space — with `err` bounding
`μ(KsFailure …)` (`KsFailure` is `HeteroCompositionSuccinct:159`). `composeSystem A B e` is
the rung as a `ProofSystem` (A's statements/witnesses, B's proofs, `Verify` through
`encStmt`, `err := A.err + B.err`), so "the composed error" becomes a term.

```lean
def ComposeErrorBoundStrict : Prop :=
  ∀ (Ω : Type) (m : EventMeasure Ω) (A B : ProofSystem) (e : VerifierEmbedding A B)
    (X : Ω → A.Stmt) (P : Ω → B.Proof),
    m.μ (fun ω => KsFailure B (e.encStmt (X ω)) (P ω)) ≤ B.err →      -- target clause
    m.μ (fun ω => ∃ πA, KsFailure A (X ω) πA) ≤ A.err →               -- ⚑ transfer clause
    m.μ (fun ω => KsFailure (composeSystem A B e) (X ω) (P ω)) ≤ (composeSystem A B e).err
```

**It closes**: `composeErrorBoundStrict_closes`. Containment then subadditivity — at coins
where the rung fails, either `B`'s relation is unsatisfiable at the embedded statement (B
fails), or it is satisfiable and `bwd` (`rung_sound`'s step) returns an accepting `A`-proof
at a witness-less statement (A fails).

ATLAS fields, all discharged:

- **Satisfiable, non-vacuous, and TIGHT** — `composeErrorBoundStrict_fires_at_F5` /
  `_tight_at_F5`, at the landed F₅ instance `accBcsSystem_F5 3 oneOracle` with the identity
  carrier (`relDecider` / `relDeciderEmbedding`) as source. The composed failure event is
  *inhabited* (`lucky_accepted` ∧ `lucky_no_witness` — the `1/|F|` round event), mass `1`,
  composed error `0 + (3+2)/5 = 1`. **Equality, not slack.**
- **Refutable, twice.** `composeErrorBoundStrict_transfer_load_bearing`: drop the transfer
  clause and it is false — `flatSystem 0 ↪ flatTarget 0`, `A.err = B.err = 0`, `B`
  `KnowledgeSound` and never failing, composed rung fails with mass `1 > 0`. And *the tower
  where the naive sum is exceeded* exists **at the landed instance**, not a toy:
  `composeErrorBoundStrict_target_load_bearing` at query budget `0` — `err = 2/5`, transfer
  clause holds, composed rung fails with mass `1 > 0 + 2/5`.
- **Premise-inhabitation** — `f5_hyp_target` (at a system that genuinely fails),
  `f5_hyp_source` (at the decider, which never fails; `relDecider_knowledgeSound`).

⚑ Why the transfer clause is content and not bookkeeping: its event is
`∃ πA, KsFailure A x πA` — an **existential** over `A`-proofs, not an adversary's output, so
pricing it is a non-uniform demand on `A.err`. Same gap `TowerSoundRO`'s teeth name at
`n ≥ 2` ("the proof `bwd` hands back is an existential, not an adversary the game bounds"),
met here at one rung.

## For the coordinator, and files

`ComposeErrorBound` should be **de-listed** from the `docs/FORMAL_STATUS_AND_NEXT_PROOFS.md`
accumulation row (discharged, says nothing); the row's "state and prove the composed error
ledger before claiming recursion" next-step should point at `ComposeErrorBoundStrict` and
its transfer clause. `ComposeFixedPoint` stays, with a named `B`. The new file is **not**
imported by `Selvage.lean` — wiring it in is the coordinator's call.

- NEW, only file touched in minidregg (uncommitted, untracked):
  `/Users/ember/dev/minidregg/Selvage/HeteroCompositionErrorBound.lean`
- NEW: `/Users/ember/dev/zkml-research/notes/compose-error-bound.md` (this note).
- Not edited: `Selvage/HeteroComposition.lean`, `Selvage.lean`, `docs/*`.

Gate: `lake env lean Selvage/HeteroCompositionErrorBound.lean` → exit 0, 25
`#guard_msgs`-pinned `#print axioms`, every one `[propext, Classical.choice, Quot.sound]`
(only the five `pointMass_*` measure-API lemmas are unpinned, audited transitively). No
`sorry`, no `axiom`, no `native_decide`. Negative control: rewriting the pinned axiom lists
to `[BOGUS]` makes the file error, so the pins are live.
