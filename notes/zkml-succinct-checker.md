# The succinct zkML contraction checker — queue item 3, built

Lane: LEAN BUILD, 2026-09-04. Repo `~/dev/minidregg`, branch `main`.
Doc row: `docs/FORMAL_STATUS_AND_NEXT_PROOFS.md` "Matmul, low-rank updates,
Spartan, and zkML"; queue item 3: *"Build one succinct, runnable zkML checker.
Bind all three matmul openings, the contraction sumcheck, the registered suite,
exact statement, and the complete failure budget. Keep native output neutral
until this checker accepts."*

Files (uncommitted, report only):

* NEW `Assurance/ZkmlMatmulSuccinctChecker.lean` (988 lines, 0 `sorry`, 9 pins)
* NEW `Assurance/ZkmlMatmulSuiteRegistry.lean` (70 lines) — the registry,
  moved out of the audit turn so both checkers bind ONE entry
* MODIFIED `Assurance/ZkmlMatmulAuditTurn.lean` (−35/+6: the registry block
  replaced by `import` + `open`; nothing else touched)
* MODIFIED `Assurance.lean` (+2 import lines)

---

## THE RESULT IN ONE LINE

The checker `check : Statement → Transcript → Except Failure (PLift Checked)`
never reads a table. It decides registry membership, three root/point/value
bindings and a `κ`-round message replay, and `accepts_iff` proves it decides
exactly `Checked`. Acceptance with true openings IS the landed
`SumcheckAccepts` run (`checked_sumcheckAccepts`), so the contraction bound
`(μ+ν)/|F| + κ·3/|F|` transfers (`strategy_sound`), and composing the tree's
three full-word BaseFold IOR verifiers lands the complete budget
`matmulSuccinctSoundnessBudget = (μ+ν)/|F| + κ·3/|F| +
matmulBaseFoldIorAlgebraicBudget` as a theorem (`fullWord_sound`). The F7
instance is decided by the kernel on literal roots and proved to be the honest
prover's transcript.

⚠ **The pessimistic number, out loud:** at the decided instance (F7,
μ=κ=ν=1) the complete budget is **`23/7 > 1`** (`budget_f7`). Covered scope
in the same sentence: this is the runnable *shape* over a toy field with the
opening IOR at *full-word* resolution; it is not a secure parameterization and
not a succinct-communication proof.

---

## 1. WHAT WAS READ (ground truth, quoted)

The three opening claims and their truth predicate — the opening interface
this tree has, no `openAt`-at-a-point invented:

```
structure MleEvalClaim (Root F : Type*) (m : ℕ) where
  rt : Root
  pt : Fin m → F
  val : F
def MleEvalClaim.Holds [Field F] (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (c : MleEvalClaim Root F m) : Prop :=
  ∃ table : (Fin m → Bool) → F,
    c.rt = S.commit (basefoldWord dom table) ∧ mle table c.pt = c.val
structure MatmulMleClaims (RootA RootB RootC F : Type*) (μ κ ν : ℕ) where
  output : MleEvalClaim RootC F (μ + ν)
  left : MleEvalClaim RootA F (μ + κ)
  right : MleEvalClaim RootB F (κ + ν)
```

The verifier-side event that "opening C/A/B at a point" means here
(`Selvage/BaseFoldIor.lean`), consumed unchanged:

```
def BaseFoldIorAccepts (T : FoldingTower F ι m) (z : Fin m → F) (H : F)
    (word : ι 0 → F) (prover : (ℕ → F) → ℕ → Polynomial F)
    (r : Fin m → F) : Prop := ...
theorem basefoldIor_exact_sound ... (hfalse : ¬ BaseFoldExactClaim T z H word) ... :
    uniformProb (Fin m → F) (fun r => BaseFoldIorAccepts T z H word prover r)
      ≤ (m : ℝ) * (3 / Fintype.card F)
```

The contraction protocol (`Selvage/SumcheckReduction.lean`,
`Assurance/ZkmlMatmulSumcheck.lean`):

```
def SumcheckAccepts {v : ℕ} (prover honest : ℕ → Polynomial F) (H S : F)
    (r : Fin v → F) : Prop :=
  (∀ i, i < v → (prover i).eval 0 + (prover i).eval 1 = scChain H prover (chalOf r) i)
    ∧ scChain H prover (chalOf r) v = scChain S honest (chalOf r) v
theorem matmul_sumcheck_soundness ... (hC : C ≠ matmulTable A B) ... :
    uniformProb (((Fin μ → F) × (Fin ν → F)) × (Fin κ → F)) (MatmulAccepts A B C prover)
      ≤ ((μ : ℝ) + ν) / Fintype.card F + (κ : ℝ) * (3 / Fintype.card F)
```

The existing failure budget (`Assurance/ZkmlMatmulBaseFold.lean`), bound to,
not paralleled:

```
noncomputable def matmulBaseFoldIorAlgebraicBudget (F : Type*) [Fintype F] (μ κ ν : ℕ) : ℝ :=
  ((μ + ν : ℕ) : ℝ) * (3 / Fintype.card F) + ((μ + κ : ℕ) : ℝ) * (3 / Fintype.card F)
    + ((κ + ν : ℕ) : ℝ) * (3 / Fintype.card F)
```

The registry (was `ZkmlMatmulAuditTurn.auditRegistry`, now
`ZkmlMatmulSuiteRegistry.auditRegistry`, byte-identical definitions):
`AuditIdentity` = six `Digest`/`Nat` fields; `auditRegistry := [auditIdentity]`;
`auditIdentity_matches_checker` pins it to `ZkmlMatmulChecker.expected`.

---

## 2. THE STATEMENTS (copied from the file)

```lean
structure Statement (Root F : Type) (μ κ ν : ℕ) where
  suite : AuditIdentity
  rootA : Root
  rootB : Root
  rootC : Root
  x : Fin μ → F
  y : Fin ν → F
  value : F

structure RoundMessage (F : Type) where        -- four coefficients, degree ≤ 3
  c0 : F
  c1 : F
  c2 : F
  c3 : F

structure Transcript (Root F : Type) (μ κ ν : ℕ) where
  rounds : ℕ → RoundMessage F
  challenges : Fin κ → F
  claims : MatmulMleClaims Root Root Root F μ κ ν

inductive Failure where
  | unregisteredSuite
  | outputRootMismatch | leftRootMismatch | rightRootMismatch
  | outputPointMismatch | leftPointMismatch | rightPointMismatch
  | outputValueMismatch
  | roundSumMismatch (round : ℕ)
  | terminalMismatch

structure Checked (stmt : Statement Root F μ κ ν) (tr : Transcript Root F μ κ ν) : Prop where
  registered : stmt.suite ∈ auditRegistry
  outputRoot : tr.claims.output.rt = stmt.rootC
  leftRoot : tr.claims.left.rt = stmt.rootA
  rightRoot : tr.claims.right.rt = stmt.rootB
  outputPoint : tr.claims.output.pt = Fin.append stmt.x stmt.y
  leftPoint : tr.claims.left.pt = Fin.append stmt.x tr.challenges
  rightPoint : tr.claims.right.pt = Fin.append tr.challenges stmt.y
  outputValue : tr.claims.output.val = stmt.value
  rounds : ∀ i, i < κ →
    (tr.rounds i).boolSum = chain stmt.value tr.rounds (chalOf tr.challenges) i
  terminal : chain stmt.value tr.rounds (chalOf tr.challenges) κ =
    tr.claims.left.val * tr.claims.right.val

def check (stmt : Statement Root F μ κ ν) (tr : Transcript Root F μ κ ν) :
    Except Failure (PLift (Checked stmt tr))
def accepts ... : Bool
theorem accepts_iff : accepts stmt tr = true ↔ Checked stmt tr
```

The PCS premise, named:

```lean
def OpeningsHold (SA SB SC) (domA domB domC) (claims : MatmulMleClaims Root Root Root F μ κ ν) : Prop :=
  claims.output.Holds SC domC ∧ claims.left.Holds SA domA ∧ claims.right.Holds SB domB
```

The bridge (⭐):

```lean
theorem checked_sumcheckAccepts
    (SA SB SC) (domA domB domC)
    (hcardA : 2 ^ (μ + κ) ≤ Fintype.card ιA) (hcardB : 2 ^ (κ + ν) ≤ Fintype.card ιB)
    (hcardC : 2 ^ (μ + ν) ≤ Fintype.card ιC)
    (A B C) (x y) (value : F) (tr : Transcript Root F μ κ ν)
    (hchecked : Checked (honestStatement SA SB SC domA domB domC A B C x y value) tr)
    (hopen : OpeningsHold SA SB SC domA domB domC tr.claims) :
    SumcheckAccepts (v := κ) tr.prover (matmulHonest A B x y (chalOf tr.challenges))
      (mle₂ C x y) (matmulTrue A B x y) tr.challenges
```

Completeness (⭐), every table pair / point / challenge vector:

```lean
theorem checker_complete (SA SB SC) (domA domB domC) (A B) (x y) (r : Fin κ → F) :
    Checked (honestStatement SA SB SC domA domB domC A B (matmulTable A B) x y
        (mle₂ (matmulTable A B) x y))
      (honestTranscript SA SB SC domA domB domC A B x y r)
```

Soundness, PCS truth as a premise (⭐); then the premise made a visible term:

```lean
theorem strategy_sound ... (hC : C ≠ matmulTable A B) (P : Strategy Root F μ κ ν) :
    uniformProb (Draw F μ κ ν) (fun w =>
        P.Accepts SA SB SC domA domB domC A B C w ∧
          OpeningsHold SA SB SC domA domB domC (P.claims w.1 w.2))
      ≤ ((μ : ℝ) + ν) / Fintype.card F + (κ : ℝ) * (3 / Fintype.card F)

theorem strategy_sound_budget ... :
    uniformProb (Draw F μ κ ν) (fun w => P.Accepts SA SB SC domA domB domC A B C w)
      ≤ ((μ : ℝ) + ν) / Fintype.card F + (κ : ℝ) * (3 / Fintype.card F) +
        uniformProb (Draw F μ κ ν) (fun w =>
          P.Accepts SA SB SC domA domB domC A B C w ∧
            ¬ OpeningsHold SA SB SC domA domB domC (P.claims w.1 w.2))
```

The complete budget, composed (⭐) — `FullStrategy` extends `Strategy` with one
prefix-measurable degree-≤2 opening prover per claim; `FullStrategy.Accepts` is
`accepts = true ∧ BaseFoldIorAccepts TC … ∧ BaseFoldIorAccepts TA … ∧
BaseFoldIorAccepts TB …` on the committed words:

```lean
noncomputable def matmulSuccinctSoundnessBudget (F : Type) [Fintype F] (μ κ ν : ℕ) : ℝ :=
  ((μ : ℝ) + ν) / Fintype.card F + (κ : ℝ) * (3 / Fintype.card F) +
    matmulBaseFoldIorAlgebraicBudget F μ κ ν

theorem fullWord_sound (SA SB SC) (TA TB TC) (hneA hneB hneC) (hcardA hcardB hcardC)
    (hC : C ≠ matmulTable A B) (P : FullStrategy Root F μ κ ν) :
    uniformProb (Draw F μ κ ν × OpenDraw F μ κ ν) (P.Accepts SA SB SC TA TB TC A B C)
      ≤ matmulSuccinctSoundnessBudget F μ κ ν
```

Its proof is a four-way split (contraction-with-true-openings, or a false
output/left/right claim that still passes its IOR), `uniformProb_or_le` three
times, `uniformProb_fst_le`/`uniformProb_prod_le` to read each term off its own
coordinate, and `basefoldIor_exact_sound` per opening after
`not_exactClaim_of_not_holds` (one word admits one value —
`basefoldExactClaim_value_unique`). No new probability toolkit.

---

## 3. WHAT IS BOUND vs WHAT IS NAMED

| doc-row obligation | status here |
|---|---|
| exact statement | **bound** — `Statement` (registered suite, three roots, `(x,y)`, value) |
| suite registry | **bound** — `registered : stmt.suite ∈ auditRegistry`, decided; `unregisteredIdentity_not_registered` is the tooth |
| three matmul openings | **bound at claim level** — roots to the statement, points to `(x,y)/(x,r)/(r,y)`, values consumed; truth = `MleEvalClaim.Holds`; **opening proofs**: `BaseFoldIorAccepts` (full-word) consumed in `fullWord_sound` |
| contraction transcript | **bound** — `chain`/`firstBadRound` replay; `chain_eq_scChain` identifies it with `scChain` on `RoundMessage.poly`; `checked_sumcheckAccepts` |
| complete failure budget | **bound** — `matmulSuccinctSoundnessBudget`, a theorem in `fullWord_sound`; every refusal is a `Failure` constructor |
| PCS (`[MATMUL-pcs]`) | **partly named** — the IOR here is *full-word* (verifier reads the whole committed word); sampled Merkle queries, BCS and `[COMMIT-CR]` are exactly what `BaseFoldCommittedIor`/`BaseFoldRawCommittedIor` retain, untouched |
| Fiat–Shamir (`[MATMUL-fs]`) | **named** — every challenge is a uniform draw (`Draw`, `OpenDraw`) |
| sparse oracle | **not applicable** — that is Spartan's obligation, no sparse table appears in the contraction |
| native output neutral | **preserved** — nothing outside Lean produces an acceptance bit; the checker consumes no bytes yet (that binding is the row's *next* clause) |

Scope items, as theorems or explicitly not: `rank1`-style
`rank1_blind_to_the_error` has its analogue here in the *premises* —
`strategy_sound` says nothing about `A`, `B` being the right operands, only
that the claimed `C` is their product. Whether the committed word really is a
padded table (`[MATMUL-pad]`) is still a commitment-layer obligation.

---

## 4. THE INSTANCE ACTUALLY DECIDED

Over `ZMod 7`, `μ = κ = ν = 1`: `eA = [[1,2],[3,4]]`, `eB = [[5,6],[0,1]]`
(`MatmulExample`), outer point `x = 3, y = 5`, challenge `r = 4`, commitment
`idealCommitment` on `dom₇₄ = {0,1,2,3}`.

```
rootA = ![1, 4, 2, 2]   rootB = ![5, 1, 6, 6]   rootC = ![5, 1, 6, 2]   -- BaseFold words
message = ⟨0, 3, 2, 0⟩                                                  -- 3t + 2t²
claims: output ⟨rootC, (3,5), 5⟩  left ⟨rootA, (3,4), 4⟩  right ⟨rootB, (4,5), 4⟩
```

`r = 4` rather than the audit turn's `2` because at `r = 2` the right opening
is `0` and the terminal check would be blind to a forged left value; at `r = 4`
both operand values are `4`, product `2 = g(4)`.

| theorem | proof | pins |
|---|---|---|
| `checker_complete_f7 : accepts stmt tr = true` | `decide` | route into `Checked` end to end on literal data |
| `wrong_suite_refused` → `unregisteredSuite` | `decide` | registry |
| `forged_output_value_refused` (5→6) → `roundSumMismatch 0` | `decide` | value bound to round 0 |
| `forged_left_opening_refused` (4→5) → `terminalMismatch` | `decide` | left opening load-bearing |
| `forged_right_opening_refused` (4→5) → `terminalMismatch` | `decide` | right opening load-bearing |
| `forged_root_refused` (one word entry) → `outputRootMismatch` | `decide` | root bound |
| `forged_point_refused` → `leftPointMismatch` | `decide` | point bound |
| `forged_round_message_refused` (c1 3→4) → `roundSumMismatch 0` | `decide` | message bound |
| `swapped_challenge_refused` (4→5, same claims) → `leftPointMismatch` | `decide` | ⚑ challenge bound to the opening points, not luck |

And the literal instance IS the honest one — not a fixture:

* `rootA_honest / rootB_honest / rootC_honest : rootX = S7.commit (basefoldWord dom₇₄ (flatten₂ X))`
  via a local `booleanMobiusPolynomial_two_eval` (the Möbius packing at
  `1+1` variables, from `parityInterleave = expand 2 even + X·expand 2 odd`
  and `Polynomial.expand_eval`), then `fin_cases <;> decide`;
* `message_honest : message = messageOf (matmulHonest eA eB ![3] ![5] (chalOf ![4]) 0)`
  — the four coefficients of `cubicRoundPoly` decided;
* `instance_statement_honest`, `instance_transcript_honest : tr = honestTranscript …`.
* `budget_f7 : matmulSuccinctSoundnessBudget F7 1 1 1 = 23/7`.

Kernel `decide` never touches a `Polynomial` (Finsupp is classical); the
replay is on `RoundMessage` coefficients, and `RoundMessage.poly_eval` /
`messageOf_eval` (degree < 4 ⇒ `eval_eq_sum_range'` over four terms) are the
only place the two meet, in theorems.

Instance was *not* shrunk — `μ=κ=ν=1` is the smallest nontrivial contraction
and it decided in the ordinary elaboration time of the file.

---

## 5. THE REGISTRY MOVE

`ZkmlMatmulSuccinctChecker` must bind the same registry as the audit turn, and
a later audit turn will consume the succinct checker; importing the turn into
the checker would be backwards and a second registry a twin. So
`AuditIdentity`, `auditIdentity`, `auditRegistry`, `auditIdentity_registered`,
`auditIdentity_matches_checker` moved verbatim to
`Assurance/ZkmlMatmulSuiteRegistry.lean` (namespace
`Minidregg.Assurance.ZkmlMatmulSuiteRegistry`); the turn imports and `open`s
it. `unregisteredIdentity` / `unregisteredIdentity_not_registered` are new
(decided). No non-Lean file references the old qualified names (grepped docs,
scripts, prover, notes).

---

## 6. BUILD EVIDENCE

Exit codes captured directly. Machine load 47–57 throughout.

| gate | result |
|---|---|
| `lake env lean Assurance/ZkmlMatmulSuiteRegistry.lean` | exit 0, silent |
| `lake build Assurance.ZkmlMatmulSuiteRegistry` (to mint its `.olean`; 2971 jobs *replayed*, 1 built) | exit 0 |
| `lake env lean Assurance/ZkmlMatmulSuccinctChecker.lean` | exit 0, silent after `omit`s |
| `lake env lean Assurance/ZkmlMatmulAuditTurn.lean` (post-move) | exit 0, silent |
| `lake build Assurance.ZkmlMatmulSuccinctChecker Assurance.ZkmlMatmulFramedWal` (targeted; rebuilds AuditTurn + FramedWal against the moved registry; 3013 jobs, 3 built, rest replayed) | exit 0, no warnings in the three modules |
| `scripts/check-import-boundary.sh` | exit 0 (Theory OK, Selvage OK) |
| `grep sorry` on both new files | 0 |
| axiom pins (`#guard_msgs … #print axioms`), 9 headline theorems | all `[propext, Classical.choice, Quot.sound]` |

No umbrella `lake build` was run (brief). `Assurance.lean` gained two import
lines with the house one-line ledger comments.

Falsifier sanity during development: the first draft's `simp only` in
`instance_transcript_honest` used `hvA : (4 : F7) = mle …` as a rewrite and
looped (the RHS contains `4`) — reversed to `mle … = 4`; and the first draft
of the F7 instance used `r = 2`, where the forged-left tooth would have been
vacuous (right value `0`). Both caught by reading the numbers, not by green.

---

## 7. WHAT THIS DOES NOT COVER — precisely

1. **Full-word, not sampled.** `BaseFoldIorAccepts` reads whole level words.
   Succinct *communication* is the sampled-query/BCS layer this composition
   deliberately does not price (`BaseFoldCommittedIor` retains it).
2. **Interactive.** `Draw × OpenDraw` are uniform; `[MATMUL-fs]` open.
3. **Identity commitment at the instance.** `idealCommitment`'s root is the
   word; `[COMMIT-CR]` is the deployed floor and is not claimed.
4. **No bytes.** The statement/transcript are Lean data; the neutral
   Preoscript/native byte binding is the row's next clause, untouched. Native
   output stays neutral because nothing here emits an acceptance bit.
5. **Operands are relative.** The checker certifies `C = A·B` for the committed
   `A`, `B`; nothing about which model or which layer.
6. **Toy field.** `23/7` is the honest number at the instance.
