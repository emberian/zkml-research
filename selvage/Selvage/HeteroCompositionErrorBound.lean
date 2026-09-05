/-
# Selvage.HeteroCompositionErrorBound — `[COMPOSE-error]`, audited

`HeteroCompositionSuccinct`'s closing aside: *`ComposeErrorBound` (`HeteroComposition:235`)
is provable from `err_nonneg` alone — an obligation that is either trivial or mis-stated.*
This file decides it, as theorems.

## The verdict: MIS-STATED, and here is the proof

`ComposeErrorBound` reads

    ∀ (A B : ProofSystem) (_ : VerifierEmbedding A B),
      KnowledgeSound B → ∀ ε, ε = A.err + B.err → 0 ≤ ε

and its docstring says "the composed knowledge error of a heterogeneous rung is at most the
sum of the two systems' errors". **The `Prop` does not say that.** Its conclusion is the
arithmetic fact `0 ≤ A.err + B.err`, which is `add_nonneg` on the two `err_nonneg` fields:

* `composeErrorBound_of_err_nonneg` — it closes, with no hypothesis used;
* `composeErrorBound_ignores_hypotheses` — the embedding and `KnowledgeSound B` are inert:
  the same body holds for arbitrary unrelated systems, and implies the obligation;
* `composeErrorBound_body_at_unembeddable` — the body holds at
  `(strictSystem, widenedSystem)`, the pair `widened_relation_refuses_embedding` proves
  admits NO embedding at all;
* `composeErrorBound_trivial_witness` — ⚑ every hypothesis of the obligation holds, its
  conclusion holds, and the rung they describe has a composed system that is
  knowledge-sound **nowhere**. Zero content, exhibited.

So the ledger row's `ComposeErrorBound` is discharged and says nothing.

## The honest statement, and why it needs two clauses

"The composed error is at most the sum" is not expressible about `ProofSystem` as it stands:
`err` is an uninterpreted real whose only tie to anything is `0 ≤ err`, so every `Prop`
relating `err` fields of abstract systems is either arithmetic (vacuous, as above) or false
(`err` can be set anywhere). An honest statement must give `err` a **semantics**. This file
gives the weakest one that supports a union bound — a nonnegative, monotone, subadditive
measure `EventMeasure Ω` on events over the adversary's coin space, with `err` bounding the
measure of `KsFailure` (`HeteroCompositionSuccinct:159`) — and then states

    ComposeErrorBoundStrict :
      μ(B fails at the embedded statement) ≤ B.err →      -- the target clause
      μ(∃ πA, A fails at the source statement) ≤ A.err →  -- ⚑ the transfer clause
      μ(the composed rung fails) ≤ A.err + B.err

`composeErrorBoundStrict_closes` proves it: the composed failure event is contained in the
union of the two, because `bwd` turns "`B`'s relation is satisfiable here" into an accepting
`A`-proof (`rung_sound`'s step), and containment + subadditivity is the whole bound. The
composed system is a definition (`composeSystem`) rather than a phrase, so "the composed
error" is a term.

⚑ **Both clauses are load-bearing, and neither is bookkeeping.**

* `composeErrorBoundStrict_transfer_load_bearing` refutes the transfer-clause-free version:
  a rung where `A.err = B.err = 0`, `B` is `KnowledgeSound`, the embedding exists, `B` never
  fails — and the composed rung fails with mass `1 > 0`. The transfer clause's event is
  `∃ πA, KsFailure A x πA`, an EXISTENTIAL over `A`-proofs rather than an adversary's
  output, so pricing it is a non-uniform demand on `A.err` — the same gap `TowerSoundRO`'s
  teeth name at `n ≥ 2` ("the proof `bwd` hands back is an existential, not an adversary the
  game bounds"), met here at one rung.
* `composeErrorBoundStrict_target_load_bearing` refutes the target-clause-free version **at
  the landed F₅ instance, not a toy**: at query budget `0` the acc system's error is
  `(0+2)/5 = 2/5`, its identity-carrier source never fails (so the transfer clause holds),
  and the composed rung fails at `(luckySt, luckyOut)` with mass `1`. **The naive sum is
  exceeded: `1 > 0 + 2/5`.** This is the `1/|F|` round event of `accRbrError`, priced.

ATLAS fields for `ComposeErrorBoundStrict`:
* **satisfiable, non-vacuously and TIGHTLY** — `composeErrorBoundStrict_fires_at_F5` /
  `composeErrorBoundStrict_tight_at_F5`: the same F₅ rung at query budget `3`, where
  `err = (3+2)/5 = 1`. The composed failure event is **inhabited** (`lucky_accepted` ∧
  `lucky_no_witness`), its mass is `1`, the composed error is `1`: the bound holds with
  EQUALITY. A satisfying witness that could have failed — at budget `0` it does.
* **refutable** — the two falsifiers above.
* **premise-inhabitation** — both hypotheses discharged at F₅ budget `3` (`f5_hyp_target`
  at a genuinely failing system, `f5_hyp_source` at the decider).

## `ComposeFixedPoint` is NOT in the same boat

`ComposeFixedPoint B := Nonempty (SelfEmbedding B) ∧ KnowledgeSound B` is parametrised by
`B`, and it has both teeth: `composeFixedPoint_trivial_witness` (it holds at
`trivialSystem`, so it is satisfiable) and `composeFixedPoint_refutable` (it FAILS at the
landed F₅ system, via `accBcsSystem_F5_not_knowledgeSound`). It is a real per-system demand
and stays listed — what is loose is only calling it an obligation without naming the `B`.

Nothing in `HeteroComposition.lean` or the docs is edited here; de-listing/re-wording the
`ComposeErrorBound` row of `docs/FORMAL_STATUS_AND_NEXT_PROOFS.md` is the coordinator's.

Design record: `zkml-research/notes/compose-error-bound.md`.
-/
import Selvage.HeteroCompositionSuccinct

namespace Minidregg.Selvage

open AccRbrBcsExample

/-! ## 1. The obligation as written: trivial, and its hypotheses are inert -/

/-- **`ComposeErrorBound` closes from `err_nonneg` alone.** Both hypotheses are discarded
(`-`), the equation is consumed by `rfl`, and what remains is `add_nonneg` on the two
`ProofSystem.err_nonneg` fields. The obligation named in
`docs/FORMAL_STATUS_AND_NEXT_PROOFS.md` is this. -/
theorem composeErrorBound_of_err_nonneg : ComposeErrorBound := by
  rintro A B - - ε rfl
  exact add_nonneg A.err_nonneg B.err_nonneg

/-- The embedding and `KnowledgeSound B` are **inert**: the body holds for two systems with
no relation to each other whatsoever. -/
theorem composeErrorBound_ignores_hypotheses :
    ∀ (A B : ProofSystem) (ε : ℝ), ε = A.err + B.err → 0 ≤ ε := by
  rintro A B ε rfl
  exact add_nonneg A.err_nonneg B.err_nonneg

/-- …and that hypothesis-free statement *implies* the obligation, so nothing about
composition is being used. -/
theorem composeErrorBound_of_ignoring
    (h : ∀ (A B : ProofSystem) (ε : ℝ), ε = A.err + B.err → 0 ≤ ε) :
    ComposeErrorBound :=
  fun A B _ _ => h A B

/-- ⚑ The body holds at the pair this repo proves is **not composable at all**:
`widened_relation_refuses_embedding` says `strictSystem → widenedSystem` admits no
`VerifierEmbedding`, and the "error bound" is satisfied there anyway. -/
theorem composeErrorBound_body_at_unembeddable :
    IsEmpty (VerifierEmbedding strictSystem widenedSystem) ∧
      ∀ ε, ε = strictSystem.err + widenedSystem.err → 0 ≤ ε :=
  ⟨widened_relation_refuses_embedding,
   fun _ h => h ▸ add_nonneg strictSystem.err_nonneg widenedSystem.err_nonneg⟩

/-! ## 2. The rung as a system, and a soundness-free inhabitant of it -/

/-- **The heterogeneous rung, as a `ProofSystem`**: `A`'s statements and witnesses, `B`'s
proofs, verification by `B` at the embedded statement, and the error the docstring of
`ComposeErrorBound` claims — `A.err + B.err`. Making the composition a definition is what
lets "the composed error" be a term rather than a phrase. -/
def composeSystem (A B : ProofSystem) (e : VerifierEmbedding A B) : ProofSystem where
  Stmt := A.Stmt
  Wit := A.Wit
  Proof := B.Proof
  Rel := A.Rel
  Verify := fun x π => B.Verify (e.encStmt x) π
  err := A.err + B.err
  err_nonneg := add_nonneg A.err_nonneg B.err_nonneg

/-- A system that accepts **everything** and whose relation holds of **nothing**, at a
chosen error `ε`. Maximally unsound at any error — including `0`. -/
def flatSystem (ε : ℝ) (hε : 0 ≤ ε) : ProofSystem where
  Stmt := Unit
  Wit := Unit
  Proof := Unit
  Rel := fun _ _ => False
  Verify := fun _ _ => true
  err := ε
  err_nonneg := hε

/-- The canonical target of `flatSystem ε`: the system whose relation IS `flatSystem`'s
verifier. Since that verifier accepts everything, this system is knowledge-sound. -/
def flatTarget (ε : ℝ) (hε : 0 ≤ ε) : ProofSystem :=
  verifierRelationSystem (flatSystem ε hε) Unit (fun _ _ => true) ε hε

/-- The canonical embedding `flatSystem ε ↪ flatTarget ε`. It exists, for free — as
`canonicalEmbedding`'s docstring says, the embedding is not where recursion is hard. -/
def flatEmbedding (ε : ℝ) (hε : 0 ≤ ε) :
    VerifierEmbedding (flatSystem ε hε) (flatTarget ε hε) :=
  canonicalEmbedding (flatSystem ε hε) Unit (fun _ _ => true) ε hε

theorem flatTarget_knowledgeSound (ε : ℝ) (hε : 0 ≤ ε) :
    KnowledgeSound (flatTarget ε hε) :=
  fun _ _ _ => ⟨(), rfl⟩

theorem flatSystem_not_knowledgeSound (ε : ℝ) (hε : 0 ≤ ε) :
    ¬ KnowledgeSound (flatSystem ε hε) := by
  intro h
  obtain ⟨w, hw⟩ := h () () rfl
  exact hw

/-- The composed rung `flatSystem ↪ flatTarget` is knowledge-sound **nowhere**: it accepts
everything and its relation holds of nothing. -/
theorem composeSystem_flat_not_knowledgeSound (ε : ℝ) (hε : 0 ≤ ε) :
    ¬ KnowledgeSound (composeSystem (flatSystem ε hε) (flatTarget ε hε)
      (flatEmbedding ε hε)) := by
  intro h
  obtain ⟨w, hw⟩ := h () () rfl
  exact hw

/-- ⚑⚑ **The obligation has no content, exhibited.** At `ε = 1` — a rung of two systems
whose errors are the *maximum* a probability can be — every hypothesis of
`ComposeErrorBound` holds (the embedding exists, the target is knowledge-sound), its
conclusion holds (`0 ≤ 1 + 1`), and the composed system is knowledge-sound at no statement
whatsoever. An obligation a maximally broken tower satisfies is not the obligation the
ledger meant. -/
theorem composeErrorBound_trivial_witness :
    Nonempty (VerifierEmbedding (flatSystem 1 zero_le_one) (flatTarget 1 zero_le_one)) ∧
    KnowledgeSound (flatTarget 1 zero_le_one) ∧
    (∀ ε, ε = (flatSystem 1 zero_le_one).err + (flatTarget 1 zero_le_one).err → 0 ≤ ε) ∧
    ¬ KnowledgeSound (composeSystem (flatSystem 1 zero_le_one) (flatTarget 1 zero_le_one)
        (flatEmbedding 1 zero_le_one)) :=
  ⟨⟨flatEmbedding 1 zero_le_one⟩,
   flatTarget_knowledgeSound 1 zero_le_one,
   fun _ h => h ▸ add_nonneg (flatSystem 1 zero_le_one).err_nonneg
     (flatTarget 1 zero_le_one).err_nonneg,
   composeSystem_flat_not_knowledgeSound 1 zero_le_one⟩

/-! ## 3. An error SEMANTICS — the weakest one a union bound needs -/

/-- **An error semantics.** `err` is an uninterpreted real in `ProofSystem`; to say
"the composed error is at most the sum" one must first say what an error *measures*. This
is the weakest structure the union bound uses: a nonnegative, monotone, subadditive
real-valued measure on events over a coin space `Ω`. `uniformProb` on a `Fintype` is one;
so is the point mass below. -/
structure EventMeasure (Ω : Type) where
  μ : (Ω → Prop) → ℝ
  nonneg : ∀ E, 0 ≤ μ E
  mono : ∀ E F, (∀ ω, E ω → F ω) → μ E ≤ μ F
  subadd : ∀ E F, μ (fun ω => E ω ∨ F ω) ≤ μ E + μ F

open Classical in
/-- The point mass at `ω₀`: an event has measure `1` iff it happens there. -/
noncomputable def pointMass {Ω : Type} (ω₀ : Ω) (E : Ω → Prop) : ℝ :=
  if E ω₀ then 1 else 0

theorem pointMass_of_true {Ω : Type} {ω₀ : Ω} {E : Ω → Prop} (h : E ω₀) :
    pointMass ω₀ E = 1 := by
  classical
  simp [pointMass, h]

theorem pointMass_of_false {Ω : Type} {ω₀ : Ω} {E : Ω → Prop} (h : ¬ E ω₀) :
    pointMass ω₀ E = 0 := by
  classical
  simp [pointMass, h]

theorem pointMass_nonneg {Ω : Type} (ω₀ : Ω) (E : Ω → Prop) : 0 ≤ pointMass ω₀ E := by
  by_cases h : E ω₀
  · rw [pointMass_of_true h]; norm_num
  · rw [pointMass_of_false h]

theorem pointMass_mono {Ω : Type} (ω₀ : Ω) (E F : Ω → Prop) (h : ∀ ω, E ω → F ω) :
    pointMass ω₀ E ≤ pointMass ω₀ F := by
  by_cases hE : E ω₀
  · rw [pointMass_of_true hE, pointMass_of_true (h ω₀ hE)]
  · rw [pointMass_of_false hE]
    exact pointMass_nonneg ω₀ F

theorem pointMass_subadd {Ω : Type} (ω₀ : Ω) (E F : Ω → Prop) :
    pointMass ω₀ (fun ω => E ω ∨ F ω) ≤ pointMass ω₀ E + pointMass ω₀ F := by
  by_cases hE : E ω₀
  · rw [pointMass_of_true (E := fun ω => E ω ∨ F ω) (Or.inl hE), pointMass_of_true hE]
    have := pointMass_nonneg ω₀ F
    linarith
  · by_cases hF : F ω₀
    · rw [pointMass_of_true (E := fun ω => E ω ∨ F ω) (Or.inr hF), pointMass_of_false hE,
        pointMass_of_true hF]
      norm_num
    · rw [pointMass_of_false (E := fun ω => E ω ∨ F ω)
          (by rintro (h | h); exacts [hE h, hF h]),
        pointMass_of_false hE, pointMass_of_false hF]
      norm_num

/-- The point mass as an `EventMeasure`. -/
noncomputable def diracMeasure {Ω : Type} (ω₀ : Ω) : EventMeasure Ω where
  μ := pointMass ω₀
  nonneg := pointMass_nonneg ω₀
  mono := pointMass_mono ω₀
  subadd := pointMass_subadd ω₀

/-! ## 4. `[COMPOSE-error]`, honestly -/

/-- ⚑ **`[COMPOSE-error]`, as the docstring meant it.** For an adversary that produces a
source statement `X ω` and a target proof `P ω` from the coins `ω`:

* if `B.err` prices `B`'s knowledge-soundness failure at the embedded statements the
  adversary reaches (**the target clause**), and
* if `A.err` prices the `A`-side failure `bwd` exhibits — ⚑ **the transfer clause**, whose
  event is an EXISTENTIAL over `A`-proofs rather than an adversary's output, and which is
  therefore a real demand and not bookkeeping —

then the composed rung's failure is priced by `A.err + B.err`, the number `composeSystem`
carries. Unlike `ComposeErrorBound`, this statement mentions the composed system's failure
event, and it is FALSE with either clause dropped
(`composeErrorBoundStrict_transfer_load_bearing`,
`composeErrorBoundStrict_target_load_bearing`). -/
def ComposeErrorBoundStrict : Prop :=
  ∀ (Ω : Type) (m : EventMeasure Ω) (A B : ProofSystem) (e : VerifierEmbedding A B)
    (X : Ω → A.Stmt) (P : Ω → B.Proof),
    m.μ (fun ω => KsFailure B (e.encStmt (X ω)) (P ω)) ≤ B.err →
    m.μ (fun ω => ∃ πA, KsFailure A (X ω) πA) ≤ A.err →
    m.μ (fun ω => KsFailure (composeSystem A B e) (X ω) (P ω))
      ≤ (composeSystem A B e).err

/-- **It closes.** Containment then subadditivity: at coins where the composed rung fails,
either `B`'s relation is unsatisfiable at the embedded statement (`B` fails there), or it is
satisfiable and `bwd` — `rung_sound`'s step — returns an accepting `A`-proof at a statement
with no `A`-witness (`A` fails there). -/
theorem composeErrorBoundStrict_closes : ComposeErrorBoundStrict := by
  intro Ω m A B e X P hB hA
  refine le_trans (m.mono _
    (fun ω => (∃ πA, KsFailure A (X ω) πA) ∨ KsFailure B (e.encStmt (X ω)) (P ω)) ?_)
    (le_trans (m.subadd _ _) (add_le_add hA hB))
  rintro ω ⟨hacc, hno⟩
  by_cases hw : ∃ w, B.Rel (e.encStmt (X ω)) w
  · obtain ⟨w, hw⟩ := hw
    obtain ⟨πA, -, hAacc⟩ := e.bwd (X ω) w hw
    exact Or.inl ⟨πA, hAacc, hno⟩
  · exact Or.inr ⟨hacc, not_exists.mp hw⟩

/-! ## 5. ⚑ Falsifier I — the TRANSFER clause is load-bearing -/

theorem flatTarget_ksFailure_empty (ε : ℝ) (hε : 0 ≤ ε) (x : (flatTarget ε hε).Stmt)
    (π : (flatTarget ε hε).Proof) : ¬ KsFailure (flatTarget ε hε) x π :=
  (knowledgeSound_iff_no_ksFailure _).mp (flatTarget_knowledgeSound ε hε) x π

/-- ⚑⚑ **`ComposeErrorBoundStrict` without the transfer clause is FALSE.** At
`flatSystem 0 ↪ flatTarget 0`: the embedding exists, the target is `KnowledgeSound`, its
failure has measure `0 ≤ 0 = B.err`, and both errors are `0` — yet the composed rung fails
with mass `1`, and `¬ (1 ≤ 0)`. The one hypothesis of the strict statement that fails here
is the transfer clause. -/
theorem composeErrorBoundStrict_transfer_load_bearing :
    KnowledgeSound (flatTarget 0 le_rfl) ∧
    (diracMeasure (Ω := Unit) ()).μ
        (fun _ => KsFailure (flatTarget 0 le_rfl)
          ((flatEmbedding 0 le_rfl).encStmt ()) ()) ≤ (flatTarget 0 le_rfl).err ∧
    ¬ (diracMeasure (Ω := Unit) ()).μ
        (fun _ => ∃ πA, KsFailure (flatSystem 0 le_rfl) () πA)
        ≤ (flatSystem 0 le_rfl).err ∧
    ¬ (diracMeasure (Ω := Unit) ()).μ
        (fun _ => KsFailure
          (composeSystem (flatSystem 0 le_rfl) (flatTarget 0 le_rfl)
            (flatEmbedding 0 le_rfl)) () ())
        ≤ (composeSystem (flatSystem 0 le_rfl) (flatTarget 0 le_rfl)
            (flatEmbedding 0 le_rfl)).err := by
  refine ⟨flatTarget_knowledgeSound 0 le_rfl, ?_, ?_, ?_⟩
  · have h : (diracMeasure (Ω := Unit) ()).μ
        (fun _ => KsFailure (flatTarget 0 le_rfl)
          ((flatEmbedding 0 le_rfl).encStmt ()) ()) = 0 :=
      pointMass_of_false (flatTarget_ksFailure_empty 0 le_rfl _ _)
    rw [h]
    exact le_rfl
  · have h : (diracMeasure (Ω := Unit) ()).μ
        (fun _ => ∃ πA, KsFailure (flatSystem 0 le_rfl) () πA) = 1 :=
      pointMass_of_true ⟨(), rfl, fun w hw => hw⟩
    rw [h]
    show ¬ (1 : ℝ) ≤ 0
    norm_num
  · have h : (diracMeasure (Ω := Unit) ()).μ
        (fun _ => KsFailure
          (composeSystem (flatSystem 0 le_rfl) (flatTarget 0 le_rfl)
            (flatEmbedding 0 le_rfl)) () ()) = 1 :=
      pointMass_of_true ⟨rfl, fun w hw => hw⟩
    rw [h]
    show ¬ (1 : ℝ) ≤ 0 + 0
    norm_num

/-! ## 6. The landed F₅ rung — tight witness at budget `3`, falsifier at budget `0` -/

/-- The decider of a relation is always knowledge-sound: its proof *is* a witness. -/
theorem relDecider_knowledgeSound (B : ProofSystem) : KnowledgeSound (relDecider B) := by
  intro _ w h
  classical
  exact ⟨w, of_decide_eq_true h⟩

theorem relDecider_ksFailure_empty (B : ProofSystem) (x : (relDecider B).Stmt)
    (π : (relDecider B).Proof) : ¬ KsFailure (relDecider B) x π :=
  (knowledgeSound_iff_no_ksFailure _).mp (relDecider_knowledgeSound B) x π

/-- The landed F₅ acc system at query budget `b`; `accBcsSystem_F5_err` gives
`err = (b + 2)·(1/5)`. -/
noncomputable abbrev f5System (b : ℕ) : ProofSystem := accBcsSystem_F5 b oneOracle

/-- The source of its identity carrier: the decider of its relation. `err = 0`. -/
noncomputable abbrev f5Source (b : ℕ) : ProofSystem := relDecider (f5System b)

noncomputable abbrev f5Embedding (b : ℕ) : VerifierEmbedding (f5Source b) (f5System b) :=
  relDeciderEmbedding (f5System b)

/-- The composed rung's carried error: `0 + (b + 2)·(1/5)`. -/
theorem f5_compose_err (b : ℕ) :
    (composeSystem (f5Source b) (f5System b) (f5Embedding b)).err
      = ((b : ℝ) + 2) * (1 / 5) := by
  show (0 : ℝ) + (accBcsSystem_F5 b oneOracle).err = _
  rw [accBcsSystem_F5_err]
  ring

/-- ⚑ **The composed rung's failure event is INHABITED at the landed instance**:
`luckyOut` is accepted at `luckySt` (`lucky_accepted`) and `luckySt` has no witness in
`R_{≤1/32}` (`lucky_no_witness`). This is the `1/|F|` round event of `accRbrError`. -/
theorem f5_compose_ksFailure (b : ℕ) :
    KsFailure (composeSystem (f5Source b) (f5System b) (f5Embedding b)) luckySt luckyOut :=
  ⟨lucky_accepted b, fun w hw => lucky_no_witness w hw⟩

theorem f5_compose_mass (b : ℕ) :
    (diracMeasure (Ω := Unit) ()).μ
      (fun _ => KsFailure (composeSystem (f5Source b) (f5System b) (f5Embedding b))
        luckySt luckyOut) = 1 :=
  pointMass_of_true (f5_compose_ksFailure b)

theorem f5_target_mass (b : ℕ) :
    (diracMeasure (Ω := Unit) ()).μ
      (fun _ => KsFailure (f5System b) ((f5Embedding b).encStmt luckySt) luckyOut) = 1 :=
  pointMass_of_true ⟨lucky_accepted b, fun w hw => lucky_no_witness w hw⟩

theorem f5_source_mass (b : ℕ) :
    (diracMeasure (Ω := Unit) ()).μ
      (fun _ => ∃ πA, KsFailure (f5Source b) luckySt πA) = 0 :=
  pointMass_of_false (by
    rintro ⟨πA, h⟩
    exact relDecider_ksFailure_empty (f5System b) _ _ h)

/-- The transfer hypothesis, discharged at every budget: the source is the decider of the
relation, which never fails, and its error is `0`. -/
theorem f5_hyp_source (b : ℕ) :
    (diracMeasure (Ω := Unit) ()).μ
      (fun _ => ∃ πA, KsFailure (f5Source b) luckySt πA) ≤ (f5Source b).err := by
  rw [f5_source_mass]
  show (0 : ℝ) ≤ 0
  exact le_rfl

/-- ⚑ The target hypothesis, discharged **at a system that genuinely fails**: the failure
mass is `1`, met exactly by `err = (3 + 2)/5 = 1` at query budget `3`. -/
theorem f5_hyp_target :
    (diracMeasure (Ω := Unit) ()).μ
        (fun _ => KsFailure (f5System 3) ((f5Embedding 3).encStmt luckySt) luckyOut)
      ≤ (f5System 3).err := by
  rw [f5_target_mass]
  show (1 : ℝ) ≤ (accBcsSystem_F5 3 oneOracle).err
  rw [accBcsSystem_F5_err]
  norm_num

/-- **The strict bound fires at the F₅ instance**, budget `3`. -/
theorem composeErrorBoundStrict_fires_at_F5 :
    (diracMeasure (Ω := Unit) ()).μ
      (fun ω => KsFailure (composeSystem (f5Source 3) (f5System 3) (f5Embedding 3))
        ((fun _ => luckySt) ω) ((fun _ => luckyOut) ω))
      ≤ (composeSystem (f5Source 3) (f5System 3) (f5Embedding 3)).err :=
  composeErrorBoundStrict_closes Unit (diracMeasure ()) (f5Source 3) (f5System 3)
    (f5Embedding 3) (fun _ => luckySt) (fun _ => luckyOut) f5_hyp_target (f5_hyp_source 3)

/-- ⚑⚑ **And it is TIGHT, not slack.** At budget `3` the composed failure mass is `1` and
the composed error `0 + (3+2)/5` is `1`: the bound holds with EQUALITY. A satisfying
witness that could have failed — and at budget `0` it does
(`composeErrorBoundStrict_target_load_bearing`). -/
theorem composeErrorBoundStrict_tight_at_F5 :
    KsFailure (composeSystem (f5Source 3) (f5System 3) (f5Embedding 3)) luckySt luckyOut ∧
    (diracMeasure (Ω := Unit) ()).μ
        (fun _ => KsFailure (composeSystem (f5Source 3) (f5System 3) (f5Embedding 3))
          luckySt luckyOut)
      = (composeSystem (f5Source 3) (f5System 3) (f5Embedding 3)).err := by
  refine ⟨f5_compose_ksFailure 3, ?_⟩
  rw [f5_compose_mass, f5_compose_err]
  norm_num

/-- ⚑⚑ **Falsifier II — the TARGET clause is load-bearing, at the LANDED instance.** At
query budget `0` the acc F₅ system's error is `(0+2)·(1/5) = 2/5`. The transfer clause
holds (the decider never fails, error `0`), the target clause FAILS (the acc system's
failure mass is `1 > 2/5`), and **the naive sum is exceeded**: the composed rung fails with
mass `1` against a carried error of `0 + 2/5`. This is the tower the docstring's "at most
the sum of the two systems' errors" would have to exclude, and the clause that excludes
it. -/
theorem composeErrorBoundStrict_target_load_bearing :
    (diracMeasure (Ω := Unit) ()).μ
        (fun _ => ∃ πA, KsFailure (f5Source 0) luckySt πA) ≤ (f5Source 0).err ∧
    ¬ (diracMeasure (Ω := Unit) ()).μ
        (fun _ => KsFailure (f5System 0) ((f5Embedding 0).encStmt luckySt) luckyOut)
        ≤ (f5System 0).err ∧
    ¬ (diracMeasure (Ω := Unit) ()).μ
        (fun _ => KsFailure (composeSystem (f5Source 0) (f5System 0) (f5Embedding 0))
          luckySt luckyOut)
        ≤ (composeSystem (f5Source 0) (f5System 0) (f5Embedding 0)).err := by
  refine ⟨f5_hyp_source 0, ?_, ?_⟩
  · rw [f5_target_mass]
    show ¬ (1 : ℝ) ≤ (accBcsSystem_F5 0 oneOracle).err
    rw [accBcsSystem_F5_err]
    norm_num
  · rw [f5_compose_mass, f5_compose_err]
    norm_num

/-! ## 7. `ComposeFixedPoint` — genuinely two-sided, and it stays -/

/-- The system that proves nothing: its relation holds of everything. -/
def trivialSystem : ProofSystem where
  Stmt := Unit
  Wit := Unit
  Proof := Unit
  Rel := fun _ _ => True
  Verify := fun _ _ => true
  err := 0
  err_nonneg := le_refl 0

/-- It verifies itself, trivially — `encProof` is the identity on `Unit`. -/
def trivialSelfEmbedding : SelfEmbedding trivialSystem where
  encStmt := id
  encProof := id
  fwd := fun _ _ _ => trivial
  bwd := fun _ w _ => ⟨w, rfl, rfl⟩

/-- **SATISFIABLE** — but only at a system that proves nothing, which is what makes
`ComposeFixedPoint` a demand about a NAMED `B` rather than a theorem. -/
theorem composeFixedPoint_trivial_witness : ComposeFixedPoint trivialSystem :=
  ⟨⟨trivialSelfEmbedding⟩, fun _ _ _ => ⟨(), trivial⟩⟩

/-- **REFUTABLE** — it FAILS at the landed F₅ system, whose second conjunct is exactly
`accBcsSystem_F5_not_knowledgeSound`. So `ComposeFixedPoint` is neither trivial nor
mis-stated: unlike `ComposeErrorBound` it stays on the ledger. -/
theorem composeFixedPoint_refutable (b : ℕ) : ¬ ComposeFixedPoint (f5System b) :=
  fun h => accBcsSystem_F5_not_knowledgeSound b h.2

/-! ## Axiom audit

Every theorem above except the five `pointMass_*` measure-API lemmas, which are audited
transitively through their consumers. -/

/-- info: 'Minidregg.Selvage.composeErrorBound_of_err_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms composeErrorBound_of_err_nonneg
/-- info: 'Minidregg.Selvage.composeErrorBound_ignores_hypotheses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms composeErrorBound_ignores_hypotheses
/-- info: 'Minidregg.Selvage.composeErrorBound_of_ignoring' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms composeErrorBound_of_ignoring
/-- info: 'Minidregg.Selvage.composeErrorBound_body_at_unembeddable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms composeErrorBound_body_at_unembeddable
/-- info: 'Minidregg.Selvage.composeErrorBound_trivial_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms composeErrorBound_trivial_witness
/-- info: 'Minidregg.Selvage.flatTarget_knowledgeSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms flatTarget_knowledgeSound
/-- info: 'Minidregg.Selvage.flatSystem_not_knowledgeSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms flatSystem_not_knowledgeSound
/-- info: 'Minidregg.Selvage.composeSystem_flat_not_knowledgeSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms composeSystem_flat_not_knowledgeSound
/-- info: 'Minidregg.Selvage.flatTarget_ksFailure_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms flatTarget_ksFailure_empty
/-- info: 'Minidregg.Selvage.composeErrorBoundStrict_closes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms composeErrorBoundStrict_closes
/-- info: 'Minidregg.Selvage.composeErrorBoundStrict_transfer_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms composeErrorBoundStrict_transfer_load_bearing
/-- info: 'Minidregg.Selvage.relDecider_knowledgeSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms relDecider_knowledgeSound
/-- info: 'Minidregg.Selvage.relDecider_ksFailure_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms relDecider_ksFailure_empty
/-- info: 'Minidregg.Selvage.f5_compose_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms f5_compose_err
/-- info: 'Minidregg.Selvage.f5_compose_ksFailure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms f5_compose_ksFailure
/-- info: 'Minidregg.Selvage.f5_compose_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms f5_compose_mass
/-- info: 'Minidregg.Selvage.f5_target_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms f5_target_mass
/-- info: 'Minidregg.Selvage.f5_source_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms f5_source_mass
/-- info: 'Minidregg.Selvage.f5_hyp_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms f5_hyp_target
/-- info: 'Minidregg.Selvage.f5_hyp_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms f5_hyp_source
/-- info: 'Minidregg.Selvage.composeErrorBoundStrict_fires_at_F5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms composeErrorBoundStrict_fires_at_F5
/-- info: 'Minidregg.Selvage.composeErrorBoundStrict_tight_at_F5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms composeErrorBoundStrict_tight_at_F5
/-- info: 'Minidregg.Selvage.composeErrorBoundStrict_target_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms composeErrorBoundStrict_target_load_bearing
/-- info: 'Minidregg.Selvage.composeFixedPoint_trivial_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms composeFixedPoint_trivial_witness
/-- info: 'Minidregg.Selvage.composeFixedPoint_refutable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms composeFixedPoint_refutable

end Minidregg.Selvage
