/-
# Selvage.AccRbrFoldExtract — census upgrade 3, resolved the other way:
the fold round bound has a FLOOR OF ONE at the compressing witness type
(for EVERY extractor), and the un-fold extractor exists — at error ZERO —
exactly when the witness carries the absorbed openings.

`Selvage/AccRbrFold.lean` enters `[ACC-rbr-fold-resid](a)` statement-first as
`FoldRoundBound`, parametrised by a caller-supplied round extractor, with
`foldRoundBound_one` (satisfiable at `ε ≡ 1`) as its satisfiability witness
and this file's `foldRoundBound_floor` as its teeth
(`ToyFold.toy_roundBound_zero_id_false`, the identity extractor refuted at
`ε ≡ 0`, is the subsumed special case). The census
(`unit-witness-census.md` §7 item 3)
asked for a CONSTRUCTED extractor and a proof of the round bound at the
per-absorbed-commitment `ε_MSIS`. This file answers with two theorems whose
conjunction is the honest shape of the residual:

* **`foldRoundBound_floor` — the zero-absorb attack.** At ANY scheme, any
  genesis `C₀ = commit Z` with `b₀ < ‖Z‖ ≤ b₀ + ρ·B` (one step over budget,
  inside the next budget) and binding at `‖Z‖`, absorbing the ZERO commitment
  `π = 0` puts `Z` in the extended knowledge state (it is a `budget b₀ 1`-short
  opening of `C₀ + ρ•0 = C₀`) while NO witness is in the prefix state (a
  `b₀`-short opening of `commit Z` would equal `Z` by binding, and `Z` is
  not `b₀`-short). The round event fires at EVERY challenge, whatever the
  extractor returns: `FoldRoundBound … extractFn ε` forces `1 ≤ ε δ`. So the
  `ε_MSIS` pricing the census asked for is FALSE for every `extractFn`, and
  `foldRoundBound_one` is TIGHT, not merely satisfiable. The reason is
  structural, not a weak extractor: the compressing fold's target relation
  (ONE plane vector opens the fold at `budget b₀ T`) cannot distinguish a
  `b₀`-short genesis plus `T` honest absorptions from a `(b₀ + ρB)`-short
  genesis plus a zero absorption, and Def 4.2 is single-transcript — the
  2–3-transcript rewinding that lattice folding actually extracts with is
  not in this tree's `RbrKnowledgeSoundness`.
  Instances: `ToyFold.toy_roundBound_floor` (every hypothesis DISCHARGED at
  the toy, riding `toy_binding_T1`) and
  `DualModeParams.production_roundBound_floor` (at the production scheme,
  under the same `[FOLD-msis]` hypothesis the positive half already assumes).

* **`foldCarriedRoundBound_zero` — the un-fold extractor, at the witness type
  that can carry it.** `foldReductionCarried` is the same fold with witness
  `W × (Fin T → W)`: the running opening PLUS the `B`-short openings of the
  absorbed commitments, which the target relation pins (`X' := C × (Fin T → C)`
  carries the absorbed commitments so `R'` can name them). `foldExtract` is the
  linear un-fold `(Y, Ys) ↦ (Y − ρ_i • Ys i, Ys)`: the commitment un-folds
  exactly (`commit` is linear), and the norm grows by `ρ·B` per un-fold
  (`nrm_sub` + `nrm_smul`). The knowledge state therefore runs a DESCENDING
  budget `budget b₀ (2T − c)` — `budget b₀ (2T)` at genesis, `budget b₀ T` at
  the full fold — and the round event is EMPTY: error `0`, unconditionally,
  no MSIS hypothesis. The price has moved, not vanished: the source relation
  is the RELAXED opening `ShortOpens (budget b₀ (2T)) C₀` — the extracted
  genesis witness is `(b₀ + 2T·ρB)`-short, twice the honest fold budget.
  Binding at that slack is the file's `fold_binding` at `2·budget b₀ (2T)`,
  and at the production point the capacity HALVES:
  `DualModeParams.carried_capacity_safe` (through `T ≤ 2^46 − 1`) /
  `DualModeParams.carried_break` (at `T ≥ 2^46`, binding of the extracted
  genesis opening is LOST, every key).

## Honest scope

* `foldReductionCarried`'s decider checks `T + 1` openings: it is NOT succinct.
  SCOPE of that conclusion — resource model (i) ONLY, the PUBLIC-TRANSCRIPT-
  ONLY extractor: it sees exactly what the verifier sees, which is what
  `RbrKnowledgeSoundness` and the `(t + k)·ε` compositions model. In model
  (i) the zero-absorb attack refutes a contract that admits an already-
  invalid genesis opening and asks a challenge-dependent step to certify
  the missing shortness (the challenge space is irrelevant to it), and the
  carried witness is the object that discharges Def 4.2. The `T + 1`
  theorem says NOTHING about (ii) straight-line extraction with a trapdoor /
  RO-query interface / prescribed prover access, nor about (iii) ONLINE
  extraction — extract each incoming witness, update a running state,
  discard it — where live extractor memory, total extraction work, output
  size, and decider work are FOUR different quantities and a theorem about
  one is not a theorem about the others. Routes not in this tree: (ii),
  (iii), and rewinding. "Not succinct" here is measured in model (i) alone.
* `MsisHardEx` enters nowhere in the round bound of the carried fold. It
  enters where it always did: binding of the (now relaxed) genesis opening,
  `fold_binding`, at a doubled budget. No new computational `Prop` is named
  because none is consumed by the theorems here.
* `AccRbrFold.lean` carries NO extractor-parametric consumer of
  `FoldRoundBound` any more: the `extractFn`-generic Def-4.2 packaging and
  the depth/FS compositions over `foldReduction` it once had were vacuous
  below error `T` by `foldRoundBound_floor`, and are retired
  (`repair-fold-callers.md`). The compressing reduction's one Def-4.2
  instance in the tree is the trivial `ε ≡ 1` one, built inline at its
  single use (`foldOB2Unguarded_false`, the error-algebra corner). The
  compositions live HERE, at the carried fold: `foldCarried_depth_composition`
  / `foldCarried_fs_sound` at error `0`, extractor CONSTRUCTED, no parameter.

Design record: `zkml-research/notes/fold-extractor-upgrade.md`.
-/
import Selvage.AccRbrFold
import Selvage.AuditSampling

namespace Minidregg.Selvage

/-! ## The floor: the zero-absorb attack, for every extractor -/

section FoldFloor

variable {R : Type} [Ring R] {W C : Type} [AddCommGroup W] [AddCommGroup C]
  [Module R W] [Module R C]
  (S : FoldCommitScheme R W C) (T : ℕ) (hT : 0 < T) (Kh : Type)
  [Fintype Kh] [Nonempty Kh] (chalVal : Kh → R) (b₀ : ℝ)

/-- **The zero-absorb attack: `FoldRoundBound` has a floor of ONE, for EVERY
extractor.** Data: a witness `Z` one step over the genesis budget but inside
the one-fold budget, and binding at `‖Z‖`. Statement `C₀ := commit Z`, round
`0`, pending message `π := 0`. At every challenge `ρ` the extended fold is
`C₀ + ρ • 0 = C₀`, so `Z` is in the extended state (`budget b₀ 1`-short); a
witness in the prefix state would be a `b₀`-short opening of `commit Z`,
hence `= Z` by binding, hence not `b₀`-short. The prefix state is EMPTY and
the round event is the whole challenge space: `Pr = 1 ≤ ε δ`.

Read against the file's keystone pair: `foldRoundBound_one` is TIGHT (the
Prop's only inhabitants at a binding instance are at `ε ≥ 1`), and
`toy_roundBound_zero_id_false` was never about the identity extractor. -/
theorem foldRoundBound_floor (Z : W) (hlo : b₀ < S.nrm Z)
    (hhi : S.nrm Z ≤ S.budget b₀ 1) (hbind : S.BindingAt (S.nrm Z))
    (extractFn : Stmt (foldReduction S T hT Kh chalVal b₀) →
      Transcript C Kh → W → W) (εfold : ℝ → ℝ)
    (h : FoldRoundBound S T hT Kh chalVal b₀ extractFn εfold) :
    ∀ δ ∈ Set.Ioo (0 : ℝ) 1, 1 ≤ εfold δ := by
  intro δ hδ
  classical
  have hh := h δ hδ ⟨(), S.commit Z, fun _ => ()⟩ ⟨0, hT⟩ [] rfl 0
  have hall : ∀ ρ : Kh, ∃ Y : W,
      (foldKState S T hT Kh chalVal b₀).state δ ⟨(), S.commit Z, fun _ => ()⟩
          ⟨[], some 0⟩
          (extractFn ⟨(), S.commit Z, fun _ => ()⟩ ⟨[] ++ [(0, ρ)], none⟩ Y)
        = false ∧
      (foldKState S T hT Kh chalVal b₀).state δ ⟨(), S.commit Z, fun _ => ()⟩
          ⟨[] ++ [(0, ρ)], none⟩ Y = true := by
    intro ρ
    refine ⟨Z, ?_, ?_⟩
    · show decide (FoldStateProp S Kh chalVal b₀ (S.commit Z) [] _) = false
      rw [decide_eq_false_iff_not]
      rintro ⟨hcom, hn⟩
      rw [chalFoldList_nil] at hcom
      rw [List.length_nil, S.budget_zero] at hn
      have hYZ := hbind _ Z hcom (le_trans hn (le_of_lt hlo)) le_rfl
      rw [hYZ] at hn
      exact absurd hlo (not_lt.mpr hn)
    · show decide (FoldStateProp S Kh chalVal b₀ (S.commit Z)
        ([] ++ [(0, ρ)]) Z) = true
      rw [decide_eq_true_eq]
      refine ⟨?_, ?_⟩
      · rw [List.nil_append, chalFoldList_cons, chalFoldList_nil, smul_zero,
          add_zero]
      · rw [List.nil_append, List.length_singleton]
        exact hhi
  have hone := uniformProb_congr (C := Kh) (q := fun _ => True)
    (fun ρ => iff_true_intro (hall ρ))
  rw [hone, uniformProb_true] at hh
  exact hh

end FoldFloor

/-! ## The carried-openings fold — the witness type at which the un-fold
extractor EXISTS -/

section FoldCarried

variable {R : Type} [Ring R] {W C : Type} [AddCommGroup W] [AddCommGroup C]
  [Module R W] [Module R C]

/-- **The fold accumulator with CARRIED absorbed openings.** Same `k = T`
rounds, same messages (the absorbed commitments), same verifier-computed
fold as `foldReduction`; the differences are exactly what single-transcript
backward extraction needs:
* witness `W × (Fin T → W)` — the running opening plus one `B`-short opening
  per absorbed commitment;
* target explicit instance `C × (Fin T → C)` — the fold AND the absorbed
  commitments, so `R'` can pin each carried opening to its commitment;
* source relation RELAXED to `budget b₀ (2T)`: the un-fold grows the norm by
  `ρ·B` per step from the `budget b₀ T` target, so the extracted genesis
  opening is `(b₀ + 2T·ρB)`-short — the slack is the price, stated on the
  relation, not hidden in an error term.
The decider checks `T + 1` openings: this reduction does NOT compress. -/
@[reducible] def foldReductionCarried (S : FoldCommitScheme R W C) (T : ℕ)
    (hT : 0 < T) (Kh : Type) [Fintype Kh] [Nonempty Kh] (chalVal : Kh → R)
    (b₀ : ℝ) : Reduction where
  Idx := Unit
  X := C
  A := Unit
  X' := C × (Fin T → C)
  A' := Unit
  W := W × (Fin T → W)
  n := 1
  n' := 1
  n_pos := one_pos
  n'_pos := one_pos
  R := fun _ C₀ _ w => S.ShortOpens (S.budget b₀ (2 * T)) C₀ w.1
  R' := fun _ out _ w => S.ShortOpens (S.budget b₀ T) out.1 w.1 ∧
    ∀ j : Fin T, S.ShortOpens S.B (out.2 j) (w.2 j)
  k := T
  k_pos := hT
  PMsg := C
  Chal := Kh
  pmsgNonempty := ⟨0⟩
  chalFintype := inferInstance
  chalNonempty := inferInstance
  δstar := 1
  δstar_pos := one_pos
  δstar_le_one := le_refl 1
  verify := fun _ C₀ _ πs ρs =>
    some ((chalFoldList chalVal C₀ (List.ofFn fun i => (πs i, ρs i)), πs),
      fun _ => ())

variable (S : FoldCommitScheme R W C) (T : ℕ) (hT : 0 < T) (Kh : Type)
  [Fintype Kh] [Nonempty Kh] (chalVal : Kh → R) (b₀ : ℝ)

/-- The carried openings agree with the completed rounds: for each completed
round `j`, `Ys j` is a `B`-short opening of the `j`-th absorbed commitment. -/
def OpensAbsorbed (rs : List (C × Kh)) (Ys : Fin T → W) : Prop :=
  ∀ (j : Fin T) (hj : (j : ℕ) < rs.length),
    S.ShortOpens S.B (rs[(j : ℕ)]'hj).1 (Ys j)

/-- **The knowledge state through a carried fold**: the running opening opens
the running fold at the DESCENDING budget `budget b₀ (2T − c)` (genesis
`2T`, full fold `T`), and the carried openings agree with the completed
rounds. -/
def FoldCarriedStateProp (C₀ : C) (rs : List (C × Kh))
    (w : W × (Fin T → W)) : Prop :=
  S.commit w.1 = chalFoldList chalVal C₀ rs ∧
    S.nrm w.1 ≤ S.budget b₀ (2 * T - rs.length) ∧
    OpensAbsorbed S T Kh rs w.2

open Classical in
/-- **Def 4.1 at the carried fold — all three clauses PROVED.** Empty: the
running fold is the genesis, the descending budget is `budget b₀ (2T)`, and
no round is completed — exactly the relaxed source relation. Prover moves:
the state never reads the pending message. Full: the running fold is the
verifier's output, the budget is `budget b₀ T`, and every absorbed
commitment is carried-opened — exactly `R'`. -/
noncomputable def foldCarriedKState :
    KStateFn (foldReductionCarried S T hT Kh chalVal b₀) where
  state := fun _δ st tr w =>
    decide (FoldCarriedStateProp S T Kh chalVal b₀ st.x tr.rounds w)
  empty_iff := by
    intro δ hδ st w
    rw [relaxedMem_of_subsingleton _ (le_of_lt hδ.1)]
    show decide (FoldCarriedStateProp S T Kh chalVal b₀ st.x [] w) = true ↔ _
    rw [decide_eq_true_eq]
    unfold FoldCarriedStateProp OpensAbsorbed
    simp [FoldCommitScheme.ShortOpens]
  prover_monotone := by
    intro δ hδ st rs w hlen h π
    exact h
  full_iff := by
    intro δ hδ st πs ρs w
    show decide (FoldCarriedStateProp S T Kh chalVal b₀ st.x
      (List.ofFn fun i => (πs i, ρs i)) w) = true ↔ _
    rw [decide_eq_true_eq]
    unfold FoldCarriedStateProp OpensAbsorbed
    constructor
    · rintro ⟨hc, hn, ho⟩
      refine ⟨(chalFoldList chalVal st.x (List.ofFn fun i => (πs i, ρs i)), πs),
        fun _ => (), rfl, ?_⟩
      rw [relaxedMem_of_subsingleton _ (le_of_lt hδ.1)]
      refine ⟨⟨hc, ?_⟩, ?_⟩
      · rw [List.length_ofFn, show 2 * T - T = T by omega] at hn
        exact hn
      · intro j
        have hj : (j : ℕ) < (List.ofFn fun i => (πs i, ρs i)).length := by
          rw [List.length_ofFn]; exact j.isLt
        have := ho j hj
        simpa only [List.getElem_ofFn, Fin.eta] using this
    · rintro ⟨x', y', heq, hrel⟩
      rw [relaxedMem_of_subsingleton _ (le_of_lt hδ.1)] at hrel
      obtain ⟨hx, -⟩ := Prod.mk.inj (Option.some.inj heq)
      subst hx
      obtain ⟨⟨hcom, hnrm⟩, ho⟩ := hrel
      refine ⟨hcom, ?_, ?_⟩
      · rw [List.length_ofFn, show 2 * T - T = T by omega]
        exact hnrm
      · intro j hj
        simpa only [List.getElem_ofFn, Fin.eta] using ho j

open Classical in
theorem foldCarriedKState_true (δ : ℝ)
    (st : Stmt (foldReductionCarried S T hT Kh chalVal b₀))
    (tr : Transcript C Kh) (w : W × (Fin T → W)) :
    (foldCarriedKState S T hT Kh chalVal b₀).state δ st tr w = true ↔
      FoldCarriedStateProp S T Kh chalVal b₀ st.x tr.rounds w :=
  decide_eq_true_iff

open Classical in
theorem foldCarriedKState_false (δ : ℝ)
    (st : Stmt (foldReductionCarried S T hT Kh chalVal b₀))
    (tr : Transcript C Kh) (w : W × (Fin T → W)) :
    (foldCarriedKState S T hT Kh chalVal b₀).state δ st tr w = false ↔
      ¬ FoldCarriedStateProp S T Kh chalVal b₀ st.x tr.rounds w :=
  decide_eq_false_iff_not

/-- **The un-fold extractor** — CONSTRUCTED, linear, δ-oblivious. On the
extended transcript `rs ++ [(π, ρ)]` (last completed round `i = |rs|`) it
returns `(Y − chalVal ρ • Ys i, Ys)`: the additive commitment un-folds
exactly, and the norm grows by at most `ρ·B` (the carried opening `Ys i`
is `B`-short and `chalVal ρ` has operator norm `≤ ρ`). On a transcript with
no completed round, or an out-of-range round, it is the identity. -/
def foldExtract (_st : Stmt (foldReductionCarried S T hT Kh chalVal b₀))
    (tr : Transcript C Kh) (w : W × (Fin T → W)) : W × (Fin T → W) :=
  match tr.rounds.getLast? with
  | none => w
  | some (_, ρ) =>
    if h : tr.rounds.length - 1 < T then
      (w.1 - chalVal ρ • w.2 ⟨tr.rounds.length - 1, h⟩, w.2)
    else w

/-- The extractor on an extended transcript, in closed form. -/
theorem foldExtract_concat
    (st : Stmt (foldReductionCarried S T hT Kh chalVal b₀)) (i : Fin T)
    (rs : List (C × Kh)) (hlen : rs.length = (i : ℕ)) (π : C) (ρ : Kh)
    (w : W × (Fin T → W)) :
    foldExtract S T hT Kh chalVal b₀ st ⟨rs ++ [(π, ρ)], none⟩ w
      = (w.1 - chalVal ρ • w.2 i, w.2) := by
  unfold foldExtract
  simp only [List.getLast?_concat, List.length_append, List.length_singleton,
    Nat.add_sub_cancel, hlen, i.isLt, dite_true, Fin.eta]

/-- **The un-fold preserves the knowledge state** — the whole round bound, as
a deterministic implication: a witness in the extended state un-folds to a
witness in the prefix state. Commitment: linear. Norm: `nrm_sub` + `nrm_smul`
against the descending budget's `budget_succ`. Carried openings: the prefix
of an agreeing family agrees. The only premise is that the challenge decode
lands in the scheme's challenge set (`hchal`), the same premise
`nrm_chalFoldList_le` carries. -/
theorem foldExtract_state (hchal : ∀ c, chalVal c ∈ S.chalSet)
    (st : Stmt (foldReductionCarried S T hT Kh chalVal b₀)) (i : Fin T)
    (rs : List (C × Kh)) (hlen : rs.length = (i : ℕ)) (π : C) (ρ : Kh)
    (w : W × (Fin T → W))
    (hw : FoldCarriedStateProp S T Kh chalVal b₀ st.x (rs ++ [(π, ρ)]) w) :
    FoldCarriedStateProp S T Kh chalVal b₀ st.x rs
      (foldExtract S T hT Kh chalVal b₀ st ⟨rs ++ [(π, ρ)], none⟩ w) := by
  obtain ⟨hc, hn, ho⟩ := hw
  rw [foldExtract_concat S T hT Kh chalVal b₀ st i rs hlen π ρ w]
  have hiT := i.isLt
  have hπ : S.ShortOpens S.B π (w.2 i) := by
    have hj : (i : ℕ) < (rs ++ [(π, ρ)]).length := by
      rw [List.length_append, List.length_singleton]; omega
    have := ho i hj
    rwa [List.getElem_concat_length hlen.symm] at this
  obtain ⟨hπc, hπn⟩ := hπ
  rw [chalFoldList_append_singleton] at hc
  simp only [foldStep] at hc
  refine ⟨?_, ?_, ?_⟩
  · show S.commit (w.1 - chalVal ρ • w.2 i) = _
    rw [map_sub, map_smul, hc, hπc, add_sub_cancel_right]
  · show S.nrm (w.1 - chalVal ρ • w.2 i) ≤ _
    have h1 : S.nrm (chalVal ρ • w.2 i) ≤ S.ρ * S.B :=
      le_trans (S.nrm_smul _ (hchal ρ) _)
        (mul_le_mul_of_nonneg_left hπn S.ρ_nonneg)
    have h2 : S.budget b₀ (2 * T - rs.length)
        = S.budget b₀ (2 * T - (rs ++ [(π, ρ)]).length) + S.ρ * S.B := by
      rw [List.length_append, List.length_singleton]
      have : 2 * T - rs.length = (2 * T - (rs.length + 1)) + 1 := by omega
      rw [this, S.budget_succ]
    rw [h2]
    exact le_trans (S.nrm_sub _ _) (add_le_add hn h1)
  · intro j hj
    have hj' : (j : ℕ) < (rs ++ [(π, ρ)]).length := by
      rw [List.length_append, List.length_singleton]; omega
    have := ho j hj'
    rwa [List.getElem_append_left hj] at this

/-- **[ACC-rbr-fold-resid](a) at the carried witness type — STATEMENT-FIRST**:
the Def-4.2 round event of `foldReductionCarried` against
`foldCarriedKState`, for a round extractor and a per-fold error.

ATLAS keystone fields:
* satisfiable: `foldCarriedRoundBound_zero` — the CONSTRUCTED `foldExtract`
  at `εfold ≡ 0`, every instance whose challenge decode is in-set.
* teeth: `ToyFold.toy_carriedRoundBound_zero_id_false` — the identity
  extractor at the toy instance is REFUTED at `εfold ≡ 0` (the honest
  one-fold carried witness inhabits the round event at challenge `+1`).
* premise-inhabitation: `foldCarriedKState` is a genuine Def-4.1 instance
  (three clauses proved), and `ToyFold.toy_chalVal3_mem` discharges `hchal`
  on concrete data. -/
def FoldCarriedRoundBound
    (extractFn : Stmt (foldReductionCarried S T hT Kh chalVal b₀) →
      Transcript C Kh → W × (Fin T → W) → W × (Fin T → W))
    (εfold : ℝ → ℝ) : Prop :=
  ∀ δ ∈ Set.Ioo (0 : ℝ) 1,
    ∀ (st : Stmt (foldReductionCarried S T hT Kh chalVal b₀)) (i : Fin T)
      (rs : List (C × Kh)), rs.length = (i : ℕ) → ∀ π : C,
      uniformProb Kh (fun ρ => ∃ w : W × (Fin T → W),
        (foldCarriedKState S T hT Kh chalVal b₀).state δ st ⟨rs, some π⟩
            (extractFn st ⟨rs ++ [(π, ρ)], none⟩ w) = false ∧
        (foldCarriedKState S T hT Kh chalVal b₀).state δ st
            ⟨rs ++ [(π, ρ)], none⟩ w = true) ≤ εfold δ

/-- **The round bound at the carried fold is ZERO** — with the constructed
extractor, the round event is empty: whatever wins the extended state,
its un-fold wins the prefix state (`foldExtract_state`). No MSIS
hypothesis is consumed; the price is the relaxed source relation. -/
theorem foldCarriedRoundBound_zero (hchal : ∀ c, chalVal c ∈ S.chalSet) :
    FoldCarriedRoundBound S T hT Kh chalVal b₀
      (foldExtract S T hT Kh chalVal b₀) (fun _ => 0) := by
  intro δ hδ st i rs hlen π
  refine le_of_eq (uniformProb_false ?_)
  rintro ρ ⟨w, hfail, hok⟩
  rw [foldCarriedKState_true] at hok
  rw [foldCarriedKState_false] at hfail
  exact hfail (foldExtract_state S T hT Kh chalVal b₀ hchal st i rs hlen π ρ
    w hok)

/-- The carried fold carries a full Def-4.2 instance: `foldCarriedKState`,
the CONSTRUCTED `foldExtract`, error `0`. Nothing is a parameter. -/
noncomputable def foldCarriedRbr (hchal : ∀ c, chalVal c ∈ S.chalSet) :
    RbrKnowledgeSoundness (foldReductionCarried S T hT Kh chalVal b₀) where
  kstate := foldCarriedKState S T hT Kh chalVal b₀
  extract := foldExtract S T hT Kh chalVal b₀
  err := fun _i _st _δ => 0
  extractTime := fun _ => 0
  extract_sound := fun δ hδ st i rs hlen π =>
    foldCarriedRoundBound_zero S T hT Kh chalVal b₀ hchal δ hδ st i rs hlen π

/-- **Depth composition for the carried fold**: straightline state-restoration
knowledge-sound at error `0` — THE depth composition for the fold shape, with
the extractor constructed and the round bound discharged, riding the landed
[OB-2′] (`OB2_depth_composition_nonneg_proved`, `Selvage/Depth.lean`). -/
theorem foldCarried_depth_composition (hchal : ∀ c, chalVal c ∈ S.chalSet)
    (Z : Set (Stmt (foldReductionCarried S T hT Kh chalVal b₀))) :
    StraightlineSrKnowledgeSoundness (foldReductionCarried S T hT Kh chalVal b₀)
      Z (fun _s _t _δ => 0) := by
  have h := OB2_depth_composition_nonneg_proved
    (foldReductionCarried S T hT Kh chalVal b₀)
    (foldCarriedRbr S T hT Kh chalVal b₀ hchal) Z (fun _ => 0)
    (fun _ _ => le_refl 0) (fun _i _st _hst _δ _hδ => le_refl 0)
  simpa only [mul_zero] using h

/-- **Fiat–Shamir of the carried fold, straightline, at error `0`** — THE
Fiat–Shamir composition for the fold shape, with NO extractor parameter and
NO round-bound hypothesis: nothing in the additive lane is caller-conditional
on an unspecified extractor any more. Riding `fsKeystone_proved` (PROVED
unconditionally). -/
theorem foldCarried_fs_sound (hchal : ∀ c, chalVal c ∈ S.chalSet)
    (Z : Set (Stmt (foldReductionCarried S T hT Kh chalVal b₀))) :
    FsStraightlineKnowledgeSoundness (foldReductionCarried S T hT Kh chalVal b₀)
      Z (fun _s _t _δ => 0) := by
  have h := fsKeystone_proved.sound
    (foldReductionCarried S T hT Kh chalVal b₀)
    (foldCarriedRbr S T hT Kh chalVal b₀ hchal) Z (fun _ => 0)
    (fun _ _ => le_refl 0) (fun _i _st _hst _δ _hδ => le_refl 0)
  simpa only [mul_zero] using h

end FoldCarried

/-! ## Keystones at the toy instance -/

namespace ToyFold

/-- The `{−1, 0, 1}` decode lands in the toy's challenge set `|r| ≤ 1`:
premise-inhabitation for `hchal`. -/
theorem toy_chalVal3_mem : ∀ c : Fin 3, chalVal3 c ∈ toy.chalSet := by
  intro c
  show (chalVal3 c).natAbs ≤ 1
  fin_cases c <;> decide

/-- **The floor, DISCHARGED at the toy**: genesis `commit (2·e₀)` at `b₀ = 1`
(`‖2·e₀‖ = 2`: over budget `1`, inside `budget 1 1 = 2`), binding at `2` from
`toy_binding_T1` (which rides the PROVED `msisHardEx_toy`). Every extractor,
every error: `FoldRoundBound` forces `1 ≤ ε δ`. The MSIS hypothesis does not
rescue the compressing fold's round bound — it is what makes the prefix
state empty. -/
theorem toy_roundBound_floor
    (extractFn : Stmt (foldReduction toy 1 one_pos (Fin 3) chalVal3 1) →
      Transcript (Fin 1 → ZMod 97) (Fin 3) → (Fin 2 → ℤ) → (Fin 2 → ℤ))
    (εfold : ℝ → ℝ)
    (h : FoldRoundBound toy 1 one_pos (Fin 3) chalVal3 1 extractFn εfold) :
    ∀ δ ∈ Set.Ioo (0 : ℝ) 1, 1 ≤ εfold δ := by
  have hnrm : toy.nrm (unitSpike 0 2) = 2 := by
    show supNorm (unitSpike (0 : Fin 2) 2) = 2
    rw [supNorm, show supNat (unitSpike (0 : Fin 2) 2) = 2 from by decide]
    norm_num
  refine foldRoundBound_floor toy 1 one_pos (Fin 3) chalVal3 1
    (unitSpike 0 2) ?_ ?_ ?_ extractFn εfold h
  · rw [hnrm]; norm_num
  · rw [hnrm, toy_budget]; norm_num
  · rw [hnrm]
    have := toy_binding_T1
    rwa [toy_budget, show (1 : ℝ) + ((1 : ℕ) : ℝ) = 2 by norm_num] at this

/-- **`FoldCarriedRoundBound` is REFUTABLE** (with `foldCarriedRoundBound_zero`
as its satisfiability, the Prove-The-Floor-FALSE pair): at the toy instance,
`εfold ≡ 0` with the IDENTITY extractor is false — the honest one-fold
carried witness `(e₀, e₀)` inhabits the round event at challenge `+1`: it
opens the extended fold `0 + 1·commit e₀` inside budget with its absorbed
opening carried, while the un-un-folded prefix state demands
`commit e₀ = 0`, refuted. Un-folding is REAL work. -/
theorem toy_carriedRoundBound_zero_id_false :
    ¬ FoldCarriedRoundBound toy 1 one_pos (Fin 3) chalVal3 0 (fun _ _ w => w)
      (fun _ => 0) := by
  intro h
  classical
  have hh := h (1 / 2) (by rw [Set.mem_Ioo]; constructor <;> norm_num)
    ⟨(), 0, fun _ => ()⟩ 0 [] rfl (intCommit 97 A97 e01)
  refine absurd hh (not_le.mpr ?_)
  refine uniformProb_pos_of_witness (2 : Fin 3) ?_
  refine ⟨(e01, fun _ => e01), ?_, ?_⟩
  · rw [foldCarriedKState_false]
    rintro ⟨hcom, -, -⟩
    rw [chalFoldList_nil] at hcom
    have h0 : intCommit 97 A97 e01 0 = 0 := congrFun hcom 0
    rw [toy_commit_e01] at h0
    exact absurd h0 (by decide)
  · rw [foldCarriedKState_true]
    refine ⟨?_, ?_, ?_⟩
    · show intCommit 97 A97 e01 = chalFoldList chalVal3 (0 : Fin 1 → ZMod 97)
        ([] ++ [(intCommit 97 A97 e01, (2 : Fin 3))])
      decide
    · show supNorm e01 ≤ toy.budget 0
        (2 * 1 - ([] ++ [(intCommit 97 A97 e01, (2 : Fin 3))] :
          List ((Fin 1 → ZMod 97) × Fin 3)).length)
      rw [show ([] ++ [(intCommit 97 A97 e01, (2 : Fin 3))] :
          List ((Fin 1 → ZMod 97) × Fin 3)).length = 1 from rfl,
        show 2 * 1 - 1 = 1 from rfl, toy_budget, supNorm,
        show supNat e01 = 1 from by decide]
      norm_num
    · intro j hj
      refine ⟨?_, ?_⟩
      · show intCommit 97 A97 e01
          = (([] ++ [(intCommit 97 A97 e01, (2 : Fin 3))] :
              List ((Fin 1 → ZMod 97) × Fin 3))[(j : ℕ)]'hj).1
        simp
      · show supNorm e01 ≤ toy.B
        rw [supNorm, show supNat e01 = 1 from by decide]
        show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)
        exact le_refl _

end ToyFold

/-! ## The floor and the halved capacity at the production point -/

namespace DualModeParams

/-- **The floor at the production scheme**: under the same `[FOLD-msis]`
hypothesis `production_fold_binding` consumes (at the one-fold budget), the
genesis `commit ((B+1)·e₀)` — one over the honest `b₀ = B`, inside
`budget B 1 = 2B` — forces every extractor's round bound to `1`. Not a toy
artefact: the attack needs only a witness one step over budget and binding
there. -/
theorem production_roundBound_floor {κ N : ℕ} (hN : 0 < N)
    (A : Fin κ → Fin N → ℤ) (T : ℕ) (hT : 0 < T) (Kh : Type) [Fintype Kh]
    [Nonempty Kh] (chalVal : Kh → ℤ)
    (hmsis : (intFoldScheme q A 1 B).MsisHardEx
      (2 * (intFoldScheme q A 1 B).budget (B : ℝ) 1))
    (extractFn : Stmt (foldReduction (intFoldScheme q A 1 B) T hT Kh chalVal
        (B : ℝ)) → Transcript (Fin κ → ZMod q) Kh → (Fin N → ℤ) → (Fin N → ℤ))
    (εfold : ℝ → ℝ)
    (h : FoldRoundBound (intFoldScheme q A 1 B) T hT Kh chalVal (B : ℝ)
      extractFn εfold) :
    ∀ δ ∈ Set.Ioo (0 : ℝ) 1, 1 ≤ εfold δ := by
  have hnrm : (intFoldScheme q A 1 B).nrm (unitSpike ⟨0, hN⟩ ((B : ℤ) + 1))
      = ((B : ℝ) + 1) := by
    show supNorm (unitSpike (⟨0, hN⟩ : Fin N) ((B : ℤ) + 1)) = _
    rw [supNorm]
    have hle := unitSpike_supNat_le (⟨0, hN⟩ : Fin N) ((B : ℤ) + 1)
    have hge := coord_le_supNat (unitSpike (⟨0, hN⟩ : Fin N) ((B : ℤ) + 1))
      ⟨0, hN⟩
    have hval : (unitSpike (⟨0, hN⟩ : Fin N) ((B : ℤ) + 1)) ⟨0, hN⟩
        = (B : ℤ) + 1 := by
      simp [unitSpike]
    rw [hval] at hge
    have habs : ((B : ℤ) + 1).natAbs = B + 1 := by omega
    rw [habs] at hle hge
    have heq : supNat (unitSpike (⟨0, hN⟩ : Fin N) ((B : ℤ) + 1)) = B + 1 :=
      le_antisymm hle hge
    rw [heq]
    push_cast
    ring
  have hbud : (intFoldScheme q A 1 B).budget (B : ℝ) 1 = (B : ℝ) + (B : ℝ) := by
    rw [production_budget]; push_cast; ring
  refine foldRoundBound_floor (intFoldScheme q A 1 B) T hT Kh chalVal (B : ℝ)
    (unitSpike ⟨0, hN⟩ ((B : ℤ) + 1)) ?_ ?_ ?_ extractFn εfold h
  · rw [hnrm]; linarith
  · rw [hnrm, hbud]
    have : (1 : ℝ) ≤ (B : ℝ) := by
      have : 1 ≤ B := by norm_num [B]
      exact_mod_cast this
    linarith
  · rw [hnrm]
    have hbind := production_fold_binding A 1 hmsis
    refine (intFoldScheme q A 1 B).bindingAt_anti ?_ hbind
    rw [hbud]
    have : (1 : ℝ) ≤ (B : ℝ) := by
      have : 1 ≤ B := by norm_num [B]
      exact_mod_cast this
    linarith

/-- The carried-fold slack at the production point: the extracted genesis
opening is `budget B (2T) = B(1 + 2T)`-short, and binding there needs the
MSIS hypothesis at `2B(1 + 2T)` — which keeps a norm gap below `q` exactly
through `T ≤ 2^46 − 1`: the fold capacity HALVES against `capacity_safe`. -/
theorem carried_capacity_safe : ∀ T : ℕ, T ≤ 2 ^ 46 - 1 →
    2 * (B * (1 + 2 * T)) < q := by
  intro T hT
  have hB : B = 65536 := by norm_num [B]
  have h46 : (2 : ℕ) ^ 46 - 1 = 70368744177663 := by norm_num
  rw [hB, q_eq]
  rw [h46] at hT
  omega

/-- Binding of the extracted (relaxed) genesis opening at the production
point, from `[FOLD-msis]` at the DOUBLED budget — `fold_binding` at `2T`. -/
theorem production_carried_binding {κ N : ℕ} (A : Fin κ → Fin N → ℤ) (T : ℕ)
    (h : (intFoldScheme q A 1 B).MsisHardEx
      (2 * (intFoldScheme q A 1 B).budget (B : ℝ) (2 * T))) :
    (intFoldScheme q A 1 B).BindingAt
      ((intFoldScheme q A 1 B).budget (B : ℝ) (2 * T)) :=
  (intFoldScheme q A 1 B).fold_binding h

/-- **The halved wall, negative half**: at `T ≥ 2^46` carried folds the
extracted genesis opening's budget `B(1 + 2T)` reaches the wraparound and
binding there is LOST — unconditionally, constructively, for every key
(`production_break` at `2T ≥ 2^47 − 1`). -/
theorem carried_break {κ N : ℕ} (hN : 0 < N) (A : Fin κ → Fin N → ℤ)
    {T : ℕ} (hT : 2 ^ 46 ≤ T) :
    ¬ (intFoldScheme q A 1 B).BindingAt
        ((intFoldScheme q A 1 B).budget (B : ℝ) (2 * T)) :=
  production_break hN A (by
    have h46 : (2 : ℕ) ^ 46 = 70368744177664 := by norm_num
    have h47 : (2 : ℕ) ^ 47 - 1 = 140737488355327 := by norm_num
    rw [h47]; rw [h46] at hT; omega)

end DualModeParams

/-! ## Axiom audit -/

/-- info: 'Minidregg.Selvage.foldRoundBound_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms foldRoundBound_floor
/-- info: 'Minidregg.Selvage.ToyFold.toy_roundBound_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ToyFold.toy_roundBound_floor
/-- info: 'Minidregg.Selvage.DualModeParams.production_roundBound_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DualModeParams.production_roundBound_floor
/-- info: 'Minidregg.Selvage.foldExtract_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms foldExtract_state
/-- info: 'Minidregg.Selvage.foldCarriedRoundBound_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms foldCarriedRoundBound_zero
/-- info: 'Minidregg.Selvage.foldCarried_depth_composition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms foldCarried_depth_composition
/-- info: 'Minidregg.Selvage.foldCarried_fs_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms foldCarried_fs_sound
/-- info: 'Minidregg.Selvage.ToyFold.toy_carriedRoundBound_zero_id_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ToyFold.toy_carriedRoundBound_zero_id_false
/-- info: 'Minidregg.Selvage.DualModeParams.carried_break' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DualModeParams.carried_break

end Minidregg.Selvage
