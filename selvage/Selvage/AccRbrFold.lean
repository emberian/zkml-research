/-
# Selvage.AccRbrFold — [ACC-rbr-fold]: accumulation at an ADDITIVE commitment
alphabet — the Nova-family fold shape, with the NORM BUDGET as a field.

`Selvage/AccRbrBcs.lean` closed the accumulator chain at the Merkle/root alphabet
and `Selvage/AccRbrBcsShifted.lean` built the lag-respecting schedule its
fold-root deployment needs — `k + 1` rounds, an inert final challenge, and the
open residual `[ACC-rbr-bcs-shifted-resid]`(a): the fold root `h_{i+1}` is
committable only AFTER `ρ_i`, and no round bound prices that attribution
(`unshifted_misaligns_F5` proves the unshifted carrier IMPOSSIBLE, not merely
unproved). Nova-family folding lives at a different alphabet: the commitment
space is an ADDITIVE GROUP, folding is `C ← C₁ + ρ • C₂`, and the fold verifier
checks a LINEAR relation at the commitment alphabet. That alphabet is untypeable
at Merkle roots — roots do not add — and this file states it.

## What the additive alphabet dissolves, and what it charges

* **DISSOLVED: the lagged-root schedule.** At a homomorphic commitment the fold
  root is VERIFIER-COMPUTABLE: `commit_mFold` (the fold commutes with `commit`)
  and `mFold_sched_local` (stage `c` reads only challenges `< c`) make every
  partial-fold commitment a DERIVED object — a function of the genesis
  commitment, the per-round commitments, and the challenges — where the shifted
  schedule had to spend a round committing it. `foldReduction` has `k = T`
  rounds, no inert challenge, and the ρ-dependent family that no single Merkle
  message could carry is not a message at all.
* **CHARGED: the norm budget.** `C₁ + ρ • C₂` grows the witness norm per fold —
  this is where naive Nova-over-lattices dies (Cyclo, ePrint 2026/359: additive
  growth within a BOUNDED number of folds). The budget is carried as data
  (`FoldCommitScheme.budget`: `b₀ + T·(ρ·B)` — additive, because the linear
  accumulator CHAIN is the flat fold; a balanced fold TREE would be geometric),
  the growth law is a theorem (`nrm_chalFoldList_le`/`nrm_mFold_le`), and
  EXCEEDING it provably loses binding, constructively
  (`binding_lost_at_wraparound`: past `⌈q/2⌉` the wraparound pair
  `⌈q/2⌉ • e₀ ≠ −⌊q/2⌋ • e₀` opens one commitment twice, for EVERY key).

## Honest scope

* The witness ring is ℤ: shortness lives in the ring of integers, `ZMod q`
  carries no norm. Module-SIS is CONTAINED in the plain-SIS shape stated here
  (a negacyclic `A` is a parameter choice, not new formal vocabulary).
* `MsisHardEx` is NONEXISTENCE of a short kernel vector — provable at toy
  parameters (`ToyFold.msisHardEx_toy`), expected FALSE at production sizes by
  pigeonhole, where the honest hypothesis is COMPUTATIONAL. This tree has no
  cost model; the computational reading is the named residual `[FOLD-msis]`,
  consumed never claimed (the `[COMMIT-CR]` pattern).
* The Def-4.1 knowledge state through a fold is PROVED (`foldKState`: the
  witness is a short opening of the RUNNING accumulator at the RUNNING budget).
  The Def-4.2 round bound — producing a shorter-prefix opening from a longer
  one, single-transcript, no rewinding — is the real content and is entered
  STATEMENT-FIRST (`FoldRoundBound`), with `foldRbrOfRoundBound` showing it is
  the ONLY missing piece, `foldRoundBound_one` its satisfiability, and
  `foldRoundBound_zero_id_false` its teeth. Lattice folding genuinely extracts
  from 2–3 transcripts with RELAXED openings (slack `ρ − ρ'`); pricing the
  single-transcript event is `[ACC-rbr-fold-resid]`(a) — the exact additive-
  alphabet analog of `[ACC-rbr-bcs-shifted-resid]`(a).
* **The Z = ∅ corner RECURS: additivity does not dissolve it.** The `Depth.lean`
  refutation lives in the ERROR algebra, not the message algebra —
  `foldOB2Unguarded_false` re-runs it at a genuine fold instance, and the
  guarded composition holds for every fold instance by direct application of
  the landed [OB-2′] (`fold_depth_composition` / `fold_fs_sound`, riding
  `OB2_depth_composition_nonneg_proved` / `fsKeystone_proved`). Error
  accumulation: `(t + T)·(εr + εM)` splits into `(t+T)·εr + (t+T)·εM` —
  one ε_MSIS per absorbed commitment, the Nebula pricing
  (`fold_fs_price_msis`).

Measurement/design record: `zkml-research/notes/acc-rbr-fold.md`; the gap this
answers: `zkml-research/notes/nebula-vega-lessons.md` §2 (Q2); the intended
instance: `zkml-research/notes/ring-hash-dual-mode.md` (q = 2⁶⁴ − 257, B = 2¹⁶,
K = 4 — `DualModeParams` below carries the exact fold capacity: safe-through
`2^47 − 2`, broken-at `2^47 − 1`).
-/
import Selvage.ZkExtraction
import Selvage.Depth
import Selvage.FiatShamir
import Selvage.HeteroComposition

namespace Minidregg.Selvage

/-! ## The fold algebra, at any module — one object, two clothings -/

section ModuleFold

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M] {n : ℕ}

/-- **The fold step** at any additive carrier with a challenge action:
`C ← C₁ + ρ • C₂` — the Nova-family fold, the operation Merkle roots do not
have. -/
def foldStep (c₁ : M) (ρ : R) (c₂ : M) : M := c₁ + ρ • c₂

/-- **The module-level partial fold**: genesis plus the first `c` links'
challenge-weighted contributions — the SAME formula as the landed
`partialFold` (`Selvage/ZkExtraction.lean`), stated at an arbitrary module so
the commitment carrier can inhabit it. `mFold_eq_partialFold` identifies the
two at `M := ι → F`: one fold algebra, not a twin. -/
def mFold (γs : ℕ → R) (m₀ : M) (ms : Fin n → M) (c : ℕ) : M :=
  m₀ + ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < c),
    γs (j : ℕ) • ms j

@[simp] theorem mFold_zero (γs : ℕ → R) (m₀ : M) (ms : Fin n → M) :
    mFold γs m₀ ms 0 = m₀ := by
  unfold mFold
  have h : Finset.univ.filter (fun j : Fin n => (j : ℕ) < 0)
      = (∅ : Finset (Fin n)) := by
    ext j
    simp
  rw [h, Finset.sum_empty, add_zero]

/-- The recommitment step, at the module level: each partial fold is the
previous one `foldStep`ped by the new round's challenge. -/
theorem mFold_succ (γs : ℕ → R) (m₀ : M) (ms : Fin n → M) (k : Fin n) :
    mFold γs m₀ ms ((k : ℕ) + 1)
      = foldStep (mFold γs m₀ ms (k : ℕ)) (γs (k : ℕ)) (ms k) := by
  unfold mFold foldStep
  have h1 : Finset.univ.filter (fun j : Fin n => (j : ℕ) < (k : ℕ) + 1)
      = insert k (Finset.univ.filter (fun j : Fin n => (j : ℕ) < (k : ℕ))) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Fin.ext_iff]
    omega
  have h2 : k ∉ Finset.univ.filter (fun j : Fin n => (j : ℕ) < (k : ℕ)) := by
    simp
  rw [h1, Finset.sum_insert h2]
  abel

/-- The full-depth fold, flat form. -/
theorem mFold_last (γs : ℕ → R) (m₀ : M) (ms : Fin n → M) :
    mFold γs m₀ ms n = m₀ + ∑ k : Fin n, γs (k : ℕ) • ms k := by
  unfold mFold
  congr 1
  refine Finset.sum_congr ?_ fun j _ => rfl
  ext j
  simp

/-- One fold, closed form: `mFold … 1 = m₀ + γ₀ • w₀`. -/
theorem mFold_one (γs : ℕ → R) (m₀ : M) (ms : Fin (n + 1) → M) :
    mFold γs m₀ ms 1 = m₀ + γs 0 • ms 0 := by
  have := mFold_succ γs m₀ ms 0
  simpa [foldStep] using this

/-- **Schedule locality — the committability the shifted Merkle schedule had
to buy with an extra round, free at any module**: stage `c` reads the
challenge schedule only at rounds `< c`. -/
theorem mFold_sched_local {γs γs' : ℕ → R} (m₀ : M) (ms : Fin n → M) {c : ℕ}
    (h : ∀ j < c, γs j = γs' j) :
    mFold γs m₀ ms c = mFold γs' m₀ ms c := by
  unfold mFold
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [h (j : ℕ) (Finset.mem_filter.mp hj).2]

end ModuleFold

/-- **The identification**: at `M := ι → F` over a field the module-level fold
IS the landed `partialFold`, definitionally — one fold algebra wearing two
signatures, machine-checked, not a twin. -/
theorem mFold_eq_partialFold {F : Type} [Field F] {ι : Type*} {n : ℕ}
    (γs : ℕ → F) (f₀ : ι → F) (ms : Fin n → ι → F) (c : ℕ) :
    mFold γs f₀ ms c = partialFold γs f₀ ms c := rfl

/-! ## The fold commitment scheme — the norm budget as a field -/

/-- **[ACC-rbr-fold]'s carrier data**: a homomorphic commitment from a normed
witness module to an additive commitment space, with the challenge set, the
challenge operator bound `ρ`, and the per-instance bound `B` carried AS
STRUCTURE FIELDS — so the norm budget (`budget`) is part of the object, never
a comment. The intended instance is the dual-mode linear mode
(`intFoldScheme`: planes over ℤ, `commit = cast ∘ mulVec A` into `ZMod q`);
the trivial-group instance also inhabits it, which the Z = ∅ refutation
uses. -/
structure FoldCommitScheme (R : Type*) [Ring R] (W : Type*) (C : Type*)
    [AddCommGroup W] [AddCommGroup C] [Module R W] [Module R C] where
  /-- The homomorphic commitment — `R`-LINEAR, which is the entire difference
  from a Merkle root: `commit (Y₁ + ρ • Y₂) = commit Y₁ + ρ • commit Y₂`. -/
  commit : W →ₗ[R] C
  /-- The witness norm (∞-norm in the intended instance). `ZMod q` carries no
  norm; shortness is a fact about the WITNESS module. -/
  nrm : W → ℝ
  nrm_nonneg : ∀ Y, 0 ≤ nrm Y
  nrm_zero : nrm 0 = 0
  nrm_neg : ∀ Y, nrm (-Y) = nrm Y
  nrm_add : ∀ Y Z, nrm (Y + Z) ≤ nrm Y + nrm Z
  /-- The legal fold challenges (the LatticeFold-style SHORT set; strong-
  sampling challenges have unbounded operator norm and are exactly what the
  budget refuses — hazard §5c of the dual-mode note, made a type-level
  fact). -/
  chalSet : Set R
  /-- The challenge operator-norm bound. -/
  ρ : ℝ
  ρ_nonneg : 0 ≤ ρ
  /-- The per-absorbed-instance witness bound. -/
  B : ℝ
  B_nonneg : 0 ≤ B
  nrm_smul : ∀ γ ∈ chalSet, ∀ Y, nrm (γ • Y) ≤ ρ * nrm Y

namespace FoldCommitScheme

variable {R : Type*} [Ring R] {W : Type*} {C : Type*}
  [AddCommGroup W] [AddCommGroup C] [Module R W] [Module R C]
  (S : FoldCommitScheme R W C)

/-- **THE NORM BUDGET** — the field the brief demanded: after `T` folds from a
genesis of norm `≤ b₀`, the honest opening norm is `≤ b₀ + T·(ρ·B)`. ADDITIVE
in `T`, because the linear accumulator chain is the FLAT fold (Cyclo's
bounded-folds regime); a balanced fold tree would be geometric. -/
def budget (b₀ : ℝ) (T : ℕ) : ℝ := b₀ + T * (S.ρ * S.B)

@[simp] theorem budget_zero (b₀ : ℝ) : S.budget b₀ 0 = b₀ := by
  simp [budget]

theorem budget_succ (b₀ : ℝ) (T : ℕ) :
    S.budget b₀ (T + 1) = S.budget b₀ T + S.ρ * S.B := by
  unfold budget
  push_cast
  ring

theorem budget_mono (b₀ : ℝ) {T T' : ℕ} (h : T ≤ T') :
    S.budget b₀ T ≤ S.budget b₀ T' := by
  unfold budget
  have : (T : ℝ) ≤ (T' : ℝ) := by exact_mod_cast h
  nlinarith [mul_nonneg S.ρ_nonneg S.B_nonneg]

theorem nrm_sub (Y Z : W) : S.nrm (Y - Z) ≤ S.nrm Y + S.nrm Z := by
  rw [sub_eq_add_neg]
  calc S.nrm (Y + -Z) ≤ S.nrm Y + S.nrm (-Z) := S.nrm_add Y (-Z)
    _ = S.nrm Y + S.nrm Z := by rw [S.nrm_neg]

/-- **The norm-growth law at the fold algebra**: the `c`-th partial fold of
in-bound witnesses under in-set challenges stays within the budget. This is
the theorem the budget field prices. -/
theorem nrm_mFold_le {n : ℕ} {γs : ℕ → R} (hγ : ∀ j, γs j ∈ S.chalSet)
    {b₀ : ℝ} {Y₀ : W} {Ys : Fin n → W} (h₀ : S.nrm Y₀ ≤ b₀)
    (hY : ∀ k, S.nrm (Ys k) ≤ S.B) :
    ∀ c ≤ n, S.nrm (mFold γs Y₀ Ys c) ≤ S.budget b₀ c := by
  intro c
  induction c with
  | zero => intro _; simpa using h₀
  | succ c ih =>
    intro hc
    have hcn : c < n := Nat.lt_of_succ_le hc
    have hstep := mFold_succ γs Y₀ Ys ⟨c, hcn⟩
    simp only [foldStep] at hstep
    rw [hstep, S.budget_succ]
    have h1 : S.nrm (γs c • Ys ⟨c, hcn⟩) ≤ S.ρ * S.B :=
      le_trans (S.nrm_smul _ (hγ c) _)
        (mul_le_mul_of_nonneg_left (hY _) S.ρ_nonneg)
    exact le_trans (S.nrm_add _ _)
      (add_le_add (ih (le_of_lt hcn)) h1)

/-- **The fold commutes with the commitment** — the theorem that DISSOLVES the
lagged-root schedule: every partial-fold commitment is a DERIVED object,
computable by the verifier from the genesis commitment, the per-round
commitments, and the challenges. What `AccRbrBcsShifted` spent a round per
fold root committing (and `unshifted_misaligns_F5` proved no unshifted round
could carry), the additive alphabet computes. -/
theorem commit_mFold {n : ℕ} (γs : ℕ → R) (Y₀ : W) (Ys : Fin n → W) (c : ℕ) :
    S.commit (mFold γs Y₀ Ys c)
      = mFold γs (S.commit Y₀) (fun k => S.commit (Ys k)) c := by
  unfold mFold
  rw [map_add, map_sum]
  simp_rw [map_smul]

/-! ### Binding, the MSIS hypothesis, and the budget/binding boundary -/

/-- `Y` is a `β`-short opening of the commitment `Cm`. -/
def ShortOpens (β : ℝ) (Cm : C) (Y : W) : Prop :=
  S.commit Y = Cm ∧ S.nrm Y ≤ β

/-- **Binding at norm bound `β`**: no commitment has two distinct `β`-short
openings. This is the property the fold consumes at `β := budget b₀ T`. -/
def BindingAt (β : ℝ) : Prop :=
  ∀ Y Y' : W, S.commit Y = S.commit Y' →
    S.nrm Y ≤ β → S.nrm Y' ≤ β → Y = Y'

/-- **The MSIS hypothesis, exact-nonexistence form**: no nonzero kernel vector
of norm `≤ β`. ⚠ HONEST LABEL: at toy parameters this is PROVED
(`ToyFold.msisHardEx_toy`); at production sizes nonexistence is expected FALSE
by pigeonhole and the honest hypothesis is COMPUTATIONAL ("no efficient
adversary FINDS one") — which this tree cannot state without a cost model.
The computational reading is the named residual `[FOLD-msis]`, consumed never
claimed. -/
def MsisHardEx (β : ℝ) : Prop :=
  ∀ Y : W, S.commit Y = 0 → S.nrm Y ≤ β → Y = 0

/-- The standard reduction, one direction: no short kernel vector at `2β` ⇒
binding at `β` (two `β`-short openings differ by a `2β`-short kernel
vector). -/
theorem bindingAt_of_msisHardEx {β : ℝ} (h : S.MsisHardEx (2 * β)) :
    S.BindingAt β := by
  intro Y Y' hc hY hY'
  have hker : S.commit (Y - Y') = 0 := by
    rw [map_sub, hc, sub_self]
  have hnrm : S.nrm (Y - Y') ≤ 2 * β := by
    calc S.nrm (Y - Y') ≤ S.nrm Y + S.nrm Y' := S.nrm_sub Y Y'
      _ ≤ β + β := add_le_add hY hY'
      _ = 2 * β := by ring
  have := h (Y - Y') hker hnrm
  exact sub_eq_zero.mp this

/-- The other direction of the sandwich: binding at `β ≥ 0` refutes short
kernel vectors at `β` (a kernel vector and `0` open the same commitment). -/
theorem msisHardEx_of_bindingAt {β : ℝ} (hβ : 0 ≤ β) (h : S.BindingAt β) :
    S.MsisHardEx β := by
  intro Y hc hn
  exact h Y 0 (by rw [hc, map_zero]) hn (by rw [S.nrm_zero]; exact hβ)

/-- Binding is antitone in the bound: a failure at `β` is a failure at every
`β' ≥ β`. -/
theorem bindingAt_anti {β β' : ℝ} (h : β ≤ β') (hb : S.BindingAt β') :
    S.BindingAt β :=
  fun Y Y' hc hY hY' => hb Y Y' hc (le_trans hY h) (le_trans hY' h)

/-- **The bounded-folds theorem, abstract half**: through `T` folds, binding
at the budget follows from the MSIS hypothesis at twice the budget — and the
honest fold witness is IN budget (`nrm_mFold_le`), so the pair (growth law,
binding-at-budget) is exactly "the fold is sound while `2·f(T)` stays inside
the MSIS bound". The concrete boundary at the dual-mode parameters is
`DualModeParams.fold_capacity_*` below. -/
theorem fold_binding {b₀ : ℝ} {T : ℕ}
    (h : S.MsisHardEx (2 * S.budget b₀ T)) :
    S.BindingAt (S.budget b₀ T) :=
  S.bindingAt_of_msisHardEx h

end FoldCommitScheme

/-! ## The transcript-shaped fold, and its norm law -/

section ChalFold

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
  {Kh : Type*}

/-- The running fold over a transcript prefix: each completed round `(π, ρ)`
folds its message in under its OWN challenge — challenge follows message, no
lag (`§ dissolution` in the module header). `chalVal` decodes the sampled
challenge alphabet into the ring. -/
def chalFoldList (chalVal : Kh → R) (C₀ : M) (rs : List (M × Kh)) : M :=
  rs.foldl (fun acc e => acc + chalVal e.2 • e.1) C₀

@[simp] theorem chalFoldList_nil (chalVal : Kh → R) (C₀ : M) :
    chalFoldList chalVal C₀ ([] : List (M × Kh)) = C₀ := rfl

theorem chalFoldList_cons (chalVal : Kh → R) (C₀ : M) (e : M × Kh)
    (tl : List (M × Kh)) :
    chalFoldList chalVal C₀ (e :: tl)
      = chalFoldList chalVal (C₀ + chalVal e.2 • e.1) tl := rfl

theorem chalFoldList_append_singleton (chalVal : Kh → R) (C₀ : M)
    (rs : List (M × Kh)) (π : M) (ρ : Kh) :
    chalFoldList chalVal C₀ (rs ++ [(π, ρ)])
      = foldStep (chalFoldList chalVal C₀ rs) (chalVal ρ) π := by
  unfold chalFoldList foldStep
  rw [List.foldl_append]
  rfl

/-- The flat form of the running fold. -/
theorem chalFoldList_eq_flat (chalVal : Kh → R) (C₀ : M)
    (rs : List (M × Kh)) :
    chalFoldList chalVal C₀ rs
      = C₀ + (rs.map fun e => chalVal e.2 • e.1).sum := by
  induction rs generalizing C₀ with
  | nil => simp
  | cons e tl ih =>
    rw [chalFoldList_cons, ih]
    simp only [List.map_cons, List.sum_cons]
    abel

/-- The zero-padded ring schedule of a sampled challenge tuple. -/
def chalSched {T : ℕ} (chalVal : Kh → R) (ρs : Fin T → Kh) : ℕ → R :=
  fun j => if h : j < T then chalVal (ρs ⟨j, h⟩) else 0

/-- **The bridge to the fold algebra**: the transcript fold of a full round
tuple IS `mFold` at the padded schedule — the protocol layer and the algebra
layer are one object. -/
theorem chalFoldList_ofFn {T : ℕ} (chalVal : Kh → R) (C₀ : M)
    (πs : Fin T → M) (ρs : Fin T → Kh) :
    chalFoldList chalVal C₀ (List.ofFn fun i => (πs i, ρs i))
      = mFold (chalSched chalVal ρs) C₀ πs T := by
  rw [chalFoldList_eq_flat, mFold_last, List.map_ofFn, List.sum_ofFn]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Function.comp, chalSched, k.isLt]

end ChalFold

namespace FoldCommitScheme

variable {R : Type*} [Ring R] {W : Type*} {C : Type*}
  [AddCommGroup W] [AddCommGroup C] [Module R W] [Module R C]
  (S : FoldCommitScheme R W C) {Kh : Type*}

/-- The homomorphism at the transcript layer: committing the witness-side
running fold IS the commitment-side running fold of the per-round
commitments. The verifier-computability of every fold root, in the shape the
protocol consumes. -/
theorem commit_chalFoldList (chalVal : Kh → R) (Y₀ : W)
    (rs : List (W × Kh)) :
    S.commit (chalFoldList chalVal Y₀ rs)
      = chalFoldList chalVal (S.commit Y₀)
          (rs.map fun e => (S.commit e.1, e.2)) := by
  induction rs generalizing Y₀ with
  | nil => simp
  | cons e tl ih =>
    rw [chalFoldList_cons, ih, List.map_cons, chalFoldList_cons,
      map_add, map_smul]

/-- The norm law at the transcript layer: a prefix of in-bound messages under
in-set challenges keeps the running fold inside the running budget. -/
theorem nrm_chalFoldList_le (chalVal : Kh → R)
    (hchal : ∀ c, chalVal c ∈ S.chalSet) :
    ∀ (rs : List (W × Kh)) (b₀ : ℝ) (Y₀ : W),
      (∀ e ∈ rs, S.nrm e.1 ≤ S.B) → S.nrm Y₀ ≤ b₀ →
      S.nrm (chalFoldList chalVal Y₀ rs) ≤ S.budget b₀ rs.length := by
  intro rs
  induction rs with
  | nil => intro b₀ Y₀ _ h₀; simpa using h₀
  | cons e tl ih =>
    intro b₀ Y₀ hmsg h₀
    rw [chalFoldList_cons]
    have h1 : S.nrm (Y₀ + chalVal e.2 • e.1) ≤ b₀ + S.ρ * S.B := by
      refine le_trans (S.nrm_add _ _) (add_le_add h₀ ?_)
      exact le_trans (S.nrm_smul _ (hchal e.2) _)
        (mul_le_mul_of_nonneg_left (hmsg e (List.mem_cons_self ..)) S.ρ_nonneg)
    refine le_trans (ih (b₀ + S.ρ * S.B) _
      (fun e' he' => hmsg e' (List.mem_cons_of_mem _ he')) h1) (le_of_eq ?_)
    simp only [List.length_cons]
    unfold budget
    push_cast
    ring

end FoldCommitScheme

/-! ## `foldReduction` — the fold as a WARP `Reduction`, k = T rounds, no lag -/

section FoldReduction

variable {R : Type} [Ring R] {W C : Type} [AddCommGroup W] [AddCommGroup C]
  [Module R W] [Module R C]

/-- `RelaxedMem` collapses to plain membership when the oracle alphabet is a
subsingleton — the fold reduction's proximity component is trivial by design
(the fold verifier is exact linear algebra; there is no word to be near). -/
theorem relaxedMem_of_subsingleton {Idx X A Wt : Type} [Subsingleton A]
    {n : ℕ} (Rel : Idx → X → (Fin n → A) → Wt → Prop) {δ : ℝ} (hδ : 0 ≤ δ)
    (idx : Idx) (x : X) (y : Fin n → A) (w : Wt) :
    RelaxedMem Rel δ idx x y w ↔ Rel idx x y w := by
  constructor
  · rintro ⟨ystar, hR, -⟩
    have hy : ystar = y := funext fun i => Subsingleton.elim _ _
    rwa [hy] at hR
  · intro hR
    exact ⟨y, hR, by rw [fracHamming_self]; exact hδ⟩

/-- **The fold accumulator as a WARP reduction at the ADDITIVE commitment
alphabet**: `k = T` rounds — one per absorbed commitment, NO extra fold-root
round and NO inert final challenge (contrast `accReductionBcsShifted`'s
`ch.length + 1`). Prover message = the absorbed commitment `C_i`; the round's
challenge `ρ_i` FOLLOWS it and weights it; the verifier COMPUTES the folded
commitment itself (`chalFoldList` — the object the Merkle deployment had to
recommit and lag). Source relation: the witness is a `b₀`-short opening of
the genesis commitment. Target relation: the witness is a BUDGET-short
opening of the folded commitment — the witness type is ONE plane vector on
both sides, and backward extraction turns a fold opening into a genesis
opening, which is exactly where the per-fold ε price lives
(`FoldRoundBound`). -/
@[reducible] def foldReduction (S : FoldCommitScheme R W C) (T : ℕ)
    (hT : 0 < T) (Kh : Type) [Fintype Kh] [Nonempty Kh] (chalVal : Kh → R)
    (b₀ : ℝ) : Reduction where
  Idx := Unit
  X := C
  A := Unit
  X' := C
  A' := Unit
  W := W
  n := 1
  n' := 1
  n_pos := one_pos
  n'_pos := one_pos
  R := fun _ C₀ _ Y => S.ShortOpens b₀ C₀ Y
  R' := fun _ Cout _ Y => S.ShortOpens (S.budget b₀ T) Cout Y
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
    some (chalFoldList chalVal C₀ (List.ofFn fun i => (πs i, ρs i)),
      fun _ => ())

variable (S : FoldCommitScheme R W C) (T : ℕ) (hT : 0 < T) (Kh : Type)
  [Fintype Kh] [Nonempty Kh] (chalVal : Kh → R) (b₀ : ℝ)

/-- **The knowledge state through a fold**: the witness is a short opening OF
THE RUNNING ACCUMULATOR at the RUNNING budget. Uniform across rounds — no
full/partial case split, no lagged attribution. -/
def FoldStateProp (C₀ : C) (rs : List (C × Kh)) (Y : W) : Prop :=
  S.commit Y = chalFoldList chalVal C₀ rs ∧
    S.nrm Y ≤ S.budget b₀ rs.length

open Classical in
/-- **Def 4.1 at the fold alphabet — all three clauses PROVED.** Empty: the
running fold is the genesis and the running budget is `b₀` — exactly the
source relation. Prover moves: the state never reads the pending message.
Full: the running fold is the verifier's own output and the running budget is
`budget b₀ T` — exactly accept-with-`R'` (the verifier never rejects; the
fold is computed, not checked — the rejection lives in the DECIDER, i.e. the
final opening, exactly as at the IOR-resolution accumulator). -/
noncomputable def foldKState :
    KStateFn (foldReduction S T hT Kh chalVal b₀) where
  state := fun _δ st tr Y =>
    decide (FoldStateProp S Kh chalVal b₀ st.x tr.rounds Y)
  empty_iff := by
    intro δ hδ st Y
    rw [relaxedMem_of_subsingleton _ (le_of_lt hδ.1)]
    show decide (FoldStateProp S Kh chalVal b₀ st.x [] Y) = true ↔ _
    rw [decide_eq_true_eq]
    unfold FoldStateProp
    simp [FoldCommitScheme.ShortOpens]
  prover_monotone := by
    intro δ hδ st rs Y hlen h π
    exact h
  full_iff := by
    intro δ hδ st πs ρs Y
    show decide (FoldStateProp S Kh chalVal b₀ st.x
      (List.ofFn fun i => (πs i, ρs i)) Y) = true ↔ _
    rw [decide_eq_true_eq]
    unfold FoldStateProp
    constructor
    · rintro ⟨hc, hn⟩
      refine ⟨chalFoldList chalVal st.x (List.ofFn fun i => (πs i, ρs i)),
        fun _ => (), rfl, ?_⟩
      rw [relaxedMem_of_subsingleton _ (le_of_lt hδ.1)]
      refine ⟨hc, ?_⟩
      simpa [List.length_ofFn] using hn
    · rintro ⟨x', y', heq, hrel⟩
      rw [relaxedMem_of_subsingleton _ (le_of_lt hδ.1)] at hrel
      have heq' : (chalFoldList chalVal st.x
          (List.ofFn fun i => (πs i, ρs i)), fun _ => ()) = (x', y') :=
        Option.some.inj heq
      obtain ⟨hx, -⟩ := Prod.mk.injEq .. ▸ heq'
      obtain ⟨hcom, hnrm⟩ := hrel
      refine ⟨by rw [hcom, ← hx], ?_⟩
      simpa [List.length_ofFn] using hnrm

/-- **[ACC-rbr-fold-resid](a) — the per-fold round bound, STATEMENT-FIRST**
(house law): with a caller-supplied round extractor, the Def-4.2 round event
against the fold knowledge state is bounded by `εfold`. This is the ONLY
missing piece of a full `RbrKnowledgeSoundness` instance
(`foldRbrOfRoundBound` packages everything else), and it is where the
per-absorbed-commitment ε_MSIS term lives: producing a shorter-prefix opening
from a longer one, single-transcript, is exactly what lattice folding buys
with 2–3 transcripts and RELAXED openings (slack `ρ − ρ'`) — the additive-
alphabet analog of `[ACC-rbr-bcs-shifted-resid]`(a).

ATLAS keystone fields:
* satisfiable: `foldRoundBound_one` — every instance at `εfold ≡ 1`.
* teeth: `ToyFold.foldRoundBound_zero_id_false` — at the toy instance,
  `εfold ≡ 0` with the identity extractor is REFUTED (the honest one-fold
  transcript inhabits the round event at every nonzero challenge).
* premise-inhabitation: `foldKState` is a genuine Def-4.1 instance (three
  clauses proved), and `ToyFold` builds the reduction on concrete data. -/
def FoldRoundBound
    (extractFn : Stmt (foldReduction S T hT Kh chalVal b₀) →
      Transcript C Kh → W → W) (εfold : ℝ → ℝ) : Prop :=
  ∀ δ ∈ Set.Ioo (0 : ℝ) 1,
    ∀ (st : Stmt (foldReduction S T hT Kh chalVal b₀)) (i : Fin T)
      (rs : List (C × Kh)), rs.length = (i : ℕ) → ∀ π : C,
      uniformProb Kh (fun ρ => ∃ Y : W,
        (foldKState S T hT Kh chalVal b₀).state δ st ⟨rs, some π⟩
            (extractFn st ⟨rs ++ [(π, ρ)], none⟩ Y) = false ∧
        (foldKState S T hT Kh chalVal b₀).state δ st ⟨rs ++ [(π, ρ)], none⟩ Y
            = true) ≤ εfold δ

/-- The round bound is all that is missing: given it, the fold carries a full
Def-4.2 instance — `foldKState` plus the caller's extractor plus the uniform
error, no slack, nothing else owed. -/
noncomputable def foldRbrOfRoundBound
    (extractFn : Stmt (foldReduction S T hT Kh chalVal b₀) →
      Transcript C Kh → W → W) (εfold : ℝ → ℝ)
    (h : FoldRoundBound S T hT Kh chalVal b₀ extractFn εfold) :
    RbrKnowledgeSoundness (foldReduction S T hT Kh chalVal b₀) where
  kstate := foldKState S T hT Kh chalVal b₀
  extract := extractFn
  err := fun _i _st δ => εfold δ
  extractTime := fun _ => 0
  extract_sound := fun δ hδ st i rs hlen π => h δ hδ st i rs hlen π

/-- Satisfiable: every fold instance meets the round bound at `εfold ≡ 1` —
the Prop is not vacuously unmeetable. -/
theorem foldRoundBound_one
    (extractFn : Stmt (foldReduction S T hT Kh chalVal b₀) →
      Transcript C Kh → W → W) :
    FoldRoundBound S T hT Kh chalVal b₀ extractFn (fun _ => 1) :=
  fun _δ _hδ _st _i _rs _hlen _π => uniformProb_le_one _

/-! ### The depth composition for the fold shape — PROVED, riding [OB-2′] -/

/-- **Depth composition for the fold shape**: given the per-fold round bound
at a nonnegative `εfold`, the fold reduction is straightline state-
restoration knowledge-sound at `(t + T)·εfold` — a DIRECT application of the
landed repaired [OB-2′] (`OB2_depth_composition_nonneg_proved`,
Selvage/Depth.lean). Nothing fold-specific remains in the composition; the
fold-specific content all lives in `FoldRoundBound`. -/
theorem fold_depth_composition (εfold : ℝ → ℝ)
    (hnn : ∀ δ ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ εfold δ)
    (extractFn : Stmt (foldReduction S T hT Kh chalVal b₀) →
      Transcript C Kh → W → W)
    (h : FoldRoundBound S T hT Kh chalVal b₀ extractFn εfold)
    (Z : Set (Stmt (foldReduction S T hT Kh chalVal b₀))) :
    StraightlineSrKnowledgeSoundness (foldReduction S T hT Kh chalVal b₀) Z
      (fun _s t δ => ((t : ℝ) + (T : ℝ)) * εfold δ) :=
  OB2_depth_composition_nonneg_proved (foldReduction S T hT Kh chalVal b₀)
    (foldRbrOfRoundBound S T hT Kh chalVal b₀ extractFn εfold h) Z εfold hnn
    (fun _i _st _hst _δ _hδ => le_refl _)

/-- Fiat–Shamir of the fold, straightline, at the same `(t + T)·εfold` —
riding `fsKeystone_proved` (PROVED unconditionally). -/
theorem fold_fs_sound (εfold : ℝ → ℝ)
    (hnn : ∀ δ ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ εfold δ)
    (extractFn : Stmt (foldReduction S T hT Kh chalVal b₀) →
      Transcript C Kh → W → W)
    (h : FoldRoundBound S T hT Kh chalVal b₀ extractFn εfold)
    (Z : Set (Stmt (foldReduction S T hT Kh chalVal b₀))) :
    FsStraightlineKnowledgeSoundness (foldReduction S T hT Kh chalVal b₀) Z
      (fun _s t δ => ((t : ℝ) + (T : ℝ)) * εfold δ) :=
  fsKeystone_proved.sound (foldReduction S T hT Kh chalVal b₀)
    (foldRbrOfRoundBound S T hT Kh chalVal b₀ extractFn εfold h) Z εfold hnn
    (fun _i _st _hst _δ _hδ => le_refl _)

/-- **The Nebula pricing, named**: with a per-fold error split as a
round term plus a per-absorbed-commitment ε_MSIS term, the FS bound splits
into `(t+T)·εr + (t+T)·ε_MSIS` — one ε_MSIS per absorbed commitment times
the query budget, the `Q·ε_MSIS` accounting of the Nebula read
(`nebula-vega-lessons.md` §1), carried not hand-waved. -/
theorem fold_fs_price_msis (εr : ℝ → ℝ) (εM : ℝ)
    (hnn : ∀ δ ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ εr δ + εM)
    (extractFn : Stmt (foldReduction S T hT Kh chalVal b₀) →
      Transcript C Kh → W → W)
    (h : FoldRoundBound S T hT Kh chalVal b₀ extractFn (fun δ => εr δ + εM))
    (Z : Set (Stmt (foldReduction S T hT Kh chalVal b₀))) :
    FsStraightlineKnowledgeSoundness (foldReduction S T hT Kh chalVal b₀) Z
      (fun _s t δ =>
        ((t : ℝ) + (T : ℝ)) * εr δ + ((t : ℝ) + (T : ℝ)) * εM) := by
  have hfun : (fun (_s t : ℕ) (δ : ℝ) =>
        ((t : ℝ) + (T : ℝ)) * εr δ + ((t : ℝ) + (T : ℝ)) * εM)
      = (fun (_s t : ℕ) (δ : ℝ) =>
        ((t : ℝ) + (T : ℝ)) * (εr δ + εM)) := by
    funext _s t δ
    ring
  rw [hfun]
  exact fold_fs_sound S T hT Kh chalVal b₀ (fun δ => εr δ + εM) hnn
    extractFn h Z

end FoldReduction

/-! ## The Z = ∅ corner, at the fold shape — it RECURS; additivity does not
dissolve it -/

section FoldOB2Corner

/-- The UNGUARDED depth composition restricted to fold reductions — the
[OB-2] shape (`Rbr.lean`) with `εfold` constrained only ON `Z`, quantified
over every fold instance. `Depth.lean` proved the general statement FALSE at
`Z = ∅`; the question the brief asked: does the additive message algebra
dissolve that corner? -/
def FoldOB2Unguarded : Prop :=
  ∀ (R W C : Type) [Ring R] [AddCommGroup W] [AddCommGroup C]
    [Module R W] [Module R C] (S : FoldCommitScheme R W C)
    (T : ℕ) (hT : 0 < T) (Kh : Type) [Fintype Kh] [Nonempty Kh]
    (chalVal : Kh → R) (b₀ : ℝ)
    (rbr : RbrKnowledgeSoundness (foldReduction S T hT Kh chalVal b₀))
    (Z : Set (Stmt (foldReduction S T hT Kh chalVal b₀))) (εfold : ℝ → ℝ),
    (∀ (i : Fin T) (st : Stmt (foldReduction S T hT Kh chalVal b₀)),
      st ∈ Z → ∀ δ ∈ Set.Ioo (0 : ℝ) 1, rbr.err i st δ ≤ εfold δ) →
    StraightlineSrKnowledgeSoundness (foldReduction S T hT Kh chalVal b₀) Z
      (fun _s t δ => ((t : ℝ) + (T : ℝ)) * εfold δ)

/-- The degenerate-but-genuine fold instance the refutation runs on: the zero
commitment over ℤ with the zero norm. Every field is inhabited honestly; the
fold algebra is the real one. -/
def zeroFoldScheme : FoldCommitScheme ℤ ℤ ℤ where
  commit := 0
  nrm := fun _ => 0
  nrm_nonneg := fun _ => le_refl 0
  nrm_zero := rfl
  nrm_neg := fun _ => rfl
  nrm_add := fun _ _ => by norm_num
  chalSet := Set.univ
  ρ := 0
  ρ_nonneg := le_refl 0
  B := 0
  B_nonneg := le_refl 0
  nrm_smul := fun _ _ _ => by norm_num

/-- **The corner RECURS — additivity does NOT dissolve it.** The refutation
never reads the message algebra: it lives in the ERROR algebra (`εfold`
unconstrained off `Z`, instantiated at `−1` against a nonnegative
probability), and the additive alphabet changed only the messages. Same move
as `OB2_depth_composition_false`: `Z = ∅`, `εfold = −1`, move budget `0`,
`T = 1`, the round bound met at `εfold ≡ 1` (`foldRoundBound_one`). The
GUARDED composition holds for every fold instance
(`fold_depth_composition`); the pair is the brief's "either answer is a
theorem worth having", with both halves on disk. -/
theorem foldOB2Unguarded_false : ¬ FoldOB2Unguarded := by
  intro h
  have h1 := h ℤ ℤ ℤ zeroFoldScheme 1 one_pos Bool (fun _ => 0) 0
    (foldRbrOfRoundBound zeroFoldScheme 1 one_pos Bool (fun _ => 0) 0
      (fun _ _ Y => Y) (fun _ => 1)
      (foldRoundBound_one zeroFoldScheme 1 one_pos Bool (fun _ => 0) 0
        (fun _ _ Y => Y)))
    ∅ (fun _ => -1)
    (fun _i st hst => ((Set.mem_empty_iff_false st).mp hst).elim)
  obtain ⟨E, hE⟩ := h1
  have hbound := hE 0 0 (1 / 2)
    (by rw [Set.mem_Ioo]; constructor <;> norm_num)
    ⟨fun _ => ⟨⟨(), 0, fun _ => ()⟩, []⟩,
      fun _ => ⟨⟨(), 0, fun _ => ()⟩, fun _ => 0, fun _ => Fin.elim0, 0⟩⟩
  have hcontra := le_trans (uniformProb_nonneg _) hbound
  norm_num at hcontra

end FoldOB2Corner

/-! ## The dual-mode linear mode: the integer-lattice instance -/

section IntInstance

/-- The ℕ-valued ∞-norm of an integer vector (`Finset.sup` of the coordinate
absolute values; `0` on the empty vector). -/
def supNat {N : ℕ} (Y : Fin N → ℤ) : ℕ :=
  Finset.univ.sup fun i => (Y i).natAbs

/-- The ∞-norm, as the ℝ-valued norm the scheme carries. Shortness lives in
ℤ — `ZMod q` has no norm; this is why the witness module is `Fin N → ℤ` and
the commitment reduces mod `q` only at the very end. -/
noncomputable def supNorm {N : ℕ} (Y : Fin N → ℤ) : ℝ := (supNat Y : ℝ)

theorem coord_le_supNat {N : ℕ} (Y : Fin N → ℤ) (i : Fin N) :
    (Y i).natAbs ≤ supNat Y := by
  unfold supNat
  exact Finset.le_sup (f := fun j => (Y j).natAbs) (Finset.mem_univ i)

theorem supNat_le_iff {N : ℕ} {Y : Fin N → ℤ} {b : ℕ} :
    supNat Y ≤ b ↔ ∀ i, (Y i).natAbs ≤ b := by
  unfold supNat
  rw [Finset.sup_le_iff]
  exact ⟨fun h i => h i (Finset.mem_univ i), fun h i _ => h i⟩

theorem supNat_zero {N : ℕ} : supNat (0 : Fin N → ℤ) = 0 :=
  Nat.le_zero.mp (supNat_le_iff.mpr fun _ => by simp)

theorem supNat_neg {N : ℕ} (Y : Fin N → ℤ) : supNat (-Y) = supNat Y := by
  unfold supNat
  congr 1
  funext i
  rw [Pi.neg_apply, Int.natAbs_neg]

theorem supNat_add_le {N : ℕ} (Y Z : Fin N → ℤ) :
    supNat (Y + Z) ≤ supNat Y + supNat Z :=
  supNat_le_iff.mpr fun i =>
    calc ((Y + Z) i).natAbs = (Y i + Z i).natAbs := rfl
      _ ≤ (Y i).natAbs + (Z i).natAbs := Int.natAbs_add_le _ _
      _ ≤ supNat Y + supNat Z :=
          Nat.add_le_add (coord_le_supNat Y i) (coord_le_supNat Z i)

theorem supNat_smul_le {N : ℕ} (r : ℤ) (Y : Fin N → ℤ) :
    supNat (r • Y) ≤ r.natAbs * supNat Y :=
  supNat_le_iff.mpr fun i =>
    calc ((r • Y) i).natAbs = (r * Y i).natAbs := by
          rw [Pi.smul_apply, smul_eq_mul]
      _ = r.natAbs * (Y i).natAbs := Int.natAbs_mul r (Y i)
      _ ≤ r.natAbs * supNat Y :=
          Nat.mul_le_mul_left _ (coord_le_supNat Y i)

/-- The dual-mode linear map `Y ↦ A·Y mod q`, ℤ-linear into `Fin κ → ZMod q`.
Plain-SIS shape on purpose: a negacyclic `A` (the ring-structured module-SIS
of the dual-mode note) is a PARAMETER CHOICE of this map, not new formal
vocabulary. -/
def intCommit (q : ℕ) [NeZero q] {κ N : ℕ} (A : Fin κ → Fin N → ℤ) :
    (Fin N → ℤ) →ₗ[ℤ] (Fin κ → ZMod q) where
  toFun := fun Y i => ((∑ j, A i j * Y j : ℤ) : ZMod q)
  map_add' := by
    intro Y Z
    funext i
    show ((∑ j, A i j * (Y j + Z j) : ℤ) : ZMod q)
      = ((∑ j, A i j * Y j : ℤ) : ZMod q) + ((∑ j, A i j * Z j : ℤ) : ZMod q)
    push_cast
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  map_smul' := by
    intro r Y
    funext i
    show ((∑ j, A i j * (r * Y j) : ℤ) : ZMod q)
      = r • ((∑ j, A i j * Y j : ℤ) : ZMod q)
    rw [zsmul_eq_mul]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

theorem intCommit_apply (q : ℕ) [NeZero q] {κ N : ℕ}
    (A : Fin κ → Fin N → ℤ) (Y : Fin N → ℤ) (i : Fin κ) :
    intCommit q A Y i = ((∑ j, A i j * Y j : ℤ) : ZMod q) := rfl

/-- The kill lemma: a vector all of whose coordinates are divisible by `q`
commits to `0` — for EVERY key. This is the wraparound the break rides. -/
theorem intCommit_eq_zero_of_dvd (q : ℕ) [NeZero q] {κ N : ℕ}
    (A : Fin κ → Fin N → ℤ) {Y : Fin N → ℤ} (h : ∀ j, (q : ℤ) ∣ Y j) :
    intCommit q A Y = 0 := by
  funext i
  rw [intCommit_apply]
  rw [show (0 : Fin κ → ZMod q) i = 0 from rfl]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact Finset.dvd_sum fun j _ => (h j).mul_left _

/-- **The dual-mode linear mode as a `FoldCommitScheme`**: planes over ℤ,
commitments in `ZMod q`, challenge set the short integers `|r| ≤ ρnat`,
per-instance bound `Bnat`. -/
noncomputable def intFoldScheme (q : ℕ) [NeZero q] {κ N : ℕ}
    (A : Fin κ → Fin N → ℤ) (ρnat Bnat : ℕ) :
    FoldCommitScheme ℤ (Fin N → ℤ) (Fin κ → ZMod q) where
  commit := intCommit q A
  nrm := supNorm
  nrm_nonneg := fun _ => Nat.cast_nonneg _
  nrm_zero := by rw [supNorm, supNat_zero, Nat.cast_zero]
  nrm_neg := fun Y => by rw [supNorm, supNorm, supNat_neg]
  nrm_add := fun Y Z => by
    rw [supNorm, supNorm, supNorm, ← Nat.cast_add]
    exact_mod_cast supNat_add_le Y Z
  chalSet := {r : ℤ | r.natAbs ≤ ρnat}
  ρ := ρnat
  ρ_nonneg := Nat.cast_nonneg _
  B := Bnat
  B_nonneg := Nat.cast_nonneg _
  nrm_smul := fun γ hγ Y => by
    have h1 : supNat (γ • Y) ≤ ρnat * supNat Y :=
      le_trans (supNat_smul_le γ Y) (Nat.mul_le_mul_right _ hγ)
    rw [supNorm, supNorm, ← Nat.cast_mul]
    exact_mod_cast h1

@[simp] theorem intFoldScheme_commit (q : ℕ) [NeZero q] {κ N : ℕ}
    (A : Fin κ → Fin N → ℤ) (ρnat Bnat : ℕ) :
    (intFoldScheme q A ρnat Bnat).commit = intCommit q A := rfl

@[simp] theorem intFoldScheme_nrm (q : ℕ) [NeZero q] {κ N : ℕ}
    (A : Fin κ → Fin N → ℤ) (ρnat Bnat : ℕ) :
    (intFoldScheme q A ρnat Bnat).nrm = supNorm := rfl

@[simp] theorem intFoldScheme_ρ (q : ℕ) [NeZero q] {κ N : ℕ}
    (A : Fin κ → Fin N → ℤ) (ρnat Bnat : ℕ) :
    (intFoldScheme q A ρnat Bnat).ρ = ρnat := rfl

@[simp] theorem intFoldScheme_B (q : ℕ) [NeZero q] {κ N : ℕ}
    (A : Fin κ → Fin N → ℤ) (ρnat Bnat : ℕ) :
    (intFoldScheme q A ρnat Bnat).B = Bnat := rfl

/-! ### Teeth: a fold exceeding the norm budget LOSES binding — constructive -/

/-- A one-coordinate spike. -/
def unitSpike {N : ℕ} (j₀ : Fin N) (c : ℤ) : Fin N → ℤ :=
  fun j => if j = j₀ then c else 0

theorem unitSpike_supNat_le {N : ℕ} (j₀ : Fin N) (c : ℤ) :
    supNat (unitSpike j₀ c) ≤ c.natAbs :=
  supNat_le_iff.mpr fun i => by
    unfold unitSpike
    by_cases hi : i = j₀ <;> simp [hi]

theorem unitSpike_sub {N : ℕ} (j₀ : Fin N) (c d : ℤ) :
    unitSpike j₀ c - unitSpike j₀ d = unitSpike j₀ (c - d) := by
  funext j
  by_cases hj : j = j₀ <;> simp [unitSpike, hj]

/-- **The wraparound pair — binding LOST past `⌈q/2⌉`, for EVERY key,
constructively**: `⌈q/2⌉·e₀` and `−⌊q/2⌋·e₀` are two DISTINCT vectors of norm
`≤ ⌈q/2⌉` whose difference is `q·e₀`, so they commit identically under every
`A`. No primality, no rank argument, no estimator: once the norm cap reaches
the wraparound, the short-plane subtype stops constraining and "binding" is
not weakened but GONE — the dual-mode note's §5c fail-open, exhibited. -/
theorem binding_lost_at_wraparound (q : ℕ) [NeZero q] {κ N : ℕ}
    (hN : 0 < N) (A : Fin κ → Fin N → ℤ) (ρnat Bnat : ℕ) {β : ℝ}
    (hβ : (((q + 1) / 2 : ℕ) : ℝ) ≤ β) :
    ¬ (intFoldScheme q A ρnat Bnat).BindingAt β := by
  intro hbind
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hba : q / 2 ≤ (q + 1) / 2 := by omega
  have hcom : (intFoldScheme q A ρnat Bnat).commit
        (unitSpike (⟨0, hN⟩ : Fin N) (((q + 1) / 2 : ℕ) : ℤ))
      = (intFoldScheme q A ρnat Bnat).commit
        (unitSpike (⟨0, hN⟩ : Fin N) (-((q / 2 : ℕ) : ℤ))) := by
    rw [intFoldScheme_commit, ← sub_eq_zero, ← map_sub, unitSpike_sub,
      show (((q + 1) / 2 : ℕ) : ℤ) - -((q / 2 : ℕ) : ℤ) = ((q : ℕ) : ℤ)
        from by omega]
    apply intCommit_eq_zero_of_dvd
    intro j
    unfold unitSpike
    by_cases hj : j = (⟨0, hN⟩ : Fin N) <;> simp [hj]
  have hn1 : (intFoldScheme q A ρnat Bnat).nrm
      (unitSpike (⟨0, hN⟩ : Fin N) (((q + 1) / 2 : ℕ) : ℤ)) ≤ β := by
    rw [intFoldScheme_nrm]
    refine le_trans ?_ hβ
    rw [supNorm]
    have h1 := le_trans
      (unitSpike_supNat_le (⟨0, hN⟩ : Fin N) (((q + 1) / 2 : ℕ) : ℤ))
      (le_of_eq (Int.natAbs_natCast _))
    exact_mod_cast h1
  have hn2 : (intFoldScheme q A ρnat Bnat).nrm
      (unitSpike (⟨0, hN⟩ : Fin N) (-((q / 2 : ℕ) : ℤ))) ≤ β := by
    rw [intFoldScheme_nrm]
    refine le_trans ?_ hβ
    rw [supNorm]
    have h1 : supNat (unitSpike (⟨0, hN⟩ : Fin N) (-((q / 2 : ℕ) : ℤ)))
        ≤ q / 2 := by
      refine le_trans (unitSpike_supNat_le _ _) (le_of_eq ?_)
      rw [Int.natAbs_neg, Int.natAbs_natCast]
    exact_mod_cast le_trans h1 hba
  have hne : unitSpike (⟨0, hN⟩ : Fin N) (((q + 1) / 2 : ℕ) : ℤ)
      ≠ unitSpike (⟨0, hN⟩ : Fin N) (-((q / 2 : ℕ) : ℤ)) := by
    intro h
    have h0 := congrFun h ⟨0, hN⟩
    unfold unitSpike at h0
    rw [if_pos rfl, if_pos rfl] at h0
    omega
  exact hne (hbind _ _ hcom hn1 hn2)

/-- The break at the FOLD budget: once `budget b₀ T` reaches the wraparound,
`BindingAt (budget b₀ T)` is false — the "exceeding the norm budget loses
binding" tooth in the shape the fold consumes. -/
theorem fold_budget_break (q : ℕ) [NeZero q] {κ N : ℕ} (hN : 0 < N)
    (A : Fin κ → Fin N → ℤ) (ρnat Bnat : ℕ) {b₀ : ℝ} {T : ℕ}
    (h : (((q + 1) / 2 : ℕ) : ℝ)
      ≤ (intFoldScheme q A ρnat Bnat).budget b₀ T) :
    ¬ (intFoldScheme q A ρnat Bnat).BindingAt
        ((intFoldScheme q A ρnat Bnat).budget b₀ T) :=
  binding_lost_at_wraparound q hN A ρnat Bnat h

end IntInstance

/-! ## The concrete fold capacity at the dual-mode parameters -/

/-! ### The dual-mode parameter point (`ring-hash-dual-mode.md` §5a: the τ=2
joint modulus), with ρ = 1 (the `{−1, 0, 1}` short-challenge set) and honest
genesis at `b₀ = B`. The capacity boundary is EXACT: the MSIS hypothesis
keeps a nonvacuous norm gap through `T = 2^47 − 2` folds, and at
`T = 2^47 − 1` the budget reaches the wraparound and binding is LOST for
every key (`production_break`). ⚠ Pessimistic reading, stated with the
claim: these theorems locate where binding provably DIES; where it provably
SURVIVES is the computational MSIS hypothesis at `2B(1+T)` — an assumption
that weakens as `T` grows, whose estimator run is the dual-mode note's O6,
un-run. -/
namespace DualModeParams

/-- `q = 2^64 − 257`. -/
def q : ℕ := 2 ^ 64 - 257
/-- `B = 2^16` — the gadget base, the per-plane ∞-bound. -/
def B : ℕ := 2 ^ 16
/-- `K = 4` planes (`B^K = 2^64`): recorded context — `K` shapes the witness
WIDTH (`N = K·m` columns of the key), not the budget recursion. -/
def K : ℕ := 4

theorem q_eq : q = 18446744073709551359 := by norm_num [q]

instance : NeZero q := ⟨by rw [q_eq]; norm_num⟩

/-- Through `T ≤ 2^47 − 2` folds the doubled budget stays strictly below `q`:
the MSIS-at-`2·f(T)` hypothesis retains a nonvacuous norm gap. -/
theorem capacity_safe : ∀ T : ℕ, T ≤ 2 ^ 47 - 2 →
    2 * (B * (1 + T)) < q := by
  intro T hT
  have hB : B = 65536 := by norm_num [B]
  have h47 : (2 : ℕ) ^ 47 - 2 = 140737488355326 := by norm_num
  rw [hB, q_eq]
  rw [h47] at hT
  omega

/-- At `T = 2^47 − 1` the budget reaches `⌈q/2⌉` — the wraparound pair
applies. -/
theorem capacity_broken : (q + 1) / 2 ≤ B * (1 + (2 ^ 47 - 1)) := by
  rw [q_eq]
  norm_num [B]

/-- Tightness: at `T = 2^47 − 1` the doubled budget already meets `q` — the
boundary of `capacity_safe` is exact, not slack. -/
theorem capacity_exact : q ≤ 2 * (B * (1 + (2 ^ 47 - 1))) := by
  rw [q_eq]
  norm_num [B]

/-- The budget of the production scheme, in closed ℕ form. -/
theorem production_budget (T : ℕ) {κ N : ℕ} (A : Fin κ → Fin N → ℤ) :
    (intFoldScheme q A 1 B).budget (B : ℝ) T = ((B * (1 + T) : ℕ) : ℝ) := by
  rw [FoldCommitScheme.budget, intFoldScheme_ρ, intFoldScheme_B]
  push_cast
  ring

/-- **The bounded-folds theorem at the production point, positive half**:
binding at the `T`-fold budget from the (named, `[FOLD-msis]`) MSIS
hypothesis at twice the budget — and `production_msis_gap` certifies that
for `T ≤ 2^47 − 2` that hypothesis still has a norm gap below `q` to live
in. -/
theorem production_fold_binding {κ N : ℕ} (A : Fin κ → Fin N → ℤ) (T : ℕ)
    (h : (intFoldScheme q A 1 B).MsisHardEx
      (2 * (intFoldScheme q A 1 B).budget (B : ℝ) T)) :
    (intFoldScheme q A 1 B).BindingAt
      ((intFoldScheme q A 1 B).budget (B : ℝ) T) :=
  (intFoldScheme q A 1 B).fold_binding h

theorem production_msis_gap {T : ℕ} (hT : T ≤ 2 ^ 47 - 2) {κ N : ℕ}
    (A : Fin κ → Fin N → ℤ) :
    2 * (intFoldScheme q A 1 B).budget (B : ℝ) T < (q : ℝ) := by
  rw [production_budget]
  have h1 := capacity_safe T hT
  exact_mod_cast h1

/-- **The bounded-folds theorem at the production point, negative half**: at
`T ≥ 2^47 − 1` folds, binding at the budget is FALSE — unconditionally,
constructively, for every key. Together with `production_fold_binding` and
`capacity_exact`: after `T` folds the norm bound is `B(1+T)`, and binding
holds iff `2B(1+T)` stays inside the MSIS bound — with the structural wall
exactly at `T = 2^47 − 1`. -/
theorem production_break {κ N : ℕ} (hN : 0 < N) (A : Fin κ → Fin N → ℤ)
    {T : ℕ} (hT : 2 ^ 47 - 1 ≤ T) :
    ¬ (intFoldScheme q A 1 B).BindingAt
        ((intFoldScheme q A 1 B).budget (B : ℝ) T) := by
  apply binding_lost_at_wraparound q hN A 1 B
  rw [production_budget]
  have h1 : (q + 1) / 2 ≤ B * (1 + T) :=
    le_trans capacity_broken (Nat.mul_le_mul_left _ (by omega))
  exact_mod_cast h1

end DualModeParams

/-! ## `ProofSystem` consumers — the HeteroComposition seam, fed -/

section FoldSystems

variable {R : Type} [Ring R] {W C : Type} [AddCommGroup W] [AddCommGroup C]
  [Module R W] [Module R C]

open Classical in
/-- The plain commitment as a `ProofSystem` — the DECIDER layer: the proof IS
the short opening, so knowledge-soundness is definitional
(`plainCommitSystem_knowledgeSound`); no extraction is claimed, only the
carrier `VerifierEmbedding`/`rung_sound` consume. -/
noncomputable def plainCommitSystem (S : FoldCommitScheme R W C) (β : ℝ) :
    ProofSystem where
  Stmt := C
  Wit := W
  Proof := W
  Rel := fun c Y => S.ShortOpens β c Y
  Verify := fun c Y => decide (S.ShortOpens β c Y)
  err := 0
  err_nonneg := le_refl 0

open Classical in
/-- The `T`-fold accumulator endpoint as a `ProofSystem`: statement =
(genesis, absorbed commitments, challenge schedule), proof = one plane
vector, verification = "opens the COMPUTED fold within the budget". -/
noncomputable def foldSystem (S : FoldCommitScheme R W C) (Kh : Type)
    (chalVal : Kh → R) (b₀ : ℝ) (T : ℕ) : ProofSystem where
  Stmt := C × (Fin T → C) × (Fin T → Kh)
  Wit := W
  Proof := W
  Rel := fun s Y => S.ShortOpens (S.budget b₀ T)
    (chalFoldList chalVal s.1 (List.ofFn fun i => (s.2.1 i, s.2.2 i))) Y
  Verify := fun s Y => decide (S.ShortOpens (S.budget b₀ T)
    (chalFoldList chalVal s.1 (List.ofFn fun i => (s.2.1 i, s.2.2 i))) Y)
  err := 0
  err_nonneg := le_refl 0

theorem plainCommitSystem_knowledgeSound (S : FoldCommitScheme R W C)
    (β : ℝ) : KnowledgeSound (plainCommitSystem S β) :=
  fun _x π h => ⟨π, by classical exact of_decide_eq_true h⟩

theorem foldSystem_knowledgeSound (S : FoldCommitScheme R W C) (Kh : Type)
    (chalVal : Kh → R) (b₀ : ℝ) (T : ℕ) :
    KnowledgeSound (foldSystem S Kh chalVal b₀ T) :=
  fun _x π h => ⟨π, by classical exact of_decide_eq_true h⟩

/-- **T = 0 IS the plain commitment** — the coincidence as a
`VerifierEmbedding` (HeteroComposition's seam), `fwd` AND `bwd` both proved:
zero folds change nothing, at every scheme. -/
noncomputable def foldZeroToPlain (S : FoldCommitScheme R W C) (Kh : Type)
    (chalVal : Kh → R) (b₀ : ℝ) :
    VerifierEmbedding (foldSystem S Kh chalVal b₀ 0)
      (plainCommitSystem S b₀) where
  encStmt := fun s => s.1
  encProof := id
  fwd := fun x π h => by
    classical
    have h' : S.ShortOpens (S.budget b₀ 0)
        (chalFoldList chalVal x.1 (List.ofFn fun i => (x.2.1 i, x.2.2 i)))
        π := of_decide_eq_true h
    show S.ShortOpens b₀ x.1 π
    simpa only [List.ofFn_zero, chalFoldList_nil,
      FoldCommitScheme.budget_zero] using h'
  bwd := fun x w h => by
    classical
    refine ⟨w, rfl, decide_eq_true ?_⟩
    show S.ShortOpens (S.budget b₀ 0)
        (chalFoldList chalVal x.1 (List.ofFn fun i => (x.2.1 i, x.2.2 i))) w
    simpa only [List.ofFn_zero, chalFoldList_nil,
      FoldCommitScheme.budget_zero] using h

/-- The reverse embedding: the plain commitment IS a zero-fold accumulator.
Together with `foldZeroToPlain`: the coincidence in both directions, at the
cross-module `VerifierEmbedding` carrier. -/
noncomputable def plainToFoldZero (S : FoldCommitScheme R W C) (Kh : Type)
    (chalVal : Kh → R) (b₀ : ℝ) :
    VerifierEmbedding (plainCommitSystem S b₀)
      (foldSystem S Kh chalVal b₀ 0) where
  encStmt := fun c => (c, fun i => i.elim0, fun i => i.elim0)
  encProof := id
  fwd := fun x π h => by
    classical
    have h' : S.ShortOpens b₀ x π := of_decide_eq_true h
    show S.ShortOpens (S.budget b₀ 0)
      (chalFoldList chalVal x (List.ofFn fun i : Fin 0 => (i.elim0, i.elim0)))
      π
    simpa only [List.ofFn_zero, chalFoldList_nil,
      FoldCommitScheme.budget_zero] using h'
  bwd := fun x w h => by
    classical
    refine ⟨w, rfl, decide_eq_true ?_⟩
    show S.ShortOpens b₀ x w
    have h' : S.ShortOpens (S.budget b₀ 0)
        (chalFoldList chalVal x
          (List.ofFn fun i : Fin 0 => (i.elim0, i.elim0))) w := h
    simpa only [List.ofFn_zero, chalFoldList_nil,
      FoldCommitScheme.budget_zero] using h'

/-- **T = 1 at zero genesis under a unit challenge coincides with the plain
commitment at bound `ρ·B`** — at the short-challenge instance (`ρ = 1`) that
is the plain commitment at `B` on the nose. The one-fold accumulator holding
a single absorbed commitment IS that commitment. -/
theorem foldSystem_one_iff_plain (S : FoldCommitScheme R W C) (Kh : Type)
    (chalVal : Kh → R) (ρ1 : Kh) (hρ : chalVal ρ1 = 1) (Cw : C) (Y : W) :
    (foldSystem S Kh chalVal 0 1).Rel (0, fun _ => Cw, fun _ => ρ1) Y ↔
      (plainCommitSystem S (S.ρ * S.B)).Rel Cw Y := by
  show S.ShortOpens (S.budget 0 1)
      (chalFoldList chalVal 0 (List.ofFn fun _ : Fin 1 => (Cw, ρ1))) Y ↔
    S.ShortOpens (S.ρ * S.B) Cw Y
  have h0 : (List.ofFn fun _ : Fin 1 => (Cw, ρ1)) = [(Cw, ρ1)] := by
    simp [List.ofFn_succ]
  have h1 : chalFoldList chalVal (0 : C)
      (List.ofFn fun _ : Fin 1 => (Cw, ρ1)) = Cw := by
    rw [h0, chalFoldList_cons, chalFoldList_nil, hρ, one_smul, zero_add]
  have h2 : S.budget 0 1 = S.ρ * S.B := by
    unfold FoldCommitScheme.budget
    norm_num
  rw [h1, h2]

open Classical in
/-- The fail-open shape: the SAME verifier relation with the norm conjunct
DROPPED — the dual-mode note's §5c hazard ("binding does not degrade, it
VANISHES"), as a `ProofSystem`. `dropped_norm_check_refuses_embedding` below
proves the type REFUSES it. -/
noncomputable def plainNoNormSystem (S : FoldCommitScheme R W C) :
    ProofSystem where
  Stmt := C
  Wit := W
  Proof := W
  Rel := fun c Y => S.commit Y = c
  Verify := fun c Y => decide (S.commit Y = c)
  err := 0
  err_nonneg := le_refl 0

end FoldSystems

/-- `Pr` positivity from a single witness — the counting complement of
`uniformProb_false`. -/
theorem uniformProb_pos_of_witness {Ch : Type} [Fintype Ch] {p : Ch → Prop}
    (c₀ : Ch) (h : p c₀) : 0 < uniformProb Ch p := by
  unfold uniformProb
  apply div_pos
  · have h1 : Nonempty {c : Ch // p c} := ⟨⟨c₀, h⟩⟩
    have h2 : 0 < Nat.card {c : Ch // p c} := Nat.card_pos
    exact_mod_cast h2
  · have h3 : (0 : ℕ) < Fintype.card Ch := @Fintype.card_pos Ch _ ⟨c₀⟩
    exact_mod_cast h3

/-! ## Keystones (ATLAS law 2): the toy instance, satisfiable AND refutable -/

namespace ToyFold

/-- The toy key: `A = [1, 10]` over `Z₉₇`, one row, two columns. Chosen so
the short kernel is provably empty at bound 4 (`|Y₀ + 10·Y₁| ≤ 44 < 97`)
while the wraparound pair still fires at 49 — one instance carrying both
verdicts. -/
def A97 : Fin 1 → Fin 2 → ℤ := fun _ j => if j = 0 then 1 else 10

/-- The toy scheme: `q = 97`, challenge bound `ρ = 1`, per-instance bound
`B = 1`. -/
noncomputable def toy : FoldCommitScheme ℤ (Fin 2 → ℤ) (Fin 1 → ZMod 97) :=
  intFoldScheme 97 A97 1 1

theorem toy_budget (b₀ : ℝ) (T : ℕ) : toy.budget b₀ T = b₀ + T := by
  unfold FoldCommitScheme.budget
  rw [show toy.ρ = ((1 : ℕ) : ℝ) from rfl, show toy.B = ((1 : ℕ) : ℝ) from rfl]
  norm_num

/-- **The MSIS hypothesis, PROVED at the toy point** (premise-inhabitation
for the whole binding story): the only kernel vector of norm ≤ 4 is zero —
`97 ∣ Y₀ + 10·Y₁` with `|Y₀ + 10·Y₁| ≤ 44` forces the integer to vanish,
then the coordinates. -/
theorem msisHardEx_toy : toy.MsisHardEx 4 := by
  intro Y hc hn
  have hn' : supNorm Y ≤ 4 := hn
  have hsup : supNat Y ≤ 4 := by
    rw [supNorm, show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num] at hn'
    exact_mod_cast hn'
  have h0 : (Y 0).natAbs ≤ 4 := le_trans (coord_le_supNat Y 0) hsup
  have h1 : (Y 1).natAbs ≤ 4 := le_trans (coord_le_supNat Y 1) hsup
  have hval : intCommit 97 A97 Y 0 = ((Y 0 + 10 * Y 1 : ℤ) : ZMod 97) := by
    rw [intCommit_apply]
    congr 1
    rw [Fin.sum_univ_two]
    rw [show A97 0 0 = 1 from rfl, show A97 0 1 = 10 from rfl]
    ring
  have hcast : ((Y 0 + 10 * Y 1 : ℤ) : ZMod 97) = 0 := by
    rw [← hval]
    exact congrFun hc 0
  have hdvd : (97 : ℤ) ∣ (Y 0 + 10 * Y 1) := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (Y 0 + 10 * Y 1) 97).mp hcast
    exact_mod_cast this
  obtain ⟨c, hcm⟩ := hdvd
  have hc0 : c = 0 := by omega
  have hy1 : Y 1 = 0 := by omega
  have hy0 : Y 0 = 0 := by omega
  funext i
  fin_cases i
  · exact hy0
  · exact hy1

/-- **Satisfiable**: binding holds through one fold at the toy point —
`budget 1 1 = 2`, and `MsisHardEx 4` (proved) covers `2·2`. -/
theorem toy_binding_T1 : toy.BindingAt (toy.budget 1 1) := by
  apply toy.bindingAt_of_msisHardEx
  have h : (2 : ℝ) * toy.budget 1 1 = 4 := by
    rw [toy_budget]
    norm_num
  rw [h]
  exact msisHardEx_toy

/-- **Refutable, at the SAME instance**: 48 folds runs the budget to
`⌈97/2⌉ = 49` and binding is GONE — the wraparound pair, fired. One
instance, both verdicts. -/
theorem toy_fold_break : ¬ toy.BindingAt (toy.budget 1 48) := by
  have h : (((97 + 1) / 2 : ℕ) : ℝ) ≤ toy.budget 1 48 := by
    rw [toy_budget]
    norm_num
  exact binding_lost_at_wraparound 97 (by norm_num) A97 1 1 h

/-! ### Teeth for the round-bound obligation -/

/-- The `{−1, 0, 1}` challenge decode. -/
def chalVal3 : Fin 3 → ℤ := fun i => (i : ℤ) - 1

/-- The spike witness `e₀ = (1, 0)`. -/
def e01 : Fin 2 → ℤ := unitSpike 0 1

theorem toy_commit_e01 : intCommit 97 A97 e01 0 = (1 : ZMod 97) := by
  rw [intCommit_apply, show (∑ j, A97 0 j * e01 j) = 1 from by decide]
  exact Int.cast_one

/-- A base point shifted along the kernel ray `97k·e₀`. -/
def shiftSpike (b : Fin 2 → ℤ) (k : ℕ) : Fin 2 → ℤ :=
  b + unitSpike 0 ((97 * k : ℕ) : ℤ)

/-- **`FoldRoundBound` is REFUTABLE** (with `foldRoundBound_one` as its
satisfiability, the Prove-The-Floor-FALSE pair): at the toy instance,
`εfold ≡ 0` with the identity extractor is false — the honest one-fold data
inhabits the round event at challenge `+1`: `e₀` opens the extended fold
(`0 + 1·commit e₀`) inside budget 1, while the id-extracted prefix state
demands `commit e₀ = 0`, refuted. The per-fold price is REAL. -/
theorem toy_roundBound_zero_id_false :
    ¬ FoldRoundBound toy 1 one_pos (Fin 3) chalVal3 0 (fun _ _ Y => Y)
      (fun _ => 0) := by
  intro h
  classical
  have hh := h (1 / 2) (by rw [Set.mem_Ioo]; constructor <;> norm_num)
    ⟨(), 0, fun _ => ()⟩ 0 [] rfl (intCommit 97 A97 e01)
  have hev : ∃ Y : Fin 2 → ℤ,
      (foldKState toy 1 one_pos (Fin 3) chalVal3 0).state (1 / 2)
          ⟨(), 0, fun _ => ()⟩ ⟨[], some (intCommit 97 A97 e01)⟩ Y = false ∧
      (foldKState toy 1 one_pos (Fin 3) chalVal3 0).state (1 / 2)
          ⟨(), 0, fun _ => ()⟩
          ⟨[] ++ [(intCommit 97 A97 e01, (2 : Fin 3))], none⟩ Y = true := by
    refine ⟨e01, ?_, ?_⟩
    · rw [show (foldKState toy 1 one_pos (Fin 3) chalVal3 0).state (1 / 2)
          ⟨(), 0, fun _ => ()⟩ ⟨[], some (intCommit 97 A97 e01)⟩ e01
        = decide (FoldStateProp toy (Fin 3) chalVal3 0 0 [] e01) from rfl]
      rw [decide_eq_false_iff_not]
      rintro ⟨hcom, -⟩
      rw [chalFoldList_nil] at hcom
      have h0 : intCommit 97 A97 e01 0 = 0 := congrFun hcom 0
      rw [toy_commit_e01] at h0
      exact absurd h0 (by decide)
    · rw [show (foldKState toy 1 one_pos (Fin 3) chalVal3 0).state (1 / 2)
          ⟨(), 0, fun _ => ()⟩
          ⟨[] ++ [(intCommit 97 A97 e01, (2 : Fin 3))], none⟩ e01
        = decide (FoldStateProp toy (Fin 3) chalVal3 0 0
            ([] ++ [(intCommit 97 A97 e01, (2 : Fin 3))]) e01) from rfl]
      rw [decide_eq_true_eq]
      constructor
      · show intCommit 97 A97 e01 = chalFoldList chalVal3 (0 : Fin 1 → ZMod 97)
          ([] ++ [(intCommit 97 A97 e01, (2 : Fin 3))])
        decide
      · show supNorm e01 ≤ toy.budget 0
          ([] ++ [(intCommit 97 A97 e01, (2 : Fin 3))] :
            List ((Fin 1 → ZMod 97) × Fin 3)).length
        rw [show ([] ++ [(intCommit 97 A97 e01, (2 : Fin 3))] :
            List ((Fin 1 → ZMod 97) × Fin 3)).length = 1 from rfl,
          toy_budget, supNorm, show supNat e01 = 1 from by decide]
        norm_num
  refine absurd hh (not_le.mpr ?_)
  refine uniformProb_pos_of_witness (2 : Fin 3) ?_
  exact hev

/-- ⚑⚑ **The dropped-norm-check gate REFUSES an embedding** — the §5c
fail-open hazard, machine-checked at the `VerifierEmbedding` carrier: the
system whose relation forgets the norm bound admits NO embedding from the
budgeted one, whatever `encStmt`/`encProof` are chosen. Argument: `fwd` at
the zero proof pins a commitment in the range; its unbudgeted coset is
INFINITE (`+ 97k·e₀` never leaves it), while the accepting proofs live in a
finite norm ball — `bwd` would have to surject the ball onto the coset. The
exact wound `widened_relation_refuses_embedding` refuses in the abstract,
here at the lattice instance where the widening is "forgot the norm
check". -/
theorem dropped_norm_check_refuses_embedding :
    IsEmpty (VerifierEmbedding (plainCommitSystem toy 1)
      (plainNoNormSystem toy)) := by
  constructor
  intro e
  classical
  have hacc0 : (plainCommitSystem toy 1).Verify (0 : Fin 1 → ZMod 97)
      (0 : Fin 2 → ℤ) = true := by
    apply decide_eq_true
    refine ⟨map_zero _, ?_⟩
    show supNorm (0 : Fin 2 → ℤ) ≤ 1
    rw [supNorm, supNat_zero]
    norm_num
  have hbase : toy.commit (e.encProof (0 : Fin 2 → ℤ))
      = e.encStmt (0 : Fin 1 → ZMod 97) :=
    e.fwd (0 : Fin 1 → ZMod 97) (0 : Fin 2 → ℤ) hacc0
  have hker : ∀ k : ℕ,
      toy.commit (unitSpike (0 : Fin 2) ((97 * k : ℕ) : ℤ)) = 0 := by
    intro k
    show intCommit 97 A97 (unitSpike (0 : Fin 2) ((97 * k : ℕ) : ℤ)) = 0
    apply intCommit_eq_zero_of_dvd
    intro j
    unfold unitSpike
    by_cases hj : j = 0
    · rw [if_pos hj]
      exact Int.natCast_dvd_natCast.mpr ⟨k, rfl⟩
    · rw [if_neg hj]
      exact dvd_zero _
  have hrel : ∀ k : ℕ, (plainNoNormSystem toy).Rel
      (e.encStmt (0 : Fin 1 → ZMod 97))
      (shiftSpike (e.encProof (0 : Fin 2 → ℤ)) k) :=
    fun k => by
      show toy.commit (shiftSpike (e.encProof (0 : Fin 2 → ℤ)) k)
        = e.encStmt (0 : Fin 1 → ZMod 97)
      unfold shiftSpike
      rw [map_add, hker k, add_zero, hbase]
  have hsel : ∀ k : ℕ, ∃ π,
      e.encProof π = shiftSpike (e.encProof (0 : Fin 2 → ℤ)) k ∧
      (plainCommitSystem toy 1).Verify (0 : Fin 1 → ZMod 97) π = true :=
    fun k => e.bwd (0 : Fin 1 → ZMod 97) _ (hrel k)
  choose g hg1 hg2 using hsel
  have hfin : Finite {π : Fin 2 → ℤ //
      (plainCommitSystem toy 1).Verify (0 : Fin 1 → ZMod 97) π = true} := by
    have hball : {π : Fin 2 → ℤ | ∀ i, π i ∈ Set.Icc (-1 : ℤ) 1}.Finite := by
      have hpi := Set.Finite.pi (fun _ : Fin 2 => Set.finite_Icc (-1 : ℤ) 1)
      refine Set.Finite.subset hpi ?_
      intro Y hY
      rw [Set.mem_pi]
      intro i _
      exact hY i
    have hsub : {π : Fin 2 → ℤ |
        (plainCommitSystem toy 1).Verify (0 : Fin 1 → ZMod 97) π = true}
        ⊆ {π : Fin 2 → ℤ | ∀ i, π i ∈ Set.Icc (-1 : ℤ) 1} := by
      intro π hπ
      obtain ⟨-, hn⟩ := of_decide_eq_true hπ
      have hn' : supNorm π ≤ 1 := hn
      have hs : supNat π ≤ 1 := by
        rw [supNorm, show (1 : ℝ) = ((1 : ℕ) : ℝ) from by norm_num] at hn'
        exact_mod_cast hn'
      intro i
      have hi := le_trans (coord_le_supNat π i) hs
      rw [Set.mem_Icc]
      omega
    exact Set.Finite.to_subtype (hball.subset hsub)
  obtain ⟨k, k', hkk, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => (⟨g k, hg2 k⟩ : {π : Fin 2 → ℤ //
      (plainCommitSystem toy 1).Verify (0 : Fin 1 → ZMod 97) π = true}))
  have hg : g k = g k' := congrArg Subtype.val heq
  have hw : shiftSpike (e.encProof (0 : Fin 2 → ℤ)) k
      = shiftSpike (e.encProof (0 : Fin 2 → ℤ)) k' := by
    rw [← hg1 k, ← hg1 k', hg]
  unfold shiftSpike at hw
  have hspike := add_left_cancel hw
  have h0 := congrFun hspike (0 : Fin 2)
  unfold unitSpike at h0
  rw [if_pos rfl, if_pos rfl] at h0
  have hnk : 97 * k = 97 * k' := by exact_mod_cast h0
  exact hkk (by omega)

end ToyFold

/-! ## Axiom audit — no `sorryAx` anywhere in this file -/

/-- info: 'Minidregg.Selvage.mFold_eq_partialFold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mFold_eq_partialFold
/-- info: 'Minidregg.Selvage.FoldCommitScheme.nrm_mFold_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FoldCommitScheme.nrm_mFold_le
/-- info: 'Minidregg.Selvage.FoldCommitScheme.commit_mFold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FoldCommitScheme.commit_mFold
/-- info: 'Minidregg.Selvage.fold_depth_composition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fold_depth_composition
/-- info: 'Minidregg.Selvage.fold_fs_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fold_fs_sound
/-- info: 'Minidregg.Selvage.fold_fs_price_msis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fold_fs_price_msis
/-- info: 'Minidregg.Selvage.foldOB2Unguarded_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms foldOB2Unguarded_false
/-- info: 'Minidregg.Selvage.binding_lost_at_wraparound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms binding_lost_at_wraparound
/-- info: 'Minidregg.Selvage.DualModeParams.production_break' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DualModeParams.production_break
/-- info: 'Minidregg.Selvage.ToyFold.msisHardEx_toy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ToyFold.msisHardEx_toy
/-- info: 'Minidregg.Selvage.ToyFold.toy_binding_T1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ToyFold.toy_binding_T1
/-- info: 'Minidregg.Selvage.ToyFold.toy_fold_break' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ToyFold.toy_fold_break
/-- info: 'Minidregg.Selvage.ToyFold.toy_roundBound_zero_id_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ToyFold.toy_roundBound_zero_id_false
/-- info: 'Minidregg.Selvage.ToyFold.dropped_norm_check_refuses_embedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ToyFold.dropped_norm_check_refuses_embedding
/-- info: 'Minidregg.Selvage.foldSystem_one_iff_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms foldSystem_one_iff_plain
/-- info: 'Minidregg.Selvage.DualModeParams.capacity_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DualModeParams.capacity_safe

end Minidregg.Selvage

