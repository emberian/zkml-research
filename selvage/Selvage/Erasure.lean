/-
# Selvage.Erasure — [ACC-extract-bind](b): from `t` opened columns to the FULL
folded codeword.

`Selvage/Commitment.lean` closed `[ACC-extract-bind]`(a)+(c) — binding and
attribution — AT THE RESOLUTION where every position of the word is opened
(`∀ i, verifyOpen …`). In deployment the prover opens only `t` spot-checked
columns (WARP App. B); obligation (b) of that seam's ledger is the lift from
those `t` opened SYMBOLS to the FULL committed word. This file closes (b) for
the unique-decoding regime `t ≥ d`: a Reed–Solomon codeword is an MDS code, so
`d` of its symbols at distinct positions determine the whole word by
Lagrange/Vandermonde interpolation — the SAME machinery `Selvage/ZKHiding.lean`
already proved for the masking layer, REUSED here rather than re-derived —
so `t ≥ d` opened columns recover it exactly.

**The argument, in the landed vocabulary:**

* RS is MDS (`Selvage/ZKHiding.lean`): `exists_codeword_open` — any `t ≤ d`
  symbol values at distinct points are the opening of SOME codeword
  (Lagrange interpolation); `open_determines` — `d ≤ t` opened symbols of TWO
  codewords force them equal EVERYWHERE, not merely at the queried points
  (root counting on the difference polynomial, `card_agreeSet_lt_of_ne`).
  `open_determines` at `t = d` is exactly "the whole word is a function of
  `d` of its symbols" — the theorem this file turns into an actual
  reconstruction function.
* `recoverFromColumns` builds that function: Lagrange-interpolate the
  degree-`< d` polynomial through the FIRST `d` of the `t` opened symbols
  (`Fin.castLE`), then evaluate it across the whole domain
  (`Selvage/ReedSolomon.lean`'s `evalOnDomain`). `recoverFromColumns_sound`
  proves it recovers the genuine word whenever the input actually came from
  one — the interpolated word agrees with `f` at the `d` points it was built
  from (`Lagrange.eval_interpolate_at_node`), and `open_determines` upgrades
  that `d`-point agreement to FULL word equality.
* `committed_word_recovered` connects to `Selvage/Commitment.lean`: given a
  `BindingCommitment` whose root commits a genuine codeword `w`, and `t ≥ d`
  VERIFIED openings at distinct positions, `recoverFromColumns` on the
  verified data returns `w` — binding (that the verified values ARE `w`'s
  symbols, via `S.binding` against `verifyOpen_of_commit_eq`) composed with
  erasure recovery (that those symbols determine `w`). This is
  `[ACC-extract-bind]`(b): the witness word whose openings AccExtract's
  algebra runs on, once opened at only `t` spot checks, is still THE word
  the root binds.

**What stays outside this file — `[ERASURE-list]`:** everything here is the
UNIQUE-decoding regime, `t ≥ d`, where the opened symbols pin down AT MOST
ONE codeword (and `recoverFromColumns` computes it whenever a genuine one
exists — `recoverFromColumns_mem` shows the output is always at least a
genuine low-degree codeword, whatever the input, so the machinery never lies
about its type even off the sound regime). Beyond unique decoding — a word
only δ-CLOSE to the code, in the Johnson list-decoding regime — `t` columns
may sit in the agreement sets of SEVERAL codewords at once, and picking one
needs the mutual-correlated-agreement machinery of
`Selvage/CorrelatedAgreement.lean` (already PROVED for RS at the
unique-decoding radius, `Selvage/ReedSolomon.lean`'s Corollary 4.11) plus the
list-enumeration wiring `Selvage/OutOfDomain.lean` flags as prose,
`[OOD-pin-proximity]`. That lift is real future work, entered here as
NEITHER a hypothesis NOR an axiom — this file's theorems require the
openings to literally BE symbols of a codeword already in the code, which is
exactly what `committed_word_recovered` gets for free from binding, not from
an assumed proximity bound.
-/
import Selvage.ZKHiding
import Selvage.Commitment

namespace Minidregg.Selvage

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-! ## `recoverFromColumns`: erasure decoding from `t ≥ d` opened columns -/

/-- **Erasure recovery.** Given `t` opened symbols (`vals` at the distinct
positions `opened`), interpolate the degree-`< d` polynomial through the
FIRST `d` of them (`Fin.castLE`, meaningful when `d ≤ t`) and evaluate it
across the WHOLE domain — the erasure-recovered codeword. Junk `0` outside
the regime (`¬ d ≤ t`), the `codewordPoly`-style `dif` idiom
(`Selvage/OutOfDomain.lean`): the def never pretends to succeed on too few
columns; `recoverFromColumns_teeth` below exhibits WHY it cannot. -/
noncomputable def recoverFromColumns (dom : ι ↪ F) (d : ℕ) {t : ℕ}
    (opened : Fin t → ι) (vals : Fin t → F) : ι → F :=
  if h : d ≤ t then
    evalOnDomain dom
      (Lagrange.interpolate (Finset.univ : Finset (Fin d))
        (dom ∘ opened ∘ Fin.castLE h) (vals ∘ Fin.castLE h))
  else 0

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Unfolding `recoverFromColumns` inside its regime `d ≤ t`. -/
theorem recoverFromColumns_eq (dom : ι ↪ F) (d : ℕ) {t : ℕ}
    (opened : Fin t → ι) (vals : Fin t → F) (hdt : d ≤ t) :
    recoverFromColumns dom d opened vals =
      evalOnDomain dom
        (Lagrange.interpolate (Finset.univ : Finset (Fin d))
          (dom ∘ opened ∘ Fin.castLE hdt) (vals ∘ Fin.castLE hdt)) := by
  unfold recoverFromColumns
  rw [dif_pos hdt]

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- The recovered word is ALWAYS a genuine low-degree codeword, whatever the
input — the interpolation degree bound (`Lagrange.degree_interpolate_lt`),
transcribed via `mem_reedSolomonCode_iff` exactly as `ZKHiding`'s
`exists_codeword_open` does. Consistency with the ACTUAL word the columns
came from is the sharper `recoverFromColumns_sound` below. -/
theorem recoverFromColumns_mem (dom : ι ↪ F) (d : ℕ) {t : ℕ}
    {opened : Fin t → ι} (hopen : Function.Injective (dom ∘ opened))
    (vals : Fin t → F) (hdt : d ≤ t) :
    recoverFromColumns dom d opened vals ∈ reedSolomonCode dom d := by
  rw [recoverFromColumns_eq dom d opened vals hdt]
  refine mem_reedSolomonCode_iff.mpr ⟨_, ?_, fun _ => rfl⟩
  have hinj : Set.InjOn (dom ∘ opened ∘ Fin.castLE hdt)
      (Finset.univ : Finset (Fin d)) :=
    (hopen.comp (Fin.castLE_injective hdt)).injOn
  have hdeg := Lagrange.degree_interpolate_lt
    (s := (Finset.univ : Finset (Fin d)))
    (v := dom ∘ opened ∘ Fin.castLE hdt) hinj (r := vals ∘ Fin.castLE hdt)
  rwa [Finset.card_univ, Fintype.card_fin] at hdeg

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- **THE LOAD-BEARING THEOREM — erasure recovery is sound.** If the `t ≥ d`
opened columns (at distinct positions) are ACTUALLY symbols of a codeword
`f`, `recoverFromColumns` returns `f` EXACTLY — full word equality, every
coordinate, not merely agreement at the opened ones. This is the MDS bound
doing real work: the interpolated word agrees with `f` at the `d` points it
was built from (`Lagrange.eval_interpolate_at_node`), and `open_determines`
(`Selvage/ZKHiding.lean`, root counting) forces two codewords agreeing at `d`
distinct points to coincide EVERYWHERE — the whole recovery, not a partial
match. -/
theorem recoverFromColumns_sound (dom : ι ↪ F) {d t : ℕ} (hdt : d ≤ t)
    {opened : Fin t → ι} (hopen : Function.Injective (dom ∘ opened))
    {f : ι → F} (hf : f ∈ reedSolomonCode dom d)
    {vals : Fin t → F} (hvals : ∀ j, vals j = f (opened j)) :
    recoverFromColumns dom d opened vals = f := by
  have hq : Function.Injective (dom ∘ (opened ∘ Fin.castLE hdt)) :=
    hopen.comp (Fin.castLE_injective hdt)
  have hgmem : recoverFromColumns dom d opened vals ∈ reedSolomonCode dom d :=
    recoverFromColumns_mem dom d hopen vals hdt
  have hinj : Set.InjOn (dom ∘ opened ∘ Fin.castLE hdt)
      (Finset.univ : Finset (Fin d)) :=
    (hopen.comp (Fin.castLE_injective hdt)).injOn
  have hagree : openSymbols (opened ∘ Fin.castLE hdt)
      (recoverFromColumns dom d opened vals) = openSymbols (opened ∘ Fin.castLE hdt) f := by
    funext j
    show (recoverFromColumns dom d opened vals) ((opened ∘ Fin.castLE hdt) j)
        = f ((opened ∘ Fin.castLE hdt) j)
    rw [recoverFromColumns_eq dom d opened vals hdt]
    show Polynomial.eval ((dom ∘ opened ∘ Fin.castLE hdt) j)
        (Lagrange.interpolate Finset.univ (dom ∘ opened ∘ Fin.castLE hdt) (vals ∘ Fin.castLE hdt))
        = f ((opened ∘ Fin.castLE hdt) j)
    rw [Lagrange.eval_interpolate_at_node (vals ∘ Fin.castLE hdt) hinj (Finset.mem_univ j)]
    exact hvals (Fin.castLE hdt j)
  exact (open_determines dom (le_refl d) hq hf hgmem hagree.symm).symm

/-! ## Connecting to `Selvage/Commitment.lean`: `[ACC-extract-bind]`(b) closed -/

section CommitmentBridge

variable {Root Op : Type*}

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- **`[ACC-extract-bind]`(b), closed for the unique-decoding regime.** A
`BindingCommitment` root committing a genuine RS codeword `w`, opened AND
VERIFIED at `t ≥ d` distinct positions, has its erasure-recovered word equal
to `w` exactly — composing binding (the verified values ARE `w`'s symbols:
`S.binding` against the honest opening `verifyOpen_of_commit_eq`) with
`recoverFromColumns_sound` (those symbols determine `w`). This closes the
`t`-column erasure lift `Selvage/Commitment.lean`'s module header deferred here:
witnesses AccExtract's algebra recovers from `t` spot-checked columns are
STILL attached to the prover's commitment, not merely to a low-degree word
consistent with the openings. -/
theorem committed_word_recovered (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) {d t : ℕ} (hdt : d ≤ t) {opened : Fin t → ι}
    (hopen : Function.Injective (dom ∘ opened)) {rt : Root} {w : ι → F}
    (hrt : rt = S.commit w) (hw : w ∈ reedSolomonCode dom d)
    {vals : Fin t → F} {op : Fin t → Op}
    (hverify : ∀ j, S.verifyOpen rt (opened j) (vals j) (op j)) :
    recoverFromColumns dom d opened vals = w :=
  recoverFromColumns_sound dom hdt hopen hw fun j =>
    S.binding rt (opened j) (vals j) (w (opened j)) (op j) (S.openAt w (opened j))
      (hverify j) (S.toOpeningScheme.verifyOpen_of_commit_eq hrt (opened j))

end CommitmentBridge

/-! ## Keystone hygiene (ATLAS law 2: satisfiable + teeth + premise inhabitation)

Over `RS[F₅, {0,1,2,3}, 2]` (`ReedSolomon.RSExample`) and the ideal
commitment (`Commitment.CommitExample.S₅`). -/

namespace ErasureExample

open RSExample CommitExample

/-- The `t = d = 2` query positions `(0, 1)` — distinct, at the recovery
bound. -/
def opened₂ : Fin 2 → Fin 4 := ![0, 1]

/-- **Premise inhabitation** — the opened positions are genuinely distinct,
at `t = d`. -/
theorem opened₂_inj : Function.Injective (dom₅ ∘ opened₂) := by decide

/-- **Satisfiable, bare recovery**: `xWord` is recovered EXACTLY from 2 of
its own symbols (positions `0, 1`) — `recoverFromColumns_sound` fires on
built data. -/
theorem xWord_recovered :
    recoverFromColumns dom₅ 2 opened₂ (fun j => xWord (opened₂ j)) = xWord :=
  recoverFromColumns_sound dom₅ (le_refl 2) opened₂_inj xWord_mem fun _ => rfl

/-- The recovery reaches an UNOPENED coordinate (position `3`, never
queried) correctly — the erasure-recovery content, not a restatement of the
input: 2 symbols reconstruct all 4. -/
theorem xWord_recovered_unopened :
    recoverFromColumns dom₅ 2 opened₂ (fun j => xWord (opened₂ j)) 3 = 3 := by
  rw [xWord_recovered]; decide

/-- **Satisfiable, through the commitment**: `xWord`'s openings against the
ideal commitment VERIFY (completeness), and recovering from them returns
the COMMITTED word — the full `[ACC-extract-bind]`(b) pipeline fires
end-to-end on built objects. -/
theorem committed_recovered_fires :
    recoverFromColumns dom₅ 2 opened₂ (fun j => xWord (opened₂ j)) = xWord :=
  committed_word_recovered S₅ dom₅ (le_refl 2) opened₂_inj rfl xWord_mem
    fun j => S₅.verifyOpen_commit xWord (opened₂ j)

/-- A second codeword sharing `xWord`'s value at position `0` — evaluations
of `2X`, distinct from `xWord` (evaluations of `X`). -/
def twoXWord : Fin 4 → ZMod 5 := fun i => 2 * (i.val : ZMod 5)

theorem twoXWord_mem : twoXWord ∈ reedSolomonCode dom₅ 2 :=
  mem_reedSolomonCode_iff.mpr
    ⟨Polynomial.C 2 * Polynomial.X + Polynomial.C 0,
      lt_of_le_of_lt Polynomial.degree_linear_le (by decide),
      fun i => by simp [twoXWord, dom₅]⟩

theorem xWord_ne_twoXWord : xWord ≠ twoXWord := by decide

/-- The single `t = 1 = d − 1` query position `0`. -/
def opened₁ : Fin 1 → Fin 4 := ![0]

theorem opened₁_inj : Function.Injective (dom₅ ∘ opened₁) := by decide

/-- **Teeth — `t = d − 1` genuinely does NOT determine the word.** Two
DISTINCT codewords (`xWord`, `twoXWord`) produce the IDENTICAL 1-symbol
opening at position `0` (both evaluate to `0` there): one opened column is
consistent with two different words, so no function of `(opened, vals)`
alone could recover both correctly — the `t ≥ d` bound of
`recoverFromColumns_sound` is load-bearing, not slack. -/
theorem recoverFromColumns_teeth :
    ∃ u v : Fin 4 → ZMod 5, u ∈ reedSolomonCode dom₅ 2 ∧ v ∈ reedSolomonCode dom₅ 2 ∧
      u ≠ v ∧ (fun j : Fin 1 => u (opened₁ j)) = fun j => v (opened₁ j) :=
  ⟨xWord, twoXWord, xWord_mem, twoXWord_mem, xWord_ne_twoXWord, by
    funext j; fin_cases j; decide⟩

/-- The def is HONEST about the failure, not silently wrong: outside the
`d ≤ t` regime it is the junk `0`, not a plausible-looking guess — `0` is
neither `xWord` nor `twoXWord`, so nothing downstream could mistake it for
a recovered word. -/
theorem recoverFromColumns_junk_outside_regime :
    recoverFromColumns dom₅ 2 opened₁ (fun j => xWord (opened₁ j)) = 0 := by
  unfold recoverFromColumns
  rw [dif_neg (by decide : ¬ (2 ≤ 1))]

end ErasureExample

/-! ## Residual — prose, not a stub

**[ERASURE-list]** — beyond unique decoding (`t < d`, or a word merely
δ-close to the code rather than genuinely IN it), the opened symbols may sit
in the agreement sets of SEVERAL codewords: `recoverFromColumns_teeth`
exhibits exactly this ambiguity at `t = d − 1`. Picking out the single
intended codeword in that regime is the Johnson-list-decoding machinery:
`Selvage/CorrelatedAgreement.lean`'s mutual correlated agreement (PROVED at the
unique-decoding radius, `Selvage/ReedSolomon.lean` Corollary 4.11) plus the
list-enumeration wiring `Selvage/OutOfDomain.lean` flags as
`[OOD-pin-proximity]`. This file's theorems never invoke that machinery as a
hypothesis — `committed_word_recovered` gets its "genuine codeword" premise
for free from `BindingCommitment` binding (the prover's committed word IS in
the code by the accumulator's own claim, not merely close to it), not from
an assumed proximity bound, so nothing here is priced on an unproved regime.

## Ledger

* `recoverFromColumns` — the erasure-decoder: interpolate `d` of the `t`
  opened columns, evaluate on the whole domain; junk `0` outside `d ≤ t`.
* `recoverFromColumns_mem` — always a genuine low-degree codeword.
* `recoverFromColumns_sound` — **THE theorem**: `t ≥ d` distinct opened
  columns of a genuine codeword recover it EXACTLY (full word equality),
  via `Selvage/ZKHiding.lean`'s `open_determines` (root-counting injectivity) —
  REUSED, not re-derived.
* `committed_word_recovered` — `[ACC-extract-bind]`(b) closed: composes
  `BindingCommitment` position-binding with `recoverFromColumns_sound`.
* Keystones — satisfiable (`xWord_recovered`, `xWord_recovered_unopened`,
  `committed_recovered_fires`), teeth (`recoverFromColumns_teeth`,
  `recoverFromColumns_junk_outside_regime`), premise inhabitation
  (`opened₂_inj`: distinct positions at `t = d`).
* Residual — `[ERASURE-list]` (prose above); rides
  `Selvage/CorrelatedAgreement.lean` + `Selvage/OutOfDomain.lean`'s
  `[OOD-pin-proximity]`, never assumed here. -/

end Minidregg.Selvage
