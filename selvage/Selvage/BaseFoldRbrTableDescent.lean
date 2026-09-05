/-
# Selvage.BaseFoldRbrTableDescent — the `[ERASURE-list]` lift, resolved

`Selvage/BaseFoldRbrTable.lean` lands the table-witness leg with an extractor
that erasure-decodes the last message's `t` opened columns, valid in the
unique-decoding regime `2^m ≤ t`.  At the deployed point `t ≪ 2^m`, so that
extractor does not run, and its module header names the missing piece as
`[ERASURE-list]`: *recover the table from `t < 2^m` verified columns together
with the RS-descent fold roots and an accepting descent, by the inverse fold*.

This file resolves that obligation in three parts, each with its ATLAS fields.

**1. The inverse fold — what is and is not determined.**  The two fold
components are a bijective re-coordinatization of the level word:
`wordOfComponents D E O` is the inverse of `f ↦ (foldEven f, foldOdd f)`
(`componentsEquiv`), and `fold α` is the projection `E + α·O`
(`fold_wordOfComponents`).  Two DISTINCT challenges therefore determine the
sibling pair (`pair_of_two_folds`, the inverse-fold identity that IS true);
ONE challenge does not: `fold · α` has the nonzero kernel
`wordOfComponents (−α·O) O` (`fold_not_injective`, on EVERY folding domain).
So no function of the round-`(i+1)` word and the round-`i` challenge returns
the round-`i` word — the inverse-fold extractor of the obligation's wording
cannot exist, and the refutation is general, not an F₅ accident.

**2. What the deployed openings DO buy: a factor of two.**  The deployed
verifier opens, per query `k` in the folded domain, the SIBLING PAIR
`(sec k, neg (sec k))` of the top word (`OpenedFriQuery`, CITED).  Those are
`TableMsg`-shaped columns at the doubled query map `pairQuery`; the landed
extractor runs on them at `2^m ≤ 2t` (`descentExtract`,
`descentExtract_committed`, `descentExtract_of_openedFriQuery`).  This is the
honest content of "`t < 2^m` columns plus the descent": one query buys two
symbols, never more — `descent_public_view_teeth_f5` exhibits, at `m = 2` and
`t = 1`, two DISTINCT tables whose BaseFold words agree on the opened sibling
pair AND fold to the SAME level-1 word (hence agree at every later round and
at the terminal), and `no_public_view_extractor_f5` concludes that no function
of the opened data can return both.  Fold roots are commitments, opaque to a
public-view extractor; they bind, they do not reveal.

**3. The all-`t` instance — the table enters through the target witness.**
WARP's Def 4.2 extractor maps a knowledge-state witness for the LONGER
transcript to one for the shorter (`RbrKnowledgeSoundness`, CITED), and
Construction B.5 seeds the chain with the prover's own target-relation
candidate `w'` (`srExtract`, CITED).  For `basefoldTableReduction` the target
relation `R'` pins `w'` to the committed table (`out.rt = S.commit (basefoldWord
dom tbl)`), and binding plus the degree window make that table unique
(`basefoldWord_injective`, CITED).  The identity extractor is therefore
sound at the scalar leg's `2/|F|` for EVERY `t ≥ 0`
(`basefoldTableRbrAllQueries`), with no erasure regime at all; its FS
compilation `basefoldTable_fs_sound_allQueries` / `basefoldTable_fs_holds_allQueries`
holds at `(t + m) · 2/|F|` for every query count.  Read the content exactly:
the FS event REQUIRES the adversary's candidate to satisfy `R'`, so the
theorem is knowledge soundness RELATIVE to the commitment being opened to a
table — the standard modular decomposition (commitment extractability ⊗
reduction knowledge soundness).  At BCS resolution the table comes out of the
random-oracle query log, `[COMMIT-CR]`'s realizer, not out of `t` columns.

**The descent leg, where it actually lives.**  What the descent buys is NOT a
round bound: it is the theorem that the DEPLOYED verifier's acceptance implies
the target witness exists.  `basefoldCommittedIor_coherent_exact_sound` (CITED)
proves exactly that at exact-membership resolution; `basefoldExactClaim_iff_holds`
bridges its `BaseFoldExactClaim` to the table leg's `MleEvalClaim.Holds`, so
both legs now meet at ONE claim object (`basefoldCommittedIor_no_witness_sound`).
The per-round event it excludes is NAMED here: `DescentMiss` — some committed
fold transition is inconsistent, yet every sampled opening passes — inhabited
on F₅ (`descentMiss_inhabited_f5`: the level-1 word deviates only at the
unqueried position), refuted by a query at the deviation (`descentMiss_teeth_f5`),
and bounded by `friAdaptive_coherent_query_miss` (CITED) at `(1 − τ)^q`
(`descentMiss_coherent_le`).  `fold_check_teeth_f5` is the brief's falsifier:
a transcript that passes the sumcheck, the terminal code check and the braided
terminal equation, and is refused ONLY by the round-0 fold check.

**Scope on the label — what remains and its exact name.**  Every bound here is
priced at the quantization floor `τ = 1/|ι_{j+1}|` (`(1 − τ)^q ≈ 1` at
`2^16`-row traces) or at exact membership.  The deployed price `(1 − δ)^q` at
macroscopic `δ` is `[PROX-fold-distance]`'s macroscopic regime: the carrier is
`FoldDistancePreserving` / `FoldDistanceTransition` (CITED), consumed by
`friAdaptive_coherent_sampled_sound` (CITED); its proved realizers are
sub-quantization (`foldDistancePreserving_of_lt_inv_card`, `b = 1`) and
half-threshold (`foldDistanceTransition_halfThreshold`, radius halves per
round); the macroscopic realizer `foldDistancePreserving_of_isProximityGenerator`
consumes the standing hypothesis `IsProximityGenerator (affineGenerator F)
(reedSolomonCode dom d) B err` — WHIR Thm 4.8 / BCIKS 2020/654 — which this
tree names and never assumes.  Nothing in this file is priced on it.

**ATLAS fields (law 2), over the landed F₅ tower (`ProximityExample.ldtTower`,
`BaseFoldExample.table`, the ideal commitment):**

* satisfiable — `descentExtract_recovers_F5` (`m = 1`, `t = 1 < 2 = 2^m`: the
  extractor returns `table` from ONE query's sibling pair);
  `rbrAllQueriesF5_state_alive` (the all-`t` instance's state is alive at
  `t = 1` with the honest table); `descentMiss_inhabited_f5`;
  `fold_not_injective_f5` (`(3, 4, 0, 1)` folds to `0` at challenge `3`);
* falsifier — `descent_public_view_teeth_f5` / `no_public_view_extractor_f5`
  (`m = 2`, `t = 1`); `fold_check_teeth_f5`; `descentMiss_teeth_f5`;
* premise inhabitation — `k₁_inj`, the regime `2^1 ≤ 1 + 1`, the window
  `2^1 ≤ 4`, `rbrAllQueriesF5_err = 2/5`, `tableFs_sound_allQueries_f5`
  at `(t + 1) · 2/5`.
-/
import Selvage.BaseFoldRbrTable
import Selvage.BaseFoldCommittedIor
import Selvage.HalfThresholdFriCoherent

namespace Minidregg.Selvage

open Polynomial

variable {F : Type} [Field F]

/-! ## 1. The inverse fold: a bijective re-coordinatization, projected -/

section InverseFold

variable {ι κ : Type} {dom : ι ↪ F} {domSq : κ ↪ F} (D : FoldingData F dom domSq)

/-- The level word rebuilt from even/odd components: `f i = E (sq i) + x_i · O (sq i)`.
One formula serves both members of every sibling pair, because `dom (neg i) = −dom i`. -/
def wordOfComponents (E O : κ → F) : ι → F :=
  fun i => E (D.sq i) + dom i * O (D.sq i)

theorem foldEven_wordOfComponents (E O : κ → F) (k : κ) :
    foldEven D (wordOfComponents D E O) k = E k := by
  unfold foldEven wordOfComponents
  rw [D.sq_neg, D.sq_sec, D.dom_neg]
  have h2 := D.two_ne
  field_simp
  ring

theorem foldOdd_wordOfComponents (E O : κ → F) (k : κ) :
    foldOdd D (wordOfComponents D E O) k = O k := by
  unfold foldOdd wordOfComponents
  rw [D.sq_neg, D.sq_sec, D.dom_neg]
  have h2 := D.two_ne
  have hx := D.dom_ne_zero (D.sec k)
  field_simp
  ring

/-- The components determine the word: `wordOfComponents` inverts
`f ↦ (foldEven f, foldOdd f)` (`foldEven_add_mul_foldOdd`, CITED). -/
theorem wordOfComponents_foldEven_foldOdd (f : ι → F) :
    wordOfComponents D (foldEven D f) (foldOdd D f) = f :=
  funext fun i => foldEven_add_mul_foldOdd D f i

/-- ⭐ **The inverse fold, as a bijection.**  A level word IS its pair of fold
components; nothing is lost in either direction. -/
def componentsEquiv : (ι → F) ≃ (κ → F) × (κ → F) where
  toFun f := (foldEven D f, foldOdd D f)
  invFun p := wordOfComponents D p.1 p.2
  left_inv f := wordOfComponents_foldEven_foldOdd D f
  right_inv p := Prod.ext (funext fun k => foldEven_wordOfComponents D p.1 p.2 k)
    (funext fun k => foldOdd_wordOfComponents D p.1 p.2 k)

/-- The fold at `α` reads ONE affine combination of the components. -/
theorem fold_wordOfComponents (E O : κ → F) (α : F) (k : κ) :
    fold D (wordOfComponents D E O) α k = E k + α * O k := by
  rw [fold, foldEven_wordOfComponents, foldOdd_wordOfComponents]

/-- The sibling pair, read off the components. -/
theorem pair_of_components (f : ι → F) (k : κ) :
    f (D.sec k) = foldEven D f k + dom (D.sec k) * foldOdd D f k ∧
    f (D.neg (D.sec k)) = foldEven D f k - dom (D.sec k) * foldOdd D f k := by
  constructor
  · have h := foldEven_add_mul_foldOdd D f (D.sec k)
    rw [D.sq_sec] at h
    exact h.symm
  · have h := foldEven_add_mul_foldOdd D f (D.neg (D.sec k))
    rw [D.sq_neg, D.sq_sec, D.dom_neg, neg_mul, ← sub_eq_add_neg] at h
    exact h.symm

/-- ⭐ **The inverse-fold identity that IS true: two distinct challenges determine
the sibling pair.**  Two words with the same fold at `α` and at `β ≠ α` agree at
`sec k` and at `neg (sec k)`. -/
theorem pair_of_two_folds (f g : ι → F) {α β : F} (hαβ : α ≠ β) (k : κ)
    (hα : fold D f α k = fold D g α k) (hβ : fold D f β k = fold D g β k) :
    f (D.sec k) = g (D.sec k) ∧ f (D.neg (D.sec k)) = g (D.neg (D.sec k)) := by
  have hsub : α - β ≠ 0 := sub_ne_zero.mpr hαβ
  have hO : foldOdd D f k = foldOdd D g k := by
    have h1 : (α - β) * foldOdd D f k = (α - β) * foldOdd D g k := by
      have := congrArg₂ (· - ·) hα hβ
      simp only [fold] at this
      linear_combination this
    exact mul_left_cancel₀ hsub h1
  have hE : foldEven D f k = foldEven D g k := by
    simp only [fold] at hα
    linear_combination hα - α * hO
  obtain ⟨hf1, hf2⟩ := pair_of_components D f k
  obtain ⟨hg1, hg2⟩ := pair_of_components D g k
  rw [hf1, hf2, hg1, hg2, hO, hE]
  exact ⟨rfl, rfl⟩

/-- The kernel of the one-challenge fold: `E = −α·O` folds to zero at `α`. -/
theorem fold_kernel (O : κ → F) (α : F) :
    fold D (wordOfComponents D (fun k => -α * O k) O) α = 0 := by
  funext k
  rw [fold_wordOfComponents, Pi.zero_apply]
  ring

/-- ⭐ **Teeth — ONE challenge does NOT determine the word.**  On every folding
domain with a nonempty folded level, some NONZERO word folds to zero at `α`:
the round-`(i+1)` word and the round-`i` challenge do not determine the
round-`i` word, so no inverse-fold extractor exists.  General, not F₅. -/
theorem fold_not_injective [Nonempty κ] (α : F) :
    ∃ f : ι → F, f ≠ 0 ∧ fold D f α = 0 := by
  refine ⟨wordOfComponents D (fun k => -α * 1) (fun _ => 1), ?_, fold_kernel D _ α⟩
  intro h0
  have h := foldOdd_wordOfComponents D (fun k => -α * 1) (fun _ => (1 : F))
    (Classical.arbitrary κ)
  rw [h0] at h
  simp [foldOdd] at h

end InverseFold

/-! ## 2. The sibling-pair query map: what the deployed openings buy -/

section PairQuery

variable {Root Op ι : Type} [Fintype F] [DecidableEq F] [Fintype ι] {m t : ℕ}
variable {κ : Type} {dom : ι ↪ F} {domSq : κ ↪ F} (D : FoldingData F dom domSq)

/-- The deployed verifier's round-0 positions: for the `t` queries `k a` in the
folded domain, the sibling pairs `sec (k a)` (first block) and `neg (sec (k a))`
(second block) — `2t` positions of the top word. -/
def pairQuery (k : Fin t → κ) : Fin (t + t) → ι :=
  fun j => if h : (j : ℕ) < t then D.sec (k ⟨j, h⟩)
    else D.neg (D.sec (k ⟨j - t, by omega⟩))

/-- The opened symbols of one query's fibre, laid out as columns at `pairQuery`. -/
def pairCols {OpBig OpSmall : Type} (o : Fin t → FriQueryOpening F OpBig OpSmall) :
    Fin (t + t) → F :=
  fun j => if h : (j : ℕ) < t then (o ⟨j, h⟩).left else (o ⟨j - t, by omega⟩).right

/-- The opening proofs, laid out as `pairCols`. -/
def pairOps {OpBig OpSmall : Type} (o : Fin t → FriQueryOpening F OpBig OpSmall) :
    Fin (t + t) → OpBig :=
  fun j => if h : (j : ℕ) < t then (o ⟨j, h⟩).leftPath else (o ⟨j - t, by omega⟩).rightPath

omit [Fintype F] [DecidableEq F] [Fintype ι] in
/-- A section value is never the negation of a section value. -/
theorem sec_ne_neg_sec (k k' : κ) : D.sec k ≠ D.neg (D.sec k') := by
  intro h
  have hk : k = k' := by
    have := congrArg D.sq h
    rwa [D.sq_sec, D.sq_neg, D.sq_sec] at this
  subst hk
  exact D.neg_ne (D.sec k) h.symm

omit [Fintype F] [DecidableEq F] [Fintype ι] in
theorem sec_injective : Function.Injective D.sec := fun a b h => by
  have := congrArg D.sq h
  rwa [D.sq_sec, D.sq_sec] at this

omit [Fintype F] [DecidableEq F] [Fintype ι] in
/-- **Premise inhabitation of the erasure regime**: distinct queries give `2t`
distinct positions under the domain embedding. -/
theorem pairQuery_injective {k : Fin t → κ} (hk : Function.Injective k) :
    Function.Injective (dom ∘ pairQuery D k) := by
  intro i j h
  have h' : pairQuery D k i = pairQuery D k j := dom.injective h
  unfold pairQuery at h'
  by_cases hi : (i : ℕ) < t <;> by_cases hj : (j : ℕ) < t
  · rw [dif_pos hi, dif_pos hj] at h'
    have := hk (sec_injective D h')
    exact Fin.ext (by simpa using congrArg Fin.val this)
  · rw [dif_pos hi, dif_neg hj] at h'
    exact absurd h' (sec_ne_neg_sec D _ _)
  · rw [dif_neg hi, dif_pos hj] at h'
    exact absurd h'.symm (sec_ne_neg_sec D _ _)
  · rw [dif_neg hi, dif_neg hj] at h'
    have hneg : Function.Injective D.neg := fun a b hab => by
      have := congrArg D.neg hab
      rwa [D.neg_neg, D.neg_neg] at this
    have := hk (sec_injective D (hneg h'))
    have hv := congrArg Fin.val this
    simp only at hv
    exact Fin.ext (by omega)

/-- ⭐ **The descent extractor at the deployed message shape.**  Read the
`t` opened sibling pairs of the top word as `2t` columns at `pairQuery` and
erasure-decode them (`extractTable`, CITED).  Its regime is `2^m ≤ 2t`: one
query buys exactly two symbols. -/
noncomputable def descentExtract {OpBig OpSmall : Type} (dom : ι ↪ F) (m : ℕ)
    (k : Fin t → κ) (o : Fin t → FriQueryOpening F OpBig OpSmall) : (Fin m → Bool) → F :=
  extractTable dom m (pairQuery D k) (pairCols o)

omit [Fintype F] [DecidableEq F] [Fintype ι] in
/-- The sibling-pair openings, as a `TableMsg` whose columns open at `pairQuery`. -/
theorem pairMsg_opens {OpSmall : Type} (S : OpeningScheme Root F ι Op) {k : Fin t → κ}
    {rt : Root} {o : Fin t → FriQueryOpening F Op OpSmall}
    (hleft : ∀ a, S.verifyOpen rt (D.sec (k a)) (o a).left (o a).leftPath)
    (hright : ∀ a, S.verifyOpen rt (D.neg (D.sec (k a))) (o a).right (o a).rightPath) :
    (⟨0, pairCols o, pairOps o⟩ : TableMsg F Op (t + t)).Opens S (pairQuery D k) rt := by
  intro j
  show S.verifyOpen rt (pairQuery D k j) (pairCols o j) (pairOps o j)
  unfold pairQuery pairCols pairOps
  by_cases h : (j : ℕ) < t
  · rw [dif_pos h, dif_pos h, dif_pos h]
    exact hleft _
  · rw [dif_neg h, dif_neg h, dif_neg h]
    exact hright _

omit [Fintype F] in
/-- ⭐ **The descent extractor recovers the committed table, through binding.**
Verified sibling-pair openings against a binding commitment of the BaseFold
word, at `2^m ≤ 2t` distinct queries, return the table exactly
(`extractTable_committed`, CITED, at the doubled query map). -/
theorem descentExtract_committed {OpSmall : Type} (S : BindingCommitment Root F ι Op)
    (hcard : 2 ^ m ≤ Fintype.card ι) (hdt : 2 ^ m ≤ t + t) {k : Fin t → κ}
    (hk : Function.Injective k) {rt : Root} {tbl : (Fin m → Bool) → F}
    (hrt : rt = S.commit (basefoldWord dom tbl)) {o : Fin t → FriQueryOpening F Op OpSmall}
    (hleft : ∀ a, S.verifyOpen rt (D.sec (k a)) (o a).left (o a).leftPath)
    (hright : ∀ a, S.verifyOpen rt (D.neg (D.sec (k a))) (o a).right (o a).rightPath) :
    descentExtract D dom m k o = tbl :=
  extractTable_committed S dom hcard hdt (pairQuery_injective D hk) hrt
    (π := ⟨0, pairCols o, pairOps o⟩) (pairMsg_opens D S.toOpeningScheme hleft hright)

omit [Fintype F] in
/-- The same, from the deployed verifier's own round-0 predicate
(`OpenedFriQuery`, CITED): its first two conjuncts ARE the pair openings. -/
theorem descentExtract_of_openedFriQuery {RootSmall OpSmall : Type}
    (S : BindingCommitment Root F ι Op) (Ssmall : OpeningScheme RootSmall F κ OpSmall)
    (hcard : 2 ^ m ≤ Fintype.card ι) (hdt : 2 ^ m ≤ t + t) {k : Fin t → κ}
    (hk : Function.Injective k) {rt : Root} {rt' : RootSmall} {tbl : (Fin m → Bool) → F}
    (hrt : rt = S.commit (basefoldWord dom tbl)) {α : F}
    {o : Fin t → FriQueryOpening F Op OpSmall}
    (hopen : ∀ a, OpenedFriQuery S.toOpeningScheme Ssmall D rt rt' α (k a) (o a)) :
    descentExtract D dom m k o = tbl :=
  descentExtract_committed D S hcard hdt hk hrt (fun a => (hopen a).1) (fun a => (hopen a).2.1)

end PairQuery

/-! ## 3. The full-word decoder — the IOR-resolution extractor -/

section FullWord

variable {ι : Type} [Fintype F] [DecidableEq F] [Fintype ι] {m : ℕ}

/-- The table of a committed word in the BaseFold window: read the word's
polynomial (`codewordPoly`, CITED) and invert the Möbius packing
(`tableOfPoly`, CITED).  This is what `extractTable` applies to the
erasure-recovered word, and what an extractor holding the WHOLE committed
word — the IOR oracle, or the random-oracle log at BCS resolution — applies
directly, at every `t`. -/
noncomputable def descentExtractWord (dom : ι ↪ F) (m : ℕ) (w : ι → F) : (Fin m → Bool) → F :=
  tableOfPoly m (codewordPoly dom (2 ^ m) w)

omit [Fintype F] [DecidableEq F] [Fintype ι] in
theorem extractTable_eq_descentExtractWord {t : ℕ} (dom : ι ↪ F) (q : Fin t → ι)
    (cols : Fin t → F) :
    extractTable dom m q cols = descentExtractWord dom m (recoverFromColumns dom (2 ^ m) q cols) :=
  rfl

omit [Fintype F] [DecidableEq F] [Fintype ι] in
/-- **The full-word decoder is exact on the code**: every codeword of the
window is the BaseFold word of the table read off it — the constructive form
of `exists_basefoldTable_of_mem_code` (CITED). -/
theorem basefoldWord_descentExtractWord (dom : ι ↪ F) {w : ι → F}
    (hw : w ∈ reedSolomonCode dom (2 ^ m)) :
    basefoldWord dom (descentExtractWord dom m w) = w := by
  funext i
  unfold basefoldWord descentExtractWord
  rw [booleanMobiusPolynomial_tableOfPoly m _ (codewordPoly_degree_lt dom (2 ^ m) w),
    ← codewordPoly_eval dom (2 ^ m) hw i]

omit [Fintype F] in
/-- Round trip on honest words, inside the degree window. -/
theorem descentExtractWord_basefoldWord (dom : ι ↪ F) (hcard : 2 ^ m ≤ Fintype.card ι)
    (tbl : (Fin m → Bool) → F) :
    descentExtractWord dom m (basefoldWord dom tbl) = tbl := by
  unfold descentExtractWord
  rw [codewordPoly_eq_of_witness (f := basefoldWord dom tbl) dom hcard
      (degree_booleanMobiusPolynomial_lt m tbl) (fun _ => rfl),
    tableOfPoly_booleanMobiusPolynomial]

end FullWord

/-! ## 4. The all-`t` instance: the table enters through the target witness -/

section AllQueries

variable {Root Op ι : Type} [Fintype F] [DecidableEq F] [Fintype ι] {m t : ℕ}

/-- ⭐ **The Def-4.2 instance for the table-witness leg at EVERY query count.**
`kstate` is the landed committed-column-consistent state (CITED); `extract` is
the identity — the knowledge-state witness of the extended transcript is
already the committed table, pinned by binding and the degree window
(`basefoldWord_injective`, CITED); `err = 2/|F|`, the scalar leg's price.
`extract_sound` PROVED: the alive witness at the extension is the unique table
`rt` commits, and the round event is CONTAINED in the scalar leg's event at
that table (`basefoldSumcheckRbr`, CITED).  No erasure regime: `hdt`, `hq`
are gone; only the window `hcard` remains.

Read the content exactly: the table is HANDED BACK, not computed from the
public view.  `basefoldTableRbr` (CITED) additionally computes it from `t ≥ 2^m`
columns; `descentExtract` from `2t ≥ 2^m` sibling-pair symbols; beyond that,
`no_public_view_extractor_f5` shows no public-view computation exists, and the
table's provenance is the commitment's extractability (`[COMMIT-CR]`). -/
noncomputable def basefoldTableRbrAllQueries (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι) :
    RbrKnowledgeSoundness (basefoldTableReduction hm S dom q) where
  kstate := basefoldTableKState hm S dom q
  extract := fun _st _tr w => w
  err := fun _i _st _δ => (2 : ℝ) / Fintype.card F
  extractTime := fun _ => 0
  extract_sound := by
    classical
    intro δ hδ st i rs hlen π
    by_cases hex : ∃ tbl : (Fin m → Bool) → F, st.x.rt = S.commit (basefoldWord dom tbl)
    · obtain ⟨tbl, hrt⟩ := hex
      have hsc := (basefoldSumcheckRbr hm tbl st.x.pt).extract_sound
        δ hδ ⟨(), st.x.val, fun _ => ()⟩ i (tableRounds rs)
        (by rw [tableRounds_length, hlen]) π.poly
      rw [basefoldSumcheckRbr_err] at hsc
      refine le_trans (uniformProb_mono ?_) hsc
      intro ρ hev
      obtain ⟨w, hdead, halive⟩ := hev
      rw [basefoldTableKState_state_eq, decide_eq_true_eq] at halive
      rw [basefoldTableKState_state_eq, decide_eq_false_iff_not] at hdead
      obtain ⟨hcols, hrt', hsum⟩ := halive
      have hw : w = tbl := basefoldWord_injective S dom hcard (hrt'.symm.trans hrt)
      subst hw
      refine ⟨(), ?_, ?_⟩
      · rw [basefoldSumcheckRbr_state_eq, decide_eq_false_iff_not]
        intro hsc'
        exact hdead ⟨fun e he => hcols e (List.mem_append_left _ he), hrt', hsc'⟩
      · rw [basefoldSumcheckRbr_state_eq, decide_eq_true_eq]
        rw [tableRounds_append] at hsum
        exact hsum
    · refine le_trans (le_of_eq (uniformProb_false ?_)) (by positivity)
      rintro ρ ⟨w, -, halive⟩
      rw [basefoldTableKState_state_eq, decide_eq_true_eq] at halive
      exact hex ⟨w, halive.2.1⟩

/-- The all-`t` instance pays the scalar leg's two field roots per round. -/
@[simp] theorem basefoldTableRbrAllQueries_err (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι) (i : Fin m)
    (st : Stmt (basefoldTableReduction hm S dom q)) (δ : ℝ) :
    (basefoldTableRbrAllQueries hm S dom q hcard).err i st δ = (2 : ℝ) / Fintype.card F := rfl

/-- **The extractor is pinned**: it returns the witness it is handed. -/
theorem basefoldTableRbrAllQueries_extract_eq (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι)
    (st : Stmt (basefoldTableReduction hm S dom q)) (tr : Transcript (TableMsg F Op t) F)
    (w : (Fin m → Bool) → F) :
    (basefoldTableRbrAllQueries hm S dom q hcard).extract st tr w = w := rfl

omit [Fintype F] [DecidableEq F] [Fintype ι] in
/-- Construction B.5 through an identity extractor returns its seed at every level. -/
theorem wAt_of_extract_id {r : Reduction} (rbr : RbrKnowledgeSoundness r)
    (hid : ∀ st tr w, rbr.extract st tr w = w) (st : Stmt r)
    (rounds : List (r.PMsg × r.Chal)) (w' : r.W) :
    ∀ (n i : ℕ), rounds.length - i = n → wAt rbr st rounds w' i = w'
  | 0, i, hn => wAt_of_le rbr st rounds w' (by omega)
  | n + 1, i, hn => by
      rw [wAt_of_lt rbr st rounds w' (by omega), hid,
        wAt_of_extract_id rbr hid st rounds w' n (i + 1) (by omega)]

/-- ⭐ **The straightline FS extractor returns the prover's target candidate** —
which the FS event's `R'` clause pins to the committed table: Construction B.5
(`srExtract`, CITED) through the identity extractor is the seed `w'`. -/
theorem basefoldTableRbrAllQueries_srExtract (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι) (s : ℕ)
    (o : SrOutput (basefoldTableReduction hm S dom q) s) (ρs : Fin m → F)
    (log : List (SrMove (basefoldTableReduction hm S dom q) s × F)) :
    srExtract (basefoldTableRbrAllQueries hm S dom q hcard) s o ρs log = o.w' :=
  wAt_of_extract_id _ (fun _ _ _ => rfl) _ _ _ _ 0 rfl

/-- The target relation pins the candidate: whatever `w'` satisfies `R'` at an
output whose root commits `basefoldWord dom tbl` IS `tbl`. -/
theorem basefoldTable_target_pins (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι)
    {x' : BaseFoldTerminalClaim Root F m} {y' : Fin 1 → Unit} {w' tbl : (Fin m → Bool) → F}
    (hrt : x'.rt = S.commit (basefoldWord dom tbl))
    (hR' : (basefoldTableReduction hm S dom q).R' () x' y' w') : w' = tbl :=
  basefoldWord_injective S dom hcard (hR'.1.symm.trans hrt)

/-- ⭐ **The table-witness leg, Fiat–Shamir compiled at EVERY query count.**
`fsKeystone_proved` (CITED) applied to `basefoldTableRbrAllQueries`: a
`t'`-query ROM adversary whose output claim has no table witness and whose
FS-compiled transcript is accepted with its candidate in `R'` succeeds with
probability at most `(t' + m) · 2/|F|` — for every `t`, no erasure regime. -/
theorem basefoldTable_fs_sound_allQueries (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι) :
    FsStraightlineKnowledgeSoundness (basefoldTableReduction hm S dom q) Set.univ
      (fun _s t _δ => ((t : ℝ) + (m : ℝ)) * (2 / Fintype.card F)) :=
  fsKeystone_proved.sound _ (basefoldTableRbrAllQueries hm S dom q hcard) Set.univ
    (fun _ => (2 : ℝ) / Fintype.card F)
    (fun _ _ => by positivity)
    (fun i st _ δ _ => le_of_eq (basefoldTableRbrAllQueries_err hm S dom q hcard i st δ))

/-- The consumer-facing corollary over `MleEvalClaim.Holds`, at every query
count — `basefoldTable_fs_holds` (CITED) with `hdt`, `hq` removed. -/
theorem basefoldTable_fs_holds_allQueries (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι) (s t' : ℕ) {δ : ℝ}
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (P : SrProver (basefoldTableReduction hm S dom q) s) :
    uniformProb ((Fin t' → F) × (Fin m → F)) (fun coins =>
        let log := srTrace P coins.1
        let o := P.out (log.map Prod.snd)
        let ρs : Fin m → F := srFinalChal P coins.1 coins.2
        ¬ o.stmt.x.Holds S dom ∧
        ∃ (x' : BaseFoldTerminalClaim Root F m) (y' : Fin 1 → Unit),
          fiatShamir (basefoldTableReduction hm S dom q) s (fsOracle o ρs) o = some (x', y') ∧
          RelaxedMem (basefoldTableReduction hm S dom q).R' δ o.stmt.idx x' y' o.w')
      ≤ ((t' : ℝ) + (m : ℝ)) * (2 / Fintype.card F) := by
  obtain ⟨E, hE⟩ := basefoldTable_fs_sound_allQueries hm S dom q hcard
  refine le_trans (uniformProb_mono ?_) (hE s t' δ hδ P)
  intro coins h
  obtain ⟨hnot, hacc⟩ := h
  refine ⟨Set.mem_univ _, ?_, hacc⟩
  rintro ⟨ystar, ⟨hrt, hval⟩, -⟩
  exact hnot ⟨_, hrt, hval⟩

end AllQueries

/-! ## 5. The descent leg: acceptance implies the witness exists, and its named event -/

section DescentLeg

variable {ιL : ℕ → Type} {RootL OpL : ℕ → Type} {m : ℕ}

omit [Field F] in
/-- ⭐ **The two legs meet at one claim object.**  The full-word IOR's strict
claim `BaseFoldExactClaim` (CITED) is EXACTLY the table leg's source relation
`MleEvalClaim.Holds` (CITED) at the root committing the word — binding makes
`commit` injective, and `basefoldWord` IS the Möbius evaluation word. -/
theorem basefoldExactClaim_iff_holds [Field F]
    (S : ∀ n, BindingCommitment (RootL n) F (ιL n) (OpL n)) (T : FoldingTower F ιL m)
    (z : Fin m → F) (H : F) (word : ιL 0 → F) :
    BaseFoldExactClaim T z H word ↔
      (⟨(S 0).commit word, z, H⟩ : MleEvalClaim (RootL 0) F m).Holds (S 0) (T.dom 0) := by
  constructor
  · rintro ⟨tbl, hw, hH⟩
    exact ⟨tbl, by rw [hw]; rfl, hH.symm⟩
  · rintro ⟨tbl, hrt, hval⟩
    exact ⟨tbl, (S 0).commit_injective hrt, hval.symm⟩

/-- **The descent's named event**: some committed fold transition is
inconsistent with the challenge, yet every sampled fibre opens consistently at
the chosen queries.  This is the event the sampled verifier cannot see and the
proximity leg must price; it is NOT a round-by-round knowledge event. -/
def DescentMiss (S : ∀ n, BindingCommitment (RootL n) F (ιL n) (OpL n))
    (T : FoldingTower F ιL m) (st : FriAdaptiveTranscript S) (r : Fin m → F)
    (qCount : ℕ) (Q : FriIndependentQuerySchedule ιL m qCount) : Prop :=
  (∃ j : Fin m,
    st.wordAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt) ≠
      fold (T.data j j.isLt) (st.wordAt r j (Nat.le_of_lt j.isLt)) (r j)) ∧
  ∀ j, FriAdaptiveRoundQueriesAccept S T st r j (Q j)

section CoherentMiss

variable [Fintype F] [DecidableEq F] {ell : ℕ} {RootP OpP : ℕ → Type}
variable (SP : ∀ n, BindingCommitment (RootP n) F (PowerTwoFriLevels ell n) (OpP n))

omit [Fintype F] in
/-- ⭐ **The named event is priced by the landed query-miss theorem.**  For
coherent power-of-two query paths, `DescentMiss` has probability at most
`(1 − τ)^q` at the quantization floor `τ ≤ 1/|ι_{j+1}|`
(`friAdaptive_coherent_query_miss`, CITED; `one_div_card_le_relDist`, CITED).
The macroscopic-`δ` version of this bound is `[PROX-fold-distance]`'s
macroscopic regime — see the module header. -/
theorem descentMiss_coherent_le (T : FoldingTower F (PowerTwoFriLevels ell) m)
    (st : FriAdaptiveTranscript SP) (hmell : m ≤ ell) (r : Fin m → F) (qCount : ℕ)
    {tau : ℝ} (htau1 : tau ≤ 1)
    (htau : ∀ j : Fin m, tau ≤ 1 / (Fintype.card (PowerTwoFriLevels ell (j + 1)) : ℝ)) :
    uniformProb (Fin qCount → PowerTwoFriLevels ell 1)
      (fun seed => DescentMiss SP T st r qCount (powerTwoCoherentSchedule hmell seed))
      ≤ (1 - tau) ^ qCount := by
  classical
  have heps : (0 : ℝ) ≤ (1 - tau) ^ qCount := pow_nonneg (sub_nonneg.mpr htau1) _
  by_cases hdev : ∃ j : Fin m,
      st.wordAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt) ≠
        fold (T.data j j.isLt) (st.wordAt r j (Nat.le_of_lt j.isLt)) (r j)
  · obtain ⟨j, hj⟩ := hdev
    letI : Nonempty (PowerTwoFriLevels ell (j + 1)) := ⟨⟨0, by positivity⟩⟩
    have hfar : tau ≤ relDist
        (st.wordAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt))
        (fold (T.data j j.isLt) (st.wordAt r j (Nat.le_of_lt j.isLt)) (r j)) :=
      le_trans (htau j) (one_div_card_le_relDist hj)
    refine le_trans (uniformProb_mono fun seed hs => hs.2) ?_
    exact friAdaptive_coherent_query_miss SP T st hmell r qCount ⟨j, hfar⟩
  · refine le_trans (le_of_eq (uniformProb_false ?_)) heps
    intro seed hs
    exact hdev hs.1

/-- ⭐ **Acceptance of the deployed sampled verifier without a source witness.**
`basefoldCommittedIor_coherent_exact_sound` (CITED) restated over the table
leg's claim object: if the committed top word and claimed value do NOT form a
true `MleEvalClaim`, the sampled BaseFold verifier on `q` coherent queries
accepts with probability at most `m · 3/|F| + (1 − τ)^q`.  Together with
`basefoldTable_fs_holds_allQueries` this is the two-leg decomposition at ONE
claim: the reduction is knowledge-sound relative to the target witness at
every `t`, and the target witness exists whenever the verifier accepts, up to
this bound. -/
theorem basefoldCommittedIor_no_witness_sound
    (T : FoldingTower F (PowerTwoFriLevels ell) m)
    (st : FriAdaptiveTranscript SP) (hmell : m ≤ ell)
    (z : Fin m → F) (H : F) (word : PowerTwoFriLevels ell 0 → F)
    (prover : (ℕ → F) → ℕ → Polynomial F)
    (qCount : ℕ) {tau : ℝ} (htau1 : tau ≤ 1)
    (htau : ∀ j : Fin m, tau ≤ 1 / (Fintype.card (PowerTwoFriLevels ell (j + 1)) : ℝ))
    (hword0 : st.word 0 (fun i => i.elim0) = word)
    (hnot : ¬ (⟨(SP 0).commit word, z, H⟩ : MleEvalClaim (RootP 0) F m).Holds (SP 0) (T.dom 0))
    (hpm : PrefixMeasurable prover)
    (hdeg : ∀ (χ : ℕ → F) (i : ℕ), i < m →
      (prover χ i).degree < ((2 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb
      ((Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1))
      (fun x => BaseFoldCommittedIorAccepts SP T st z H prover qCount x.1
        (powerTwoCoherentSchedule hmell x.2))
      ≤ (m : ℝ) * (3 / Fintype.card F) + (1 - tau) ^ qCount :=
  basefoldCommittedIor_coherent_exact_sound SP T st hmell z H word prover qCount htau1 htau
    hword0 (fun h => hnot ((basefoldExactClaim_iff_holds SP T z H word).mp h)) hpm hdeg

end CoherentMiss

end DescentLeg

/-! ## 6. F₅ keystones -/

namespace BaseFoldRbrTableDescentExample

open BaseFoldExample ProximityExample MleEvalClaimExample BaseFoldRbrTableExample
  HalfThresholdFriTranscriptExample

/-! ### The inverse fold's teeth on the landed domain -/

/-- `(3, 4, 0, 1)` — the evaluations of `X − 3` on `{1, 2, 3, 4}`: a nonzero
word that folds to ZERO at challenge `3`.  One challenge does not see it. -/
def kernelWord : Fin 4 → ZMod 5 := ![3, 4, 0, 1]

theorem fold_not_injective_f5 : kernelWord ≠ 0 ∧ fold data0 kernelWord 3 = 0 := by
  constructor <;> decide

/-! ### The sibling-pair extractor at `m = 1`, `t = 1 < 2^m` -/

/-- One query, at the folded position `0` (`sec 0 = 0`, `neg (sec 0) = 3`). -/
def k₁ : Fin 1 → levels 1 := fun _ => ⟨0, by decide⟩

theorem k₁_inj : Function.Injective k₁ := fun a b _ => Subsingleton.elim a b

/-- The regime: `t = 1 < 2 = 2^1`, and the sibling pair reaches it, `2^1 ≤ 1 + 1`. -/
theorem regime_f5 : 1 < 2 ^ 1 ∧ 2 ^ 1 ≤ 1 + 1 := by decide

/-- The honest opening of the one query: the pair of the committed word and its fold. -/
noncomputable def honestOpening : Fin 1 → FriQueryOpening (ZMod 5) Unit Unit := fun a =>
  { left := basefoldWord dom0 table (data0.sec (k₁ a))
    right := basefoldWord dom0 table (data0.neg (data0.sec (k₁ a)))
    next := fold data0 (basefoldWord dom0 table) 3 (k₁ a)
    leftPath := ()
    rightPath := ()
    nextPath := () }

/-- **Satisfiable / the extractor computes at `t < 2^m`**: from ONE query's
sibling pair, verified against the root, the descent extractor returns
`table` exactly — the landed extractor needed `t = 2`. -/
theorem descentExtract_recovers_F5 : descentExtract data0 dom0 1 k₁ honestOpening = table :=
  descentExtract_committed (rt := basefoldWord dom0 table) data0 S₄ (by decide) (by decide)
    k₁_inj rfl (fun _ => rfl) (fun _ => rfl)

/-! ### The public view at `m = 2`, `t = 1` does not determine the table -/

/-- Every word on the four-point domain is a codeword of the `m = 2` window
(`reedSolomonCode_card_eq_top`, CITED): rate one. -/
theorem mem_window_f5 (w : Fin 4 → ZMod 5) : w ∈ reedSolomonCode dom0 (2 ^ 2) := by
  have h := reedSolomonCode_card_eq_top dom0
  rw [Fintype.card_fin] at h
  rw [show (2 : ℕ) ^ 2 = 4 by norm_num, h]
  exact Submodule.mem_top

/-- The spike `(0, 0, 2, 0)`: zero on the opened pair `{0, 3}`, and its fold at
challenge `2` is zero everywhere — the kernel word `(X − 2)(1 − X²)`. -/
def spike₂ : Fin 4 → ZMod 5 := ![0, 0, 2, 0]

/-- **Falsifier — two tables, one public view.**  Two DISTINCT `m = 2` tables
whose BaseFold words agree on the one opened sibling pair AND fold to the SAME
level-1 word at the round-0 challenge: every later round's openings and the
terminal coincide.  `t = 1 < 2 = 2^(m−1)`: the sibling-pair regime is
load-bearing. -/
theorem descent_public_view_teeth_f5 :
    ∃ tbl₁ tbl₂ : (Fin 2 → Bool) → ZMod 5, tbl₁ ≠ tbl₂ ∧
      (∀ j, basefoldWord dom0 tbl₁ (pairQuery data0 k₁ j)
        = basefoldWord dom0 tbl₂ (pairQuery data0 k₁ j)) ∧
      fold data0 (basefoldWord dom0 tbl₁) 2 = fold data0 (basefoldWord dom0 tbl₂) 2 := by
  have h₁ := basefoldWord_descentExtractWord (m := 2) dom0 (mem_window_f5 0)
  have h₂ := basefoldWord_descentExtractWord (m := 2) dom0 (mem_window_f5 spike₂)
  refine ⟨descentExtractWord dom0 2 0, descentExtractWord dom0 2 spike₂, ?_, ?_, ?_⟩
  · intro h
    have := congrArg (basefoldWord dom0) h
    rw [h₁, h₂] at this
    exact absurd this (by decide)
  · rw [h₁, h₂]
    decide
  · rw [h₁, h₂]
    decide

/-- ⭐ **No public-view extractor exists at `m = 2`, `t = 1`.**  No function of
the opened sibling pair and the ENTIRE level-1 word (a fortiori of the level-1
openings and the terminal) returns the table for every table. -/
theorem no_public_view_extractor_f5 :
    ¬ ∃ E : (Fin (1 + 1) → ZMod 5) → (levels 1 → ZMod 5) → ((Fin 2 → Bool) → ZMod 5),
      ∀ tbl : (Fin 2 → Bool) → ZMod 5,
        E (fun j => basefoldWord dom0 tbl (pairQuery data0 k₁ j))
          (fold data0 (basefoldWord dom0 tbl) 2) = tbl := by
  rintro ⟨E, hE⟩
  obtain ⟨tbl₁, tbl₂, hne, hpair, hfold⟩ := descent_public_view_teeth_f5
  have hsame := congrArg₂ E (funext hpair) hfold
  exact hne ((hE tbl₁).symm.trans (hsame.trans (hE tbl₂)))

/-! ### The fold check has teeth; the named event is inhabited and refuted -/

/-- The honest fold of the committed word at challenge `3` is the constant `4`
(`mobius_descent_terminal`, CITED, read one level down). -/
theorem fold_honest_f5 (k : levels 1) : fold data0 (basefoldWord dom0 table) 3 k = 4 :=
  mobius_descent_terminal k

/-- The adversarial level-1 word `(4, 0)`: agrees with the honest fold at
position `0`, deviates at position `1`. -/
def missWord1 : levels 1 → ZMod 5 := ![4, 0]

/-- The adversarial strategy: the honest top word, then `(4, 0)`. -/
noncomputable def missWord : ∀ n, levels n → ZMod 5
  | 0 => basefoldWord dom0 table
  | 1 => missWord1
  | _ + 2 => Fin.elim0

noncomputable def missTranscript : FriAdaptiveTranscript idealSchemes where
  word := fun n _ => missWord n
  root := fun n _ => missWord n
  root_eq_commit := fun _ _ => rfl

/-- The one-query schedule at folded position `0`. -/
def qZero : FriIndependentQuerySchedule levels 1 1 := fun j _ =>
  ⟨0, by rw [Fin.fin_one_eq_zero j]; decide⟩

/-- The one-query schedule at folded position `1`. -/
def qOne : FriIndependentQuerySchedule levels 1 1 := fun j _ =>
  ⟨1, by rw [Fin.fin_one_eq_zero j]; decide⟩

/-- The committed transition is inconsistent: `(4, 0) ≠ (4, 4)`. -/
theorem missWord1_ne_fold : missWord1 ≠ fold data0 (basefoldWord dom0 table) 3 := by
  intro h
  have := congrFun h ⟨1, by decide⟩
  rw [fold_honest_f5] at this
  exact absurd this (by decide)

/-- **The named event is inhabited**: the inconsistent transition passes the
one sampled fibre at position `0`, where the words agree. -/
theorem descentMiss_inhabited_f5 :
    DescentMiss idealSchemes ldtTower missTranscript ![3] 1 qZero := by
  refine ⟨⟨0, ?_⟩, ?_⟩
  · exact missWord1_ne_fold
  · intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    refine ⟨fun _ => {
        left := basefoldWord dom0 table (data0.sec ⟨0, by decide⟩),
        right := basefoldWord dom0 table (data0.neg (data0.sec ⟨0, by decide⟩)),
        next := 4,
        leftPath := (),
        rightPath := (),
        nextPath := () }, ?_⟩
    intro a
    refine ⟨rfl, rfl, rfl, ?_⟩
    have h := fold_honest_f5 ⟨0, by decide⟩
    rw [fold, foldEven, foldOdd] at h
    exact h.symm

/-- **Teeth**: the same transition is REFUSED by a query at the deviation. -/
theorem descentMiss_teeth_f5 :
    ¬ FriAdaptiveRoundQueriesAccept idealSchemes ldtTower missTranscript ![3] 0 (qOne 0) := by
  intro hacc
  have h := friAdaptiveRoundQueries_pins idealSchemes ldtTower missTranscript ![3] 0 hacc 0
  change missWord1 ⟨1, by decide⟩ = fold data0 (basefoldWord dom0 table) 3 ⟨1, by decide⟩ at h
  rw [fold_honest_f5] at h
  exact absurd h (by decide)

/-- The adversarial sumcheck message `3 + 3X²`: Boolean sum `4` (the honest
claim) and value `0` at the challenge `3` — matched to a zero terminal. -/
noncomputable def badPoly : Polynomial (ZMod 5) := C 3 + C 3 * X ^ 2

theorem badPoly_eval (x : ZMod 5) : badPoly.eval x = 3 + 3 * x ^ 2 := by
  simp [badPoly]

theorem badPoly_degree : badPoly.degree < ((2 + 1 : ℕ) : WithBot ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  have hn3 : 3 ≤ n := by simpa using hn
  simp [badPoly, Polynomial.coeff_X_pow, Polynomial.coeff_C, show n ≠ 0 by omega,
    show n ≠ 2 by omega]

noncomputable def badProver : (ℕ → ZMod 5) → ℕ → Polynomial (ZMod 5) := fun _ _ => badPoly

/-- The adversarial strategy behind the brief's falsifier: the honest top word,
then the constant ZERO word. -/
noncomputable def zeroWord : ∀ n, levels n → ZMod 5
  | 0 => basefoldWord dom0 table
  | 1 => 0
  | _ + 2 => Fin.elim0

noncomputable def zeroTranscript : FriAdaptiveTranscript idealSchemes where
  word := fun n _ => zeroWord n
  root := fun n _ => zeroWord n
  root_eq_commit := fun _ _ => rfl

/-- ⭐ **Falsifier — the fold check alone refuses.**  At the honest claim `4`
and challenge `3`, the adversarial transcript passes the degree check, the
Boolean-sum check, the terminal code check (`0` is constant) and the braided
terminal equation (`0 = 0 · eq`), and is refused ONLY by the round-0 fold
check: no opening data can authenticate `next = 0` against `fold = 4`. -/
theorem fold_check_teeth_f5 :
    (∀ i, i < 1 → (badProver (chalOf ![3]) i).degree < ((2 + 1 : ℕ) : WithBot ℕ)) ∧
    (∀ i, i < 1 → (badProver (chalOf ![3]) i).eval 0 + (badProver (chalOf ![3]) i).eval 1 =
      scChain (mle table ![3]) (badProver (chalOf ![3])) (chalOf ![3]) i) ∧
    zeroTranscript.wordAt ![3] 1 le_rfl ∈
      reedSolomonCode (ldtTower.dom 1) (basefoldDegSched 1 1) ∧
    (∀ k : levels 1, scChain (mle table ![3]) (badProver (chalOf ![3])) (chalOf ![3]) 1 =
      zeroTranscript.wordAt ![3] 1 le_rfl k * eqMle ![3] ![3]) ∧
    ¬ FriAdaptiveRoundQueriesAccept idealSchemes ldtTower zeroTranscript ![3] 0 (qZero 0) := by
  have hmle : mle table ![3] = 4 := by decide
  refine ⟨fun _ _ => badPoly_degree, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    show badPoly.eval 0 + badPoly.eval 1 = mle table ![3]
    rw [badPoly_eval, badPoly_eval, hmle]
    decide
  · exact Submodule.zero_mem _
  · intro k
    show badPoly.eval (chalOf ![3] 0) = (0 : ZMod 5) * eqMle ![3] ![3]
    rw [badPoly_eval, zero_mul]
    decide
  · intro hacc
    have h := friAdaptiveRoundQueries_pins idealSchemes ldtTower zeroTranscript ![3] 0 hacc 0
    change (0 : ZMod 5) = fold data0 (basefoldWord dom0 table) 3 ⟨0, by decide⟩ at h
    rw [fold_honest_f5] at h
    exact absurd h (by decide)

/-- ⭐ **The fold check refuses the whole transcript.**  `fold_check_teeth_f5`
closed into the sampled verifier's predicate (`BaseFoldCommittedIorAccepts`,
CITED): every conjunct but the round-0 fibre holds, and the verifier rejects. -/
theorem fold_check_refuses_f5 :
    ¬ BaseFoldCommittedIorAccepts idealSchemes ldtTower zeroTranscript ![3] (mle table ![3])
      badProver 1 ![3] qZero :=
  fun h => fold_check_teeth_f5.2.2.2.2 (h.2.2.1.1 0)

/-! ### The all-`t` instance at `t = 1 < 2^m` -/

/-- One column position — `t = 1`, below the landed extractor's `2^1 = 2`. -/
def q₁ : Fin 1 → Fin 4 := fun _ => 0

/-- The all-`t` Def-4.2 object on the F₅ instance at `t = 1`. -/
noncomputable def rbrAllQueriesF5 :
    RbrKnowledgeSoundness (basefoldTableReduction (m := 1) (by decide) S₄ dom0 q₁) :=
  basefoldTableRbrAllQueries (by decide) S₄ dom0 q₁ (by decide)

noncomputable def stAllQueriesF5 :
    Stmt (basefoldTableReduction (m := 1) (by decide) S₄ dom0 q₁) :=
  ⟨(), honestClaim, fun _ => ()⟩

/-- **Satisfying witness at `t = 1`**: the knowledge state is alive on the
honest claim at the empty transcript with the honest table. -/
theorem rbrAllQueriesF5_state_alive :
    rbrAllQueriesF5.kstate.state (1 / 2) stAllQueriesF5 Transcript.empty table = true := by
  refine (rbrAllQueriesF5.kstate.empty_iff (1 / 2) ?_ stAllQueriesF5 table).mpr ?_
  · change (1 / 2 : ℝ) ∈ Set.Ioo 0 1
    norm_num
  · refine ⟨stAllQueriesF5.y, ⟨rfl, rfl⟩, ?_⟩
    rw [fracHamming_self]
    norm_num

/-- **Falsifier at `t = 1`**: the root committing `[2, 1]` with the honest value
`4` at `z = 3` is REFUSED at witness `table` and accepted at `[2, 1]` — the
landed generic tooth (`basefoldTable_source_teeth`, CITED) at the query count
the landed instance cannot reach. -/
theorem basefoldTable_teeth_allQueries_f5 :
    ¬ (basefoldTableReduction (m := 1) (by decide) S₄ dom0 q₁).R ()
        ⟨S₄.commit (basefoldWord dom0 table'), ![3], mle table ![3]⟩ (fun _ => ()) table ∧
      (basefoldTableReduction (m := 1) (by decide) S₄ dom0 q₁).R ()
        ⟨S₄.commit (basefoldWord dom0 table'), ![3], mle table ![3]⟩ (fun _ => ()) table' :=
  basefoldTable_source_teeth (by decide) S₄ dom0 q₁ (by decide) table_ne_table'
    mle_table'_eq _

/-- The round price computes to `2/5` at `t = 1`. -/
theorem rbrAllQueriesF5_err (i : Fin 1)
    (st : Stmt (basefoldTableReduction (m := 1) (by decide) S₄ dom0 q₁)) (δ : ℝ) :
    rbrAllQueriesF5.err i st δ = 2 / 5 := by
  rw [rbrAllQueriesF5, basefoldTableRbrAllQueries_err, ZMod.card]
  norm_num

/-- The compiled leg at `t = 1`: `(t + 1) · 2/5`, a live finite-field number
at a query count the landed instance cannot reach. -/
theorem tableFs_sound_allQueries_f5 :
    FsStraightlineKnowledgeSoundness
      (basefoldTableReduction (m := 1) (by decide) S₄ dom0 q₁) Set.univ
      (fun _s t _δ => ((t : ℝ) + 1) * (2 / 5)) := by
  have h := basefoldTable_fs_sound_allQueries (m := 1) (by decide) S₄ dom0 q₁ (by decide)
  have hfun : (fun (_s t : ℕ) (_δ : ℝ) =>
        ((t : ℝ) + ((1 : ℕ) : ℝ)) * (2 / (Fintype.card (ZMod 5) : ℝ)))
      = fun (_s t : ℕ) (_δ : ℝ) => ((t : ℝ) + 1) * (2 / 5) := by
    funext s t δ
    rw [ZMod.card]
    norm_num
  rwa [hfun] at h

end BaseFoldRbrTableDescentExample

/-- info: 'Minidregg.Selvage.pair_of_two_folds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pair_of_two_folds
/-- info: 'Minidregg.Selvage.fold_not_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fold_not_injective
/-- info: 'Minidregg.Selvage.descentExtract_committed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms descentExtract_committed
/-- info: 'Minidregg.Selvage.basefoldWord_descentExtractWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefoldWord_descentExtractWord
/-- info: 'Minidregg.Selvage.basefoldTableRbrAllQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefoldTableRbrAllQueries
/-- info: 'Minidregg.Selvage.basefoldTableRbrAllQueries_srExtract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefoldTableRbrAllQueries_srExtract
/-- info: 'Minidregg.Selvage.basefoldTable_fs_sound_allQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefoldTable_fs_sound_allQueries
/-- info: 'Minidregg.Selvage.basefoldTable_fs_holds_allQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefoldTable_fs_holds_allQueries
/-- info: 'Minidregg.Selvage.basefoldExactClaim_iff_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefoldExactClaim_iff_holds
/-- info: 'Minidregg.Selvage.descentMiss_coherent_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms descentMiss_coherent_le
/-- info: 'Minidregg.Selvage.basefoldCommittedIor_no_witness_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefoldCommittedIor_no_witness_sound
/-- info: 'Minidregg.Selvage.BaseFoldRbrTableDescentExample.fold_not_injective_f5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms BaseFoldRbrTableDescentExample.fold_not_injective_f5
/-- info: 'Minidregg.Selvage.BaseFoldRbrTableDescentExample.descentExtract_recovers_F5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms BaseFoldRbrTableDescentExample.descentExtract_recovers_F5
/-- info: 'Minidregg.Selvage.BaseFoldRbrTableDescentExample.descent_public_view_teeth_f5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms BaseFoldRbrTableDescentExample.descent_public_view_teeth_f5
/-- info: 'Minidregg.Selvage.BaseFoldRbrTableDescentExample.no_public_view_extractor_f5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms BaseFoldRbrTableDescentExample.no_public_view_extractor_f5
/-- info: 'Minidregg.Selvage.BaseFoldRbrTableDescentExample.descentMiss_inhabited_f5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms BaseFoldRbrTableDescentExample.descentMiss_inhabited_f5
/-- info: 'Minidregg.Selvage.BaseFoldRbrTableDescentExample.descentMiss_teeth_f5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms BaseFoldRbrTableDescentExample.descentMiss_teeth_f5
/-- info: 'Minidregg.Selvage.BaseFoldRbrTableDescentExample.fold_check_teeth_f5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms BaseFoldRbrTableDescentExample.fold_check_teeth_f5
/-- info: 'Minidregg.Selvage.BaseFoldRbrTableDescentExample.fold_check_refuses_f5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms BaseFoldRbrTableDescentExample.fold_check_refuses_f5
/-- info: 'Minidregg.Selvage.BaseFoldRbrTableDescentExample.basefoldTable_teeth_allQueries_f5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms BaseFoldRbrTableDescentExample.basefoldTable_teeth_allQueries_f5
/-- info: 'Minidregg.Selvage.BaseFoldRbrTableDescentExample.rbrAllQueriesF5_state_alive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms BaseFoldRbrTableDescentExample.rbrAllQueriesF5_state_alive
/-- info: 'Minidregg.Selvage.BaseFoldRbrTableDescentExample.tableFs_sound_allQueries_f5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms BaseFoldRbrTableDescentExample.tableFs_sound_allQueries_f5

end Minidregg.Selvage
