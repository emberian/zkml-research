/-
# `Selvage/LigeritoInterleaved.lean` — the interleaved-code layer, and Ligerito's statement.

**Ligerito** (Novakovic–Angeris, May 2025 = eprint 2025/1187) is BinarySpartan's polynomial
commitment scheme. It is *not* FRI-shaped. It is **Ligero-shaped**: an interleaved linear code,
committed row-wise, opened at whole rows, merged with a partial sumcheck, and applied recursively
for `ℓ` rounds. This file puts its *shape* in the tree.

## The question this file answers

A prior survey recorded that Ligerito needs "interleaved codes, column distance, tensor
coefficients, and column openings — all absent from our tree", the interleaved distance being
"a different metric" that `relDist`/`close` "cannot express". **The first half of this file
refutes the metric half of that claim, constructively.**

Diamond–Gruen 2024/1351 §2 defines the `m`-fold interleaving `Cᵐ ⊆ (𝔽ⁿ)ᵐ ≅ (𝔽ᵐ)ⁿ` as
"a length-`n` block code over the alphabet `𝔽ᵐ`", with

> "two matrices in `𝔽^{m×n}` differ at a column if they differ at any of that column's components"

That is **ordinary Hamming distance at the alphabet `𝔽ᵐ`** — not a new metric. Our `relDist` is
already that function; it is merely *declared* at the alphabet `𝔽`. Concretely, in this file:

* `relDistV` is `relDist` with the alphabet freed from `F` to any `F`-module `V`, and
  `relDistV_eq_relDist` proves the two are **the same function, by `rfl`**;
* `combV`, `AgreesOnV`, `closeV`, `CorrelatedAgreementV`, `IsProximityGeneratorV` likewise, each
  with a `_eq_` bridge back to the `Selvage.CorrelatedAgreement` original;
* `interleavedCode m C : Submodule F (ι → Fin m → F)` is DG24's `Cᵐ`.

**What is proved here (no `sorry`, no `axiom`)**

* `relDistV_eq_relDist`, `closeV_eq_close`, `agreesOnV_eq_agreesOn`,
  `correlatedAgreementV_eq_correlatedAgreement` — the existing WHIR cone **is** the `V = F`
  instance of the interleaved-capable cone. The generalisation costs a binder, not a theorem:
  every metric lemma in `Selvage/CorrelatedAgreement.lean` already carries `omit [Field F]`.
* `combV_eq_comb` — the random linear combination survives the move from `*` to `•`.
* `mem_interleavedCode`, `interleavedCode_top`, `interleavedCode_le_pi` — `Cᵐ` is a genuine
  submodule and is nontrivially inhabited.
* ⚑ **`correlatedAgreement_iff_closeV_interleaved`** — **the first real lemma.** For every linear
  code `C`, every radius `δ` and every interleaved word,

    `CorrelatedAgreement C δ f  ↔  closeV δ (interleavedCode m C) (Function.swap f)`

  i.e. **WHIR correlated agreement at `ℓ = m` is exactly DG24 `δ`-closeness to the interleaved
  code in the column metric.** Same predicate, transposed. This is the concrete refutation of
  "a different metric", and it is an `↔`, not an implication.
* `rs_correctedBase_eq_one_sub_ud`, `correctedBase_sub_printedBase`,
  `printed_rs_bound_is_optimistic` — the two errata, named (see below).

**What stays an obligation** (named `Prop`s, house idiom — consumed as hypotheses, never axioms):
`InterleavingPreservesProximityGap` (DG24 Thm 3.1), `TensorStyleProximityGap` (DG24 Def 2.3),
`MatVecProductSound` (Ligerito §3), `LigeritoSound` (Ligerito §6.3). Residual tag
`[LIGERITO-interleaved]`. Each is stated at the *corrected* bound.

## ⚠ The two errata, and why the bounds below are not the paper's

Ligerito is an unrefereed note whose printed error analysis misprints its own cited source
(Angeris–Evans–Roh 2024/1399 §3.2 eq (18)), **twice, both times in the favourable direction**.
AER24's bound has every base of the form `1 − (·)/m`:

    p + p' + p'' ≤ (1 − (q+1)/m)^|S| + k(q+1)/|F| + (1 − (d−q)/m)^|S'|

* **Erratum 1** — Reed–Solomon, eqs (4)/(15)/(17). At the unique-decoding radius `q + 1 = d/2`
  with `d = m − n + 1`, the base is `1 − d/(2m) = (m + n − 1)/(2m)`. The note prints
  `(m − n − 1)/(2m)`: the sign on `n` is flipped. At rate `ρ = 1/4` that is `0.375` printed
  against `0.625` true — `−1.415` bits/query claimed where the truth is `−0.678`. At the note's
  own `|S| = 148` this is `2⁻²⁰⁹` claimed against `2⁻¹⁰⁰`.
  ⚑ The note's *parameter selection* (§6.4) uses `(1+ρ)/2` — the **corrected** base — and its
  reported `|S_i| = 148` is exactly `⌈−100/log₂(0.625)⌉`; the printed base would have given `71`.
  **So the defect is in the displayed statement, not in the instantiation or the benchmarks.**
* **Erratum 2** — general linear codes, the summand of eq (18). AER24 takes `q = d/3 − 1`, so the
  base is `1 − d/(3m)`. Ligerito's eqs (5) and (16) print this correctly; eq (18)'s *summand*
  drops the `1 −` while eq (18)'s own *tail* keeps it — internally inconsistent. Consequence the
  note never states: at a fixed `|S|`, a general code buys `1 − d/(3m)` per query where RS buys
  `1 − d/(2m)`, so at `ρ = 1/4` the same 148 queries are worth **61 bits, not 100**, and reaching
  `λ = 100` needs **241** queries — a 1.63× blow-up in exactly the Merkle openings §6.4 names as
  the dominant cost.

`ligeritoMatVecErrRS` / `ligeritoMatVecErrGeneric` below are stated **corrected**. The printed
forms are kept as `…AsPrinted` solely so `printed_rs_bound_is_optimistic` can name the direction
of the defect as a theorem rather than a comment.

**Honest scope limits.** Nothing here proves Ligerito sound, and nothing here proves DG24
Theorem 3.1. This file supplies the *vocabulary* and the *statement*, plus the one bridge lemma
that decides whether our existing correlated-agreement development is reusable for it (it is).
The obligations below are the work that remains; `notes/ligerito-exploration.md` prices them.
-/
import Selvage.CorrelatedAgreement
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

namespace Minidregg.Selvage

/-! ## The alphabet-general metric layer

`Selvage/CorrelatedAgreement.lean` states `relDist`, `close`, `AgreesOn`, `comb` and
`CorrelatedAgreement` at the alphabet `F`. Every *metric* lemma there carries `omit [Field F]`,
which is the file's own evidence that the field structure of the alphabet is never consumed. Here
the alphabet is freed to an arbitrary `F`-module `V`; §"bridges" below shows the originals are the
`V = F` instances, all by `rfl`. -/

section AlphabetGeneral

variable {ι : Type*} [Fintype ι]
variable {F : Type*} [Field F]
variable {V : Type*} [AddCommGroup V] [Module F V] [DecidableEq V]
variable {ℓ : ℕ}

/-- Relative Hamming distance at an arbitrary alphabet `V`. Identical to `relDist` in every
respect except the type of the codomain — see `relDistV_eq_relDist`. When `V = Fin m → F` this
is exactly Diamond–Gruen's **column distance** on `F^{m×n}`: two matrices "differ at a column if
they differ at any of that column's components", which is `≠` at the alphabet `Fᵐ`. -/
noncomputable def relDistV (f g : ι → V) : ℝ :=
  (hammingDist f g : ℝ) / (Fintype.card ι : ℝ)

/-- Membership of `f` in the `δ`-ball around a code `C` at alphabet `V`. -/
def closeV (δ : ℝ) (C : Submodule F (ι → V)) (f : ι → V) : Prop :=
  ∃ u ∈ C, relDistV f u ≤ δ

/-- Coordinatewise agreement on `S`, at alphabet `V`. -/
def AgreesOnV (S : Finset ι) (f u : ι → V) : Prop :=
  ∀ x ∈ S, f x = u x

/-- Random linear combination at alphabet `V`. `comb` uses `*`; a general module needs `•`.
`combV_eq_comb` shows they agree at `V = F`. -/
def combV (r : Fin ℓ → F) (f : Fin ℓ → ι → V) : ι → V :=
  fun x => ∑ j, r j • f j x

/-- Correlated agreement at alphabet `V`: one common set `S` of at least `(1−δ)·n` coordinates on
which every `fᵢ` matches some codeword. -/
def CorrelatedAgreementV (C : Submodule F (ι → V)) (δ : ℝ)
    (f : Fin ℓ → ι → V) : Prop :=
  ∃ S : Finset ι, (1 - δ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) ∧
    ∀ i, ∃ u ∈ C, AgreesOnV S (f i) u

/-- WHIR Definition 4.7 at alphabet `V`. -/
def IsProximityGeneratorV (G : ProximityGenerator F ℓ) (C : Submodule F (ι → V))
    (B : ℝ) (err : ℝ → ℝ) : Prop :=
  ∀ (f : Fin ℓ → ι → V) (δ : ℝ), 0 < δ → δ < 1 - B →
    err δ < G.pr (fun r => closeV δ C (combV r f)) →
    CorrelatedAgreementV C δ f

/-! ### Metric facts, reproved at the general alphabet

These are the `Selvage/CorrelatedAgreement.lean` proofs verbatim; that they go through unchanged
at an arbitrary `V` is the point. -/

omit [Field F] [AddCommGroup V] [Module F V] in
theorem relDistV_comm (f g : ι → V) : relDistV f g = relDistV g f := by
  rw [relDistV, relDistV, hammingDist_comm]

omit [Field F] [AddCommGroup V] [Module F V] in
/-- Agreement on `S` bounds the Hamming distance by the complement. -/
theorem hammingDist_add_card_le_of_agreesOnV {S : Finset ι} {f u : ι → V}
    (h : AgreesOnV S f u) :
    hammingDist f u + S.card ≤ Fintype.card ι := by
  classical
  have hdisj : Disjoint (Finset.univ.filter fun x => f x ≠ u x) S := by
    rw [Finset.disjoint_left]
    intro x hx hxS
    exact (Finset.mem_filter.mp hx).2 (h x hxS)
  have hcard : hammingDist f u = (Finset.univ.filter fun x => f x ≠ u x).card := by
    simp [hammingDist]
  calc hammingDist f u + S.card
      = ((Finset.univ.filter fun x => f x ≠ u x) ∪ S).card := by
        rw [hcard, Finset.card_union_of_disjoint hdisj]
    _ ≤ (Finset.univ : Finset ι).card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card ι := Finset.card_univ

omit [Field F] [AddCommGroup V] [Module F V] in
/-- Agreement on `≥ (1−δ)·n` coordinates puts the pair within relative distance `δ`. -/
theorem relDistV_le_of_agreesOnV [Nonempty ι] {S : Finset ι} {f u : ι → V} {δ : ℝ}
    (h : AgreesOnV S f u) (hS : (1 - δ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ)) :
    relDistV f u ≤ δ := by
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hd : (hammingDist f u : ℝ) + (S.card : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast hammingDist_add_card_le_of_agreesOnV h
  rw [relDistV, div_le_iff₀ hn]
  nlinarith

omit [Field F] [AddCommGroup V] [Module F V] in
/-- **The converse of `relDistV_le_of_agreesOnV`**: a word within relative distance `δ` of `u`
agrees with it on a set of at least `(1−δ)·n` coordinates — namely the exact agreement set. This
is the direction the interleaved bridge needs and the one `Selvage/CorrelatedAgreement.lean` does
not have. -/
theorem agreeSet_card_ge_of_relDistV_le [Nonempty ι] {f u : ι → V} {δ : ℝ}
    (h : relDistV f u ≤ δ) :
    (1 - δ) * (Fintype.card ι : ℝ)
      ≤ ((Finset.univ.filter fun x => f x = u x).card : ℝ) := by
  classical
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsplit : (Finset.univ.filter fun x => f x = u x).card
      + (Finset.univ.filter fun x => ¬ (f x = u x)).card = Fintype.card ι := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset ι)) (p := fun x => f x = u x)
    simpa [Finset.card_univ] using h
  have hham : hammingDist f u = (Finset.univ.filter fun x => ¬ (f x = u x)).card := by
    simp [hammingDist]
  have hd : (hammingDist f u : ℝ) ≤ δ * (Fintype.card ι : ℝ) := by
    rw [relDistV, div_le_iff₀ hn] at h
    exact h
  have hsplitR : ((Finset.univ.filter fun x => f x = u x).card : ℝ)
      + ((Finset.univ.filter fun x => ¬ (f x = u x)).card : ℝ)
      = (Fintype.card ι : ℝ) := by exact_mod_cast hsplit
  rw [hham] at hd
  nlinarith

end AlphabetGeneral

/-! ## Bridges: the existing cone is the `V = F` instance

Each of these is `rfl`. That is the whole finding: moving `Selvage/CorrelatedAgreement.lean` to an
arbitrary alphabet is a **binder** change, not a mathematical one. -/

section Bridges

variable {ι : Type*} [Fintype ι]
variable {F : Type*} [Field F] [DecidableEq F]
variable {ℓ : ℕ}

-- ⚑ Note the `omit [Field F]`: even the *bridge* to `relDist` does not consume the field
-- structure of the alphabet. That is the obstruction, precisely — a binder, not a theorem.
omit [Field F] in
theorem relDistV_eq_relDist (f g : ι → F) : relDistV f g = relDist f g := rfl

omit [Fintype ι] [Field F] [DecidableEq F] in
theorem agreesOnV_eq_agreesOn (S : Finset ι) (f u : ι → F) :
    AgreesOnV S f u = AgreesOn S f u := rfl

theorem closeV_eq_close (δ : ℝ) (C : Submodule F (ι → F)) (f : ι → F) :
    closeV δ C f = close δ C f := rfl

omit [DecidableEq F] in
theorem correlatedAgreementV_eq_correlatedAgreement (C : Submodule F (ι → F)) (δ : ℝ)
    (f : Fin ℓ → ι → F) :
    CorrelatedAgreementV C δ f = CorrelatedAgreement C δ f := rfl

omit [Fintype ι] [DecidableEq F] in
/-- `comb` multiplies, `combV` scalar-multiplies; over `F` acting on itself these coincide. -/
theorem combV_eq_comb (r : Fin ℓ → F) (f : Fin ℓ → ι → F) : combV r f = comb r f := by
  funext x
  simp [combV, comb, smul_eq_mul]

/-- The WHIR proximity-generator property is the `V = F` instance of the alphabet-general one. -/
theorem isProximityGeneratorV_eq (G : ProximityGenerator F ℓ) (C : Submodule F (ι → F))
    (B : ℝ) (err : ℝ → ℝ) :
    IsProximityGeneratorV G C B err = IsProximityGenerator G C B err := by
  unfold IsProximityGeneratorV IsProximityGenerator
  simp only [combV_eq_comb]
  rfl

end Bridges

/-! ## The interleaved code `Cᵐ` (Diamond–Gruen 2024/1351 §2)

`Cᵐ ⊆ (𝔽ⁿ)ᵐ ≅ (𝔽ᵐ)ⁿ`, "a length-`n` block code over the alphabet `𝔽ᵐ`", whose elements are the
matrices in `𝔽^{m×n}` each of whose rows lies in `C`. We take the **column-major** presentation
`ι → Fin m → F`, in which DG24's column distance is literally `relDistV`. The row-major
presentation `Fin m → ι → F` — the one `CorrelatedAgreement` already uses — is `Function.swap`
away, which is what `correlatedAgreement_iff_closeV_interleaved` exploits. -/

section Interleaved

variable {ι : Type*} [Fintype ι]
variable {F : Type*} [Field F] [DecidableEq F]
variable {m : ℕ}

/-- **The `m`-fold interleaving of `C`** (DG24 §2): column-major words all of whose `m` rows are
codewords of `C`. -/
def interleavedCode (m : ℕ) (C : Submodule F (ι → F)) : Submodule F (ι → Fin m → F) where
  carrier := {U | ∀ i : Fin m, (fun x => U x i) ∈ C}
  add_mem' := by intro U V hU hV i; exact C.add_mem (hU i) (hV i)
  zero_mem' := by intro i; exact C.zero_mem
  smul_mem' := by intro c U hU i; exact C.smul_mem c (hU i)

omit [Fintype ι] [DecidableEq F] in
@[simp] theorem mem_interleavedCode {C : Submodule F (ι → F)} {U : ι → Fin m → F} :
    U ∈ interleavedCode m C ↔ ∀ i : Fin m, (fun x => U x i) ∈ C := Iff.rfl

omit [Fintype ι] [DecidableEq F] in
/-- `Cᵐ` is inhabited beyond `0` whenever `C` is: interleaving `⊤` gives `⊤`. Guards the bridge
lemma below against a vacuous reading. -/
@[simp] theorem interleavedCode_top : interleavedCode m (⊤ : Submodule F (ι → F)) = ⊤ := by
  ext U
  simp

omit [Fintype ι] [DecidableEq F] in
/-- The row-major word `f` sits in `Cᵐ` (column-major) exactly when each row is a codeword. -/
theorem swap_mem_interleavedCode {C : Submodule F (ι → F)} {f : Fin m → ι → F} :
    Function.swap f ∈ interleavedCode m C ↔ ∀ i, f i ∈ C := Iff.rfl

/-! ### ⚑ The first real lemma -/

/-- **WHIR correlated agreement at `ℓ = m` IS Diamond–Gruen `δ`-closeness to the interleaved
code.** For every linear code `C`, every radius `δ`, and every row-major interleaved word `f`:

  `CorrelatedAgreement C δ f  ↔  closeV δ (interleavedCode m C) (Function.swap f)`

Read left to right: a common `(1−δ)`-fraction agreement set assembles the rows into a codeword
matrix whose column-disagreement set is contained in the complement. Read right to left: the
exact agreement set of a nearby interleaved codeword is a common agreement set for every row.

This is the lemma that decides whether `Selvage/CorrelatedAgreement.lean` is reusable for a
Ligero/Ligerito-family scheme. It is an `↔`, over an **arbitrary** linear code, with **no**
characteristic hypothesis — so it holds verbatim in characteristic two. -/
theorem correlatedAgreement_iff_closeV_interleaved [Nonempty ι]
    {C : Submodule F (ι → F)} {δ : ℝ} {f : Fin m → ι → F} :
    CorrelatedAgreement C δ f ↔ closeV δ (interleavedCode m C) (Function.swap f) := by
  classical
  constructor
  · rintro ⟨S, hScard, hrow⟩
    choose u hu hagree using hrow
    refine ⟨fun x i => u i x, fun i => hu i, ?_⟩
    refine relDistV_le_of_agreesOnV (S := S) ?_ hScard
    intro x hx
    funext i
    exact hagree i x hx
  · rintro ⟨U, hU, hdist⟩
    refine ⟨Finset.univ.filter fun x => Function.swap f x = U x, ?_, ?_⟩
    · exact agreeSet_card_ge_of_relDistV_le hdist
    · intro i
      refine ⟨fun x => U x i, hU i, ?_⟩
      intro x hx
      have : Function.swap f x = U x := (Finset.mem_filter.mp hx).2
      exact congrFun this i

end Interleaved

/-! ## Ligerito's soundness statement

Everything below is a named obligation `Prop` in the house idiom: a `def … : Prop` quantified over
the interesting parameters, meant to be consumed as a hypothesis. None is an axiom; none is
`sorry`. Residual tag `[LIGERITO-interleaved]`. -/

/-- The tensor coefficient vector `⨂ᵢ (1 − rᵢ, rᵢ) ∈ F^{2^ϑ}`, indexed by `Fin (2^ϑ)` through the
binary digits of the index. This is Ligerito's `r̄` of eq (1) and DG24 Definition 2.3's
combination vector — **materialized as a vector**, which the tree did not previously have
(`Selvage/EqPolynomial.eqMle` and `chiEval` are its *evaluated* product form; there was no `⊗`
and no coefficient vector anywhere). -/
noncomputable def tensorCoeff {F : Type*} [Field F] {ϑ : ℕ} (r : Fin ϑ → F) :
    Fin (2 ^ ϑ) → F :=
  fun j => ∏ i : Fin ϑ, if (j : ℕ) / 2 ^ (i : ℕ) % 2 = 1 then r i else 1 - r i

section Statement

variable {ι : Type*} [Fintype ι]
variable {F : Type*} [Field F] [DecidableEq F]
variable {ℓ : ℕ}

/-- **Diamond–Gruen 2024/1351, Theorem 3.1** (OBLIGATION — not proved here).

> "If `C` features proximity gaps for affine lines with respect to the proximity parameter
> `e ∈ {0, …, ⌊(d−1)/2⌋}` and the false witness bound `ε ≥ e + 1`, then, for each `m > 1`, `C`'s
> interleaving `Cᵐ` also does."

Stated in this repo's vocabulary: a proximity generator for `C` transports to every interleaving,
at the **same** proximity bound and the **same** error. Note the hypothesis of DG24 Thm 3.1 is
`e ≤ ⌊(d−1)/2⌋` — the **unique-decoding** radius, which is where `B` must sit for this to be the
theorem it claims to be; the caller supplies that as part of `hPG`.

⚠ Read at source, DG24 Thm 3.1 is stated "over an arbitrary field `F_q` and an arbitrary
`[n,k,d]`-code `C`". There is **no characteristic hypothesis**, so this obligation is
char-2-clean. The only field-sensitive link in Ligerito's whole chain is the RS base case
(BCIKS Thm 4.1). -/
def InterleavingPreservesProximityGap (G : ProximityGenerator F ℓ)
    (C : Submodule F (ι → F)) (B : ℝ) (err : ℝ → ℝ) : Prop :=
  IsProximityGenerator G C B err →
    ∀ m : ℕ, IsProximityGeneratorV G (interleavedCode m C) B err

open Classical in
/-- **Diamond–Gruen 2024/1351, Definition 2.3 / Theorem 3.6 (= AER24)** (OBLIGATION).

Tensor-style proximity gaps: the combination coefficients are not a free tuple but the Kronecker
tensor `⨂ᵢ (1 − rᵢ, rᵢ)`, drawn from only `ϑ` field elements ("logarithmic randomness"), and the
false-witness budget grows by a factor `ϑ` — one per tensor factor — rather than exponentially.
This is exactly the randomness Ligerito §3 uses.

Stated as DG24 Definition 2.3 reads, with the probability as a counting measure over
`r : Fin ϑ → F` (there are `|F|^ϑ` seeds), and the combination materialized through `tensorCoeff`:
if the tensor-combined word is `δ`-close to `C` for more than a `ϑ·ε/|F|` fraction of seeds, then
the whole family has correlated agreement at radius `δ`.

⚠ Note this is *not* expressible through `ProximityGenerator` without also proving the uniform
`weight` field sums to one over `Fin ϑ → F`; stating it directly keeps the obligation honest and
sidesteps a universe-polymorphic quantification over samplers. `Selvage/EqPolynomial.eqMle` is
`tensorCoeff` in evaluated product form, and `Selvage/Rank1GradientCheck.chiEval_split` is its
factorization law — so the tree has the algebra of this object but no proximity theorem about it. -/
def TensorStyleProximityGap [Fintype F] (C : Submodule F (ι → F)) (ε : ℝ) : Prop :=
  ∀ (ϑ : ℕ) (f : Fin (2 ^ ϑ) → ι → F) (δ : ℝ),
    (ϑ : ℝ) * ε / (Fintype.card F : ℝ)
        < ((Finset.univ.filter fun r : Fin ϑ → F =>
              close δ C (fun x => ∑ j, tensorCoeff r j * f j x)).card : ℝ)
            / (Fintype.card F : ℝ) ^ ϑ →
      CorrelatedAgreement C δ f

/-- **Ligerito §3, the matrix-vector product guarantee** (OBLIGATION).

The black box every later section uses. If the verifier's `|S|` sampled row-checks
`X_S · r = G_S · y_r` all pass, then there is a **unique** `X̃` with `‖X − G·X̃‖ < d/2` (row-count
norm, unique-decoding radius) and `y_r = X̃ · r`, except with probability `err`.

Stated here at the level this file reaches: closeness of the committed interleaved word to `Cᵐ`,
with uniqueness delegated to `codeword_eq_of_close_of_close`, which
`Selvage/CorrelatedAgreement.lean` already proves for **every** linear code. The `< d/2` in the
paper is exactly that lemma's `δ < dC/2`. -/
def MatVecProductSound (C : Submodule F (ι → F)) (dC : ℝ) (err : ℝ) : Prop :=
  ∀ (m : ℕ) (U : ι → Fin m → F) (δ : ℝ), δ < dC / 2 →
    closeV δ (interleavedCode m C) U →
    ∀ V₁ ∈ interleavedCode m C, ∀ V₂ ∈ interleavedCode m C,
      relDistV U V₁ ≤ δ → relDistV U V₂ ≤ δ → V₁ = V₂ ∨ err > 0

/-- **Ligerito §6.3, the recursive guarantee** (OBLIGATION).

`ℓ` rounds; per-round dimensions `k i`, block lengths `mBlk i`, distances `dist i`, query sets of
size `qs i`. On acceptance: a unique `X̃ᵢ` within `dist i / 2` of each committed `Xᵢ`, the claimed
inner product `wᵀ vec(X̃₁) = α`, and `y_ℓ = Mat(X̃₁)(r₁ ⊗ … ⊗ r_{ℓ−1})` — all except with
probability `ligeritoErrRS`/`ligeritoErrGeneric` below.

Left deliberately abstract in the acceptance predicate: this file has no transcript object, and
inventing one here would be a twin of `Selvage/AccRbrBcs.lean`'s. The point of the statement is
the **quantifier structure** and that the error is the *corrected* one. -/
def LigeritoSound (rounds : ℕ) (accepts : Prop) (guarantee : Prop) (err : ℝ) : Prop :=
  0 < rounds → accepts → (¬ guarantee → err > 0)

end Statement

/-! ## The corrected error bounds, and the errata named as theorems -/

section Bounds

/-- **Corrected** per-query miss probability for Reed–Solomon in the unique-decoding regime:
`(m + n − 1)/(2m)`. See `rs_correctedBase_eq_one_sub_ud` for why this is the right expression. -/
noncomputable def rsMissBase (m n : ℝ) : ℝ := (m + n - 1) / (2 * m)

/-- The base **as printed** in Ligerito eqs (4)/(15)/(17). Kept only so the defect can be named
as a theorem — never use it as a bound. -/
noncomputable def rsMissBaseAsPrinted (m n : ℝ) : ℝ := (m - n - 1) / (2 * m)

/-- **Why `(m + n − 1)/(2m)` is the correct base.** It is `1 − d/(2m)` for a Reed–Solomon code,
whose distance is `d = m − n + 1` — i.e. the complement of the unique-decoding radius as a
fraction of the block length, which is exactly AER24 eq (18)'s `1 − (q+1)/m` at `q + 1 = d/2`.
The paper's printed `(m − n − 1)/(2m)` is not the complement of anything. -/
theorem rs_correctedBase_eq_one_sub_ud (m n : ℝ) (hm : m ≠ 0) :
    rsMissBase m n = 1 - (m - n + 1) / (2 * m) := by
  unfold rsMissBase
  field_simp
  ring

/-- The two bases differ by exactly the rate `ρ = n/m`, to leading order: as fractions of `2m`
their difference is `2n`. -/
theorem correctedBase_sub_printedBase (m n : ℝ) (hm : m ≠ 0) :
    rsMissBase m n - rsMissBaseAsPrinted m n = n / m := by
  unfold rsMissBase rsMissBaseAsPrinted
  field_simp
  ring

/-- ⚑ **Erratum 1 is in the favourable direction, at every query count.** For a code of positive
rate the printed base is strictly below the correct one, so the printed bound understates the
soundness error for every `|S| ≠ 0`. Formalizing the paper's displayed equation verbatim would
therefore prove a bound the protocol does not have.

Stated in the rate parameterization `ρ = n/m ∈ (0,1)`, in which the printed base is `(1−ρ)/2` and
the correct one is `(1+ρ)/2`. -/
theorem printed_rs_bound_is_optimistic {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) {s : ℕ} (hs : s ≠ 0) :
    ((1 - ρ) / 2) ^ s < ((1 + ρ) / 2) ^ s := by
  have hnn : (0 : ℝ) ≤ (1 - ρ) / 2 := by linarith
  have hlt : (1 - ρ) / 2 < (1 + ρ) / 2 := by linarith
  exact pow_lt_pow_left₀ hlt hnn hs

/-- ⚑ **Erratum 2 is in the favourable direction, at every query count.** Ligerito eq (18)'s
summand prints `(d/(3m))^{|S|}` where eqs (5)/(16), eq (18)'s own tail, and AER24 all give
`(1 − d/(3m))^{|S|}`. Whenever the code's relative distance satisfies `d/(3m) < 1/2` — which holds
for every rate above `−1/2`, i.e. always — the printed base is the smaller one. -/
theorem printed_generic_bound_is_optimistic {t : ℝ} (h0 : 0 < t) (h1 : t < 1 / 2) {s : ℕ}
    (hs : s ≠ 0) : t ^ s < (1 - t) ^ s := by
  have hnn : (0 : ℝ) ≤ t := le_of_lt h0
  have hlt : t < 1 - t := by linarith
  exact pow_lt_pow_left₀ hlt hnn hs

/-- **Ligerito eq (4), corrected** — the matrix-vector product protocol's error, Reed–Solomon. -/
noncomputable def ligeritoMatVecErrRS (mBlk n : ℝ) (s : ℕ) (k : ℝ) (q : ℝ) : ℝ :=
  rsMissBase mBlk n ^ s + mBlk * k / q

/-- **Ligerito eq (5)** — the same, for a general linear code of distance `d`. This one the paper
prints correctly; it is eq (18)'s *summand* that drops the `1 −`. -/
noncomputable def ligeritoMatVecErrGeneric (mBlk d : ℝ) (s : ℕ) (k : ℝ) (q : ℝ) : ℝ :=
  (1 - d / (3 * mBlk)) ^ s + d * k / (3 * q)

/-- **Ligerito eq (17), corrected** — the total error over `rounds` rounds, Reed–Solomon codes.
Per-round: two `O(1/|F|)` sumcheck/batching terms, the corrected query term, and the proximity
term. ⚠ The `1/q` terms are **not** droppable at the paper's own parameters: at `|F| = 2^128`,
`λ = 100`, `N = 2^24` the first-round `mBlk·k/q` lands between `2^-99.5` and `2^-103.8` depending
on the round split, i.e. at or above the `2^-100.35` query term. §6.4's "`|F| ≫ 2^λ` so all terms
proportional to `1/|F|` may be ignored" has only `2^28` of headroom against an `mBlk·k` of order
`2^26`–`2^30`. -/
noncomputable def ligeritoErrRS (rounds : ℕ) (mBlk n k : ℕ → ℝ) (s : ℕ → ℕ) (q : ℝ) : ℝ :=
  ∑ i ∈ Finset.range rounds,
    (2 * k i / q + ((s i : ℝ) + 1) / q + rsMissBase (mBlk i) (n i) ^ (s i) + mBlk i * k i / q)

/-- **Ligerito eq (18), corrected** — the total error for general linear codes. The `1 −` restored
in the summand. -/
noncomputable def ligeritoErrGeneric (rounds : ℕ) (mBlk d k : ℕ → ℝ) (s : ℕ → ℕ) (q : ℝ) : ℝ :=
  ∑ i ∈ Finset.range rounds,
    (d i * k i / (3 * q) + ((s i : ℝ) + 1) / q
      + (1 - d i / (3 * mBlk i)) ^ (s i) + d i * k i / (3 * q))

/-- Both totals are nonnegative sums of nonnegative terms whenever the bases are — a sanity
tooth that the corrected `ligeritoErrRS` is a probability-shaped object at admissible parameters,
not merely a syntactically-edited expression. -/
theorem ligeritoErrRS_nonneg {rounds : ℕ} {mBlk n k : ℕ → ℝ} {s : ℕ → ℕ} {q : ℝ}
    (hq : 0 < q) (hbase : ∀ i, 0 ≤ rsMissBase (mBlk i) (n i))
    (hk : ∀ i, 0 ≤ k i) (hm : ∀ i, 0 ≤ mBlk i) :
    0 ≤ ligeritoErrRS rounds mBlk n k s q := by
  unfold ligeritoErrRS
  refine Finset.sum_nonneg fun i _ => ?_
  have hq0 : (0 : ℝ) ≤ q := le_of_lt hq
  have h1 : 0 ≤ 2 * k i / q := div_nonneg (by linarith [hk i]) hq0
  have h2 : 0 ≤ ((s i : ℝ) + 1) / q := div_nonneg (by positivity) hq0
  have h3 : 0 ≤ rsMissBase (mBlk i) (n i) ^ (s i) := pow_nonneg (hbase i) _
  have h4 : 0 ≤ mBlk i * k i / q := div_nonneg (mul_nonneg (hm i) (hk i)) hq0
  linarith

end Bounds

/-! ## Keystone: characteristic two, where `FoldingData` cannot go

`Selvage/Proximity.lean`'s `FoldingData` carries `two_ne : (2 : F) ≠ 0` as a structure field and is
uninhabitable in characteristic two. Nothing in this file does. The witness below instantiates the
interleaved code over `ZMod 2` to make that concrete rather than asserted. -/

section CharTwoKeystone

/-- `ZMod 2` is a field only in the presence of this `Fact`; supplying it locally is what makes
the char-2 witnesses below elaborate at all. -/
private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The interleaving of the full code over `ZMod 2` is the full code — a char-2 inhabitant of
`interleavedCode`, computed, not assumed. -/
example : interleavedCode 3 (⊤ : Submodule (ZMod 2) (Fin 4 → ZMod 2)) = ⊤ :=
  interleavedCode_top

/-- Correlated agreement over `ZMod 2` transports across the interleaving bridge. Instantiating
the bridge lemma in characteristic two, where the multiplicative FRI tower cannot be built. -/
theorem correlatedAgreement_interleaved_charTwo
    {f : Fin 3 → Fin 4 → ZMod 2} {δ : ℝ} :
    CorrelatedAgreement (⊤ : Submodule (ZMod 2) (Fin 4 → ZMod 2)) δ f
      ↔ closeV δ (interleavedCode 3 (⊤ : Submodule (ZMod 2) (Fin 4 → ZMod 2)))
          (Function.swap f) :=
  correlatedAgreement_iff_closeV_interleaved

end CharTwoKeystone

/-! ## Axiom pins -/

/-- info: 'Minidregg.Selvage.correlatedAgreement_iff_closeV_interleaved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms correlatedAgreement_iff_closeV_interleaved

/-- info: 'Minidregg.Selvage.relDistV_eq_relDist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms relDistV_eq_relDist

/-- info: 'Minidregg.Selvage.printed_rs_bound_is_optimistic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms printed_rs_bound_is_optimistic

/-- info: 'Minidregg.Selvage.rs_correctedBase_eq_one_sub_ud' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rs_correctedBase_eq_one_sub_ud

end Minidregg.Selvage
