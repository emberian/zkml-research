/-
# Selvage.AdditiveBasisBinding — the ordered basis is what a handle must carry

`Selvage/AdditiveBaseFold.lean`'s `keystone_basis_ambiguity` is a proved NEGATIVE:
`X² + X` on the four-point GF(16) domain `span{1, x₁}` is the LCH commitment of
`preA` under the ordered basis `(1, x₁)` **and** of `preB` under `(x₁, 1)` — same
span, same evaluation points, same Merkle leaves, both orderings linearly
independent, different Boolean tables, different terminal constants.

That file names the hazard and does not repair it. This file repairs it, and the
repair is stated as theorems rather than as a convention:

| § | statement | direction |
|---|---|---|
| 1 | `table_unique_of_novelPack_eq` — at a FIXED ordered basis, the codeword determines the table | ⭐ positive |
| 2 | `no_span_indexed_decoder` — **no** decode function indexed by (span, codeword) is correct on honest commitments | ⚑ negative, at GF(16) |
| 3 | `lchBasisBoundPcs` + `lchRingSwitchTarget` — a handle carrying the ORDERED basis is `Complete` and `Extractable` | ⭐ positive |
| 4 | `spanBoundPcs_not_extractable` — a handle carrying only the SPAN is provably NOT `Extractable` | ⚑ negative, at GF(16) |
| 5 | teeth — the honest commitment is still ACCEPTED; the reordered sibling is REFUSED; and the reordering is asserted to be a real mutation that the span-indexed handle cannot see | both |

## What "the encoding IS the binding" means here, and why this layer holds the tuple

The hazard is that a binding which agrees on the span and differs on the ORDER
reintroduces the hole one level down. This file therefore takes the strongest
possible tag — **the ordered basis itself, as the function `ℕ → F` read
positionally** — and proves the closure against that. The byte-level canonical
encoding lives one layer out, in
`Compiler/Tower256AdditiveFriController.lean`'s `basisPrefix`, together with
`basisPrefix_inj`: the sponge input determines the ordered tuple. The two layers
compose — bytes ⇒ ordered tuple (Compiler) ⇒ table (here) — and the composition is
`Compiler.Tower256AdditiveFriController.transcript_determines_table`.

## Scope, said plainly

`LargeFieldMlePcs` is Diamond–Posen's `Π′` surface: a handle, an evaluation point
and a claimed value, with `accepts` a PREDICATE. `Extractable` is therefore the
zero-error idealization `Selvage/RingSwitching.lean` already labels as such. What
this file adds is not a proximity or ROM result: it is the statement that the map
from a HANDLE to a committed multilinear is well defined when the handle carries
the ordered basis and ill defined when it carries only the span. That is exactly
the obligation `RingSwitching`'s §7 item 4 names as blocking, and nothing here
claims more. In particular `lchBasisBoundPcs`'s root is the codeword polynomial
itself, so this file says nothing about succinctness, Merkle binding, or FRI
proximity — those remain where they were.

## ⚠ Not a `FoldingData` in sight

Same discipline as `AdditiveBaseFold`: no declaration below takes a `FoldingData`,
a `FoldingTower`, `fold`, `proximityTest` or `chalExt`, so nothing here is
vacuous at characteristic two (`Selvage/CharTwoWall.lean`). The GF(16) keystones
in §2, §4 and §5 discharge non-vacuity by exhibiting concrete unequal values.
-/
import Selvage.AdditiveBaseFold
import Selvage.RingSwitching

namespace Minidregg.Selvage

open Polynomial
open Minidregg.Theory

set_option autoImplicit false

variable {F : Type} [Field F]

/-! ## 1. At a fixed ordered basis, the codeword determines the table

This is the positive half of `novelPack_injective_of_natDegree_lt`, pushed
through the Möbius layer so that it speaks about TABLES — the objects
`LargeFieldMlePcs` commits to — rather than about coefficient polynomials. -/

/-- ⭐ **THE CLOSURE FACT.** Two Boolean tables with the same LCH commitment
**under the same ordered basis** are equal. `keystone_basis_ambiguity` is
precisely the failure of this statement when the two bases are allowed to
differ, so this theorem and that counterexample are the two sides of one
boundary: the hypothesis `β` is shared here, and is the only thing the
counterexample changes. -/
theorem table_unique_of_novelPack_eq (β : ℕ → F) (l : ℕ)
    (t u : (Fin l → Bool) → F)
    (h : novelPack β l (booleanMobiusPolynomial l t)
        = novelPack β l (booleanMobiusPolynomial l u)) :
    t = u := by
  have hmob : booleanMobiusPolynomial l t = booleanMobiusPolynomial l u :=
    novelPack_injective_of_natDegree_lt
      (natDegree_lt_of_degree_lt (degree_booleanMobiusPolynomial_lt l t))
      (natDegree_lt_of_degree_lt (degree_booleanMobiusPolynomial_lt l u)) h
  have htab := congrArg (tableOfPoly l) hmob
  rwa [tableOfPoly_booleanMobiusPolynomial, tableOfPoly_booleanMobiusPolynomial]
    at htab

/-- **The packing reads the basis only on its live range.** `novelPack β m`
touches `β 0 … β (m-1)` and nothing else, because `additiveFoldedBasis` shifts
the window down by one at each level. This is what lets a transcript bind a
FINITE ordered tuple `β ↾ Fin ell` and still determine the commitment: the
binding does not have to reach the junk beyond `ell`. -/
theorem novelPack_congr : ∀ (m : ℕ) (β β' : ℕ → F) (p : F[X]),
    (∀ n, n < m → β n = β' n) → novelPack β m p = novelPack β' m p := by
  intro m
  induction m with
  | zero => intro β β' p _; rfl
  | succ m ih =>
      intro β β' p hagree
      have h0 : β 0 = β' 0 := hagree 0 (Nat.succ_pos m)
      have hfold : ∀ n, n < m →
          additiveFoldedBasis β n = additiveFoldedBasis β' n := by
        intro n hn
        rw [additiveFoldedBasis, additiveFoldedBasis, h0,
          hagree (n + 1) (Nat.succ_lt_succ hn)]
      rw [novelPack_succ, novelPack_succ, h0,
        ih (additiveFoldedBasis β) (additiveFoldedBasis β') (evenPart p) hfold,
        ih (additiveFoldedBasis β) (additiveFoldedBasis β') (oddPart p) hfold]

/-- ⭐ **THE CLOSURE FACT, IN THE FORM A TRANSCRIPT CAN DISCHARGE.** Two tables
committed under two bases that AGREE ON THE LIVE RANGE are equal. A transcript
that pins `β ↾ Fin l` therefore determines the committed multilinear — which is
exactly what `Compiler.Tower256AdditiveFriController.basisPrefix_inj` supplies,
and exactly what `additiveDomain` equality does NOT supply
(`no_span_indexed_decoder`). -/
theorem table_unique_of_basis_agree (β β' : ℕ → F) (l : ℕ)
    (hagree : ∀ n, n < l → β n = β' n)
    (t u : (Fin l → Bool) → F)
    (h : novelPack β l (booleanMobiusPolynomial l t)
        = novelPack β' l (booleanMobiusPolynomial l u)) :
    t = u :=
  table_unique_of_novelPack_eq β' l t u
    (by rw [← novelPack_congr l β β' (booleanMobiusPolynomial l t) hagree, h])

/-- The same fact as an injectivity statement about the commitment map at a
fixed ordered basis. -/
theorem lchCommit_injective (β : ℕ → F) (l : ℕ) :
    Function.Injective
      (fun t : (Fin l → Bool) → F => novelPack β l (booleanMobiusPolynomial l t)) :=
  fun _ _ h => table_unique_of_novelPack_eq β l _ _ h

/-! ## 2. ⚑ There is NO span-indexed decoder

The sharpest form of the hazard, and the one that does not depend on how a
verifier is modelled: a Merkle root over the evaluation points, plus any label
that identifies the DOMAIN, is a pair `(span, codeword)`. This section proves no
function of that pair can recover the committed table on honest commitments. -/

section NoSpanDecoder

open AdditiveBaseFoldKeystone

/-- The Möbius round trip lets the keystone commitments be restated with a TABLE
where they were stated with a coefficient polynomial. -/
theorem novelPack_table_preA :
    novelPack keystoneBeta 2
        (booleanMobiusPolynomial 2 (tableOfPoly 2 preA)) = sharedWord := by
  rw [booleanMobiusPolynomial_tableOfPoly 2 preA
    (degree_lt_of_natDegree_lt preA_natDegree_lt)]
  exact novelPack_preA

theorem novelPack_table_preB :
    novelPack keystoneBetaSwap 2
        (booleanMobiusPolynomial 2 (tableOfPoly 2 preB)) = sharedWord := by
  rw [booleanMobiusPolynomial_tableOfPoly 2 preB
    (degree_lt_of_natDegree_lt preB_natDegree_lt)]
  exact novelPack_preB

/-- ⚑⚑ **THE UNREPAIRED BINDING ADMITS NO DECODER AT ALL.**

Suppose someone claims that the committed multilinear is a function of the
evaluation DOMAIN and the committed codeword — which is exactly what a Merkle
root over the domain points plus a `domainId` sponge label gives you. No such
function exists: at GF(16) the two orderings of `{1, x₁}` produce the same
`additiveDomain` and the same codeword `X² + X` from two DIFFERENT tables, so any
candidate `decode` must return both, and they are unequal.

This is stronger than "the transcript is ambiguous": it rules out repairing the
gap by any cleverness that stays indexed on the span. -/
theorem no_span_indexed_decoder :
    ¬ ∃ decode : Submodule (ZMod 2) (binaryTower 2) → (binaryTower 2)[X] →
          ((Fin 2 → Bool) → binaryTower 2),
        ∀ (β : ℕ → binaryTower 2) (t : (Fin 2 → Bool) → binaryTower 2),
          LinearIndependent (ZMod 2) (fun j : Fin 2 => β j) →
          decode (additiveDomain β 2)
              (novelPack β 2 (booleanMobiusPolynomial 2 t)) = t := by
  rintro ⟨decode, hdec⟩
  have hA := hdec keystoneBeta (tableOfPoly 2 preA) keystoneBeta_linearIndependent
  have hB := hdec keystoneBetaSwap (tableOfPoly 2 preB)
    keystoneBetaSwap_linearIndependent
  rw [novelPack_table_preA] at hA
  rw [novelPack_table_preB, keystoneBetaSwap_additiveDomain] at hB
  exact tableOfPoly_preA_ne_preB (hA.symm.trans hB)

end NoSpanDecoder

/-! ## 3. The repaired handle: a commitment that carries the ordered basis

`LargeFieldMlePcs` is `Selvage/RingSwitching.lean`'s `Π′` surface. The repair is
one field: the handle records the ordered basis it was committed under, and
`accepts` reads the basis off the handle rather than guessing it. -/

/-- A commitment handle for the additive (LCH) scheme. `basis` is read
POSITIONALLY — it is the ordered `GF(2)`-basis, not its span — which is the whole
content of the repair. -/
structure BasisBoundRoot (F : Type) [Field F] where
  /-- The arity the handle was committed at. -/
  arity : ℕ
  /-- ⭐ The ORDERED basis. Two handles that differ only by a reordering are
  different handles. -/
  basis : ℕ → F
  /-- The committed LCH codeword. -/
  word : F[X]

/-- ⭐ **THE REPAIRED SCHEME.** `Commit` stamps the ordered basis into the handle;
`accepts` is the most generous predicate consistent with honest openings — any
table whose LCH packing **under the handle's own basis** is the handle's word.
The generosity matters: the extractor below has to work against a verifier that
concedes every such reading, so `Extractable` is not bought by making the
verifier picky. -/
noncomputable def lchBasisBoundPcs (β : ℕ → F) : LargeFieldMlePcs F where
  Root := BasisBoundRoot F
  commit := fun {l} t => ⟨l, β, novelPack β l (booleanMobiusPolynomial l t)⟩
  accepts := fun {l} rt r s =>
    rt.arity = l ∧ ∃ t : (Fin l → Bool) → F,
      novelPack rt.basis l (booleanMobiusPolynomial l t) = rt.word ∧ mle t r = s

@[simp] theorem lchBasisBoundPcs_commit (β : ℕ → F) {l : ℕ}
    (t : (Fin l → Bool) → F) :
    (lchBasisBoundPcs β).commit t
      = ⟨l, β, novelPack β l (booleanMobiusPolynomial l t)⟩ :=
  rfl

theorem lchBasisBoundPcs_accepts_iff (β : ℕ → F) {l : ℕ}
    (rt : BasisBoundRoot F) (r : Fin l → F) (s : F) :
    (lchBasisBoundPcs β).accepts rt r s ↔
      rt.arity = l ∧ ∃ t : (Fin l → Bool) → F,
        novelPack rt.basis l (booleanMobiusPolynomial l t) = rt.word ∧
          mle t r = s :=
  Iff.rfl

/-- **The repair does not refuse honest work** (Theorem 3.2's hypothesis). -/
theorem lchBasisBoundPcs_complete (β : ℕ → F) :
    (lchBasisBoundPcs β).Complete := fun t _ => ⟨rfl, t, rfl, rfl⟩

/-- ⭐⭐ **`Extractable` — THE OBLIGATION `keystone_basis_ambiguity` WAS BLOCKING.**

A handle determines a table, extracted before the evaluation point is seen
(Definition 2.9's strict form). The proof is exactly §1: two accepted readings of
one handle share the handle's ordered basis, so `table_unique_of_novelPack_eq`
collapses them. Replace the handle's `basis` field by anything that only pins the
span and this proof breaks at that step — which is `no_span_indexed_decoder`. -/
theorem lchBasisBoundPcs_extractable (β : ℕ → F) :
    (lchBasisBoundPcs β).Extractable := by
  classical
  intro l rt
  by_cases hex : ∃ t : (Fin l → Bool) → F,
      novelPack rt.basis l (booleanMobiusPolynomial l t) = rt.word
  · obtain ⟨t, ht⟩ := hex
    refine ⟨t, fun r s hacc => ?_⟩
    obtain ⟨-, u, hu, hval⟩ := hacc
    have hut : u = t := table_unique_of_novelPack_eq rt.basis l u t (by rw [hu, ht])
    rw [← hval, hut]
  · refine ⟨fun _ => 0, fun r s hacc => ?_⟩
    obtain ⟨-, u, hu, -⟩ := hacc
    exact absurd ⟨u, hu⟩ hex

/-- ⭐ **THE DOWNSTREAM OBLIGATION, DISCHARGED.** `Selvage/RingSwitching.lean`'s
§7 item 4 records the ordered-basis binding as a BLOCKING prerequisite:
"Ring-switching's `Extractable` is FALSE for a scheme with that ambiguity."
With the basis in the handle it is not false, and this is the witness — a
`RingSwitchTarget` built from the actual LCH packing, at any characteristic-two
field and any ordered basis.

Compare `RingSwitching.trivialTarget`, which is inhabitation only: its handle IS
the table, so its `extractable` is `fun rt => ⟨rt.2, …⟩`. Here the handle is the
packed codeword and extraction runs through
`novelPack_injective_of_natDegree_lt`. -/
noncomputable def lchRingSwitchTarget [CharP F 2] (β : ℕ → F) :
    RingSwitchTarget F where
  pcs := lchBasisBoundPcs β
  complete := lchBasisBoundPcs_complete β
  extractable := lchBasisBoundPcs_extractable β

/-! ## 4. ⚑ And the unrepaired handle is provably NOT extractable

§2 rules out any span-indexed decoder. This section says the same thing in the
shape `RingSwitchTarget` actually consumes, so that the obligation is visibly
REFUTABLE and not merely unproved: a `Π′` whose handle records the domain rather
than the ordered basis fails `Extractable`. -/

section SpanBound

variable [Algebra (ZMod 2) F]

/-- The handle a transcript that binds the DOMAIN gives you: an arity, the
evaluation subspace, and the codeword. This is the faithful model of today's
controller — a Merkle root over the domain points plus a `domainId` label. -/
structure SpanBoundRoot (F : Type) [Field F] [Algebra (ZMod 2) F] where
  arity : ℕ
  domain : Submodule (ZMod 2) F
  word : F[X]

/-- The unrepaired scheme. `accepts` admits any reading under any ordered basis
of the RECORDED DOMAIN — which is not generosity invented for this proof but the
verifier's actual ignorance: with the basis unbound, every such reading is an
honest complete opening (`lch_opening_complete` runs at each of them). -/
noncomputable def spanBoundPcs (β : ℕ → F) : LargeFieldMlePcs F where
  Root := SpanBoundRoot F
  commit := fun {l} t =>
    ⟨l, additiveDomain β l, novelPack β l (booleanMobiusPolynomial l t)⟩
  accepts := fun {l} rt r s =>
    rt.arity = l ∧ ∃ basis : ℕ → F,
      LinearIndependent (ZMod 2) (fun j : Fin l => basis j) ∧
        additiveDomain basis l = rt.domain ∧
        ∃ t : (Fin l → Bool) → F,
          novelPack basis l (booleanMobiusPolynomial l t) = rt.word ∧
            mle t r = s

/-- The unrepaired scheme is still complete — so its failure below is a
soundness failure, not a scheme that refuses everything. -/
theorem spanBoundPcs_complete (β : ℕ → F)
    (hβ : ∀ l : ℕ, LinearIndependent (ZMod 2) (fun j : Fin l => β j)) :
    (spanBoundPcs β).Complete :=
  fun {l} t _ => ⟨rfl, β, hβ l, rfl, t, rfl, rfl⟩

end SpanBound

section SpanBoundRefutation

open AdditiveBaseFoldKeystone

/-- A cube corner where the two keystone tables actually disagree. Naming it
keeps the refutation constructive: the witness is produced, not assumed. -/
theorem exists_corner_tableOfPoly_ne :
    ∃ b : Fin 2 → Bool, tableOfPoly 2 preA b ≠ tableOfPoly 2 preB b := by
  by_contra hcon
  exact tableOfPoly_preA_ne_preB
    (funext fun b => not_not.mp fun hne => hcon ⟨b, hne⟩)

/-- ⚑⚑ **THE FLOOR IS FALSE WITHOUT THE BINDING.** The span-bound scheme is not
`Extractable`: the single handle `⟨2, span{1, x₁}, X² + X⟩` accepts two different
values at one evaluation point, so no extracted table can answer for both.

Paired with `lchBasisBoundPcs_extractable`, this is the actual content of the
repair — the obligation is satisfiable with the ordered basis and refutable
without it, so it is a real check rather than a provable tautology. -/
theorem spanBoundPcs_not_extractable :
    ¬ (spanBoundPcs (F := binaryTower 2) keystoneBeta).Extractable := by
  intro hext
  obtain ⟨b, hb⟩ := exists_corner_tableOfPoly_ne
  obtain ⟨t, ht⟩ := hext (l := 2)
    (⟨2, additiveDomain keystoneBeta 2, sharedWord⟩ : SpanBoundRoot (binaryTower 2))
  have hA : mle t (cubePt b) = tableOfPoly 2 preA b := by
    refine ht (cubePt b) (tableOfPoly 2 preA b) ⟨rfl, keystoneBeta, ?_, rfl,
      tableOfPoly 2 preA, novelPack_table_preA, ?_⟩
    · exact keystoneBeta_linearIndependent
    · exact mle_agrees _ b
  have hB : mle t (cubePt b) = tableOfPoly 2 preB b := by
    refine ht (cubePt b) (tableOfPoly 2 preB b) ⟨rfl, keystoneBetaSwap, ?_, ?_,
      tableOfPoly 2 preB, novelPack_table_preB, ?_⟩
    · exact keystoneBetaSwap_linearIndependent
    · exact keystoneBetaSwap_additiveDomain
    · exact mle_agrees _ b
  exact hb (hA.symm.trans hB)

/-! ## 5. Teeth

The repaired binding must ACCEPT the honest commitment and REFUSE the reordered
sibling. A refusal that comes from refusing everything is worthless, and a
mutation that has stopped mutating reads as a passing test, so both halves are
asserted: the reordering is a real change (`keystoneBeta ≠ keystoneBetaSwap`)
that the OLD binding provably cannot see (`keystoneBetaSwap_additiveDomain`),
and the NEW handles differ because of it. -/

/-- **The mutation is real, and the old binding is blind to it.** Assert this
before reading any verdict below: the two bases are different functions, and yet
their `additiveDomain`s — everything a domain-bound transcript records — are
equal. If either half ever became false, the teeth would be measuring nothing. -/
theorem keystone_reordering_is_a_real_mutation :
    keystoneBeta ≠ keystoneBetaSwap ∧
      additiveDomain keystoneBetaSwap 2 = additiveDomain keystoneBeta 2 := by
  refine ⟨fun h => ?_, keystoneBetaSwap_additiveDomain⟩
  have h0 : (1 : binaryTower 2) = fpGen 1 := congrFun h 0
  exact fpGen_ne_one 1 h0.symm

/-- ⭐ **TOOTH 1 — the honest commitment is still ACCEPTED.** The repaired scheme
accepts the true evaluation of the true table at every point; the fix is not a
blanket refusal. -/
theorem tooth_honest_accepted (r : Fin 2 → binaryTower 2) :
    (lchBasisBoundPcs keystoneBeta).accepts
      ((lchBasisBoundPcs keystoneBeta).commit (tableOfPoly 2 preA)) r
      (mle (tableOfPoly 2 preA) r) :=
  lchBasisBoundPcs_complete keystoneBeta (tableOfPoly 2 preA) r

/-- ⭐ **TOOTH 2 — the reordered sibling is REFUSED.** `preB`'s reading of the
shared codeword is not an opening of the honest handle: the handle carries
`(1, x₁)`, and no table packs to `X² + X` under `(1, x₁)` except `preA`'s. Under
the old span-indexed handle this same pair was accepted
(`spanBoundPcs_not_extractable`'s `hB`), which is what makes this a tooth and not
a restatement. -/
theorem tooth_reordered_refused (r : Fin 2 → binaryTower 2) :
    ¬ (lchBasisBoundPcs keystoneBeta).accepts
        ((lchBasisBoundPcs keystoneBeta).commit (tableOfPoly 2 preA)) r
        (mle (tableOfPoly 2 preB) r) ∨
      mle (tableOfPoly 2 preA) r = mle (tableOfPoly 2 preB) r := by
  classical
  by_cases hval : mle (tableOfPoly 2 preA) r = mle (tableOfPoly 2 preB) r
  · exact Or.inr hval
  · refine Or.inl fun hacc => hval ?_
    obtain ⟨-, u, hu, hmle⟩ := hacc
    have hut : u = tableOfPoly 2 preA :=
      table_unique_of_novelPack_eq keystoneBeta 2 u (tableOfPoly 2 preA) hu
    rw [← hmle, hut]

/-- ⭐ **TOOTH 2, the sharp form.** At the corner where the two tables disagree
the refusal is unconditional: the honest handle rejects `preB`'s value outright. -/
theorem tooth_reordered_refused_at_corner :
    ∃ r : Fin 2 → binaryTower 2,
      (lchBasisBoundPcs keystoneBeta).accepts
          ((lchBasisBoundPcs keystoneBeta).commit (tableOfPoly 2 preA)) r
          (mle (tableOfPoly 2 preA) r) ∧
        ¬ (lchBasisBoundPcs keystoneBeta).accepts
            ((lchBasisBoundPcs keystoneBeta).commit (tableOfPoly 2 preA)) r
            (mle (tableOfPoly 2 preB) r) := by
  obtain ⟨b, hb⟩ := exists_corner_tableOfPoly_ne
  refine ⟨cubePt b, tooth_honest_accepted (cubePt b), fun hacc => ?_⟩
  obtain ⟨-, u, hu, hmle⟩ := hacc
  have hut : u = tableOfPoly 2 preA :=
    table_unique_of_novelPack_eq keystoneBeta 2 u (tableOfPoly 2 preA) hu
  rw [hut] at hmle
  rw [mle_agrees, mle_agrees] at hmle
  exact hb hmle

/-- ⭐ **TOOTH 3 — the two handles are DIFFERENT.** The keystone's two readings,
which the domain-bound transcript could not tell apart, now land on different
handles, and the difference is exactly the `basis` field. -/
theorem tooth_handles_differ :
    ((lchBasisBoundPcs keystoneBeta).commit (tableOfPoly 2 preA) :
        BasisBoundRoot (binaryTower 2))
      ≠ (lchBasisBoundPcs keystoneBetaSwap).commit (tableOfPoly 2 preB) := by
  intro h
  exact keystone_reordering_is_a_real_mutation.1
    (congrArg BasisBoundRoot.basis h)

/-- ⭐ **TOOTH 3, and the words really were the same.** The handles differ ONLY in
the basis field: the committed codewords are literally equal, which is what makes
`tooth_handles_differ` a statement about the binding rather than about the data. -/
theorem tooth_words_agree :
    ((lchBasisBoundPcs keystoneBeta).commit (tableOfPoly 2 preA) :
        BasisBoundRoot (binaryTower 2)).word
      = ((lchBasisBoundPcs keystoneBetaSwap).commit (tableOfPoly 2 preB) :
          BasisBoundRoot (binaryTower 2)).word :=
  novelPack_table_preA.trans novelPack_table_preB.symm

end SpanBoundRefutation

/-! ## 6. Axiom pins -/

/-- info: 'Minidregg.Selvage.table_unique_of_novelPack_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms table_unique_of_novelPack_eq
/-- info: 'Minidregg.Selvage.novelPack_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms novelPack_congr
/-- info: 'Minidregg.Selvage.table_unique_of_basis_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms table_unique_of_basis_agree
/-- info: 'Minidregg.Selvage.lchCommit_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lchCommit_injective
/-- info: 'Minidregg.Selvage.no_span_indexed_decoder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_span_indexed_decoder
/-- info: 'Minidregg.Selvage.lchBasisBoundPcs_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lchBasisBoundPcs_complete
/-- info: 'Minidregg.Selvage.lchBasisBoundPcs_extractable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lchBasisBoundPcs_extractable
/-- info: 'Minidregg.Selvage.lchRingSwitchTarget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lchRingSwitchTarget
/-- info: 'Minidregg.Selvage.spanBoundPcs_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms spanBoundPcs_complete
/-- info: 'Minidregg.Selvage.spanBoundPcs_not_extractable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms spanBoundPcs_not_extractable
/-- info: 'Minidregg.Selvage.keystone_reordering_is_a_real_mutation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms keystone_reordering_is_a_real_mutation
/-- info: 'Minidregg.Selvage.tooth_honest_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_honest_accepted
/-- info: 'Minidregg.Selvage.tooth_reordered_refused_at_corner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_reordered_refused_at_corner
/-- info: 'Minidregg.Selvage.tooth_handles_differ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_handles_differ
/-- info: 'Minidregg.Selvage.tooth_words_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_words_agree

end Minidregg.Selvage
