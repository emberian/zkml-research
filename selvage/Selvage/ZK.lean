/-
# Selvage.ZK — OB-4, the disclosure layer: the ported architecture and the
word-level hiding shell of the masked γ-fold.

**OB-4 is a contribution slot, confirmed ABSENT from the literature**
(docs/SELVAGE-RECOMPOSITION.md §4): neither WARP nor Arc has any ZK — salt-zero
Merkle commitments, `t` codeword symbols leaked per accumulation step, no
sketch of a simulator — and 2026/289's concrete zk machinery is
Pedersen-homomorphic with rewinding extraction (4m-transcript trees,
expected-PPT), disqualified twice over for a hash-based straightline stack.
**ZK for hash-based straightline accumulation does not exist. That is Selvage's
open problem.** This file builds what genuinely closes today and confines the
open mathematics to the honest prose residual `[OB-4-hiding]` at the bottom —
most of OB-4 lives THERE, and saying so is the point of a contribution slot.

What PORTS from 2026/289 (the generic layer only — none of their Pedersen /
rewinding machinery):

* **The compliance/accumulation separation** (their Thm 1, fully generic): the
  per-step recursive relation splits into a compliance predicate φ (carried by
  a SMALL zk proof) and the accumulation-verifier's check (public, non-zk), so
  zk confines to the compliance proof plus zk of the accumulation SCHEME in
  the strengthened sense — the simulator produces the accumulator AND the
  accumulation proof. This kills the O(2^d) masking blowup of a monolithic
  zk-NARK over the recursion. Here: `ComplianceSplit`, with the split's
  exactness a REAL theorem field, instantiated on the actual append algebra
  (`AccClaim.append_satisfies_iff` — a new app constraint joining the running
  claim IS the compliance side; LOOM §6's "a pin is itself a CRS constraint").

* **Idea (a) — mask by folding in ONE uniformly random satisfying pair** to
  randomize the output accumulator. Cheap on our substrate: the folded word is
  recommitted every step anyway (WARP's schedule; `foldRoot` in
  `Selvage/Accumulator.lean`). This file PROVES its algebraic core, RE-DERIVED on
  our fold (not cited from their rewinding proof): for `γ ≠ 0` the masking map
  `g ↦ f + γ • g` — literally the fold's word operation, the witness of
  `foldClaims_satisfies` — is a BIJECTION from the satisfying set of the mask
  claim onto the satisfying set of the PUBLIC folded claim (`mask_bijOn`,
  `maskEquiv`). Consequence, stated in exact counting form with no probability
  scaffolding: pushing a uniformly random satisfying mask through the fold
  gives the uniform distribution on the folded claim's satisfying set — every
  folded-satisfying output has EXACTLY ONE explaining mask
  (`exists_unique_mask`), non-satisfying outputs have none
  (`not_exists_mask_of_not_satisfies`), and the support depends only on
  PUBLIC data, never on the secret witness (`ZkAccScheme.witness_free`).
  That is a perfect (information-theoretic, distribution-equality)
  word-level simulator: sample uniformly from `simSupport` — the satisfying
  set of the folded claim, computable from the claim alone.

* Idea (b) — zk-sumcheck masking (CFS17/XZZ+19 with the KS24 point-update;
  mask size O(d·m), not O(n)) — belongs to the sumcheck front
  (`Selvage/Sumcheck.lean`), NOT to this file's fold algebra; it is named in
  `[OB-4-hiding]` below, unbuilt.

**Honest scope.** What is proved here is hiding of the folded WORD only. The
commitment root stays opaque (hiding of `rt` is the commitment layer's
obligation, dual to the binding consumed by `[ACC-extract]`), and the spot-
check opening leakage — the `t` symbols per step that make WARP/Arc non-zk —
is not modeled at all: that is the genuinely new mathematics, `[OB-4-hiding]`.
No `sorry`, no vacuous `Prop := True`: everything below either carries a
proof or is prose.

Keystones (ATLAS law 2) over the F₅ code of `RSExample`, reusing
`AccExample`'s claims: the scheme property is INHABITED at every nonzero
challenge and REFUTED at γ = 0 — sharp iff `zkAccScheme_F5_iff`: the mask is
load-bearing, not decorative.
-/
import Mathlib.Data.Set.Card
import Selvage.Accumulator

namespace Minidregg.Selvage

variable {Root : Type*} {F : Type*} [Field F] {ι : Type*} {r r₁ r₂ : ℕ}

/-! ## The compliance/accumulation separation (2026/289 Thm 1, the generic part)

The architecture that ports: split the per-step relation so that the zk
burden confines to a SMALL compliance proof, while the accumulation-verifier
check stays public and non-zk. The split itself is generic and exact — a
structure whose keystone field is the real iff, not a `True` stub. -/

/-- **The compliance split** — 2026/289 Thm 1's generic shape: a step relation
`rel` factors EXACTLY into a compliance predicate (the application-side
constraints, carried by the small zk proof) and the accumulation-verifier's
public check. `split_iff` is the load-bearing field: the factorization is an
iff, so nothing of the relation escapes the two sides. -/
structure ComplianceSplit (Wit : Type*) where
  /-- The step's total relation. -/
  rel : Wit → Prop
  /-- The compliance side φ — proved by the small zk proof. -/
  compliance : Wit → Prop
  /-- The accumulation-verifier's check — public, non-zk. -/
  accCheck : Wit → Prop
  /-- Exactness of the split. -/
  split_iff : ∀ w, rel w ↔ compliance w ∧ accCheck w

/-- The split instantiated on the REAL accumulation algebra: one step's total
relation — the witness satisfies the running claim WITH the new application
constraints appended (`AccClaim.append`, LOOM §6's seqDescr accumulation) —
factors exactly into the app-side compliance (`B`) and the public running
check (`A`), by `AccClaim.append_satisfies_iff` verbatim. The zk layer below
masks the witness this relation constrains; the small zk proof OF the
compliance side is `[OB-4-hiding]` scope. -/
def foldStepSplit (C : Submodule F (ι → F)) (A : AccClaim Root F ι r₁)
    (B : AccClaim Root F ι r₂) : ComplianceSplit (ι → F) where
  rel f := AccClaim.Satisfies C (A.append B) f
  compliance f := AccClaim.Satisfies C B f
  accCheck f := AccClaim.Satisfies C A f
  split_iff _ := AccClaim.append_satisfies_iff.trans and_comm

/-! ## The masking map and its inverse

Idea (a)'s algebra: the mask IS the fold's word operation. Nothing new is
folded — the map below is exactly the witness constructor of
`foldClaims_satisfies`, read as a function of the mask word `g`. -/

/-- **The masking map**: randomize the running witness `f` by folding in a
mask word `g` at challenge `γ` — the fold's word operation `f + γ • g`
(`foldClaims_satisfies`' witness), as a function of the MASK. -/
def mask (f : ι → F) (γ : F) (g : ι → F) : ι → F := f + γ • g

/-- The inverse of the masking map at `γ ≠ 0`: recover the mask from the
masked output. -/
def unmask (f : ι → F) (γ : F) (h : ι → F) : ι → F := γ⁻¹ • (h - f)

@[simp] theorem mask_apply (f : ι → F) (γ : F) (g : ι → F) :
    mask f γ g = f + γ • g := rfl

theorem unmask_mask {γ : F} (hγ : γ ≠ 0) (f g : ι → F) :
    unmask f γ (mask f γ g) = g := by
  simp only [unmask, mask, add_sub_cancel_left, inv_smul_smul₀ hγ]

theorem mask_unmask {γ : F} (hγ : γ ≠ 0) (f h : ι → F) :
    mask f γ (unmask f γ h) = h := by
  simp only [mask, unmask, smul_inv_smul₀ hγ, add_sub_cancel]

/-- For `γ ≠ 0` the masking map is injective — the randomizer genuinely
permutes, never merges (the left inverse is `unmask`). -/
theorem mask_injective {γ : F} (hγ : γ ≠ 0) (f : ι → F) :
    Function.Injective (mask f γ) :=
  Function.LeftInverse.injective (g := unmask f γ) (unmask_mask hγ f)

/-- **The γ = 0 degeneration**: without a genuine challenge the "mask" is the
constant map — the output IS the secret witness, verbatim. Total leakage;
the teeth theorems below turn this into a refutation of the scheme property
at γ = 0. -/
theorem mask_zero (f : ι → F) : mask f (0 : F) = fun _ => f := by
  funext g; simp [mask]

/-! ## Satisfying sets: the sample space and the simulator's support -/

/-- The satisfying set of a claim — the set the mask word ranges over
(uniformly, in the distribution reading) and, for the FOLDED claim, the
simulator's support. -/
def satWords (C : Submodule F (ι → F)) (A : AccClaim Root F ι r) :
    Set (ι → F) :=
  {f | AccClaim.Satisfies C A f}

@[simp] theorem mem_satWords {C : Submodule F (ι → F)}
    {A : AccClaim Root F ι r} {f : ι → F} :
    f ∈ satWords C A ↔ AccClaim.Satisfies C A f := Iff.rfl

/-! ## The randomizing bijection — idea (a), proved -/

section Fold

variable (foldRoot : Root → F → Root → Root)

/-- The surjectivity half's algebraic content: from any word satisfying the
FOLDED claim, `unmask` recovers a word satisfying the mask claim `B` —
membership by linearity of the code, constraints by γ-linearity of the
channel (the same shared-functional alignment `hshare` as
`foldClaims_satisfies`, this time run backwards at `γ⁻¹`). -/
theorem unmask_satisfies {C : Submodule F (ι → F)} {A B : AccClaim Root F ι r}
    {f h : ι → F} {γ : F} (hγ : γ ≠ 0)
    (hshare : ∀ i, B.weights i = A.weights i)
    (hf : AccClaim.Satisfies C A f)
    (hh : AccClaim.Satisfies C (foldClaims foldRoot A B γ) h) :
    AccClaim.Satisfies C B (unmask f γ h) := by
  refine ⟨C.smul_mem _ (C.sub_mem hh.1 hf.1), fun i => ?_⟩
  have hAh : A.weights i h = A.targets i + γ * B.targets i := hh.2 i
  rw [hshare i]
  have hstep : A.weights i (unmask f γ h)
      = γ⁻¹ * (A.weights i h - A.weights i f) := by
    simp only [unmask, map_smul, map_sub, smul_eq_mul]
  rw [hstep, hf.2 i, hAh, add_sub_cancel_left, inv_mul_cancel_left₀ hγ]

/-- **The randomizing bijection** (idea (a), the portable core): for `γ ≠ 0`
and a secret witness `f` of the running accumulator, the masking map
`g ↦ f + γ • g` is a bijection from the satisfying set of the mask claim `B`
ONTO the satisfying set of the PUBLIC folded claim. Forward is exactly
`foldClaims_satisfies` (reused, not re-derived); backward is `unmask`.
Distribution reading: a uniformly random satisfying mask pushes forward to
the uniform distribution on the folded claim's satisfying set — a set the
simulator can name without ever seeing `f`. -/
theorem mask_bijOn {C : Submodule F (ι → F)} {A B : AccClaim Root F ι r}
    {f : ι → F} {γ : F} (hγ : γ ≠ 0)
    (hshare : ∀ i, B.weights i = A.weights i)
    (hf : AccClaim.Satisfies C A f) :
    Set.BijOn (mask f γ) (satWords C B)
      (satWords C (foldClaims foldRoot A B γ)) := by
  refine ⟨fun g hg => foldClaims_satisfies foldRoot γ hshare hf hg,
    (mask_injective hγ f).injOn, fun h hh => ?_⟩
  exact ⟨unmask f γ h, unmask_satisfies foldRoot hγ hshare hf hh,
    mask_unmask hγ f h⟩

/-- The bijection as an `Equiv` of subtypes — mask words correspond one-to-one
with folded-satisfying outputs, with `unmask` the explicit inverse. -/
def maskEquiv {C : Submodule F (ι → F)} {A B : AccClaim Root F ι r}
    {f : ι → F} {γ : F} (hγ : γ ≠ 0)
    (hshare : ∀ i, B.weights i = A.weights i)
    (hf : AccClaim.Satisfies C A f) :
    satWords C B ≃ satWords C (foldClaims foldRoot A B γ) where
  toFun g := ⟨mask f γ g, foldClaims_satisfies foldRoot γ hshare hf g.2⟩
  invFun h := ⟨unmask f γ h, unmask_satisfies foldRoot hγ hshare hf h.2⟩
  left_inv g := Subtype.ext (unmask_mask hγ f g)
  right_inv h := Subtype.ext (mask_unmask hγ f h)

/-- **Uniformity, exact counting form**: every output satisfying the folded
claim is explained by EXACTLY ONE satisfying mask. With
`not_exists_mask_of_not_satisfies` this is the whole pushforward
distribution: `Pr[output = h] = 1/|satWords C B|` on the folded satisfying
set, `0` off it — uniform on public support, no probability scaffolding
needed to say so. -/
theorem exists_unique_mask {C : Submodule F (ι → F)}
    {A B : AccClaim Root F ι r} {f h : ι → F} {γ : F} (hγ : γ ≠ 0)
    (hshare : ∀ i, B.weights i = A.weights i)
    (hf : AccClaim.Satisfies C A f)
    (hh : AccClaim.Satisfies C (foldClaims foldRoot A B γ) h) :
    ∃! g, g ∈ satWords C B ∧ mask f γ g = h := by
  refine ⟨unmask f γ h,
    ⟨unmask_satisfies foldRoot hγ hshare hf hh, mask_unmask hγ f h⟩, ?_⟩
  rintro g ⟨-, hg⟩
  rw [← hg, unmask_mask hγ]

/-- The off-support count is zero: no satisfying mask reaches an output that
violates the folded claim (this is `foldClaims_satisfies` in contrapositive —
completeness needs no `γ ≠ 0`). -/
theorem not_exists_mask_of_not_satisfies {C : Submodule F (ι → F)}
    {A B : AccClaim Root F ι r} {f h : ι → F} {γ : F}
    (hshare : ∀ i, B.weights i = A.weights i)
    (hf : AccClaim.Satisfies C A f)
    (hh : ¬ AccClaim.Satisfies C (foldClaims foldRoot A B γ) h) :
    ¬ ∃ g ∈ satWords C B, mask f γ g = h := by
  rintro ⟨g, hg, rfl⟩
  exact hh (foldClaims_satisfies foldRoot γ hshare hf hg)

/-! ## The simulation statement: `ZkAccScheme` -/

/-- **The simulator's support** — the satisfying set of the FOLDED claim.
Every datum on the right-hand side is public: the code, the two claims, the
challenge. The secret witness `f` does not occur; that absence IS the
simulation content, made syntactic. -/
def simSupport (C : Submodule F (ι → F)) (A B : AccClaim Root F ι r)
    (γ : F) : Set (ι → F) :=
  satWords C (foldClaims foldRoot A B γ)

/-- **Word-level zk of the accumulation scheme** (the strengthened sense of
2026/289, restricted to the layer our substrate models today: the folded
WORD; roots and opening transcripts are `[OB-4-hiding]`). Two keystone
fields, both real:

* `sim_support_eq` — for EVERY secret witness of the running accumulator, the
  reachable masked outputs are exactly `simSupport`, a public set: the
  simulator that samples uniformly from `simSupport` has the right support,
  and the support cannot depend on the witness;
* `mask_injOn` — distinct masks give distinct outputs, so the pushforward of
  the uniform mask distribution is UNIFORM on that support: real and
  simulated distributions coincide exactly (perfect, not computational).

Together these are `Set.BijOn` (`zkAccScheme_iff_bijOn`), split so each
field states one face of the simulation argument. -/
structure ZkAccScheme (C : Submodule F (ι → F))
    (foldRoot : Root → F → Root → Root) (A B : AccClaim Root F ι r)
    (γ : F) : Prop where
  sim_support_eq : ∀ f, AccClaim.Satisfies C A f →
    mask f γ '' satWords C B = simSupport foldRoot C A B γ
  mask_injOn : ∀ f, AccClaim.Satisfies C A f →
    Set.InjOn (mask f γ) (satWords C B)

/-- **The hiding shell, proved**: at every nonzero challenge, the masked fold
is word-level zk — the bijection theorem packaged as the scheme property. -/
theorem zkAccScheme_of_ne_zero {C : Submodule F (ι → F)}
    {A B : AccClaim Root F ι r} {γ : F} (hγ : γ ≠ 0)
    (hshare : ∀ i, B.weights i = A.weights i) :
    ZkAccScheme C foldRoot A B γ where
  sim_support_eq _ hf := (mask_bijOn foldRoot hγ hshare hf).image_eq
  mask_injOn _ _ := (mask_injective hγ _).injOn

variable {foldRoot}

/-- The scheme property is exactly the bijection, for every witness. -/
theorem zkAccScheme_iff_bijOn {C : Submodule F (ι → F)}
    {A B : AccClaim Root F ι r} {γ : F} :
    ZkAccScheme C foldRoot A B γ ↔
      ∀ f, AccClaim.Satisfies C A f →
        Set.BijOn (mask f γ) (satWords C B)
          (satWords C (foldClaims foldRoot A B γ)) := by
  constructor
  · rintro ⟨hsim, hinj⟩ f hf
    refine ⟨fun g hg => ?_, hinj f hf, fun h hh => ?_⟩
    · have h1 : mask f γ g ∈ mask f γ '' satWords C B :=
        Set.mem_image_of_mem _ hg
      rwa [hsim f hf] at h1
    · have h1 : h ∈ simSupport foldRoot C A B γ := hh
      rwa [← hsim f hf] at h1
  · intro hb
    exact ⟨fun f hf => (hb f hf).image_eq, fun f hf => (hb f hf).injOn⟩

/-- **Witness independence** — the simulation reading made pointwise: two
provers holding DIFFERENT secret witnesses of the same accumulator produce
identically distributed masked outputs (equal supports; uniformity is
`mask_injOn`). The distinguisher learns nothing about which witness was
held. -/
theorem ZkAccScheme.witness_free {C : Submodule F (ι → F)}
    {A B : AccClaim Root F ι r} {γ : F}
    (hZ : ZkAccScheme C foldRoot A B γ) {f₁ f₂ : ι → F}
    (h₁ : AccClaim.Satisfies C A f₁) (h₂ : AccClaim.Satisfies C A f₂) :
    mask f₁ γ '' satWords C B = mask f₂ γ '' satWords C B := by
  rw [hZ.sim_support_eq f₁ h₁, hZ.sim_support_eq f₂ h₂]

/-- The counting corollary: the public support has exactly as many words as
the mask space — the uniform simulator's denominator is the mask space's
size. -/
theorem ncard_simSupport {C : Submodule F (ι → F)}
    {A B : AccClaim Root F ι r} {f : ι → F} {γ : F} (hγ : γ ≠ 0)
    (hshare : ∀ i, B.weights i = A.weights i)
    (hf : AccClaim.Satisfies C A f) :
    (simSupport foldRoot C A B γ).ncard = (satWords C B).ncard := by
  rw [simSupport, ← (mask_bijOn foldRoot hγ hshare hf).image_eq,
    Set.InjOn.ncard_image (mask_injective hγ f).injOn]

end Fold

/-! ## Teeth for the mask itself: γ = 0 leaks -/

/-- At γ = 0 the image of ANY nonempty mask space collapses to the secret
witness alone: the output support is `{f}` — the "masked" output publishes
the witness. -/
theorem image_mask_zero {C : Submodule F (ι → F)} {B : AccClaim Root F ι r}
    (f : ι → F) (hB : (satWords C B).Nonempty) :
    mask f 0 '' satWords C B = {f} := by
  rw [mask_zero]; exact hB.image_const f

/-- **The mask is load-bearing**: at γ = 0 the output supports of two provers
holding distinct witnesses are DISTINCT singletons — the distinguisher reads
the witness off the output. Contrast `ZkAccScheme.witness_free` at `γ ≠ 0`. -/
theorem mask_zero_witness_dependent {C : Submodule F (ι → F)}
    {B : AccClaim Root F ι r} {f₁ f₂ : ι → F}
    (hB : (satWords C B).Nonempty) (hne : f₁ ≠ f₂) :
    mask f₁ (0 : F) '' satWords C B ≠ mask f₂ 0 '' satWords C B := by
  rw [image_mask_zero f₁ hB, image_mask_zero f₂ hB]
  simpa using hne

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

Over `RS[F₅, {0,1,2,3}, 2]` (`RSExample`), reusing `AccExample`'s running
accumulator `evalA` (the constraint `f 2 = 2`) and mask claim `evalB1`
(`f 2 = 1`, shared functional — the post-alignment state), with two genuinely
distinct secret witnesses of `evalA` and two genuinely distinct satisfying
masks:

* **satisfiable / premise inhabitation** — `zkAccScheme_F5`: the scheme
  property FIRES at every nonzero challenge with all hypotheses concretely
  discharged; `exists_unique_mask_F5` instantiates the uniqueness theorem at
  a computed masked output (`fold_honest_nonzero`'s witness). The bijection
  is genuine and computes: `mask_roundtrip_F5` runs `unmask ∘ mask` to the
  identity by `decide`, and `masked_value_F5` computes the masked word.
* **teeth** — the mask genuinely permutes: two distinct satisfying masks give
  distinct outputs (`mask_outputs_distinct_F5`, by `decide`); and the mask is
  non-trivial: at γ = 0 the outputs of the two witnesses are distinguishable
  (`leak_at_zero_F5`), refuting the scheme property. Sharp:
  `zkAccScheme_F5_iff` — word-level zk holds IFF γ ≠ 0. -/

namespace ZkExample

open RSExample AccExample

/-- A second secret witness of `evalA`: the constant-2 word, evaluations of
`C 2` — a genuine codeword with `q2 twoWord = 2`, distinct from `xWord`. -/
def twoWord : Fin 4 → ZMod 5 := fun _ => 2

theorem twoWord_mem : twoWord ∈ reedSolomonCode dom₅ 2 :=
  mem_reedSolomonCode_iff.mpr
    ⟨Polynomial.C 2,
      by rw [Polynomial.degree_C (by decide : (2 : ZMod 5) ≠ 0)]; decide,
      fun i => by simp [twoWord]⟩

theorem xWord_sat_evalA :
    AccClaim.Satisfies (reedSolomonCode dom₅ 2) evalA xWord :=
  ⟨xWord_mem, fun _ => q2_xWord⟩

theorem twoWord_sat_evalA :
    AccClaim.Satisfies (reedSolomonCode dom₅ 2) evalA twoWord :=
  ⟨twoWord_mem, fun _ => rfl⟩

theorem oneWord_sat_evalB1 :
    AccClaim.Satisfies (reedSolomonCode dom₅ 2) evalB1 oneWord :=
  ⟨oneWord_mem, fun _ => rfl⟩

/-- A second satisfying mask: evaluations of `X + 4` — a genuine codeword
with `q2 slopeWord = 2 + 4 = 1`, distinct from `oneWord`. -/
def slopeWord : Fin 4 → ZMod 5 := fun i => (i.val : ZMod 5) + 4

theorem slopeWord_mem : slopeWord ∈ reedSolomonCode dom₅ 2 :=
  mem_reedSolomonCode_iff.mpr
    ⟨Polynomial.X + Polynomial.C 4,
      by rw [Polynomial.degree_X_add_C]; decide,
      fun i => by simp [slopeWord, dom₅]⟩

theorem slopeWord_sat_evalB1 :
    AccClaim.Satisfies (reedSolomonCode dom₅ 2) evalB1 slopeWord :=
  ⟨slopeWord_mem, fun _ => show q2 slopeWord = 1 by decide⟩

/-- **Premise inhabitation / satisfiable**: the hiding shell FIRES on the F₅
claims at every nonzero challenge — running accumulator `evalA`, mask claim
`evalB1`, shared channel discharged by `rfl`. -/
theorem zkAccScheme_F5 {γ : ZMod 5} (hγ : γ ≠ 0) :
    ZkAccScheme (reedSolomonCode dom₅ 2) trivialRoot evalA evalB1 γ :=
  zkAccScheme_of_ne_zero trivialRoot hγ (fun _ => rfl)

/-- The masked word, computed: `xWord + 2 • oneWord = (2, 3, 4, 0)`. -/
theorem masked_value_F5 : mask xWord 2 oneWord = ![2, 3, 4, 0] := by decide

/-- The bijection computes: `unmask` genuinely inverts `mask` on concrete
words, by `decide`. -/
theorem mask_roundtrip_F5 : unmask xWord 2 (mask xWord 2 oneWord) = oneWord := by
  decide

/-- Two genuinely distinct satisfying masks... -/
theorem masks_distinct_F5 : oneWord ≠ slopeWord := by decide

/-- ...map to distinct outputs: the randomizer permutes, never merges
(`mask_injective` witnessed concretely, by `decide`). -/
theorem mask_outputs_distinct_F5 :
    mask xWord 2 oneWord ≠ mask xWord 2 slopeWord := by decide

/-- The uniqueness theorem instantiated at a computed output: the masked word
`xWord + 2 • oneWord` (satisfying the folded claim by
`fold_honest_nonzero`) is explained by EXACTLY ONE satisfying mask. -/
theorem exists_unique_mask_F5 :
    ∃! g, g ∈ satWords (reedSolomonCode dom₅ 2) evalB1 ∧
      mask xWord 2 g = xWord + (2 : ZMod 5) • oneWord :=
  exists_unique_mask (A := evalA) (B := evalB1) (γ := 2) trivialRoot
    (by decide) (fun _ => rfl) xWord_sat_evalA (fold_honest_nonzero 2)

/-- **Witness independence at γ ≠ 0**: the two distinct secret witnesses
`xWord` and `twoWord` of `evalA` produce IDENTICAL masked-output supports —
the distinguisher cannot tell which was held. -/
theorem witness_independent_F5 {γ : ZMod 5} (hγ : γ ≠ 0) :
    mask xWord γ '' satWords (reedSolomonCode dom₅ 2) evalB1
      = mask twoWord γ '' satWords (reedSolomonCode dom₅ 2) evalB1 :=
  (zkAccScheme_F5 hγ).witness_free xWord_sat_evalA twoWord_sat_evalA

/-- **Teeth at γ = 0**: without the mask the two witnesses' outputs are
distinguishable — the supports differ (they are the distinct singletons
`{xWord}` and `{twoWord}`). -/
theorem leak_at_zero_F5 :
    mask xWord (0 : ZMod 5) '' satWords (reedSolomonCode dom₅ 2) evalB1
      ≠ mask twoWord 0 '' satWords (reedSolomonCode dom₅ 2) evalB1 :=
  mask_zero_witness_dependent ⟨oneWord, oneWord_sat_evalB1⟩ (by decide)

/-- **Sharp**: on the F₅ instance, word-level zk of the masked fold holds IFF
the challenge is nonzero — the hiding shell is exactly as strong as the mask
is genuine. -/
theorem zkAccScheme_F5_iff (γ : ZMod 5) :
    ZkAccScheme (reedSolomonCode dom₅ 2) trivialRoot evalA evalB1 γ ↔ γ ≠ 0 := by
  constructor
  · intro hZ hγ0
    subst hγ0
    exact leak_at_zero_F5 (hZ.witness_free xWord_sat_evalA twoWord_sat_evalA)
  · exact zkAccScheme_F5

/-- The compliance split fires on the real algebra: `xWord` inhabits the
total step relation (running claim `evalA` ⌢ the conservation constraint —
OB-3's app-side shape), and `split_iff` decomposes it exactly. -/
def consvClaim : AccClaim Unit (ZMod 5) (Fin 4) 1 := ⟨(), fun _ => (consv, 1)⟩

theorem foldStepSplit_fires :
    (foldStepSplit (reedSolomonCode dom₅ 2) evalA consvClaim).rel xWord :=
  AccClaim.append_satisfies_iff.mpr
    ⟨xWord_sat_evalA, ⟨xWord_mem, fun _ => consv_xWord⟩⟩

example :
    (foldStepSplit (reedSolomonCode dom₅ 2) evalA consvClaim).compliance xWord ∧
      (foldStepSplit (reedSolomonCode dom₅ 2) evalA consvClaim).accCheck xWord :=
  ((foldStepSplit _ evalA consvClaim).split_iff xWord).mp foldStepSplit_fires

end ZkExample

/-! ## Residual obligations — prose, not stubs

**[OB-4-hiding]** — hiding for the spot-check opening leakage, with a
straightline RBR proof. THE contribution slot (LOOM §4: confirmed absent from
the literature — this is Selvage's open problem, not a transcription task), and
most of OB-4's mass. What this file proved is the word-level shell: the
folded word's DISTRIBUTION is perfectly simulatable from public data. What it
deliberately does not touch, and what any real zk claim must close:

* **The leakage surface is the `t` spot-check symbols per step.** WARP/Arc's
  verifier opens `t` columns of EACH input word under salt-zero Merkle: the
  opened symbols are honest codeword coordinates of the PRE-mask words, and
  across `d` accumulation steps the `t·d` opened symbols of successive
  partial folds are correlated linear images of the secret witness. The mask
  above randomizes the post-fold word only — it says NOTHING about openings.
  Realizer path: masked openings / zk-code machinery — augment the working
  code so any `t` opened symbols of a committed word are uniform (a masking
  subcode / zk-augmentation `C' = C ⊕ M` with `t`-wise uniformity), and
  re-prove the fold soundness ROUND-BY-ROUND on the augmented code, because
  the straightline law (LOOM §2) forbids importing 2026/289's
  rewinding-based zk proof outright.
* **The simulator must produce the accumulator AND the accumulation proof**
  (the strengthened sense). At our resolution the accumulation proof
  includes the recommitment root `foldRoot A.rt γ B.rt`: `Root` is opaque
  here, so root-hiding (a hiding commitment — salted Merkle/BCS) is the
  commitment layer's obligation, dual to the binding consumed by
  `[ACC-extract]`, and joins this residual, not the fold algebra.
* **The sumcheck front leaks evaluations** (`Selvage/Sumcheck.lean`): idea (b),
  zk-sumcheck masking — mask the summed polynomial with a low-degree `G` of
  size O(d·m) (not O(n)), CFS17/XZZ+19 shape with the KS24 point-update to
  keep claim-state constant — belongs to this residual and must also be
  re-proved RBR-style.
* **The small compliance zk proof** of `ComplianceSplit.compliance` (the φ
  side of 2026/289 Thm 1): the split above confines the zk burden there;
  building that small proof (and its RBR/FS story) is residual scope.
* **Sampling the mask pair**: the prover needs one uniformly random
  satisfying word of the mask claim — for a CRS channel this is uniform
  sampling from an affine subspace (a solvable linear system), cheap
  precisely because the folded word is recommitted every step anyway
  (LOOM §4's "cheap here" remark); stating the sampler and its uniformity
  is part of this residual's bookkeeping, not new mathematics.

The shell proved here is the reusable floor for all of it: any masked-opening
design still folds the mask in by `g ↦ f + γ • g`, and `mask_bijOn` /
`ZkAccScheme` say that step, at least, hides perfectly.

`#print axioms` on `mask_bijOn`, `maskEquiv`, `exists_unique_mask`,
`zkAccScheme_of_ne_zero`, `ZkAccScheme.witness_free`, `ncard_simSupport`,
`mask_zero_witness_dependent`, `zkAccScheme_F5_iff`,
`exists_unique_mask_F5`, `foldStepSplit_fires`: `propext`,
`Classical.choice`, `Quot.sound` — no `sorryAx` anywhere in the file. -/

end Minidregg.Selvage
