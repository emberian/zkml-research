/-
# Selvage.CosetNovelTransform — the repaired Weft transform: evaluate OFF the window

`Selvage/AdditiveBaseFold.lean` proves `novelPack`: the LCH novelpoly packing of a
coefficient vector, linear, inside the degree window, and a BIJECTION of that window.
That object is the encoder of the additive (char-2) BaseFold line.  The Weft sketch
(`zkml-research/notes/aligned-hash-space.md` §3) proposed reusing it, unchanged, as the
MIXING LAYER of a char-2 algebraic hash — ONE proved linear object serving as both the
code's encoding map and the hash's diffusion layer.

That sketch was killed (`k16-proof-and-weft.md` §2), and the kill's stated reason —
"branch 6 against MDS 25" — was later found not to be the disqualifying fact.  What
actually breaks it is **the point set**, and this file is the theorem-level statement of
both the defect and the repair:

> The evaluation domain CONTAINED its own interpolation window.  The domain point `0`
> lies in the window, and `X̂₀ = 1`, so evaluation at `0` reads off the constant
> coefficient: **output lane 0 = input lane 0, exactly**.  That is
> `novelPack_eval_zero` below — proved for EVERY level `m` and EVERY ordered basis `β`,
> where the kill's own script measured one instance and its `range(1, 5)` skipped the
> level (`b = 0`) that reads it.

## The repair, and why it costs nothing

Evaluate on the affine COSET `x* + V` instead of on `V`.  `cosetPack β s m p` is that
transform, defined as `novelPack β m p ∘ (X + s)`, and:

* `cosetPack_shift_zero` — the killed form is the `s = 0` member of the SAME family.
  The repair is a one-parameter deformation, not a different object.
* ⭐ `cosetPack_succ` — **the free-ness theorem**.  The coset transform satisfies the
  same butterfly recursion as `novelPack_succ`, with two changes and no others: the
  shift folds to `q_{β₀}(s)` and the odd branch's multiplier `X` becomes `X + s`.  Same
  number of multiplications, same network — the `[DERIVED, standard]` "zero field ops"
  line of `notes/weft2.md` §4, machine-checked.
* Everything the code side needs is preserved and re-proved for the shifted transform:
  linearity, the degree window, injectivity and surjectivity ON the window, and the
  unique-table statement `exists_unique_table_cosetPack`.

## ⭐ THE ONE-OBJECT IDENTITY, made explicit rather than merely coexisting

`IsMixingLayer` and `IsEvaluationEncoder` are two independent obligations, and
`weft_one_object` inhabits BOTH with the SAME function.  The identity is not free, and
the tooth proves it: `weft_shift_zero_encodes_but_does_not_mix` shows the KILLED form
still satisfies the encoder obligation in full — it is a perfectly good additive-code
encoder — and is REFUSED the mixing-layer obligation, by the fixed lane.

## [WEFT-multiround] — the obligation the re-opening named, discharged on its quotient half

The kill's postmortem worry, stated exactly: *round constants break invariant SUBSPACES
but do NOT break invariant QUOTIENTS.*  `AutonomousSet f A` is the quotient notion — the
`A`-coordinates of the output are a function of the `A`-coordinates of the input, so the
round map DESCENDS to `K^A`.  Proved here, all general in the S-box, the round constants
and the round count:

* `autonomousSet_add_const` — a round constant CANNOT break an autonomous set; it merely
  becomes the quotient map's own constant.  This is the asymmetry the kill did not state.
* `autonomousSet_comp_lanewise` — neither can a lane-wise S-box, whatever it is.
* `autonomousSet_iterate` — so an autonomous set survives EVERY number of rounds.
* `weftRound_autonomous_shift_zero` — the killed form HAS one: `{0}`, at every `m`, every
  `β`, every S-box, every constant vector.  This is the b = 0 level.
* ⭐ `weftMix_no_autonomousSet` / `weftRound_no_autonomousSet` — the repaired form has
  NONE, at ANY level: for every nonempty proper `A`.  It follows from
  `cosetPack_monomial_eval_ne_zero` (every matrix entry is nonzero when the shift lies
  outside the window), which also gives `weftMix_single_full_support`: full diffusion in
  ONE round, hence no coordinate subspace trail of any length.

⚠ **Scope, stated not waived.** The families quantified over here are the COORDINATE
ones (lane sets).  General `K`-subspace trails, the block-constant family, and the
multi-round minimum active S-box count are NOT covered by anything below; they are
measured — for the deployed geometry only — in `~/src/ring-ro-hash/weft_coset_repair.py`
and reported in `zkml-research/notes/weft-coset-repair.md`.

**Substrate**: nothing here authors a constraint.  This is Lean-authored mathematics over
the proved Lean objects; if any of it ever becomes a circuit, the AIR is Lean-authored.
-/
import Selvage.AdditiveBaseFold

namespace Minidregg.Selvage

open Polynomial
open Minidregg.Theory

set_option autoImplicit false

variable {F : Type*} [Field F]

/-! ## §1 The repaired transform: the same packing, evaluated on a coset -/

/-- ⭐ **THE REPAIRED TRANSFORM.** The LCH packing composed with the translation
`X ↦ X + s`: `cosetPack β s m p` evaluated on the window `V` is `novelPack β m p`
evaluated on the affine coset `s + V` (`cosetPack_eval`).  The killed Weft mixing layer
is the member `s = 0`. -/
noncomputable def cosetPack (β : ℕ → F) (s : F) (m : ℕ) (p : F[X]) : F[X] :=
  (novelPack β m p).comp (X + C s)

/-- **The killed form is the `s = 0` member of the repaired family.**  The repair is a
one-parameter deformation of the object the kill studied, not a replacement for it. -/
@[simp] theorem cosetPack_shift_zero (β : ℕ → F) (m : ℕ) (p : F[X]) :
    cosetPack β 0 m p = novelPack β m p := by
  simp [cosetPack]

/-- **The point-set statement.** Evaluating the coset transform on the window is
evaluating the original packing on the coset. -/
@[simp] theorem cosetPack_eval (β : ℕ → F) (s : F) (m : ℕ) (p : F[X]) (x : F) :
    (cosetPack β s m p).eval x = (novelPack β m p).eval (x + s) := by
  simp [cosetPack, eval_comp]

@[simp] theorem cosetPack_zero (β : ℕ → F) (s : F) (p : F[X]) :
    cosetPack β s 0 p = C (p.coeff 0) := by
  simp [cosetPack]

/-- The translate of the fold polynomial is the fold polynomial plus a constant — the
one algebraic fact behind the free-ness theorem.  `q_β` is GF(2)-additive, so translating
its argument only shifts its value. -/
theorem foldPoly_comp_X_add_C [CharP F 2] (b s : F) :
    (foldPoly b).comp (X + C s) = foldPoly b + C (foldMap b s) := by
  have h2 : (2 : F[X]) = 0 := CharTwo.two_eq_zero
  simp only [foldPoly, foldMap, add_comp, mul_comp, pow_comp, X_comp, C_comp, map_add,
    map_mul, map_pow]
  linear_combination (X * C s : F[X]) * h2

/-- ⭐⭐ **THE FREE-NESS THEOREM — the repair is the SAME butterfly network.**

`cosetPack` satisfies the recursion of `novelPack_succ` with exactly two changes: the
shift folds to `q_{β₀}(s)` on the way down, and the odd branch's multiplier `X` becomes
`X + s`.  The number of multiplications and additions is identical — this is the
machine-checked form of "same butterflies, shifted twiddles, zero field ops"
(`notes/weft2.md` §4), which that note could only label `[DERIVED, standard]`. -/
theorem cosetPack_succ [CharP F 2] (β : ℕ → F) (s : F) (m : ℕ) (p : F[X]) :
    cosetPack β s (m + 1) p =
      (cosetPack (additiveFoldedBasis β) (foldMap (β 0) s) m (evenPart p)).comp
          (foldPoly (β 0))
        + (X + C s) *
            (cosetPack (additiveFoldedBasis β) (foldMap (β 0) s) m (oddPart p)).comp
              (foldPoly (β 0)) := by
  have key : ∀ A : F[X],
      (A.comp (foldPoly (β 0))).comp (X + C s)
        = (A.comp (X + C (foldMap (β 0) s))).comp (foldPoly (β 0)) := by
    intro A
    rw [comp_assoc, comp_assoc, foldPoly_comp_X_add_C]
    congr 1
    simp
  simp only [cosetPack, novelPack_succ, add_comp, mul_comp, X_comp, key]

/-! ### Linearity and the degree window — inherited, and re-stated for the repaired form -/

theorem cosetPack_add (β : ℕ → F) (s : F) (m : ℕ) (p q : F[X]) :
    cosetPack β s m (p + q) = cosetPack β s m p + cosetPack β s m q := by
  simp [cosetPack, novelPack_add, add_comp]

theorem cosetPack_C_mul (β : ℕ → F) (s : F) (m : ℕ) (a : F) (p : F[X]) :
    cosetPack β s m (C a * p) = C a * cosetPack β s m p := by
  simp [cosetPack, novelPack_C_mul, mul_comp]

/-- `novelPack` of the zero polynomial is zero (the `a = 0` case of `novelPack_C_mul`). -/
@[simp] theorem novelPack_zero_poly (β : ℕ → F) (m : ℕ) : novelPack β m (0 : F[X]) = 0 := by
  have h := novelPack_C_mul m β (0 : F) (0 : F[X])
  simpa using h

@[simp] theorem cosetPack_zero_poly (β : ℕ → F) (s : F) (m : ℕ) :
    cosetPack β s m (0 : F[X]) = 0 := by
  simp [cosetPack]

/-- **The repaired transform stays inside the same degree window.**  Composition with a
degree-1 polynomial does not move `natDegree`, so the base check of the low-degree test
is met by the coset form exactly as it is by `novelPack`. -/
theorem cosetPack_natDegree_lt (β : ℕ → F) (s : F) (m : ℕ) (p : F[X]) :
    (cosetPack β s m p).natDegree < 2 ^ m := by
  have hd : (X + C s : F[X]).natDegree = 1 := by
    simpa using natDegree_X_add_C (x := s)
  have := natDegree_comp (p := novelPack β m p) (q := (X + C s : F[X]))
  rw [cosetPack, this, hd, mul_one]
  exact novelPack_natDegree_lt m β p

/-- ⭐ **THE REPAIRED TRANSFORM IS STILL A BIJECTION OF THE WINDOW — injective half.**
This is the code-side prize, transported: translation is an automorphism of `F[X]`, so
the proved injectivity of `novelPack` on the window carries over unchanged. -/
theorem cosetPack_injective_of_natDegree_lt {m : ℕ} {β : ℕ → F} {s : F} {p q : F[X]}
    (hp : p.natDegree < 2 ^ m) (hq : q.natDegree < 2 ^ m)
    (h : cosetPack β s m p = cosetPack β s m q) : p = q := by
  refine novelPack_injective_of_natDegree_lt (β := β) hp hq ?_
  have := congrArg (fun r : F[X] => r.comp (X + C (-s))) h
  simpa [cosetPack, comp_assoc, add_comp, X_comp, C_comp] using this

/-- ⭐ **…and surjective onto the window.**  Every codeword of the level-`m` window is
the coset transform of a coefficient vector in that window. -/
theorem cosetPack_surjective_on_window (m : ℕ) (β : ℕ → F) (s : F) (P : F[X])
    (hP : P.natDegree < 2 ^ m) :
    ∃ p : F[X], p.natDegree < 2 ^ m ∧ cosetPack β s m p = P := by
  have hd : (X + C (-s) : F[X]).natDegree = 1 := by
    simpa using natDegree_X_add_C (x := -s)
  have hPs : (P.comp (X + C (-s))).natDegree < 2 ^ m := by
    rw [natDegree_comp, hd, mul_one]; exact hP
  obtain ⟨p, hp, hpe⟩ := novelPack_surjective_on_window m β _ hPs
  refine ⟨p, hp, ?_⟩
  rw [cosetPack, hpe, comp_assoc]
  simp

/-- ⭐ **THE COMMITMENT STILL DETERMINES A TABLE, AND ONLY ONE.**  The uniqueness the
additive-BaseFold descent runs on is a property of the transform, not of the point set:
it survives the repair verbatim.  This is the half of the file that lives whether or not
a char-2 hash slot ever opens. -/
theorem exists_unique_table_cosetPack (β : ℕ → F) (s : F) (m : ℕ) (P : F[X])
    (hP : P.natDegree < 2 ^ m) :
    ∃! p : F[X], p.natDegree < 2 ^ m ∧ cosetPack β s m p = P := by
  obtain ⟨p, hp, hpe⟩ := cosetPack_surjective_on_window m β s P hP
  refine ⟨p, ⟨hp, hpe⟩, ?_⟩
  rintro q ⟨hq, hqe⟩
  exact cosetPack_injective_of_natDegree_lt hq hp (by rw [hqe, hpe])

/-! ## §2 ⭐ THE FIXED LANE — the defect, in full generality

`weft_branch.py` measured `row 0 of M = (1, 0, …, 0)` at one basis, one width, one
field, and its flag loop `range(1, 5)` never asked about the level that reads it.  The
fact is general and needs no basis, no width and no field: `X̂₀ = 1` and every other
novelpoly basis element vanishes at `0`, so evaluation at the domain point `0` reads off
the constant coefficient. -/

/-- ⭐ **THE FIXED LANE.** The level-`m` packing of ANY polynomial, evaluated at the
domain point `0`, is its constant coefficient — for every `m` and every ordered basis.
`0` lies in every additive domain, so this is a defect of the WINDOW, not of a basis
choice: it is the `b = 0` level of the invariant flag. -/
theorem novelPack_eval_zero : ∀ (m : ℕ) (β : ℕ → F) (p : F[X]),
    (novelPack β m p).eval 0 = p.coeff 0 := by
  intro m
  induction m with
  | zero => intro β p; simp
  | succ m ih =>
      intro β p
      rw [novelPack_succ]
      have h0 : (foldPoly (β 0)).eval 0 = 0 := by simp [foldPoly]
      simp only [eval_add, eval_mul, eval_comp, eval_X, h0, zero_mul, add_zero]
      rw [ih (additiveFoldedBasis β) (evenPart p), coeff_evenPart_terminal]

/-! ## §3 Density off the window — every entry of the repaired matrix is nonzero

The matrix entries are `X̂ᵢ(s + v)`, and `X̂ᵢ` is a product of subspace-vanishing
polynomials whose roots all lie in the window.  So a shift OUTSIDE the window makes every
entry nonzero — which is the whole structural content of the repair, and it is stated
here for every level, every basis and every shift, not for one instance. -/

section Density

variable [CharP F 2] [Algebra (ZMod 2) F]

/-- The fold is GF(2)-additive on finite sums — the LINEARITY that makes a coset shift a
twiddle shift. -/
theorem foldMap_sum (b : F) {ι : Type*} (s : Finset ι) (g : ι → F) :
    foldMap b (∑ i ∈ s, g i) = ∑ i ∈ s, foldMap b (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [foldMap]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, foldMap_add, ih]

/-- The fold of a point outside the level-`m+1` window lies outside the FOLDED level-`m`
window.  (The fold is GF(2)-additive with kernel `{0, β₀}`, so a fold-collision with the
folded window pulls the point back into the window.) -/
theorem foldMap_notMem_additiveDomain (β : ℕ → F) (m : ℕ) {x : F}
    (hx : x ∉ additiveDomain β (m + 1)) :
    foldMap (β 0) x ∉ additiveDomain (additiveFoldedBasis β) m := by
  intro hmem
  obtain ⟨c, hc⟩ := (mem_additiveDomain_iff _ m _).mp hmem
  have hsmul : ∀ (a : ZMod 2) (z : F), foldMap (β 0) (a • z) = a • foldMap (β 0) z := by
    intro a z
    rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 from by decide) a with rfl | rfl
    · simp [foldMap]
    · simp
  set y : F := ∑ j : Fin m, c j • β ((j : ℕ) + 1) with hy
  have hfy : foldMap (β 0) y = foldMap (β 0) x := by
    rw [hy, foldMap_sum, ← hc]
    unfold domainPoint additiveFoldedBasis
    exact Finset.sum_congr rfl fun j _ => hsmul (c j) (β ((j : ℕ) + 1))
  have hymem : y ∈ additiveDomain β (m + 1) := by
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨j.succ, by simp⟩
  have hβ0 : β 0 ∈ additiveDomain β (m + 1) :=
    Submodule.subset_span ⟨(0 : Fin (m + 1)), by simp⟩
  rcases foldMap_eq_iff.mp hfy with h | h
  · exact hx (h ▸ hymem)
  · have hxe : x = y - β 0 := by rw [h]; ring
    exact hx (hxe ▸ Submodule.sub_mem _ hymem hβ0)

/-- ⭐ **EVERY MATRIX ENTRY IS NONZERO WHEN THE SHIFT LEAVES THE WINDOW.**  For a
monomial index inside the window and a point outside it, the packing does not vanish.
Together with `cosetPack_eval` this says: the repaired mixing matrix
`M[j][i] = X̂ᵢ(s + vⱼ)` has NO zero entry, for every level, every ordered basis and every
shift `s ∉ V_m`. -/
theorem novelPack_monomial_eval_ne_zero : ∀ (m : ℕ) (β : ℕ → F) (i : ℕ), i < 2 ^ m →
    ∀ x : F, x ∉ additiveDomain β m → (novelPack β m (X ^ i)).eval x ≠ 0 := by
  intro m
  induction m with
  | zero =>
      intro β i hi x _
      interval_cases i
      simp
  | succ m ih =>
      intro β i hi x hx
      have hx0 : x ≠ 0 := fun h =>
        hx (h ▸ Submodule.zero_mem (additiveDomain β (m + 1)))
      have hfold := foldMap_notMem_additiveDomain β m hx
      rcases Nat.even_or_odd i with ⟨k, hk⟩ | ⟨k, hk⟩
      · -- i = 2k : the even branch
        have hk2 : k < 2 ^ m := by omega
        have he : evenPart (X ^ i : F[X]) = X ^ k := by
          ext j
          rw [coeff_evenPart_terminal, coeff_X_pow, coeff_X_pow]
          by_cases hjk : j = k
          · subst hjk; rw [if_pos (by omega), if_pos rfl]
          · rw [if_neg (by omega), if_neg hjk]
        have ho : oddPart (X ^ i : F[X]) = 0 := by
          ext j
          rw [coeff_oddPart_terminal, coeff_zero, coeff_X_pow, if_neg (by omega)]
        rw [novelPack_succ, he, ho]
        simpa [eval_comp] using ih (additiveFoldedBasis β) k hk2 _ hfold
      · -- i = 2k+1 : the odd branch, which multiplies by the point itself
        have hk2 : k < 2 ^ m := by omega
        have he : evenPart (X ^ i : F[X]) = 0 := by
          ext j
          rw [coeff_evenPart_terminal, coeff_zero, coeff_X_pow, if_neg (by omega)]
        have ho : oddPart (X ^ i : F[X]) = X ^ k := by
          ext j
          rw [coeff_oddPart_terminal, coeff_X_pow, coeff_X_pow]
          by_cases hjk : j = k
          · subst hjk; rw [if_pos (by omega), if_pos rfl]
          · rw [if_neg (by omega), if_neg hjk]
        rw [novelPack_succ, he, ho]
        have := ih (additiveFoldedBasis β) k hk2 _ hfold
        simpa [eval_comp, hx0] using this

/-- The repaired matrix's entries, stated on the coset transform itself. -/
theorem cosetPack_monomial_eval_ne_zero (β : ℕ → F) (s : F) (m : ℕ) (i : ℕ)
    (hi : i < 2 ^ m) (v : F) (hv : v ∈ additiveDomain β m)
    (hs : s ∉ additiveDomain β m) :
    (cosetPack β s m (X ^ i)).eval v ≠ 0 := by
  rw [cosetPack_eval]
  refine novelPack_monomial_eval_ne_zero m β i hi _ ?_
  intro hmem
  exact hs (by simpa using Submodule.sub_mem _ hmem hv)

end Density

/-! ## §4 The lane view: invariant subspaces, autonomous quotients, and multi-round -/

section Lanes

variable {t : ℕ}

/-- Lane vector to polynomial: lane `i` is the `i`-th novelpoly coefficient. -/
noncomputable def ofLanes (c : Fin t → F) : F[X] := ∑ i : Fin t, C (c i) * X ^ (i : ℕ)

theorem ofLanes_coeff (c : Fin t → F) (i : Fin t) : (ofLanes c).coeff (i : ℕ) = c i := by
  classical
  rw [ofLanes, finsetSum_coeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [coeff_C_mul, coeff_X_pow, if_neg (by exact fun h => hb (Fin.ext h.symm)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem ofLanes_natDegree_lt (c : Fin t → F) (ht : 0 < t) : (ofLanes c).natDegree < t := by
  have hle : (ofLanes c).natDegree ≤ t - 1 := by
    refine natDegree_le_iff_coeff_eq_zero.mpr fun n hn => ?_
    rw [ofLanes, finsetSum_coeff]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hi := i.isLt
    rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
  omega

theorem ofLanes_injective : Function.Injective (ofLanes (F := F) (t := t)) := by
  intro c d h
  funext i
  rw [← ofLanes_coeff c i, ← ofLanes_coeff d i, h]

/-- ⭐ **THE MIXING LAYER, as a matrix action.**  Input lane `i` is the `i`-th novelpoly
coefficient; output lane `j` is the value at `pt j`.  Written as an explicit sum over
columns so that the matrix ENTRY `(cosetPack β s m (X^i)).eval (pt j)` is the object the
structural theorems are about. -/
noncomputable def weftMix (β : ℕ → F) (s : F) (m : ℕ) (pt : Fin t → F)
    (c : Fin t → F) (j : Fin t) : F :=
  ∑ i : Fin t, c i * (cosetPack β s m (X ^ (i : ℕ))).eval (pt j)

theorem weftMix_add (β : ℕ → F) (s : F) (m : ℕ) (pt : Fin t → F) (u v : Fin t → F) :
    weftMix β s m pt (u + v) = weftMix β s m pt u + weftMix β s m pt v := by
  funext j
  simp only [weftMix, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem weftMix_smul (β : ℕ → F) (s : F) (m : ℕ) (pt : Fin t → F) (a : F) (u : Fin t → F) :
    weftMix β s m pt (a • u) = a • weftMix β s m pt u := by
  funext j
  simp only [weftMix, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- The single-lane input reads off one matrix ENTRY. -/
theorem weftMix_single (β : ℕ → F) (s : F) (m : ℕ) (pt : Fin t → F) (i j : Fin t) (a : F) :
    weftMix β s m pt (Pi.single i a) j = a * (cosetPack β s m (X ^ (i : ℕ))).eval (pt j) := by
  classical
  rw [weftMix, Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The coset packing of a finite sum, unfolded — linearity through a `Finset.sum`. -/
theorem cosetPack_sum (β : ℕ → F) (s : F) (m : ℕ) {ι : Type*} (S : Finset ι) (g : ι → F[X]) :
    cosetPack β s m (∑ i ∈ S, g i) = ∑ i ∈ S, cosetPack β s m (g i) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cosetPack_add, ih]

/-- ⭐ **THE MIXING LAYER IS THE ENCODER.**  The matrix action equals the evaluation of
the packed window polynomial: the two readings of `weftMix` are the same function, which
is what the one-object identity of §5 turns into an inhabited pair of obligations. -/
theorem weftMix_eq_eval (β : ℕ → F) (s : F) (m : ℕ) (pt : Fin t → F) (c : Fin t → F)
    (j : Fin t) :
    weftMix β s m pt c j = (cosetPack β s m (ofLanes c)).eval (pt j) := by
  rw [ofLanes, cosetPack_sum, eval_finsetSum, weftMix]
  exact Finset.sum_congr rfl fun i _ => by
    rw [cosetPack_C_mul, eval_mul, eval_C]

/-! ### Invariant subspaces and autonomous quotients — the two sides, and the asymmetry -/

/-- **An invariant coordinate SUBSPACE**: a state supported inside `A` has its image
supported inside `A`.  This is the family the kill enumerated (and the family a round
constant outside `A` breaks). -/
def InvariantSet (f : (Fin t → F) → (Fin t → F)) (A : Finset (Fin t)) : Prop :=
  ∀ u : Fin t → F, (∀ i, i ∉ A → u i = 0) → ∀ j, j ∉ A → f u j = 0

/-- ⭐ **An autonomous coordinate QUOTIENT**: the `A`-coordinates of the output are a
function of the `A`-coordinates of the input, so the map DESCENDS to `K^A`.  This is the
notion the kill's postmortem named and its script never enumerated from `b = 0`. -/
def AutonomousSet (f : (Fin t → F) → (Fin t → F)) (A : Finset (Fin t)) : Prop :=
  ∀ u v : Fin t → F, (∀ i ∈ A, u i = v i) → ∀ j ∈ A, f u j = f v j

/-- ⭐ **A ROUND CONSTANT CANNOT BREAK AN AUTONOMOUS SET.**  This is the asymmetry the
kill's "broken only by round-constant addition" clause misses: the constant is simply
absorbed into the quotient map. -/
theorem autonomousSet_add_const {f : (Fin t → F) → (Fin t → F)} {A : Finset (Fin t)}
    (h : AutonomousSet f A) (rc : Fin t → F) :
    AutonomousSet (fun u => f u + rc) A := by
  intro u v huv j hj
  simp [h u v huv j hj]

/-- ⭐ **NEITHER CAN A LANE-WISE S-BOX — whatever it is.**  No hypothesis on `σ`: not
bijectivity, not `σ 0 = 0`, not low degree. -/
theorem autonomousSet_comp_lanewise {f : (Fin t → F) → (Fin t → F)} {A : Finset (Fin t)}
    (h : AutonomousSet f A) (σ : F → F) :
    AutonomousSet (fun u => f fun i => σ (u i)) A :=
  fun u v huv j hj => h _ _ (fun i hi => by rw [huv i hi]) j hj

theorem autonomousSet_comp {f g : (Fin t → F) → (Fin t → F)} {A : Finset (Fin t)}
    (hf : AutonomousSet f A) (hg : AutonomousSet g A) :
    AutonomousSet (g ∘ f) A :=
  fun u v huv j hj => hg _ _ (fun i hi => hf u v huv i hi) j hj

/-- ⭐⭐ **[WEFT-multiround], THE NEGATIVE HALF: AN AUTONOMOUS SET SURVIVES EVERY NUMBER
OF ROUNDS.**  Whatever the round map is built from — any S-box, any constants — if it
has an autonomous set for one round it has it for `R` rounds, for every `R`.  A quotient
is not a subspace, and iteration does not dilute it. -/
theorem autonomousSet_iterate {f : (Fin t → F) → (Fin t → F)} {A : Finset (Fin t)}
    (h : AutonomousSet f A) : ∀ R : ℕ, AutonomousSet (f^[R]) A := by
  intro R
  induction R with
  | zero => intro u v huv j hj; simpa using huv j hj
  | succ R ih =>
      intro u v huv j hj
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact ih _ _ (fun i hi => h u v huv i hi) j hj

/-! ### The defect: the killed form's `b = 0` quotient, general in everything -/

/-- **The round map**: lane-wise S-box, then the mixing layer, then round constants. -/
noncomputable def weftRound (σ : F → F) (rc : Fin t → F) (β : ℕ → F) (s : F) (m : ℕ)
    (pt : Fin t → F) (u : Fin t → F) : Fin t → F :=
  fun j => weftMix β s m pt (fun i => σ (u i)) j + rc j

/-- The killed form's row 0, from `novelPack_eval_zero`: output lane 0 IS input lane 0. -/
theorem weftMix_shift_zero_lane_zero (β : ℕ → F) (m : ℕ) (pt : Fin t → F) (ht : 0 < t)
    (hpt0 : pt ⟨0, ht⟩ = 0) (c : Fin t → F) :
    weftMix β 0 m pt c ⟨0, ht⟩ = c ⟨0, ht⟩ := by
  classical
  rw [weftMix, Finset.sum_eq_single ⟨0, ht⟩]
  · simp [hpt0, novelPack_eval_zero]
  · intro b _ hb
    have hb0 : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
    rw [hpt0]
    simp only [cosetPack_shift_zero, novelPack_eval_zero, coeff_X_pow]
    rw [if_neg (Ne.symm hb0), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- ⭐⭐ **THE DEFECT, IN FULL GENERALITY.**  The killed form has the autonomous quotient
`{0}` — at every level `m`, every ordered basis `β`, every lane-wise S-box `σ` and every
round-constant vector `rc`.  With `autonomousSet_iterate` this says the 32-bit lane
`x₀ ↦ σ(x₀) + rc₀` runs autonomously for ANY number of rounds: exactly the `b = 0` level
`weft_branch.py:300`'s `range(1, 5)` never asked about. -/
theorem weftRound_autonomous_shift_zero (σ : F → F) (rc : Fin t → F) (β : ℕ → F) (m : ℕ)
    (pt : Fin t → F) (ht : 0 < t) (hpt0 : pt ⟨0, ht⟩ = 0) :
    AutonomousSet (weftRound σ rc β 0 m pt) {⟨0, ht⟩} := by
  intro u v huv j hj
  have hj0 : j = ⟨0, ht⟩ := by simpa using hj
  subst hj0
  have hu := weftMix_shift_zero_lane_zero β m pt ht hpt0 (fun i => σ (u i))
  have hv := weftMix_shift_zero_lane_zero β m pt ht hpt0 (fun i => σ (v i))
  simp only [weftRound, hu, hv]
  rw [huv ⟨0, ht⟩ (Finset.mem_singleton_self _)]

/-! ### The repair: no invariant subspace and no autonomous quotient, at ANY level -/

section Repair

variable [CharP F 2] [Algebra (ZMod 2) F]

/-- ⭐ **FULL DIFFUSION IN ONE ROUND.**  A single active input lane reaches EVERY output
lane.  Hence there is no nontrivial coordinate subspace trail of ANY length: the image of
any nonzero support is already the whole lane set. -/
theorem weftMix_single_full_support (β : ℕ → F) (s : F) (m : ℕ) (pt : Fin t → F)
    (hm : t ≤ 2 ^ m) (hpt : ∀ j : Fin t, pt j ∈ additiveDomain β m)
    (hs : s ∉ additiveDomain β m) (i j : Fin t) {a : F} (ha : a ≠ 0) :
    weftMix β s m pt (Pi.single i a) j ≠ 0 := by
  rw [weftMix_single]
  exact mul_ne_zero ha
    (cosetPack_monomial_eval_ne_zero β s m i (lt_of_lt_of_le i.isLt hm) (pt j) (hpt j) hs)

/-- ⭐⭐ **THE REPAIR, ON THE QUOTIENT SIDE: NO AUTONOMOUS SET AT ANY LEVEL.**  For every
nonempty proper lane set `A` — `b = 0` (the singletons) included — the repaired mixing
layer has no autonomous quotient.  General in the level, the ordered basis and the shift;
the only hypothesis is that the shift leaves the window. -/
theorem weftMix_no_autonomousSet (β : ℕ → F) (s : F) (m : ℕ) (pt : Fin t → F)
    (hm : t ≤ 2 ^ m) (hpt : ∀ j : Fin t, pt j ∈ additiveDomain β m)
    (hs : s ∉ additiveDomain β m) (A : Finset (Fin t)) (hA : A.Nonempty)
    (hAu : A ≠ Finset.univ) :
    ¬ AutonomousSet (weftMix β s m pt) A := by
  classical
  intro h
  obtain ⟨j, hj⟩ := hA
  obtain ⟨i, hi⟩ : ∃ i : Fin t, i ∉ A := by
    by_contra hc
    exact hAu (Finset.eq_univ_iff_forall.mpr (by simpa using hc))
  have hagree : ∀ k ∈ A, (0 : Fin t → F) k = (Pi.single i (1 : F) : Fin t → F) k := by
    intro k hk
    have : k ≠ i := fun hki => hi (hki ▸ hk)
    simp [Pi.single_eq_of_ne this]
  have hzero : weftMix β s m pt 0 j = 0 := by simp [weftMix]
  have := h 0 (Pi.single i (1 : F)) hagree j hj
  rw [hzero] at this
  exact weftMix_single_full_support β s m pt hm hpt hs i j (a := (1 : F)) one_ne_zero this.symm

/-- ⭐ **…and no invariant coordinate SUBSPACE either**, by the same density. -/
theorem weftMix_no_invariantSet (β : ℕ → F) (s : F) (m : ℕ) (pt : Fin t → F)
    (hm : t ≤ 2 ^ m) (hpt : ∀ j : Fin t, pt j ∈ additiveDomain β m)
    (hs : s ∉ additiveDomain β m) (A : Finset (Fin t)) (hA : A.Nonempty)
    (hAu : A ≠ Finset.univ) :
    ¬ InvariantSet (weftMix β s m pt) A := by
  classical
  intro h
  obtain ⟨i, hi⟩ := hA
  obtain ⟨j, hj⟩ : ∃ j : Fin t, j ∉ A := by
    by_contra hc
    exact hAu (Finset.eq_univ_iff_forall.mpr (by simpa using hc))
  refine weftMix_single_full_support β s m pt hm hpt hs i j (a := (1 : F)) one_ne_zero ?_
  refine h (Pi.single i (1 : F)) (fun k hk => ?_) j hj
  have : k ≠ i := fun hki => hk (hki ▸ hi)
  simp [Pi.single_eq_of_ne this]

/-- ⭐⭐ **THE REPAIR SURVIVES THE FULL ROUND — any non-constant S-box, any constants.**
The round map `u ↦ M(σ∘u) + rc` has no autonomous set at any level.  The only hypothesis
on the S-box is that it is not constant (a constant "S-box" makes every set autonomous,
which is a statement about that S-box and not about the mixing layer). -/
theorem weftRound_no_autonomousSet (σ : F → F) (rc : Fin t → F) (β : ℕ → F) (s : F)
    (m : ℕ) (pt : Fin t → F) (hm : t ≤ 2 ^ m)
    (hpt : ∀ j : Fin t, pt j ∈ additiveDomain β m) (hs : s ∉ additiveDomain β m)
    {a : F} (hσ : σ a ≠ σ 0) (A : Finset (Fin t)) (hA : A.Nonempty)
    (hAu : A ≠ Finset.univ) :
    ¬ AutonomousSet (weftRound σ rc β s m pt) A := by
  classical
  intro h
  obtain ⟨j, hj⟩ := hA
  obtain ⟨i, hi⟩ : ∃ i : Fin t, i ∉ A := by
    by_contra hc
    exact hAu (Finset.eq_univ_iff_forall.mpr (by simpa using hc))
  have hagree : ∀ k ∈ A, (0 : Fin t → F) k = (Pi.single i a : Fin t → F) k := by
    intro k hk
    have : k ≠ i := fun hki => hi (hki ▸ hk)
    simp [Pi.single_eq_of_ne this]
  have hround := h 0 (Pi.single i a) hagree j hj
  -- the two S-boxed states differ exactly in lane `i`, by `σ a - σ 0`
  have hdiff : (fun k => σ ((Pi.single i a : Fin t → F) k))
      = (fun _ => σ 0) + Pi.single i (σ a - σ 0) := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Pi.single_eq_of_ne hk]
  have h0 : (fun k => σ ((0 : Fin t → F) k)) = (fun _ : Fin t => σ 0) := by funext k; simp
  simp only [weftRound, h0, hdiff, add_left_inj] at hround
  rw [weftMix_add] at hround
  simp only [Pi.add_apply] at hround
  have hR : weftMix β s m pt (Pi.single i (σ a - σ 0)) j = 0 := by linear_combination -hround
  exact weftMix_single_full_support β s m pt hm hpt hs i j
    (a := σ a - σ 0) (sub_ne_zero.mpr hσ) hR

end Repair

/-! ## §5 ⭐ THE ONE-OBJECT IDENTITY — mixing layer AND code encoding map -/

/-- **The hash-side obligation, minimally stated.**  Additive and homogeneous in the
state, injective, and carrying NO autonomous quotient at any level — the last is the
property round constants provably cannot supply (`autonomousSet_add_const`), which is
why it belongs in the interface rather than in the round schedule. -/
structure IsMixingLayer (f : (Fin t → F) → (Fin t → F)) : Prop where
  /-- Additive in the state. -/
  add : ∀ u v, f (u + v) = f u + f v
  /-- Homogeneous in the state. -/
  smul : ∀ (a : F) u, f (a • u) = a • f u
  /-- Invertible on the state. -/
  inj : Function.Injective f
  /-- No invariant coordinate subspace at any level. -/
  noSubspace : ∀ A : Finset (Fin t), A.Nonempty → A ≠ Finset.univ → ¬ InvariantSet f A
  /-- No autonomous coordinate quotient at any level — including `b = 0`. -/
  noQuotient : ∀ A : Finset (Fin t), A.Nonempty → A ≠ Finset.univ → ¬ AutonomousSet f A

/-- **The code-side obligation.**  Each state is the coefficient vector of a polynomial
inside the level-`m` degree window, distinct states get distinct polynomials, and the
output is that polynomial's evaluation on the point set: an encoding map of the additive
code.  The representing polynomial is quantified over, not named — so nothing here is
true by the definition of `cosetPack`. -/
structure IsEvaluationEncoder (m : ℕ) (pt : Fin t → F) (f : (Fin t → F) → (Fin t → F)) where
  /-- The representing polynomial of each message. -/
  poly : (Fin t → F) → F[X]
  /-- It lies in the level-`m` degree window. -/
  window : ∀ c, (poly c).natDegree < 2 ^ m
  /-- The output is its codeword on the point set. -/
  codeword : ∀ c j, f c j = (poly c).eval (pt j)
  /-- Distinct messages get distinct representatives. -/
  polyInj : Function.Injective poly

/-- Both forms — killed and repaired — satisfy the CODE obligation.  The killed Weft
mixing layer is a perfectly good additive-code encoder; that was never the problem. -/
noncomputable def weftMix_isEncoder (β : ℕ → F) (s : F) (m : ℕ) (pt : Fin t → F)
    (ht : 0 < t) (htm : t ≤ 2 ^ m) :
    IsEvaluationEncoder m pt (weftMix β s m pt) where
  poly := fun c => cosetPack β s m (ofLanes c)
  window := fun c => cosetPack_natDegree_lt β s m _
  codeword := fun c j => weftMix_eq_eval β s m pt c j
  polyInj := by
    intro c d h
    refine ofLanes_injective ?_
    exact cosetPack_injective_of_natDegree_lt
      (lt_of_lt_of_le (ofLanes_natDegree_lt c ht) htm)
      (lt_of_lt_of_le (ofLanes_natDegree_lt d ht) htm) h

/-- The mixing layer is invertible on the state, at the natural width `t = 2^m`: a
window polynomial vanishing at all `t` distinct points is zero, and the packing is
injective on the window. -/
theorem weftMix_injective (β : ℕ → F) (s : F) (m : ℕ)
    (pt : Fin t → F) (ht : 0 < t) (htm : t = 2 ^ m) (hptinj : Function.Injective pt) :
    Function.Injective (weftMix β s m pt) := by
  intro c d h
  have hwin : ∀ e : Fin t → F, (ofLanes e).natDegree < 2 ^ m :=
    fun e => htm ▸ ofLanes_natDegree_lt e ht
  have hpe : cosetPack β s m (ofLanes c) = cosetPack β s m (ofLanes d) := by
    refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ hptinj (fun j => ?_) ?_
    · rw [← weftMix_eq_eval, ← weftMix_eq_eval, h]
    · simp only [Fintype.card_fin, max_lt_iff, htm]
      exact ⟨cosetPack_natDegree_lt β s m _, cosetPack_natDegree_lt β s m _⟩
  exact ofLanes_injective
    (cosetPack_injective_of_natDegree_lt (hwin c) (hwin d) hpe)

/-! ### ⭐⭐ The identity, and the tooth that makes it non-vacuous -/

/-- ⭐⭐ **THE ONE-OBJECT IDENTITY.**  ONE function satisfies BOTH obligations: it is a
mixing layer (linear, invertible, and free of invariant subspaces and autonomous
quotients at every level) AND the encoding map of the additive code (every state is a
window polynomial, and the output is its codeword on the point set).

This is the prize the Weft sketch was reaching for and the kill appeared to destroy: not
two objects that agree, ONE proved linear object with two jobs.  The hypotheses are
exactly the repair — the shift leaves the window — plus the natural width. -/
theorem weft_one_object [CharP F 2] [Algebra (ZMod 2) F] (β : ℕ → F) (s : F) (m : ℕ)
    (pt : Fin t → F) (ht : 0 < t) (htm : t = 2 ^ m) (hptinj : Function.Injective pt)
    (hpt : ∀ j : Fin t, pt j ∈ additiveDomain β m) (hs : s ∉ additiveDomain β m) :
    IsMixingLayer (weftMix β s m pt) ∧ Nonempty (IsEvaluationEncoder m pt (weftMix β s m pt)) :=
  ⟨{ add := weftMix_add β s m pt
     smul := weftMix_smul β s m pt
     inj := weftMix_injective β s m pt ht htm hptinj
     noSubspace := weftMix_no_invariantSet β s m pt (le_of_eq htm) hpt hs
     noQuotient := weftMix_no_autonomousSet β s m pt (le_of_eq htm) hpt hs },
   ⟨weftMix_isEncoder β s m pt ht (le_of_eq htm)⟩⟩

/-- ⭐ **THE TOOTH — the identity is not free.**  The KILLED form satisfies the code
obligation in full (it is a perfectly good additive-code encoder; that was never the
problem) and is REFUSED the mixing-layer obligation, by the `b = 0` autonomous quotient.
So the two interfaces are independent, and an object can inhabit one and fail the other:
`weft_one_object`'s conjunction is a real statement about the repaired transform, not a
consequence of the way either structure is written. -/
theorem weft_shift_zero_encodes_but_does_not_mix (β : ℕ → F) (m : ℕ) (pt : Fin t → F)
    (ht : 0 < t) (htm : t ≤ 2 ^ m) (h2 : 1 < t) (hpt0 : pt ⟨0, ht⟩ = 0) :
    Nonempty (IsEvaluationEncoder m pt (weftMix β (0 : F) m pt))
      ∧ ¬ IsMixingLayer (weftMix β (0 : F) m pt) := by
  classical
  refine ⟨⟨weftMix_isEncoder β 0 m pt ht htm⟩, fun hmix => ?_⟩
  have hne : ({⟨0, ht⟩} : Finset (Fin t)).Nonempty := ⟨_, Finset.mem_singleton_self _⟩
  have hnu : ({⟨0, ht⟩} : Finset (Fin t)) ≠ Finset.univ := by
    intro hcon
    have h1 : (⟨1, h2⟩ : Fin t) ∈ ({⟨0, ht⟩} : Finset (Fin t)) := hcon ▸ Finset.mem_univ _
    simp at h1
  refine hmix.noQuotient _ hne hnu ?_
  -- the identity S-box and zero constants: `weftMix` itself is the round map
  have hround := weftRound_autonomous_shift_zero (σ := (id : F → F)) (rc := (0 : Fin t → F))
    β m pt ht hpt0
  have heq : weftRound (id : F → F) (0 : Fin t → F) β 0 m pt = weftMix β 0 m pt := by
    funext u j; simp [weftRound]
  rwa [heq] at hround

/-! ### ⭐ SATISFIABILITY — the repaired object EXISTS, so §5 is not an empty quantifier

`weft_one_object` is a conditional, and its hypothesis is "the shift leaves the window".
A conditional whose hypothesis nothing satisfies is the vacuity this cone has been burned
by, so the hypothesis is discharged here rather than assumed: any field bigger than the
window has such a shift, and the window's own points supply the point set. -/

/-- **A shift outside the window exists whenever the field is bigger than the window.**
(The window has exactly `2^m` points for an independent basis, so a field of larger
cardinality cannot be exhausted by it.) -/
theorem exists_shift_outside_window [Fintype F] [Algebra (ZMod 2) F] {β : ℕ → F} {m : ℕ}
    (hβ : LinearIndependent (ZMod 2) fun j : Fin m => β j)
    (hcard : 2 ^ m < Fintype.card F) : ∃ s : F, s ∉ additiveDomain β m := by
  by_contra hc
  push_neg at hc
  have htop : additiveDomain β m = ⊤ := by
    refine eq_top_iff.mpr fun x _ => hc x
  have h1 : Nat.card (additiveDomain β m) = 2 ^ m := additiveDomain_card hβ
  rw [htop] at h1
  have h2 : Nat.card ((⊤ : Submodule (ZMod 2) F)) = Nat.card F :=
    Nat.card_congr (Submodule.topEquiv (R := ZMod 2) (M := F)).toEquiv
  rw [h2, Nat.card_eq_fintype_card] at h1
  omega

/-- ⭐⭐ **THE REPAIRED TRANSFORM IS INHABITED.**  For any independent ordered basis over
a field larger than its window there IS a shift and a point set at which `weftMix` is
simultaneously a mixing layer and an encoder.  Together with
`weft_shift_zero_encodes_but_does_not_mix` — which shows the mixing-layer obligation can
FAIL on a member of the same family — the `IsMixingLayer` interface is satisfiable,
refutable, and not provable: it is a floor, not a tautology. -/
theorem weft_one_object_satisfiable [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    {β : ℕ → F} {m : ℕ} (hβ : LinearIndependent (ZMod 2) fun j : Fin m => β j)
    (hcard : 2 ^ m < Fintype.card F) :
    ∃ (s : F) (pt : Fin (2 ^ m) → F),
      IsMixingLayer (weftMix β s m pt)
        ∧ Nonempty (IsEvaluationEncoder m pt (weftMix β s m pt)) := by
  classical
  obtain ⟨s, hs⟩ := exists_shift_outside_window hβ hcard
  have hcardfun : Fintype.card (Fin m → ZMod 2) = 2 ^ m := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  let e : (Fin m → ZMod 2) ≃ Fin (2 ^ m) := Fintype.equivFinOfCardEq hcardfun
  refine ⟨s, fun j => domainPoint β m (e.symm j), ?_⟩
  have hptinj : Function.Injective fun j : Fin (2 ^ m) => domainPoint β m (e.symm j) :=
    (domainPoint_injective hβ).comp e.symm.injective
  exact weft_one_object β s m _ (Nat.two_pow_pos m) rfl hptinj
    (fun j => domainPoint_mem β m _) hs

end Lanes

/-! ## §6 Axiom pins — every load-bearing statement, per declaration.
⚑ This class of pin has caught a `sorryAx` degradation twice in this cone. -/

/-- info: 'Minidregg.Selvage.cosetPack_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cosetPack_eval
/-- info: 'Minidregg.Selvage.cosetPack_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cosetPack_succ
/-- info: 'Minidregg.Selvage.cosetPack_natDegree_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cosetPack_natDegree_lt
/-- info: 'Minidregg.Selvage.cosetPack_injective_of_natDegree_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cosetPack_injective_of_natDegree_lt
/-- info: 'Minidregg.Selvage.cosetPack_surjective_on_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cosetPack_surjective_on_window
/-- info: 'Minidregg.Selvage.exists_unique_table_cosetPack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exists_unique_table_cosetPack
/-- info: 'Minidregg.Selvage.novelPack_eval_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms novelPack_eval_zero
/-- info: 'Minidregg.Selvage.foldMap_notMem_additiveDomain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms foldMap_notMem_additiveDomain
/-- info: 'Minidregg.Selvage.novelPack_monomial_eval_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms novelPack_monomial_eval_ne_zero
/-- info: 'Minidregg.Selvage.cosetPack_monomial_eval_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cosetPack_monomial_eval_ne_zero
/-- info: 'Minidregg.Selvage.autonomousSet_add_const' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms autonomousSet_add_const
/-- info: 'Minidregg.Selvage.autonomousSet_comp_lanewise' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms autonomousSet_comp_lanewise
/-- info: 'Minidregg.Selvage.autonomousSet_iterate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms autonomousSet_iterate
/-- info: 'Minidregg.Selvage.weftMix_eq_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms weftMix_eq_eval
/-- info: 'Minidregg.Selvage.weftRound_autonomous_shift_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms weftRound_autonomous_shift_zero
/-- info: 'Minidregg.Selvage.weftMix_single_full_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms weftMix_single_full_support
/-- info: 'Minidregg.Selvage.weftMix_no_autonomousSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms weftMix_no_autonomousSet
/-- info: 'Minidregg.Selvage.weftMix_no_invariantSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms weftMix_no_invariantSet
/-- info: 'Minidregg.Selvage.weftRound_no_autonomousSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms weftRound_no_autonomousSet
/-- info: 'Minidregg.Selvage.weft_one_object' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms weft_one_object
/-- info: 'Minidregg.Selvage.weft_shift_zero_encodes_but_does_not_mix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms weft_shift_zero_encodes_but_does_not_mix
/-- info: 'Minidregg.Selvage.exists_shift_outside_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exists_shift_outside_window
/-- info: 'Minidregg.Selvage.weft_one_object_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms weft_one_object_satisfiable

end Minidregg.Selvage
