/-
# Selvage.MultisetFingerprint -- the Reed-Solomon multiset fingerprint, priced

Nebula's Corollary 1 (following Spice, eprint 2018/907): two committed tuple
multisets are compared by the grand products

    PROD_{t in A} (gamma2 - enc_{gamma1}(t))  =?  PROD_{t in B} (gamma2 - enc_{gamma1}(t))

where `enc_{gamma1}` compresses a tuple to one field element by evaluating its
coefficient vector at `gamma1` (their `a + gamma1 v + gamma1^2 t` is the width-3
instance; wide values take more lanes, which is why the encoding here is an
arbitrary polynomial `vec : T -> F[X]` of bounded degree rather than a fixed
affine form -- a BabyBear-lane-safe statement).

* **Completeness** (`fingerprint_multiset_complete`): equal multisets pass at
  every challenge -- no probability, no hypotheses.
* **Soundness** (`fingerprint_multiset_sound`): distinct multisets (distinct
  already as multisets of encoding polynomials) pass on at most
  `max(|A|,|B|) * (k+1) / |F|` of the challenge pairs, `k` the encoding degree
  bound.  The proof prices BOTH challenges with the ONE existing
  Schwartz-Zippel citation `uniformProb_poly_eval_eq_zero_le`
  (Selvage/LogupStar.lean): work in `(F[X])[Y]`, where the two grand products
  are products of monic linear factors whose root multisets are the encoding
  polynomials themselves -- unique factorization makes the difference `P`
  nonzero, a nonzero `Y`-coefficient of `P` prices `gamma1` (degree
  `<= max * k`), and the specialized difference prices `gamma2` (degree
  `<= max`).  No new probability toolkit; the product space is sliced with the
  landed `uniformProb_prod_le`/`uniformProb_equiv`.
* **The ordering is load-bearing** (`fingerprint_forged_after_challenge`): for
  EVERY challenge pair there is a forged pair of distinct singleton multisets
  with identical fingerprints -- a prover choosing tuple values after seeing
  gamma defeats the check with probability 1, against the theorem's
  `2/|F|` for the committed-first order.  The deployment's realization of
  "committed first" is the roots-before-challenge schedule the controller
  bridge already enforces (`AcceptedLogupRun`, Compiler side); this module
  states the quantifier order, the join names the remaining binding
  obligations.

The consumer joining this to the kernel's memory tuples is
`Assurance/TwistMemoryFingerprintJoin.lean`.
-/
import Selvage.LogupStar

namespace Minidregg.Selvage

open Polynomial

universe u

/-! ## Linear-factor products over a commutative ring -/

/-- The product of monic linear factors with the given multiset of roots. -/
noncomputable def linFactors {R : Type*} [CommRing R] (s : Multiset R) :
    Polynomial R :=
  (s.map fun a => X - C a).prod

/-- Over a domain, the root multiset is recovered exactly: `linFactors` is
injective.  (Mathlib's `roots_multiset_prod_X_sub_C`, used once.) -/
theorem linFactors_injective {R : Type*} [CommRing R] [IsDomain R] :
    Function.Injective (linFactors (R := R)) := by
  intro s t h
  have hroots := congrArg Polynomial.roots h
  rwa [linFactors, linFactors, roots_multiset_prod_X_sub_C,
    roots_multiset_prod_X_sub_C] at hroots

/-- Ring maps push through the linear-factor product. -/
theorem map_linFactors {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (s : Multiset R) :
    (linFactors s).map f = linFactors (s.map ⇑f) := by
  unfold linFactors
  rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun a _ => ?_)
  simp

/-- Evaluation of the linear-factor product. -/
theorem eval_linFactors {R : Type*} [CommRing R] (s : Multiset R) (x : R) :
    (linFactors s).eval x = (s.map fun a => x - a).prod := by
  unfold linFactors
  rw [eval_multiset_prod, Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun a _ => ?_)
  simp

/-- The `Y`-degree of the linear-factor product is the multiset size. -/
theorem natDegree_linFactors {R : Type*} [CommRing R] [Nontrivial R]
    (s : Multiset R) : (linFactors s).natDegree = Multiset.card s :=
  natDegree_multiset_prod_X_sub_C_eq_card s

/-- Coefficient-degree bound: if every root polynomial has degree at most `k`,
every `(F[X])`-coefficient of the linear-factor product has degree at most
`|s| * k` (the coefficients are elementary symmetric functions of the roots). -/
theorem natDegree_coeff_linFactors_le {F : Type} [Field F] {k : ℕ}
    (s : Multiset (Polynomial F)) :
    (∀ a ∈ s, a.natDegree ≤ k) →
      ∀ j, ((linFactors s).coeff j).natDegree ≤ Multiset.card s * k := by
  induction s using Multiset.induction_on with
  | empty =>
      intro _ j
      rcases j with _ | j <;>
        simp [linFactors, Polynomial.coeff_one]
  | cons a s ih =>
      intro hdeg j
      have hstep : linFactors (a ::ₘ s) = (X - C a) * linFactors s := by
        unfold linFactors
        rw [Multiset.map_cons, Multiset.prod_cons]
      have hmul : (Multiset.card s + 1) * k = Multiset.card s * k + k :=
        Nat.succ_mul _ _
      have htail := ih fun b hb => hdeg b (Multiset.mem_cons_of_mem hb)
      have hhead : a.natDegree ≤ k := hdeg a (Multiset.mem_cons_self a s)
      rw [hstep, sub_mul, Multiset.card_cons]
      -- coeff j (X*p - C a*p) = coeff j (X*p) - coeff j (C a*p)
      rw [Polynomial.coeff_sub]
      refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
      · rcases j with _ | j
        · simp [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero]
        · rw [Polynomial.coeff_X_mul]
          exact le_trans (htail j) (by omega)
      · rw [Polynomial.coeff_C_mul]
        refine le_trans Polynomial.natDegree_mul_le ?_
        have := htail j
        omega

/-! ## The fingerprint -/

/-- The grand-product fingerprint of a tuple multiset at the challenge pair
`γ = (γ₁, γ₂)`: each tuple is compressed to `(vec t).eval γ₁` and the products
of `γ₂ - ·` are compared. -/
noncomputable def fingerprintProd {F : Type} [Field F] {T : Type u}
    (vec : T → Polynomial F) (γ : F × F) (A : Multiset T) : F :=
  (A.map fun t => γ.2 - (vec t).eval γ.1).prod

/-- The fingerprint is the bivariate linear-factor product, specialized at
`γ₁` coefficient-wise and evaluated at `γ₂`. -/
theorem fingerprintProd_eq {F : Type} [Field F] {T : Type u}
    (vec : T → Polynomial F) (γ : F × F) (A : Multiset T) :
    fingerprintProd vec γ A =
      ((linFactors (A.map vec)).map (evalRingHom γ.1)).eval γ.2 := by
  unfold fingerprintProd
  rw [map_linFactors, eval_linFactors, Multiset.map_map, Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun t _ => ?_)
  simp

/-- **Completeness**: equal multisets pass at every challenge pair. -/
theorem fingerprint_multiset_complete {F : Type} [Field F] {T : Type u}
    (vec : T → Polynomial F) (γ : F × F) {A B : Multiset T} (h : A = B) :
    fingerprintProd vec γ A = fingerprintProd vec γ B := by
  rw [h]

/-- **Soundness (Nebula Corollary 1, generalized encoding).**  If the two
multisets of encoding polynomials differ, the fingerprint check passes on at
most a `max(|A|,|B|) * (k+1) / |F|` fraction of challenge pairs.  The
quantifier order is the theorem: `A`, `B`, `vec` are fixed BEFORE the
uniform draw -- the committed-first schedule.  Both challenge legs discharge
from the one landed Schwartz--Zippel lemma. -/
theorem fingerprint_multiset_sound {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {T : Type u}
    (vec : T → Polynomial F) {k : ℕ}
    (hdeg : ∀ t, (vec t).natDegree ≤ k)
    {A B : Multiset T} (hne : A.map vec ≠ B.map vec) :
    uniformProb (F × F) (fun γ =>
      fingerprintProd vec γ A = fingerprintProd vec γ B) ≤
      ((max (Multiset.card A) (Multiset.card B) * (k + 1) : ℕ) : ℝ) /
        Fintype.card F := by
  classical
  set M : ℕ := max (Multiset.card A) (Multiset.card B) with hM
  set P : Polynomial (Polynomial F) :=
    linFactors (A.map vec) - linFactors (B.map vec) with hPdef
  have hP : P ≠ 0 := sub_ne_zero.mpr fun h => hne (linFactors_injective h)
  obtain ⟨j₀, hj₀⟩ : ∃ j, P.coeff j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hP (Polynomial.ext_iff.mpr (by simpa using hall))
  -- the gamma1 leg: a nonzero coefficient of P, of degree <= M * k
  have hAdeg : ∀ a ∈ A.map vec, a.natDegree ≤ k := fun a ha => by
    obtain ⟨t, _, rfl⟩ := Multiset.mem_map.mp ha
    exact hdeg t
  have hBdeg : ∀ a ∈ B.map vec, a.natDegree ≤ k := fun a ha => by
    obtain ⟨t, _, rfl⟩ := Multiset.mem_map.mp ha
    exact hdeg t
  have hcdeg : (P.coeff j₀).natDegree ≤ M * k := by
    rw [hPdef, Polynomial.coeff_sub]
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · refine le_trans
        (natDegree_coeff_linFactors_le (k := k) (A.map vec) hAdeg j₀) ?_
      rw [Multiset.card_map]
      exact Nat.mul_le_mul_right _ (le_max_left _ _)
    · refine le_trans
        (natDegree_coeff_linFactors_le (k := k) (B.map vec) hBdeg j₀) ?_
      rw [Multiset.card_map]
      exact Nat.mul_le_mul_right _ (le_max_right _ _)
  -- the gamma2 leg: the specialized difference, of Y-degree <= M
  have hDdeg : ∀ c : F, (P.map (evalRingHom c)).natDegree ≤ M := by
    intro c
    refine le_trans (Polynomial.natDegree_map_le) ?_
    rw [hPdef]
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · rw [natDegree_linFactors, Multiset.card_map]
      exact le_max_left _ _
    · rw [natDegree_linFactors, Multiset.card_map]
      exact le_max_right _ _
  -- event inclusion: acceptance implies a gamma1 root or a gamma2 root
  refine le_trans (uniformProb_mono
    (q := fun γ : F × F => (P.coeff j₀).eval γ.1 = 0 ∨
      (P.map (evalRingHom γ.1) ≠ 0 ∧
        (P.map (evalRingHom γ.1)).eval γ.2 = 0))
    (fun γ hγ => ?_)) ?_
  · have hDeval : (P.map (evalRingHom γ.1)).eval γ.2 = 0 := by
      rw [hPdef, Polynomial.map_sub, Polynomial.eval_sub, sub_eq_zero,
        ← fingerprintProd_eq, ← fingerprintProd_eq]
      exact hγ
    by_cases hD : P.map (evalRingHom γ.1) = 0
    · left
      have hc := congrArg (fun q => Polynomial.coeff q j₀) hD
      simpa [Polynomial.coeff_map] using hc
    · exact Or.inr ⟨hD, hDeval⟩
  -- price the two legs
  refine le_trans (uniformProb_or_le _ _) ?_
  have hb1 : uniformProb (F × F)
      (fun γ : F × F => (P.coeff j₀).eval γ.1 = 0) ≤
      ((M * k : ℕ) : ℝ) / Fintype.card F := by
    have hswap : uniformProb (F × F)
        (fun γ : F × F => (P.coeff j₀).eval γ.1 = 0) =
        uniformProb (F × F)
          (fun δ : F × F => (P.coeff j₀).eval δ.2 = 0) :=
      uniformProb_equiv (Equiv.prodComm F F)
        (fun δ : F × F => (P.coeff j₀).eval δ.2 = 0)
    rw [hswap]
    refine uniformProb_prod_le (by positivity) fun a => ?_
    exact uniformProb_poly_eval_eq_zero_le _ hj₀ hcdeg
  have hb2 : uniformProb (F × F)
      (fun γ : F × F => P.map (evalRingHom γ.1) ≠ 0 ∧
        (P.map (evalRingHom γ.1)).eval γ.2 = 0) ≤
      ((M : ℕ) : ℝ) / Fintype.card F := by
    refine uniformProb_prod_le (by positivity) fun a => ?_
    by_cases hD : P.map (evalRingHom a) = 0
    · rw [uniformProb_false (fun b hb => hb.1 hD)]
      positivity
    · refine le_trans (uniformProb_mono fun b hb => hb.2) ?_
      exact uniformProb_poly_eval_eq_zero_le _ hD (hDdeg a)
  refine le_trans (add_le_add hb1 hb2) (le_of_eq ?_)
  rw [← add_div]
  norm_cast

/-- Distinct multisets have distinct encoding-polynomial multisets whenever
the encoding is injective on their members -- the range-checked-columns form
of injectivity, inhabitable even though tuples with unbounded components
cannot inject into bounded-degree polynomials globally. -/
theorem map_ne_map_of_injOn {T : Type u} {R : Type*} (f : T → R)
    {A B : Multiset T}
    (hinj : Set.InjOn f {t | t ∈ A ∨ t ∈ B}) (hne : A ≠ B) :
    A.map f ≠ B.map f := by
  classical
  intro hmap
  apply hne
  ext x
  by_cases hx : x ∈ A ∨ x ∈ B
  · have hcount : ∀ (s : Multiset T), (∀ t ∈ s, t ∈ A ∨ t ∈ B) →
        Multiset.count (f x) (s.map f) = Multiset.count x s := by
      intro s hs
      rw [Multiset.count_map,
        show (s.filter fun a => f x = f a) = s.filter (x = ·) from
          Multiset.filter_congr fun a ha =>
            ⟨fun h => hinj hx (hs a ha) h, fun h => congrArg f h⟩]
      rw [← Multiset.countP_eq_card_filter]
      rfl
    have hA := hcount A fun t ht => Or.inl ht
    have hB := hcount B fun t ht => Or.inr ht
    rw [← hA, ← hB, hmap]
  · push Not at hx
    rw [Multiset.count_eq_zero_of_notMem hx.1,
      Multiset.count_eq_zero_of_notMem hx.2]

/-- Soundness packaged over member-injectivity: the form the memory join
consumes. -/
theorem fingerprint_multiset_sound_of_injOn {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {T : Type u}
    (vec : T → Polynomial F) {k : ℕ}
    (hdeg : ∀ t, (vec t).natDegree ≤ k)
    {A B : Multiset T}
    (hinj : Set.InjOn vec {t | t ∈ A ∨ t ∈ B}) (hne : A ≠ B) :
    uniformProb (F × F) (fun γ =>
      fingerprintProd vec γ A = fingerprintProd vec γ B) ≤
      ((max (Multiset.card A) (Multiset.card B) * (k + 1) : ℕ) : ℝ) /
        Fintype.card F :=
  fingerprint_multiset_sound vec hdeg (map_ne_map_of_injOn vec hinj hne)

/-! ## The ordering tooth: values chosen AFTER gamma defeat the fingerprint -/

namespace MultisetFingerprintExample

/-- Width-2 tuples over F₅ encoded Nebula-style: `(v, s) ↦ v + s·X`. -/
noncomputable def pairVec : ZMod 5 × ZMod 5 → Polynomial (ZMod 5) :=
  fun p => C p.1 + C p.2 * X

theorem pairVec_injective : Function.Injective pairVec := by
  intro p q h
  have h0 := congrArg (fun r => Polynomial.coeff r 0) h
  have h1 := congrArg (fun r => Polynomial.coeff r 1) h
  simp only [pairVec, Polynomial.coeff_add, Polynomial.coeff_C,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_zero, Polynomial.coeff_X_one,
    mul_zero, mul_one, add_zero, zero_add, if_pos,
    one_ne_zero, reduceIte] at h0 h1
  exact Prod.ext h0 h1

theorem pairVec_natDegree_le : ∀ p, (pairVec p).natDegree ≤ 1 := by
  intro p
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (by simp) ?_)
  refine le_trans Polynomial.natDegree_mul_le ?_
  simp

/-- **⚑ The commit-then-challenge order is load-bearing.**  For EVERY
challenge pair there exist DISTINCT singleton multisets with identical
fingerprints: the tuple `(0, 1)` and the forged tuple `(γ₁, 0)` collide at
`γ₁` by construction.  A prover who sees γ before choosing values wins with
probability 1; the committed-first order (the theorem above) prices the same
forgery at `2/|F|`. -/
theorem fingerprint_forged_after_challenge (γ : ZMod 5 × ZMod 5) :
    ∃ A B : Multiset (ZMod 5 × ZMod 5), A ≠ B ∧
      fingerprintProd pairVec γ A = fingerprintProd pairVec γ B := by
  refine ⟨{(0, 1)}, {(γ.1, 0)}, ?_, ?_⟩
  · intro h
    have := Multiset.singleton_inj.mp h
    have h2 := congrArg Prod.snd this
    simp at h2
  · simp [fingerprintProd, pairVec]

/-- The soundness event is NONEMPTY: the fixed distinct pair `{(0,1)}` vs
`{(1,0)}` IS accepted at `γ₁ = 1` -- the `max·(k+1)/|F|` bound prices a real
event, not an empty one. -/
theorem false_accept_event_nonempty :
    fingerprintProd pairVec ((1 : ZMod 5), (0 : ZMod 5))
        {((0 : ZMod 5), (1 : ZMod 5))} =
      fingerprintProd pairVec ((1 : ZMod 5), (0 : ZMod 5))
        {((1 : ZMod 5), (0 : ZMod 5))} ∧
    ({((0 : ZMod 5), (1 : ZMod 5))} : Multiset (ZMod 5 × ZMod 5)) ≠
      {((1 : ZMod 5), (0 : ZMod 5))} := by
  constructor
  · simp [fingerprintProd, pairVec]
  · intro h
    exact absurd (Multiset.singleton_inj.mp h) (by decide)

/-- The fingerprint has teeth at the committed-first order: a concrete fixed
pair of distinct multisets is refused at a concrete challenge. -/
theorem fixed_pair_refused_at_challenge :
    fingerprintProd pairVec ((1 : ZMod 5), (0 : ZMod 5)) {((0 : ZMod 5), (1 : ZMod 5))} ≠
      fingerprintProd pairVec ((1 : ZMod 5), (0 : ZMod 5)) {((0 : ZMod 5), (2 : ZMod 5))} := by
  simp only [fingerprintProd, Multiset.map_singleton, Multiset.prod_singleton,
    pairVec]
  intro h
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] at h
  have : (4 : ZMod 5) = 3 := by
    calc (4 : ZMod 5) = 0 - (0 + 1 * 1) := by decide
    _ = 0 - (0 + 2 * 1) := h
    _ = 3 := by decide
  exact absurd this (by decide)

end MultisetFingerprintExample

/-! ## Axiom pins -/

/-- info: 'Minidregg.Selvage.linFactors_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms linFactors_injective
/-- info: 'Minidregg.Selvage.fingerprint_multiset_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fingerprint_multiset_sound
/-- info: 'Minidregg.Selvage.fingerprint_multiset_sound_of_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fingerprint_multiset_sound_of_injOn
/-- info: 'Minidregg.Selvage.MultisetFingerprintExample.fingerprint_forged_after_challenge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MultisetFingerprintExample.fingerprint_forged_after_challenge
/-- info: 'Minidregg.Selvage.MultisetFingerprintExample.fixed_pair_refused_at_challenge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MultisetFingerprintExample.fixed_pair_refused_at_challenge

end Minidregg.Selvage
