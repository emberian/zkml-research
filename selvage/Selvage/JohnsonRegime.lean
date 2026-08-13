/-
# Selvage.JohnsonRegime — the beyond-unique-decoding frontier, driven to its
honest boundary: the Johnson list bound PROVED, mutual CA past `dC/2`
REDUCED locally to the named historical conjecture interface (WHIR Conj. 4.12), the
`t`-column sampling bridge BOUNDED.

**What this file is.** `[SUBUD-johnson]` (Selvage/SubUdSeam.lean's residual)
named four parts. Part (i)'s UD case landed in `Selvage/ProximityGapUD.lean`.
This file attacks the rest at the honest resolution each part admits:

* **(iii) — PROVABLE, and PROVED: the Johnson bound.** The Johnson radius
  `J(ρ) = 1 − √ρ` (`johnsonRadius`) and the classical list-size bound
  (`johnson_list_bound`): for ANY code of pairwise relative distance ≥ dC
  and any δ < `1 − √(1 − dC)`, every finite list of codewords δ-close to a
  common word has size ≤ `(dC − δ) / ((1 − δ)² − (1 − dC))` — finite, and
  blowing up exactly at the Johnson radius. The proof is the classical
  double counting: shrink each agreement set to the exact size `⌈(1−δ)n⌉`,
  count coordinate incidences two ways, Cauchy–Schwarz
  (`sq_sum_le_card_mul_sum_sq`), and the pairwise-agreement cap from the
  minimum distance (the CITED `reedSolomonCode_minDist` at the RS
  instantiation `reedSolomon_johnson_list_bound`, where `dC := 1 − ρ` gives
  the literature radius `J(ρ) = 1 − √ρ` on the nose). Below UD the pin was
  a singleton (`subUdRecover_sound`, CITED); past UD it is a LIST, and this
  is the theorem that the list is SMALL — the quantitative content of
  "recovered up to the mutual-CA list" in the Johnson regime. Selecting
  the intended member is the landed `[OOD-pin-proximity]` seam, untouched.

* **(ii) — PROVED IN THE LITERATURE FOR THE RS/POLYNOMIAL-GENERATOR
  JOHNSON INSTANCE, but not formalized locally.** The landed WHIR Lemma 4.10 upgrade
  (`hasMutualCorrelatedAgreement_of_isProximityGenerator`, CITED) caps the
  mutual-CA bound at `B⋆ = max (1 − dC/2) B` — intrinsically
  unique-decoding. Whether mutual CA extends to the generator's OWN bound
  `B` was posed as **WHIR (eprint 2024/1586) Conjecture 4.12**. Subsequent
  results prove the relevant RS/polynomial-generator instance through the
  Johnson radius: eprints 2025/2051 and 2025/2110 prove mutual correlated
  agreement, with 2025/2055 developing the corresponding proximity
  consequences. Those proofs are NOT formalized in this tree. Moreover,
  `WHIRConjecture412` is deliberately more parametric than the RS instance,
  so it remains a named LOCAL `Prop`, consumed only as an explicit
  hypothesis rather than silently upgraded by a citation. What IS proved
  locally is the reduction
  (`mutualCA_johnson_of_conj`, `mutualCA_johnson`,
  `foldFamily_mutualCA_johnson`) — conjecture + proximity gap at `B = √ρ`
  ⟹ mutual correlated agreement on ALL of `δ ∈ (0, J(ρ))`, in the exact
  shape `Selvage/SubUdSeam.lean`'s family ladder consumes — and the STRICT
  interval gain (`johnson_interval_extends_UD`: the UD cap `(1−ρ)/2` sits
  strictly inside `J(ρ)` for every rate ρ < 1). The conjecture Prop is
  satisfiable as a shape (`whirConjecture412_top` — at the full code the
  implication holds outright, so the Prop is no contradiction) and
  non-vacuous where consumers need it (`conjecture_band_nonempty` — the
  band `(dC/2, J(ρ))` it governs is inhabited at the landed F₁₁ site).

* **(iv) — PROVABLE, and PROVED: the sampling bridge.** A word δ-far from
  a comparison word survives `t` uniformly-drawn column checks with
  probability ≤ `(1 − δ)^t`: `column_sampling_bridge` (count form) and
  `column_sampling_bridge_pr` (fraction form), by exact counting — the
  survivor set of `t`-column schedules IS the `t`-power of the agreement
  set (`column_sampling_count`). This is the amplification that discharges
  the closeness-EVENT premise `hobs` of `subUdRecover_of_foldFamily` from
  deployed `t`-column spot checks; the bound is ATTAINED at the F₅
  keystone (`sampling_bridge_tight`), so it is not improvable in general.

**The honest boundary, in one sentence.** Johnson-regime LIST SIZE and
`t`-column AMPLIFICATION are theorems (proved here, no hypotheses beyond
the code's distance); Johnson-regime MUTUAL CORRELATED AGREEMENT — the
statement the beyond-UD extractor actually rides — is literature-proved
for the needed RS/polynomial-generator Johnson instance (2025/2051,
2025/2055, 2025/2110), but remains conditional in THIS Lean tree on the
historically named `WHIRConjecture412` plus the locally unformalized
Johnson-regime proximity gap. Capacity-level versions are not a stronger
future endpoint: the conjecture family at capacity is false (2025/2046).

**Keystones** (ATLAS law 2). Satisfiable: `J(1/2) = 1 − 1/√2 ∈ (0.29, 0.30)`
strictly beats the UD radius `1/4` (`johnson_win_at_rate_half`), and the
general strict gain holds at every rate < 1 (`ud_radius_lt_johnsonRadius`).
Teeth: at the landed `RS[F₁₁, {0..7}, 2]` corruption site, the ball of
radius `δ = 1/2` around `midWord` — PAST the UD radius `7/16`, where
`subUdRecover_sound`'s premise genuinely fails — holds TWO distinct
codewords, and the proved Johnson bound caps the count at 3
(`johnson_ball_past_UD`): multiple codewords (UD teeth), bounded list (the
Johnson pin is real). The conjecture band `(7/16, 1/2)` at that site is
nonempty (`conjecture_band_nonempty`). The sampling bound is met with
equality at F₅ (`sampling_bridge_tight`). No `sorry`, no vacuous
`Prop := True`, and `WHIRConjecture412` is nowhere asserted, only named.
-/
import Mathlib.Algebra.Order.Chebyshev
import Selvage.CorrelatedAgreement
import Selvage.ReedSolomon
import Selvage.ProximityGapUD
import Selvage.SubUdSeam

namespace Minidregg.Selvage

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]
variable {ℓ : ℕ}

/-! ## The Johnson radius, and its strict win over unique decoding -/

/-- **The Johnson radius** `J(ρ) = 1 − √ρ` — the list-decoding radius of a
rate-ρ Reed–Solomon code (BCIKS 2020/654 Thm 1.2's Johnson regime, WHIR
Thm 4.8's `B = √ρ` read as a radius `1 − B`). Beyond the unique-decoding
radius `(1 − ρ)/2` the nearby codeword is no longer unique; up to `J(ρ)`
the list of nearby codewords is provably SMALL (`johnson_list_bound`). -/
noncomputable def johnsonRadius (ρ : ℝ) : ℝ := 1 - Real.sqrt ρ

/-- **The win, at every rate**: the unique-decoding radius `(1 − ρ)/2` sits
STRICTLY below the Johnson radius for every rate ρ < 1 — the gap is
`(1 − √ρ)²/2 > 0`. This is the interval the Johnson regime buys. -/
theorem ud_radius_lt_johnsonRadius {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    (1 - ρ) / 2 < johnsonRadius ρ := by
  have hsq := Real.sq_sqrt hρ0
  have hs1 : Real.sqrt ρ < 1 := by
    have h := Real.sqrt_lt_sqrt hρ0 hρ1
    rwa [Real.sqrt_one] at h
  have h1s : (0 : ℝ) < 1 - Real.sqrt ρ := by linarith
  unfold johnsonRadius
  nlinarith [mul_pos h1s h1s]

/-! ## Agreement-set counting bridges -/

omit [DecidableEq ι] [Field F] in
/-- δ-closeness puts ≥ `(1 − δ)·n` coordinates in the canonical agreement
set — the counting form of the landed `exists_agreesOn_of_close`, aimed at a
GIVEN codeword rather than an existential one. -/
theorem card_agreeFilter_ge_of_relDist_le [Nonempty ι] {g u : ι → F} {δ : ℝ}
    (h : relDist g u ≤ δ) :
    (1 - δ) * (Fintype.card ι : ℝ)
      ≤ ((Finset.univ.filter fun x => g x = u x).card : ℝ) := by
  classical
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsplit : (Finset.univ.filter fun x => g x = u x).card
      + (Finset.univ.filter fun x => ¬ g x = u x).card = Fintype.card ι := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hh : hammingDist g u
      = (Finset.univ.filter fun x => ¬ g x = u x).card := by
    simp [hammingDist, ne_eq]
  have hd : (hammingDist g u : ℝ) ≤ δ * (Fintype.card ι : ℝ) := by
    rw [relDist, div_le_iff₀ hn] at h
    linarith
  have hcast : ((Finset.univ.filter fun x => g x = u x).card : ℝ)
      + (hammingDist g u : ℝ) = (Fintype.card ι : ℝ) := by
    rw [hh]; exact_mod_cast hsplit
  nlinarith

omit [DecidableEq ι] [Field F] in
/-- δ-farness caps the canonical agreement set at `(1 − δ)·n` coordinates —
the converse counting bound, consumed by the sampling bridge. -/
theorem card_agreeFilter_le_of_le_relDist [Nonempty ι] {g u : ι → F} {δ : ℝ}
    (h : δ ≤ relDist g u) :
    ((Finset.univ.filter fun x => g x = u x).card : ℝ)
      ≤ (1 - δ) * (Fintype.card ι : ℝ) := by
  classical
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsplit : (Finset.univ.filter fun x => g x = u x).card
      + (Finset.univ.filter fun x => ¬ g x = u x).card = Fintype.card ι := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hh : hammingDist g u
      = (Finset.univ.filter fun x => ¬ g x = u x).card := by
    simp [hammingDist, ne_eq]
  have hd : δ * (Fintype.card ι : ℝ) ≤ (hammingDist g u : ℝ) := by
    rw [relDist, le_div_iff₀ hn] at h
    linarith
  have hcast : ((Finset.univ.filter fun x => g x = u x).card : ℝ)
      + (hammingDist g u : ℝ) = (Fintype.card ι : ℝ) := by
    rw [hh]; exact_mod_cast hsplit
  nlinarith

/-! ## The Johnson list bound — PROVED

The classical double-counting argument, in full: given a finite list `T` of
codewords all δ-close to `g`, shrink each codeword's agreement set with `g`
to the EXACT size `a = ⌈(1−δ)n⌉` (the exactness is what makes the incidence
count sharp), count the coordinate incidences `m x = #{u ∈ T : x ∈ A'ᵤ}` two
ways, apply Cauchy–Schwarz to `∑ m x`, and cap the off-diagonal pair counts
`|A'ᵤ ∩ A'ᵥ| ≤ (1 − dC)n` by the minimum distance. The endgame inequality
`L·(A² − b) ≤ A − b` (with `A = a/n ≥ 1 − δ`, `b = 1 − dC`) transfers to the
radius `1 − δ` because `(A − b)/(A² − b)` is decreasing in `A` on the
Johnson region — the factored monotonicity step `hkey`. -/

/-- **The Johnson list bound.** For ANY linear code with pairwise relative
distance ≥ dC and any radius `δ < 1 − √(1 − dC)` (the Johnson radius at
distance dC): every finite set `T` of codewords within relative distance δ
of a common word `g` satisfies

  `|T| ≤ (dC − δ) / ((1 − δ)² − (1 − dC))`.

The denominator is positive exactly on the Johnson interval, and the bound
blows up at its right end — the honest shape of list decoding. Stated over
an arbitrary `Finset` of qualifying codewords, so no finiteness of the code
or of the ball is presupposed. -/
theorem johnson_list_bound [Nonempty ι] {C : Submodule F (ι → F)} {dC δ : ℝ}
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hdC0 : 0 ≤ dC) (hdC1 : dC ≤ 1) (hδ0 : 0 ≤ δ)
    (hδJ : δ < 1 - Real.sqrt (1 - dC)) (g : ι → F) {T : Finset (ι → F)}
    (hTC : ∀ u ∈ T, u ∈ C) (hTδ : ∀ u ∈ T, relDist g u ≤ δ) :
    (T.card : ℝ) ≤ (dC - δ) / ((1 - δ) ^ 2 - (1 - dC)) := by
  classical
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  -- the radius bookkeeping: δ < 1, the denominator is positive, δ < dC
  have hs0 : (0 : ℝ) ≤ 1 - dC := by linarith
  have hsnn : (0 : ℝ) ≤ Real.sqrt (1 - dC) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (1 - dC) ^ 2 = 1 - dC := Real.sq_sqrt hs0
  have hs1 : Real.sqrt (1 - dC) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have h1δs : Real.sqrt (1 - dC) < 1 - δ := by linarith
  have hδ1 : δ < 1 := by linarith
  have hgap : 1 - dC < (1 - δ) ^ 2 := by
    nlinarith [mul_self_lt_mul_self hsnn h1δs]
  have hgap0 : (0 : ℝ) < (1 - δ) ^ 2 - (1 - dC) := by linarith
  have hs_ge : 1 - dC ≤ Real.sqrt (1 - dC) := by
    nlinarith [mul_nonneg hsnn (sub_nonneg.mpr hs1)]
  have hδdC : δ < dC := by linarith
  -- the exact-size agreement sets: a = ⌈(1−δ)n⌉ coordinates each
  set a : ℕ := ⌈(1 - δ) * (Fintype.card ι : ℝ)⌉₊ with ha'
  have haR : (1 - δ) * (Fintype.card ι : ℝ) ≤ (a : ℝ) := Nat.le_ceil _
  have haN : a ≤ Fintype.card ι := by
    rw [ha']
    refine Nat.ceil_le.mpr ?_
    nlinarith [mul_nonneg hδ0 (le_of_lt hn)]
  have hex : ∀ u : ι → F, ∃ s' : Finset ι,
      u ∈ T → s' ⊆ Finset.univ.filter (fun x => g x = u x) ∧ s'.card = a := by
    intro u
    by_cases hu : u ∈ T
    · obtain ⟨s', hsub, hcard⟩ := Finset.exists_subset_card_eq
        (Nat.ceil_le.mpr (card_agreeFilter_ge_of_relDist_le (hTδ u hu)))
      exact ⟨s', fun _ => ⟨hsub, hcard⟩⟩
    · exact ⟨∅, fun h => absurd h hu⟩
  choose A' hA' using hex
  -- double counting, fact 1: total incidences = L·a
  have key1 : ∑ x : ι, (T.filter fun u => x ∈ A' u).card = T.card * a := by
    calc ∑ x : ι, (T.filter fun u => x ∈ A' u).card
        = ∑ x : ι, ∑ u ∈ T, if x ∈ A' u then 1 else 0 :=
          Finset.sum_congr rfl fun x _ => Finset.card_filter _ _
      _ = ∑ u ∈ T, ∑ x : ι, if x ∈ A' u then 1 else 0 := Finset.sum_comm
      _ = ∑ u ∈ T, (A' u).card := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [← Finset.card_filter]
          congr 1
          rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
      _ = ∑ _u ∈ T, a := Finset.sum_congr rfl fun u hu => (hA' u hu).2
      _ = T.card * a := by rw [Finset.sum_const, smul_eq_mul]
  -- double counting, fact 2: squared incidences = pairwise intersections
  have key2 : ∑ x : ι, (T.filter fun u => x ∈ A' u).card ^ 2
      = ∑ u ∈ T, ∑ v ∈ T, (A' u ∩ A' v).card := by
    have hpt : ∀ x : ι, (T.filter fun u => x ∈ A' u).card ^ 2
        = ∑ u ∈ T, ∑ v ∈ T, if x ∈ A' u ∩ A' v then 1 else 0 := by
      intro x
      rw [sq, Finset.card_filter, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      by_cases h1 : x ∈ A' u <;> by_cases h2 : x ∈ A' v <;>
        simp [h1, h2, Finset.mem_inter]
    calc ∑ x : ι, (T.filter fun u => x ∈ A' u).card ^ 2
        = ∑ x : ι, ∑ u ∈ T, ∑ v ∈ T, if x ∈ A' u ∩ A' v then 1 else 0 :=
          Finset.sum_congr rfl fun x _ => hpt x
      _ = ∑ u ∈ T, ∑ x : ι, ∑ v ∈ T, if x ∈ A' u ∩ A' v then 1 else 0 :=
          Finset.sum_comm
      _ = ∑ u ∈ T, ∑ v ∈ T, ∑ x : ι, if x ∈ A' u ∩ A' v then 1 else 0 :=
          Finset.sum_congr rfl fun u _ => Finset.sum_comm
      _ = ∑ u ∈ T, ∑ v ∈ T, (A' u ∩ A' v).card := by
          refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
          rw [← Finset.card_filter]
          congr 1
          rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  -- the pairwise cap from the minimum distance
  have hoff : ∀ u ∈ T, ∀ v ∈ T, u ≠ v →
      ((A' u ∩ A' v).card : ℝ) ≤ (1 - dC) * (Fintype.card ι : ℝ) := by
    intro u hu v hv huv
    have hAg : AgreesOn (A' u ∩ A' v) u v := by
      intro x hx
      obtain ⟨hxu, hxv⟩ := Finset.mem_inter.mp hx
      have h1 := (Finset.mem_filter.mp ((hA' u hu).1 hxu)).2
      have h2 := (Finset.mem_filter.mp ((hA' v hv).1 hxv)).2
      rw [← h1, ← h2]
    have hbound := hammingDist_add_card_le_of_agreesOn hAg
    have hdist := hdC u (hTC u hu) v (hTC v hv) huv
    have hdn : dC * (Fintype.card ι : ℝ) ≤ (hammingDist u v : ℝ) := by
      rw [relDist, le_div_iff₀ hn] at hdist
      exact hdist
    have hcast : (hammingDist u v : ℝ) + ((A' u ∩ A' v).card : ℝ)
        ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hbound
    nlinarith
  -- assemble the row bound and sum it
  have hsum2 : (∑ u ∈ T, ∑ v ∈ T, ((A' u ∩ A' v).card : ℝ))
      ≤ (T.card : ℝ) * (a : ℝ) + (T.card : ℝ) * ((T.card : ℝ) - 1)
        * ((1 - dC) * (Fintype.card ι : ℝ)) := by
    have hrow : ∀ u ∈ T, ∑ v ∈ T, ((A' u ∩ A' v).card : ℝ)
        ≤ (a : ℝ) + ((T.card : ℝ) - 1) * ((1 - dC) * (Fintype.card ι : ℝ)) := by
      intro u hu
      rw [← Finset.add_sum_erase T _ hu]
      have hdiag : ((A' u ∩ A' u).card : ℝ) = (a : ℝ) := by
        rw [Finset.inter_self]
        exact_mod_cast (hA' u hu).2
      have herase : ∑ v ∈ T.erase u, ((A' u ∩ A' v).card : ℝ)
          ≤ (T.erase u).card • ((1 - dC) * (Fintype.card ι : ℝ)) :=
        Finset.sum_le_card_nsmul _ _ _ fun v hv =>
          hoff u hu v (Finset.mem_of_mem_erase hv)
            (Ne.symm (Finset.ne_of_mem_erase hv))
      have hcarderase : ((T.erase u).card : ℝ) = (T.card : ℝ) - 1 := by
        rw [Finset.card_erase_of_mem hu,
          Nat.cast_sub (Finset.one_le_card.mpr ⟨u, hu⟩), Nat.cast_one]
      rw [nsmul_eq_mul, hcarderase] at herase
      linarith
    calc ∑ u ∈ T, ∑ v ∈ T, ((A' u ∩ A' v).card : ℝ)
        ≤ T.card • ((a : ℝ) + ((T.card : ℝ) - 1)
            * ((1 - dC) * (Fintype.card ι : ℝ))) :=
          Finset.sum_le_card_nsmul _ _ _ hrow
      _ = (T.card : ℝ) * (a : ℝ) + (T.card : ℝ) * ((T.card : ℝ) - 1)
            * ((1 - dC) * (Fintype.card ι : ℝ)) := by
          rw [nsmul_eq_mul]; ring
  -- Cauchy–Schwarz over the incidence counts
  have hCS : (∑ x : ι, ((T.filter fun u => x ∈ A' u).card : ℝ)) ^ 2
      ≤ (Fintype.card ι : ℝ)
        * ∑ x : ι, ((T.filter fun u => x ∈ A' u).card : ℝ) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun x : ι => ((T.filter fun u => x ∈ A' u).card : ℝ))
    rwa [Finset.card_univ] at h
  have key1R : ∑ x : ι, ((T.filter fun u => x ∈ A' u).card : ℝ)
      = (T.card : ℝ) * (a : ℝ) := by exact_mod_cast key1
  have key2R : ∑ x : ι, ((T.filter fun u => x ∈ A' u).card : ℝ) ^ 2
      = ∑ u ∈ T, ∑ v ∈ T, ((A' u ∩ A' v).card : ℝ) := by exact_mod_cast key2
  -- the master inequality: (L·a)² ≤ n·(L·a + L(L−1)·(1−dC)n)
  have master : ((T.card : ℝ) * (a : ℝ)) ^ 2
      ≤ (Fintype.card ι : ℝ) * ((T.card : ℝ) * (a : ℝ)
        + (T.card : ℝ) * ((T.card : ℝ) - 1)
          * ((1 - dC) * (Fintype.card ι : ℝ))) := by
    calc ((T.card : ℝ) * (a : ℝ)) ^ 2
        = (∑ x : ι, ((T.filter fun u => x ∈ A' u).card : ℝ)) ^ 2 := by
          rw [key1R]
      _ ≤ (Fintype.card ι : ℝ)
            * ∑ x : ι, ((T.filter fun u => x ∈ A' u).card : ℝ) ^ 2 := hCS
      _ = (Fintype.card ι : ℝ)
            * ∑ u ∈ T, ∑ v ∈ T, ((A' u ∩ A' v).card : ℝ) := by rw [key2R]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum2 (le_of_lt hn)
  -- endgame: divide out L, normalize by n, transfer the radius
  rcases Nat.eq_zero_or_pos T.card with hT0 | hT1
  · rw [hT0, Nat.cast_zero]
    exact div_nonneg (by linarith) (le_of_lt hgap0)
  · set L : ℝ := (T.card : ℝ) with hL'
    set α : ℝ := (a : ℝ) with hα'
    have hL1 : (1 : ℝ) ≤ L := by rw [hL']; exact_mod_cast hT1
    have hLpos : (0 : ℝ) < L := by linarith
    have h1 : L * α ^ 2 ≤ (Fintype.card ι : ℝ) * α
        + (Fintype.card ι : ℝ) * (L - 1) * ((1 - dC) * (Fintype.card ι : ℝ)) := by
      have hmul : L * (L * α ^ 2) ≤ L * ((Fintype.card ι : ℝ) * α
          + (Fintype.card ι : ℝ) * (L - 1)
            * ((1 - dC) * (Fintype.card ι : ℝ))) := by
        calc L * (L * α ^ 2) = (L * α) ^ 2 := by ring
          _ ≤ (Fintype.card ι : ℝ) * (L * α + L * (L - 1)
                * ((1 - dC) * (Fintype.card ι : ℝ))) := master
          _ = L * ((Fintype.card ι : ℝ) * α + (Fintype.card ι : ℝ) * (L - 1)
                * ((1 - dC) * (Fintype.card ι : ℝ))) := by ring
      exact le_of_mul_le_mul_left hmul hLpos
    have hnne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hn
    have hαN : α ≤ (Fintype.card ι : ℝ) := by rw [hα']; exact_mod_cast haN
    set A : ℝ := α / (Fintype.card ι : ℝ) with hA'
    have hAn1 : 1 - δ ≤ A := by rw [hA', le_div_iff₀ hn]; exact haR
    have hAn2 : A ≤ 1 := by rw [hA', div_le_one hn]; exact hαN
    -- normalized master: L·A² ≤ A + (L−1)·(1−dC)
    have h2 : L * A ^ 2 ≤ A + (L - 1) * (1 - dC) := by
      have hN2 : (0 : ℝ) < (Fintype.card ι : ℝ) ^ 2 := by positivity
      have hdiv := (div_le_div_iff_of_pos_right hN2).mpr h1
      have e1 : L * α ^ 2 / (Fintype.card ι : ℝ) ^ 2 = L * A ^ 2 := by
        rw [hA', div_pow]; ring
      have e2 : ((Fintype.card ι : ℝ) * α + (Fintype.card ι : ℝ) * (L - 1)
            * ((1 - dC) * (Fintype.card ι : ℝ))) / (Fintype.card ι : ℝ) ^ 2
          = A + (L - 1) * (1 - dC) := by
        rw [hA']
        field_simp
      rwa [e1, e2] at hdiv
    -- shed the counting machinery: the endgame is pure real arithmetic
    clear! A'
    clear hTC hTδ hdC haR haN hαN
    have hstep : L * (A ^ 2 - (1 - dC)) ≤ A - (1 - dC) := by nlinarith [h2]
    -- radius transfer: (A − b)/(A² − b) is decreasing in A on the region
    have h1mδ : (0 : ℝ) ≤ 1 - δ := by linarith
    have hA0 : (0 : ℝ) ≤ A := by linarith
    have hfac1 : (0 : ℝ) ≤ A - (1 - δ) := by linarith
    have hfac2 : (0 : ℝ) ≤ A * (1 - δ) - (1 - dC) * (A - δ) := by
      nlinarith [mul_nonneg (mul_nonneg hA0 hdC0) h1mδ,
        mul_nonneg (mul_nonneg hδ0 hs0) (sub_nonneg.mpr hAn2)]
    have hkey : (A - (1 - dC)) * ((1 - δ) ^ 2 - (1 - dC))
        ≤ ((1 - δ) - (1 - dC)) * (A ^ 2 - (1 - dC)) := by
      nlinarith [mul_nonneg hfac1 hfac2]
    have hA2b : (0 : ℝ) < A ^ 2 - (1 - dC) := by
      nlinarith [mul_nonneg hfac1 (by linarith : (0 : ℝ) ≤ A + (1 - δ))]
    have hchain : (L * ((1 - δ) ^ 2 - (1 - dC))) * (A ^ 2 - (1 - dC))
        ≤ ((1 - δ) - (1 - dC)) * (A ^ 2 - (1 - dC)) := by
      calc (L * ((1 - δ) ^ 2 - (1 - dC))) * (A ^ 2 - (1 - dC))
          = (L * (A ^ 2 - (1 - dC))) * ((1 - δ) ^ 2 - (1 - dC)) := by ring
        _ ≤ (A - (1 - dC)) * ((1 - δ) ^ 2 - (1 - dC)) :=
            mul_le_mul_of_nonneg_right hstep (le_of_lt hgap0)
        _ ≤ ((1 - δ) - (1 - dC)) * (A ^ 2 - (1 - dC)) := hkey
    have hfinal : L * ((1 - δ) ^ 2 - (1 - dC)) ≤ (1 - δ) - (1 - dC) :=
      le_of_mul_le_mul_right hchain hA2b
    rw [le_div_iff₀ hgap0]
    linarith

/-- **The Johnson list bound at Reed–Solomon rate ρ = d/n** — the general
bound fed the CITED `reedSolomonCode_minDist` at the literature's rounded
distance `dC := 1 − ρ`, giving the radius `J(ρ) = 1 − √ρ` on the nose:
for `δ < johnsonRadius ρ`, any list of RS codewords within δ of a common
word has size ≤ `(1 − ρ − δ) / ((1 − δ)² − ρ)`. -/
theorem reedSolomon_johnson_list_bound [Nonempty ι] (dom : ι ↪ F) {d : ℕ}
    (hdn : d ≤ Fintype.card ι) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδJ : δ < johnsonRadius ((d : ℝ) / (Fintype.card ι : ℝ)))
    (g : ι → F) {T : Finset (ι → F)}
    (hTC : ∀ u ∈ T, u ∈ reedSolomonCode dom d)
    (hTδ : ∀ u ∈ T, relDist g u ≤ δ) :
    (T.card : ℝ) ≤ (1 - (d : ℝ) / (Fintype.card ι : ℝ) - δ)
      / ((1 - δ) ^ 2 - (d : ℝ) / (Fintype.card ι : ℝ)) := by
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hρ0 : (0 : ℝ) ≤ (d : ℝ) / (Fintype.card ι : ℝ) := by positivity
  have hρ1 : (d : ℝ) / (Fintype.card ι : ℝ) ≤ 1 := by
    rw [div_le_one hn]
    exact_mod_cast hdn
  have hdC : ∀ u ∈ reedSolomonCode dom d, ∀ v ∈ reedSolomonCode dom d,
      u ≠ v → 1 - (d : ℝ) / (Fintype.card ι : ℝ) ≤ relDist u v := by
    intro u hu v hv huv
    refine le_trans ?_ (reedSolomonCode_minDist dom d u hu v hv huv)
    have hdd : ((d : ℝ) - 1) / (Fintype.card ι : ℝ)
        ≤ (d : ℝ) / (Fintype.card ι : ℝ) :=
      (div_le_div_iff_of_pos_right hn).mpr (by linarith)
    linarith
  have hδJ' : δ < 1 - Real.sqrt (1 - (1 - (d : ℝ) / (Fintype.card ι : ℝ))) := by
    rw [show (1 : ℝ) - (1 - (d : ℝ) / (Fintype.card ι : ℝ))
        = (d : ℝ) / (Fintype.card ι : ℝ) from by ring]
    exact hδJ
  have h := johnson_list_bound hdC (by linarith) (by linarith) hδ0 hδJ' g hTC hTδ
  rwa [show (1 : ℝ) - (1 - (d : ℝ) / (Fintype.card ι : ℝ))
      = (d : ℝ) / (Fintype.card ι : ℝ) from by ring] at h

/-! ## WHIR Conjecture 4.12 — historical name, still a LOCAL hypothesis

The landed Lemma 4.10 (`hasMutualCorrelatedAgreement_of_isProximityGenerator`,
CITED) upgrades a proximity generator to MUTUAL correlated agreement only at
the capped bound `B⋆ = max (1 − dC/2) B` — its proof pins the nearby codeword
by UNIQUE decoding and cannot cross `dC/2`. Whether the upgrade holds at the
generator's own bound `B` — for RS with `B = √ρ` (WHIR Thm 4.8 / BCIKS),
i.e. mutual CA on the whole Johnson interval `(0, J(ρ))` — was WHIR
(eprint 2024/1586) Conjecture 4.12. The needed RS/polynomial-generator
Johnson instance is now a theorem in the literature (2025/2051 and
2025/2110; see also the proximity consequences in 2025/2055), but its
proof is not formalized here. The general `Prop` below is also intentionally
broader than that instance. It therefore remains a LOCAL interface,
consumed only as an explicit hypothesis, never an instance or axiom. The
capacity-level conjecture family must not be substituted for it: those
stronger variants are false (2025/2046). -/

/-- **WHIR Conjecture 4.12, as a named conjecture-hypothesis.** For the
generator/code pair: the plain proximity gap at bound `B` upgrades to MUTUAL
correlated agreement at the SAME bound and error — no unique-decoding cap.
The landed Lemma 4.10 PROVES this Prop when `B` already dominates
`1 − dC/2`; its content past `dC/2` (for RS at `B = √ρ`: the band
`(dC/2, J(ρ))`, nonempty by `conjecture_band_nonempty`) is the part not
formalized locally. This definition is the honest LOCAL boundary marker:
everything beyond-UD downstream in this tree must consume it BY NAME. -/
def WHIRConjecture412 (G : ProximityGenerator F ℓ) (C : Submodule F (ι → F))
    (B : ℝ) (err : ℝ → ℝ) : Prop :=
  IsProximityGenerator G C B err → HasMutualCorrelatedAgreement G C B err

omit [DecidableEq ι] in
/-- The conjecture Prop is a satisfiable SHAPE, not a contradiction: over
the full code `⊤` (every function a codeword) the implication holds
outright — the mutual-CA failure event is empty. Satisfiability of the
statement form, NOT a local formalization of the literature's RS theorem. -/
theorem whirConjecture412_top (G : ProximityGenerator F ℓ) :
    WHIRConjecture412 G (⊤ : Submodule F (ι → F)) 0 (fun _ => 0) := by
  intro _ f δ _ _
  have hempty : ∀ r, ¬ MutualCAFailure (⊤ : Submodule F (ι → F)) δ f r := by
    rintro r ⟨S, _, -, i, hifail⟩
    exact hifail (f i) Submodule.mem_top fun x _ => rfl
  rw [G.pr_eq_zero hempty]

/-- **The provable side of the boundary, sharp**: wherever the proximity
bound `B` already dominates the unique-decoding cap `1 − dC/2`, the
conjecture Prop is a THEOREM — the landed Lemma 4.10
(`hasMutualCorrelatedAgreement_of_isProximityGenerator`, CITED) with the
`max` collapsed. So the content not discharged by THIS local Lemma 4.10
route is EXACTLY the band
`B < 1 − dC/2`: for RS at `B = √ρ` and exact distance, that is the
macroscopic regime `√n·(1 − √ρ) > 1` (quantized toy sites with
`√n − √d ≤ 1` fall to this theorem — see `whirConjecture412_sqrtRate_F5`;
the landed F₁₁ site with `√8 − √2 > 1` does not discharge locally). -/
theorem whirConjecture412_of_ud_bound [Nonempty ι] (G : ProximityGenerator F ℓ)
    (C : Submodule F (ι → F)) {B : ℝ} {err : ℝ → ℝ} {dC : ℝ}
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (herr_mono : ∀ {δ₁ δ₂ : ℝ}, 0 < δ₁ → δ₁ ≤ δ₂ → δ₂ < 1 - B →
      err δ₁ ≤ err δ₂)
    (herr_nonneg : ∀ {δ : ℝ}, 0 < δ → δ < 1 - B → 0 ≤ err δ)
    (hB : 1 - dC / 2 ≤ B) :
    WHIRConjecture412 G C B err := fun hPG => by
  have h := hasMutualCorrelatedAgreement_of_isProximityGenerator G C hdC hPG
    (fun h1 h2 h3 => herr_mono h1 h2 h3) (fun h1 h2 => herr_nonneg h1 h2)
  rwa [max_eq_right hB] at h

omit [DecidableEq ι] in
/-- **The reduction — Johnson-regime mutual CA from the named conjecture.**
`WHIRConjecture412` at the RS/`√ρ` instance plus the proximity gap at
`B = √ρ` (BCIKS Thm 1.2's Johnson case — literature-PROVED, here an
honest hypothesis exactly as `Selvage/ReedSolomon.lean` carries it) yields
mutual correlated agreement with `B⋆ = √ρ`: the admissible radius interval
becomes `(0, 1 − √ρ) = (0, johnsonRadius ρ)`, strictly containing the
landed UD interval (`johnson_interval_extends_UD`). The proof is the
one-step discharge — the POINT is that importing a local formalization of
the published RS theorem can discharge this named seam with zero
re-derivation downstream. -/
theorem mutualCA_johnson_of_conj [Nonempty ι] [Fintype F] (dom : ι ↪ F)
    (d : ℕ) {err : ℝ → ℝ}
    (hconj : WHIRConjecture412 (affineGenerator F) (reedSolomonCode dom d)
      (Real.sqrt ((d : ℝ) / (Fintype.card ι : ℝ))) err)
    (hPG : IsProximityGenerator (affineGenerator F) (reedSolomonCode dom d)
      (Real.sqrt ((d : ℝ) / (Fintype.card ι : ℝ))) err) :
    HasMutualCorrelatedAgreement (affineGenerator F) (reedSolomonCode dom d)
      (Real.sqrt ((d : ℝ) / (Fintype.card ι : ℝ))) err :=
  hconj hPG

omit [DecidableEq ι] in
/-- **`mutualCA_johnson` — mutual correlated agreement up to the JOHNSON
radius, REDUCED (not proved): the failure-probability bound at every
`δ ∈ (0, J(ρ))`.** Compare the landed `foldFamily_mutualCA` /
`hasMutualCorrelatedAgreement_UD`, which cap δ at the UD point: under the
two named hypotheses the same conclusion runs to `johnsonRadius ρ`. -/
theorem mutualCA_johnson [Nonempty ι] [Fintype F] (dom : ι ↪ F) (d : ℕ)
    {err : ℝ → ℝ}
    (hconj : WHIRConjecture412 (affineGenerator F) (reedSolomonCode dom d)
      (Real.sqrt ((d : ℝ) / (Fintype.card ι : ℝ))) err)
    (hPG : IsProximityGenerator (affineGenerator F) (reedSolomonCode dom d)
      (Real.sqrt ((d : ℝ) / (Fintype.card ι : ℝ))) err)
    (f : Fin 2 → ι → F) {δ : ℝ} (hδ0 : 0 < δ)
    (hδJ : δ < johnsonRadius ((d : ℝ) / (Fintype.card ι : ℝ))) :
    (affineGenerator F).pr (MutualCAFailure (reedSolomonCode dom d) δ f)
      ≤ err δ :=
  hconj hPG f δ hδ0 hδJ

omit [DecidableEq ι] in
/-- **The seam consumer, cited concretely**: `Selvage/SubUdSeam.lean`'s
`foldFamily_mutualCA` at the Johnson radius — the recovery ladder's rung 4b
for the correlated fold family `![f₀, g]`, radius interval widened from the
UD cap to `(0, J(ρ))` under the named conjecture. This is exactly where the
beyond-UD sub-UD seam (list recovery via `johnson_list_bound` + the
`[OOD-pin-proximity]` selection) would consume mutual CA. -/
theorem foldFamily_mutualCA_johnson [Nonempty ι] [Fintype F]
    {dom : ι ↪ F} {d : ℕ} {err : ℝ → ℝ}
    (hconj : WHIRConjecture412 (affineGenerator F) (reedSolomonCode dom d)
      (Real.sqrt ((d : ℝ) / (Fintype.card ι : ℝ))) err)
    (hPG : IsProximityGenerator (affineGenerator F) (reedSolomonCode dom d)
      (Real.sqrt ((d : ℝ) / (Fintype.card ι : ℝ))) err)
    (f₀ g : ι → F) {δ : ℝ} (hδ0 : 0 < δ)
    (hδJ : δ < johnsonRadius ((d : ℝ) / (Fintype.card ι : ℝ))) :
    (affineGenerator F).pr
      (MutualCAFailure (reedSolomonCode dom d) δ ![f₀, g]) ≤ err δ :=
  mutualCA_johnson dom d hconj hPG ![f₀, g] hδ0 hδJ

/-- **What the conjecture buys, displayed**: the landed Lemma 4.10 cap
`B⋆ = max (1 − dC/2) √ρ` (at the rounded `dC = 1 − ρ`) leaves the interval
`(0, (1 − ρ)/2)`; the conjecture's interval `(0, J(ρ))` is STRICTLY wider
at every rate ρ < 1. -/
theorem johnson_interval_extends_UD {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    1 - max (1 - (1 - ρ) / 2) (Real.sqrt ρ) < johnsonRadius ρ := by
  have hAM : Real.sqrt ρ ≤ (1 + ρ) / 2 := by
    nlinarith [Real.sq_sqrt hρ0, Real.sqrt_nonneg ρ,
      sq_nonneg (1 - Real.sqrt ρ)]
  have hmax : max (1 - (1 - ρ) / 2) (Real.sqrt ρ) = 1 - (1 - ρ) / 2 :=
    max_eq_left (by linarith)
  rw [hmax]
  have h := ud_radius_lt_johnsonRadius hρ0 hρ1
  linarith

/-! ## The sampling bridge — `[SUBUD-johnson]`(iv), PROVED

`t` enters the sub-UD seam only as soundness amplification: a fold δ-far
from its checked shape survives `t` uniformly-drawn column comparisons with
probability ≤ `(1 − δ)^t`. The count is EXACT — the survivor set of
`t`-schedules is the `t`-th power of the agreement set — so the bound is the
agreement mass itself, attained whenever the agreement fraction is exactly
`1 − δ` (`sampling_bridge_tight`). This is the quantitative bridge from the
deployed `t`-column spot checks to the closeness EVENT `hobs` that
`subUdRecover_of_foldFamily` consumes (per-word form; the union over the
committed codeword list is the consumer's step). -/

omit [DecidableEq ι] [Field F] in
/-- The survivor count is a perfect power: `t`-column schedules on which
`g` and `w` agree are exactly the maps into the agreement set. -/
theorem column_sampling_count (t : ℕ) (g w : ι → F) :
    (Finset.univ.filter fun q : Fin t → ι => ∀ j, g (q j) = w (q j)).card
      = (Finset.univ.filter fun x => g x = w x).card ^ t := by
  classical
  have hset : Finset.univ.filter (fun q : Fin t → ι => ∀ j, g (q j) = w (q j))
      = Fintype.piFinset fun _ : Fin t =>
          Finset.univ.filter fun x => g x = w x := by
    ext q
    simp [Fintype.mem_piFinset]
  rw [hset, Fintype.card_piFinset_const]

omit [DecidableEq ι] [Field F] in
/-- **The sampling bridge, count form**: if `g` is δ-far from `w`, at most
a `(1 − δ)^t` fraction of the `n^t` column schedules survives — stated as
the survivor count against `(1 − δ)^t · n^t`. -/
theorem column_sampling_bridge [Nonempty ι] (t : ℕ) {g w : ι → F} {δ : ℝ}
    (hδ : δ ≤ relDist g w) :
    ((Finset.univ.filter fun q : Fin t → ι =>
        ∀ j, g (q j) = w (q j)).card : ℝ)
      ≤ (1 - δ) ^ t * (Fintype.card ι : ℝ) ^ t := by
  classical
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hA := card_agreeFilter_le_of_le_relDist hδ
  rw [column_sampling_count]
  calc (((Finset.univ.filter fun x => g x = w x).card ^ t : ℕ) : ℝ)
      = (((Finset.univ.filter fun x => g x = w x).card : ℝ)) ^ t := by
        push_cast
        ring
    _ ≤ ((1 - δ) * (Fintype.card ι : ℝ)) ^ t :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hA t
    _ = (1 - δ) ^ t * (Fintype.card ι : ℝ) ^ t := mul_pow _ _ _

omit [DecidableEq ι] [Field F] in
/-- **The sampling bridge, fraction form**: the survival probability of a
δ-far pair under `t` uniform independent column checks is ≤ `(1 − δ)^t`. -/
theorem column_sampling_bridge_pr [Nonempty ι] (t : ℕ) {g w : ι → F} {δ : ℝ}
    (hδ : δ ≤ relDist g w) :
    ((Finset.univ.filter fun q : Fin t → ι =>
        ∀ j, g (q j) = w (q j)).card : ℝ) / (Fintype.card ι : ℝ) ^ t
      ≤ (1 - δ) ^ t := by
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hnt : (0 : ℝ) < (Fintype.card ι : ℝ) ^ t := by positivity
  rw [div_le_iff₀ hnt]
  exact column_sampling_bridge t hδ

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation) -/

namespace JohnsonRegimeExample

open RSExample SubUdSeamExample

/-! ### Satisfiable: the Johnson radius computed, the win exhibited -/

/-- **The Johnson win at the deployed-shape rate ρ = 1/2, computed**:
`J(1/2) = 1 − 1/√2 ∈ (0.29, 0.30)`, strictly above the UD radius
`(1 − ρ)/2 = 1/4`. The beyond-UD band is macroscopic. -/
theorem johnson_win_at_rate_half :
    (1 - (1/2 : ℝ)) / 2 < johnsonRadius (1/2) ∧
      (0.29 : ℝ) < johnsonRadius (1/2) ∧ johnsonRadius (1/2) < 0.30 := by
  refine ⟨ud_radius_lt_johnsonRadius (by norm_num) (by norm_num), ?_, ?_⟩
  · unfold johnsonRadius
    have h : Real.sqrt (1/2) < 0.71 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    linarith
  · unfold johnsonRadius
    have h : (0.7 : ℝ) < Real.sqrt (1/2) := by
      have h49 := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 0.49)
        (by norm_num : (0.49 : ℝ) < 1/2)
      rwa [show (0.49 : ℝ) = 0.7 ^ 2 from by norm_num,
        Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 0.7)] at h49
    linarith

/-! ### Teeth: a ball PAST the UD radius with TWO codewords, Johnson-capped

The landed `RS[F₁₁, {0..7}, 2]` corruption site (n = 8, exact distance
`dC = 7/8`, UD radius `7/16`, Johnson radius `1 − √(1/8) ≈ 0.65`). At
`δ = 1/2` the UD pin is genuinely unavailable — and the proved list bound
caps the ball at 3 codewords, with 2 exhibited. -/

/-- The mid word between the zero codeword and `xWord₁₁`: `xWord₁₁` on
`{0,1,2,3}`, zero on `{4,…,7}` — Hamming distance 3 to `0`, 4 to
`xWord₁₁`. -/
def midWord : Fin 8 → ZMod 11 := ![0, 1, 2, 3, 0, 0, 0, 0]

theorem relDist_midWord_zero :
    relDist midWord (0 : Fin 8 → ZMod 11) = 3/8 := by
  rw [relDist,
    show hammingDist midWord (0 : Fin 8 → ZMod 11) = 3 from by decide]
  norm_num [Fintype.card_fin]

theorem relDist_midWord_x : relDist midWord xWord₁₁ = 1/2 := by
  rw [relDist, show hammingDist midWord xWord₁₁ = 4 from by decide]
  norm_num [Fintype.card_fin]

/-- The two-codeword list in the δ = 1/2 ball around `midWord`. -/
def ballList : Finset (Fin 8 → ZMod 11) := {0, xWord₁₁}

theorem ballList_card : ballList.card = 2 := by decide

theorem ballList_mem : ∀ u ∈ ballList, u ∈ reedSolomonCode dom₁₁ 2 := by
  intro u hu
  rcases Finset.mem_insert.mp hu with rfl | hu'
  · exact Submodule.zero_mem _
  · rw [Finset.mem_singleton] at hu'
    subst hu'
    exact xWord₁₁_mem

theorem ballList_close : ∀ u ∈ ballList, relDist midWord u ≤ 1/2 := by
  intro u hu
  rcases Finset.mem_insert.mp hu with rfl | hu'
  · rw [relDist_midWord_zero]; norm_num
  · rw [Finset.mem_singleton] at hu'
    subst hu'
    rw [relDist_midWord_x]

/-- The exact RS distance at the F₁₁ site, in `hdC` shape: `dC = 7/8`
(the CITED `reedSolomonCode_minDist` evaluated). -/
theorem hdC_F11 : ∀ u ∈ reedSolomonCode dom₁₁ 2,
    ∀ v ∈ reedSolomonCode dom₁₁ 2, u ≠ v → (7/8 : ℝ) ≤ relDist u v := by
  intro u hu v hv huv
  have h := reedSolomonCode_minDist dom₁₁ 2 u hu v hv huv
  rw [Fintype.card_fin] at h
  norm_num at h
  linarith

/-- δ = 1/2 sits strictly INSIDE the Johnson radius at `dC = 7/8`:
`√(1/8) < 1/2`. -/
theorem half_lt_johnson_F11 : (1/2 : ℝ) < 1 - Real.sqrt (1 - 7/8) := by
  have h : Real.sqrt (1 - 7/8) < 1/2 := by
    rw [show (1 : ℝ) - 7/8 = 1/8 from by norm_num,
      Real.sqrt_lt' (by norm_num)]
    norm_num
  linarith

/-- **The list bound FIRED**: the two-codeword ball is Johnson-capped at
`(7/8 − 1/2) / ((1/2)² − 1/8) = 3`. -/
theorem ballList_johnson_bounded : (ballList.card : ℝ) ≤ 3 := by
  have hb := johnson_list_bound (dC := 7/8) (δ := 1/2) hdC_F11
    (by norm_num) (by norm_num) (by norm_num) half_lt_johnson_F11
    midWord ballList_mem ballList_close
  calc (ballList.card : ℝ)
      ≤ ((7:ℝ)/8 - 1/2) / ((1 - 1/2) ^ 2 - (1 - 7/8)) := hb
    _ = 3 := by norm_num

/-- **The Johnson teeth, assembled**: δ = 1/2 is PAST the UD radius
`dC/2 = 7/16` (the `subUdRecover_sound` premise fails — the
`beyond_ud_list_ambiguous` phenomenon at word scale), the ball genuinely
holds TWO distinct codewords, and the PROVED bound caps it at 3:
`1 < 2 ≤ 3` — a real list, really small. -/
theorem johnson_ball_past_UD :
    (1 - ((2:ℝ) - 1) / 8) / 2 < 1/2 ∧
      ballList.card = 2 ∧ (ballList.card : ℝ) ≤ 3 :=
  ⟨by norm_num, ballList_card, ballList_johnson_bounded⟩

/-! ### The conjecture band: nonempty exactly where nothing landed reaches -/

/-- **The band WHIR Conj 4.12 governs is NONEMPTY at the landed F₁₁ site**:
`δ = 9/20` sits strictly between the exact UD cap `dC/2 = 7/16` (where the
landed Lemma 4.10 machinery stops) and the Johnson radius
`J(1/4) = 1 − √(1/4) = 1/2` (where the conjecture's reduction delivers
mutual CA). The named conjecture is non-vacuous where its consumers live. -/
theorem conjecture_band_nonempty :
    (1 - ((2:ℝ) - 1) / 8) / 2 < 9/20 ∧
      (9/20 : ℝ) < johnsonRadius ((2:ℝ) / 8) := by
  constructor
  · norm_num
  · unfold johnsonRadius
    rw [show (2:ℝ)/8 = (1/2 : ℝ) ^ 2 from by norm_num,
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/2)]
    norm_num

/-! ### The conjecture Prop inhabited, and the reduction FIRED end-to-end -/

/-- **The conjecture Prop inhabited at a genuine rate-1/2 RS site** — at the
PROVED UD generator's own parameters (`B = (2+ρ)/3 = 5/6`, `err = n/|F|`):
here `B` dominates the exact-distance UD cap `1 − dC/2 = 5/8`, so
`whirConjecture412_of_ud_bound` PROVES the instance. Premise inhabitation
for the conjecture-hypothesis, at a non-degenerate code. -/
theorem whirConjecture412_F5 :
    WHIRConjecture412 (affineGenerator (ZMod 5)) (reedSolomonCode dom₅ 2)
      ((2 + (2 : ℝ) / (Fintype.card (Fin 4) : ℝ)) / 3)
      (fun _ => (Fintype.card (Fin 4) : ℝ) / (Fintype.card (ZMod 5) : ℝ)) := by
  refine whirConjecture412_of_ud_bound _ _ (reedSolomonCode_minDist dom₅ 2)
    (fun _ _ _ => le_refl _)
    (fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ?_
  norm_num [Fintype.card_fin]

/-- **The reduction fired END-TO-END**: the inhabited conjecture instance
fed the PROVED UD proximity generator
(`reedSolomonCode_isProximityGenerator_UD`, CITED) — mutual CA delivered
through the `WHIRConjecture412` channel with every hypothesis discharged.
Honest label: NO new radius at this site (`B = 5/6` is inside the
UD-provable band, and the conclusion matches the landed
`hasMutualCorrelatedAgreement_UD`); the NEW radii live exactly at the
instances that stay open. -/
theorem reduction_fires_F5 :
    HasMutualCorrelatedAgreement (affineGenerator (ZMod 5))
      (reedSolomonCode dom₅ 2)
      ((2 + (2 : ℝ) / (Fintype.card (Fin 4) : ℝ)) / 3)
      (fun _ => (Fintype.card (Fin 4) : ℝ) / (Fintype.card (ZMod 5) : ℝ)) :=
  whirConjecture412_F5 (reedSolomonCode_isProximityGenerator_UD dom₅ 2)

/-- **Even the `B = √ρ` instance is provable at THIS toy site** — the
quantization quirk `√n − √d = 2 − √2 ≤ 1` puts `√(1/2) ≈ 0.707` above the
exact-distance cap `5/8`, so the literature's own bound falls to the UD
theorem here. Premise inhabitation at the conjecture's exact `B`; the OPEN
content of THIS local Lemma 4.10 route is the macroscopic regime
`√n(1 − √ρ) > 1` (already at the landed F₁₁ site,
`√8 − √2 ≈ 1.41 > 1`, this route is unavailable; the published Johnson
theorems are not formalized here). -/
theorem whirConjecture412_sqrtRate_F5 :
    WHIRConjecture412 (affineGenerator (ZMod 5)) (reedSolomonCode dom₅ 2)
      (Real.sqrt ((2 : ℝ) / (Fintype.card (Fin 4) : ℝ)))
      (fun _ => (Fintype.card (Fin 4) : ℝ) / (Fintype.card (ZMod 5) : ℝ)) := by
  refine whirConjecture412_of_ud_bound _ _ (reedSolomonCode_minDist dom₅ 2)
    (fun _ _ _ => le_refl _)
    (fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ?_
  -- 1 − dC/2 = 5/8 ≤ √(1/2), i.e. (5/8)² = 25/64 ≤ 1/2
  rw [Fintype.card_fin, Real.le_sqrt (by norm_num) (by norm_num)]
  norm_num

/-! ### The sampling bridge: bound ATTAINED at F₅ -/

/-- **Sampling-bridge tightness, computed**: `xWord` vs `0` on the landed
F₅ site have relative distance exactly 3/4; at `t = 2` columns the survivor
count is exactly 1 = `(1 − 3/4)² · 4²` — the proved bound holds with
EQUALITY, so `(1 − δ)^t` is not improvable in general. -/
theorem sampling_bridge_tight :
    (Finset.univ.filter fun q : Fin 2 → Fin 4 =>
        ∀ j, xWord (q j) = (0 : Fin 4 → ZMod 5) (q j)).card = 1 ∧
    ((Finset.univ.filter fun q : Fin 2 → Fin 4 =>
        ∀ j, xWord (q j) = (0 : Fin 4 → ZMod 5) (q j)).card : ℝ)
      ≤ (1 - 3/4) ^ 2 * (Fintype.card (Fin 4) : ℝ) ^ 2 ∧
    (1 - (3/4 : ℝ)) ^ 2 * (Fintype.card (Fin 4) : ℝ) ^ 2 = 1 := by
  refine ⟨by decide, ?_, by norm_num [Fintype.card_fin]⟩
  exact column_sampling_bridge 2 (le_of_eq relDist_xWord_zero.symm)

end JohnsonRegimeExample

/-! ## Residual obligation — prose, not a stub

**What CLOSED here (proved, hypothesis-free):** the Johnson radius
`J(ρ) = 1 − √ρ` with its strict win over UD at every rate
(`ud_radius_lt_johnsonRadius`, `johnson_interval_extends_UD`); the Johnson
LIST-SIZE bound for every linear code (`johnson_list_bound`) and its RS
instantiation at radius exactly `J(ρ)` (`reedSolomon_johnson_list_bound`) —
the classical double-counting proof in full, no radius loss, blowing up
only at `J` itself; the `t`-column sampling bridge `(1 − δ)^t`
(`column_sampling_count` / `column_sampling_bridge` / `_pr`), exact and
attained. Keystones fired on the landed F₅/F₁₁ sites: two codewords in a
past-UD ball capped at 3; `J(1/2) ∈ (0.29, 0.30) > 1/4`; the sampling
bound met with equality.

**What is REDUCED locally — the historical conjecture boundary:**

* **`WHIRConjecture412`** — mutual correlated agreement past `dC/2` at the
  generator's own bound (WHIR eprint 2024/1586, Conjecture 4.12).
  The relevant RS/polynomial-generator Johnson instance is PROVED by
  2025/2051 and 2025/2110, with 2025/2055 giving related proximity
  consequences, but those arguments are not formalized locally. The
  stronger capacity-level conjecture family is FALSE (2025/2046), so
  “through Johnson” is the precise positive boundary, not evidence for
  capacity. This file retains the historical name as a parametric `Prop`
  broader than the cited RS instance: satisfiable as a shape
  (`whirConjecture412_top`), non-vacuous where consumed
  (`conjecture_band_nonempty`), and PROVED by the landed Lemma 4.10 whenever
  `B ≥ 1 − dC/2`. Its content not discharged by the local Lemma 4.10 route
  is exactly the band `(dC/2, 1 − B)`. The reductions
  (`mutualCA_johnson_of_conj`, `mutualCA_johnson`,
  `foldFamily_mutualCA_johnson`) are proved: conjecture + Johnson-regime
  proximity gap ⟹ mutual CA on all of `(0, J(ρ))`, in the exact shape the
  sub-UD seam ladder consumes. A faithful local formalization of the
  published RS theorem should discharge this interface at that instance.

**What REMAINS provable but unformalized, named:**

* **(a) The Johnson-regime proximity gap** `hPG` at `B = √ρ` (BCIKS
  2020/654 Thm 1.2 proper / WHIR Thm 4.8): literature-PROVED, genuinely
  heavy (the full BCIKS machinery), carried as the same honest hypothesis
  every landed consumer uses — `[SUBUD-johnson]`(i)'s hard half,
  inherited unchanged. The UD-regime realizer is landed
  (`Selvage/ProximityGapUD.lean`, radius `(1 − ρ)/3`, residual
  `[PROXGAP-tight]`).
* **(b) List-member selection** past `dC/2`: `johnson_list_bound` caps the
  list; picking the intended member is the landed `[OOD-pin-proximity]`
  seam (`Selvage/OutOfDomain.lean`), untouched here.
* **(c) The sharp Johnson constant.** The bound
  `(dC − δ)/((1 − δ)² − (1 − dC))` is the classical double-counting form;
  the literature's `1/(2η√ρ)` parametrization (at `δ = 1 − √ρ − η`) is a
  weakening of it. The alphabet-aware (q-ary) refinement of the Johnson
  bound is not attempted.
* **(d) The list-decoding SEAM assembly**: composing
  `johnson_list_bound` + `mutualCA_johnson` + `[OOD-pin-proximity]` into a
  beyond-UD `subUdRecover` analogue (the list-valued decoder with an OOD
  pin) — the natural next file once (a) or the conjecture's status moves.

Beyond Johnson is a separate frontier, not an extrapolation to capacity:
2026/858 studies threshold halving and 2026/861 the action-orbit route.
Neither is imported by this file, and 2025/2046 rules out the old blanket
capacity conjectures.

## Ledger

* `johnsonRadius` — DEFINED: `J(ρ) = 1 − √ρ`.
* `ud_radius_lt_johnsonRadius` / `johnson_interval_extends_UD` — PROVED:
  the strict interval gain at every rate < 1 (gap `(1 − √ρ)²/2`).
* `card_agreeFilter_ge_of_relDist_le` / `card_agreeFilter_le_of_le_relDist`
  — PROVED: the two counting bridges between `relDist` and the canonical
  agreement set.
* `johnson_list_bound` — PROVED: the Johnson list bound for every linear
  code (double counting + Cauchy–Schwarz + exact-size normalization +
  the factored radius-transfer step).
* `reedSolomon_johnson_list_bound` — PROVED: the RS form at radius
  `J(ρ)`, `reedSolomonCode_minDist` CITED at the rounded distance.
* `WHIRConjecture412` — DEFINED (a `Prop`, nowhere asserted): mutual CA
  past `dC/2` at the generator's own bound — the historical WHIR Conj 4.12
  interface, now literature-proved for the needed RS/polynomial-generator
  Johnson instance but not formalized locally.
* `whirConjecture412_top` — PROVED: the Prop shape is satisfiable (full
  code, degenerate site).
* `whirConjecture412_of_ud_bound` — PROVED (boundary-sharpening): the
  conjecture Prop is a THEOREM wherever `B ≥ 1 − dC/2` (Lemma 4.10 CITED,
  `max` collapsed) — the content left open by that local route is EXACTLY
  `B < 1 − dC/2`; for RS at `√ρ`/exact distance, exactly the macroscopic
  regime `√n(1 − √ρ) > 1`.
* `JohnsonRegimeExample.whirConjecture412_F5` /
  `whirConjecture412_sqrtRate_F5` / `reduction_fires_F5` — PROVED: the
  conjecture Prop inhabited at the genuine rate-1/2 F₅ site (at the proved
  UD generator's `B = 5/6`, and — quantization quirk `√4 − √2 ≤ 1` — even
  at the literature's `B = √ρ`), and the reduction fired END-TO-END through
  the conjecture channel with the PROVED `hPG`; no new radius at that site,
  said plainly — the F₁₁-scale instances (`√8 − √2 > 1`) remain
  undischargeable by the local Lemma 4.10 route alone.
* `mutualCA_johnson_of_conj` / `mutualCA_johnson` /
  `foldFamily_mutualCA_johnson` — PROVED (reductions): conjecture + `hPG`
  at `√ρ` ⟹ mutual CA on `(0, J(ρ))`, in the sub-UD seam's shape.
* `column_sampling_count` / `column_sampling_bridge` / `_pr` — PROVED:
  the `(1 − δ)^t` amplification, exact.
* Keystones — `johnson_win_at_rate_half` (J(1/2) ∈ (0.29, 0.30) > 1/4),
  `johnson_ball_past_UD` (+ `ballList_*`, `hdC_F11`,
  `half_lt_johnson_F11`: two codewords past UD, capped at 3),
  `conjecture_band_nonempty` (the conjecture's band inhabited),
  `sampling_bridge_tight` (bound attained).
* Residual — prose above: (a) `hPG` at `√ρ` (BCIKS, provable-unformalized),
  (b) `[OOD-pin-proximity]` selection (inherited), (c) sharp/q-ary
  constants, (d) the beyond-UD decoder assembly; plus the LOCAL historical
  interface `WHIRConjecture412` (published RS theorem not yet imported,
  named and never silently claimed).

`#print axioms` on `johnson_list_bound`, `reedSolomon_johnson_list_bound`,
`mutualCA_johnson`, `column_sampling_bridge_pr`,
`JohnsonRegimeExample.johnson_ball_past_UD`,
`JohnsonRegimeExample.sampling_bridge_tight`,
`JohnsonRegimeExample.conjecture_band_nonempty`: `propext`,
`Classical.choice`, `Quot.sound` — no `sorryAx` anywhere in the file. -/

end Minidregg.Selvage
