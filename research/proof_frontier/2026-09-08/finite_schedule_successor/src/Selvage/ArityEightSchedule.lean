/- Finite external arity-eight schedules on the existing binary folding tower.
Only a prefix enters each source/injected word. Fresh external scalars remain
independent; the internal powers of each scalar are not independent. -/
import Selvage.ArityEightTwoRound

namespace Minidregg.Selvage.ArityEight.Schedule
open scoped Classical

structure Words (F : Type) (ι : ℕ → Type) where
  word : ∀ n, (Fin n → F) → ι (3*n) → F
  input : ∀ n, (Fin n → F) → ι (3*(n+1)) → F

def Words.wordAt {F : Type} {ι : ℕ → Type} (s : Words F ι)
    {m : ℕ} (r : Fin m → F) (n : ℕ) (hn : n ≤ m) : ι (3*n) → F :=
  s.word n (friPrefix r n hn)

section Tower
variable {F : Type} [Field F] {ell m : ℕ}

/-- The literal three-fold transition plus the prefix-fixed degree-eight input. -/
def literal (T : FoldingTower F (PowerTwoFriLevels ell) (3*m))
    (s : Words F (PowerTwoFriLevels ell)) (j : Fin m) (p : Fin j.val → F) (β : F) :
    PowerTwoFriLevels ell (3*(j.val+1)) → F :=
  fun i => fold8 (T.data (3*j.val) (by omega)) (T.data (3*j.val+1) (by omega))
    (T.data (3*j.val+2) (by omega)) (s.word j p) β i + β^8*s.input j p i

def blockAt (T : FoldingTower F (PowerTwoFriLevels ell) (3*m))
    (s : Words F (PowerTwoFriLevels ell)) (j : Fin m) (r : Fin m → F) :=
  literal T s j (friPrefix r j (Nat.le_of_lt j.isLt)) (r j)

/-- One shared coherent seed vector, projected at each third binary transition. -/
def roundQueries (hell : 3*m ≤ ell) (j : Fin m) {q : ℕ}
    (seed : Fin q → PowerTwoFriLevels ell 1) : Fin q → PowerTwoFriLevels ell (3*(j.val+1)) :=
  powerTwoCoherentRound hell (⟨3*j.val+2,by omega⟩ : Fin (3*m)) seed

def Accepts [DecidableEq F] (T : FoldingTower F (PowerTwoFriLevels ell) (3*m))
    (s : Words F (PowerTwoFriLevels ell)) (deg : ℕ → ℕ) (q : ℕ) (hell : 3*m ≤ ell)
    (r : Fin m → F) (seed : Fin q → PowerTwoFriLevels ell 1) : Prop :=
  s.wordAt r m le_rfl ∈ reedSolomonCode (T.dom (3*m)) (deg m) ∧
  ∀ j : Fin m, ∀ a, s.wordAt r (j+1) (by omega) (roundQueries hell j seed a) =
    blockAt T s j r (roundQueries hell j seed a)

/-- Exceptional round only when its prefix-selected source is far. -/
def BadRound [DecidableEq F] (T : FoldingTower F (PowerTwoFriLevels ell) (3*m))
    (s : Words F (PowerTwoFriLevels ell)) (deg : ℕ → ℕ) (radius : ℕ → ℝ)
    (j : Fin m) (r : Fin m → F) : Prop :=
  ¬close (radius j) (reedSolomonCode (T.dom (3*j.val)) (deg j)) (s.wordAt r j (by omega)) ∧
    close (radius j) (reedSolomonCode (T.dom (3*(j.val+1))) (deg (j+1))) (blockAt T s j r)

end Tower

section Probability
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {ell m : ℕ}

omit [DecidableEq F] in
/-- Reusable probability form of prefix conditioning, with a real per-prefix bound. -/
theorem prefix_challenge_bound (j : Fin m) (p : (Fin j.val → F) → F → Prop)
    {ε : ℝ} (hε : 0 ≤ ε) (hp : ∀ pfx, uniformProb F (p pfx) ≤ ε) :
    uniformProb (Fin m → F) (fun r => p (friPrefix r j (by omega)) (r j)) ≤ ε := by
  let e := splitCoord (β := F) j
  have he := uniformProb_equiv e (fun x =>
    p (friPrefix (e.symm x) j (by omega)) x.2)
  have hrewrite : uniformProb (Fin m → F) (fun r => p (friPrefix r j (by omega)) (r j)) =
      uniformProb (({i : Fin m // i ≠ j} → F) × F)
        (fun x => p (friPrefix (e.symm x) j (by omega)) x.2) := by
    rw [←he]
    apply uniformProb_congr
    intro r
    rw [Equiv.symm_apply_apply]
    rfl
  rw [hrewrite]
  apply uniformProb_prod_le hε
  intro a
  have hc : ∀ b : F, friPrefix (e.symm (a,b)) j (by omega) =
      friPrefix (e.symm (a,0)) j (by omega) := by
    intro b
    funext i
    unfold friPrefix
    have hn : (⟨i.val,by omega⟩ : Fin m) ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      exact (Nat.ne_of_lt i.isLt) hv
    exact (splitCoord_symm_apply_of_ne (a,b) hn).trans (splitCoord_symm_apply_of_ne (a,(0:F)) hn).symm
  calc
    _ = uniformProb F (p (friPrefix (e.symm (a,0)) j (by omega))) :=
      uniformProb_congr fun b => by rw [hc b]
    _ ≤ ε := hp _

/-- Each actual external challenge incurs its own domain-sized error. -/
theorem bad_round_bound (T : FoldingTower F (PowerTwoFriLevels ell) (3*m))
    (s : Words F (PowerTwoFriLevels ell)) (deg : ℕ → ℕ) (radius : ℕ → ℝ)
    (j : Fin m) (hd : 1 ≤ deg (j+1)) (hdeg : deg j = 8*deg (j+1))
    (hρ : 0 < radius j)
    (hrate : (deg (j+1):ℝ) < (1-2*radius j)*(Fintype.card (PowerTwoFriLevels ell (3*(j.val+1))):ℝ)) :
    uniformProb (Fin m → F) (BadRound T s deg radius j) ≤
      ((8*Fintype.card (PowerTwoFriLevels ell (3*(j.val+1))):ℕ):ℝ)/Fintype.card F := by
  apply prefix_challenge_bound j (fun p β =>
    ¬close (radius j) (reedSolomonCode (T.dom (3*j.val)) (deg j)) (s.word j p) ∧
      close (radius j) (reedSolomonCode (T.dom (3*(j.val+1))) (deg (j+1))) (literal T s j p β))
      (by positivity)
  intro p
  by_cases hf : close (radius j) (reedSolomonCode (T.dom (3*j.val)) (deg j)) (s.word j p)
  · rw [uniformProb_false (fun _ h => h.1 hf)]
    positivity
  · have hf' : ¬close (radius j) (reedSolomonCode (T.dom (3*j.val)) (8*deg (j+1))) (s.word j p) := by
      simpa only [←hdeg] using hf
    exact le_trans (uniformProb_mono fun _ h => h.2)
      (fold8_injected_uniform_sound (T.data (3*j.val) (by omega))
        (T.data (3*j.val+1) (by omega)) (T.data (3*j.val+2) (by omega))
        hd hρ hrate (s.word j p) (s.input j p) hf')

/-- The finite challenge error is derived by summing the actual prefix-conditioned rounds. -/
theorem bad_schedule_bound (T : FoldingTower F (PowerTwoFriLevels ell) (3*m))
    (s : Words F (PowerTwoFriLevels ell)) (deg : ℕ → ℕ) (radius : ℕ → ℝ)
    (hd : ∀ j : Fin m, 1 ≤ deg (j+1)) (hdeg : ∀ j : Fin m, deg j = 8*deg (j+1))
    (hρ : ∀ j : Fin m, 0 < radius j)
    (hrate : ∀ j : Fin m, (deg (j+1):ℝ) < (1-2*radius j)*
      (Fintype.card (PowerTwoFriLevels ell (3*(j.val+1))):ℝ)) :
    uniformProb (Fin m → F) (fun r => ∃ j, BadRound T s deg radius j r) ≤
      ∑ j : Fin m, ((8*Fintype.card (PowerTwoFriLevels ell (3*(j.val+1))):ℕ):ℝ)/Fintype.card F := by
  exact le_trans (uniformProb_exists_le _)
    (Finset.sum_le_sum fun j _ => bad_round_bound T s deg radius j (hd j) (hdeg j) (hρ j) (hrate j))

omit [Fintype F] in
/-- A first far-to-close transition must deviate from its literal fold. This
induction retains source farness until a discrepancy occurs. -/
theorem earliest_transition_cover (T : FoldingTower F (PowerTwoFriLevels ell) (3*m))
    (s : Words F (PowerTwoFriLevels ell)) (deg : ℕ → ℕ) (radius : ℕ → ℝ) {τ : ℝ}
    (hfinal : 0 ≤ radius m) (hgap : ∀ j : Fin m, radius (j+1)+τ ≤ radius j)
    (hfar : ¬close (radius 0) (reedSolomonCode (T.dom 0) (deg 0)) (s.word 0 (fun i => i.elim0)))
    (r : Fin m → F) (hgood : ¬∃ j, BadRound T s deg radius j r)
    (hmem : s.wordAt r m le_rfl ∈ reedSolomonCode (T.dom (3*m)) (deg m)) :
    ∃ j : Fin m, τ ≤ relDist (s.wordAt r (j+1) (by omega)) (blockAt T s j r) := by
  by_contra hdev
  push Not at hdev
  have hall : ∀ n (hn : n ≤ m), ¬close (radius n)
      (reedSolomonCode (T.dom (3*n)) (deg n)) (s.wordAt r n hn) := by
    intro n
    induction n with
    | zero =>
      intro hn
      have hp : friPrefix r 0 hn = (fun i => i.elim0) := Subsingleton.elim _ _
      simpa only [Words.wordAt,hp] using hfar
    | succ n ih =>
      intro hn hclose
      let j : Fin m := ⟨n,by omega⟩
      have hs := ih (by omega)
      have hb : ¬close (radius n) (reedSolomonCode (T.dom (3*(n+1))) (deg (n+1)))
          (blockAt T s j r) := fun hf => hgood ⟨j,hs,hf⟩
      obtain ⟨c,hc,hcclose⟩ := hclose
      apply hb
      refine ⟨c,hc,?_⟩
      have ht := relDist_triangle (blockAt T s j r) (s.wordAt r (n+1) hn) c
      rw [relDist_comm (blockAt T s j r) (s.wordAt r (n+1) hn)] at ht
      have hd := hdev j
      have hg := hgap j
      dsimp [j] at hd hg
      linarith
  exact hall m le_rfl ⟨_,hmem,by simpa [relDist, hammingDist] using hfinal⟩

omit [Fintype F] in
set_option maxHeartbeats 800000 in
/-- One coherent tail suffices: select a discrepant transition after all
external challenges are fixed, and use its existing uniform marginal. -/
theorem coherent_query_bound (T : FoldingTower F (PowerTwoFriLevels ell) (3*m))
    (s : Words F (PowerTwoFriLevels ell)) (deg : ℕ → ℕ) (radius : ℕ → ℝ)
    (q : ℕ) (hell : 3*m ≤ ell) {τ : ℝ} (hτ : τ ≤ 1) (hfinal : 0 ≤ radius m)
    (hgap : ∀ j : Fin m, radius (j+1)+τ ≤ radius j)
    (hfar : ¬close (radius 0) (reedSolomonCode (T.dom 0) (deg 0)) (s.word 0 (fun i => i.elim0)))
    (r : Fin m → F) (hgood : ¬∃ j, BadRound T s deg radius j r) :
    uniformProb (Fin q → PowerTwoFriLevels ell 1) (Accepts T s deg q hell r) ≤ (1-τ)^q := by
  by_cases hf : s.wordAt r m le_rfl ∈ reedSolomonCode (T.dom (3*m)) (deg m)
  · obtain ⟨j,hj⟩ := earliest_transition_cover T s deg radius hfinal hgap hfar r hgood hf
    let p : (Fin q → PowerTwoFriLevels ell (3*(j.val+1))) → Prop :=
      fun Q => ∀ a, s.wordAt r (j+1) (by omega) (Q a) = blockAt T s j r (Q a)
    have hpush : uniformProb (Fin q → PowerTwoFriLevels ell 1)
        (fun seed => p (roundQueries hell j seed)) ≤
        uniformProb (Fin q → PowerTwoFriLevels ell (3*(j.val+1))) p :=
      powerTwoCoherentRound_uniform_le hell (⟨3*j.val+2,by omega⟩ : Fin (3*m)) p
    have hmiss : uniformProb (Fin q → PowerTwoFriLevels ell (3*(j.val+1))) p ≤ (1-τ)^q :=
      point_query_miss q hj
    have hsub : uniformProb (Fin q → PowerTwoFriLevels ell 1) (Accepts T s deg q hell r) ≤
        uniformProb (Fin q → PowerTwoFriLevels ell 1) (fun seed => p (roundQueries hell j seed)) :=
      uniformProb_mono fun seed h => h.2 j
    exact hsub.trans (hpush.trans hmiss)
  · rw [uniformProb_false (fun _ h => hf h.1)]
    exact pow_nonneg (sub_nonneg.mpr hτ) _

/-- Finite prefix-adaptive arity-eight terminal soundness. No global event
bound is assumed: challenge errors and the single query tail are derived. -/
theorem sound (T : FoldingTower F (PowerTwoFriLevels ell) (3*m))
    (s : Words F (PowerTwoFriLevels ell)) (deg : ℕ → ℕ) (radius : ℕ → ℝ)
    (q : ℕ) (hell : 3*m ≤ ell) {τ : ℝ}
    (hd : ∀ j : Fin m, 1 ≤ deg (j+1)) (hdeg : ∀ j : Fin m, deg j = 8*deg (j+1))
    (hρ : ∀ j : Fin m, 0 < radius j) (hτ : τ ≤ 1) (hfinal : 0 ≤ radius m)
    (hgap : ∀ j : Fin m, radius (j+1)+τ ≤ radius j)
    (hrate : ∀ j : Fin m, (deg (j+1):ℝ) < (1-2*radius j)*
      (Fintype.card (PowerTwoFriLevels ell (3*(j.val+1))):ℝ))
    (hfar : ¬close (radius 0) (reedSolomonCode (T.dom 0) (deg 0)) (s.word 0 (fun i => i.elim0))) :
    uniformProb ((Fin m → F) × (Fin q → PowerTwoFriLevels ell 1))
      (fun x => Accepts T s deg q hell x.1 x.2) ≤
      (∑ j : Fin m, ((8*Fintype.card (PowerTwoFriLevels ell (3*(j.val+1))):ℕ):ℝ)/Fintype.card F) + (1-τ)^q := by
  let bad := fun r => ∃ j, BadRound T s deg radius j r
  have hb := bad_schedule_bound T s deg radius hd hdeg hρ hrate
  have hq : uniformProb ((Fin m → F) × (Fin q → PowerTwoFriLevels ell 1))
      (fun x => ¬bad x.1 ∧ Accepts T s deg q hell x.1 x.2) ≤ (1-τ)^q := by
    apply uniformProb_prod_le (pow_nonneg (sub_nonneg.mpr hτ) _)
    intro r
    by_cases hbad : bad r
    · rw [uniformProb_false (fun _ h => h.1 hbad)]
      exact pow_nonneg (sub_nonneg.mpr hτ) _
    · exact le_trans (uniformProb_mono fun _ h => h.2)
        (coherent_query_bound T s deg radius q hell hτ hfinal hgap hfar r hbad)
  have hsplit : uniformProb ((Fin m → F) × (Fin q → PowerTwoFriLevels ell 1))
      (fun x => Accepts T s deg q hell x.1 x.2) ≤
      uniformProb ((Fin m → F) × (Fin q → PowerTwoFriLevels ell 1)) (fun x => bad x.1) +
      uniformProb ((Fin m → F) × (Fin q → PowerTwoFriLevels ell 1))
        (fun x => ¬bad x.1 ∧ Accepts T s deg q hell x.1 x.2) := by
    refine le_trans (uniformProb_mono fun x hx => ?_) (uniformProb_or_le _ _)
    by_cases hbad : bad x.1
    · exact Or.inl hbad
    · exact Or.inr ⟨hbad,hx⟩
  rw [TwoRound.uniform_fst (B := Fin q → PowerTwoFriLevels ell 1) bad] at hsplit
  change uniformProb (Fin m → F) bad ≤ _ at hb
  linarith

end Probability
end Minidregg.Selvage.ArityEight.Schedule

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.prefix_challenge_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.prefix_challenge_bound

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.bad_round_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.bad_round_bound

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.bad_schedule_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.bad_schedule_bound

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.earliest_transition_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.earliest_transition_cover

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.coherent_query_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.coherent_query_bound

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.sound
