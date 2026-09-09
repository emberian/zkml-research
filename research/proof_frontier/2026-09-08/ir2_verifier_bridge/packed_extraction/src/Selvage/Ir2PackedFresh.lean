/- Optional classical fresh typed-hash execution composition. The arbitrary
actual-suite theorem is Ir2PackedSoundness; this ideal macro-query law is NOT
a probability model already justified for the deployed PaddingFreeSponge. -/
import Selvage.Ir2PackedSoundness
import Selvage.ShapeRootExtractionFresh

namespace Minidregg.Selvage.Ir2Fri.Packed
open BabyBearExt4 Ir2FriSchedule CommitmentFreshTrace
open scoped Classical
noncomputable section

/-- Five pre-FRI input roots and five prefix-adaptive packed FRI roots. -/
def rootFamily {Digest : Type} (st : Checkpoints Digest) (r : Fin 5 → Ext4)
    (i : Fin 10) : Checkpoint Digest :=
  Sum.elim st.input (fun j => st.fri j (friPrefix r j (by omega))) (finSumFinEquiv.symm i)

def validFamily (i : Fin 10) : Leaf → Prop :=
  Sum.elim (fun b v => v.length=inputLeafLength b) (fun j v => v.length=friLeafLength j) (finSumFinEquiv.symm i)

/-- The extraction residual is exactly one finite family, with no duplicate
root charge for every supplied coordinate or repeated query. -/
theorem failure_iff_family {N : ℕ} (st : Checkpoints (Fin N)) (r : Fin 5 → Ext4) (L : Log (Fin N)) :
    Failure st r L ↔ ShapeRootExtraction.FamilyFailure validFamily
      (fun i => (rootFamily st r i).log) L (fun i => (rootFamily st r i).root) := by
  constructor
  · rintro (⟨b,hb⟩|⟨j,hj⟩)
    · refine ⟨finSumFinEquiv (Sum.inl b : Fin 5 ⊕ Fin 5),?_⟩
      simpa [validFamily,rootFamily] using hb
    · refine ⟨finSumFinEquiv (Sum.inr j : Fin 5 ⊕ Fin 5),?_⟩
      simpa [validFamily,rootFamily] using hj
  · rintro ⟨i,hi⟩
    cases he : (finSumFinEquiv.symm i : Fin 5 ⊕ Fin 5) with
    | inl b => exact Or.inl ⟨b,by simpa [validFamily,rootFamily,he] using hi⟩
    | inr j => exact Or.inr ⟨j,by simpa [validFamily,rootFamily,he] using hi⟩

abbrev Coins (Q N : ℕ) := Fin Q → Fin N

/-- Query/log facts of a causal ideal macro-query execution. Hash response
coins are separate from fresh beta and base query-word coins. Fixing one tape
leaves the other strategy constrained by its relevant prefixes. -/
structure Execution (Q N q : ℕ) [NeZero N] where
  strategy : External q → Strategy Leaf Q N 10
  fresh : ∀ x,CommitmentFreshTrace.Fresh (strategy x)
  checkpoints : Coins Q N → Checkpoints (Fin N)
  proverLog : Coins Q N → External q → Log (Fin N)
  openings : Coins Q N → External q → Openings (Fin N) q
  origins : ∀ c x i, CheckpointOrigin (strategy x) c
    (rootFamily (checkpoints c) x.1 i).log (rootFamily (checkpoints c) x.1 i).root
  checkpoints_logged : ∀ c x,CheckpointsLogged (checkpoints c) x.1 (proverLog c x)
  covered : ∀ c x e,e ∈ proverLog c x ++
    verificationLog (cachedSuite (strategy x) c 0) q (rawQueries x) (openings c x) →
      e ∈ oracleLog (strategy x) c

variable {Q N q : ℕ} [NeZero N]

def executionLog (E : Execution Q N q) (c : Coins Q N) (x : External q) : Log (Fin N) :=
  E.proverLog c x ++ verificationLog (cachedSuite (E.strategy x) c 0) q (rawQueries x) (E.openings c x)

def InitiallyFar (E : Execution Q N q) (c : Coins Q N) : Prop :=
  ¬close (2/5:ℝ) (reedSolomonCode (domain 0) (degree 0)) (extracted (E.checkpoints c)).input

def ExecutionAccepts (E : Execution Q N q) (c : Coins Q N) (x : External q) : Prop :=
  FreshAccepts (cachedSuite (E.strategy x) c 0) (E.checkpoints c) q x (E.openings c x)

/-- The actual shaped failure is covered by the existing fresh-response game.
This is a conditional idealization, with no claim that Poseidon macro-calls are independent. -/
theorem failure_probability (E : Execution Q N q) :
    uniformProb (Coins Q N × External q) (fun y =>
      Failure (E.checkpoints y.1) y.2.1 (executionLog E y.1 y.2)) ≤
      ((3*(Q:ℝ)^2+Q)/2+10*Q)/N := by
  have hs := uniformProb_equiv (Equiv.prodComm (Coins Q N) (External q))
    (fun y => Failure (E.checkpoints y.2) y.1.1 (executionLog E y.2 y.1))
  simp only [Equiv.prodComm_apply,Prod.swap] at hs
  rw [hs]
  apply uniformProb_prod_le (by positivity)
  intro x
  have h := ShapeRootExtraction.oracle_family_failure_probability (E.strategy x) (E.fresh x)
    (fun _ => validFamily)
    (fun c i => (rootFamily (E.checkpoints c) x.1 i).log)
    (fun c => executionLog E c x)
    (fun c i => (rootFamily (E.checkpoints c) x.1 i).root)
    (fun c i => E.origins c x i) (fun c e he => E.covered c x e he)
  exact (uniformProb_congr (fun c => failure_iff_family (E.checkpoints c) x.1 (executionLog E c x))).le.trans h

/-- Complete conditional ideal execution bound for the actual packed q38 profile.
Initial extraction farness is inside the joint event, including on colliding hash tapes. -/
theorem sound (E : Execution Q N 38) :
    uniformProb (Coins Q N × External 38) (fun y => InitiallyFar E y.1 ∧ ExecutionAccepts E y.1 y.2) ≤
      (131064:ℝ)/(modulus^4:ℕ)+
        ((((modulus-1:ℕ):ℝ)/(modulus:ℝ))*(3/5:ℝ)+1/(modulus:ℝ))^38+
      ((3*(Q:ℝ)^2+Q)/2+10*Q)/N := by
  let ideal : Coins Q N × External 38 → Prop := fun y => InitiallyFar E y.1 ∧
    NativeFreshAccepts (extracted (E.checkpoints y.1)) 38 y.2.1 y.2.2
  let bad : Coins Q N × External 38 → Prop := fun y =>
    Failure (E.checkpoints y.1) y.2.1 (executionLog E y.1 y.2)
  have hi : uniformProb (Coins Q N × External 38) ideal ≤
      (131064:ℝ)/(modulus^4:ℕ)+
        ((((modulus-1:ℕ):ℝ)/(modulus:ℝ))*(3/5:ℝ)+1/(modulus:ℝ))^38 := by
    apply uniformProb_prod_le (by positivity)
    intro c
    by_cases hf : InitiallyFar E c
    · exact (uniformProb_mono fun _ h => h.2).trans (native_fresh_38 (extracted (E.checkpoints c)) hf)
    · rw [uniformProb_false (fun _ h => hf h.1)]
      positivity
  have hc : ∀ y : Coins Q N × External 38,
      InitiallyFar E y.1 ∧ ExecutionAccepts E y.1 y.2 → ideal y ∨ bad y := by
    intro y hy
    have h := supplied_cover (cachedSuite (E.strategy y.2) y.1 0) (E.checkpoints y.1)
      38 y.2.1 (rawQueries y.2) (E.openings y.1 y.2) (E.proverLog y.1 y.2)
      (E.checkpoints_logged y.1 y.2) hy.2
    exact h.elim (fun h => Or.inl ⟨hy.1,h⟩) Or.inr
  exact ((uniformProb_mono hc).trans (uniformProb_or_le ideal bad)).trans (add_le_add hi (failure_probability E))

/-- Concrete macro-query accounting: fresh distinct calls are bounded by the
actual prover log plus at most136q verifier records, not by permutation counts. -/
theorem fresh_count_le (E : Execution Q N q) (B : ℕ) (c : Coins Q N) (x : External q)
    (hP : (E.proverLog c x).length ≤ B)
    (hcover : ∀ e ∈ entries (E.strategy x) c,e ∈ executionLog E c x) : Q ≤ B+136*q := by
  have h := fresh_count_le_calls (E.strategy x) (E.fresh x) c (executionLog E c x) hcover
  have hv := verificationLog_length_le (cachedSuite (E.strategy x) c 0) q (rawQueries x) (E.openings c x)
  have hl : (executionLog E c x).length = (E.proverLog c x).length+
      (verificationLog (cachedSuite (E.strategy x) c 0) q (rawQueries x) (E.openings c x)).length :=
    List.length_append
  omega

end
end Minidregg.Selvage.Ir2Fri.Packed

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.failure_iff_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.failure_iff_family

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.failure_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.failure_probability

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.sound

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.fresh_count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.fresh_count_le

