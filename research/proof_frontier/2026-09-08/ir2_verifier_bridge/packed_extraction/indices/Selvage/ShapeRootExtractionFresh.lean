/- Finite checkpoint-family accounting for shape-directed extraction.
The price is solely the existing ideal fresh typed macro-query law. -/
import Selvage.ShapeRootExtraction

namespace Minidregg.Selvage.ShapeRootExtraction
open EfficientRootOpening CommitmentFreshTrace
open scoped Classical
variable {Value : Type} {Q N R : ℕ}

/-- Failure at any member of the actual finite family of checkpoint roots and public leaf shapes. -/
def FamilyFailure (valid : Fin R → Value → Prop) (P : Fin R → Log Value (Fin N))
    (L : Log Value (Fin N)) (root : Fin R → Fin N) : Prop :=
  ∃ i, Bad (valid i) (P i) L (root i)

/-- Statement-first causal cover. The shared trace already accounts for every declared root. -/
def FamilyCoverContract (A : Strategy Value Q N R) : Prop :=
  ∀ (c : Fin Q → Fin N) (valid : Fin R → Value → Prop)
    (P : Fin R → Log Value (Fin N)) (L : Log Value (Fin N)) (root : Fin R → Fin N),
    (∀ i, CheckpointOrigin A c (P i) (root i)) → LogCovered A c L →
    FamilyFailure valid P L root → CommitmentFreshTrace.Bad A c

/-- Narrow same-role, same-shape failures are covered once by the existing causal trace event. -/
theorem family_failure_cover (A : Strategy Value Q N R) : FamilyCoverContract A := by
  intro c valid P L root hO hL hF
  obtain ⟨i,hi⟩ := hF
  exact checkpoint_bad_cover A c (P i) L (root i) (hO i) hL
    (bad_to_unfiltered (valid i) (P i) L (root i) hi)

/-- Ideal uniform-response-tape bound for the entire checkpoint family.
No actual PaddingFreeSponge/Poseidon price or desired event-bound premise enters. -/
theorem family_failure_probability [NeZero N] (A : Strategy Value Q N R)
    (valid : (Fin Q → Fin N) → Fin R → Value → Prop)
    (P : (Fin Q → Fin N) → Fin R → Log Value (Fin N))
    (logs : (Fin Q → Fin N) → Log Value (Fin N))
    (root : (Fin Q → Fin N) → Fin R → Fin N)
    (hO : ∀ c i, CheckpointOrigin A c (P c i) (root c i))
    (hL : ∀ c, LogCovered A c (logs c)) :
    uniformProb (Fin Q → Fin N) (fun c => FamilyFailure (valid c) (P c) (logs c) (root c)) ≤
      ((3*(Q:ℝ)^2+Q)/2+R*Q)/N :=
  (uniformProb_mono fun c h => family_failure_cover A c (valid c) (P c) (logs c)
    (root c) (hO c) (hL c) h).trans (bad_probability A)

/-- The same ideal law through the existing lazy-sampling handler, with freshness explicit. -/
theorem oracle_family_failure_probability [NeZero N] (A : Strategy Value Q N R) (hf : Fresh A)
    (valid : (Fin Q → Fin N) → Fin R → Value → Prop)
    (P : (Fin Q → Fin N) → Fin R → Log Value (Fin N))
    (logs : (Fin Q → Fin N) → Log Value (Fin N))
    (root : (Fin Q → Fin N) → Fin R → Fin N)
    (hO : ∀ c i, CheckpointOrigin A c (P c i) (root c i))
    (hL : ∀ c e, e ∈ logs c → e ∈ oracleLog A c) :
    uniformProb (Fin Q → Fin N) (fun c => FamilyFailure (valid c) (P c) (logs c) (root c)) ≤
      ((3*(Q:ℝ)^2+Q)/2+R*Q)/N := by
  apply family_failure_probability A valid P logs root hO
  intro c e he
  simpa only [oracleLog_eq_entries A hf c] using hL c e he

end Minidregg.Selvage.ShapeRootExtraction

/-- info: 'Minidregg.Selvage.ShapeRootExtraction.family_failure_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ShapeRootExtraction.family_failure_cover

/-- info: 'Minidregg.Selvage.ShapeRootExtraction.family_failure_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ShapeRootExtraction.family_failure_probability

/-- info: 'Minidregg.Selvage.ShapeRootExtraction.oracle_family_failure_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ShapeRootExtraction.oracle_family_failure_probability
