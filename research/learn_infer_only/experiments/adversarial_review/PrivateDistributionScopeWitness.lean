/- Small independent scope teeth for the fair-hidden-seed, one-total-read game. -/
import Theory.PrivateDistributionBudget

namespace PrivateDistributionScopeWitness
open Minidregg.Theory.PrivateDistributionBudget
open Minidregg.Theory.PrivatePolicyEvolution (visible)

def seedAndOneRead (secret : Bool) : Multiset (Bool × Bool) :=
  {(false, visible true (world secret false)),
   (true, visible true (world secret true))}

theorem exposed_seed_recovers (secret seed : Bool) :
    Bool.xor seed (visible true (world secret seed))=secret := by
  cases secret <;> cases seed <;> rfl

theorem fair_seed_but_public_side_information_distinguishes :
    seedAndOneRead false ≠ seedAndOneRead true := by
  decide +kernel

def biasedSamples (secret : Bool) : Multiset Bool :=
  {visible true (world secret false), visible true (world secret false),
   visible true (world secret false), visible true (world secret true)}

theorem biased_seed_changes_event_counts :
    eventCount id (biasedSamples false)=1 ∧
    eventCount id (biasedSamples true)=3 := by
  decide +kernel

/-- info: 'PrivateDistributionScopeWitness.exposed_seed_recovers' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms PrivateDistributionScopeWitness.exposed_seed_recovers
/-- info: 'PrivateDistributionScopeWitness.fair_seed_but_public_side_information_distinguishes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PrivateDistributionScopeWitness.fair_seed_but_public_side_information_distinguishes
/-- info: 'PrivateDistributionScopeWitness.biased_seed_changes_event_counts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PrivateDistributionScopeWitness.biased_seed_changes_event_counts

end PrivateDistributionScopeWitness
