/-
# Selvage.BaseFoldBcsStrictRomLedger — carry rejection through the ROM ledger

The BaseFold sponge-game adapter prices the exact absorbed-block schedule, and
the strict query sampler prices the chance that any ideal query-seed digest has
a zero first lane.  These are distinct losses: sponge indifferentiability is a
construction/ideal-game hop, while fail-closed rejection is the cost of
replacing an always-defined uniform coordinate oracle by the exact BabyBear
decoder.

This module puts both terms in one machine-checked ledger.  The ROM premise is
still the explicitly open ideal-permutation sponge target; no deployed
Poseidon2 assumption is asserted.  No retry policy is present, so the sampler
term is exactly the landed union bound `q / BabyBear.modulus`.
-/

import Selvage.BaseFoldBcsSpongeGame
import Selvage.BaseFoldBcsQuerySamplingJoint

namespace Minidregg.Selvage.BaseFoldBcsStrictRomLedger

open Minidregg.Selvage
open BabyBearExt4
open Minidregg.Selvage.BaseFoldPoseidon2
open Minidregg.Selvage.BaseFoldPoseidon2Rom
open Minidregg.Selvage.BaseFoldBcsFiatShamir
open Minidregg.Selvage.BaseFoldBcsSpongeGame
open Minidregg.Selvage.BaseFoldBcsQuerySampling

set_option autoImplicit false

noncomputable section

/-- The exact local ROM-plus-sampling ledger.  `work` counts primitive sponge
evaluations; `queryCount` counts independently drawn query-seed digests. -/
def strictRomSamplingError (work queryCount : Nat) : Real :=
  romError work + (queryCount : Real) / (modulus : Real)

/-- The receipt-indexed sponge advantage and fail-closed rejection probability
fit the combined ledger exactly.  The two probabilities live on their honest
sample spaces and are combined only by addition, ready for a later union-bound
composition with raw-IOR and collision events. -/
theorem constructionDistinguisher_rom_and_rejection_bound
    {m queryCount : Nat}
    (hrom : romConstructionTarget)
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool) :
    |realProb (constructionDistinguisher statement receipt verdict) (0, 0) -
        idealProb (constructionDistinguisher statement receipt verdict) (0, 0)| +
        uniformProb (Fin queryCount → Digest) QuerySeedRejection
      ≤ strictRomSamplingError
          (transcriptPrimitiveWork statement receipt) queryCount := by
  exact add_le_add
    (constructionDistinguisher_romBound hrom statement receipt verdict)
    (querySeedRejection_le queryCount)

/-- An arithmetic composition rule for the next proof layer.  Any raw-IOR
false-accept bound can add the exact construction/sampling ledger without
renaming or dropping either term. -/
theorem add_rawFailure_le_strictLedger
    {m queryCount : Nat} {tau rawFailure equivocation : Real}
    (rawBound :
      rawFailure ≤
        (m : Real) * (3 / Fintype.card E) +
          (1 - tau) ^ queryCount + equivocation)
    {receiptWork : Nat} {romAdvantage rejection : Real}
    (romAndRejection :
      romAdvantage + rejection ≤
        strictRomSamplingError receiptWork queryCount) :
    rawFailure + romAdvantage + rejection ≤
      (m : Real) * (3 / Fintype.card E) +
        (1 - tau) ^ queryCount + equivocation +
          strictRomSamplingError receiptWork queryCount := by
  linarith

#check @strictRomSamplingError
#check @constructionDistinguisher_rom_and_rejection_bound
#check @add_rawFailure_le_strictLedger

/-- info: 'Minidregg.Selvage.BaseFoldBcsStrictRomLedger.constructionDistinguisher_rom_and_rejection_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms constructionDistinguisher_rom_and_rejection_bound

end

end Minidregg.Selvage.BaseFoldBcsStrictRomLedger
