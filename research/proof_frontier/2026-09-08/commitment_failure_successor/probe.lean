import Selvage.CommitmentTraceWitnesses
open Minidregg.Selvage
open CommitmentFreshTrace.Witnesses
#eval (CommitmentFreshTrace.collisionWitness (CommitmentFreshTrace.entries adaptive collision)).isSome
#eval (CommitmentFreshTrace.lateWitness [] (CommitmentFreshTrace.entries adaptive late) 4).isSome
open ArityEight.Witnesses ArityEight.Witnesses.Logged
#eval ((SuppliedOpeningTrace.rowRun H D₀ D₁ D₂ sourceRoot inputRoot nextRoot 0 0 (row 0)).1,
       (SuppliedOpeningTrace.rowRun H D₀ D₁ D₂ sourceRoot inputRoot nextRoot 0 1 (row 1)).1,
       (SuppliedOpeningTrace.rowRun H D₀ D₁ D₂ sourceRoot inputRoot nextRoot 0 0 (row 0)).2.length)
