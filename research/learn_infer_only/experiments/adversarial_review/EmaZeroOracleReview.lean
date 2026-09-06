/-
[EXECUTED only] Compiled finite bad-oracle sample. This is not a concrete hash
attack or a contradiction of random-oracle soundness: the checker accepts a
false descriptor at the deliberately constant-zero oracle. It preserves the
need for the separate satisfying-descriptor premise or probabilistic game.
-/
import Assurance.ResidentEmaWitness

open Minidregg.Assurance.ResidentEmaWitness
open Minidregg.Assurance.ResidentEmaRelease
open Minidregg.Compiler.ResidentEmaCertificate
open Minidregg.Compiler.CommittedTerminalFiatShamir
open Minidregg.Compiler.CommittedTerminalRealizer
open Minidregg.Compiler.NativeKernelPlan
open Minidregg.Selvage

#eval show IO Unit from do
  let w := candidateWord 128 248 144 0
  let O : SrMove (reduction forged.plan.context) 0 → Ext6L := fun _ => ext6Zero
  let rc := fsProve (scheme forged.plan.context).commit descriptor (bitCorner 8)
    descriptor_nonempty O ((scheme forged.plan.context).commit w) w
  let checked := Minidregg.Assurance.ResidentEmaRelease.check forged O rc
  let satisfies := descriptorHoldsCheck descriptor (traceOf rc.word)
  unless checked && !satisfies do
    throw (IO.userError "Expected deliberate bad-oracle sample was not reproduced")
  IO.println s!"EMA_ZERO_ORACLE_SAMPLE receipt_check={checked} descriptor_holds={satisfies} wrong_biased_post=144 correct_biased_post=143"
