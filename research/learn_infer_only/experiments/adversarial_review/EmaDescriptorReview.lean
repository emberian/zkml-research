/-
[EXECUTED only] Independent native descriptor census and full-byte candidate
checks. These are compiled finite checks, not new kernel theorems or a proof
backend. The imported universal semantic theorem is reviewed separately.
-/
import Compiler.ResidentEmaCertificate

open Minidregg.Compiler
open Minidregg.Compiler.DescriptorEval
open Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.ResidentEmaCertificate

#eval show IO Unit from do
  let d := descriptor
  let adds := d.gates.countP (fun gate => gate.op == .add)
  let muls := d.gates.countP (fun gate => gate.op == .mul)
  let residuals := d.gates.length + d.zeros.length
  let coordinates := 8
  let coefficient := residuals - 1 + coordinates
  unless d.nPublic == 4 && d.nVars == 31 && d.nWires == 153 &&
      d.gates.length == 122 && d.zeros.length == 32 &&
      residuals <= 2^coordinates && coefficient == 161 do
    throw (IO.userError "Descriptor census or derived price coefficient changed")
  let mut checked := 0
  for c in [:256] do
    for u in [:256] do
      let total := 7*c+u
      let n := total/8
      let r := total%8
      let arr := candidate c u n r
      unless descriptorHoldsCheck d (fun i => arr.getD i 0) do
        throw (IO.userError s!"Honest full-byte candidate refused at {c},{u}")
      checked := checked+1
  let wrong := candidate 128 248 144 0
  if descriptorHoldsCheck d (fun i => wrong.getD i 0) then
    throw (IO.userError "Wrong logical post accepted by descriptor")
  IO.println s!"EMA_CENSUS public={d.nPublic} variables={d.nVars} wires={d.nWires} gates={d.gates.length} adds={adds} muls={muls} zeros={d.zeros.length} residuals={residuals} sumcheck_coordinates={coordinates} price_numerator={coefficient} fs_rounds={coordinates+1}"
  IO.println s!"EMA_FULL_BYTE_CANDIDATES accepted={checked} wrong_post_refused=true"
