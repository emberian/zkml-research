/- Executed checks through the existing emitted-descriptor checker. These checks
are logged execution evidence, not axioms or a claim about a Rust compiler. -/
import Compiler.FheSourceCertificateVerifier
import Compiler.FheSourceCertificateWitness

namespace Minidregg.Compiler.FheSourceCertificate
open Minidregg.Compiler
open Minidregg.Compiler.FheRnsScale
open Minidregg.Compiler.IntegerCertificateEmission
open Minidregg.Compiler.DescriptorEval
open Minidregg.Compiler.NativeKernelPlan
open Lean (Json toJson)
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000


def certificateDigits (x : Fin 21 → ℕ) (i : Fin 462) : ℕ :=
  digit 64 (x (groupDigit.symm i).1) (groupDigit.symm i).2.val

def sourceCarry (c : ℕ) (coeff : Fin 462 → ℕ) (x : Fin 462 → ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 => (digit 64 c i+∑ j, digit 64 (coeff j) i*x j+sourceCarry c coeff x i)/64

def installGroup (a : Array BabyBear) (offset bits : ℕ) (values : Array ℕ) : Array BabyBear := Id.run do
  let mut a := a
  for i in [:values.size] do
    a := a.set! (offset+i) (values[i]! : BabyBear)
    for j in [:bits] do
      a := a.set! (offset+values.size+bits*i+j) (digit 2 values[i]! j : BabyBear)
  return a

def cachedCarries (c : ℕ) (coeff ds : Array ℕ) : Array ℕ := Id.run do
  let mut carry := 0
  let mut result := #[0]
  for column in [:57] do
    let mut mass := digit 64 c column+carry
    for j in [:462] do
      mass := mass+digit 64 coeff[j]! column*ds[j]!
    carry := mass/64
    result := result.push carry
  return result

def sourceVariableArray (x : Fin 21 → ℕ) : Array BabyBear := Id.run do
  let xv := Array.ofFn x
  let ds := Array.ofFn (certificateDigits (fun i => xv[i.val]!))
  let mut a := installGroup (Array.replicate 30294 0) 0 6 ds
  for row in List.finRange 12 do
    let c := leftConstant row
    let l := Array.ofFn (digitCoefficient (leftMatrix row))
    let r := Array.ofFn (digitCoefficient (rightMatrix row))
    let mut total := c
    for j in [:462] do total := total+l[j]!*ds[j]!
    a := installGroup a (resultStart row) 6 ((List.range 57).toArray.map (digit 64 total))
    a := installGroup a (resultStart row+399) 15 (cachedCarries c l ds)
    a := installGroup a (resultStart row+1327) 15 (cachedCarries (rightConstant row) r ds)
  return a

def sourceCheck (d : ConstraintDescriptor BabyBear) (x : Fin 21 → ℕ) : Bool :=
  let a := fillAux d (sourceVariableArray x)
  descriptorHoldsCheck d (fun i => a.getD i 0)

def withValue (x : Fin 21 → ℕ) (position : Fin 21) (value : ℕ) : Fin 21 → ℕ :=
  Function.update x position value

def wrongOutput (x : Fin 21 → ℕ) (y : ℕ) : Fin 21 → ℕ :=
  withValue (withValue x 18 y) 19 (deployedQ.toNat-1-y)


def runSourceChecks : IO Unit := do
  IO.println "source certificate: constructing descriptors"
  let d := optimizedSourceDescriptor
  let raw := sourceDescriptor
  let shared := sharedSourceDescriptor
  let cap := sourceValues capturedResidues
  IO.println "source certificate: checking captured positive witness"
  unless sourceCheck d cap do throw <| IO.userError "captured source+1 witness refused"
  IO.println "source certificate: checking raw and CSE controls"
  unless sourceCheck raw cap do throw <| IO.userError "raw emitted witness refused"
  unless sourceCheck shared cap do throw <| IO.userError "existing CSE witness refused"
  IO.println "source certificate: checking forged alternatives"
  if sourceCheck d (wrongOutput cap 172480) then throw <| IO.userError "wrong nearest neighbor accepted"
  let badCorr := withValue (withValue (wrongOutput cap 172480) 15 (cap 15-1)) 16 (cap 16+2*(2^127))
  if sourceCheck d badCorr then throw <| IO.userError "out-of-range correction remainder accepted"
  let badGarner := withValue (withValue cap 12 (cap 12-1)) 13 (cap 13+2*(2^126))
  if sourceCheck d badGarner then throw <| IO.userError "out-of-range Garner remainder accepted"
  let badInput := withValue (withValue cap 0 (deployedBase 0).toNat) 6 0
  if sourceCheck d badInput then throw <| IO.userError "noncanonical input residue accepted"
  let initial := sourceVariableArray cap
  let badDigit := initial.set! 0 64
  let filled := fillAux d badDigit
  if descriptorHoldsCheck d (fun i => filled.getD i 0) then throw <| IO.userError "out-of-range radix digit accepted"
  let cases : List (Fin 6 → ℤ) := [fun _ => 0,fun i => deployedBase i-1,
    fun i => (1234567890123456789*(i.val+1))%deployedBase i,
    fun i => (987654321987654321*(i.val+17))%deployedBase i]
  let mut outputs : Array Json := #[]
  for r in cases do
    let x := sourceValues r
    unless sourceCheck d x do throw <| IO.userError "canonical source row refused"
    let bad := wrongOutput x ((x 18+1)%deployedQ.toNat)
    if sourceCheck d bad then throw <| IO.userError "mutated output accepted"
    outputs := outputs.push <| Json.mkObj [("Y",toJson (toString (deployedOutput r))),
      ("canonical_output",toJson (toString (x 18))),("accepted",toJson true),("wrong_output_refused",toJson true)]
  let result := Json.mkObj [("label",toJson "EXECUTED exact pinned source certificate through existing emitted checker"),
    ("field",toJson babyBearP),("scalar_digits",toJson (462:ℕ)),("groups",toJson (21:ℕ)),
    ("rows",toJson (12:ℕ)),("weighted_accumulators",toJson (24:ℕ)),("columns",toJson (57:ℕ)),
    ("carry_bits",toJson (15:ℕ)),("variables",toJson d.nVars),("raw_gates",toJson raw.gates.length),
    ("existing_CSE_gates",toJson shared.gates.length),("optimized_gates",toJson d.gates.length),
    ("optimized_add_gates",toJson (d.gates.filter fun g => g.op==.add).length),
    ("optimized_mul_gates",toJson (d.gates.filter fun g => g.op==.mul).length),
    ("optimized_zero_checks",toJson d.zeros.length),("optimized_wires",toJson d.nWires),
    ("captured_output",toJson (172481:ℕ)),("wrong_neighbor",toJson (172480:ℕ)),
    ("captured_plus_one_accepted_all_three_descriptors",toJson true),
    ("wrong_neighbor_refused",toJson true),("correction_remainder_range_attack_refused",toJson true),
    ("Garner_remainder_range_attack_refused",toJson true),("noncanonical_residue_refused",toJson true),
    ("out_of_range_digit_refused",toJson true),("additional_rows",Json.arr outputs)]
  IO.FS.writeFile "../../../experiments/bfv_lift_refinement/source_certificate/check-results.json" (result.pretty++"\n")
  writeDescriptorJson "../../../experiments/bfv_lift_refinement/source_certificate/optimized-descriptor.json" d
  IO.println result.pretty

#eval runSourceChecks

end Minidregg.Compiler.FheSourceCertificate
