/-
# `#assert_axioms` and `#assert_axioms_tree` — axiom footprints as checks that can fail

`#assert_axioms foo` elaborates to nothing when `foo` depends on no axiom
outside Lean's three standard ones (`propext`, `Classical.choice`,
`Quot.sound`), and is an error otherwise.  `sorryAx` and `Lean.ofReduceBool`
(the compiler trust of `native_decide`) are therefore refused.

`#assert_axioms_tree` is the same check over the whole package: every constant
declared in one of this package's modules (roots `Theory`, `Compiler`,
`Kernel`, `Assurance`, `Pred`, `Effects`, `Selvage`, `Host`, `Minidregg`) that
the importing module can see. It fails on any constant resting on `sorryAx` or
on a declared axiom, and on any package `axiom` declaration. The compiler trust
(`native_decide`'s auxiliary axioms, `Lean.ofReduceBool`) is admitted there only as a
counted exception, reported in the verdict line: `native_decide` is a
deliberate tool in this tree (the `*_compiled` facts), not a hole. The root
`AxiomCensus` module runs it over the umbrella.

It lives in `Theory/` (it imports only Mathlib's tactic base), so every library
of the tree may import it without crossing the ATLAS §7 import boundary.
Lean v4.30 precomputes each imported declaration's axioms at olean export, so
the census is a lookup per constant, not a walk.
-/
import Mathlib.Tactic.Basic

namespace Minidregg.Theory.AssertAxioms

open Lean Elab Command

/-- The axioms a kernel-checked Mini theorem may rest on. -/
def standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The compiler trust `native_decide` adds; refused by `#assert_axioms`,
counted (not refused) by `#assert_axioms_tree`. In Lean v4.30 each
`native_decide` proof is an auxiliary axiom `<theorem>._native.native_decide.ax_…`
(older toolchains used `Lean.ofReduceBool`). -/
def isCompilerTrust (axiomName : Name) : Bool :=
  axiomName == ``Lean.ofReduceBool || axiomName == ``Lean.trustCompiler ||
    axiomName.components.any (· == `_native)

elab "#assert_axioms " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axioms ← liftCoreM <| collectAxioms name
  let outside := axioms.toList.filter (fun axiomName => !standard.contains axiomName)
  unless outside.isEmpty do
    throwError m!"{name} depends on axioms outside the standard three: {outside}"

/-- This package's module roots. -/
def packageRoots : List Name :=
  [`Theory, `Compiler, `Kernel, `Assurance, `Pred, `Effects, `Selvage, `Host, `Minidregg]

/-- The module a constant was declared in, when it is one of this package's. -/
def packageModule? (env : Environment) (constant : Name) : Option Name := do
  let index ← env.getModuleIdxFor? constant
  let module ← env.header.moduleNames[index.toNat]?
  if packageRoots.contains module.getRoot then some module else none

elab "#assert_axioms_tree" : command => do
  let env ← getEnv
  let mut checked := 0
  let mut compiled := 0
  let mut offenders : Array (Name × List Name) := #[]
  for (constant, info) in env.constants.map₁.toList do
    if (packageModule? env constant).isNone then continue
    checked := checked + 1
    if info matches .axiomInfo _ then
      unless isCompilerTrust constant do offenders := offenders.push (constant, [constant])
      continue
    let axioms ← liftCoreM <| collectAxioms constant
    let outside := axioms.toList.filter (fun axiomName => !standard.contains axiomName)
    if outside.isEmpty then continue
    if outside.all isCompilerTrust then compiled := compiled + 1
    else offenders := offenders.push (constant, outside)
  unless offenders.isEmpty do
    throwError m!"#assert_axioms_tree: {offenders.size} package constants rest on axioms outside the standard three and the compiler trust (first 20): {offenders.toList.take 20}"
  logInfo m!"#assert_axioms_tree: {checked} package constants; {compiled} rest on the compiler trust (native_decide); none on sorryAx or a declared axiom"

end Minidregg.Theory.AssertAxioms
