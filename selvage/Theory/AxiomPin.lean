/-
# `#assert_axioms` — axiom footprints as checks that can fail (core module)

`#assert_axioms foo bar …` elaborates to nothing when every named constant
depends on no axiom outside Lean's three standard ones (`propext`,
`Classical.choice`, `Quot.sound`), and is an error naming every offender
otherwise.  `sorryAx`, a declared project axiom and the compiler trust of
`native_decide` (`Lean.ofReduceBool`, `…._native…`) are therefore refused;
`#assert_compiled` (Theory/AssertCompiled.lean) is the pin for those.

This module imports only `Lean`, so Mathlib-free modules (the Objective Bend
Core4 definitions and proofs) can pin their theorems without taking a Mathlib
dependency.  `Theory.AssertAxioms` re-exports it and adds the tree-wide census.

The axiom footprint of a declaration is pinned where it is stated, as a
`#guard_msgs … #print axioms` pair (the contract manifests that once held it as
a column were deleted on 2026-10-27: docs/COORDINATION-2026-10-27.md §2).
-/
module

public import Lean
meta import Lean

@[expose] public section

namespace Minidregg.Theory.AssertAxioms

open Lean Elab Command

/-- The axioms a kernel-checked Mini theorem may rest on. -/
def standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]

elab "#assert_axioms " ids:ident+ : command => do
  let mut offenders : Array MessageData := #[]
  for id in ids do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axioms ← liftCoreM <| collectAxioms name
    let outside := axioms.toList.filter (fun axiomName => !standard.contains axiomName)
    unless outside.isEmpty do
      offenders := offenders.push m!"{name} depends on axioms outside the standard three: {outside}"
  unless offenders.isEmpty do
    throwError MessageData.joinSep offenders.toList "\n"

end Minidregg.Theory.AssertAxioms
