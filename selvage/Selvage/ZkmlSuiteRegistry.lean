/-
# Selvage.ZkmlSuiteRegistry — the exact admitted Dregg2 zkML suite identity

This is the receiving-side identity boundary for the checked first-order suite
export in `breadstuffs`.  It deliberately registers only source, payload,
protocol, and checker identity.  Registration is not a theorem that the native
Rust checker refines Lean, that Plonky3 is sound, or that the retained BaseFold
and Fiat--Shamir obligations have been discharged.

The payload bytes themselves are checked by
`scripts/check-zkml-suite-artifact.sh`.  Keeping that byte-level check separate
prevents a host JSON parser or SHA implementation from silently entering the
Selvage theorem claim.
-/
import Mathlib.Data.List.Basic

namespace Minidregg.Selvage.ZkmlSuiteRegistry

set_option autoImplicit false

/-- Every identity supplied by a candidate computation before its proof bytes
may be routed to a checker.  All fields participate in exact admission. -/
structure AdmissionRequest where
  suiteId : String
  schemaVersion : Nat
  sourceRepository : String
  sourceCommit : String
  payloadBytes : Nat
  payloadSha256 : String
  protocolId : String
  protocolMode : String
  checkerId : String
  checkerVersion : Nat
  checkerContentIdentity : String
  deriving DecidableEq, Repr

/-- A registered identity plus its intentionally narrow semantic ceiling. -/
structure RegisteredSuite where
  admission : AdmissionRequest
  claimCeiling : String
  namedResiduals : List String
  deriving DecidableEq, Repr

/-- Exact identity emitted from breadstuffs commit `e496fb4` and copied into
`artifacts/zkml-suites`.  The payload identity excludes its trailing newline,
as specified by the source exporter. -/
def dreggIr2BabyBearPoseidonFri : RegisteredSuite where
  admission := {
    suiteId := "dregg.ir2.babybear-ext4.poseidon2-w16.fri.v1"
    schemaVersion := 1
    sourceRepository := "https://github.com/emberian/breadstuffs"
    sourceCommit := "e496fb48d6aaf374d4c0302c95c0fcc69bb8051d"
    payloadBytes := 6654
    payloadSha256 :=
      "b131ed2ad3e9628dbcdbf2bf6c8cf845a6f31f87eea3c91ba8aa00d019c494f0"
    protocolId :=
      "p3-batch-stark/TwoAdicFriPcs@82cfad73cd734d37a0d51953094f970c531817ec"
    protocolMode := "IR-v2 FRI"
    checkerId := "dregg.ir2.verify_vm_descriptor2_with_config"
    checkerVersion := 1
    checkerContentIdentity :=
      "git:e496fb48d6aaf374d4c0302c95c0fcc69bb8051d"
  }
  claimCeiling :=
    "checked source-export and exact suite identity; no deployed verifier refinement"
  namedResiduals := [
    "Rust checker refines the Lean checker",
    "Plonky3 verifier soundness",
    "deployed registry authentication and upgrade policy",
    "BaseFold/Poseidon2 commitment and Fiat--Shamir instantiation"
  ]

/-- The current registry has one admitted suite.  Growth is explicit source
work: unknown suites are not inferred from proof bytes or benchmark fixtures. -/
def registry : List RegisteredSuite := [dreggIr2BabyBearPoseidonFri]

/-- Fail-closed exact lookup.  Every field, including source and checker
content identity, must match the registered request. -/
def lookup (request : AdmissionRequest) : Option RegisteredSuite :=
  if request = dreggIr2BabyBearPoseidonFri.admission then
    some dreggIr2BabyBearPoseidonFri
  else
    none

/-- Successful lookup is equivalent to the one exact registered identity. -/
theorem lookup_some_iff (request : AdmissionRequest) (suite : RegisteredSuite) :
    lookup request = some suite ↔
      request = dreggIr2BabyBearPoseidonFri.admission ∧
        suite = dreggIr2BabyBearPoseidonFri := by
  constructor
  · intro h
    by_cases hrequest : request = dreggIr2BabyBearPoseidonFri.admission
    · have hsuite : dreggIr2BabyBearPoseidonFri = suite := by
        simpa [lookup, hrequest] using h
      exact ⟨hrequest, hsuite.symm⟩
    · simp [lookup, hrequest] at h
  · rintro ⟨rfl, rfl⟩
    simp [lookup]

theorem exact_suite_admitted :
    lookup dreggIr2BabyBearPoseidonFri.admission =
      some dreggIr2BabyBearPoseidonFri := by
  simp [lookup]

theorem unknown_suite_refused :
    lookup { dreggIr2BabyBearPoseidonFri.admission with
      suiteId := "dregg.ir2.unregistered" } = none := by
  native_decide

theorem wrong_source_commit_refused :
    lookup { dreggIr2BabyBearPoseidonFri.admission with
      sourceCommit := "e496fb48d6aaf374d4c0302c95c0fcc69bb8051e" } = none := by
  native_decide

theorem wrong_payload_identity_refused :
    lookup { dreggIr2BabyBearPoseidonFri.admission with
      payloadSha256 :=
        "a131ed2ad3e9628dbcdbf2bf6c8cf845a6f31f87eea3c91ba8aa00d019c494f0" } = none := by
  native_decide

theorem wrong_checker_version_refused :
    lookup { dreggIr2BabyBearPoseidonFri.admission with
      checkerVersion := 2 } = none := by
  native_decide

theorem wrong_checker_content_refused :
    lookup { dreggIr2BabyBearPoseidonFri.admission with
      checkerContentIdentity := "git:unregistered" } = none := by
  native_decide

end Minidregg.Selvage.ZkmlSuiteRegistry
