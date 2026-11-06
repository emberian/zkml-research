/-
# Selvage.AuditFlashProveDecide — the audit decision for FlashProve, compiled and exported

The functions a commit-then-audit auditor over FlashProve's `cp_verify` decides with, written in
core Lean only (no Mathlib), so the compiled objects are small enough to link into the Rust auditor
(`breadstuffs/audit-flashprove`). `Selvage/AuditFlashProve.lean` builds the `Round` of
`Selvage/AuditSampling.lean` from THESE constants and proves its legs; the auditor calls THESE
constants through `@[export]`. There is no second copy of the decision anywhere. What every
checker shares (the verdict type, `fires`, the fail-closed `alarm` and its fail-open falsifier
`alarmOpen`, the opening, round and rate rules, the line parser) is `Selvage/AuditDecideCore.lean`.

* `auditVerdict openOk stdout exit expect` — a failed opening of the committed files is a
  rejection; otherwise `verdictOf stdout exit expect`, the checker's verdict on one `cp_verify` call, following
  FlashProve's own acceptance rule (`docs/verifying.md`, "When to accept", points 1, 3, 4, 5, 6;
  points 2, 7, 8 are about where the files and the ID come from, which the auditor discharges by
  building the request and token files from its own committed record): exit status exactly 0, the
  last line of standard output exactly `YES`, exactly one `covered:` line and exactly one
  `result-v1` line, whose fields equal the auditor's own `r`, `e`, `tokens`, `y=yes`,
  `policy=exact-match`, `sh=8`, `status=0`, `claim=exact-match`, `id`, `build`, and `work=0` unless
  proof of work is accepted. Every word of those two lines must be `key=value` (prose is allowed
  only after ` (` on the `covered:` line). Exit 1 is `reject`. Every other ending (any other exit code, a signal,
  a timeout, a missing proof, a spawn failure: `exit = none`) is `noVerdict`.
-/

import Selvage.AuditDecideCore

namespace Minidregg.Selvage.AuditFlashProve

open Minidregg.Selvage.AuditCore

/-- What the auditor already holds before the call: none of it comes from the server or from the
files sent with the proof. -/
structure Expect where
  /-- the commitment ID, 64 lowercase hex digits, pinned at setup -/
  id : String
  /-- the `build=` digest of the `cp_verify` the auditor built itself -/
  build : String
  /-- the request's `r` and `e` -/
  r : Nat
  e : Nat
  /-- whether proof of work may count towards the verifier's bits (point 6) -/
  acceptWork : Bool
  deriving Repr, Inhabited

/-- The `tokens=` value the auditor asks for: the reply tokens `r+1 .. e-1`. A request with a
single checked reply token (`r + 1 = e - 1`) is not in the population and its formatting is not
pinned, so it is rejected (fail-closed) rather than guessed. -/
def tokensOf (r e : Nat) : Option String :=
  if r + 1 < e - 1 then some s!"{r + 1}..{e - 1}" else none

/-- Every field point 5 of the acceptance rule asks of the `covered:` line. -/
def coveredOk (x : Expect) (line : String) : Bool :=
  match fieldsOf line true, tokensOf x.r x.e with
  | some fs, some toks =>
    fieldIs fs "r" (toString x.r) && fieldIs fs "e" (toString x.e)
      && fieldIs fs "tokens" toks && fieldIs fs "y" "yes"
      && fieldIs fs "policy" "exact-match" && fieldIs fs "sh" "8"
  | _, _ => false

/-- The `result-v1` fields: status, claim, the pinned ID, the pinned build, and proof of work only
if the auditor accepts it. -/
def resultOk (x : Expect) (line : String) : Bool :=
  match fieldsOf line false with
  | none => false
  | some fs =>
  fieldIs fs "status" "0" && fieldIs fs "claim" "exact-match" && fieldIs fs "id" x.id
    && fieldIs fs "build" x.build && fieldIs fs "r" (toString x.r)
    && fieldIs fs "e" (toString x.e) && fieldIs fs "y" "yes"
    && fieldIs fs "policy" "exact-match"
    && (x.acceptWork || fieldIs fs "work" "0")

/-- **The checker's verdict on one `cp_verify` call.** `exit = none` is a call that did not end
with an exit status of its own: killed, timed out, never started, or no proof to hand it. -/
def verdictOf (stdout : String) (exit : Option UInt32) (x : Expect) : Verdict :=
  match exit with
  | some 0 =>
    let ok := lastLine stdout == some "YES"
      && ((uniqueTagged stdout "covered:").map (coveredOk x)).getD false
      && ((uniqueTagged stdout "result-v1").map (resultOk x)).getD false
    if ok then .accept else .reject
  | some 1 => .reject
  | _ => .noVerdict

/-- **The audit's verdict.** `openOk` is the auditor's own check that the files it hands to
`cp_verify` are the committed ones: their SHA-256 digests, read with a size cap from a directory
only the auditor writes, equal the record's, and the record opens at its position under the MMR
root. A failed opening is a rejection: the provider did not produce what it committed to. -/
def auditVerdict (openOk : Bool) (stdout : String) (exit : Option UInt32) (x : Expect) : Verdict :=
  if openOk then verdictOf stdout exit x else .reject

/-! ## The C ABI

Bytes and fixed-width words only, plus Lean `String`s that the caller makes with
`lean_mk_string` (owned: the callee consumes them; Lean's `@[export]` takes no borrow annotation). `hasExit = 0` means `exit = none`. -/

@[export minidregg_fp_audit_verdict]
def verdictC (openOk : UInt8) (stdout : String) (hasExit : UInt8) (exitCode : UInt32) (id build : String)
    (r e : UInt32) (acceptWork : UInt8) : UInt8 :=
  (auditVerdict (openOk ≠ 0) stdout (if hasExit = 0 then none else some exitCode)
    { id, build, r := r.toNat, e := e.toNat, acceptWork := acceptWork ≠ 0 }).code

/-! ## Teeth, by evaluation -/

private def sampleOut : String :=
  "proof of work: up to 32 bits counted in 38 rounds\n" ++
  "covered: r=60 e=64 T=64 C=256 theta=256 cap=0 s=16 sh=8 positions=60..63 tokens=61..63 y=yes next-token=no policy=exact-match above-clip=0 (places in the request, counted from 0; y=yes: the answer is about y too)\n" ++
  "result-v1 status=0 claim=exact-match id=79a5 bits=128 work=32 r=60 e=64 T=64 tokens=61..63 y=yes policy=exact-match sh=8 build=93af\n" ++
  "YES\n"

private def sampleExpect : Expect := { id := "79a5", build := "93af", r := 60, e := 64, acceptWork := true }

-- the sample is accepted
#guard verdictOf sampleOut (some 0) sampleExpect == .accept
-- a trailing space on the last line is not `YES`
#guard verdictOf ((sampleOut.splitOn "YES\n").headD "" ++ "YES \n") (some 0) sampleExpect == .reject
-- another ID
#guard verdictOf sampleOut (some 0) { sampleExpect with id := "79a6" } == .reject
-- another range
#guard verdictOf sampleOut (some 0) { sampleExpect with e := 65 } == .reject
-- proof of work refused
#guard verdictOf sampleOut (some 0) { sampleExpect with acceptWork := false } == .reject
-- a second `covered:` line
#guard verdictOf ("covered: r=1\n" ++ sampleOut) (some 0) sampleExpect == .reject
-- exit 5, 2, 124, none
#guard verdictOf sampleOut (some 5) sampleExpect == .noVerdict
#guard verdictOf sampleOut (some 2) sampleExpect == .noVerdict
#guard verdictOf sampleOut (some 124) sampleExpect == .noVerdict
#guard verdictOf sampleOut none sampleExpect == .noVerdict
#guard verdictOf "NO: proof-refused\n" (some 1) sampleExpect == .reject
-- codex round 1: prose smuggled onto the result-v1 line
#guard verdictOf ((sampleOut.splitOn "build=93af").headD "" ++ "build=93af ( work=99 status=1\nYES\n") (some 0) sampleExpect == .reject
-- a bare second covered: line
#guard verdictOf ("covered:\n" ++ sampleOut) (some 0) sampleExpect == .reject
#guard verdictOf ("result-v1\n" ++ sampleOut) (some 0) sampleExpect == .reject
-- a malformed field beside a valid one
#guard verdictOf ((sampleOut.splitOn " build=93af").headD "" ++ " work=1=2 build=93af\nYES\n") (some 0) sampleExpect == .reject
-- a single checked reply token is rejected, not guessed
#guard tokensOf 60 62 == none
-- a failed opening is a rejection even with a perfect output
#guard auditVerdict false sampleOut (some 0) sampleExpect == .reject
#guard auditVerdict true sampleOut (some 0) sampleExpect == .accept
-- codex round 2: an empty digest never matches, even against an empty committed one
#guard !openingOk true true "" "" "" "" none none
#guard pNumOfPpm 1000000 == none && pNumOfPpm 0 == none
#guard pNumOfPpm 10000 == some 184467440737095516
#guard pNumOfPpm 200000 == some 3689348814741910323
#guard auditRoundOk 5 7 && !auditRoundOk 5 6 && !auditRoundOk 0xFFFFFFFFFFFFFFFF 1

end Minidregg.Selvage.AuditFlashProve
