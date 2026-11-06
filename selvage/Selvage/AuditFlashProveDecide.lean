/-
# Selvage.AuditFlashProveDecide — the audit decision for FlashProve, compiled and exported

The functions a commit-then-audit auditor over FlashProve's `cp_verify` decides with, written in
core Lean only (no Mathlib), so the compiled objects are small enough to link into the Rust auditor
(`breadstuffs/audit-flashprove`). `Selvage/AuditFlashProve.lean` builds the `Round` of
`Selvage/AuditSampling.lean` from THESE constants and proves its legs; the auditor calls THESE
constants through `@[export]`. There is no second copy of the decision anywhere.

* `fires coin pNum` — the selection rule `Sel`: the round's 64-bit coin is below `pNum`, so the
  nominal rate is `pNum / 2^64`.
* `verdictOf stdout exit expect` — the checker's verdict on one `cp_verify` call, following
  FlashProve's own acceptance rule (`docs/verifying.md`, "When to accept", points 1, 3, 4, 5, 6;
  points 2, 7, 8 are about where the files and the ID come from, which the auditor discharges by
  building the request and token files from its own committed record): exit status exactly 0, the
  last line of standard output exactly `YES`, exactly one `covered:` line and exactly one
  `result-v1` line, whose fields equal the auditor's own `r`, `e`, `tokens`, `y=yes`,
  `policy=exact-match`, `sh=8`, `status=0`, `claim=exact-match`, `id`, `build`, and `work=0` unless
  proof of work is accepted. Exit 1 is `reject`. Every other ending (any other exit code, a signal,
  a timeout, a missing proof, a spawn failure: `exit = none`) is `noVerdict`.
* `alarm fired v` — FAIL-CLOSED: a fired audit alarms on every verdict but `accept`.
* `alarmOpen fired v` — the FAIL-OPEN falsifier: a fired audit alarms only on `reject`, so a
  `noVerdict` reads as acceptance. `Selvage/AuditFlashProve.lean` proves it collapses `q`.
-/

namespace Minidregg.Selvage.AuditFlashProve

/-- The checker's verdict on one call. -/
inductive Verdict where
  | accept
  | reject
  | noVerdict
  deriving DecidableEq, Repr, Inhabited

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

/-- **The selection rule.** The audit fires iff the 64-bit coin is below `pNum`. -/
def fires (coin pNum : UInt64) : Bool := decide (coin < pNum)

/-- The lines of standard output. A trailing newline ends the last line; it does not open an empty
one. Any other empty line is kept, so `"YES\n\n"` ends in an empty line, not in `YES`. -/
def outputLines (stdout : String) : List String :=
  let ls := stdout.splitOn "\n"
  match ls.getLast? with
  | some "" => ls.dropLast
  | _ => ls

/-- The last line of standard output, if there is one. -/
def lastLine (stdout : String) : Option String := (outputLines stdout).getLast?

/-- The unique line beginning with `pfx`; `none` if there are zero or several. -/
def uniqueLine (stdout : String) (pfx : String) : Option String :=
  match (outputLines stdout).filter (fun l => l.startsWith pfx) with
  | [l] => some l
  | _ => none

/-- The `key=value` fields of a line, read up to the first ` (`, which opens the prose that
`cp_verify` appends to its `covered:` line. -/
def fieldsOf (line : String) : List (String × String) :=
  let head := (line.splitOn " (").headD ""
  (head.splitOn " ").filterMap fun w =>
    match w.splitOn "=" with
    | [k, v] => some (k, v)
    | _ => none

/-- The value of `key` if it occurs exactly once among the fields. -/
def field (fs : List (String × String)) (key : String) : Option String :=
  match fs.filter (fun kv => kv.1 == key) with
  | [kv] => some kv.2
  | _ => none

/-- `field fs key = some v`, as a Boolean. -/
def fieldIs (fs : List (String × String)) (key v : String) : Bool :=
  field fs key == some v

/-- The `tokens=` value the auditor asks for: the reply tokens `r+1 .. e-1`. -/
def tokensOf (r e : Nat) : String := s!"{r + 1}..{e - 1}"

/-- Every field point 5 of the acceptance rule asks of the `covered:` line. -/
def coveredOk (x : Expect) (line : String) : Bool :=
  let fs := fieldsOf line
  fieldIs fs "r" (toString x.r) && fieldIs fs "e" (toString x.e)
    && fieldIs fs "tokens" (tokensOf x.r x.e) && fieldIs fs "y" "yes"
    && fieldIs fs "policy" "exact-match" && fieldIs fs "sh" "8"

/-- The `result-v1` fields: status, claim, the pinned ID, the pinned build, and proof of work only
if the auditor accepts it. -/
def resultOk (x : Expect) (line : String) : Bool :=
  let fs := fieldsOf line
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
      && ((uniqueLine stdout "covered: ").map (coveredOk x)).getD false
      && ((uniqueLine stdout "result-v1 ").map (resultOk x)).getD false
    if ok then .accept else .reject
  | some 1 => .reject
  | _ => .noVerdict

/-- **Fail-closed alarm.** A fired audit alarms on every verdict but `accept`. -/
def alarm (fired : Bool) (v : Verdict) : Bool := fired && v != .accept

/-- **Fail-open alarm, the falsifier.** A fired audit alarms only on `reject`. -/
def alarmOpen (fired : Bool) (v : Verdict) : Bool := fired && v == .reject

/-- The verdict as a byte: 0 accept, 1 reject, 2 no verdict. -/
def Verdict.code : Verdict → UInt8
  | .accept => 0
  | .reject => 1
  | .noVerdict => 2

/-- The byte back to a verdict; anything unknown is `noVerdict`. -/
def Verdict.ofCode (c : UInt8) : Verdict :=
  if c = 0 then .accept else if c = 1 then .reject else .noVerdict

/-! ## The C ABI

Bytes and fixed-width words only, plus Lean `String`s that the caller makes with
`lean_mk_string` (owned: the callee consumes them; Lean's `@[export]` takes no borrow annotation). `hasExit = 0` means `exit = none`. -/

@[export minidregg_fp_audit_fires]
def firesC (coin pNum : UInt64) : UInt8 := if fires coin pNum then 1 else 0

@[export minidregg_fp_audit_verdict]
def verdictC (stdout : String) (hasExit : UInt8) (exitCode : UInt32) (id build : String)
    (r e : UInt32) (acceptWork : UInt8) : UInt8 :=
  (verdictOf stdout (if hasExit = 0 then none else some exitCode)
    { id, build, r := r.toNat, e := e.toNat, acceptWork := acceptWork ≠ 0 }).code

@[export minidregg_fp_audit_alarm]
def alarmC (fired verdict : UInt8) : UInt8 :=
  if alarm (fired ≠ 0) (Verdict.ofCode verdict) then 1 else 0

@[export minidregg_fp_audit_alarm_open]
def alarmOpenC (fired verdict : UInt8) : UInt8 :=
  if alarmOpen (fired ≠ 0) (Verdict.ofCode verdict) then 1 else 0

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
#guard alarm true .noVerdict && !alarmOpen true .noVerdict
#guard fires 4 5 && !fires 5 5

end Minidregg.Selvage.AuditFlashProve
