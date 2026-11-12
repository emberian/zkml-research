/-
# Selvage.AuditDecideCore — what every commit-then-audit decision shares, compiled and exported

Core Lean only (no Mathlib), linked into the Rust auditors (`breadstuffs/audit-flashprove`). The
checker-specific verdicts live beside it: `Selvage/AuditFlashProveDecide.lean` (FlashProve's
`cp_verify`) and `Selvage/AuditExactDecide.lean` (an exact recompute of gptoss-int v0).
`Selvage/AuditChecked.lean` builds the `Round` of `Selvage/AuditSampling.lean` from these constants.

* `fires coin pNum` — the selection rule: the round's 64-bit coin is below `pNum`.
* `alarm fired v` — FAIL-CLOSED: a fired audit alarms on every verdict but `accept`.
* `alarmOpen fired v` — the FAIL-OPEN falsifier: alarms only on `reject`.
* `openingOk`, `auditRoundOk`, `pNumOfPpm` — the auditor's eligibility rules.
* the line parser every checker's output goes through: `outputLines`, `lastLine`,
  `uniqueTagged`, `fieldsOf`, `field`, `fieldIs`.
-/

namespace Minidregg.Selvage.AuditCore

/-- The checker's verdict on one call. -/
inductive Verdict where
  | accept
  | reject
  | noVerdict
  deriving DecidableEq, Repr, Inhabited

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

/-- The lines whose first space-separated word is exactly `tag`. -/
def taggedLines (stdout tag : String) : List String :=
  (outputLines stdout).filter fun l => (l.splitOn " ").head? == some tag

/-- The unique line tagged `tag`; `none` if there are zero or several. -/
def uniqueTagged (stdout tag : String) : Option String :=
  match taggedLines stdout tag with
  | [l] => some l
  | _ => none

/-- One word as `key=value`: exactly one `=`, a nonempty key. Anything else is malformed. -/
def kv? (w : String) : Option (String × String) :=
  match w.splitOn "=" with
  | [k, v] => if k.isEmpty then none else some (k, v)
  | _ => none

/-- The fields of a tagged line: every word after the tag must be `key=value`, or the line is
malformed (`none`). For the `covered:` line the words are read up to the first ` (`, which opens
the prose `cp_verify` appends there; no other line may carry prose. -/
def fieldsOf (line : String) (prose : Bool) : Option (List (String × String)) :=
  let head := if prose then (line.splitOn " (").headD "" else line
  ((head.splitOn " ").drop 1).mapM kv?

/-- The value of `key` if it occurs exactly once among the fields. -/
def field (fs : List (String × String)) (key : String) : Option String :=
  match fs.filter (fun kv => kv.1 == key) with
  | [kv] => some kv.2
  | _ => none

/-- `field fs key = some v`, as a Boolean. -/
def fieldIs (fs : List (String × String)) (key v : String) : Bool :=
  field fs key == some v

/-- A digest as the record and the staging step write it: exactly 64 lowercase hex digits. -/
def isDigest (d : String) : Bool :=
  d.length == 64 && d.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- **The opening check.** Staging succeeded (every handed file was a regular file, read within
the cap, into a fresh private directory); the request and token digests are well-formed and equal
the record's; the proof digest equals the record's, or both say "no proof"; and the record opens at
its position under the root (`mmrOk`, the `dregg-query` `verify_range` result, whose own Lean model
is `Dregg2.Lightclient.MMR`). -/
def openingOk (stageOk mmrOk : Bool) (reqC yC reqS yS : String) (proofC proofS : Option String) :
    Bool :=
  stageOk && mmrOk && isDigest reqC && isDigest yC && reqC == reqS && yC == yS
    && match proofC, proofS with
      | some a, some b => isDigest a && a == b
      | none, none => true
      | _, _ => false

/-- The audit round is the requester's seen round plus two. -/
def auditRoundOk (seen round : UInt64) : Bool := seen < 0xFFFFFFFFFFFFFFF0 && round == seen + 2

/-- The rate in parts per million as `⌊ppm · 2^64 / 10^6⌋`, or `none` outside `0 < ppm < 10^6`:
a 100% rate is not representable as `coin < pNum`, and a 0% rate has `q = 0`. -/
def pNumOfPpm (ppm : UInt64) : Option UInt64 :=
  if 0 < ppm && ppm < 1000000 then some (UInt64.ofNat (ppm.toNat * 2 ^ 64 / 1000000)) else none

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

Bytes and fixed-width words only, plus Lean `String`s that the caller makes with `lean_mk_string`
(owned: the callee consumes them). -/

@[export minidregg_audit_fires]
def firesC (coin pNum : UInt64) : UInt8 := if fires coin pNum then 1 else 0

@[export minidregg_audit_alarm]
def alarmC (fired verdict : UInt8) : UInt8 :=
  if alarm (fired ≠ 0) (Verdict.ofCode verdict) then 1 else 0

@[export minidregg_audit_alarm_open]
def alarmOpenC (fired verdict : UInt8) : UInt8 :=
  if alarmOpen (fired ≠ 0) (Verdict.ofCode verdict) then 1 else 0

@[export minidregg_audit_opening_ok]
def openingOkC (stageOk mmrOk : UInt8) (reqC yC reqS yS : String) (hasProofC : UInt8)
    (proofC : String) (hasProofS : UInt8) (proofS : String) : UInt8 :=
  if openingOk (stageOk ≠ 0) (mmrOk ≠ 0) reqC yC reqS yS
      (if hasProofC = 0 then none else some proofC) (if hasProofS = 0 then none else some proofS)
  then 1 else 0

@[export minidregg_audit_round_ok]
def auditRoundOkC (seen round : UInt64) : UInt8 := if auditRoundOk seen round then 1 else 0

/-- `0` for an unrepresentable rate, else `pNum` (never `0` for a valid rate: `ppm ≥ 1` gives
`pNum ≥ 2^64/10^6 > 0`). -/
@[export minidregg_audit_pnum_of_ppm]
def pNumOfPpmC (ppm : UInt64) : UInt64 := (pNumOfPpm ppm).getD 0

#guard alarm true .noVerdict && !alarmOpen true .noVerdict
#guard alarm true .reject && !alarm true .accept && !alarm false .reject
#guard fires 4 5 && !fires 5 5
#guard lastLine "a\nYES\n" == some "YES" && lastLine "YES\n\n" == some ""
#guard fieldsOf "t k=v (prose" true == some [("k", "v")] && fieldsOf "t k=v (prose" false == none

end Minidregg.Selvage.AuditCore
