/-
# Selvage.AuditExactDecide — the audit decision for an exact recompute of gptoss-int v0

Core Lean only, `@[export]`ed to `breadstuffs/audit-flashprove` (`fpaudit`, checker `exact`). The
checker recomputes a committed transcript with gptoss-int v0, the integer gpt-oss-20b of
`zkml-research/research/exact_recompute_2026_11_06` (bit-identical across numpy float64 limbs, JAX
int8 limbs on XLA:CPU and on a Tesla T4), teacher-forced, and reports the integer argmax at every
position that predicts an output token. It decides nothing: THIS module compares what it reported
with what was committed. Its standard output, exit status 0:

    pins spec=<sha256> params=<sha256> weights=<sha256>
    shape prompt=<n> output=<m>
    argmax tokens=<t1>,<t2>,...,<tm>
    DONE

* `reported stdout x` — the argmax list, if the output is well formed FOR THIS AUDIT: last line
  exactly `DONE`; exactly one `pins` line whose three digests are the auditor's pinned spec, params
  and weights (and nothing else); exactly one `shape` line naming the committed prompt length and
  output length; exactly one `argmax` line with one field `tokens=`, decimal naturals without
  leading zeros, as many as the committed output.
* `verdictOf` — exit 0 and a report: `accept` iff the report IS the committed output, else
  `reject`. No report, another exit status, a kill, a timeout, a spawn failure: `noVerdict`.
* `auditVerdict` — a failed opening of the committed files is `reject`.

Fail-closed and the coin come from `Selvage/AuditDecideCore.lean`; `Selvage/AuditExact.lean`
proves that under the transport hypothesis (the recompute reports the spec's argmax or nothing) no
false transcript is accepted with its committed record.
-/
import Selvage.AuditDecideCore

namespace Minidregg.Selvage.AuditExact

open Minidregg.Selvage.AuditCore

/-- What the auditor holds before the call. The pins are set up once; the prompt length and the
output come from the committed record it opened. -/
structure Expect where
  spec : String
  params : String
  weights : String
  promptLen : Nat
  output : List Nat
  deriving Repr, Inhabited

/-- A decimal natural: nonempty, digits only, no leading zero unless it is `0`. -/
def natOf? (w : String) : Option Nat :=
  if w.isEmpty || !(w.all Char.isDigit) || (w.length > 1 && w.front == '0') then none
  else w.toNat?

/-- A comma-separated list of decimal naturals. -/
def tokensOf? (v : String) : Option (List Nat) := (v.splitOn ",").mapM natOf?

/-- The `pins` line: exactly the three fields, each the auditor's own well-formed digest. -/
def pinsOk (x : Expect) (line : String) : Bool :=
  match fieldsOf line false with
  | some fs => fs.length == 3 && isDigest x.spec && isDigest x.params && isDigest x.weights
      && fieldIs fs "spec" x.spec && fieldIs fs "params" x.params && fieldIs fs "weights" x.weights
  | none => false

/-- The `shape` line: exactly the committed prompt length and output length. -/
def shapeOk (x : Expect) (line : String) : Bool :=
  match fieldsOf line false with
  | some fs => fs.length == 2 && fieldIs fs "prompt" (toString x.promptLen)
      && fieldIs fs "output" (toString x.output.length)
  | none => false

/-- The argmax list the recompute reported, if its output is well formed for this audit. -/
def reported (stdout : String) (x : Expect) : Option (List Nat) :=
  if lastLine stdout == some "DONE" && !x.output.isEmpty
      && ((uniqueTagged stdout "pins").map (pinsOk x)).getD false
      && ((uniqueTagged stdout "shape").map (shapeOk x)).getD false then
    match (uniqueTagged stdout "argmax").bind (fieldsOf · false) with
    | some [("tokens", v)] =>
      match tokensOf? v with
      | some ts => if ts.length == x.output.length then some ts else none
      | none => none
    | _ => none
  else none

/-- **The checker's verdict on one recompute.** -/
def verdictOf (stdout : String) (exit : Option UInt32) (x : Expect) : Verdict :=
  match exit with
  | some 0 =>
    match reported stdout x with
    | some ts => if ts == x.output then .accept else .reject
    | none => .noVerdict
  | _ => .noVerdict

/-- **The audit's verdict**: a failed opening is a rejection. -/
def auditVerdict (openOk : Bool) (stdout : String) (exit : Option UInt32) (x : Expect) : Verdict :=
  if openOk then verdictOf stdout exit x else .reject

/-! ## The C ABI -/

/-- `output` is the committed output as the record stores it, `t1,t2,...`; a record the auditor
cannot read as tokens gives no verdict (fail-closed: an alarm). -/
@[export minidregg_exact_audit_verdict]
def verdictC (openOk : UInt8) (stdout : String) (hasExit : UInt8) (exitCode : UInt32)
    (spec params weights : String) (promptLen : UInt32) (output : String) : UInt8 :=
  match tokensOf? output with
  | some ts =>
    (auditVerdict (openOk ≠ 0) stdout (if hasExit = 0 then none else some exitCode)
      { spec, params, weights, promptLen := promptLen.toNat, output := ts }).code
  | none => Verdict.noVerdict.code

/-! ## Teeth, by evaluation -/

private def dA : String := "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
private def dB : String := "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
private def dC : String := "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
private def ex : Expect := { spec := dA, params := dB, weights := dC, promptLen := 5, output := [12, 0, 7] }
private def out (toks : String) : String :=
  s!"gptoss-int v0 recompute\npins spec={dA} params={dB} weights={dC}\nshape prompt=5 output=3\nargmax tokens={toks}\nDONE\n"

#guard verdictOf (out "12,0,7") (some 0) ex == .accept
-- one token differs: the committed transcript is not the integer model's
#guard verdictOf (out "12,0,8") (some 0) ex == .reject
-- too few or too many tokens, a leading zero, a sign, a space, an empty field: no report
#guard verdictOf (out "12,0") (some 0) ex == .noVerdict
#guard verdictOf (out "12,0,7,1") (some 0) ex == .noVerdict
#guard verdictOf (out "12,00,7") (some 0) ex == .noVerdict
#guard verdictOf (out "12,+0,7") (some 0) ex == .noVerdict
#guard verdictOf (out "12,,7") (some 0) ex == .noVerdict
-- another spec, params or weights pin; a missing DONE; a second argmax line
#guard verdictOf (out "12,0,7") (some 0) { ex with spec := dB } == .noVerdict
#guard verdictOf (out "12,0,7") (some 0) { ex with weights := dA } == .noVerdict
#guard verdictOf ((out "12,0,7").replace "DONE\n" "") (some 0) ex == .noVerdict
#guard verdictOf ("argmax tokens=12,0,7\n" ++ out "12,0,7") (some 0) ex == .noVerdict
-- another prompt length
#guard verdictOf (out "12,0,7") (some 0) { ex with promptLen := 6 } == .noVerdict
-- an extra field on the pins line
#guard verdictOf ((out "12,0,7").replace s!"weights={dC}" s!"weights={dC} x=1") (some 0) ex == .noVerdict
-- any exit but 0, or none
#guard verdictOf (out "12,0,7") (some 1) ex == .noVerdict
#guard verdictOf (out "12,0,7") none ex == .noVerdict
-- a failed opening
#guard auditVerdict false (out "12,0,7") (some 0) ex == .reject
-- the C ABI: committed output as text
#guard verdictC 1 (out "12,0,7") 1 0 dA dB dC 5 "12,0,7" == 0
#guard verdictC 1 (out "12,0,7") 1 0 dA dB dC 5 "12,0,8" == 1
#guard verdictC 1 (out "12,0,7") 1 0 dA dB dC 5 "12, 0,7" == 2

end Minidregg.Selvage.AuditExact
