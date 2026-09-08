# Bounded structural preservation proposal

[SOURCE inspected] `Compiler/EmitShare.lean` defines `cseGo` at line 125. A signature
hit inserts `current.out → keptRepresentative` into the substitution and drops the
gate; a miss keeps the rewritten gate with the original output index. `cse` reverses
the accumulated kept list and substitutes output roots. Header fields are unchanged.
Existing reusable facts include `cseGo_kept_mono`, `cseGo_subst_stable`,
`cse_nPublic`, `cse_nVars`, `cse_nWires`, `emit_ssa` and `emit_wellFormed`.
The signature-table preservation lemma `sig_insert_spec` is private to that file.
Search instrument: `rg` over `Compiler/EmitShare.lean` and `Compiler/Emit.lean`; no
claim of absence outside those files.

[DERIVED proposed theorem] A bounded next seam is
`d.SSA → d.WellFormed → (cse d).SSA ∧ (cse d).WellFormed`.
This is enough to instantiate the existing `fillAux` execution laws unconditionally
for every emitted source term list after CSE, using the existing emission theorems.
It does not need a new gate evaluator or a computation over the fixed EMA expression.
It proves less than the stronger initialized-reference checker (SSA + bounds permit
uninitialized sparse holes), but exactly the conditions required by `fillAux` and the
existing source-output theorem. The stronger runtime checker remains appropriate.

[DERIVED induction obligations] Carry the following invariants through `cseGo`:

- Every substitution representative is at most its original index.
- Every signature-table hit names a retained gate; retained outputs precede every
  remaining input-list output.
- Retained gates have bounded operands below their own output and retain auxiliary
  output bounds; the reversed kept list is strictly ordered.
- A miss preserves these properties because operand substitution never increases an
  index. A hit preserves the substitution inequality because its representative is
  from an earlier retained gate.

[DERIVED packaging] Root output bounds follow from substitution non-increase; the
three header fields are unchanged by existing theorems. This gives a generic proof
with structural induction over the original gate list and no EMA-specific arithmetic.
The only likely local map plumbing is the signature invariant update, currently
private, plus `HashMap.getD_insert` cases. It should be owned in a separate successor
module after this generic bridge is frozen. This note proposes the subtask; no new
CSE theorem is claimed or implemented here.

[SOURCE / INFERRED] Direct normalization has an additional obstacle beyond memory:
the Lean toolchain's `Init/Prelude.lean:4645` declares `mixHash` opaque, and CSE's
`DWire`/product hashes use that operation. The 3 GiB Infer probe actually returned a
failed decidable reduction. A structural proof uses abstract HashMap lookup/insert
laws and can therefore avoid evaluating opaque hashes entirely.
