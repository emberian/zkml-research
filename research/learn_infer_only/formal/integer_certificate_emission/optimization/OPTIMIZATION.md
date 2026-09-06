# Generic arithmetic source simplification

[DERIVED] A generic source simplifier now removes zero products, zero additions,
unit multiplications and computations between constants before the existing
descriptor emitter allocates gates. Its field semantics are proved for every
expression and assignment. At the unchanged 109-bit-Q certificate, emitted gates
fall from 52,378 to 17,344; existing CSE then gives 15,208. This reduces an emitted
arithmetic bill, not the missing BFV convolution, source-binding or privacy work.

[EXECUTED] Both proposed modules pass with 27 exact axiom pins. The isolated
Compiler umbrella, existing import-boundary script and `git apply --check` pass in
`experiments/integer_certificate_emission/optimization/review_01.json`. The first
tranche's pinned artifacts, including its 20-pin patch, are byte-identical before
and after validation. No companion, shared ledger or old-tranche file was edited.
No commits were made. Metered searches: 0.

## Why a source pass

[SOURCE + EXECUTED search] A local `rg` search over all minidregg Compiler/Theory
Lean files for `simplif`, `constantFold`, `foldConst`, `constFold`, smart-add/multiply,
and normalize-Term/System names found no existing arithmetic Term simplifier by
that instrument. `Compiler/EmitShare.lean:70–79` explicitly limits CSE to structural
sharing, without algebraic identities. That existing pass was retained and composed
after the new one.

[SOURCE: local Lean] `Compiler/Air.lean:47–65` defines the actual `AirOp`/`AirSig`
syntax and constructors. `Compiler/Signature.lean:165`, `fold_unique`, provides the
initiality theorem. `Compiler/AirFlatten.lean` and `Compiler/Emit.lean` are the
existing gate allocator/emitter. This patch authors no emitted gates, independent
AIR language, evaluator or checker.

[DERIVED] `Compiler/AirSimplify.lean:43–50` defines `simplify` as a fold of this
same signature. Smart constructors inspect constant roots and implement only:

```
constant + constant  → their field sum
constant * constant  → their field product
0 + x, x + 0         → x
0 * x, x * 0         → 0
1 * x, x * 1         → x
```

[DERIVED] `simplify_eval_hom` at:104 makes evaluation of the simplified term a
homomorphism for the original evaluation algebra; `simplify_preserves` at:110
uses existing initiality for the whole-expression proof. These are field
equalities. The pass does not assert that an arbitrary field equality is an integer
equality; the earlier QR range/carry proofs still carry that obligation.

[DERIVED] `simplifySystem` at:120 also drops syntactically zero constant assertions.
It retains nonzero constant assertions, which remain unsatisfiable. Theorem
`simplifySystem_accepts_iff` at:132 proves exact acceptance equivalence with the
original source system. `emitSimplified_accepts_iff` at:154 composes through the
existing emitter; `checked_emitSimplified_forces` at:176 gives the concrete checker
direction. `fillAux_emitSimplified_holds` at:183 reuses the existing generated
auxiliary evaluator for accepting source assignments. CSE composition is the
generic theorem at:191.

## Witness and falsifiers

[DERIVED] The generic pass has a kernel-proved nonzero public inhabitant at x=3
for an expression containing zero products, nested constant arithmetic, unit-like
additions and a nonzero final target. The optimized descriptor refuses x=4 for every
auxiliary assignment. These are `nonzero_premise_inhabited` and
`wrong_public_value_refused`, at:212 and:218.

[DERIVED + EXECUTED] A deliberately unsafe sibling drops *all* constant assertions.
It accepts `[1=0]`; the original and safe optimized systems refuse. Theorem
`dropping_nonzero_constant_is_failopen` at:231 and an executed generated-descriptor
control preserve that failure. `zero_is_not_a_unit_rewrite` at:247 separately keeps
the `0*x → x` mistake live. These falsifiers identify invalid rewrite rules, not a
weakness of the proved pass.

[DERIVED] `Compiler/IntegerCertificateSimplification.lean` transports the preceding
small/full-modulus signed QR theorems through source simplification and through
simplification followed by CSE. `Small.descriptor_sound`/:27 and
`Small.sharedDescriptor_sound`/:31 preserve the small relation;
`Large.descriptor_sound`/:76 and `Large.sharedDescriptor_sound`/:80 preserve the
full signed equation and remainder range. The small accepting witness and universal
wrong-quotient refusal remain kernel-proved. The large positive evidence remains
compiled, as in the preceding tranche.

[EXECUTED] The unchanged witness generators and existing `fillAux`/
`descriptorHoldsCheck` produce the following controls across four pipelines:
original, original+CSE, simplified, simplified+CSE.

- All 64 small signed coefficients pass; all 64 wrong-quotient variants refuse in
  each pipeline: 256 honest/forged pairs total.
- All 598 single-wire +1 mutations of the simplified small negative witness refuse.
- All seven full-modulus signed/extremal inputs pass; wrong quotient and shifted
  remainder variants refuse in each pipeline: 28 honest/two-forgery triples total.
- A constant-zero assertion is safely removed; a constant-one contradiction is
  retained; the unsafe-drop-all-constants sibling accepts the contradiction.

[EXECUTED] Exact verdicts and the emitted census are in
`experiments/integer_certificate_emission/optimization/results.json`.

## Emitted cost, preserving the scope

[EXECUTED] These are counts from actual Lean-emitted descriptors, not latency or
cryptographic soundness estimates.

| Relation / pass | Gates | Add / multiply | Zero checks | Variables | Wire header |
|---|---:|---:|---:|---:|---:|
| Small original | 570 | 292 / 278 | 141 | 115 | 685 |
| Small CSE | 485 | 250 / 235 | 141 | 115 | 685 |
| Small simplified | 483 | 245 / 238 | 141 | 115 | 598 |
| Small simplified+CSE | 435 | 221 / 214 | 141 | 115 | 598 |
| Large original | 52,378 | 26,361 / 26,017 | 4,555 | 3,773 | 56,151 |
| Large CSE | 21,279 | 13,262 / 8,017 | 4,555 | 3,773 | 56,151 |
| Large simplified | 17,344 | 8,749 / 8,595 | 4,555 | 3,773 | 21,117 |
| Large simplified+CSE | 15,208 | 7,717 / 7,491 | 4,555 | 3,773 | 21,117 |

[EXECUTED] All 16,868 original large zero-product gates disappear before Emit.
Products with a constant operand fall from 22,091 to 4,669, then 4,081 after CSE.
The remaining products include nonzero, nonunit coefficients multiplying variables;
the pass does not incorrectly treat those as fully constant computations.

[DERIVED] Source simplification decreases the wire header because removed
operations never allocate an auxiliary wire. Subsequent CSE still preserves that
new header, leaving its own dropped-auxiliary holes. The 598 all-wire mutation
control applies to the simplified small descriptor **before** CSE; it does not
claim every unused CSE slot is constrained. These two notions of wire savings must
not be conflated.

[DERIVED baseline] Unchanged replication over 3×4096 coefficients would now use
186,875,904 simplified+CSE gates and 55,971,840 zero checks. The wire headers sum to
259,485,696. This remains the coefficient-certificate slice only, before convolution,
source/output-residue binding, commitments, proof protocol, relinearization and
noise. It is an unoptimized replication bill, not a lower bound or a full BFV circuit.

## Reproduce and reuse

[EXECUTED] From `/Users/ember/dev/zkml-research`:

```sh
python3 research/learn_infer_only/experiments/integer_certificate_emission/optimization/check.py
python3 research/learn_infer_only/experiments/integer_certificate_emission/optimization/check.py IntegerCertificateSimplification
python3 research/learn_infer_only/experiments/integer_certificate_emission/optimization/check.py SimplificationChecks
python3 research/learn_infer_only/experiments/integer_certificate_emission/optimization/review.py
python3 research/learn_infer_only/experiments/integer_certificate_emission/optimization/package.py
```

[EXECUTED] Exact compiler commands, source hashes, stdout/stderr and failed development
attempts are retained in this tranche's `compile_*.json`. The harness now checks
successful source-matching dependencies before dependent compilation. `review_01.json`
records all 27 pins, the patch hash and the first-tranche hash comparison. Large
new JSON descriptors are kept in deterministic gzip form; scripts regenerate plain
JSON. All first-tranche descriptor/checker artifacts remain unchanged.

[DERIVED boundary] `minidregg-air-simplification.patch` is a proposed patch, not
applied code or a global replacement of every current Emit call. Its generic
`AirSimplify` module stands on existing minidregg modules; its signed-QR application
module depends on the preserved first-tranche patch. The isolated umbrella uses
existing dependency oleans and is not a clean full `lake build Minidregg`.

[OPEN] The BFV source-scaler lane has this generic import/entry point for its exact
Garner arithmetic certificate. Further savings require another justified compiler
pass or a changed source relation, such as better linear-combination lowering or
range-proof sharing. No latency, proof error, engine-fidelity or privacy claim
follows merely from the reduced gate count.
