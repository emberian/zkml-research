# Direct matched-field arithmetic for the complete update and linear program

[EXECUTED] Two additive Lean modules prove the arithmetic of the matched-field
backend, including a complete FIFO update followed by all eleven linear stages.
`CHECKS.json` records the individual source-matching Lean checks and 29 pinned
axiom footprints. No native proof or benchmark was run in this formal lane.

[EXECUTED] The main application theorem is
`Minidregg.Compiler.MatchedFieldProgram.updateThenLinearSound`. Given canonical
public rows satisfying the native-shaped equations and the specified public
operand staging, it proves both:

```
model = (acc + fresh + q - old) mod q
trace[10] = inferDot(transforms, evaluationKey, model, query)
```

[DERIVED] The conclusion is equality of every canonical output residue, for both
ciphertext components, all four exact moduli, and all 8,192 coefficients. The
arithmetic head has no carry, range-table, lookup, or LogUp premise. It reuses the
existing `BfvInferComposition` initial operands, rotation operands, fixed public
permutations, residue lifts, and prefix induction. It does not introduce a second
BFV program.

## Exact row bridge

[SOURCE: implementation inspected] `native/src/proof.rs:101` refuses noncanonical
public residues. `MacAir::eval` at line 149 uses sixteen preprocessing columns:
`d[0..3], key0[0..3], key1[0..3], add0, add1, out0, out1`. It asserts main = 0 and,
for both components, `add + sum(d * key) = out`. Both equations are unconditional
on every row, including row 1023. Exact source hashes are in `SOURCE.json`.

[EXECUTED] `MatchedFieldMac.equations_iff` proves that these `ZMod q` equations are
exactly the authorized natural-number MAC modulo q when outputs are canonical.
`complete` constructs accepted canonical rows for all canonical operands.
`allRowsSound` quantifies over every row of any finite domain; there is no terminal
row exemption. `primes_exact` names the four native 50-bit moduli.

[EXECUTED] This arithmetic equivalence requires q > 0, not primality or a bound on
the unreduced integer MAC. Primality and correct Rust field operations remain
necessary to interpret the native field/PCS implementation. This packet does not
supply that implementation refinement or a primality certificate.

## Complete program and witnesses

[SOURCE: implementation inspected] `native/src/linear.rs:397` gives stage zero the
query coefficient and the two model coefficients. Lines 404–414 give the next ten
stages the lifted digits, switching key, previous-plus-permuted addend, previous
second component, and claimed output. `reconstruct_update` at line 499 instead
uses `(fresh0,fresh1,old0,old1)`, keys `(1,0,q-1,0)` and `(0,1,0,q-1)`, and the
accumulator addend. These layouts are the definitions used by the new bridge.

[EXECUTED] `MatchedFieldProgram.Checked` requires a canonical sixteen-column row,
its whole-row equations, and equalities identifying the operands and outputs.
Those equalities bind the staging; they do not assume the result of the MAC.
`linearSound` derives all eleven stages. `updateSound` derives FIFO subtraction,
including the old-residue bound from accepted row canonicality.
`updateThenLinearSound` joins both operations on the same updated model.

[EXECUTED] Nonzero accepted MAC rows produce 47 and 58 at every native modulus;
changing 47 to 48 is refused. A complete update accepts 5 + 7 - 3 = 9 and refuses
12 (omitted expiry). The joined premise witness starts with 1 + 5 - 3 = 3, accepts
all eleven stages on all primes and coefficients, and reaches component values
6,144 and 6. Its transform callbacks and evaluation key are zero. This is a
nonvacuity witness for the abstract program, not a claim that zero callbacks are
the native NTT, a valid cryptographic evaluation key, or a useful learned model.

## Remaining native boundary

[OPEN] This is a source-grounded mathematical equation theorem. Native proof-byte
acceptance is not a Lean premise that automatically implies row equations. The
remaining bridge must justify Rust field operations, AIR polynomial semantics,
PCS/FRI extraction on the complete domain, and the binding of preprocessing to the
consumer-reconstructed rows. SHA-256 and Fiat–Shamir remain explicit security
assumptions; no numerical security level is inherited from the old backend.

[OPEN] Public IO reconstruction still must identify the canonical Rust parser,
NTT/inverse NTT callbacks, query encoding, key indexing, row/chunk coverage, and
caller-selected hashes with the existing BFV program. The theorem covers all
coefficients and all eleven stages; showing that the native consumer supplies
all those premises remains an implementation obligation. BFV decryption/noise
correctness, confidentiality, and the application controller are separate.

## Applying and reproducing

[EXECUTED] `matched-field-arithmetic.patch` adds only
`Compiler/MatchedFieldMac.lean` and `Compiler/MatchedFieldProgram.lean` to
minidregg. It expects the existing BFV composition dependency packet; it does not
modify that packet or any companion tree. Local checks reuse frozen dependency
oleans in an ignored output overlay. Reproduce in this workspace with:

```
python3 research/vfhe_2026_09_08/matched_field/formal/check_one.py MatchedFieldMac
python3 research/vfhe_2026_09_08/matched_field/formal/check_one.py MatchedFieldProgram
```

[EXECUTED] The patch passes `git apply --check` against the read-only companion
and its existing import-boundary script passes. These are applicability/boundary
checks, not a claim that the unmodified companion imports these new modules.
Search query count: zero web, zero Scry. Native runtime runs: zero.
