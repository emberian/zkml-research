# Pinned BFV scaler: modular and machine-word arithmetic

2026-09-06. Research patch for the read-only Minidregg tree. The preceding
27/33/23/22-pin BFV artifacts remain byte-identical. This tranche adds proofs and
small executable checks, not an encryption implementation or a new descriptor.

## What closes

[DERIVED, kernel checked] A passing frozen source-plus-target checker now implies
that each external target limb equals the **complete handwritten per-target word
formula** transcribed from the pinned scaler. The endpoint is
`Minidregg.Compiler.FheRnsSourceWord.accepted_target_matches_source` at
`Compiler/FheRnsSourceWord.lean:179`.

It has no added caller-supplied canonicality hypothesis. The new
`source_check_canonical` theorem extracts canonical source residues from the
already enforced source descriptor, then applies `sourceWordRefinement`:

```text
every canonical six-residue input r, every target i:
  sourceWordTarget(r,i) = deployedOutput(r) mod targetPrime(i)

every passing frozen source-plus-target checker:
  externalTarget[i] = sourceWordTarget(r,i)
```

[DERIVED, kernel checked] The word formula includes the source's sign/magnitude
correction branches, projected gamma and omega constants, lazy Shoup products,
two-word Barrett reductions, 2p negations, u128 accumulation and final canonical
reduction. All arithmetic bounds needed by these modeled operations are
discharged for the deployed six-to-three parameter instance. The captured
nearest-plus-one row remains inhabited and gives 172481 in all three target
limbs; its tempting 172480 neighbor is refused.

**[OPEN] This is a theorem about a handwritten model of the pinned source's
equations. It is not a Rust language, compiler, unsafe-array, constructor or NTT
refinement theorem.** The source correspondence is inspected and experimentally
checked, not produced by a verified Rust extractor.

## Exact source locations

[SOURCE: implementation read] All paths below are under
`/Users/ember/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/fhe-math-0.1.1/`.
`experiments/bfv_lift_refinement/modular_lowering/source-map.json` retains full
paths, SHA256 hashes, line intervals and theorem correspondence.

| Source | Operation actually inspected | Checked model endpoint |
|---|---|---|
| `src/zq/mod.rs:17–22` | Boolean mask/xor selection | `FheBarrettWord.mask_selection` |
| `src/zq/mod.rs:54–69` | Modulus bounds and Barrett reciprocal construction | `FheRnsSourceWord.target_word_bounds` |
| `src/zq/mod.rs:169–208` | Shoup reciprocal and lazy multiplication | `FheShoupWord.wordLazyShoup_correct` |
| `src/zq/mod.rs:577–580` | Canonical u128 reduction wrapper | `FheBarrettWord.wordReduce_correct` |
| `src/zq/mod.rs:635–645` | One-step correction of a lazy residue | `FheBarrettWord.wordReduceOne_correct` |
| `src/zq/mod.rs:672–687` | Split-word lazy Barrett reduction | `FheBarrettWord.wordLazyBarrett_correct` |
| `src/rns/scaler.rs:76–116` | Gamma/omega projection and Shoup setup | Projected-product theorem; Rust constructor remains inspected source |
| `src/rns/scaler.rs:250–304` | Garner index and signed correction branches | Prior 33-pin word model plus new magnitude bounds |
| `src/rns/scaler.rs:307–340` | Per-target initialization, correction, products and output | `FheRnsSourceWord.sourceWordRefinement` |
| `src/rns/mod.rs:109–119` | BigUint projection to residues | Inspected source; no Rust BigUint proof |

The pinned `src/zq/mod.rs` hash is
`12d082a17076f9f1b46a642958df1fc0ecef3b8b2c5c51e714735ebee938e7b3`;
the scaler hash is
`82719d9ba27cc48542a6ba6989240217cc50d9005591208e7d7648b211f33c4f`.

## Shoup: the first operand need not be canonical modulo the target

[SOURCE] `lazy_mul_shoup` checks the **second** operand and its precomputed
reciprocal. It accepts an arbitrary u64 first operand. This matters because the
scaler passes extended-base residues directly to much smaller target primes.
An `a < p` premise would miss the actual call site.

[DERIVED, kernel checked] With word base B, canonical `0 ≤ b < p`, and
`0 ≤ a < B`, define

```text
s = floor(B b / p)
q = floor(a s / B)
r = a b − q p
```

The exact identity
`B r = a ((B b) mod p) + p ((a s) mod B)` proves `0 ≤ r < 2p` and
`r mod p = a b mod p`. If `2p < B`, the explicit double-word wrapping operations
and final one-word cast equal this integer residual. Every product fits B², the
subtraction cannot underflow, and its result fits B. The actual modulus
constructor's `2 ≤ p < 2^62` implies the needed bound at `B=2^64`.

[DERIVED, kernel checked] A public toy witness uses B=256, p=31, a=34 and b=11:
the lazy result is 33, so both the wide first operand and noncanonical lazy result
are meaningful. Omitting canonicality of b admits a counterexample at a=8, b=32.
This falsifies a weakened model contract, not the source's stated preconditions.

## Barrett and canonical reduction

[DERIVED, kernel checked] The split high-word formula is proved generically:

```text
lo(a) = a mod B, hi(a) = floor(a/B)
middle = lo(a)hi(c) + hi(a)lo(c) + floor(lo(a)lo(c)/B)
floor(a c / B²) = floor(middle/B) + hi(a)hi(c)
```

For `c=floor(B²/p)`, the reciprocal's `lo(c)+hi(c)<B` bound controls the source's
three-term u128 addition. The generic literal Barrett theorem carries this
premise explicitly; `target_word_bounds` kernel-checks it for all three deployed
target constants. The result is a lazy residue in `[0,2p)`. The mask/xor selector
is separately proved over arbitrary 64-bit vectors, and one selected subtraction
canonicalizes a lazy residue. The unselected wrapping subtraction may wrap; the
selector does not return it.

[DERIVED, kernel checked] At B=256, p=31, a=65535, the lazy Barrett result is 32
and the canonical result is 1. Omitting the strict `x<2p` input premise breaks
one-step reduction at x=62. These witnesses inhabit the actual bounds and expose
their necessity without assuming a plaintext BFV result.

## Accumulation and the closed deployed instance

[DERIVED, kernel checked] `modularAccumulationSound` proves the exact source
equation from lazy representatives, which may differ from their canonical
residues by p:

```text
acc = 2p − lazyGamma + (negative ? 2p − lazyW : lazyW) + Σ lazyTerm[i]
acc mod p = (Σ r[i] omega[i] − v gamma + signedCorrection) mod p
```

Pointwise congruence, projected coefficients and signed correction are proved
compositionally. Their lazy ranges make both 2p-subtractions nonnegative.
For six terms, `0 ≤ acc ≤ 16p < 2^128`; nonnegative partial sums therefore cannot
overflow the source's u128 additions. `sourceWordTarget` models the accumulated
word wrap explicitly and the proof removes it using this bound.

[DERIVED, kernel checked] The deployed theorem also proves the selected v and
correction magnitude fit u128, checks the negative branch's literal `+1` cannot
overflow, and reuses the prior all-canonical U256 correction/index bounds. Gamma
is integral in the pinned BFV downscale, as established in the earlier module.
Every call to Shoup and Barrett is discharged before the final modular identity;
their correctness is no longer an unexplained primitive premise at this model
endpoint.

## Executed evidence

[EXECUTED] `word_probe.rs` links the existing cached `fhe-math` rlib used by the
earlier engine probe. It calls the actual `Modulus` API for seven moduli, including
the three target primes and a large extended prime. It does no HE encryption,
polynomial multiplication or dependency rebuild. `probe-run.json` pins the Rust
version, source, rlib and output. Compilation took about 0.19 seconds and the
1,904-row probe about 0.006 seconds on this run; these are test-run timings, not
cryptographic performance claims.

[EXECUTED] `check_words.py` compares the literal word transcript to every actual
API result: **1,904 rows match**, including 1,805 first operands at least p,
405 noncanonical lazy Shoup results and 320 noncanonical lazy Barrett results.
The maximum observed middle sum uses 128 bits and remains below 2^128. Additional
exhaustive reduced-word checks cover 35,920 Shoup cases and 138,752 Barrett cases,
with the stated premise/range falsifiers retained.

[EXECUTED] `check_source_words.py` compares the complete word path with the
previous integer model on 1,002 seeded/end-point six-residue rows, spanning both
correction signs. It also matches five retained actual Rust coefficient arrays,
including negative and nearest-plus-one boundaries: **3,021 target checks** in
total. These are finite cross-checks of model correspondence, separate from the
universal Lean statement.

## Validation, cost, and reproduction

[EXECUTED] `validation-summary.json` records **38 exact axiom pins** across four
modules, grouped 8+10+8+12. Fifteen dependencies, all four new modules and a
side-effect-free Compiler umbrella compile freshly in isolation. The companion
import-boundary check and all five BFV patch-application checks pass. Individual
standard axiom reports are retained in `axiom-pins.json`; no blanket axiom-free
claim is made. There is no `sorry`, custom `axiom`, `native_decide`, or
`ofReduceBool` in the patch. No full descriptor kernel reduction or full
Minidregg build was attempted. Companion trees were not modified.

Patch: `minidregg-fhe-modular-lowering.patch`, SHA256
`994e75fece5090d9cc29a8408dd18b105f25d05825ae01048cf8216e16bfc464`.
It imports the frozen 22-pin target projection and its preceding BFV/compiler
chain. Exact source and dependency hashes are in `validation-summary.json`.

[DERIVED] This proof adds **zero emitted constraints**. The earlier composed
descriptor remains 161,027 gates per scalar; this is still a conservative
two-descriptor arithmetic count, not a latency claim. The inspected per-target
source path calls seven lazy Shoup multiplications, three lazy Barrett reductions
and two one-step corrections. These call counts do not imply a proof cost or
charge any work to the separate sliding-window Learn operation.

Kernel/import/patch recheck:

```sh
cd /Users/ember/dev/minidregg
lake env python3 /Users/ember/dev/zkml-research/research/learn_infer_only/formal/bfv_lift_refinement/modular_lowering/validate.py
```

Lightweight replay from the research root uses the retained actual API fixture:

```sh
python3 research/learn_infer_only/experiments/bfv_lift_refinement/modular_lowering/check_words.py
python3 research/learn_infer_only/experiments/bfv_lift_refinement/modular_lowering/check_source_words.py
```

`run_probe.py` can regenerate actual primitive outputs when the earlier engine
probe's cached rlib exists; it records its hash rather than rebuilding the HE
workspace. `source-map.json` and `manifest.json` pin correspondence and retained
artifacts. This tranche used zero metered searches and zero PDF downloads.

## What remains

- [OPEN] Formal correspondence from Rust source, integer casts, arrays/unsafe
  accesses and compiled code to these handwritten word equations. The actual
  cached-library comparisons provide executed evidence, not a Rust semantics
  theorem or a side-channel guarantee.
- [OPEN] Rust BigUint constructor/projection and table-generation refinement.
  The already pinned constants and arithmetic constructor formulas are used;
  another implementation or parameter family must discharge its own bounds.
- [OPEN] Committed input residue provenance, extension, integer convolution/NTT,
  a complete multiplication controller, and authenticated proof-protocol pins.
- [OPEN] Universal completeness of the finite emitted layouts and a kernel proof
  of complete emitted witness acceptance remain separate from this soundness
  result. No secrecy, master-read absence, private release, relinearization,
  noise, or deployable-system claim follows from this scalar arithmetic patch.
