# Exact basis extension for the complete saved nonlinear square

[EXECUTED] The compiler-generated identity-scaling extension relation was proved over **all 16,384 input-component/coefficient positions** of the actual N8192 ciphertext square. Four 4096-row proofs cover **147,456 output residues: 65,536 copies and 81,920 newly computed residues**. There is no sampled-position claim or padding. The runtime then freshly verified the full 28-proof square join: 4 extension, 18 tensor-product and 6 reused rescale proofs. Runtime evidence is `../full_bfv_multiply_successor/results/extension001/result.json` and `results/whole_verify001/result.json`.

[DERIVED] The reusable source theorem is `ExactBasisExtension.matrixSound` in `Compiler/ExactBasisExtension.lean`. It quantifies over both modulus counts, fixed source coefficients, positive modulus/denominator premises, and every natural scalar assignment satisfying the generated signed matrix. The actual public theorem `ActualBasisExtension.publicRowSound` in `Compiler/BasisExtensionPublic.lean` forces canonical inputs, all four copied residues, and all five exact native-projection outputs for every accepted BabyBear assignment.

## Deployed arithmetic and representation boundary

[SOURCE] `fhe-dregg/src/bfv/ops/mul.rs:178` extends each input using `ScalingFactor::one()`. The actual square has two distinct input components, reused on both multiplication sides. `fhe-math-0.1.1/src/rq/scaler.rs:26` detects the four common moduli; `:64` copies those rows in the input representation. For the five new moduli it performs a backward NTT if necessary, calls `RnsScaler.scale` with starting_index4, then performs forward NTT only on the new rows. Exact absolute paths and hashes are in source_pins.json.

[SOURCE] In `rns/scaler.rs:247`, the identity branch computes the Garner accumulator and rounded word quotient; the `is_one` branch skips the theta-omega/theta-gamma correction. The source therefore forces, for canonical PowerBasis input residues r,

```
T = Σ_i r_i · thetaGarner_i
v = floor((2T + 2^127) / 2^128)
new_j = (Σ_i r_i · Garner_i − Qbase · v) mod newPrime_j
copy_i = r_i
```

[DERIVED] This retains the captured 127-bit fixed-point Garner coefficients. The theorem does not replace v with a quotient computed from an ideal centered CRT representative. Input complements force canonical r; a quotient/remainder equation and complement force v and its remainder; each target has a shifted signed quotient, remainder and canonical complement. Four explicit source rows force the common-residue copies. The shift of target quotients is 2^194; it changes witness representation, not the forced output formula.

[EXECUTED] `generate_constants.py` reads the actual public native constructor Debug capture, reconstructs Garner coefficients using the same integer construction, and checks every projected gamma/omega, combined theta word and the 127 shift. It authors constants only. Capture SHA256: `eae1fb16c2c90b455ee155550ff74fe332a92da18cdfb36baa399a5c605ff0c4`. Its output is `results/constants.json` and the generated `Compiler/ActualBasisExtension.lean` data module.

## Compiler obligations discharged

[DERIVED] `ProfiledMatrix.coefficient_le_mass`, `auto_constants` and `auto_coefficients` are reusable proofs that the automatic unsigned-mass result width contains every constant and shifted coefficient. The instance no longer assumes or individually enumerates these capacities. `ActualBasisExtension.capacity` also discharges every carry-range and local BabyBear sum budget, using the concrete per-row profile. `sourceSound` composes these field gadgets with the exact extension matrix theorem.

[DERIVED] `ActualBasisExtension.garner_range` supplies nonnegative T<2^191 from canonical actual inputs and theta bounds. The reused `FheRnsScale.wordV127_correct` then connects the exact source quotient to the U256-word mathematical model. `projectionAgreement` proves the full Garner/gamma lifts have precisely the captured native modular projections, and `nativeAgreement` connects each target formula. Structural input/copy/new-output wire theorems connect all public digits, including zero high digits, to the decoded scalar groups.

[DERIVED] `ExactBasisExtension.inhabited` supplies a cheap nonzero valid matrix instance. `wrongOutputRefused` excludes a changed output for every auxiliary assignment at that instance. The inherited field compiler also has its frozen inhabited assignment and capacity-truncation falsifier. The actual large accepting witnesses were supplied to the real prover, not normalized as closed kernel examples.

[OPEN] Accepted-assignment soundness is universal. Generic field-witness completeness for every possible parameter set/canonical input, and the full automatic digit-window carry-allocation completeness argument, are not claimed. All field capacities needed by soundness are proved; all actual full-operation witnesses passed the emitted relation. Arbitrary parameter choices can restrict the accepting set, including through insufficient signed-quotient offsets.

## Actual emitted and consumed component

| Item | Value |
|---|---:|
| Scalar groups / radix digits / matrix rows | 30 /22 /20 |
| Public arity | 84 |
| Input / copied / new-output start columns | 1 /25 /49 |
| Witness columns | 22,977 |
| Arithmetic constraints, excluding lookup | 29,933 |
| ExactPublicRows lookup | table 11, one per row |
| Native witness instructions / registers | 99,592 /99,593 |
| Plan and descriptor emission seconds | 29.305 |
| Actual full extension positions | 16,384 |
| Extension proof bytes | 21,658,145 |
| Extension native emission seconds, four chunks | 26.178 |
| Extension prove seconds, four chunks | 61.818 |
| Extension peak process RSS bytes | 8,225,964,032 |

[EXECUTED] Counts come from `program/emission.json`; timing/proof measurements are the single full runtime observation in `../full_bfv_multiply_successor/`. The complete square bundle contains 69,269,567 proof bytes and its 28 fresh verifications passed. No rescale proof was regenerated. That joined result retains the stated public parser and NTT trust boundary.

[EXECUTED] `EmitBasisExtension.lean` obtains every arithmetic gate by `Signature.fold` over the existing simplified compiler source. `BasisExtensionWitnessPlan` derives scalars by solving the actual source rows through the frozen generic single-variable and quotient/remainder eliminators, then emits the existing sparse carry/digit computation. The unchanged generic BigInt executor consumes this plan; there is no basis-extension equation, carry routine or AIR authored in Rust.

[EXECUTED] Frozen callable artifacts in READY.json:

- `program/template_ir2.json`: SHA256 `5bd98484deb16e5f1af364e479a4e17d139ba5b379f539e32df96f7b031b65a2`.
- `program/witness_plan.json`: SHA256 `ea44b48aeb7b69a51f3d2379459c1ca4b28ef774274f483e6fabd4c6f7f6d178`.
- Reused `rescale_native_emitter/native/target/release/lean-bigint-witness`: SHA256 `f73ba9e4c6e6504ff5ed3ccfcc6b9bef2036037d445b0cc68e4d242da7cd74ff`.

[EXECUTED] Seven Compiler modules contain 23 theorem declarations with 23 exact axiom pins. All final per-module checks and the exporter check exited 0; commands/source hashes are in `results/checked_modules.json`. The proposal adds those modules and the standalone exporter after the frozen predecessors. Dependency oleans were reused in an isolated owned overlay. The existing import-boundary script passed; no Theory, Selvage, companion source or shared target was edited. Failed elaboration attempts are retained. No broad build, sampled proof grid or full-tensor Lean sourceCheck was used.

## Remaining trust boundary and continuation

[OPEN] The theorem is about the Lean signed source, field gadgets, public aliases and exact word/projection model. It does not newly refine Rust execution, native Shoup/modulus operators, constructor code, serde/ciphertext extraction, NTT transforms, proof-protocol/PCS implementation, or the fixed phase/index join controller. These remain explicit in the complete square consumer. The fast native witness plan and interpreter are untrusted producers; the actual generated relation checks their outputs.

[OPEN] A complete saved square is narrower than `Infer(committed_model,query)`: the preceding encrypted plaintext products, Galois rotations and evaluation-key switching/reduction still require their own arithmetic joins. The actual level0 multi-prime switching branch is being inspected; no nonexistent modulus-down step or single-prime bit decomposition is assumed. Root owns shared integration/ledgers. No new web searches were used.
