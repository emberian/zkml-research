# Fused ring evaluation and ring-switch witness generation

[EXECUTED result] **One real proof through the modified matvec prover passed with PCS enabled and the original verifier unchanged.** The prover's public spectral cache was invoked once, produced both ciphertext outputs and quotient witnesses, and all four decrypted results matched. This is now an actual prover-path change, beyond the earlier Python arithmetic prototype.

[EXECUTED deliverables] Apply [implementation/fused-matvec.patch](implementation/fused-matvec.patch) to `tremblaythibaultl/matvecmul` commit `00379074cad457367a86dde2ecee9d0f318a7e12`. Patch SHA-256: `3ac1aa4ca8e414d5a4703b31b6601113995919f14e925049886d248ba2579443`. [implementation/source_pins.json](implementation/source_pins.json) pins the five changed/new files, lockfile and unchanged verifier. The isolated source and build cache remain under `implementation/` and are ignored by Git; the checked patch is the portable source artifact. No companion source was edited.

## Why this delta

[SOURCE] The focused search returned ring switching, ring CCS, lattice folding and aligned arithmetic directions already largely represented in the notes. The useful implementation seam was in the primary [matvec author repository](https://github.com/tremblaythibaultl/matvecmul): `src/protocol/prover/mod.rs:96–107` computes full polynomial products and divides them into quotients and remainders, while lines 153–155 independently recompute the ring products. Its NTT backend transforms each operand pair separately. The source even marks the redundant remainder computation as a possible improvement. This is an actionable implementation delta, not a claim of a new CRT theorem or cryptographic construction.

[SOURCE] *Practical SNARGs for Matrix Multiplications over Encrypted Data*, [eprint 2026/027](https://eprint.iacr.org/2026/027), §3.2 and Algorithm 3, reduces ring products to ordinary polynomial identities with committed quotient witnesses before a random evaluation challenge. The paper was read from the absolute local mirror. This construction supplies the real consumer for the fusion.

[SOURCE/DERIVED] *Verifiable Bootstrapping from Lattice-based Folding*, [2026/1127](https://eprint.iacr.org/2026/1127), §4, explicitly explains why putting coefficient products in NTT slots still requires a coefficient/NTT consistency relation and constant checks. It supports the decision to bind a real arithmetic relation, rather than reclaim the old shared-twiddle savings. The new search also reached [Cyclo's author publication page](https://research.aalto.fi/en/publications/cyclo-lightweight-lattice-based-folding-viapartial-range-checks/) and [repository](https://github.com/osdnk/cyclo). Its additive norm-refresh direction is already in VERDICTS; its repository describes ring-arithmetic benchmarks, not an immediately usable replacement for this prover. No broad negative finding about lattice folding follows.

## Implemented relation and reuse

[DERIVED] For degree-`<N` public matrix entries `A_ij` and input ciphertext components `C_jk`, form the ordinary polynomial

`S_ik = Σ_j A_ij C_jk = Y_ik + (X^N+1)Q_ik`.

Write `S=L+X^N H`; then `Y=L−H`, `Q=H`. Thus the same full product supplies the FHE output and proof witness. [RELATION.md](RELATION.md) gives the exact degrees, zero case, challenge-order condition and the optional complementary-domain identity `Q=(D−Y)/2`, where `D=S mod(X^N−1)`.

[EXECUTED native implementation] `FusedMatvec` caches the public matrix's zero-padded length-`2N` spectra. Each input ciphertext component is transformed once and reused for every output row. It accumulates all Hadamard products before normalizing and inverse-transforming once per output component, then splits into `Y,Q`. It uses the actual locked `tfhe-ntt` 0.6.1 `Plan::{fwd,mul_accumulate,normalize,inv}` backend. Its transform order is the library's bit-reversed negacyclic frequency order; it does not reuse the Python prototype's natural-order tables.

[EXECUTED caller integration] `Prover::preprocess` now returns the cache in its second tuple slot, and `Prover::prove` calls `cache.evaluate(x)` where full-product/division work occurred. The separate ring matvec was removed. Proof structure, commitment timing, sumcheck, PCS and verifier sources are unchanged. Existing callers that infer the preprocessing tuple continue to pass the second slot through; its public Rust type changes from `Matrix<PolynomialRing<…>>` to `FusedMatvec<…>`.

[DERIVED costs at executed shape] The native run has `r=4,m=2,k=2,N=1024`. It uses eight public preprocessing transforms and twelve online transforms, all length `2048` (four input transforms and eight output inverses). The old per-product pattern uses 48 transforms at length `2048` and 48 at length `1024`. Spectral products fall from `3Nrmk=49,152` to `2Nrmk=32,768`. The executed cache reports 16,384 stored `u64` field elements, or 131,072 bytes of spectral payload, excluding plans/vector overhead. These counts follow from the executed dimensions and source, not a native speed comparison.

## Actual proof execution

[EXECUTED] [implementation/native_command.json](implementation/native_command.json) records the single normal run: September 8, 2026, 16:07:24 UTC, PID 69140, exit zero, with a 300-second cap. Source hashes were unchanged before/after. The binary was `target/release/examples/fused_proof`, SHA-256 `7404eec4cbd7b593ea3611654d1de828cdd1d77c459587fcc319112502c28b47`.

[EXECUTED] Configuration: ring degree `1024`; integer matrix `4×2048`, encoded as a `4×2` ring matrix; two input ciphertexts, each with mask and body; Goldilocks coefficient field, quadratic extension proof field; plaintext modulus `16`; deterministic public matrix/vector with expected outputs `[14,12,10,8]`; fresh key/encryption randomness retained only in process memory. This is a small synthetic configuration, with no new FHE security estimate. The unchanged WHIR wrapper selects 100-bit `ConjectureList` parameters; successful execution is not a new security proof.

[EXECUTED] Exact [result.json](implementation/normal_001/result.json):

| Phase/result | Observed value |
|---|---:|
| Public preprocessing, including spectral cache | 0.980208 ms |
| Prover, with all three PCS openings enabled | 35.239958 ms |
| Unchanged verifier, including its preprocessing | 3.155166 ms |
| Decrypt and compare, after verifier acceptance | 0.130167 ms |
| Fused prover calls | 1 |
| Matching plaintext outputs | 4 |
| Input ciphertext bytes | 32,768 |
| Output ciphertext bytes | 65,536 |
| Three PCS opening byte strings | 152,812 bytes |
| Sumcheck size reported by existing API | 1,840 bytes |

[EXECUTED validation] Before that crypto run, the new Rust arithmetic test compared every output/quotient coefficient with the old full-product/division and independent ring-multiplication paths on nonconstant public vectors. It passed. The release example built with the locked dependency graph and ran once. An initial offline build stopped because `cc v1.2.40` was missing; a directory-owned dependency cache supplied the locked crates, after which the public test and example build passed. No cryptographic retry or baseline crypto run occurred.

[EXECUTED evidence scope] [public_artifacts.json](implementation/public_artifacts.json) pins the saved public ciphertexts, quotient commitments, three PCS opening byte strings and aggregate result. The actual verifier ran against the complete in-memory proof. The upstream API has no complete wire serializer for the private fields of `SumCheckProof`; these saved pieces are therefore **not a standalone replayable proof bundle**. Private keys and plaintext decryption traces were not archived. A complete public proof serializer is needed for browser/offline replay of a future run.

[OPEN performance] No matched native baseline was run in this cycle, so the 35.24 ms figure is not an established speedup. The next experiment should use one materially larger matched unfused/fused workload and include the shared `Y/Q` contraction being prepared by polynomial_gluing. No benchmark grid is needed.

## Public prototype and source coverage

[EXECUTED] [fused_ring_matvec.py](fused_ring_matvec.py) separately implements both a fused length-`2N` cyclic transform and complementary length-N cyclic/negacyclic transforms. [run_public.py](run_public.py) passed 85 monomial-pair controls, four nonconstant matrix shapes against coefficient schoolbook multiplication, eight direct transform/evaluation checks, and equality across all three algorithms through `N=4096`. Positive fixtures and exact operation counts are in [positive_fixtures.json](positive_fixtures.json) and [results.json](results.json). Python timings have short, fixed-order samples and visible local scheduling variability; they are not Rust, FHE or whole-proof measurements.

[DERIVED retained limits] The tighter residual degree `2N−2` requires an enforced top-zero quotient coefficient in a verifier game; honest generator correctness alone does not establish that restriction against malicious commitments. An unrestricted length-N quotient permits degree `2N−1`, covered by the paper's conservative `2N/|E|`. The native patch preserves the existing verifier and makes no stronger soundness claim. Complementary-coset CRT needs invertible `2`; no characteristic-two or M31 scalar-slot isomorphism is assumed. Cross-limb provenance, decryption correctness bounds and ROM/QROM security remain their existing separate questions.

[EXECUTED search coverage] [SOURCES.json](SOURCES.json) records all queries and local primary-source hashes: nine web search queries (the ninth followed Scry's exact Cyclo title), three page-open attempts including one incorrect repository URL error, two successful Scry SQL queries, one schema-call attempt whose response was not retained, zero Kagi queries and zero eprint PDF network requests. Scry returned 20 and 38 rows and explicitly reports snapshot freshness lag; it is not a complete current eprint index. No field-wide absence or novelty claim is made. The preceding notes were read to avoid repeating the ring-switching, circle-alignment and BAT refutations.
