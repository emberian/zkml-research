# Wave 11 Lane 2 — trace packing in Tower256

[DERIVED] The Fan–Paar coordinate layout packs 32 bytes bijectively into one field element. Reading its absolute trace requires a parity mask of weight 68. Coordinate 255 alone gives the wrong answer on two explicit inputs.

## Proof audit

[SOURCE] In *Sumcheck bit packing*, Frigo and shelat use the trace-dual basis to turn an evaluation on individual bits into field-linear relations on packed words. Theorem 3.4 samples an independent field challenge per bit claim. Equation (6) factors tensor coefficients. Figure 2 blinds the traces and opens two linear relations using one additional pair \((r,r^2)\). Theorem 4.3 assumes a hiding commitment with a zero-knowledge linear-relation check. I read the construction and soundness argument in §§3–4, including equations (5)–(9). [Local paper text](/Users/ember/paperbin/2026-frigo-shelat-sumcheck-bit-packing-2026-2770.txt:230)

| Claim | Kernel evidence |
|---|---|
| [REFUTED: absolute trace equals coordinate 255 in this basis] | The mask in big-endian numeric hex is `26c6636dc63a6da5c63a6da56da5a55700000000000000000000000000000000`. The basis vector at 255 has trace 0 and the vector at 128 has trace 1. The JSON serializes the mask in little-endian byte order. [Trace refinement and tooth](/Users/ember/dev/minidregg/Theory/Tower256TraceBitPacking.lean:222) |
| [SOURCE] Duality and bijection | `dual_basis_biorthogonal` proves the full Kronecker pairing at every tower level. `pluckBit_packBits_id` and `packBits_pluckBit_id` prove both inverse laws. [Dual basis](/Users/ember/dev/minidregg/Theory/Tower256TraceBitPacking.lean:280) · [First inverse](/Users/ember/dev/minidregg/Theory/Tower256TraceBitPacking.lean:363) · [Second inverse](/Users/ember/dev/minidregg/Theory/Tower256TraceBitPacking.lean:398) |
| [SOURCE] Constructive additive Hilbert 90 | `solveArtinSchreier_spec` verifies the witness computed from a trace-zero input. The equivalence theorem and `tooth_trace_one_no_artin_schreier_root` cover both trace classes. [Solver](/Users/ember/dev/minidregg/Theory/Tower256TraceBitPacking.lean:536) · [Equivalence and refusal](/Users/ember/dev/minidregg/Theory/Tower256TraceBitPacking.lean:566) |
| [SOURCE] Frobenius and masks | `frobenius_weighted_sum_sq` proves \(\sum_j\delta_j^2t_j^2=(\sum_j\delta_jt_j)^2\). The module proves the honest linear identity, injectivity of the implicit first pad, and the reduction with a potentially dishonest committed square. [Folding](/Users/ember/dev/minidregg/Theory/Tower256TraceBitPacking.lean:618) · [Implicit pad](/Users/ember/dev/minidregg/Theory/Tower256TraceBitPacking.lean:660) · [Reduction](/Users/ember/dev/minidregg/Theory/Tower256TraceBitPacking.lean:710) |
| [DERIVED] Theorem 3.4 batching | For a fixed nonzero error vector and any fixed affine target, the accepting fraction of independent uniform field weights is exactly \(2^{-256}\). Squaring each independent weight preserves that count. For a *single* challenge used in powers, the separate polynomial theorem gives at most \((N-1)/2^{256}\). The Rust transcript uses independent XOF outputs and squares them. [Counting theorems](/Users/ember/dev/minidregg/Theory/Tower256TraceBitPacking.lean:728) · [Power bound](/Users/ember/dev/minidregg/Theory/Tower256TraceBitPacking.lean:797) |

[EXECUTED] Running `research/wave11_frontier_upgrades_2026_11_22/formal_trace_pack/build_and_verify.sh --lean-only` freshly elaborated the 938-line minidregg module with warnings as errors. The tier boundary passed, the harness found zero proof placeholders, custom axioms and native decisions, and Lean checked 21 pinned axiom reports. The reports list standard Lean foundations where used. Lean regenerated the 20,261-byte vector with SHA-256 `4386aa58daf451ae4fb59e16cdb854dfb434fb7b78658654017b9d81dcf479fd`. [Harness](../research/wave11_frontier_upgrades_2026_11_22/formal_trace_pack/build_and_verify.sh) · [Lean vector](/Users/ember/dev/minidregg/prover/testdata/tower256_trace_pack_conformance.json)

[EXECUTED] On hbox, the isolated obend build completed 17 jobs. All three stored proofs rejected their mutations, including replacing the parity trace by the top-bit read and adding a trace-one value to the Artin–Schreier map. The added `linear_batching_unique_challenge` identifies the unique accepting coordinate after all other challenges are fixed. This supplies the field-count argument directly alongside obend's power-batching bound. A remote axiom audit of all 48 direct namespace declarations found zero dependencies on `Classical.choice` after replacing the implicit finite-order equality instance and an arithmetic proof by decidable natural-number equality and explicit cancellation. Local and remote target SHA-256 was `d8eb330ca7b051b4886c97c6a2303cf7ddf315c5fcef632ce9700d0d03280698`. [Obend theorem](/Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/obend-wt/w11-tower256-trace-pack/lean/Obend/Crypto/Tower256TracePack.lean:570)

## Rust prover and verifier

[SOURCE] Both public verification paths take the expected content root, byte length, automaton and claimed acceptance. The transition-table path compiles the public table into shared Boolean multiplexers, packs the internal state and gate bits, and folds every transition constraint into a sumcheck. The tensor specialization proves parity of the AND of two public byte-parity predicates. Both reduce their blinded terminal evaluations to the Figure 2 check. Each input byte of a tensor coefficient updates one XOR bucket. Reducing those buckets takes a fixed 255 pair reductions per byte position, giving \(O(32M+32\cdot256)\) for the 256-column transpose. The field operations to construct and batch the 256-by-256 tensor matrix are additional. [Transpose](/Users/ember/dev/minidregg/prover/src/tower256_trace_pack.rs:72) · [Sumcheck](/Users/ember/dev/minidregg/prover/src/tower256_trace_pack.rs:485) · [Table prover](/Users/ember/dev/minidregg/prover/src/tower256_trace_pack.rs:1299)

[SOURCE] The proof commits to 255 explicit trace-pad seeds, the mask \(r\), and its claimed square before the batching challenges. It transmits the 256 masked traces and the blinded sum \(A\). The verifier checks every trace, derives independent \(\delta_j\), and merges equations (8) and (9) with a fresh challenge after \(A\). The terminal opening uses disjoint-coset additive Reed–Solomon shares, a masked dot-product polynomial, and a BaseFold chain with a final constant. The wire verifier authenticates batched Merkle openings. Both configurations use rate 1/4, 148 query draws with replacement, and zero grinding. [Linear checks](/Users/ember/dev/minidregg/prover/src/tower256_trace_pack.rs:661) · [Coset verifier](/Users/ember/dev/minidregg/prover/src/tower256_trace_pack.rs:829)

[DERIVED] The algebraic trace-pad uniformity result assumes uniformly random field inputs. Rust expands secret seeds with domain-separated cSHAKE streams. The hiding argument for one transcript uses fresh commitment and proof randomness. Reopening the same sharing exposes further linear observations. The full Fiat–Shamir/BaseFold composition and multi-proof privacy remain [OPEN]. The kernel count above concerns the packing reduction. The UD-100 label records the FRI parameter schedule.

## Release benchmarks

[EXECUTED] The six rows below use one release run on an Apple M2 Max. Each pair uses identical deterministic bytes and the same two-state DFA, which toggles when bits 0 and 7 of a byte are both set. The general packed path receives its complete transition table. The specialized path receives the two bit masks. Prover time includes commitment and receipt encoding. Verifier time starts from wire bytes and caller-supplied public inputs. The baseline wire includes a 1,042-byte magic and public DFA header. The packed table verifier receives the public DFA separately. [Benchmark code](/Users/ember/dev/minidregg/prover/tests/tower256_trace_packing.rs:36)

| Payload | Prover | Content symbols | Prove (ms) | Verify (ms) | Receipt (bytes) |
|---:|---|---:|---:|---:|---:|
| 16 KiB | Unpacked table | 131,072 | 4,788.756 | 79.314 | 905,408 |
| 16 KiB | Packed table | 4,096 | 621.937 | 225.380 | 278,272 |
| 16 KiB | Packed AND specialization | 4,096 | 128.460 | 42.317 | 261,856 |
| 64 KiB | Unpacked table | 524,288 | 19,352.941 | 96.879 | 1,160,676 |
| 64 KiB | Packed table | 16,384 | 2,511.965 | 912.759 | 546,560 |
| 64 KiB | Packed AND specialization | 16,384 | 460.272 | 118.728 | 515,968 |

[DERIVED] These sizes give exactly **32×** fewer content codeword symbols than the byte layout and **256×** fewer than a one-field-symbol-per-bit layout at the same rate and random-half overhead. The bit-layout counts are 1,048,576 and 4,194,304 respectively. The timed baseline is the byte layout. Auxiliary rows, opening messages and Merkle paths are accounted for in the measured receipt sizes.

## Falsifiers and reproduction

[EXECUTED] Rust matched every entry of the 256-by-256 dual pairing, the trace mask, the Lean-emitted Artin–Schreier witnesses and refusals, and the tensor vector. The full-width distribution check established rank 255, verified all 8,192 byte contributions of the square-plus-identity map, and found that its image is the trace kernel. Each image point has two preimages, giving exact TVD 0 on that kernel. [Conformance and distribution tests](/Users/ember/dev/minidregg/prover/tests/tower256_trace_packing.rs:88)

[EXECUTED] Flipping one DFA-irrelevant bit of the 524,288-bit document preserved the DFA result and changed the externally pinned root. Its original receipt failed verification. A trace-one masked message failed the trace check. A prover that committed to \(b=r^2+1\) and recomputed the complete transcript failed the systematic sum check. A prover that committed an incorrect intermediate DFA state and recomputed its receipt failed the Boolean sum check. The suite also covered non-power-of-two lengths, wrong claims, changed automata, damaged authentication data and truncation. [64 KiB test](/Users/ember/dev/minidregg/prover/tests/tower256_trace_packing.rs:196) · [Dishonest prover tests](/Users/ember/dev/minidregg/prover/src/tower256_trace_pack.rs:1025)

[EXECUTED] The retained command and output excerpts below distinguish the minidregg overlay and release suite from the obend build.

```sh
research/wave11_frontier_upgrades_2026_11_22/formal_trace_pack/build_and_verify.sh
# CARGO_TARGET_DIR=/tmp/target-w11-t256, cargo test --locked --release
# 938 lines < 950; 0 sorry, 0 axiom, 0 native_decide; 21 #print axioms pins
# OK: scripts/check-import-boundary.sh passed
# test result: ok. 2 passed; 0 failed
# test result: ok. 6 passed; 0 failed

# On hbox, in /tmp/obend-w11-t256/lean, inside the 12G swarm-build scope
SWARM_MEM_MAX=12G timeout --kill-after=10s 600s lake build Obend.Crypto.Tower256TracePack
# Build completed successfully (17 jobs).
```

[EXECUTED] Local `/Users/ember/dev/obebuilder/target/release/obb lint` in the isolated worktree reported two errors and 135 warnings, with zero findings on the lane file. Strict lint failed on two stale hardware README symbol references at lines 7 and 10. The emitter maps those labels to `retimedMac2StageRtl` and `widthProbeTwoClockRtl`. Cone, apex and harness checks completed successfully. A separate strict pipeline check reported `UNDECLARED` with zero obligation classes. The requested green-lint gate leaves the obend change uncommitted on `w11-tower256-trace-pack` at base `bd2a274d`. [Hardware references](/Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/obend-wt/w11-tower256-trace-pack/hardware/README.md:7) · [Emitter mapping](/Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/obend-wt/w11-tower256-trace-pack/lean/tools/emitsv/EmitSv.lean:118)

[EXECUTED] Kagi: 0, Scry: 0, eprint downloads: 0.
