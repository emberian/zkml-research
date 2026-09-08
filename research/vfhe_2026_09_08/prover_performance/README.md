# Reuse outer MLE weights in the existing contraction prover

[EXECUTED] The patch accelerates the actual minidregg `prove_matmul` path by computing each outer equality-weight vector once, then streaming matrix rows through those weights. On the existing BabyBear `[2,1024] × [1024,128]` workload, complete algebraic proving fell from **7.82 ms to 1.97 ms (3.97×)**. The complete claim, four evaluations per round and challenge vector are unchanged. This measurement excludes commitments and applies to the existing contraction engine, not the separate BFV DescriptorIR-v2 STARK path.

| Phase | Original median | Patched median | Ratio |
|---|---:|---:|---:|
| Bind both outer points / construct cubic tables | 7.728 ms | 1.726 ms | 4.48× |
| `prove_matmul`, including binding and all rounds | 7.817 ms | 1.970 ms | 3.97× |
| Claimed-output MLE evaluation | 12.19 µs | 2.96 µs | 4.12× |
| Compute output matrix, unchanged implementation | 3.421 ms | 3.343 ms | 1.02× noise/control |

[EXECUTED method] One workload and field, deterministic public synthetic operands/challenges, Apple M2 Max, `rustc 1.98.0-nightly (91fe22da8 2026-06-21)`, optimization level3. Nine paired samples per phase, eight calls per sample, alternating original/patched order after a warmup; all raw observations are in `workload.jsonl`. This is a local, shared-machine measurement. The unchanged output computation is a control, not an optimization claim. The earlier run is retained in `workload.initial.jsonl`; the final run restored exact source snapshots after rustfmt recursively changed only their whitespace. `validation.json` records this harness correction.

## What changed and why it is equivalent

[SOURCE] Baseline `/Users/ember/dev/minidregg/prover/src/sumcheck.rs` at commit `6937394e1dc2c2aaff986c7d4b3a258aca5d16fd`: `MatmulClaim::row_partial:606`, `col_partial:619`, `mle2_eval:649`, `prove_matmul:667`. The current companion file matches that base. `docs/VERDICTS.md` §5a identifies repeated partial evaluation as the dominant algebraic cost; `notes/shared-arithmetic.md` distinguishes reusable arithmetic from work that must wait for a challenge. This optimization is performed after the existing caller supplies the challenge.

[DERIVED] Previously each matrix entry recomputed `chi_eval(index, point)`, a product over the outer point's coordinates. A new private `chi_weights` computes the full basis using the tensor recurrence. When adding a coordinate x as the new high index bit, a prior weight w gives low weight `w−wx` and high weight `wx`. This equals `(1−x)w` and `xw`; it preserves the existing LSB-first convention and needs one multiplication per pair. The row partial walks each stored row contiguously and reuses its weight across the inner index. The column partial reuses one basis across all rows. `mle2_eval` uses the same bases and factors the row weight outside the row sum by distributivity.

[DERIVED counts] At the measured shape, equality-basis multiplications fall from 919,552 to 128. The 133,120 matrix-value products remain. Total outer-binding multiplication calls therefore fall from 1,052,672 to 133,248 (7.90×); the measured time reduction is 4.48×. The basis scratch is at most128 u64 values for either partial, and 130 values when both bases coexist in `mle2_eval`. No new matrix-sized witness buffer is allocated.

[SOURCE / preserved behavior] Public APIs, code relation, modulus, point ordering, canonical transcript requirements, four-node cubic wire, `h(1)` transmission, verifier round checks and terminal checks are retained. Shape validation precedes basis allocation, including for a malformed large column dimension. The implementation remains unverified Rust compute matched to Lean-authored conformance vectors, exactly the status described by the existing module; no Rust refinement theorem is claimed.

## Correctness and delivery

[EXECUTED] Debug checks passed 60 existing library tests, eight existing Lean-authored matmul conformance tests, and three focused new tests. Release checks passed the same eight conformance tests and all three new tests; `release-tests.log` retains the command output. New tests compare against literal chi sums across zero-dimensional, asymmetric and rectangular tables, three small/base fields, Boolean corners and noncanonical u64 inputs; they also retain a shape-before-allocation refusal. The saved workload checks exact full-transcript equality, honest acceptance, forged-output refusal in both versions and an `h(1)` mutation refusal.

[EXECUTED] `outer-mle-reuse.patch` changes only:

- `prover/src/sumcheck.rs` — the existing implementation and private basis helper.
- `prover/tests/matmul_binding_reuse.rs` — the focused equivalence/order/shape tests.

[EXECUTED] The patch applies to the named baseline and reproduces the checked isolated files exactly. `git diff --check` passes. Isolate: `/tmp/minidregg-prover-performance-20260908`, branch `research/outer-mle-reuse-20260908`. Original companions and their unrelated dirty work were not edited. No commit or push was made. Patch SHA256: `ec8fde4a1e755a13d86bc69157e1ab6c45003e00df9b2f71bcc4dba9bd048b59`.

Reproduce the one workload from this directory:

```sh
rustc --edition=2021 -C opt-level=3 bench.rs -o /tmp/minidregg-prover-performance-bench
/tmp/minidregg-prover-performance-bench
```

After applying the patch in an isolated minidregg checkout:

```sh
cargo test --release --manifest-path prover/Cargo.toml --test matmul_binding_reuse --test zkml_matmul_conformance
```

[OPEN application] The vFHE execution lane currently targets `3·ctA+5·ctB` through a DescriptorIR-v2 STARK, which does not call this engine. The separate ring/vector lane's proposed shared-point contractions of Y and Q have the same reusable-basis shape, but that connection has not been implemented here. No FRI query count, soundness knob, commitment policy or security label changed; the fourfold figure is not a complete vFHE/system speedup.
