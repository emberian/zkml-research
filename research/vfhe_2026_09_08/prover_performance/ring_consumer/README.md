# Shared contraction in the actual ring prover

[EXECUTED] The successor patch connects the fused ring quotient/remainder witness to the existing `matvec` prover. On one public workload with ring degree 1024, four output rows, two inner ring entries and two RLWE components, computing the two sumcheck claims fell from **550,444 ns to 63,639 ns** (median, **8.65×**, 486,805 ns saved). The modified production prover completed with all three PCS openings enabled; the unchanged verifier accepted, and all 8,192 output coefficients matched the fused output. These are claim-computation timings, not an end-to-end speedup or a security claim.

[SOURCE] Base implementation: `tremblaythibaultl/matvecmul` commit `00379074cad457367a86dde2ecee9d0f318a7e12`, followed by the other lane's [fused-matvec.patch](../../new_constructions/implementation/fused-matvec.patch), SHA256 `3ac1aa4ca8e414d5a4703b31b6601113995919f14e925049886d248ba2579443`. The base `src/protocol/prover/mod.rs` SHA256 is `6f93d51085e43916e8d312d0b4355d6f83e0d041a4b9b80476c7f74b932cccdb`. The full source remains in that lane's isolated `new_constructions/implementation/matvecmul/`; original companion trees were not edited. This consumer uses the implementation's Goldilocks field and its quadratic extension with nonresidue 7.

[DERIVED] For each output row `i` and component `k`, the existing fused constructor returns

```
S_ik(X) = sum_j A_ij(X) C_jk(X) = Y_ik(X) + (X^D + 1) Q_ik(X).
```

Use the caller's exact equality weights `w_i = eq(tau, i)`, component weights `beta_k`, and cached powers `alpha^t`. The helper computes

```
y_eval = sum_i w_i sum_k beta_k sum_t alpha^t Y_ikt
q_eval = sum_i w_i sum_k beta_k sum_t alpha^t Q_ikt.
z1_claim = y_eval + (alpha^D + 1) q_eval
z3_claim = q_eval.
```

[DERIVED] These are the original total claims by polynomial evaluation and distributivity. The helper reads coefficients in row/component/coefficient order, evaluates each component before multiplying by its component weight, and evaluates each row before multiplying by its row weight. It shares the caller's power table across `Y` and `Q`. The quotient's low `D` coefficients are exactly the projection used by the existing committed quotient MLEs. This reasoning relies on the existing fused quotient/remainder identity; the helper itself is an evaluator, not a new check of that identity.

[SOURCE] The production changes are [the helper](src/protocol/ring_contraction.rs) and [the caller](src/protocol/prover/mod.rs). The caller contracts after the original absorption of `Y` and quotient commitments and the original challenge squeeze, at lines 183–189. It replaces only the two `sum_over_boolean_hypercube` calls, at lines 204 and 219. All original sumcheck tables and round computations remain in use, as do the matrix and two quotient PCS openings. The verifier, transcript, sumcheck, PCS, fused constructor, Cargo dependencies and lockfile are byte-identical to the fused baseline; this was checked during patch replay. The patch adds a four-element row-weight buffer on this workload and does not remove the expanded tables needed by the current sumcheck engine.

[EXECUTED] [ring-contraction.patch](ring-contraction.patch), SHA256 `419193cdc4c273fa0763d8ececd4374179041e3ba6a0df0b4ae49896a2c28af1`, applies after the fused patch. It changes two existing modules and adds the helper plus a test module. An independent temporary tree applied and reversed the patch successfully; all resulting changed files matched the checked isolate bytes. Exact checked-file hashes and machine-readable samples are in [RESULTS.json](RESULTS.json).

[EXECUTED] The focused release tests compared the new claims with the existing full-table scans at alpha 0, 1, −1 and a non-base-field challenge. They compared resulting transcript challenges, verifier results and terminal MLE products. Asymmetric rows/components make ordering controls meaningful; swapped row/component weights and a changed quotient coefficient change the computed claims, and the original sumcheck refuses the corrupted quotient claim at round zero. Truncated quotient storage is refused. Both focused tests passed; the explicit workload is separately invoked. See [claim-tests.log](claim-tests.log) and [the test source](src/protocol/prover/ring_contraction_tests.rs).

[EXECUTED] The single release workload alternated nine old/new samples with 32 calls per sample after four warmups on each side, on an Apple M2 Max with rustc `1.98.0-nightly (91fe22da8 2026-06-21)`. Timing excludes common witness/table generation and all sumcheck/PCS work. The actual modified production proof then took 34.514 ms and verification 2.740 ms on the same shape. Those whole-proof numbers have no paired baseline and support only successful execution, not a measured whole-proof speedup. Its deterministic public field tensors require no encryption or secret key. All three PCS openings were present, all output coefficients matched, and a changed output was refused. The refusal uses an existing verifier `unwrap` panic, caught by the test; it is not evidence of a clean-error verifier API. Full output: [consumer-workload.log](consumer-workload.log).

Reproduce from `/tmp/matvec-ring-contraction-20260908`, or an independently patched checkout with the same locked dependencies:

```sh
CARGO_HOME=/tmp/matvec-ring-contraction-20260908/cargo_home cargo test --offline --locked --release --lib protocol::prover::ring_contraction_tests -- --nocapture
CARGO_HOME=/tmp/matvec-ring-contraction-20260908/cargo_home cargo test --offline --locked --release --lib protocol::prover::ring_contraction_tests::ring_claim_workload_and_real_pcs_consumer -- --ignored --exact --nocapture
```

[OPEN] This is a concrete optimization of the upstream ring proof relation, not a formal Rust refinement, a completed vFHE system or a change to the independent BFV Plonky3 lane. The current expanded-table sumcheck remains the larger next implementation seam; this package does not change its protocol or claim a new soundness result.
