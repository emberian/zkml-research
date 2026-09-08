[EXECUTED] Completed isolated implementation and one before/after workload. Existing `prove_matmul` median 7.817ms→1.970ms (3.97×), outer binding 7.728ms→1.726ms (4.48×), same complete transcript. Existing Lean-authored conformance and focused equivalence/order/refusal tests pass in release; 60 existing library tests also pass in debug. See README.md and outer-mle-reuse.patch.

[EXECUTED] Baseline 6937394e1dc2c2aaff986c7d4b3a258aca5d16fd; isolate `/tmp/minidregg-prover-performance-20260908`, branch `research/outer-mle-reuse-20260908`. Original companions unchanged. Patch applies and reproduces the checked files. No proof relation, wire, challenge or soundness knob changed.

[OPEN scope] This accelerates the actual contraction engine's algebraic prover. Commitments and the current BFV DescriptorIR-v2 STARK remain outside the measured path. Root owns integration.

[EXECUTED follow-on] Completed the actual ring prover consumer in ring_consumer/: shared Y/Q contraction replaces two claim-total scans, 550444ns→63639ns on one public r4/m2/k2/D1024 workload. Two focused tests and a PCS-enabled production proof pass; unchanged verifier accepts all8192 output coefficients, modified output refused via existing panic behavior. Successor patch after the fused ring patch is ready; no whole-proof speedup claim.
