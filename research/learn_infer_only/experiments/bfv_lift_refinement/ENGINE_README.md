# Full-coefficient fhe.rs oracle

[EXECUTED] Reproduce from zkml-research:

```sh
python3 research/learn_infer_only/experiments/bfv_lift_refinement/run_engine.py
python3 research/learn_infer_only/experiments/bfv_lift_refinement/check_engine.py
python3 research/learn_infer_only/experiments/bfv_lift_refinement/engine_costs.py
```

[EXECUTED] The first command runs Rust offline in an isolated Cargo workspace, records public full-coefficient fixtures, checks them independently, and writes `engine-run.json` and `engine-results.json`. It hashes the live source files before and after the execution, records the lockfile/toolchain/commands, and writes only this lane's directories. The second command checks the retained gzip without rebuilding. The third prints the computed source-arithmetic range and operation bill in `engine-costs.json`.

[EXECUTED] Eleven full tensors: four small seeded fresh encrypted pairs, one N4096/Q109 seeded fresh encrypted pair, and six structurally valid constructed N4096 boundary pairs. All **114,944 extension coefficients**, **86,208 integer-convolution coefficients**, and **86,208 unrelinearized output coefficients** agree with the literal source model. The five fresh pairs agree with centered nearest rounding on all12,480 output coefficients; the first tranche's unsigned-input reference differs at all12,480. Structured fixtures expose one extension-lift discrepancy and three exact-nearest rounding discrepancies. Each parameter family also has65 scalar extension and90 scalar downscale boundary checks; the N4096 family has33 and35 strict-reference disagreements respectively. There are no source-model mismatches.

[DERIVED] The probe recreates `Multiplicator::default`'s public extension basis and factors through `Multiplicator::new`, which uses the same implementation with relinearization disabled. It compares the entire three-component tensor, rather than decrypted messages. Constructed fixtures use `Ciphertext::new` and are not claimed to be fresh encryption samples. This is arithmetic evidence at library-admissible parameters, not a security/noise/PQ theorem or a break of BFV.

[DERIVED] `fhe_scaler_model.py` reexpresses RnsScaler's fixed-point arithmetic in Python integers, including wrapping and truncation. `check_engine.py` reconstructs CRT representatives independently and uses balanced Kronecker substitution for full signed negacyclic convolution, crosschecked against direct schoolbook convolution for N≤64. The final checker verifies that the downscaler's selected lift equals the full integer convolution on every retained tensor coefficient and that the observed rounding error lies in{0,1}. These are checked finite facts; the universal scalar arithmetic statement is in the separate Lean patch.

[EXECUTED] All retained data are synthetic and public. `engine_probe/target/` and the uncompressed scratch fixture are ignored. The current complete fixture is `engine_probe/full-coefficients.jsonl.gz`; the earlier smaller run is retained as `full-coefficients.jsonl.first.gz`. Source pins include fhe-dregg and cached fhe-math0.1.1. The selected vendored `ops/mul.rs` is byte-identical to cached upstream fhe0.1.1. No Scry search, private credential read or PDF download was used in this tranche.

[SOURCE: local extraction] The full PDF text and rendered scratch pages are ignored. Extraction command: `pdftotext -layout /Users/ember/dev/gh/forks/IACR-eprint-mirror/2021/204.pdf research/learn_infer_only/experiments/bfv_lift_refinement/paper-2021-204.txt`. Source PDF hash and inspected locations are retained in `engine-run.json`; the note records Remark3.2 and §3.3 without treating the paper as an exact implementation theorem.
