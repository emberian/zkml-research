# Checked patch and reproducibility

[EXECUTED] **27 theorem declarations / 27 exact `#guard_msgs` axiom pins pass.** The module builds to an `.olean`, an isolated copy of the **Compiler umbrella including the new import builds**, the companion's existing import-boundary script passes, and `git apply --check` accepts the patch. The complete command/output ledger is `validation.json`; hashes and a compact result are in `validation-summary.json`.

[EXECUTED] The checked companion commit is `6937394e1dc2c2aaff986c7d4b3a258aca5d16fd`; Lean4.30.0, arm64 Apple Darwin. The patch adds `Compiler/BFVScaleLiftRefinement.lean` and one import to `Compiler.lean`. Source imports only `Mathlib.Tactic`. No source file or compiled output in minidregg or breadstuffs was written. Temporary `.olean` files and the copied umbrella were created under this lane's directory and removed after checking.

[EXECUTED] Reproduce the formal validation from the companion environment:

```sh
cd /Users/ember/dev/minidregg
/Users/ember/.elan/bin/lake env python3 /Users/ember/dev/zkml-research/research/learn_infer_only/formal/bfv_lift_refinement/validate.py
```

[EXECUTED] Reproduce the finite audit from the research tree:

```sh
cd /Users/ember/dev/zkml-research
python3 research/learn_infer_only/experiments/bfv_lift_refinement/audit.py
```

[DERIVED] Every theorem's exact axiom dependency is pinned. Eight concrete arithmetic teeth depend on no axioms; `canonical_lift_unique` uses only `propext`; the other theorems use at most `[propext, Classical.choice, Quot.sound]`. No `sorry`, custom axiom, `native_decide`, unchecked reduction or `#guard` unit test appears. Theorems proved with `decide` are kernel computations, not VM-only tests.

[OPEN] This is an **isolated Compiler umbrella check**, not a full Minidregg default build or an independent review of the theorem statements. The root swarm owns combined integration and independent adversarial review. Compiler emission, runtime-library refinement, ciphertext decryption correctness/noise and cryptographic proof soundness remain absent from the claims.

[EXECUTED] Earlier failed iterations are retained rather than relabeled as successes: `build-first.log` records missing decidability unfolding for proposition abbreviations; `build-second.log` and `build-third.log` record tactic-unfolding/absolute-value cast corrections. `validation-failed-root.json` records an output-module root mismatch; `validation-failed-umbrella-path.json` records Lean module lookup selecting the first Compiler directory. The final validator fixes these by compiling from the proper isolated root and supplying read-only symlinks to cached Compiler dependencies. No mathematical counterexample to the final theorem was suppressed by these corrections.

[EXECUTED] `axioms-unpinned.log` is the earlier single-convolution module's actual axiom output; `axioms-final-unpinned.log` includes the tensor extension. The final source pins the latter exactly. `minidregg-bfv-lift-refinement.patch` is the artifact for the maintainer to apply; do not apply it from this research run.
