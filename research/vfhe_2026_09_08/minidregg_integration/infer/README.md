# One minidregg patch for the complete nonlinear Infer dependencies

[EXECUTED] [minidregg-complete-infer.patch](minidregg-complete-infer.patch) is one applicable cumulative patch: **90 files, comprising 76 Compiler modules, 13 Lean exporters and the root import change**. It includes the frozen [51-file arithmetic patch](../minidregg-fhe-arithmetic.patch), which remains unchanged. All 88 copied files retain their recorded completed-source bytes; only the new umbrella and root import are integration glue. Patch size is 541,726 bytes; SHA256 `41334884b11980604bcaaafacaa6dfdbc14ccc9b42027e790d7f136b51030ff7`.

[SOURCE] The cumulative target is minidregg base `6937394e1dc2c2aaff986c7d4b3a258aca5d16fd`. It includes the original arithmetic package, the completed per-row rescale compiler and witness-plan emitter, exact basis extension, full tensor-square arithmetic, paired key-switch MAC arithmetic, and the final whole-Infer composition. The required `Compiler/BfvQueryWitnessPlan.lean` instruction builder is included explicitly so the maintainer does not reconstruct research overlays.

[EXECUTED resolution] New glue consists only of `Compiler/FheInfer.lean` and one additional `Compiler.lean` import. **The root file is the sole overlapping target:** it retains the predecessor's `FheArithmetic` hook and appends `FheInfer`. No arithmetic or exporter target conflicts occurred. The original `Compiler/FheArithmetic.lean` and all previously resolved source bytes are retained. `EmitBfvRescale.lean` remains the earlier integration's assertion-sharing replacement; its superseded exporter is not reintroduced. Separate TFHE/soundness expansions and the paused restricted-ring work are excluded. Native runtime crates, generated proof/trace payloads, diagnostic runners and constant-regeneration scripts remain outside this source patch.

[SOURCE] The intended source contract covers the saved N8192 level-zero Infer: initial ciphertext–plaintext multiplication, ten rotation/add stages using paired modular MACs, then basis extension, tensor square and directed rescale. `BfvInferContract.inferSound` joins accepted source rows and their common intermediate arrays into one output implication. The source's public transform callbacks and input-specific common-modulus roundtrip remain explicit premises. Native parsing, seed expansion, encoding, NTT/serialization implementation, exact byte/stage bindings and proof-protocol soundness remain external obligations. Consolidation adds no theorem, BFV security, decryption/noise, learning-utility or recipient-privacy claim.

[EXECUTED validation] The patch applies exactly in owned sparse copies of the recorded base and the actual dirty `Compiler.lean`; all existing dirty-root edits are preserved. Read-only `git apply --check` in the actual companion also passes. Only three import files were compiled using retained completed-module oleans: the new `FheInfer` umbrella (21.09s), the patched base root (10.33s) and the patched dirty-root copy (10.00s), all exit 0 with empty outputs. The existing Theory/Selvage import-boundary script passes, and this patch changes neither namespace. No completed theorem module was rebuilt, no exporter or runtime was rerun, and no companion file was written.

[SOURCE landing] This is a cumulative replacement for the *proposed patch*, not a patch to stack on top of the old proposal. From an appropriate maintainer checkout, apply only the final cumulative patch:

```sh
git apply --check /absolute/path/minidregg-complete-infer.patch
git apply /absolute/path/minidregg-complete-infer.patch
lake build Compiler.FheInfer
```

[SOURCE provenance] [PROVENANCE.json](PROVENANCE.json) records every target's original source/pin, resolved import order, completed-package evidence, retained oleans, exact commands and preservation checks. The final composition pin file is `1c59ee77e6284ba46001fcbff896125e522bfaccd72f4838114fd34881798e7c`; its five modules and exporter are included unchanged. `assemble.py` and `check_integration.py` document this consolidation. No independent source review, new math, cryptographic execution, web search or proof rechecking was performed.

[OPEN maintainer gate] The eventual full-tree `lake build Minidregg` remains the companion's landing gate. The successful import-glue checks reuse the authors' retained artifacts and do not replace that fresh full-source integration build. Root owns landing this proposal with the accepted runtime.
