# One minidregg integration patch for completed FHE arithmetic

[EXECUTED] [minidregg-fhe-arithmetic.patch](minidregg-fhe-arithmetic.patch) collects the completed requested packages into one applicable patch against minidregg commit `6937394e1dc2c2aaff986c7d4b3a258aca5d16fd`. It contains **27 completed compiler modules, 15 required predecessor modules, seven exporters, one new import umbrella and one root import change: 51 files total**. All 49 copied source/exporter files match their previous recorded pins. The two new glue files contain imports/documentation only; no theorem or arithmetic implementation changed.

[EXECUTED] The patch applies cleanly to a sparse copy of the recorded base and to a copy of the current dirty `Compiler.lean`. It also passes read-only `git apply --check` in the actual main tree. The existing root edits, including `UwueavePreoProjectionV2` and the other imports/comments, are preserved; only one `Compiler.FheArithmetic` import is added. Main minidregg and all frozen research packages remain unchanged. See [patch_application.json](patch_application.json).

| [SOURCE] Completed package | Imported entry points | Exact covered scope |
|---|---|---|
| `arithmetic_coverage` | `BfvOperationWitness` and its linear/expiry layouts | Canonical whole-word `3A+5B mod q` and `acc+fresh−old mod q`, with range/carry constraints and witnesses. |
| `arithmetic_rescale` | `BfvRescaleSound`, `BfvRescaleWitness` | One source relation joins the exact directed six-input rounding certificate and three canonical target projections through the same integer output. Preceding convolution is separate. |
| `arithmetic_rescale_generic` | `DirectedRnsEmit`, `DirectedRnsExhibits`, `NonlinearRnsPublicSound` | Parameterized signed-matrix/RNS compilation under its capacity, positivity, divisibility and exact-gamma premises; the captured 9→4 instance preserves native projected arithmetic. Its runtime exercised 32 selected positions, not the whole ciphertext. |
| `compiler_cost_successor` | `AirAssertionShare`, `BfvRescaleAssertionShare` | Stable full-syntax assertion sharing preserves the accepted source assignments and existing emitted-descriptor meaning. |
| `bootstrap_successor` | `TfheModulusSwitch` | Exact native-u32 rounding/wrap map into 1024 rotation exponents; no full PBS claim. |
| `bootstrap_rotation_successor` | `TfheInitialRotation` | Forced index/sign and wrapping-u32 coefficient law for the initial degree 512 GLWE rotation, including permutation lemmas. The runtime's two-proof join is separate from the Lean arithmetic theorem. |
| `query_arithmetic` | `BfvQueryWitness`, `BfvQueryTeeth` | Whole-word multiplication for `0<q<64^7`, composed into both ciphertext/plaintext products and final subtraction of the current two-prime query. Encoding, decryption and classification remain separate. |

[SOURCE] The dependency chain is included, rather than requiring the maintainer to reconstruct earlier overlays: `IntegerCertificateEmission`, `AirSimplify`, `BFVScaleLiftRefinement`, `FheRnsScaleDecomposition`, and the required source-certificate/target-projection modules. Their retained final validation summary supplies their exact source pins. Old `Checks` runners, abandoned probes, trace/proof payloads and native runtime crates are not imported or bundled. Ongoing `rescale_compiler_successor` is excluded. Separate proof-frontier work is also outside this patch.

[EXECUTED resolution] `EmitBfvRescale.lean` is the completed assertion-sharing exporter, SHA256 `d9749e5db641e99334e09d28e5d314c559ea47adf8e54ce8b5ed9147c7935333`, replacing the earlier exporter `7abd63fda7ec6a3224864205cd5636617ea971dbb458d6248395e08edb1692fd`. This is the sole overlapping target. The other six exporters retain their exact completed bytes. No parallel old rescale exporter is added. [PROVENANCE.json](PROVENANCE.json) records every target, original source, existing pin, owner group, dependency order and reused validation record.

[EXECUTED integration validation] Only new import glue was compiled with retained completed-module oleans: `Compiler/FheArithmetic.lean` (3.13s), the patched base `Compiler.lean` (3.53s), and the patched dirty-root copy (2.99s), all exit 0 with empty outputs. The existing read-only import-boundary script passes. [glue_checks.json](glue_checks.json) contains exact commands and Lean paths; [reused_oleans.json](reused_oleans.json) identifies the reused artifacts. Initial overlay setup failed to locate one retained predecessor olean, then the first import check found a missing base-cache link; both were corrected by linking existing artifacts. No completed proof module was rebuilt, no exporter was rerun, and no whole-tree build or new audit was performed.

[SOURCE landing] From the maintainer's selected minidregg checkout:

```sh
git apply --check /absolute/path/minidregg-fhe-arithmetic.patch
git apply /absolute/path/minidregg-fhe-arithmetic.patch
lake build Compiler.FheArithmetic
```

[SOURCE] `Compiler.lean` imports that umbrella, so the existing `Minidregg` target reaches every included compiler module. [BUILD_ORDER.txt](BUILD_ORDER.txt) gives the resolved dependency order for targeted work; Lake can determine the same order from imports. Exporters are executable entry files, used with their original caller-owned output directories and public-row arguments. Their historical evidence and invocation details remain in the corresponding frozen research packages.

[OPEN maintainer gate] Per `CLAUDE.md`, the eventual whole-tree `lake build Minidregg` is the landing integration gate. It was intentionally not run during this swarm task. New import-glue success reuses the recorded dependency artifacts; it does not replace a fresh full-tree source build. This patch establishes no additional theorem beyond the existing packages, and no Rust/serialization/proof-backend refinement, end-to-end FHE privacy, full ciphertext-multiplication or full programmable-bootstrap security claim.

[EXECUTED provenance] Patch SHA256: `7e3e625deefe311d1f7d359ca6f3fc54fc727818bc138afaf955170cc42ed265`. Source/package pin checks were limited to the files being integrated and their existing records; no global re-hash or audit campaign. No web/Scry/Kagi query, cryptographic execution or companion write occurred in this integration task.
