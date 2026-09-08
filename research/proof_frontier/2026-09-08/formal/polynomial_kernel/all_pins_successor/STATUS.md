# Polynomial all-pins successor — checked

[EXECUTED] Root requested this integration-only successor because the existing combined integration census requires a guarded axiom report for every theorem/lemma declaration. The original eight-pin package remains frozen. This package appends eight exact guards, yielding sixteen declarations and sixteen guards.

[EXECUTED] The complete original source is a byte-for-byte prefix of the successor. Every mathematical definition, theorem statement, proof body, namespace, import and public signature is unchanged. `proof_body_preservation.json` records that comparison. All sixteen declarations are theorems; there are no additional private theorem/lemma declarations left without a pin.

[EXECUTED] The actual existing `experiments/integration/check_all_formal.py` census accepts the successor with sixteen declarations, sixteen pins and no forbidden constructs; see `integration_census.json`. The original eight guards and newly observed helper axiom reports all have only `[propext, Classical.choice, Quot.sound]` dependencies.

[EXECUTED] `lake env lean Theory/PolynomialMatrixKernel.lean` exits zero with empty stdout/stderr and all sixteen guards, at exact source SHA256 `6c2aa5d0be03d7c00c3aca459eff2532570f205f6af604210f2cf033aaaec5dd`; see `lean_final.json`. Source is in `PolynomialMatrixKernel.lean`. The complete checked patch is `polynomial-kernel.patch`, SHA256 `83b4a44a855109efbbcc2b467f4531c52faf1374e5a83718c884277b8c275ae4`.

[EXECUTED] The patch adds the same module destination and unchanged Apache license. Fresh application with `--whitespace=error-all`, reconstructed-byte equality and the import-boundary script all pass; see `patch_and_import_checks.json`. Source/patch/toolchain/license pins are in `provenance.json`. Isolated checkout: `/tmp/minidregg-polynomial-all-pins-20260908`, based on minidregg `6937394e1dc2c2aaff986c7d4b3a258aca5d16fd`, Lean 4.30, Mathlib `1c2b90b13009c65b090d95a83c98e248deafb6f1`.

[SOURCE] The original attributed ArkLib source remains `22dbd4e836c15a21f68889afa69b7130da04abbb`, BWMatrix.lean:606,618,630,742,760,789,937,944,1175. Copyright/authors and complete Apache 2.0 license remain unchanged; there is no new mathematical claim in this successor.

[EXECUTED] `integration_entry.json` supplies the replacement lane entry and exact source override for the existing root integration tool. `support_file_entry.json` supplies its license support entry. Paths in both entries are relative to `research/learn_infer_only`, matching that tool's `RESIDENT` root.

[OPEN] Root owns combined integration and the full umbrella build. The full-UD consumer retains the exact same theorem name/signature/body; only diagnostic guards change. No further lane theorem work remains.
