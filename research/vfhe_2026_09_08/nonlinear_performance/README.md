This successor builds a corrected, compact proof path for one complete nonlinear BFV class kernel on the saved public `live001/query01/class000` inputs. The complete fresh consumer accepted all 116 proofs at `runtime/consumer001/RESULT.json`. Complete proof data fell 8.19%; MAC proving fell 16.85%, while whole proving improved only 1.69% and full peak memory rose. See `REPORT.md` for the measured costs and the preserved wrapper-error correction.

The public consumer binds the caller-approved model ciphertext, query, evaluation key, and kernel ciphertext digests. It covers the packed dot/reduction computation and the complete square: 88 paired-MAC chunks, four basis-extension chunks, 18 tensor-product chunks, and six rescale chunks. All 116 proofs in this successor are new. The old model ciphertext is an approved input; its historical teaching chain is not re-proved here. This is one class kernel, not another multiclass decision or private-reader execution.

[DERIVED] The compact compiler retains 349 source columns. Range completion constructs omitted Boolean witnesses and applies the frozen paired-MAC theorem. `formal/Compiler/RangeKeyswitchInfer.lean` joins the compact row result to the existing full kernel source contract. The emitted arithmetic uses the shared Lean whole-row fold. Square templates use the shared strict migration that preserves each normalized source arithmetic body and all lookups/metadata. It was validated against that fold on the generated query artifact.

[SOURCE] This also repairs a substantive historical error: legacy `gate` assertions were transition-only and left the final row of each chunk arithmetically unconstrained. Every successor arithmetic assertion is `window_gate/on_transition:false`. Historical proof acceptance remains historical executed evidence; it is not reused as a complete arithmetic argument.

[EXECUTED] `backend/checks/010-compact-shape.json` records the patched native shape: 1,293 main columns plus 132 Ext4 permutation columns, or 1,821 base-field equivalents, versus 2,659 for the historical MAC. The existing four-bit range table is unchanged. At most four consecutive global lookup interactions on the same bus are grouped while preserving tuples, order, and signed multiplicities. This changes the MAC to three AIR instances, degree six, and eight ZK quotient chunks. All four copied public reader binaries compile against that isolated patch; `runtime/build001/BUILD.json` records the builds.

The proof configuration retains FRI blowup 3, 38 queries, query proof-of-work 16, extension degree four, four salts/random codewords, and witness hiding. The profile and grouped backend ID are new. The historical numerical PCS/extraction theorem for a different pinned query layout is **not** inherited. The source range-completion and whole-row arguments do not formalize the Rust parser, descriptor lowering, LogUp/FRI implementation, seed expansion, NTT transforms, or protocol controller.

Run the same complete public case from the frozen request:

```sh
python3 research/vfhe_2026_09_08/nonlinear_performance/runtime/api.py prove /absolute/new-run
```

Consume its retained proof bundle separately, without producing proofs or reading secrets:

```sh
python3 research/vfhe_2026_09_08/nonlinear_performance/runtime/api.py verify \
  /absolute/approved-request.json /absolute/produced-run /absolute/new-verification
```

These commands require the pinned workspace and saved public case files named by the request. They do not invoke an encoder, encryption, setup, or reader. `runtime/pipeline.py` also exposes the existing caller-selected update/Infer producer and verifier interfaces under the new approved profile; the measured execution is the single saved class Infer. `CONTRACT.md` fixes the no-retry, public-only attempt and comparison scope. Raw witness traces are compressed and ignored by Git; proofs, costs, and public bindings are retained.

The historical `runtime/run.py` wrapper is frozen with its optional-diagnostic failure; use `runtime/api.py`, which selects the exact metadata checker exercised in `consumer001`. That final dispatcher is source/CLI-checked; production and full acceptance were executed separately once, with no repeat for packaging.
