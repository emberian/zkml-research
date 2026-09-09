The app uses retained runtime artifacts from this working tree. From the repository root:

```sh
python3 research/vfhe_2026_09_08/continuing_system/run.py check
python3 research/vfhe_2026_09_08/continuing_system/run.py build --engine linear-compact
python3 research/vfhe_2026_09_08/continuing_system/run.py build --engine linear-matched
python3 research/vfhe_2026_09_08/continuing_system/run.py build --engine packed-matched
python3 research/vfhe_2026_09_08/continuing_system/run.py check --engine all
```

`--engine` accepts `squared-compact` (default), `linear-compact`, `linear-matched`, `packed-matched`, or `all`, for both `check` and `build`. The default does not read or require optional engine files. Compact linear adds its native producer/consumer/reader; matched linear adds its native producer/consumer and uses the same signed reader. Packed matched includes those matched-engine prerequisites plus the dedicated reader for signed class sums. `all` includes all four modes. All modes retain the shared issuer/base dependencies checked by the current application. These flags check prerequisites; score and proof backend are chosen separately when creating a learner.

The check verifies selected operational pins, issuer source pins, local E5 model files and the encoder Python environment. Optional native build sources are checked against the compact linear profile or matched `SOURCE.json`, including the latter's recorded local dependencies. It performs no key generation, proof, model load or model forward pass. For direct invocation, `bootstrap.py --check` is the default and `bootstrap.py --build --engine ...` is equivalent to the launcher.

`CONTINUING_SYSTEM_PROFILE` / `CONTINUING_SYSTEM_WORKER` retain their base-backend meaning. Optional profiles and workers follow `CONTINUING_SYSTEM_LINEAR_PROFILE`, `CONTINUING_SYSTEM_LINEAR_WORKER`, `CONTINUING_SYSTEM_MATCHED_PROFILE` and `CONTINUING_SYSTEM_MATCHED_WORKER`, exactly as the app does. Corresponding `--profile`, `--worker`, `--linear-profile`, `--linear-worker`, `--matched-profile` and `--matched-worker` flags override them for a check/build. Matched mode checks that its proof plan agrees with the signed reader's plan.

Packed reader paths follow `CONTINUING_PACKED_READER` and `CONTINUING_PACKED_READER_PROFILE`, with `--packed-reader` and `--packed-reader-profile` overrides. Bootstrap checks its five operational pins against `packed/reader/PROFILE.json` and the source/binary/profile identities in `packed/reader/SOURCE.json`. Its four source files must match before a missing reader can be rebuilt; the new binary must then match the fifth pin before installation.

The retained encoder environment is `research/learn_infer_only/experiments/adaptation_utility/.venv/bin/python`, with dependencies recorded in that directory's `requirements-lock.txt`. The system Python currently lacks torch/transformers; use the root launcher, which selects the retained environment. Bootstrap reports both environments and does not install packages.

`--build` skips every valid executable. For a missing known Rust executable, it runs the retained package's exact release target with Cargo `--offline --locked` in an isolated temporary target directory. The optional linear, matched and packed-reader packages use one build job, matching their retained build settings; existing packages use four. Optional source-pin failures stop that binary's build. Diagnostics include the full command, manifest, environment and build log.

The compact linear manifest is `continuing_system/linear/native/Cargo.toml`; matched field uses `matched_field/native/Cargo.toml`; the packed reader uses `continuing_system/packed/reader/native/Cargo.toml`. The four grouped proof wrappers use `nonlinear_performance/runtime/native/{infer,square,rescale,update}/Cargo.toml`; the generic witness executor uses `rescale_native_emitter/native/Cargo.toml`; the issuer/capture binary uses `research/learn_infer_only/experiments/end_to_end/nonlinear_successor_2026_09_08/crypto/Cargo.toml`. No optional build changes their sources or approved binaries.

A built executable is installed only if its bytes match the expected pin and its destination is still absent. Existing mismatches are never overwritten. A different successful build is retained as a candidate with an actionable diagnostic; bootstrap neither changes frozen pins nor asserts reproducible binary identity across toolchains/build paths. System zstd, model files, JSON templates and witness plans are restore prerequisites, not Cargo targets. No Lean build is needed for runtime launch because the emitted circuit artifacts are retained.

[EXECUTED] The current workspace passed default `check` (59 pinned files, seven executables) and `build --engine all` (125 pinned files, nine executables). The latter performed zero builds; logs are `/tmp/continuing-bootstrap-default-check.json` and `/tmp/continuing-bootstrap-all-build.json`. The missing-executable Cargo/install path was not exercised merely for this check.

[EXECUTED] After adding packed mode, one Python parse and `check --engine all` passed: 130 pinned files and ten executables, including the packed reader's exact binary. Log: `/tmp/continuing-bootstrap-packed-all-check.json`. No build or cryptographic command was run for this extension.

Bootstrap does not claim that a fresh clone is portable: retained profiles, the E5 configuration and Cargo local dependencies contain absolute paths to the research tree, companion source trees, Cargo cache and model cache. Restoring those dependencies or deliberately constructing a new development profile is necessary on another machine. Companion sources and existing approved binaries remain unchanged.
