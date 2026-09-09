The app uses retained runtime artifacts from this working tree. Check them with the root launcher or directly:

```sh
python3 research/vfhe_2026_09_08/continuing_system/bootstrap.py --check
python3 research/vfhe_2026_09_08/continuing_system/bootstrap.py --build
```

`--check` is the default. It verifies the caller profile's operational pins, issuer source pins and local E5 model files, reports the seven required executables, and finds the encoder Python environment. It performs no key generation, proof, model load or model forward pass. `CONTINUING_SYSTEM_PROFILE` and `CONTINUING_SYSTEM_WORKER` select the same alternatives as the application backend.

The retained encoder environment is `research/learn_infer_only/experiments/adaptation_utility/.venv/bin/python`, with dependencies recorded in that directory's `requirements-lock.txt`. The system Python currently lacks torch/transformers; use the root launcher, which selects the retained environment. Bootstrap reports both environments and does not install packages.

`--build` skips every valid executable. For a missing known Rust executable, it runs the retained package's exact release target with Cargo `--offline --locked`, four build jobs and an isolated temporary target directory. The diagnostic includes the full command, manifest, environment and build log. The four grouped proof wrappers use `nonlinear_performance/runtime/native/{infer,square,rescale,update}/Cargo.toml`; the generic witness executor uses `rescale_native_emitter/native/Cargo.toml`; the issuer/capture binary uses `research/learn_infer_only/experiments/end_to_end/nonlinear_successor_2026_09_08/crypto/Cargo.toml`.

A built executable is installed only if its bytes match the expected pin and its destination is still absent. Existing mismatches are never overwritten. A different successful build is retained as a candidate with an actionable diagnostic; bootstrap neither changes frozen pins nor asserts reproducible binary identity across toolchains/build paths. System zstd, model files, JSON templates and witness plans are restore prerequisites, not Cargo targets. No Lean build is needed for runtime launch because the emitted circuit artifacts are retained.

The current workspace passed both modes: 59 pinned files and seven executables valid; `--build` performed zero builds. The missing-executable Cargo/install path was not exercised merely for this check. Bootstrap does not claim that a fresh clone is portable: retained profiles, the E5 configuration and Cargo local dependencies contain absolute paths to the research tree, companion source trees, Cargo cache and model cache. Restoring those dependencies or deliberately constructing a new development profile is necessary on another machine. Companion sources and existing approved binaries remain unchanged.
