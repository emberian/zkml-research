# Next for the reviewed project-source rebuild

[OPEN root action] Run the pinned 952-pin manifest with `--rebuild-project`.
Record its own Lean result, compiled-module order, empty project-cache inventory,
filtered LEAN_PATH, output paths and before/after source hashes. The review's
567-module graph is the current expected four-umbrella source closure.

[DERIVED boundary] Preserve the 29 baseline sources outside that closure and
the external package/toolchain cache distinction in the resulting claim. Existing
generated conformance/Rust files should appear only under the run's copied source
working directory. No dependency rebuild or whole-companion build is inferred.

[OPEN changed inputs] New manifests or changed checker/source bytes need a new
bounded preflight. The next proposed execution-proof package is outside this
review's 952-pin approval. No shared truth ledger update follows automatically.
