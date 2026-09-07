# Complete utility workload through the verifying reader

[OPEN execution in progress] `utility_001` runs both previously selected public
histories through actual BFV, the repaired public journal and the independent
verifying reader. The intended denominator is all 384 Learn and 96 Infer
commands, including the 16 known-empty outputs. It does not select examples or
run, train or download a model. Final numbers must come from the completed
`utility_001/report.json`.

[SOURCE] Before this run, the repaired baseline
`journal/results/utility_002/report.json` recorded all 480 commands and 96 exact
integer comparisons. The separate `journal/results/live_text_002/report.json`
recorded one new text's issuer encoding and one Learn/two Infer operations.
This driver does not rerun that text or use it to enlarge the held-out sample.
Their exact report hashes, materialized fixture hashes and source/binary hashes
are pinned in this run's `fixture_pins.json` and `source_pins.json`.

[DERIVED protocol] Setup uses fresh OS randomness and the existing real-BFV CLI.
The initial baseline receiver started by the shared Run helper is stopped before
any workload command. A distinct verifying-reader database and CAS take over
the authority's delivery socket. The command authorizer registers each query
ticket there. Learn finalizes and is independently replayed. Infer's first
publication remains pending until its envelope is independently replayed; an
exact authority retry then releases through the verifying reader. No baseline
decryption is used. Fresh inputs, public queries and the initial zero are the
only blobs uploaded to the verifier, which computes each result itself.

[DERIVED data boundary] Only the issuer and test oracle receive the copied
plaintext fixture. Public host/authority processes receive ciphertexts, public
queries and signed command metadata. The trusted verifier retains the full BFV
secret; this is benchmark R, with no master-key-absence or OS-isolation claim.
The fixture was already public, so this is known-state utility integration,
not fresh-private-ingress confidentiality evidence. Issuer provenance, command
policy and reader persistence remain trusted. Ed25519 authentication is
classical; the composition has no end-to-end post-quantum claim.

From the repository root, with the already-built crypto CLI and materialized
frozen inputs, one command executes the complete normal workload:

```sh
python3 research/learn_infer_only/experiments/end_to_end/verified_reader/utility_driver.py
```

Choose unused `--runtime` and `--reports` paths for another execution. Runtime
must remain under the ignored `verified_reader/runtime/` directory to preserve
the intended artifact discipline. Ciphertext bytes and timing vary with fresh
randomness and machine load. No adversarial-control code is imported or run.
