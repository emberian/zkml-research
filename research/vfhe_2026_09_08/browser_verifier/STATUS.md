# Browser verifier construction

[SOURCE] The isolated wrapper now imports the shared
`vfhe_public_preprocessing_backend::FixedPublicPreprocessing` adapter on the
same typed descriptor, exact-public table 11 and postcard proof format as
`proved_operation`. It uses the existing generic IR2 verification routine.
It adds no arithmetic AIR, witness generation or simulated verification.

[EXECUTED] Complete: the shared portable-adapter WASM and native CLI builds
succeeded. The frozen module is 2,063,586 bytes, SHA256
`96137c1ed0ad5fc7584ca72ef006ff70ac1951831408ee12ab22ce3879f6f908`.
Two genuine proofs passed the same browser-target module under Node WebAssembly:
the complete BFV `3·A+5·B` relation and actual learner event 65 `acc+fresh−old`.
Each changed-public-output control reached the real verifier and was rejected.
The main companions and microsite remain unchanged.

[EXECUTED debug only] `results/proof001-debug.json` records one check of the
prover's unsuccessful proof001: the actual WASM verifier rejects it with the
same `InvalidOpeningArgument(InvalidPowWitness)` reported by the native prover
lane, in 2001 ms. That artifact is not a genuine fixture and is not packaged
for a demo. The command/source are `web/verify-file.mjs`; no reproof was done here.

[EXECUTED] `web/` and both fixture directories are frozen for root's site
integration. `BROWSER_PACKAGE.json` records approved template hashes, all asset
sizes/hashes and the verification result paths. No extra validation cycle is
needed. Original pre-adapter sources/artifacts remain in `results/pre_adapter/`.

[OPEN] Root owns UI integration and actual browser-engine measurements. This
consumer checks caller-selected public rows; ciphertext decoding, event/FIFO
authorization, key membership and plaintext correctness are outside its claim.
