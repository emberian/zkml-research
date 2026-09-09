# Status

[DERIVED] The complete matched-field AIR, SHA-256 PCS/challenger configuration,
352-chunk linear and 32-chunk update producer/independent-consumer CLI, and cached
public reconstruction are implemented in the isolated `native/` crate. The
four-prime field module and quartic extensions are integrated. No companion tree
was edited.

[EXECUTED] The first offline single-job Cargo check populated dependencies and
stopped because the concurrently authored field module had not yet landed.
Command/output: `experiments/cargo-check-01.log`. This is not a successful build.

[EXECUTED] Normal library tests pass: 11 passed, 0 failed, 1 deliberately ignored
proof test. The tests include complete prime/generator certificates for all four
primes, independent quartic irreducibility checks, arithmetic/root/Frobenius tests,
strict canonical parsing, fixed-plan mutation rejection, and both MAC equations
rejecting an invalid final row. Output: `experiments/cargo-test-lib-01.log`;
command: `experiments/COMMANDS.md`.

[EXECUTED] The complete release build succeeded offline in 2m 36s, including both
update and linear native APIs. `experiments/cargo-build-release-01.log` retains
the output. `PIPELINE.json` pins the executable, caller, and linear plan;
`experiments/profile-check.json` and `experiments/native-profile.json` retain the
successful profile checks. `SOURCE.json` records source, binary and local patched
dependency identities.

[EXECUTED] The retained optimized-Python contract test passed its valid cases and
11 rejection cases for both interfaces, with no cryptographic operations:
`experiments/caller-contract-check.py` and `.log`.

[EXECUTED] The first full actual FIFO-expiry update and linear query passed:
384 fresh proofs were produced and all 384 independently consumed. Update and
dot ciphertext bytes equal the retained lifecycle captures. No source fix,
standalone preflight proof, new key or private read was needed. The same pinned
native/caller/profile artifacts are frozen for the full-app engine integration.

[EXECUTED] Shared-machine observed production/consumption wall times are
2.61/1.20 seconds for update and 45.05/14.20 seconds for linear. Total distinct
proof transport is 70,058,364 bytes. `experiments/fifo-expiry-run001.json` retains
input identities, native and caller timing evidence, output equality, memory,
and the two post-run consumer rejection controls. `COSTS.csv` is the phase table.

[OPEN] No numerical soundness, security-equivalent speedup, end-to-end formal
correctness, signed decoder result, or complete continuing-app lifecycle is
claimed by this lane. The parent and whole-app integration owner handle that
lifecycle and its existing signed reader.

[EXECUTED] External search count: zero. Local source inspection only.
