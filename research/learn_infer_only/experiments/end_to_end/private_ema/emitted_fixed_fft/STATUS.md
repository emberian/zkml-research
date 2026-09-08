# Fixed-FFT generic successor

[EXECUTED complete] The separate fixed-feature build passed tests and all five
public replay pairs (ten host processes), ending 2026-09-08 04:48:49 UTC, exit 0.
Every process observed Dif4/base512/FFT512 at polynomial size 1024; all public
input/executable hashes and complete-byte replay comparisons matched. The
completed emitted_runtime source/freeze/smoke remain unchanged.

[SOURCE correction] `fft64-default` was preliminary shorthand, not the TFHE
1.6.3 Cargo feature. Cached source declares the exact feature above and selects
UserProvided Dif4 at the Fourier size instead of Measure(10ms). Source evidence
and build feature resolution will be retained before execution.

[EXECUTED evidence] REPORT.md, SOURCE_AUDIT.md, summary.json, costs.csv and
reports/controls/ retain the exact result. inputs.json fixes the four prior
sample tuples plus the old fourteenth-failure public input tuple. freeze.json
SHA256 is `b6805534d4aa32d4ea99f7017d71a3a38738a8c60fc84370c471826cfa94077e`;
binary SHA256 is `6c0954fae626940e720c47bfb535347ecd3c3fc0b19b36d0834b70465b02d197`.
Build logs/compiler feature events, source archive checks and all ciphertexts
are retained. No private reader, decryption, old failed-output file read, retry
or long workload occurred. No commits were made from this lane.

[OPEN scope] The result concerns five fixed public tuples on the recorded
Apple M2 Max/aarch64 build and observed plan. It neither proves general
determinism nor diagnoses the old failure or tests plaintext correctness under
the changed FFT feature. Root owns any separately coordinated successor.
