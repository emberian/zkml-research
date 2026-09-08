# Next

[EXECUTED] Full repaired-point measurement is complete and sealed in
`MANIFEST.json`; see `REPORT.md`. The next performance target is native/batched
Gaussian proposal handling: sampling consumed 146.71 seconds of setup and
7.24–8.92 seconds per encode. Exact FLINT multiplication at N=16384 took
0.02475 seconds for one saved arithmetic probe, so changing the ring backend
is not the first demonstrated bottleneck. Do not rerun the prior estimator
or reopen frozen proof packages merely to validate this code.

[OPEN] Potential next implementation work: native/batched Gaussian proposals,
shared decode coefficient extraction, compact ciphertext packing and distinct
recipient processes. Decode currently extracts ciphertext coefficients again
for each recipient; sharing that extraction is another concrete optimization.
These are not claims of implemented behavior.
