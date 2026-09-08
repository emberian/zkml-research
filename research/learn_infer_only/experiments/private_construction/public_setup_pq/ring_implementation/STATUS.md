# Status

[EXECUTED] Core API and CLI implemented. Toy, candidate-N reduced-dimension,
and full repaired-dimension executions passed encode, designated read, signed
combination and exact window expiry. The full run completed in 265.74 seconds
at 2.038 GiB peak RSS: one setup, three fresh inputs and 112 matching designated
reads. Source hashes stayed unchanged during each run.
No private data or raw ciphertext is written; reports preserve source hashes,
timings, sample counts and parameter distinctions. Frozen predecessor packages
are not edited. Root owns shared ledgers and commits.

[EXECUTED] Full key generation/publication took 172.53 seconds, of which
146.71 seconds were Gaussian sampling. Each fresh encode took 10.49–12.83
seconds, with 7.24–8.92 seconds spent sampling errors. All 19,922,944 Gaussian
coefficients in that run used the accelerated finite threshold law; zero
natural cap fallbacks occurred. No security certification follows from these
functional runs.
