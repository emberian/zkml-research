# Resume

[EXECUTED] Read `DESIGN.md`, `MANIFEST.json`, and `MEASUREMENTS.json` first;
the latter records the run command and exact source hashes.

[DERIVED] The parent ring runtime can use `GaussianSampler` directly and
record its `last_stats` after each sample call. Keep actual outputs in
the parent's authorized private memory lifecycle, not these public ledgers.

[OPEN] Independently audit the interval-squeeze and lazy-prefix refinement;
assess side-channel discipline and the random-bit generator separately.
Whole-ring throughput must be measured by the ring implementation; do not
present sampler throughput as encryption/decryption throughput.
