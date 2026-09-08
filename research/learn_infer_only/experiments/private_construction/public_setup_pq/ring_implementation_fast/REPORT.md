# Measured successor: native Gaussian screening and shared decoding

[EXECUTED] The same full repaired workload now finishes in **117.129 seconds**,
down from **265.738 seconds**, a **2.27 x** overall speedup. It uses identical
N=16384, w=64, d=577, r=16 parameters and public synthetic fixture rules, with
independent fresh OS randomness. All 112 designated reads matched, including
signed combinations and exact window expiry. This is one matched successor
run; no extra full cryptographic run or estimator invocation was performed.

| Measured quantity | Baseline | Successor | Baseline/successor |
|---|---:|---:|---:|
| Total workload |265.738 s|117.129 s|2.27 x|
| Setup, including table and new private cache |184.896 s|82.587 s|2.24 x|
| Recipient key generation/publication |172.527 s|62.651 s|2.75 x|
| Key Gaussian sampling |146.712 s|24.664 s|5.95 x|
| Three inputs' error sampling |23.758 s|4.184 s|5.68 x|
| Mean fresh encode |11.434 s|7.181 s|1.59 x|
| Mean all-16-recipient fresh decode |6.474 s|1.498 s|4.32 x|
| Mean window update |0.120 s|0.118 s|1.02 x|
| Peak process RSS |2.038 GiB|2.217 GiB|successor +8.8%|

[EXECUTED provenance] `results/candidate_full_fast_001.json` records exact
parameters, source hashes, native library hash/rebuild command, all timings and
sampler counters. `results/COMPARISON.json` is produced by `compare.py` from
that report and the unchanged baseline `candidate_full_001.json`. It checks
identical parameters, three inputs, 16 actual recipient rows, zero absent rows,
19, 922, 944 Gaussian coefficients and 112 matching reads. Both reports say
PASS and their runtime sources stayed unchanged during execution.

```sh
../ring_implementation/.venv/bin/python -B run.py --profile candidate_full --inputs 3 --output results/candidate_full_fast_001.json > results/candidate_full_fast_001.log 2> results/candidate_full_fast_001.stderr.log
../ring_implementation/.venv/bin/python -B compare.py > results/COMPARISON.log
```

[EXECUTED scope] These are saved single runs on a shared machine. The
successor did not improve every unchanged component's wall time: public A
generation took 3.579 s versus 1.112 s, and directly uniform missing public rows
took 13.546 s versus 10.994 s. We report the observed overall improvement without
treating these runs as a controlled performance distribution. No repeated
full run was used to select a favorable result.

## Actual changes

[DERIVED implementation] The native C loop parses OS-byte buffers, performs
integer Gaussian squeeze decisions and retains the sequential attempt count.
It pauses at a gray proposal; Python runs the exact unchanged threshold
routine and any required independent suffix draw, then resumes. The
4096-proposal cap and zero fallback are unchanged. `sampling/reference.py`
is byte-identical to the frozen baseline sampler. There is no float Gaussian
substitution, seeded noncryptographic PRNG or approximate acceptance rule.

[EXECUTED] The integrated full run sampled 16, 777, 216 key and 3, 145, 728 error
coefficients. It processed318, 814, 415 proposals through 84, 056 native calls;
77, 765 proposals needed exact Python threshold evaluation. Zero natural cap
fallbacks occurred. Gaussian calls requested 2, 452, 540, 480 OS random bytes.
The sampler's separate contemporaneous million-coefficient comparisons found
10.28 x error-width and 7.23 x key-width speedups; the table above uses the
larger integrated run's actual timings instead.

[DERIVED implementation] `RecipientBatch` prepares an exact FLINT integer
matrix from only the supplied actual recipient keys. For every ciphertext
it extracts each public c0 coefficient block once, transforms it to
`[b0,-b_(N-1),...,-b1]`, and multiplies by that private matrix. The phases and
nearest actual-Delta codepoint decoder are unchanged. Matrix preparation
cost 2.337 s and its memory are included. The independent one-recipient API
remains available; this cache is optional and private to a caller already
holding those keys. It neither creates missing rows nor expands their span.

[EXECUTED] The integrated toy compares batch outputs directly against the
unchanged single-recipient decoder. The full run exercises three encodes,
all recipients, exact expiry and a signed 2*c0-c1 combination; each returned
the expected transformed integer lift. The initial shared-decoder smoke
report retains an earlier runner hash; `integrated_toy_001` and the full
report pin the final runtime sources.

## Boundaries and next cost

[SOURCE/EXECUTED] Native compilation uses `/usr/bin/cc`, C11 and optimization
level 3. The stored `build_command` is a reproducible rebuild command. The
initial auto-build used the same compiler/source/flags with a temporary
output name before atomic rename; that temporary filename was not logged.
The generated library's hash is in the run; `_build` is ignored and contains
no secret data. The original baseline and prior mathematical packages are
unchanged.

[INFERRED] Sampling is no longer the dominant fraction of fresh encoding:
the three encodes spent1.32–1.50 s sampling errors and 5.53–6.03 s elsewhere.
Recipient key generation/publication took 62.65 s, of which24.66 s was sampling.
Exact multiplication and uniform-residue generation are concrete next
optimization targets. Neither improvement is claimed here.

[OPEN] Variable-time behavior, OS-generator assumptions, expected-time uniform
rejection, secure memory, packing, authenticated transport and computational
security remain outside the executed claim. The prototype still implements
fixed-coordinate scalar-window closure, not arbitrary nonlinear encrypted
computation. It ran three fresh inputs, not 384. No private samples, keys,
coins, input vectors or raw ciphertexts were persisted.
