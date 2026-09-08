# Faster executable ring prototype

[DERIVED implementation] This successor preserves the baseline ring
algorithms, parameters, public-input fixtures and Gaussian output law while
replacing two measured bottlenecks. `sampling/proposal_screen.c` performs
sequential integer proposal screening over OS random bytes, returning to
the exact baseline Python threshold routine only for a gray decision.
`RecipientBatch` extracts each ciphertext's coefficients once and performs
all supplied recipients' signed products with an exact FLINT integer matrix.
No floating Gaussian, approximate polynomial product or replacement PRNG is
used. The sibling `../ring_implementation/` remains the immutable baseline.

[EXECUTED] The matched full repaired workload took **117.13 seconds versus
265.74 seconds** for the baseline, a **2.27 x overall speedup**. Mean encode
time dropped from **11.43 to 7.18 seconds**; all-16-recipient read time dropped
from **6.47 to 1.50 seconds**. Peak RSS rose **8.8%**, to **2.217 GiB**.
See `REPORT.md` and `results/COMPARISON.json`: one setup, three encodes, 48 fresh designated reads,
48 live-window reads and 16 signed-combination reads. Setup timing includes
the new one-time private recipient-matrix preparation. The comparison is
between saved single runs on the same shared machine, not a controlled
benchmark distribution.

## Run and reuse

[EXECUTED environment] The measured run reuses the baseline's isolated
Python 3.14 / python-flint 0.9.0 environment. A C compiler builds the small
screening library into ignored `sampling/_build/` on first use. The run
records the reproducible rebuild command, compiled library hash and source
hashes. The first auto-build used a transient output filename before atomic
rename; that filename was not logged.

```sh
cd research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_implementation_fast
../ring_implementation/.venv/bin/python -B run.py --profile toy --inputs 5 --output results/local_toy.json
../ring_implementation/.venv/bin/python -B run.py --profile candidate_full --inputs 3 --output results/local_full.json
```

[DERIVED] Alternatively create an independent `.venv` and install
`requirements.txt`, then use its Python. Public setup, registration,
encoding, `combine` and `Window` have the same API as the baseline.
Independent recipients can continue calling `public.decode(key, ciphertext)`.
A caller already holding a specified set of recipient keys can prepare:

```python
from ring import RecipientBatch
readers = RecipientBatch(public, keys)
scores = readers.decode(ciphertext)
```

[DERIVED credentials] The cache is private: it contains copies of exactly
the supplied actual recipient rows. It does not create absent-recipient rows
or expand the supplied keys' linear span. The public setup object retains no
private rows. A single-process all-recipient benchmark does not establish a
multi-process private execution boundary.

[DERIVED exact decoding] For each `c0` polynomial with coefficients `b`,
the shared vector block is `[b0,-b_(N-1),...,-b1]`. Multiplying the flattened
integer secret rows by this vector gives exactly the original negacyclic
constant products. The resulting phases use the unchanged exact nearest
`Delta*t mod q` decoder. Matrix preparation time and extra memory count in
the full measurements.

[SOURCE/DERIVED sampling] `sampling/reference.py` is byte-identical to the
frozen baseline sampler. The native screen uses only integer operations;
it preserves proposal order, carries the rejection-attempt counter across
buffers, and pauses before resolving each gray event. Python applies the
same exact threshold, rare suffix decision and 4096-attempt zero fallback.
See `sampling/DESIGN.md` for the implementation contract and measured
sampling-only speedups.

[OPEN] This remains variable-time research code using OS random bytes.
Uniform residues still use expected-time rejection. Packing, authenticated
transport, secure memory, constant-time execution, Ring-LWE hardness and
computational security are not certified. The full run executes three inputs,
not the theorem's 384-input workload. Exact arithmetic success and a speedup
do not resolve these separate assumptions. No private coefficients, keys,
coins, input vectors or ciphertexts are written by the runner.
