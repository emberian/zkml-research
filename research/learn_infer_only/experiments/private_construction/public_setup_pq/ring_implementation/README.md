# Executable fixed-coordinate ring prototype

[EXECUTED] This package implements actual public setup, recipient-local key
generation, encoding, signed updates, exact window expiry and designated
decoding. It runs synthetic inputs in memory and writes timing/count reports.
It does not store recipient keys, input vectors, encryption coins or ciphertexts.
The full repaired-point run passed in **265.74 seconds**, peaking at
**2.038 GiB RSS**. Setup took **184.63 seconds**; its three encodes took
**12.83, 10.49 and 10.98 seconds**. All 112 designated reads matched across
fresh inputs, live windows and a signed combination. See `REPORT.md` and
`results/candidate_full_001.json`; smaller probes are identified separately.

[DERIVED implementation] `ring.py` uses FLINT arbitrary-precision modular
polynomials for exact multiplication in `Z_q[T]/(T^N+1)`. Products reduce as
`product.truncate(N) - product.right_shift(N)`. Scalar second components use
the signed dot product `a[0]*b[0] - sum(a[k]*b[N-k], k=1..N-1)`.
No floating FFT approximation enters ring arithmetic.

[DERIVED credentials] `generate_recipient_key` returns a private row and a
public product. `PublicSetup.register_public` receives only that product.
`PublicSetup.finish` draws absent recipients' public polynomials directly
uniformly; it never creates their private rows. The runner simulates the
recipients as distinct objects in one process. It is not a claim of process
isolation, secure memory erasure, authenticated registration or malicious
recipient security.

[DERIVED input/closure] The sample policy is a sparse invertible basis
`B=I+C`, where `C` has entries only in the first recipient rows and later
columns. Thus `C²=0` and `B^-1=I-C`. All input coordinates survive. Each
designated row combines its original coordinate with later coordinates using
public coefficients 2 and 3 when available. Encoding accepts the complete
`F_p^d` vector. Decoding finds the closest **actual** `Delta*t mod q`
codepoint in the declared integer interval; it does not substitute `D*v/q`.

[DERIVED updates] `combine` accepts signed coefficients and rejects an L1
budget above `W`. `Window` retains original ciphertexts, subtracts the exact
outgoing ciphertext, and tracks the live queue norm. The runner checks the
expired state against a separately rebuilt sum coefficient-for-coefficient.
This is scalar linear closure; arbitrary matrix changes and nonlinear
encrypted computation are not implemented.

## Run

[EXECUTED environment] The isolated environment uses Python 3.14,
python-flint 0.9.0 and NumPy 2.5.3. NumPy is available for sampler development;
the production ring and Gaussian sampler paths use Python integers and FLINT.

```sh
cd research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_implementation
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
.venv/bin/python -B run.py --profile toy --inputs 5 --output results/local_toy.json
.venv/bin/python -B run.py --profile candidate_n_probe --inputs 3 --output results/local_probe.json
.venv/bin/python -B run.py --profile candidate_full --inputs 3 --output results/local_full.json
```

[DERIVED API] The same operations are reusable independently of the runner:

```python
from ring import PublicSetup, Window, generate_recipient_key
from run import params
from sampling.sampler import GaussianSampler

p = params("toy")
sampler = GaussianSampler()
public = PublicSetup(p, sampler)
keys = []                       # recipient-local objects in this example
for i in range(p.recipients):
    key, product = generate_recipient_key(p, public.A, i, sampler)
    public.register_public(i, product)
    keys.append(key)
public.finish()

ciphertext = public.encode(list(range(p.d)))
score = public.decode(keys[0], ciphertext)
combined = public.combine([(2, ciphertext)])
twice_score = public.decode(keys[0], combined)
window = Window(public, capacity=2)
window.push(ciphertext)
```

## Profiles and interpretation

| Profile | N | w | d | recipients | Purpose |
|---|---:|---:|---:|---:|---|
| `toy` | 64 | 4 | 9 | 2 | Small complete execution, 31-bit modulus |
| `candidate_n_probe` | 16,384 | 8 | 33 | 2 | Candidate ring dimension/modulus/widths, reduced other dimensions |
| `candidate_full` | 16,384 | 64 | 577 | 16 | All repaired candidate dimensions |

[SOURCE] The full profile is copied from the frozen
`../ring_candidate/hardness/GRID.json`, point `ring_joint_repair_16384`:
`q = 4294967767 * 2^256 + 1`, `p=28439893`, `sigma_K=2^25`,
`sigma_e=2^10`, `F=2^247`, `W=32`, `D=8204908842`. The prototype
checks the deterministic cutoff correctness inequality. The prior exact
prime/splitting and statistical certificates remain in their frozen package.
Three fresh encryptions do not execute its 384-input workload.

[SOURCE/DERIVED sampler] `sampling/sampler.py` implements the frozen finite
Gaussian threshold law with an integer squeeze table and adaptive random-bit
prefixes. Width means mass proportional to `exp(-pi*k*k/sigma**2)`, not
standard deviation. Its output support is `|k|<8*sigma`; the 4096-proposal cap
returns zero. See `sampling/DESIGN.md` for the exact equivalence argument,
measurements and entropy convention. This is variable-time research code,
with OS random bytes as the implementation's entropy source. The separate
uniform-modulus sampler uses ordinary rejection with expected-time termination;
the complete prototype therefore does not instantiate every strict bounded-time
reduction resource bound in the frozen finite-sampler theorem.

[OPEN] Successful arithmetic and decoding do not establish Ring-LWE hardness,
the structured lattice/GSA model, computational security, constant-time
behavior, secure seed expansion, authenticated ciphertexts, serialization or
a deployed recipient transport. Packed byte counts in reports are mathematical
storage targets; this implementation stores Python/FLINT objects in RAM and
does not implement that packed format. Actual process peak RSS and elapsed
times are measured separately. The original ring/hardness/finite-sampler
packages are unchanged.

[SOURCE] Library interfaces inspected in the official
[python-flint documentation](https://python-flint.readthedocs.io/en/latest/fmpz_mod_poly.html)
and [python-flint repository](https://github.com/flintlib/python-flint).
This construction lane used one targeted primary web search, zero Scry queries,
zero estimator calls and zero eprint downloads.
