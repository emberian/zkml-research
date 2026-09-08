# Ring hardness filter and coupled finite repair

[EXECUTED/DERIVED, 2026-09-08] The frozen N=4096 ring parameter point
fails the tested generic lattice cost models. The coupled N=16384 point
has substantially higher modeled costs, with larger ciphertext and key
sizes. These are generic structured-ring proxy heuristics, not a proof of
Ring-LWE hardness or a concrete post-quantum security level. The earlier
conditional mathematical proof is unchanged.

## 1. Exact declared run and model scope

[SOURCE/EXECUTED] `MODEL_AND_GRID.md` was written and `GRID.json` computed
before any estimator entry. Root authorized exactly the declared 24 calls:
two points, three paths, four cost models, with a 45-second cap per entry.
All 24 completed. There were zero preflight failures, exceptions, timeouts,
Infinity results, implicit retries or extra grid points. All raw entries
and complete cost dictionaries are retained in `estimates.jsonl`; runtime
and source provenance are in `estimates.manifest.json` and the logs.

[EXECUTED] The same archived estimator commit
`53da5982597709ba0fdf94ea37a84d822310fd84` and Sage 10.8 installation
used by the prior scalar audit were reused without modification. All 27
pinned source hashes match before and after the run. The driver used local
cache paths, disabled bytecode writes, and performed no package install,
key/ciphertext/Gaussian sampling, lattice reduction or attack execution.
The sum of recorded estimator calculation times is about 58.3 seconds;
this is not attack latency.

[DERIVED exact input] Both points use the certified split prime
`q=4294967767·2^256+1`, 64 independent uniform ring samples, a single
uniform ring secret, and coefficient errors of mass `exp(-πe²/1024²)`.
The raw scalar dimension proxy is `n=N,m=64N`; the Gaussian input is
`DiscreteGaussianAlpha(QQ(1024)/q,q)`, whose standard-deviation parameter
is approximately 408.5. `1024/q` lies between `2^-279` and `2^-278`.
Neither the key Gaussian nor scalar flood is the Ring-LWE error law.

[DERIVED normal-form justification] `MODEL_AND_GRID.md` §2 proves the
ring transformation conditional on the first sample multiplier being a
unit. The exceptional probability is at most `N/q`; a conservative gap
comparison costs `2N/q`. The transformation spends one ring sample and
makes its independent Gaussian error the new secret. Consequently the
explicit normalized estimator inputs have `n=N,m=63N`: 258,048 scalar
coordinates at N=4096 and 1,032,192 at N=16384. The driver checks Gaussian
type, coordinate mean/standard deviation, and each vector dimension.
All three paths, including the public dual wrapper, receive that normalized
input. No raw-dual result is used.

[HYPOTHESIS structured geometry] Normal form preserves the negacyclic
matrix blocks; it does not produce an independent scalar LWE matrix. The
estimator uses generic lattice shapes, Gaussian-heuristic success rules
and reduction-cost models as proxies for those structured lattices. This
extra modeling step is unproved for the exact ring/modulus/sample family.
Primal uSVP and BDD use GSA. The dual path uses its named generic length
and distinguishing model. The complete scope and pinned source locations
are in `MODEL_AND_GRID.md` §§1–3.

## 2. The baseline fails the named cost filter

[EXECUTED] Minima over {uSVP, BDD, normalized dual} for the exact N=4096
point are:

| named model | minimum log2 modeled cost | path | block size |
|---|---:|---|---:|
| MATZOV classical | 51.944007 | BDD | 60 |
| ADPS16 classical | 17.812000 | uSVP | 61 |
| ADPS16 quantum core-SVP | 16.165000 | uSVP | 61 |
| MATZOV quantum depth×width | 55.750336 | BDD | 60 |

[DERIVED] This point does not support a 128-cost claim in these models
and should not be selected for cryptographic implementation. The low core-
SVP numbers omit substantial costs; they are not full attack wall times.
The finite-cost MATZOV outputs independently remain far below that target.
Here the optimizer returns block sizes 60–61, above its floor of 40, so
the conclusion is not merely an unpriced floor result.

[DERIVED] This finding changes the parameter recommendation, not the
frozen conditional algebra. Its small setup/privacy statistical error
never bounded its exact computational premise.

## 3. Coupled N=16384 point and its modeled costs

[EXECUTED] The second point keeps `w=64,q,σe=1024`, and the complete
plaintext/recipient/window fixture fixed. It changes `N` from 4096 to
16384, `σK` from `2^24` to `2^25`, and `F` from `2^244` to `2^247`.
Both the new order-`2N` root and all joint finite inequalities pass in
`GRID.json`. The larger secret dimension is 16,384, not its 1,048,576
raw scalar error coordinates.

[EXECUTED] Minima for this exact point are:

| named model | minimum log2 modeled cost | path | block size |
|---|---:|---|---:|
| MATZOV classical | 211.909745 | BDD | 629 |
| ADPS16 classical | 184.252000 | uSVP | 631 |
| ADPS16 quantum core-SVP | 167.215000 | uSVP | 631 |
| MATZOV quantum depth×width | 199.731572 | BDD | 629 |

[EXECUTED] The normalized-dual costs are respectively 213.429623,
184.544000, 167.480000 and 201.430075. None beats the corresponding
primal minimum. The selected block sizes across all 12 larger-point
entries are 629–632, within the pinned MATZOV fit's stated limit of 1024.
Every dictionary, optimized lattice dimension and model label is retained.

[DERIVED] This is evidence that the coupled point passes the declared
generic cost filter. It is not evidence that all structured-ring, ideal,
subfield, algebraic, hybrid or future attacks cost that much. No alternative
shape model was run and no generic-to-ring success theorem is supplied.
The field's explicit splitting and large power-of-two divisor of `q-1`
have not been assigned any computational security benefit.

## 4. The statistical and physical price remains coupled

[DERIVED/EXECUTED] With `BK=8σK`, `BE=8σe`, the larger degree changes
`C=wN·BK·BE` from `2^58` to `2^61`; the eightfold flood increase
preserves the scalar-smudging bound. The raised-power smoothing inequalities
and the exact rank/short-vector estimates hold for both setup and augmented
masking. All 17 fixed coalition sizes have ideal non-LWE privacy terms
below `2^-168`. Correctness tail bounds are below `2^-203` and `2^-200`
for the baseline and larger degree, respectively. The exact integer
decoder inequalities hold with the unchanged prime and denominator.

[EXECUTED] At the larger degree the bit-packed arithmetic is:

| quantity | count or bytes |
|---|---:|
| ciphertext coefficients | 1,049,153 |
| ciphertext bytes | 37,900,653 |
| public A+P bytes | 379,389,952 |
| one recipient row bytes, strict tail event | 3,801,088 |
| all 16 recipient rows bytes, same event | 60,817,408 |
| fresh encryption full ring products, degree 16,384 | 64 |
| fresh encryption scalar coefficient products | 9,453,568 |
| fresh encryption Gaussian coefficients | 1,048,576 |
| recipient read coefficient products | 1,048,576 |
| one add/subtract residue operations | 1,049,153 |

[DERIVED] The key count uses 29 signed bits on the strict coefficient-tail
event. Ciphertext/public residues use 289 bits. These ideal representations
exclude metadata and allocation/NTT workspace, and do not predict latency.
The degree change also changes the cost of each ring product; a constant
ring-product count is not a constant execution cost.

## 5. What this audit does and does not close

[DERIVED] The immediate computational plausibility issue is resolved at
the scope of the declared filter: reject the original small ring point,
retain the fully coupled larger point as a conditional candidate for further
review. The exact unit-conditioned normal-form argument closes the sample-
count/secret-distribution map; the generic structured-lattice geometry and
attack coverage remain modeling assumptions.

[OPEN] Finite sampler/cutoff errors, strict bounded-QPT resources, the
matching quantum-advice class, and a theorem mapping dual/canonical Ring-LWE
with discrete errors to this exact finite sample law remain open. Exact
unbounded-support sampling in an ideal proof is not a bounded-QPT
implementation. The ideal ledger `768ε_RLWE+2^-168` is still conditional.
No estimator output supplies its required advantage-versus-work curve.
Subtracting `log2(768)` from a fixed-success cost is not a security theorem.

[OPEN] Independent review of the frozen map, arithmetic and recorded run
is requested from the assigned review lane; no duplicate estimator run is
needed. Application semantic nonvacuity, retained per-input read capability,
private encryption coins and bounded scalar-window closure remain exactly
as scoped by the frozen construction.

[EXECUTED meter] This hardness continuation used zero new web searches,
zero Scry SQL/schema calls, zero PDF downloads, one Sage process and exactly
24 estimator entries. It generated no cryptographic state, Gaussian draw,
lattice basis, attack or implementation timing. All sources were the
existing local paper/extract and pinned estimator artifacts. No literature
absence claim is made.
