# Pinned estimator audit for the executed BFV window

[EXECUTED, 2026-09-06] This follow-up estimates specified generic-LWE attack
costs using the exact BFV modulus and CBD parameter tuple. It does not prove
BFV confidentiality, rule out attacks exploiting ring structure, or close
the resident's surviving-read-key and protected-release gaps. The bounded
runs are complete; errors and timeouts remain explicit in the JSONL files.

## Environment and reproducibility

[SOURCE: official install instructions] Sage supports conda-forge binaries
on Apple Silicon. Its feedstock describes `sagelib` as the minimal Python
package sufficient for `import sage.all`; `sage` adds the full distribution.
Sources: [Sage installation guide](https://doc.sagemath.org/html/en/installation/conda.html),
[conda-forge feedstock](https://github.com/conda-forge/sage-feedstock).
Micromamba's documented manual macOS ARM archive was downloaded, without
shell initialization or a global package installation:
[Micromamba installation](https://mamba.readthedocs.io/en/latest/installation/micromamba-installation.html).

[EXECUTED] Micromamba 2.9.0; sagelib 10.8; Python 3.12; SciPy 1.18.0.
The initial minimal solve required 155 binary packages / 430463184 download
bytes; SciPy added one approximately 14 MB package. Full Sage's 1184644502-
byte solve was inspected but not installed. Maxima 5.49.0 later added one
31963559-byte binary package for coded BKW. Setup and successful initial
estimates fit within ten minutes. Runtime packages reside in this
directory's ignored `runtime/`; the final 157-package URL/hash lock is
`environment-final-explicit.txt`, with JSON provenance alongside it.

[EXECUTED failure and repair] Directly running the environment's Python
failed because Singular was absent from PATH; `micromamba run --prefix …`
activates the package environment correctly. The first estimator import
then exposed missing SciPy; adding its binary package fixed that. BKW's
later missing-Maxima error was likewise resolved by its binary package. Failed
logs remain (`import_probe*`, `first_pass_activated*`). No estimate was
extracted from failed invocations. `import_activated.log` checks Sage 10.8
and factors the executed Q83 product into the two recorded primes.

[EXECUTED pin] Estimator commit
`53da5982597709ba0fdf94ea37a84d822310fd84` (2026-08-19) was copied using
`git archive` from the clean local `/Users/ember/src/lattice-estimator`.
The snapshot is private to this experiment, not edited. Source/archive
hashes are in `environment-final-provenance.json`. The script sets local
Sage/cache paths before its imports and disables Python bytecode writes.

```text
research/learn_infer_only/experiments/he_closure_costs/estimator/runtime/bin/micromamba --no-rc --root-prefix /Users/ember/dev/zkml-research/research/learn_infer_only/experiments/he_closure_costs/estimator/runtime/mamba run --prefix /Users/ember/dev/zkml-research/research/learn_infer_only/experiments/he_closure_costs/estimator/runtime/sage python research/learn_infer_only/experiments/he_closure_costs/estimator/run_estimates.py --seconds 180 --output first_pass_ready.jsonl
```

[EXECUTED] Each result file has a neighboring `.manifest.json` recording
its precise invocation, Sage/Python versions, distribution and model hash.
`wall_seconds_estimator_runtime_not_attack_latency` measures the estimator
software only. It is not an attack benchmark or hardware security metric.

## Distribution and sample model

[SOURCE / DERIVED] The library samples a difference of two 20-bit popcounts
at variance 10. The exact estimator input is **ND.CenteredBinomial(20)** for
both Xs and Xe: independent Bernoulli sums of length eta, bounds ±eta,
variance eta/2. Thus eta=20, not eta=10. No top-level ternary or Gaussian
distribution substitutes for this tuple. Pin:
[`nd.py:296–333`](https://github.com/malb/lattice-estimator/blob/53da5982597709ba0fdf94ea37a84d822310fd84/estimator/nd.py#L296).

[SOURCE: important approximation] That class sets `is_Gaussian_like=True`.
Its `support_size` uses the full support cardinality times a requested
fraction and carries a TODO questioning binomial accuracy. Primal geometry
uses moments and shape heuristics; the dual-hybrid entropy/advantage
expressions use standard deviation in Gaussian-shaped formulas, not the
exact binomial probability mass function (`lwe_dual.py:523–610`). BKW's
sample amplification replaces a sum distribution by a matched Gaussian
(`lwe_parameters.py:121–125`). Direct CBD input is not an exact-distribution
proof of every attack subroutine. `control_with_CBD.log` verifies the exact
41-point PMF binomial(40,20+x)/2^40 has mass 1, mean 0 and variance 10, and
reproduces the pinned README's Kyber512 default uSVP cost rounded to 143.8.

[DERIVED instance mapping] The BFV public key is one RLWE sample
`(a, -a*s+e)` with N=4096 and CBD variance-10 secret/error. Its coefficient
equations give 4096 scalar equations with a structured negacyclic matrix.
We run n=4096 with m=4096 as a **generic-LWE attack proxy**, and m=∞ as a
stronger-sample-access sensitivity. Treating the structured rows as generic
LWE is an attack-cost heuristic, not a reduction proving that ring-LWE is
at least as hard. uSVP returned the same chosen lattice dimension and cost
in the two sample modes. Other attack paths can differ. In particular, the
aliased MATZOV dual-hybrid routine defaults its lattice sample count to n
(`lwe_dual.py:582–583`); its caller never supplies m while optimizing other
parameters, and params.m only limits beta (`:641–676`). Its equal outputs
therefore do **not** establish optimization over the lattice sample count.

[SOURCE / DERIVED role accounting] The executed Q83 window has one public
encryption key, no rotations, no relinearization and no key-switch keys.
Fresh encryptions computed publicly from this key are not automatically
new independent raw RLWE public-key samples at the original error width.
The phase-noise bound for fresh public-key ciphertexts in `window_ledger.py`
is a correctness bound, not Xe for the public-key LWE instance. No
evaluation-key circular-security/KDM claim is established. Adding such keys
or a decryption/release oracle requires a new exposure audit. The test
reader actually retains the entire secret key and lies outside this
key-recovery attack instance; that role trivially reads the state.

## Explicit models and attack coverage

[SOURCE] The pinned defaults are MATZOV and GSA (`conf.py:14–16`). The
estimator README calls its bit-cost results heuristic estimates, and
distinguishes `.estimate.rough` from the full evaluator. We call individual
attacks with explicit arguments rather than inherit undocumented defaults.
Source: [pinned README](https://github.com/malb/lattice-estimator/blob/53da5982597709ba0fdf94ea37a84d822310fd84/README.rst).

| Label | Explicit reduction model | Meaning and limitation |
|---|---|---|
| MATZOV_classical | MATZOV(nn="list_decoding-classical") | Classical list-decoding cost, finite-dimensional model constants |
| ADPS16_classical | ADPS16(mode="classical") | Core-SVP cost 2^(0.292 beta); omits finite-cost detail present in MATZOV |
| ADPS16_quantum_core_svp | ADPS16(mode="quantum") | Core-SVP cost 2^(0.265 beta); a quantum reduction-cost model |
| MATZOV_quantum_depth_width | MATZOV(nn="list_decoding-dw") | Quantum list-decoding depth-times-width model; different units/assumptions from core-SVP |

[SOURCE] Constants and modes:
[`reduction.py:637–676`](https://github.com/malb/lattice-estimator/blob/53da5982597709ba0fdf94ea37a84d822310fd84/estimator/reduction.py#L637),
[`reduction.py:739–756`](https://github.com/malb/lattice-estimator/blob/53da5982597709ba0fdf94ea37a84d822310fd84/estimator/reduction.py#L739),
[`reduction.py:963–995`](https://github.com/malb/lattice-estimator/blob/53da5982597709ba0fdf94ea37a84d822310fd84/estimator/reduction.py#L963).
GSA is the assumed reduced-basis shape for all primal calls. Quantum model
substitution does **not** turn every guessing, FFT, memory access or other
part of an attack into an optimized quantum algorithm. A model's minimum
is not a lower bound against all possible quantum attacks.

[EXECUTED coverage] `first_pass_ready.jsonl` has uSVP and dual-hybrid
for both moduli, both sample modes and the first three reduction models.
`additional_attacks.jsonl` adds BDD, dual, primal hybrid and MITM hybrid.
`nonlattice_attacks.jsonl` tests coded BKW and Arora–GB once per tuple with
their own cost rules; their labels do not imply use of MATZOV reduction.
`quantum_depth_width.jsonl` tests uSVP, BDD, dual and dual-hybrid in the
fourth model. All **72 primary lattice calls completed**: six attacks,
three reduction models, two moduli and two sample modes. Every additional
exception/timeout is retained. Full `.estimate` wraps
Arora–GB with secret guessing; the direct call here is explicitly narrower.
No all-attacks security claim is permitted from these files.

## Results and interpretation

[EXECUTED] Minimum completed lattice-attack **log2 estimated costs**, not
proved security bits. The first three rows each cover all six named lattice
attacks. `summary.csv` and `summary.json` identify the attaining attack and
selected result file, with coverage counted by distinct attack names.

| Reduction model | Q83, m=4096 | Q83, m=∞ | Q109, m=4096 | Q109, m=∞ |
|---|---:|---:|---:|---:|
| MATZOV classical; BDD | 172.579637 | 172.566633 | 127.556093 | 127.557710 |
| ADPS16 classical; uSVP | 145.708 | 145.708 | 98.112 | 98.112 |
| ADPS16 quantum core-SVP; uSVP | 132.235 | 132.235 | 89.040 | 89.040 |
| MATZOV quantum depth×width; BDD; partial coverage | 164.224491 | 164.192891 | 123.749318 | 123.750660 |

[EXECUTED numerical qualification] All 16 listed minimum candidates
reproduced with exactly matching output floats in fresh Sage processes.
The slight Q109 m=∞ BDD cost increase is the routine's numerical search
output, not a theorem that additional samples strengthen LWE. An attacker
with more samples may reuse the finite-sample attack; these optimization
outputs are not rigorous lower bounds.

[EXECUTED unresolved numerical failure] The fourth model's original
dual-hybrid calls all raised `SignError` at `lwe_dual.py:607`. In separate
fresh processes, Q83/m4096 and both Q109 sample modes succeeded; Q83/m∞
still failed. The exact cause was not diagnosed and no estimator code was
changed. Isolated reruns remain separate from original coverage/history in
`summary.json`; their existence does not erase the failed calls. The three
successful dual-hybrid costs exceed the corresponding BDD costs.

[EXECUTED bounded nonlattice coverage] After installing Maxima, coded BKW
returned log2 cost **786.317809** for Q109 in both sample modes, with its
reported sample demand log2(m)=768.768128; Q83 calls timed out at 90 seconds.
The finite-sample path may synthesize samples with increased/approximated
noise; do not interpret its output m as independently supplied samples.
Arora–GB returned infinite cost for both m=4096 cases and timed out for
both m=∞ cases at 60 seconds. Infinite estimator output is not a proof of
attack impossibility. Old dependency errors remain as unsuccessful attempts.

[DERIVED] Q83 clears 128 in the selected ADPS16 quantum core-SVP proxy
while Q109 does not; that is a model-specific research improvement over
the previous distribution-mismatched table comparison. Ring-specific and
other unmodeled attacks, quantum-model limitations, release oracles and
future evaluation-key exposure remain outside this result. The smaller Q
also passed the separately pinned encrypted window and its conditional
correctness bound. No encrypted experiment was rerun here; no production
parameter recommendation or protection from the test reader follows.
