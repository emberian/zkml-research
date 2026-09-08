# Finite parameter certificate results

[EXECUTED, 2026-09-08] Command:
`python3 research/learn_infer_only/experiments/adversarial_review/public_setup_pq/finite_reduction/check_parameters.py`.
Exit 0. Exact integer/rational checks classify all three original profiles
as not certified by this conservative finite reduction, and both adjusted
profiles as passing. All ten original/adjusted regularity checks also pass.
Inputs, outputs and source hashes are in `INPUTS.json` and `RESULTS.json`.
No key, ciphertext, Gaussian sample, cryptographic primitive or estimator ran.

[DERIVED/EXECUTED] All rows use `p=28,439,893`, `d=577`, `r=16`, `T=384`.
The prime and original public parameter rows are copied from the pinned
construction-author cost report. The two passing rows are:

| Parameter | Finite 1024 | Finite 4096 |
|---|---:|---:|
| `n` | 1024 | 4096 |
| LWE secret dimension `n-d` | 447 | 3519 |
| `M=L` | `2^20` | `2^23` |
| `m=M+L` | `2^21` | `2^24` |
| `q` | `p^13` | `p^15` |
| modulus bit length | 322 | 372 |
| `σ1` | `2^20` | `2^24` |
| `σ2` | `2^83` | `2^98` |
| certified analysis width `ξ` | `2^153` | `2^178` |
| encryption error width `αq` | `2^172` | `2^192` |
| assumed LWE error width `βq=αq/(2ξ)` | `2^18` | `2^13` |

[DERIVED] These satisfy the exact certificate of `FINITE_THEOREM.md` §5
at `κ=160`. For the 1024 row, the encryption/setup parameters are unchanged
from the author's original fixed-coordinate cost row; only the analytical
`ξ` and the corresponding LWE assumption differ. The 4096 row doubles
`M` and the dominant public/key/ciphertext dimensions. It is a new parameter
row and requires its own correctness and cost calculation.

[EXECUTED original-row failures] The original 1024 fixed-coordinate row has
`ξ=2^100`, below this proof's sufficient `2^153`. The original 4096 row
has `ξ=2^120`, below this proof's sufficient `2^177` at its original
row count, and `M=4,194,304` fails the explicit strict requirement
`M>4,423,680`. Doubling `M` yields the passing `ξ=2^178` row above.
The original full-source normalization also fails the row count and this
proof's operator-norm certificate. Its `M=268,435,456` is below the
required strict floor `520,765,440`, and its `ξ=2^33964` is below this
proof's sufficient `2^50953` at the original row count.

[DERIVED scope of failure] These are failures of this sufficient certificate,
not lower bounds on necessary parameters or refutations of ALS's asymptotic
theorem. In particular, a sharper analysis of the gadget could lower `ξ`.
The effect of smaller base LWE noise on actual computational hardness is
not evaluated here.

[DERIVED/EXECUTED finite ledger] For the exact scheme distributions and
assuming a reduction sampler whose full output tuple has per-world
discrepancy at most `2^-160`, §5 gives

```text
j=0:  Adv_public ≤ 768 εLWE + 1,803,144 · 2^-160,
j=16: Adv_public ≤ 768 εLWE + 1,753,992 · 2^-160.
```

[DERIVED] Both displayed statistical terms are below `2^-139`. They include
setup and augmented regularity, first-errorless rank failure, gadget quality,
Gaussian-image error, gadget tail abort, both Gaussian-conversion errors,
and the explicitly assumed sampler-accuracy budget. They do not bound
`εLWE`. They also do not include the separate correctness-failure event or
any approximation in the scheme's own sampling implementation.

[OPEN] The ideal distribution theorem is finite. A finite-bit implementation
of its reduction samplers, with the stated tuple-level discrepancy and a
resource bound, has not been certified here. Thus the number `2^-139` is a
conditional statistical ledger, not a certified security level. The root
can integrate this precise boundary without importing hidden constant-one
normalizations.
