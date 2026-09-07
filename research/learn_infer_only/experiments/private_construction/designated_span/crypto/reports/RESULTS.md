# Positive designated-recipient backend result

[EXECUTED] `python3 .../designated_span/crypto/positive_driver.py` completed
33 fresh signed-577 input encryptions and Learn transitions with a 32-item
window. The four predeclared reads were row 0 before any admission, row 7 after
one admission, row 8 after 32, and row 15 after 33. All four recipient results
matched the separately calculated private integers. These comprise one known
zero-state control and three nonempty encrypted reads. Admission 33 expired
the exact original ciphertext from admission 1. Repeating that final public
transition with the same immutable inputs produced identical state bytes.

[EXECUTED] The complete run took 252.419228667 seconds on the recorded shared
machine. Its retained evidence is [`positive_001/report.json`](positive_001/report.json),
SHA256 `6c5fdf598bfcef1c199c77ba515dc39c1f8b93b7efba4791187463b4338439f5`,
the predeclared inputs/query schedule, source hashes, full public command log,
and successful full context-validation result in that directory. No private
vector, score, key, private-key/input hash or per-recipient decode timing is
included in those public reports. Runtime private files are ignored by Git.
The aggregate benchmark wall time includes all roles; it is not a claim about
a timing-free cryptographic observation model.

[EXECUTED] The final runtime source is `crypto.py`, SHA256
`d7dfc2f46044ea438e1de548b6f922720cf36418b02bc02dac095cbc5851adb0`,
with three pinned local dependencies (`group.py`, `native_pow.py`, `rows.json`).
An immutable copy under `runtime/positive_001/source/` was executed. The
separate read-only `validate_positive.py` also passed. It reconstructs each
private window by coordinates before taking the dot product, checks the four
retained recipient answers, output identities and randomizer bytes, exact
public replay, final key inventory/modes, source pins, and public log omissions.
It invokes no adversarial, malformed-input, routing or extraction experiment.

## Costs and byte counts

[EXECUTED] These are actual subprocess wall times in this run, including
startup, context loading, validation, file reads and writes. Different roles
share a machine; the figures are not isolated microbenchmarks or statistical
speedup estimates. Recipient decode timings remain in private records.

| Public/setup operation | Calls | Total seconds | Mean seconds |
| --- | ---: | ---: | ---: |
| Fresh setup, including 33 private child processes | 1 | 130.583937125 | 130.583937125 |
| Full public context validation | 1 | 3.514038500 | 3.514038500 |
| Issuer encryption, validated context reused | 33 | 35.727445667 | 1.082649869 |
| Public Learn, including one exact replay | 34 | 72.980524126 | 2.146486004 |
| Public fixed-row Infer | 4 | 4.791469582 | 1.197867396 |
| Recipient-output inspection | 4 | 0.329997500 | 0.082499375 |

[EXECUTED] Four cached query encodings took 81.450–84.171 ms each; a separate
uncached encoding of the same row-0 query took 3560.802 ms and returned exactly
the same bytes. Full context validation checks 593 subgroup elements and all
16 token equations, making 9209 native exponent calls for these fixed rows.
Each cached call still reads, hashes, strictly parses, range-checks and checks
the identities of the complete context. Ciphertext subgroup checks always run.

[EXECUTED] The complete setup (parent plus child counts) made 166394 native
exponent calls, 19313 subgroup checks and 272 token-row checks across 17 full
context validations. Its parent-only counters in the command log intentionally
exclude child counters; all 33 child summaries are preserved separately.
There were 16 final dedicated recipient files and no remaining projection
delivery or pending-scalar files. Final keys are mode 0600 in a mode 0700
directory. The source holds the master only in the initializer child and
never serializes it. Physical erasure is not verified.

[EXECUTED/DERIVED] Each state is 148147 bytes; each recipient output is 691
bytes; each private dedicated scalar envelope is 435 bytes. The public context
is 342331 bytes. A full 32-ciphertext queue plus its accumulator occupies
4888851 bytes of ciphertext envelopes, excluding paths, journal/database
metadata, retained history and public context. These are the actual sizes in
the run and agree with the exact 179-byte envelope/header construction.

## Preserved uncached first path

[EXECUTED] Before validation reuse was added, an independent first setup,
fresh random input, Learn, row-0 transformation and recipient decode also
passed the exact private integer comparison. Evidence is
[`first_full_validation.json`](first_full_validation.json) and its byte-identical
runtime source snapshot under `full_validation_source/`. The first source
hash is `6455474e1af495fcd4097acc214e11ea667b4113712bbe2c3822290e8c50e14d`.
Process-work times were setup 107.797135792 s, query encoding 3.331591834 s,
encryption 4.316510458 s, Learn 5.271033959 s and Infer 4.424714500 s. These
exclude Python startup and differ from the later whole-invocation timing
measure; neither run is a paired performance trial.

## Reproduction and limits

```sh
python3 research/learn_infer_only/experiments/private_construction/designated_span/crypto/positive_driver.py \
  --runtime research/learn_infer_only/experiments/private_construction/designated_span/crypto/runtime/positive_002 \
  --reports research/learn_infer_only/experiments/private_construction/designated_span/crypto/reports/positive_002
python3 research/learn_infer_only/experiments/private_construction/designated_span/crypto/validate_positive.py \
  --runtime research/learn_infer_only/experiments/private_construction/designated_span/crypto/runtime/positive_002 \
  --reports research/learn_infer_only/experiments/private_construction/designated_span/crypto/reports/positive_002
```

[DERIVED] Reproduction uses fresh OS-backed randomness, so public ciphertext
and context hashes differ. It preserves the dimensions, operations, declared
read schedule, exact arithmetic comparisons and source/dependency checks.
The measured native library is OpenSSL 3.6.4 (25 Aug 2026); its resolved dylib
hash and interpreter/platform are pinned in the reports. No package download,
model rerun, training, web search or metered search was used.

[DERIVED scope] This is classical fixed-span DDH arithmetic with dedicated
recipient credentials, trusted private setup and issuer inputs, and same-account
process separation. It tests fresh synthetic vectors, not utility accuracy or
ambiguity of actual text-encoder outputs. A scalar recipient can still compute
its projection outside its local journal gate, including on retained old input
ciphertexts. Host-only privacy excludes recipient feedback. Fixed-span coalition
limits, correlated dedicated keys, nonconstant-time execution, honest erasure,
source authenticity, query policy and independent continuity assumptions remain
as described in the reviewed contract and backend README. The sibling journal
integration is separate evidence; this suite does not establish it.
