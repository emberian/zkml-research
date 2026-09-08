# Actual nonlinear nine-to-four rescale proof

[EXECUTED] The first proof for a fixed batch from the real nonlinear text-kernel
operation passed. A separate process accepted the proof; the same proof was
rejected after changing the first public output digit. The proof covers **32
actual distinct coefficient positions and 128 output residue equations**, out of
24,576 component/coefficient positions in the degree8192 output ciphertext.
No padding or whole-ciphertext proof claim is involved.

The batch includes each of the three components at indices0,4095,4096,8191,
plus20 fixed positions listed in `selection.json`. Every selected position joins
all nine extended input residues and all four output residues in one88-column
radix512 public tuple. The importer independently checked all98,304 captured
output residues against the canonical raw output ciphertext after library inverse
NTT. It read no private files and reran no FHE operation.

[SOURCE] Input comes from
`../../learn_infer_only/experiments/end_to_end/nonlinear_successor_2026_09_08/public_trace/`.
The source descriptor and full public tensor are retained in `results/case001/`.
The actual plaintext modulus is4294475777; the exact four- and nine-prime bases
are in its `operation.json`. This is the native fixed-point directed scaler's
output, rather than an ideal nearest-rounding substitute.

[SOURCE / REPORTED] The arithmetic lane emits the relation and all witness
columns from Lean. Its first frozen artifact has63,845 trace columns,76,269
arithmetic constraints plus one exact-public lookup, and8,172,160 witness bytes.
`../arithmetic_rescale_generic/artifacts/emission.json` reports all32 actual
source rows checked and changed-output/radix512 falsifiers refused. Generic
matrix/compiler and concrete capacity proofs compile. Final public-alias and
native-word bridge pins were still being sealed at that handoff; consult that
lane's completed source theorem report for the final universal scope.

[EXECUTED] Rust defines no arithmetic constraints or witness generator. It
materializes the exact public rows, consumes the generated IR2/trace, and uses
the unchanged portable backend from `../proved_operation/backend`. Witness
hiding and proof-system settings are unchanged. The final source/binary pins are
in `BUILD.json`; commands and full outputs are retained under `results/`.

| Measurement | Value |
|---|---:|
| Proof bytes | 14,454,987 |
| Proving call | 2.590259s |
| Same-process independent-config verification | 0.641082s |
| Fresh-process verification call | 0.506974s |
| Changed-output rejection call | 0.160543s |
| Whole proving command | 3.868960s |
| Peak proving child RSS | 412,254,208bytes |

[EXECUTED] These are one-run observations on the recorded native host with
`RAYON_NUM_THREADS=4`. Proof SHA256:
`eb887940a2734828b56500a4d5f42316e29c1fb12c20a795ee341c6c24f62a31`.
Template SHA256:
`66a7e92c42525450458f4a4bd0062ddd43fb4da095b476e9ced54940ad56e517`.

[OPEN scope] This proof does not establish extension/convolution, upstream dot
products, the encoder, authorization, ciphertext-key membership, or the full
ciphertext/learner computation. Captured-intermediate provenance, public decoding
and basis conversion remain implementation assumptions. The proof demonstrates
acceptance of this generated arithmetic statement, with source-semantic coverage
provided separately by the arithmetic lane.

The development formatting incident and exact restoration are documented once
in `README.md`; all completed source/binary/proof siblings remain unchanged.
