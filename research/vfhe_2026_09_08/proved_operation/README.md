# Real BFV operation with a generated proof relation

This directory executes a full BFV ciphertext linear combination and feeds a
Lean-generated relation and Lean-produced witness into the existing
DescriptorIR-v2 Plonky3 HidingFRI prover. There is no operation AIR or carry
witness implementation in Rust. Both full proofs now pass fresh native verification and the shared JavaScript/WASM
consumer; see REPORT.md and RESULT.json for results.

Build the isolated runner with `cargo build --release --offline -j2`. The main
breadstuffs and minidregg trees are read-only dependencies; Cargo.lock records
the resolved dependency versions. The executable lives under this directory's
ignored `target/`.

The initial fixture is `results/case001/`: actual ciphertexts for
`output = 3*A + 5*B`, degree 4096, two components and three RNS moduli. It was
generated with a fresh key on public synthetic messages; the secret key was
not saved. `public_rows.json` has 8192 rows containing rowID and all three
radix64 input/output limbs. Its plaintext and residue comparisons are executed
fixture checks, separate from the proof.

The source relation and witness exporter live in the sibling
`../arithmetic_coverage/`. The emitted template's public table 11 is populated
with coefficient rows reconstructed from the actual ciphertext files. The
64 public columns are rowID,A[3][7],B[3][7],output[3][7], limb major and digit
least-significant first. All RNS limbs of a coefficient share one lookup tuple.
The separate PI vector has length 0 because these public values are in the
statement's preprocessed exact table; they are not absent from the statement.

Commands consume an application-selected template rather than accepting a
relation supplied inside a proof:

```
target/release/vfhe-proved-operation inspect TEMPLATE results/case001
target/release/vfhe-proved-operation prove TEMPLATE results/case001 TRACE_LEU32 PROOF_DIR
target/release/vfhe-proved-operation verify TEMPLATE results/case001 PROOF_DIR/proof.bin
target/release/vfhe-proved-operation verify-changed-output TEMPLATE results/case001 PROOF_DIR/proof.bin
```

Proof bytes use postcard. Verification rejects trailing bytes and reconstructs
the public coefficient rows from ciphertexts, not from a proof-side manifest.
`run_command.py LABEL COMMAND...` retains one invocation and its output/costs.

The real useful-learner expiry is separately imported at
`results/learner_expiry001/`. Its four public ciphertexts are byte-identical
copies of the frozen event 65 handoff. Public replay of `acc+fresh-old` matches
the full canonical output payload. Its table layout is
rowID,acc[2][7],fresh[2][7],old[2][7],out[2][7], width 57. The commands
`inspect-update`, `prove-update`, `verify-update`, and
`verify-update-changed-output` use that reader with the generated update
template. No private learner files are read.

The formal arithmetic theorem is distinct from the executed proof backend.
Rust ciphertext decoding and NTT-to-coefficient conversion, generated-JSON
parsing, and the existing prover/verifier remain implementation assumptions.
These coefficient statements do not establish encryption-key membership,
encoder execution, FIFO authorization, or a whole learner correctness theorem.

[EXECUTED fix] The shared backend/ library changes only public preprocessing
commitment reconstruction to use portable fixed public salts. Witness hiding
and all FRI settings remain unchanged. The original failed proof is retained;
the two accepted proofs use the separately named corrected backend.
