# A real nonlinear BFV rescale batch

[EXECUTED] This executable imports public intermediates from the actual nonlinear
text-kernel operator and exports a fixed batch for a Lean-generated nine-to-four
RNS scaling relation. The source capture has degree 8192, three output components,
nine extended primes and four ciphertext primes. No private files are required.

The 32 distinct selected positions, including all 12 component/row boundaries,
are explicit in `selection.json`. Each public row contains its selection ordinal,
9 × 7 radix512 input digits and 4 × 6 radix512 output digits. There is no padding.
The relation covers these 32 of 24,576 positions and 128 output residues.

The importer checks integer bounds, tensor dimensions, declared parameters,
source hashes, canonical ciphertext decoding and all 98,304 output residue values
against the raw output ciphertext after the library's inverse NTT. The captured
extended product, decoding, basis conversion and origin metadata remain outside
the arithmetic proof. The proof does not cover convolution or the complete
ciphertext/learner operation.

The Rust runner defines no AIR equations and computes no arithmetic witness.
It reads the ordered IR2 template emitted from Lean, supplies its ExactPublicRows
table, and consumes the Lean-produced trace. It uses the unchanged shared
`../proved_operation/backend` portable public-preprocessing adapter. Witness
commitment randomness and all proof-system parameters remain unchanged.

Build and import (run from this directory):

```sh
cargo build --release --offline -j2
target/release/vfhe-proved-rescale-generic import PUBLIC_TRACE selection.json NEW_CASE
```

The source directory uses fixed names `descriptor.json`, `basic.json`,
`basic.dot.ct` and `basic-000.ct`; embedded paths are never followed.
For a generated relation with the same 88-column public layout:

```sh
RAYON_NUM_THREADS=4 target/release/vfhe-proved-rescale-generic prove TEMPLATE CASE TRACE NEW_PROOF
RAYON_NUM_THREADS=4 target/release/vfhe-proved-rescale-generic verify TEMPLATE CASE PROOF_BIN
RAYON_NUM_THREADS=4 target/release/vfhe-proved-rescale-generic verify-changed-output TEMPLATE CASE PROOF_BIN
```

The caller chooses the approved template; changing that template changes the
statement. The proof report records its hash. Proof decoding rejects trailing
bytes. The changed-output check flips the first output digit while preserving
the original proof. `run_command.py` retains command output and measured costs.

[EXECUTED] The actual32-position proof passed, fresh-process verification accepted,
and a changed public output digit was rejected. See `REPORT.md` and `RESULT.json`
for scope, exact artifacts and measured costs.

[EXECUTED development correction] An accidental `cargo fmt --all` reached eight
companion files and the frozen shared adapter. The adapter was restored from
bytes matching its preexisting frozen hash. The companion files were restored
only after a retained baseline established they were clean, with current-content
guards; the three preexisting modified files and staged diff were preserved.
The resulting complete companion status matches that baseline. Evidence is in
`results/formatting-restored.json` and `results/shared-backend-restored.json`.
The final runner build used the restored adapter. Future formatting targets
owned files explicitly.
