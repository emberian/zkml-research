# Executed BFV operation proofs

[EXECUTED] Two complete BFV ciphertext relations have real generated proofs
that pass fresh native verification and reject changed public output claims.
The second is actual useful-learner event 65: adding a fresh encrypted example
and subtracting its expired example from the class accumulator.

| Relation | Complete coverage | Trace | Proof bytes | Prove call | Fresh verifier call |
|---|---:|---:|---:|---:|---:|
| `3*A + 5*B mod q` | 24,576 residues | 8,192×1,234 | 557,834 | 3.141s | 100.2ms |
| `acc+fresh-old mod q` | 16,384 residues | 8,192×1,017 | 508,777 | 1.767s | 85.5ms |

[EXECUTED] Both include every polynomial position and component at degree 4096.
Four Rayon workers were selected. Full prove commands took 4.750s and 1.904s,
with peak RSS 1.589GB and 998MB. The prove call includes the existing backend's
internal self-verification. Full fresh-verifier commands, including input
loading, took 0.994s and 0.110s. Exact commands and costs are retained in
results/ and summarized in RESULT.json.

[SOURCE/EXECUTED] The sibling arithmetic_coverage package owns the universal
BabyBear-to-integer modular arithmetic theorems, ordered Signature.fold emission
and Lean witness production. Its whole-row theorems are
`Minidregg.Compiler.BfvLinearCombination.wholeRowSound` and
`Minidregg.Compiler.BfvExpiry.wholeRowSound`. Rust supplies public ciphertext
data and invokes the generic IR2 backend. It contains no duplicate operation
AIR or carry witness. The source relations contain 1,698 and 1,456 arithmetic
constraints, plus one exact public lookup each.

[EXECUTED] All RNS limbs of a position share one public lookup tuple and rowID.
The verifier reconstructs those tuples from the actual ciphertext files. The
weighted fixture uses decoded PowerBasis coefficients; the learner expiry
uses the exact stored canonical NTT slots, with no basis conversion. Its four
source payloads were also publicly replayed and matched the recorded output
byte-for-byte. No private learner files were read.

[EXECUTED fix] The first weighted proof is preserved under results/proof001/
as a failed artifact. Internal verification with saved common data passed,
but independent reconstruction failed with InvalidPowWitness. Source inspection
found randomized Merkle leaf salts in the public preprocessing commitment.
The owned backend/ adapter routes only commit_preprocessing through a portable
Xoshiro256PlusPlus 0.8.1 fixed public-salt factory. Witness, quotient,
random-codeword, FRI and verification methods delegate to the existing
OS-seeded hiding PCS. All FRI settings remain unchanged. Tests passed for
stable public commitments across configurations/call order, changed commitments
for changed public data, and randomized witness commitments. Both accepted
proofs use this explicitly identified adapter.

[REPORTED, sibling executed logs retained] The shared JavaScript/WASM consumer
accepts both proofs and rejects changed public outputs under Node WebAssembly.
Genuine calls took 1.669s and 1.747s. See
../browser_verifier/results/verify-wasm.json and verify-wasm-expiry.json.

[SCOPE] The formal arithmetic theorems are separate from Rust codecs, generic
IR2 execution, the PCS adapter and Plonky3 proving/verifying. These coefficient
proofs do not establish encoder execution, FIFO authorization, ciphertext-key
membership, distributed witness privacy or a whole learner correctness theorem.
Exact proof/template/data anchors and selected source pins are in RESULT.json.
