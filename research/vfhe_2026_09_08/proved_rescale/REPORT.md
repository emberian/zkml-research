# Complete small BFV rescale proof

[EXECUTED] A real degree-8 BFV ciphertext multiplication produced three output
components. All eight decrypted coefficients match the negacyclic plaintext
product. Every rescale position in every output component now has a generated
proof: 24 actual positions and 72 output residues. Fresh native verification
passes; changing the first claimed output digit rejects.

The proof is **8,592,353 bytes**. The prove call took **1.377s**, including the
existing internal check; independent-common self-verification took 408ms.
Fresh verification took 312ms internally and 440ms including parsing/I/O.
The full prove command took 2.028s, peak RSS 244.7MB, with four Rayon workers.
Exact commands and outputs are retained under results/ and in RESULT.json.

[SOURCE/EXECUTED] arithmetic_rescale owns the Lean relation and witness.
`Minidregg.Compiler.BfvRescaleRow.rowSound` (Compiler/BfvRescaleRow.lean:109)
forces all three target residues from the exact fixed-point downscaler output;
it composes the existing source and target-projection systems with shared
intermediate values. This includes the source's nearest-plus-one behavior.
The emitted relation has 45,209 arithmetic constraints and one exact public
lookup, width 37,665. All 32 source rows passed before proving.

[EXECUTED] The first 24 public tuples cover each actual position; eight explicit
copies of position 23, with fresh rowIDs, pad to the backend's required power
of two. Each tuple joins all six input residues and all three output residues.
The verifier reconstructs these tuples from the saved product polynomials and
actual output ciphertext. The unchanged portable public-preprocessing backend
from proved_operation is reused; no prior source or binary was modified.

[SCOPE] This proves the complete small rescale step, not the whole ciphertext
multiplication controller. RNS extension and convolution provenance were
executed/reconstructed with the same library operators and checked against
all output residues; they are outside this relation. Ciphertext decoding and
basis conversion remain implementation assumptions. Degree 8 is a small
arithmetic fixture, not a secure FHE parameter. No secret key was saved,
relinearization or modulus switching performed, or full nonlinear learner proof
claimed. The completed full-size linear/learner-expiry package remains separate.
