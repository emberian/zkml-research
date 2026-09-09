# Complete saved BFV square join

The fixed target is the actual saved degree-8192, two-component ciphertext
`basic.dot.ct`, squared without relinearization or modulus switching into
the saved three-component `basic-000.ct`. The base has four 50-bit primes;
the multiplication basis adds five 62-bit primes. Exact constants are
`results/case001/operation.json` and the native reader's fixed arrays.

[EXECUTED] The public importer has produced all required rows. It reconstructs
base PowerBasis coefficients from the raw input, records the actual identity
RNS extension, and checks its forward transforms against native extension in
NTT representation. Native tensor products and inverse transforms agree with
all 221,184 previously captured pre-rescale residues. The saved rescale was
not recomputed. All 98,304 output residues match the raw output ciphertext.

The new proof sequence contains four extension chunks and eighteen tensor
chunks, each 4,096 rows, with no padding. Each invocation generates an
untrusted witness from a Lean-generated plan, loads the approved generated
template, produces a proof and verifies it under a fresh backend configuration.
Chunks execute sequentially with four Rayon threads. Any failure or timeout
stops with its outputs retained; no retry belongs to the frozen sequence.

The final consumer freshly verifies all 28 proofs: four extension proofs,
eighteen tensor proofs and the six unchanged complete-rescale proofs. It does
not trust producer acceptance flags. It chooses templates from locally approved
phase configurations and requires every fixed component/prime interval. The
six rescale proofs are reused only against precisely the same reconstructed
public input/output rows; they are not reproved.

Public boundary layout:

- Extension: 16,384 positions, global ID `component*8192+coefficient`. Public
  arity 84 is row ID, four input words of six radix512 digits, four copied
  output words of six digits, then five new output words of seven digits.
- Tensor: 73,728 tuples, global ID `primeIndex*8192+NTTindex`. Public arity 56
  is row ID then `a0,a1,p0,p1,p2`, each eleven radix64 digits. Nine fixed-prime
  templates force `p0=a0²`, `p1=2*a0*a1`, `p2=a1²` modulo that prime.
- Rescale: 24,576 positions, global ID `component*8192+coefficient`. Public
  arity 88 and the previously approved directed 9-to-4 relation are unchanged.

The verifier derives the input PowerBasis from the raw ciphertext, loads the
claimed extension PowerBasis, and recomputes its NTT representation. It also
transforms the exact captured rescale inputs into the tensor outputs. It checks
copied common-modulus rows in both representations. **No scaler or product
arithmetic is executed in this verifier path.** Generated relation proofs
decide those nonlinear transitions. The final rescale verifier binds the
PowerBasis result to the canonical raw output ciphertext.

The fixed controller requires the same input/output ciphertext hashes,
extension tensor hash and captured rescale-input hash throughout. Exact public
row binding, decoding/serialization, linear transforms, source/parameter
capture, relation loading and proof backend remain explicit implementation
TCB. No Lean refinement of these Rust/Python/library layers is asserted.
Accepted-assignment soundness comes from the generated source relations;
native witness programs remain untrusted.

Full acceptance means the saved raw ciphertext square arithmetic is verified
under that TCB. It does not include the preceding encrypted dot product or
rotations, text encoding, BFV security/noise, private-key custody, decryption,
authorization or a shipped system. No private files are needed.

Sources/configurations freeze before proof launch. Public commands, costs,
proofs and bindings are retained. Raw traces are compressed after successful
proof production and kept under ignored `work/`; raw and compressed hashes
are saved before removal of the raw file. Final reporting aggregates public
records only. No sampled precursor proof, baseline reproof or negative grid
is part of this complete run.
