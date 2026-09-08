# Actual committed-query arithmetic proof

[EXECUTED] The first proof of the saved live `card_arrival` query passed.
It binds both ciphertext–plaintext products and their final subtraction across
all8192 NTT positions of the two-component ciphertext:16384 final output
residues across both primes. Fresh-process verification accepted; changing the
first final-output digit caused rejection. The842,564-byte proof is in
`results/proof001/proof.bin`.

[EXECUTED] The public exporter reconstructs the actual577-coefficient reversed
positive and negative query encodings, exports the native plaintext NTT values,
checks all32768 native product residues, and compares the complete output payload
with the saved query result. Canonical input/query/output parsing and matching
parameters/key metadata are checked. It reads no private key and performs no
decryption. Exact public inputs, products, NTT plaintexts and output are retained
in `results/case001/`.

[SOURCE / DERIVED] `../query_arithmetic/README.md` describes the new generic
modular multiplication theorem and its composition with the existing generated
subtraction relation. `wholeRowSound` and `emittedSystem_sound` bind the shared
internal products to the final public result. Four Lean modules and22 exact
axiom guards passed. The emitter constructs every auxiliary witness from the
public values; internal products are not caller premises. Four constructed
source cases and output/radix controls are checked. Actual8192-row constraints
are checked by the native prover; there is no duplicated full Lean interpreter
pass. The template has2509 columns and2744 arithmetic constraints plus one
exact-public binding, from4442 source constraints before generic sharing.
Rust defines no replacement AIR or arithmetic witness.

[EXECUTED provenance] Retained public service metadata links the accumulator,
query and result to revision1/model root
`e5b2c59da18da8ce4d43aea3c431fa8ff017df029575458a3f2abe5e9cb4ddb6`.
See `results/case001/provenance.json`. This proof was generated after the earlier
live run's reader phase. It does not retroactively make that historical query
proof-gated before decryption. The new `proved_journal/query_gate_successor`
consumer owns proof-before-private-receive behavior for subsequent queries.

| One shared-host observation | Value |
|---|---:|
| Proof bytes | 842,564 |
| Proving call | 3.813823s |
| Same-process independent-config verification | 0.100227s |
| Fresh-process verification call | 0.111377s |
| Changed-output rejection call | 0.102262s |
| Whole proving command | 4.002188s |
| Peak proving child RSS | 2,100,527,104bytes |

[EXECUTED] Four Rayon threads were used, with other swarm work allowed on the
host. These are one-run costs, not a throughput distribution. Exact commands,
stdout/stderr and process measurements are in `results/*.command.json`.

[EXECUTED reusable interface] `run.py ACC_CT QUERY_JSON OUT_CT NEW_RUN` connects
public export, the frozen Lean emitter, proving and independent fresh verification.
It checks source/native pins, requires the emitted template to match the approved
one exactly, and records input/proof/template hashes in `NEW_RUN/result.json`.
All outputs stay in the new caller-owned directory. It has no secret reader or
retry and inherits the caller's process group for service cancellation/quiescence.
The first integrated wrapper execution belongs to the new substantive service
run; this lane already executed its native stages against the retained fixture.
`README.md` gives the CLI and `PIPELINE.json` the fixed implementation choices.

[EXECUTED pins] Proof:
`1fa6b436dd9fab6c84500469e1752f5785226459600708c924dfa5bd2e6ce9f9`.
Template:
`f42c5efcaa994656b0c9ef2d1270aa2d6eb7dae0e5ba85938d23dbb3dc46c10d`.
Native binary:
`9566638eef8f0dce7c5d3edd351f1e29da6301164ccbe1d8451ce642874c8c2c`.

[OPEN scope] This is the complete ciphertext arithmetic for one active class.
The other class, multiclass ranking, query encoding/NTT, serializer, ciphertext-key
membership, BFV noise/plaintext validity, reader behavior and protocol metadata
remain outside the arithmetic theorem. Future complete application queries must
verify every returned class ciphertext and perform their own accepted-head,
request and recipient checks before receipt. The shared portable proof backend
and witness hiding settings are unchanged.

The two remaining formatting-only edits discovered in a frozen predecessor were
restored to exact hashes recorded in its RESULT.json, without rebuilding it.
Evidence: `results/frozen-operation-formatting-restored.json`; no new incident
or intentional predecessor edit occurred during this query implementation.
