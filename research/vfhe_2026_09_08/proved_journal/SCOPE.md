# Exact scope

[SOURCE implementation] The approved native binary reconstructs 8,192 public
rows of width 57 directly from four canonical BFV ciphertext payloads. Each row
contains its row identifier and seven least-significant-first radix-64 digits
for each of two RNS limbs of accumulator, incoming, expired and output values.
The selected Lean-generated template constrains 16,384 residue equations for
`out = acc + fresh - old` in the stored NTT representation. No basis conversion
or fresh arithmetic randomness is part of this operation. See the frozen
[`update.rs`](../proved_operation/src/update.rs),
[`main.rs`](../proved_operation/src/main.rs),
[`shared backend`](../proved_operation/backend/src/lib.rs) and
[`template`](../arithmetic_coverage/artifacts_expiry/template_ir2.json).

[SOURCE implementation] Genesis approves one executable, template, service
source, parameter identifier, declared key identifier, recipient identifier,
learner class, initial accumulator checkpoint and randomness rule. Every
request binds the genesis digest, parent state hash/revision, exact four
ciphertext hashes, rows/proof/source-event hashes, learner events, recipient and
policy hashes. The service stages bytes, reconstructs the rows independently of
the supplied rows file, requires exact row-byte equality, and runs the actual
native proof verifier. Only then does a SQLite `BEGIN IMMEDIATE` transaction
check the current parent again and append the receipt and head atomically.

[SOURCE implementation] The proof establishes the selected ciphertext
arithmetic relation. The Python request policy and receipt bind genesis,
parent, recipient and declared randomness to the accepted proof under the
protocol TCB. Those metadata fields are not new arithmetic theorem conclusions
and are not independently proved as part of the native relation. The exact
ciphertext envelope is protocol-bound; keyID equality does not establish
ciphertext membership in that key.

[SOURCE implementation] The TCB includes local caller authorization and choice
of initial checkpoint, JSON and ciphertext/descriptor/proof parsing, the native
adapter and verifier binary, Python request/commit logic, filesystem/SQLite,
and the shared OS. Canonical ciphertext decoding and exact reserialization are
performed by the native reader. Native proof parsing uses the existing strict
postcard path. OS permissions isolate ordinary local files, not an adversarial
process with the same account's authority. There is no signed issuer protocol,
rollback-resistant external anchor, distributed consensus or hostile-storage
claim. A clean reopen audits retained receipt/CAS hashes and the parent chain;
it does not rerun every historical proof.

[SOURCE implementation] The incoming and expired ciphertexts are trusted
learner-provided operands. This relation does not prove text encoding, correct
choice of expired FIFO entry, window capacity, model accuracy, decryption,
ciphertext key membership, or authorization to issue an event. The generator of
`source_event.json` is not authenticated by its hash. The service enforces exact
current accumulator continuation and one class, not the complete learner/FIFO
application policy.

[SOURCE policy] The arithmetic is deterministic and does not rerandomize its
output. Fresh encryption randomness is the upstream learner's responsibility.
The shared backend's public preprocessing is fixed; the retained prover uses
OS randomness for witness commitments. This service neither generates those
commitments nor certifies their randomness freshness.

[EXECUTED scope] The demonstration used only public ciphertexts, rows, proof,
template and metadata. It performed no secret-key reads or private comparisons;
both local service processes closed. It preserves the actual learner's full
BFV reader and makes no confidentiality or restricted-release claim. One
accepted update demonstrates the generic continuation gate; a longer newly
proved teaching sequence is follow-up work, not a result claimed here.

