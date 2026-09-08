# Exact query-gate scope

[SOURCE arithmetic] The selected generated relation binds two ciphertext ×
plaintext products and their final subtraction for each class query. It covers
8,192 rows of width 57: row identifier, two radix-64 limbs each for accumulator,
positive plaintext multiplier, negative plaintext multiplier and final output.
Both ciphertext components and both actual RNS primes are included. The
products share their intermediates with the final subtraction in one joined
relation. This is not a proof of only one sign or one output component.

[SOURCE encoding TCB] The public native reader parses the exact canonical query
JSON, reverses its 577 signed coefficients, splits positive/negative parts,
encodes the two plaintext polynomials and obtains their NTT representations
using the existing FHE library. Parsing, plaintext encoding and NTT conversion
remain implementation TCB. The native verifier reconstructs rows from the exact
accumulator/query/output files. There are no rotations or key-switch operations
in this selected host-infer branch. The underlying generated theorem and
backend assumptions remain those of the query compiler/runtime package.

[SOURCE protocol] A query genesis binds the frozen gate/pipeline/config/native
source identities, approved template, underlying model genesis and recipient.
Each request binds the current global revision/head hash/model root, canonical
query hash, all active classes and committed counts, and each class's exact
accumulator/output/proof/row hashes. Class coverage comes from committed
receipt-derived queues, not a caller-supplied subset. The gate compares exact
coverage, independently reconstructs rows and executes native verification for
every required class, then checks the same current head under the journal's
write lock and writes a durable public acceptance file. Private receive
requires that acceptance and rechecks current state and all output bindings.

[SOURCE protocol] Model/global-head/recipient/request binding and class coverage
are local protocol logic; they are not additional native arithmetic theorem
conclusions. Application issuer identity, plaintext encoder, FIFO/counts,
ranking/decoder, JSON/ciphertext/proof parsing, SQLite/filesystem and shared OS
remain trusted. The same-account full reader can operate outside this adapter;
there is no cryptographic decryption restriction, key-membership proof, hostile
storage guarantee or confidentiality claim.

[SOURCE new-query boundary] The predecessor live001 query was already received
and remains explicitly historical. This successor creates a different isolated
key/model, performs new genuine teaching and evaluates a new query. Its proof
pipelines, gate exports and native verifiers must all terminate before private
receipt. The gate's command wrapper checks process-group absence; all active
class acceptances are present in the public record before the reader runs.

[SOURCE decision boundary] Empty classes are excluded under the existing
committed-count readout policy. The bounded demonstration intentionally
populates both declared classes, so its decision depends on two proved class
scores. This is a small semantic/mechanics fixture, not an accuracy benchmark.
The direct integer comparison is performed afterward and attributed as an
application check, not used to authorize public acceptance or select a proof.

[SOURCE limits] The gate does not prove text encoding, issued examples'
authorization, decryption, ranking, complete model/FIFO semantics, or historical
initialization. Its underlying live service imports a fresh zero checkpoint
and uses the existing proof-gated updates to populate it. Source bytes and
completed predecessor states are preserved. No stopped routing path, new
independent-review gate or large validation grid is involved.
