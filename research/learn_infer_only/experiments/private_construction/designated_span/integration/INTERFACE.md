# Exact normal interface and host-view boundary

[DERIVED from copied code] These are application capabilities, not additional
cryptographic primitives. `source/crypto/crypto.py` implements the designated
DDH backend; the journal controls the honest application's use of it.

| Endpoint or process | Inputs | Result and binding |
|---|---|---|
| Trusted setup | Fixed 16 public rows, group/dimension/window parameters | Public context plus 16 separate dedicated recipient scalar files. Full public context algebra is validated and its digest cached under pinned source identity. |
| Trusted issuer `issue` | Fresh private signed-int8 vector; selected public parent/route/record ID | Fresh 578-element ciphertext plus independent issuer signature over its digest and bounded-range assertion. No online master/function-key issuance credential. |
| Host `propose` / authority `submit` Learn | Exact admitted ciphertext and canonical current queue | Multiply accumulator by fresh ciphertext; when full, divide by the oldest exact original. State includes the queue and accumulator. Authority independently recomputes. |
| Command `authorize` Infer | One of the 16 preregistered queries plus exact parent/route | Signature binds query digest, context, row, row digest, token digest and dedicated recipient identity. |
| Host / authority Infer | Current accumulator and canonical fixed query | Two-group-element designated output ciphertext; current learning state is unchanged. |
| Public reader `put`, `sync` | Encrypted blobs and finalized journal envelope | Checks exact signed context, current head, uniqueness and every arithmetic transition before advancing its own durable verified journal. No scalar key is loaded. |
| Public reader `register`, `receive` | Selected query ticket; exact independently verified output | Durably accepts the designated ciphertext/envelope then ACKs. Replays return the same accepted identity. No scalar decode or decode counter is consulted. |
| Public reader `status`, `verified_status` | Public request | Counts only selected/accepted/verified public records and reports the verified state digest. Neither reads private answers. |
| Recipient-private `drain.py` | Verified accepted records and dedicated key directory | Opens each designated row using only that row's scalar, stores private signed score/dedup/cost. No public RPC or public database mutation. |
| Trusted oracle `compare` | Private raw fixture and private answers | Aggregate correctness evidence for the researcher. This comparison bit and coordinator scheduling are outside the cryptographic host view. |

[DERIVED] Public metadata includes dimensions, rows, fixed horizon/window rules,
route/request chronology, recipient and token identities, ciphertext equality,
accepted/replayed status, and all public context/ciphertext bytes. Public
verification work is a computation of these public objects. Encryption and
recipient decoding are private-role computations; whole-program side-channel
resistance is not claimed.

[DERIVED] The public service's later status, retry, persistence and error branches
do not depend on private answer value, private decode success or private dedup.
The private drain can stop or fail without changing an accepted ciphertext row.
This is a source-level dependency statement for the service, not a formal timing
proof of the Python/shared-OS benchmark. The trusted coordinator is expressly
outside that statement: it waits for private comparisons before publishing its
research report and, in the preserved first run, before scheduling the final
public replay check. No research report is treated as an allowed cryptographic
host observation.

[DERIVED] Integer score correctness assumes honest bounded issuance and exact
queue expiry. Each row has the fixed bound `32*127*sum(abs(y_j))`; group-order
wraparound is excluded for that integer interval. The recipient still obtains
the entire modular group projection, and the bounded discrete-log routine is an
application decoder, not a cryptographic magnitude gate.

[DERIVED] Dedicated recipients can bypass their own reader software, derive
linear combinations of the fixed keys and evaluate their span on retained inputs.
The public row enumeration is an honest application policy, not an enforceable
limit on a recipient that owns keys. New independent query directions cannot be
issued after master erasure using this setup. Window expiry preserves bounded
current arithmetic; it does not revoke retained input ciphertexts or supply
history deletion. Orderly reopening verifies durable continuation under the
persistence assumption; no malicious-rollback or hardware-finality experiment is
performed here.
