# Credential and persistence inventory

[DERIVED from the frozen source] The narrow host-view composition is the source
DDH designated fixed-span claim combined with independent classical role keys.
This file records implementation roles; it does not prove erasure or OS isolation.

| Role / material | Creation and survival | Actual authority / trust premise |
|---|---|---|
| Initializer vector `s` | OS randomness in initializer subprocess; not serialized; process exits | Full input-read master during honest setup; every copy must be erased/absent afterward. Software execution cannot certify physical erasure. |
| Fixed projection deliveries `k_i=<s,y_i>` | Initializer writes private temporary row delivery; corresponding recipient registration consumes it; orchestrator removes delivery before finalization | Any retained `k_i` together with public `tau_i` gives dedicated `a_i`; erasure must include these and all equivalent copies, not merely `s`. |
| Recipient pending / final `a_i` | Separate recipient process samples each independent scalar; temporary pending file removed after final key envelope; only `r00.key` through `r15.key` remain | Each scalar decodes its fixed row on any valid retained input/output. This run's private drain holds all16 and is the full fixed-span recipient coalition. |
| Public `h`, `A_i`, `tau_i`, rows | Canonical public context, digest pinned in genesis/config and every envelope | Host can encrypt public or private issuer inputs, add/subtract exact originals, and transform all16 fixed rows. It does not hold a recipient scalar. Public token consistency is not proof of honest erasure. |
| Issuer encryption randomness | Fresh OS randomness in each issuer CLI process, never output or retained as a credential | Fresh independent randomness is essential. Private issuer side channels and copied random coins are excluded. |
| Issuer plaintext inputs / integer oracle | Generated and saved under `.private/oracle/` by the trusted fixture process | The oracle/issuer knows all40 inputs and the initial zero, so it can reconstruct this fixture's entire raw aggregate by replay. These files are excluded from the host view; their survival prevents a coalition-wide no-read-all claim for the actual test. This is a role boundary, not an OS sandbox. |
| Issuer Ed25519 signing key | Independently generated after crypto setup | Authenticates the bounded-input assertion; no ZK range proof is supplied. The bounded score theorem assumes honest input issuance/range. |
| Command Ed25519 signing key | Independently generated after crypto setup | Authorizes one exact query context/parent/route/recipient. Gives no decryption capability. |
| Authority Ed25519 signing key | Independently generated after crypto setup | Signs the durable journal result. The recipient verifier independently recomputes all transitions rather than trusting arithmetic from this signer. |
| Public verification service | Public context, genesis/source pins, immutable encrypted CAS, expected query tickets, verified journal, accepted ciphertext records | Has no recipient scalar path/config. Receives, retries, status, pending and ACK behavior depend only on public records. No RPC invokes private drain. |
| Private drain | Dedicated key directory plus separate private answer DB and cost log | Reads the accepted/verified public records; writes no public acceptance/delivery state. Private dedup limits this honest software run, not the coalition's key authority. |
| Trusted research coordinator | Orchestrates roles, holds fixture/oracle access, publishes aggregate evidence | Its comparison bit, final report publication, private-phase scheduling and wall-clock timing are **outside** the cryptographic host view. They are not an additional public API proved safe here. |

[DERIVED: two-phase persistence] `reader.py` stores only the accepted encrypted
output and signed envelope in `received`. `verified_reader/service.py` maintains
`verified_head` and `verified_journal` after recomputation. `drain.py` opens that
DB only for reads, then writes its separate `.private/reader/answers.sqlite3` and
private cost log. No later public method reads either private output location.
Every public retry/status response remains a function of the public acceptance
DB, irrespective of private decoding success or value. Physical lock/scheduling,
shared-OS observation and private coordinator feedback remain excluded.

[REPORTED / explicitly outside the host view] The frozen first harness performs
all public event ACKs and exact retries before private drain, then schedules its
independent arithmetic replay and trusted aggregate report after drain. This is
normal functional evidence, not a timing/feedback-safe coordinator protocol. A
subsequent wrapper should finish all public replay/status handling first and save
only recipient-private comparisons afterward. We preserve the original executed
source and do not change a running experiment.

[DERIVED: limits] W=32 controls the intended current aggregate. Retained input
ciphertexts remain available, so expiry supplies neither plaintext deletion nor
revocation. The recipient coalition can evaluate its whole fixed span on each
retained input/snapshot without following this reader. Public/secret roles are
separate processes under one account; the machine owner can read those files.
Actual isolation requires a separate deployment boundary not implemented here.
