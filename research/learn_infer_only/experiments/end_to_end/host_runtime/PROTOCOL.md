# Paired persistent-host prototype

[HYPOTHESIS preregistered] Persisting the existing CAS canonical-inspection
dictionary should remove repeated `inspect` subprocesses for unchanged current
queue blobs. Every CAS get must still read and SHA256 all blob bytes, and all
existing authorization, parent, canonical state, transition and result checks
must execute. Binary hashes remain checked before every actual crypto call.

[DERIVED design] A separate adapter invokes the unchanged frozen
`roles.propose` function. Its constructor lookup receives one metered CAS
object. One-shot mode exits after a request; persistent mode retains that
object and its existing `inspected` dictionary. Both use the identical wrapper
and accounting; the original normal CLI is also checked on the first request.
`CAS.get`, all validators, `model.transition`, the authority and reader are
unchanged. Source snapshots and hashes are frozen before the run.

[HYPOTHESIS experiment] Execute one normal encrypted journal history: 40 Learn,
four Infer after Learn indices 1,16,33,40, capacity32 on route0, hence eight
exact expiries. All 577-dimensional source and query vectors are public fixed
bounded integer fixtures; actual BFV setup and fresh encryption use the normal
OS-random path. This is an encrypted arithmetic workload, not a new utility or
private-ingress result. Each event is authorized once; both proposal paths
receive the same actual signed action/head/fresh ciphertext bytes in separate
CAS directories. Alternate which proposal path executes first. Compare the
complete canonical request bytes and actual result ciphertext bytes for every
event, then submit the normal proposal to the unchanged authority/reader.
Compare four returned private-reader oracle scalars with exact integer scores
and perform full public recomputed replay.

[HYPOTHESIS measurements] Report paired host caller wall time, time inside the
proposal function, crypto subprocess counts by command, actual full-blob SHA256
call/byte counts, and persistent inspection-cache size. The hash meter delegates
to the original SHA256 function; the first SHA invocation inside unchanged
CAS.get is its complete blob check. Both modes must have equal get/hash counts
and bytes. End-to-end harness time includes both proposal paths, issuer,
authority, reader, transport, replay and instrumentation and is not a separate
optimized end-to-end timing. No adversarial, signing-key-compromise or routed
output experiment is part of this tranche.

[OPEN trust boundary] The worker retains public ciphertext inspection metadata
and fixes one genesis/CAS/crypto configuration for its lifetime. It is keyless by
its configured inputs and command trace; this is not an OS isolation theorem.
The authority still independently recomputes all transitions. Cache correctness
uses unchanged pinned validation semantics and content-address identity with
full rehashes. Existing file-read/CLI time-of-check races and SHA256 assumptions
are unchanged. Historical metadata grows with distinct ciphertexts until worker
restart; there is no pruning or new continuity authority in this prototype.

