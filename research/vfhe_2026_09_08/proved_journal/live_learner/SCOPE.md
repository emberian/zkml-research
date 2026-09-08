# Live acceptance boundary

[SOURCE implementation] The adapter reuses the frozen useful learner's
`Encoder` and `Learner.crypto`/`receive` methods. It deliberately does not call
`Learner.teach_vector`, which would eagerly publish tentative learner state.
The new issuer object's `learner.json` stays at revision zero with an empty
class map. Actual model heads, event order and receipts live in the multiclass
proof-gated journal. The adapter reconstructs counts/queues from that accepted
history, not a separately saved tentative model.

[SOURCE implementation] New text is encoded by the fixed E5-base-v2 checkpoint,
with the existing mean-pooling/normalization, seeded projection and integer
rounding recipe in the useful learner's encoder/config. Labels are not encoder
inputs. Model files are loaded from the existing local cache; the loaded model
and runtime libraries remain trusted issuer dependencies. The proof does not
verify the encoder. No model-file attestation or benchmark claim is added here.

[SOURCE policy] The imported initial checkpoint has a fresh native BFV key and
two declared empty classes. Its canonical zero ciphertext comes from native
keygen's difference of a ciphertext with itself. This initialization is trusted
application setup, not proof of an older model. The adapter uses zero outgoing
until a class has eight committed observations; later it selects the oldest
committed incoming ciphertext. The journal independently enforces exact
class/global parent, one-class replacement and approved arithmetic proof, while
the FIFO/authorization semantics remain adapter TCB. The fixed class set cannot
be extended by an ordinary teach request.

[SOURCE implementation] A candidate, source event, generated witness/proof and
request stay under `proposals/`. Staging never changes the accepted journal.
Commit requires a completed proof pipeline and the journal's actual fresh
verification/current-parent transaction. Queries read a consistent committed
head/receipt snapshot and evaluate only the corresponding content-addressed
class ciphertexts. A public query record is written after all public host
processes finish and before private receipt. The proof pipeline's process group
must be absent before proceeding. Plaintext outputs come from the new
instance's full reader after those public phases.

[SOURCE TCB] Local caller authorization, source-event identity, cached encoder,
canonical parsers, native verifier/adapter, Python FIFO/query/commit logic,
SQLite/filesystem and shared OS remain trusted. The journal checks the emitted
update relation, not inference arithmetic, ciphertext key membership, encoder
execution, FIFO authority or cryptographic recipient restriction. The host
query and reader are actual executions; there is no new query proof. Direct
same-account access to the journal/key is outside this adapter's enforcement
claim. The full BFV reader survives, and no confidentiality claim is made.

[EXECUTED scope] One newly encoded teaching example and one distinct query were
run, using one loaded model object and two encoder forwards. There were two
declared classes and one active class after teaching; the inactive class was
excluded from ranking. This demonstrates the live acceptance path and actual
integer score, not classification accuracy across two populated classes.
The failed proposal substituted the proposed next model root and was refused
before proof execution/commit. It was not a malformed-proof experiment.

[EXECUTED scope] A direct integer dot comparison was performed only after the
public phases and actual private receive; both feature vectors came from this
instance's newly encoded inputs. The new private key/cache were never exported.
The public packet includes the new proof and exact public case; model weights,
private feature caches and large generated trace remain outside that packet.
No frozen predecessor model or key, stopped routing path or companion source
was changed. Expiry, multiple populated classes, concurrent writers and a
long-running teaching session were not exercised by this bounded run.

