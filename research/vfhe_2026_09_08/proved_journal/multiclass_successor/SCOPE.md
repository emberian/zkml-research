# Model checkpoint, arithmetic proof and protocol boundary

[EXECUTED provenance] `checkpoint_from_records.py` selected the 64 successful
public `host-learn` records for events 1–64 from the existing learner's
`models/bfv/operations.jsonl`. It retained that prefix and the actual event-65
and event-66 public records in
[`checkpoint_public_records.json`](results/sequence001/checkpoint_public_records.json).
It checked exact selected accumulator hashes and recorded parent-hash lineages:
events 1,5,9,13,17,21,25,29 for `card_arrival` and
2,6,10,14,18,22,26,30 for `cash_withdrawal_charge`. Neither selected head is
consumed by a later recorded operation through event 64. Their next recorded
consumers are events 65 and 66, respectively.

[SOURCE boundary] This is a two-class checkpoint imported at event 64. It does
not prove earlier ciphertext arithmetic, class attribution, the encoder, FIFO
selection, or the original eight-class model history. Class labels and
source-event authorization remain application metadata. The helper reads the
public operation log and selected public ciphertexts/source-event files; it
does not load private keys, feature inputs or reader answers. It retains only
the selected public host-operation records and a byte hash of their source log.

[SOURCE implementation] For each new update, the native reader reconstructs
the selected 8,192 × 57 rows from the exact four canonical ciphertexts and the
service compares those bytes to the bound submitted rows. The actual native
verifier must accept the approved Lean-generated template/proof. Inside a
SQLite write transaction the service rechecks the global parent, current class
accumulator, consecutive global event, and next model root. It then changes
exactly one map entry, retains all other entries and commits the receipt/head
atomically. The request and receipt bind the before/after roots, selected class,
exact payloads, rows, proof, genesis, recipient and declared randomness rule.

[SOURCE boundary] The arithmetic proof concerns `out = acc + fresh - old` in
the stored BFV NTT representation: 16,384 RNS equations per update. The Python
class-selection and global-parent/commit logic binds that accepted proof into
the model protocol. Class labels, model root, authorization, genesis and
recipient are not new native proof conclusions. KeyID equality remains declared
metadata, not proof of ciphertext key membership or enforcement of recipient
key scope. The fixed class set is policy; dynamic class creation needs an
explicit extension or newly approved checkpoint.

[SOURCE TCB] The surviving assumptions from the
[single-class scope](../SCOPE.md) apply: trusted local callers and checkpoint
selection, native ciphertext/descriptor/proof parsers and verifier, Python
protocol logic, SQLite/filesystem durability and the shared OS. Reopen checks
the retained hash chain, model roots and CAS; it does not execute every proof
again. There is no external rollback anchor, hostile-storage guarantee or
distributed consensus. Source-event hashing does not authenticate its issuer.

[SOURCE policy] Arithmetic remains deterministic without rerandomization;
upstream encryption randomness is trusted and proof-commitment randomness
freshness is not certified here. The existing full BFV reader survives. There
is no confidentiality or restricted-release claim.

[EXECUTED boundary] Two consecutive actual updates, one stale-parent refusal,
clean process reopen and one historical retry were executed. Concurrent
writer contention, crash injection, a larger model, new teaching and proof
generation were not part of this run. Both service processes closed and zero
private comparisons were performed. No stopped routing path or companion tree
was used or changed.

