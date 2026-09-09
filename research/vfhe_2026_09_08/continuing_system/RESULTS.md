# A continuing learner, through expiry and restart

[EXECUTED] The linear/matched application completed the fixed 17-operation
workload: twelve fresh teachings, four two-class queries, and a process reopen.
The ninth and tenth teachings to `proof_integrity` removed its two oldest
examples. All 64 decrypted signed slot values, class sums, counts and exact
rational rankings matched the independently computed integer reference. The
post-restart query produced fresh proofs and returned the same scores and model
root as the preceding query.

[EXECUTED] This workload produced **3,200 fresh proofs**, independently verified
all 3,200, and performed eight private class reads after complete public
acceptance. Proof data totaled **583,046,239 bytes**. Recorded worker-attempt time
was **638.021 seconds**; no proof phase failed or was discarded. This time covers
the workload after browser initialization and feature preparation, not those
earlier steps. Sources: `results/linear-matched/RESULT.json`, the individual
`steps/*/completed.json` records, command/stdout/stderr records and `MANIFEST.json`.

## What changed in the computation

[DERIVED from implementation] The application can now select mean signed
similarity, avoiding the ciphertext square and integer rescaling. The new proof
backend also works directly in the four BFV arithmetic fields, eliminating the
smaller proof field's carry and range witnesses. The score rule and exact backend
descriptor are fixed at genesis; existing squared-mode instances reopen with
their original policy.

[EXECUTED] The first two-class query in each complete application path gives a
concrete comparison:

| Observed query | Squared / compact | Linear / matched |
|---|---:|---:|
| Worker time | 1,103.216 s | 113.070 s |
| Fresh proofs, independently checked | 232 | 704 |
| Proof bytes | 235,624,423 | 128,677,569 |
| Decrypted values matching reference | 16 / 16 | 16 / 16 |

[SOURCE: retained execution records] The squared record is retained in
`results/squared-compact/steps/query_initial/completed.json`. The matched record is retained in
`results/linear-matched/steps/query_initial/completed.json`. These observations
change both the score and proof profile, with concurrent work on the same
machine. They are not a controlled, equal-security cryptographic benchmark.

[EXECUTED] The complete squared lifecycle also finished all 17 operations with
1,024 fresh proofs independently verified, 64 matching returned kernel values,
and the same model and answer after restart. It produced 1,012,130,665 proof bytes
and used 5,546.018 worker seconds during concurrent work. Its complete public
records are in `results/squared-compact/`.

[EXECUTED] A separate complete matched update-and-linear-query case returned
ciphertexts byte-identical to the original FIFO-expiry computation. Its one-class
producer took 45.05 seconds and consumer 14.20 seconds, with peak resident memory
of 186.7 MB and 181.1 MB respectively. The public FHE computation itself took
0.370 seconds. Proof verification therefore remains far more expensive than
recomputing this small function. Exact phase costs are in
`../matched_field/experiments/fifo-expiry-run001.json` and `../matched_field/COSTS.csv`.

[EXECUTED] The compact linear application also completed fresh setup, one teaching,
a complete 88-proof query and independent verification, then reopening. Negating
the fixed query vector produced exactly `[-13411,0,0,0,0,0,0,0]`, including the
8192-slot repetition check. Repeating its stable request in another process
returned the retained result with no new proofs or private reads. Its query took
470.88 seconds during concurrent work. This is a signed-arithmetic stress case,
not a language-utility observation; `results/signed-compact/` retains its commands,
outputs, fixed vector transformation and costs.

## What it accomplishes

[EXECUTED] A further complete implementation packs eight class centroids into
each ciphertext bank. Its separate nine-class workload completed eighteen
teachings, two FIFO expirations, three queries and a restart: **22 operations,
2,336 fresh proofs independently checked, 424,195,924 proof bytes, and 499.706
worker seconds**. All forty bank-lane values (including padding), class counts,
sums and exact rankings matched the reference. No proof phase failed.

| Packed query | Active classes / banks | Fresh proofs | Worker time |
|---|---:|---:|---:|
| Initial | 8 / 1 | 352 | 87.672 s |
| After later teaching and expiry | 9 / 2 | 704 | 162.888 s |
| Fresh query after restart | 9 / 2 | 704 | 120.437 s |

[DERIVED from implementation] Each fixed lane now contains the encrypted sum of
one class's live examples. FIFO expiry subtracts the exact oldest encrypted
contribution. A query yields up to eight class sums per proof batch; the reader
bounds each sum using its actual count, and ranking divides by that count. Every
occupied bank verifies before any bank is read. The layout has a separate genesis.
The frozen run and all command/output records are in `results/packed-matched/`;
the complete application is in `packed/`.

[EXECUTED: separate plaintext utility] Its nine authored held-out texts scored
8/9 before the ninth class had any training example and 9/9 after that class was
introduced. This is a different corpus from the two-class comparison above;
class availability and teaching change together. No broad accuracy or
controlled speedup claim follows from those numbers.

[EXECUTED] The local browser interface creates a learner, accepts text teachings
and queries, displays actual job progress and exact scores, and survives service
restarts. The matched instance was initialized through that interface before
running the fixed workload. Open `http://127.0.0.1:8848` while its local service is
running, or follow `README.md` to create another instance. Whole proof batches
are checked before the controller commits a teaching or invokes its reader.

[EXECUTED: browser text flow] After the packed workload, a new network teaching
and a new query were typed and submitted through the actual browser at
`http://127.0.0.1:8850`. The E5 encoder, encrypted update, two-bank query, full
consumer and reader completed. The visible answer was `network_transport` at
revision 19; all nine class sums and sixteen bank lanes matched an integer
reference computed before the private answer completed. The teaching job took
13.936 seconds and query 139.856 seconds. Public texts, vectors, job results,
reference and executed comparison are retained in `results/browser-packed/`.

[EXECUTED: plaintext utility] On twenty fixed, author-written held-out issue
texts, both linear and squared scoring achieved 20/20 initially, 19/20 after
later teaching, and 18/20 after expiry. Keeping the initial model unchanged scored
20/20. The experiment demonstrates continuing computation, not an accuracy gain.
These are small public-corpus observations, not general model performance; only
the four designated lifecycle queries were evaluated under encryption.

[EXECUTED: Lean] The additive matched-field proof package composes canonical
FIFO-update equations with all eleven BFV linear stages. It contains nonzero
joined witnesses and 29 guarded axiom footprints. This is an arithmetic theorem;
the native PCS/Fiat–Shamir and public IO reconstruction remain explicit premises.
See `../matched_field/formal/README.md` and its proposed companion-tree patch.

[OPEN] The full BFV reader key remains. The encoder and observations are public
in this experiment; setup, native parsing/NTT reconstruction, the controller and
proof backend remain trusted implementation boundaries. SQLite continuity does
not prevent a host from copying an entire instance. Neither this run nor its
Lean arithmetic bridge establishes master-read absence, whole-system
post-quantum security, or a numerical soundness level for the new proof profile.
