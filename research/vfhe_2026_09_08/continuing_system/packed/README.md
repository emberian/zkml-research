# Packed class-centroid learner

[DERIVED: implementation] `core.py` is a complete separate continuing learner.
Each ciphertext bank contains up to eight class centroids, one per fixed SIMD
lane. Supplied class order determines `bank=index//8`, `lane=index%8`; it is bound
at the distinct `packed-class-centroid-genesis-v1` genesis. No old instance is
converted. The public feature contract remains 576 bounded integer coordinates.

Each class retains its own FIFO of eight encrypted contributions. Teaching places
the fresh contribution in that class's fixed lane and proves
`bank_out = bank_acc + fresh - expired`. Other lanes remain represented by their
existing contributions. Expiry removes that class's exact oldest ciphertext.
The shared matched-field consumer verifies all 32 update proofs before the
SQLite current-parent transaction commits the new bank ciphertext and class
queue to the journal/CAS.

For a query, each occupied bank gets a fresh complete eleven-stage linear
producer and independent consumer, 352 proofs per bank. Every occupied bank must
verify before **any** private read. The dedicated reader obtains eight signed
class sums, checks their exact counts and bounds `abs(sum) <= 20000*count`, and
requires zero sums for empty lanes. The application ranks active classes by exact
rational `sum/count`, breaking ties by label. It never squares the linear output.
Thus eight active classes in one bank require one complete proof batch; nine
classes in two banks require two. These counts follow the caller contracts, not
a timing measurement made by this lane.

## API and execution

```python
initialize(root, classes)  # Classes are ordered and fixed, up to 1024.
live = Live(root)
live.teach_vector(label, vector, text, request_id)
live.query_vector(vector, text, request_id)
live.head()
live.metadata()
```

`teach`, `query`, `prepare_query`, `accept_query`, `receive`, and `get_progress`
also retain the original app's call shapes. The public encoder is reused for text
calls. `init`, `teach`, `query`, and `status` are CLI subcommands of `core.py`;
`teach`/`query` accept `--vector-json`. Use the retained encoder virtualenv from
the parent application's `BUILD.md` for text input. The separate `workload/`
directory owns the runnable public-corpus lifecycle evaluation.

The head has `classes` (bank, lane, teach count, FIFO), `banks` (accumulator digest),
revision, genesis, and a model-root digest covering both maps. Results expose
class counts, signed sums, exact rational scores, ranking, the native bank reader
outputs, `accepted_all_banks`, receipts, and actual proof counts/bytes. They do not
reinterpret a bank lane as an individual retained example.

The implementation inherits the existing durable request/phase primitives.
Completed stable request IDs return their stored results, including after later
revisions. Changed input under the same ID is refused. Interrupted work can reuse
only complete whole phases; partial proof batches remain unaccepted. A changed
parent makes unfinished work explicitly stale. Reopening replays all committed
bank/class transitions and checks the current head. Keygen recovery preserves any
partial key material rather than silently creating another instance key.

`backend.py` reuses the existing pinned public matched caller in subprocesses and
the original issuer. It pins the dedicated packed reader and the shared source
files at genesis. `CONTINUING_PACKED_READER` and
`CONTINUING_PACKED_READER_PROFILE` may select the reader for a new instance.
Existing instances always reopen their recorded descriptors. Running parent app,
engine, profile, and prover sources were not changed for this implementation.

[EXECUTED] `CHECKS.json` records Python imports, actual source/reader/proof profile
byte-pin checks and the CLI entry point. This lane launched no keygen, encryption,
proof generation, or private read. Root owns the complete live workload.

[OPEN] This remains software-controlled full-reader custody. Public encoder and
inputs, setup/key validity, encoding and BFV correctness, exact class placement
and FIFO counts, native parsing/NTT reconstruction, journal/SQLite, and the native
proof backend remain explicit boundaries. Packing reduces complete proof batches
for this linear score; it does not establish hidden input acquisition, absence of
read authority, or a full native verifier-to-application theorem.
