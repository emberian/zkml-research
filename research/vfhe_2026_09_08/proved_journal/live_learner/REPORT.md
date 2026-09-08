# New text reaches a proved commit and a real query

[EXECUTED] The existing ML Python environment ran
`research/vfhe_2026_09_08/proved_journal/live_learner/run_demo.py` with exit 0,
completing at 2026-09-08 17:15:40 UTC. Total execution took 42.368429084 seconds.
Exact argv and the fresh fixture are retained in
[`command.json`](results/live001/command.json).

[EXECUTED] The new teaching text was “My replacement bank card still has not
arrived after three weeks.” Its class was `card_arrival`. The distinct query
was “The bank mailed my new card, but I am still waiting for it.” The encoder
loaded the locally cached E5 model once and executed two new-text forward
batches. Total forward time was 0.558597542 seconds; no coordinates clipped.
The subsequent integer comparison reused those two local feature-cache entries.

[EXECUTED] A fresh isolated BFV key pair and explicit two-class zero checkpoint
were created. One issuer encryption and actual `host-learn` produced a new
candidate. The production pipeline generated a fresh 503,998-byte proof in a
38.620449500-second pipeline: 36.469636834 seconds in Lean witness emission,
1.976745750 seconds in the proof command and 0.127300042 seconds in fresh
verification. The template remained the approved expiry template. The proof
was not event65/event66's saved proof. See
[`pipeline_result.json`](results/live001/pipeline_result.json), command/log files,
[proof](results/live001/proof.bin) and [exact public case](results/live001/case/source_event.json).

[EXECUTED] Staging and proof generation left the accepted head at revision zero.
A candidate with a substituted proposed model root was refused as
`proposed_model_root`, again leaving the head unchanged. The real request then
passed journal verification and committed revision one, changing only
`card_arrival`. The other declared class, `cash_withdrawal_charge`, remained
empty at its original zero head. A fresh adapter object recovered the exact
accepted state from the journal; the issuer's eager model state remained empty.

[EXECUTED] The query evaluated both accepted class ciphertexts through actual
`host-infer` operations, completed the public record, and then performed two
actual full-reader decryptions. The active class's score was 241,320, matching
the direct integer dot product computed afterward. Ranking selected
`card_arrival`; with one active class, this is not an accuracy benchmark.
The proof-pipeline process group was absent and all public proof/commit/query
work completed before private receipt.

[EXECUTED evidence] The packet retains
[the failed proposal](results/live001/failed_proposal.json),
[committed response](results/live001/committed.json),
[journal history](results/live001/history.json),
[public query completion](results/live001/public_query_complete.json),
[actual answer](results/live001/query.json),
[public operation log](results/live001/public_operations.jsonl),
[encoder statistics](results/live001/encoder_stats.json),
[final result](results/live001/RESULT.json), and
[public case export](results/live001/public_case_export.json).
The public BFV log records one keygen, one encryption, one update, one query
encoding, two host inferences and two reader calls. Reader scalar stdout is
omitted from that operation log; the attributed application answer/comparison
is separately retained.

| Artifact | SHA-256 |
|---|---|
| live.py | `fb9e743da3b8ccfdcf9586e829cc74c63f88233d2dcab3a48760f95c55593759` |
| run_demo.py | `d09ad299a18b7afa117d713a093d70636262908ca69d1841f1a7ab28bed21875` |
| fresh proof.bin | `db97c23396017219c22ee88487c320bba70ec6dccf172929e7900620ff68485f` |
| RESULT.json | `42eb6b1ef7489ca4e7657b77ad0cc18d4e913e7d604f7f5546d757a6d685ff81` |

[SOURCE scope] The executable joins new plaintext encoding, actual BFV
arithmetic, a fresh generated update proof, accepted-state visibility and a
real full-reader query. Encoder, initial checkpoint, FIFO, parser/protocol and
reader boundaries remain explicit; the query has no new proof and there is no
confidentiality claim. [Scope](SCOPE.md) and [reusable command](README.md).

