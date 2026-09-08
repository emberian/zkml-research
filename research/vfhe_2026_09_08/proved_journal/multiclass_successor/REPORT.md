# Two actual class updates under one durable model head

[EXECUTED] `run_sequence.py` completed with exit 0 at
2026-09-08 17:01:51 UTC. In 1.656366125 seconds, it imported an explicit
two-class checkpoint64, verified the real event65 and event66 proofs, committed
both updates, refused a stale parent, reopened the service and retried a
historical request. This is a single saved-input integration run, not a new
training/proof-generation run or throughput claim.

| Global learner event | Journal revision | `card_arrival` head event | `cash_withdrawal_charge` head event |
|---|---|---|---|
| 64, imported | 0 | 29 | 30 |
| 65, proof accepted | 1 | 65 | 30 |
| 66, proof accepted | 2 | 65 | 66 |

[EXECUTED] Each transition preserved every unselected entry in this two-class
model. Receipts bind the previous and next model roots and the selected class.
The event66 candidate prepared against checkpoint64 refused as `stale_parent`
after event65 committed, leaving the head unchanged. Its newly prepared request
against the current global parent then accepted with the production event66
proof. A fresh process recovered exactly revision 2, both class heads and the
final model root. Retrying event65 returned the same historical receipt without
new proof execution; the journal still contained exactly two receipts.

[EXECUTED] Event65 native proof verification reported 110,469,625 ns internally
and took 134,204,958 ns as a subprocess. Event66 reported 100,888,292 ns and took
124,803,917 ns as a subprocess. Their native row reconstructions took
32,859,167 ns and 30,386,833 ns. Each proof covers 8,192 rows / 16,384 RNS
equations. Both service processes exited 0 and removed the socket. Exact source
and input posthashes matched, including the preserved single-class source and
result.

[EXECUTED evidence] See [commands](results/sequence001/commands.json),
[public RPCs](results/sequence001/public_rpc.json),
[imported checkpoint](results/sequence001/checkpoint64.json),
[genesis](results/sequence001/genesis.json),
[event65 receipt](results/sequence001/receipt65.json),
[event66 receipt](results/sequence001/receipt66.json),
[final global head](results/sequence001/head66.json),
[source/input pins](results/sequence001/source_pins.json), and
[result](results/sequence001/RESULT.json).

| Byte artifact | SHA-256 |
|---|---|
| service.py | `f36e386933ed6b97a0c90db2f66dd75afcec8958163ec0a6c73b24faa15e4340` |
| checkpoint_from_records.py | `8df102c0643fe45c63119a7891cd33d1878fa4ddf1bdcae7670c0ad5e8e29487` |
| run_sequence.py | `acdf37f60f6ac256f44a4bd86d081ea5444d120cb9063e96818d4d78c5c86606` |
| checkpoint64.json | `351741c3489015a489f98241b7d0bc3b2847af9995f3140d3e38653a72533178` |
| event65 proof | `acf747cf42eff8171b2b774abae5572e8d7bdb7ace144754c7605128c15e5ba6` |
| event66 production proof | `365006cd229920b4cda7118fa51f89cc012124e8681eb2e7b75291e402407a01` |
| RESULT.json | `52da49324100fb997b2428a3c4f6732fbfe3c10f76f31a812f170ddb7dda6f8b` |

[SOURCE scope] The imported two-class history is recorded provenance, not
proved history. Only the two subsequent selected arithmetic transitions are
proof-gated here. The model-map/parent/commit binding is explicit protocol TCB;
the full BFV reader survives. There were no secret-key reads or private
comparisons. See [SCOPE.md](SCOPE.md) and the [reusable CLI](README.md).

