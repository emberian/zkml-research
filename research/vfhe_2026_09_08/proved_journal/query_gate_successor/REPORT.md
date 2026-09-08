# A fresh two-class query is proved before private receive

[EXECUTED] The retained `run_demo.py` command exited 0 at
2026-09-08 17:58:37 UTC. The complete fresh run took 306.241376583 seconds:
isolated key/zero checkpoint, two genuine text teaches with new update proofs,
a new query with two new joined arithmetic proofs, one coverage refusal,
public acceptance, then actual private receive. Exact input texts and argv are
in [command.json](results/gated001/command.json). The already received live001
predecessor query was preserved and was not relabelled as proof gated.

[EXECUTED] New teaching examples populated `card_arrival` and
`cash_withdrawal_charge`, one committed observation each. Their update-proof
pipelines took 37.554346791 and 43.142441333 seconds. Both updates committed
under the existing model-map journal, yielding global revision 2. The new query
was “Why was I charged a fee for taking cash out at an ATM?” The cached E5
model was loaded once for three new encoded texts; no benchmark or model
tuning was run.

| Active class | Joined query proof bytes | Complete query-proof pipeline |
|---|---:|---:|
| `card_arrival` | 842,647 | 112.492746125 s |
| `cash_withdrawal_charge` | 842,459 | 107.790803834 s |

[EXECUTED] Both class pipelines generated fresh proofs and independently
verified them. Each covers all 8,192 rows of the joined relation: both signed
ciphertext/plaintext products and their final subtraction. The gate then
reconstructed each case again from exact ciphertext/query bytes and performed
fresh native verification against the approved template. Those final verifier
calls reported 136,758,292 ns and 143,504,709 ns internally. These are one-run
measurements, not security or throughput claims.

[EXECUTED] A proposal that omitted the active `cash_withdrawal_charge` class was
refused as `active_class_coverage`. It created no public acceptance and left
the model head unchanged, with zero reader calls. The complete proposal then
passed both native verifiers, the exact current-head check under the journal
write lock, and durable public acceptance. The record includes the common
query, model root/revision, recipient/request binding, committed counts and
both accepted accumulator/output/proof identities. Every public subprocess
group was absent before proceeding.

[EXECUTED] Only after that acceptance did the adapter perform its first two
full-reader decryptions for this new query. The actual scores were 238,227 for
`cash_withdrawal_charge` and 211,756 for `card_arrival`; the answer selected
`cash_withdrawal_charge`. Both matched the direct integer dot products computed
afterward. The accepted model stayed at revision 2 and a fresh adapter recovered
the exact head. This is a two-populated-class semantic/mechanics fixture, not
an accuracy benchmark.

[EXECUTED evidence] Public evidence includes
[query genesis](results/gated001/query_genesis.json),
[model history](results/gated001/model_history.json),
[request](results/gated001/request.json),
[coverage refusal](results/gated001/coverage_refusal.json),
[public acceptance](results/gated001/public_acceptance.json),
[actual answer](results/gated001/answer.json),
[later integer comparison](results/gated001/integer_comparison_after_receive.json),
[operation log](results/gated001/public_operations.jsonl), and
[result](results/gated001/RESULT.json).
`class0/` and `class1/` retain each exact public case, proof and command logs;
`teach0/` and `teach1/` retain the new update-proof records. No private key,
feature cache or large witness trace was exported. Six query-gate dependencies
and ten underlying live dependencies retained their exact pinned bytes.

| Artifact | SHA-256 |
|---|---|
| gate.py | `fb1edbc07ca0be001ec226eac1834e8bc5f3fbc11d24197d2d820c8ff5b4e965` |
| run_demo.py | `141e36d92f1489b41de3d5c6fd968cac3a5f4dd07a687f64d92fc5aefcaf2faa` |
| class0 query proof | `bbd292c8cc76f5d2cadb832f9f380cabd41185b202683940281098f0560cc8a7` |
| class1 query proof | `1c49d589330a34544228c1c6b50750187cf71d54b5a57cfefbcbf41cb261f8ef` |
| public_acceptance.json | `91243b8c25522ab66981346f843aa266d236673bb94efbcacd0bdc39ba2f0c48` |
| RESULT.json | `5833c3526a1330b74f62d5e4a35dc888bc91553c8c4c7b2d892231805564f298` |

[SOURCE scope] Plaintext encoding, query/NTT parsing, application metadata and
class coverage, durable global-head checks, BFV decoder/ranking and shared OS
remain TCB. The proof establishes selected ciphertext arithmetic; the adapter
orders the actual receive behind all required acceptances. The full reader
survives, and there is no decryption restriction or confidentiality claim.
[Scope](SCOPE.md), [runnable command](README.md).

