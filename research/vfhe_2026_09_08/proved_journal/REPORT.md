# Actual proof-gated learner journal

[EXECUTED] `python3 -B research/vfhe_2026_09_08/proved_journal/run_demo.py`
completed with exit 0 on 2026-09-08 at 16:46:15 UTC. The public demonstration
took 1.696525500 seconds in one local run. It used the real event-65 ciphertexts
and existing 508,777-byte native proof; no new model, Lean or prover run was
needed. Exact subprocess commands and outputs are in
[`commands.json`](results/demo001/commands.json), and the actual service
requests/responses are in [`public_rpc.json`](results/demo001/public_rpc.json).

[EXECUTED] A deliberately changed candidate replaced `out.ct` with the canonical
`fresh.ct`, reconstructed the corresponding rows and updated its candidate hash
metadata. The service reached the actual native verifier with the original
proof, which exited 1 with
`InvalidOpeningArgument(InvalidPowWitness)`. The head remained at revision 0.
The candidate is explicitly labelled as a refusal fixture, not an authentic
learner event.

[EXECUTED] The real request then passed native verification and committed
journal revision 1, continuing the class accumulator from learner event 29 to
event 65. The native verifier reported 196,282,833 ns internally; its complete
process took 230,976,917 ns. The preceding native row reconstruction took
49,922,583 ns. These are one-run timings, not throughput or security claims.

[EXECUTED] A distinct request with the old parent refused as `stale_parent`.
After clean process shutdown and fresh-process reopen, the exact head matched.
The original request retried with the identical receipt, no new proof execution
and only one retained journal row. Both service processes exited 0 and removed
their socket. Input/source posthashes matched the launch values. The accepted
receipt records the authoritative parent check inside the write transaction;
concurrent contention was not separately exercised.

[EXECUTED pins] The retained public packet includes
[`source_pins.json`](results/demo001/source_pins.json),
[`genesis.json`](results/demo001/genesis.json),
[`receipt.json`](results/demo001/receipt.json),
[`final_head.json`](results/demo001/final_head.json) and
[`RESULT.json`](results/demo001/RESULT.json). Key byte identities are:

| Artifact | SHA-256 |
|---|---|
| service.py | `613b4fc26dad931db5cf50088c77dbaae7b2683607e5ded42e9e78e722369b17` |
| run_demo.py | `140ce44c4d137f03f06e3c566ddd66d75fd6707fd43d8d4bc76a718d94404831` |
| native verifier | `dd41ec2eac52bf35ff8a9c6e736fa4dcb7cb4ae41cec6bace5cf593a3cf87cc6` |
| approved template | `1afc2b3a120f59fdd79d273c6d32887373c5718225cb6e94b82a7231010c3aa7` |
| proof | `acf747cf42eff8171b2b774abae5572e8d7bdb7ace144754c7605128c15e5ba6` |
| actual output ciphertext | `67d13c84cc4b131b4011eacbf55dfe86c22093125ba7f45e6e9b84413429ab54` |
| RESULT.json | `ffbb1736cc1515773b74fe72000bd58046a882fcd6beaff1d0e674f3a6b7544b` |

[SOURCE scope] This is an executed durable protocol gate over the selected
generated arithmetic proof. Metadata binding, parsers, initial checkpoint,
issuer semantics and commit storage remain TCB. The existing full BFV reader
survives. There were zero private comparisons. It does not prove FIFO selection
or the text encoder and makes no confidentiality claim. See [SCOPE.md](SCOPE.md)
and the [reusable CLI](README.md).

