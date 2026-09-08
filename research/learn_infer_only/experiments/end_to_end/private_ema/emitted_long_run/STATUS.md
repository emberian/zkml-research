# Completed: emitted fixed-FFT full nonlinear workload

[EXECUTED] The existing frozen pipeline completed at 2026-09-08 08:10:00 UTC,
well before its 11:28:28 cutoff. All four stages and tool session 34769 exited
zero. All 384 Learn / 96 Infer events and their 480 independent-process byte
replays passed; all 960 hosts logged the expected fixed Dif4 plan. No failure,
timeout or cryptographic retry occurred.

[EXECUTED] The complete public seal at 08:09:57.111440 UTC preceded all 484
private checks (4 initial states, 384 primary Learn selected-route states,
96 primary Infer signs), which all matched. Replay plaintext was not separately
opened. The final reused-fixture target score remains 28/32; all checkpoints
scored 76/96. Public wall time was 9,687.877 seconds; private drain 2.436 seconds.
The unrestricted full-reader credential remains retained.

[EXECUTED collection] At 14:33:43 UTC, public-only post-completion collection
rechecked all 39 frozen files, 1,364 public artifacts and 480 full-byte pairs,
without any crypto invocation, private-file read or original-seal change.
The completed result is `summary.json`; final explanation is `REPORT.md`;
late public provenance is `collection.json`. `costs.csv` retains 1,848 process
rows. Raw public ciphertexts remain in ignored runtime storage.

[SOURCE pins] Original freeze SHA256
`6cc20a07b75330c2fb7aaa19a2021c6b495096c6b477b1554eb4a2a14c7943e8`;
original public seal SHA256
`b2f972552b5383d05207737939ddb2fe81e0c9ff68077104e13939f786dee566`.
All earlier completed/failed runs and the fixed runtime remain unchanged.

[SOURCE observability] The final public-worker progress snapshot retains static
false/zero public_phase_closed/reader_invocations fields despite phase=public_closed.
They are not final phase gates/counters. Authoritative completion is in
public_phase.json, public_seal.json, private_drain.json and pipeline.json.
Frozen sources and original records were preserved.
