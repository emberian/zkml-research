# Fresh continuing Learn/Infer: completed two-class run

[EXECUTED] The single fresh run completed successfully on 2026-09-09 at
00:54:51 UTC (September 8 locally). Two supplied-text teachings were proved and
committed as global model revision 2. One new query was evaluated against both
active classes, with complete fresh arithmetic proofs accepted before either
full-reader call. Both decrypted results exactly matched plaintext arithmetic,
and the returned class matched the fixed intended label.

| Class | Kernel sum; one committed example per class |
|---|---:|
| card_arrival | 169,989,444 |
| cash_withdrawal_charge — returned and intended | 221,533,456 |

[EXECUTED] All 16 kernel lanes and both sums matched, including the seven empty
lanes per class. This is one functional example, not an accuracy estimate. The
fixed texts are in `fixture_builder/fixture.json`; the encoder made exactly one
fresh batch of those three texts. There was no tuning or example substitution.
The authoritative executed outcome is
[results/live001/RESULT.json](results/live001/RESULT.json), SHA256
`5a6d1e8faa8c21d6daf3717144eaacba04e546ac310126254e4d6b45dc0492de`.

| Measured quantity | Result |
|---|---:|
| Whole fresh flow, including setup, encoding, proofs and delivery | 1,429.111 s |
| New proof objects | 248 |
| Reused proof objects | 0 |
| Proof bytes | 304,995,885 |
| Proving, sum of backend timers | 880.313 s |
| Native witness emission, sum of process times | 269.999 s |
| Explicit prover self-verification calls | 248; 28.441 s |
| Fresh consumer verification calls | 248; 83.190 s |
| Peak prover RSS | 8,975,597,568 bytes |
| Full-reader calls, after public acceptance | 2 |
| Failed runtime steps / retries | 0 / 0 |

[DERIVED from executed records] **248 proof objects and 496 explicit verification
calls are different counts.** Each new proof had one self-check; the update
journal or final query gate then invoked a fresh native verifier for it. The
16 update proofs cover both components, all four primes and all 8,192 NTT
positions for each of two updates. The 232 class proofs comprise two complete
116-proof kernel computations. Every extension, tensor and rescale proof is new;
there is no saved-square dependency. Source cost records are enumerated in
[results/live001/COSTS.json](results/live001/COSTS.json); outer process costs are
in `launches/live001/run.command.json`. One proof host ran at a time, with four
Rayon workers. No extra benchmark or verification campaign followed.

[EXECUTED] The authoritative public acceptance was durably written at
`00:54:51.098852Z`. First receive started at `00:54:51.141335Z`, and the first
reader process started at `00:54:51.143531Z`. Its accepted model root is
`1c0de7daddd10b302641c9a10bf96d066ec3681a74d15c787fdc499f1aaeea82`.
The original acceptance is
`runtime/live001/queries/query01/public_acceptance.json`, SHA256
`89516fd324e7d10b99fb63e2d37d45becfc1f296e0a515edb78c8c7fba0110e7`;
a readable copy is [results/live001/public_acceptance.json](results/live001/public_acceptance.json).
The two teaching commit records are
`runtime/live001/teaching/{teach01,teach02}/committed.json`; their full receipts
are in the durable journal and the public export. The post-receipt answer is
[results/live001/answer.json](results/live001/answer.json).

[SOURCE capability] [live.py](live.py) supplies continuing `init`, `teach`,
`query` and `status` commands. Later calls consume the same accepted model;
they do not require another setup. `teach` proves `acc+fresh−old` using the
existing four-prime paired-MAC profiles and commits only after fresh
verification and the current-parent check. `query` requires every active class,
binds the common request/recipient/query to the accepted revision, and publishes
all-class acceptance before delivery. [README.md](README.md) gives the commands.

[SOURCE supported; not exercised here] Each class has an eight-entry cyclic
lane/FIFO memory. A ninth and later teaching subtracts the exact oldest
committed issued ciphertext, then inserts in its released lane. The existing
signed-update relation covers this arithmetic; FIFO/lane selection remains
controller TCB. This example exercised two initial insertions, no expiry,
one query and two active classes. Class declarations are fixed at setup;
request IDs must be fresh, and text features must fit the unchanged profile.

[SOURCE] The additive teaching/history composition is
[the BfvTeachingUpdate source](../../live_nonlinear_arithmetic/Compiler/BfvTeachingUpdate.lean),
including `updateSound`, `historySound`, `noExpiry` and `learnThenInferSound`.
It reuses the approved MAC templates and the completed
[Infer contract](../../full_bfv_infer_composition/Compiler/BfvInferContract.lean).
The only new native code is the teaching public reader/generic proof adapter,
built in 4.47 seconds. Existing Infer, square and rescale binaries, native
witness executor, parameter profile and proof backend were reused unchanged.
No handwritten AIR was introduced. `PIPELINE.json` pins the approved callables;
`BUILD.json` retains the new adapter build.

[SOURCE retention] [PUBLIC_EXPORT.md](PUBLIC_EXPORT.md) describes the explicit
whitelisted public export and replay commands. The export excludes the full
reader, private directories, decryption logs and answers; replay uses the
current approved workspace with caller-selected manifest/model/recipient pins.
[EXECUTED] The post-run export completed with 837 manifested public files
(692,386,462 bytes), manifest SHA256
`c56bd219677895eb684d54cc926b5de2b857e2533e139f44f527aed85c56e535`.
The bundle is retained at `public_bundle/live001/`;
[PUBLIC_BUNDLE.json](results/live001/PUBLIC_BUNDLE.json) gives its independent
model/recipient pins. No crypto replay was performed for publication.
Raw witness traces were compressed after successful
proving, then removed: 17,396,072,448 raw bytes became 1,379,378,855 bytes in
ignored `work/`. Existing proof/result files remain retained. No private file
is needed to verify the public bundle.

[SCOPE] This is a fresh two-class nonlinear learning/query flow with a
continuing local interface, under explicit public encoder, encryption/initial
setup, key-membership, parser, seed expansion, NTT/linear-map, journal and proof
backend TCB. The full reader survives. It is not a private resident,
cryptographically restricted recipient, shipped system, BFV security/noise
proof, or general utility benchmark. Setup and text issuance are trusted;
the two actual post-setup arithmetic updates and both query computations were
proved and bound to the accepted model. No further cryptographic execution is
needed for this milestone.
