# Prepared public-seed durable journal join — unlaunched

[EXECUTED status, 2026-09-08 14:38 UTC] Source preparation completed; no cryptographic
run, sampling, model forward or service has launched. The initial inventory found no
runtime or reports directory. The only subsequent operational command was `driver.py
prepare`, which reported 44 source pins, 79 signature-library files, zero crypto commands
and zero services. Reports now contains only the preparation's execution_pins.json.
Runtime, LAUNCH.json, PRELAUNCH_REVIEW.json and RUN_AUTHORIZATION.json remain absent.
Root explicitly prohibited today's 45-minute run after the usage reset at14:31UTC.

[EXECUTED freeze] PREPARATION_MANIFEST.json SHA256
`110901f488ca678d4c6cf6c0db6dbdc4344d736ce8c539f0d15210cea9834e7d` pins47 files.
SOURCE_PINS.json SHA256 is
`ed78111662429aecadfe206244c458c4c97a1d7ded3032191f8a1ccdaf0edf24`;
reports/normal_001/execution_pins.json is
`31548249055545245b75068c41199b5fe9c62dccfc40473a5ec048e5b769315b`;
CONTRACT.md is `61b093868ae333e67862b8dd4d51cda09f1849e9e95ccbe74160e59a3520f6b7`.
The36 unchanged dependency copies include the complete nested primitive seed packet;
its original manifest remains `be861661…`. File modes and original paths are recorded.
All fixed source files parse; the public index schedule has37 events, reopen revision18,
historical retry of revision2 and exact c01 expiry at Learn33.

[DERIVED useful new seam] The primitive seed adapter has no durable journal, and the
previous journal used direct accepted-value sampling. New setup_join.py substitutes the
unchanged seed wrapper and creates public_seed_setup in genesis. That extension binds
full transcript/registry/announcements/context/verification identities, seed bytes/suite/
cap/domain digest, complete setup source_identity, the nested seed manifest and new join
inventory. Existing genesis hashing carries these identities into signed authorizations,
receipts and installed heads. No journal, host or crypto module changes.

[DERIVED phase design] driver.py's public worker runs the fixed33/4/1 workload, orderly
reopen at revision18, one exact historical Infer retry, all37 arithmetic replays, complete
seed replay and source/log/history/storage checks. It closes services and the public host.
The separate public_close.py checks signed histories and both closed public SQLite stores,
rehashes CAS inventories and binds the saved full arithmetic replay. launch.py waits for
each process group to disappear, seals public reports, and only then permits the private
worker's single four-answer drain and direct integer comparisons. The outer watchdog
interrupts blocking inherited RPC/subprocess waits at2700seconds; bounded cleanup checks
group existence independently of leader exit and escalates if needed. Failure never
permits another phase. These are source plans, not runtime-tested behavior.

[REPORTED partial independent review] The reviewer inspected an earlier six-file wrapper
snapshot plus36 copied dependencies,12 nested pins and33 ASTs, finding the setup binding
and private-phase split coherent. Its [report](../../../../../adversarial_review/public_seed_journal/REPORT.md)
SHA256 is `7a8bd2d2dafd1cca64597124d1dc7c399825b57325b28f6b102043df43e07d65`;
review manifest is `6122f2512d63e1ffeebbce5a9be163cc606120b8560b98b8e99a7150a4dfaaa6`.
That frozen review explicitly does **not** accept final launch.py, public_close.py or
the final preparation gate. The reviewer was reassigned to the completed TFHE evidence
review. Do not treat its partial disposition as an accepted prelaunch gate.

[OPEN required before execution] A future reviewer must inspect the exact47-file freeze,
especially whole-group cleanup, phase gating, postshutdown public SQLite/CAS verification
and the four-answer private join. No future runtime is justified by source parsing alone.
After acceptance, the reviewer gate must bind both source and execution inventories:

```json
{
  "disposition": "accepted",
  "root_notified": true,
  "source_pins_sha256": "ed78111662429aecadfe206244c458c4c97a1d7ded3032191f8a1ccdaf0edf24",
  "execution_pins_sha256": "31548249055545245b75068c41199b5fe9c62dccfc40473a5ec048e5b769315b",
  "review_report_path": "ABSOLUTE_REVIEW_REPORT_PATH",
  "review_report_sha256": "EXACT_REVIEW_REPORT_SHA256"
}
```

[OPEN authorization] Separately, a new explicit root/user instruction must authorize
the run. RUN_AUTHORIZATION.json binds `launch_authorized: true`, the exact execution-pins
hash and timezone-aware `not_before_utc`/`not_after_utc` strings. The launch time must
leave the full45-minute budget before the authorized window closes. Neither gate exists.
The sole future entry point is `python3 -B launch.py` from this directory; there are no
alternate path/seed options. Do not run driver public/private directly or regenerate the
frozen preparation if an environment pin drifts; review a clearly separated successor.

[DERIVED limitations] This is still a known public integer fixture with all16 full
per-input recipient row credentials, including expired inputs. Timing-bearing verification
and validation records are committed into genesis, outside the conditional classical
ROM/DDH transcript claim. SHAKE instantiation, honest independent registration, Ed25519,
compiled runtime correspondence, full credential authority and shared-OS limits remain.
No selected-only release, new utility, OS isolation, hidden nonlinear learning or PQ
claim follows. Completed primitive and its two review packages remain byte-frozen.

[EXECUTED search accounting] This preparation used no network, web, Scry, crypto or
model query. Root owns shared ledgers and commits.

[EXECUTED final integrity] PREPARATION_RECHECK.json passes: all 47 frozen files, 36 dependency copies, 44 runtime pins, 79 signature-library files and 35 Python ASTs; all 167 completed primitive files and both completed review inventories remain unchanged. Runtime and both gates remain absent. An initial read-only collector used an incorrect review-directory parent index and failed before completion; preparation_recheck_001_source.py and preparation_recheck_001.json preserve it. Only that unfrozen collector path was corrected; the frozen source packet was unchanged. The repeated read-only collection passed.
