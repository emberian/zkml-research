[SOURCE-ONLY, not executed during the live run] `export_public.py` adds an explicit public export and public replay command without changing the approved profile, driver, instance or proof sources. Preparation compiled the new Python source and displayed its CLI help. No export, proof replay, encoder operation or private read was run by the helper's author.

After the instance is idle, export to a fresh directory outside that instance:

```sh
python3 export_public.py export /absolute/live-instance /absolute/new-public-bundle --query query01
```

Omit `--query` to include all accepted queries. Pending or failed queries are not implicitly exported. The command acquires the existing adapter lock in shared, nonblocking mode and opens the SQLite journal read-only. An active writer causes refusal rather than a pause or retry. It exports the exact committed head and complete retained teaching-receipt chain as JSON; it never copies the database. Historical accepted queries are checked against their own committed revision and every class active at that revision, even if the exported head has since advanced.

[SOURCE] The fixed whitelist includes public setup key/evaluation key/parameters/literal-zero ciphertext; committed teaching requests/receipts/cases and eight proof pairs per update; selected query requests/public acceptances and each active class's three public case schemas and116 proof pairs. Only `proof.bin` and `proof.json` are copied from proof folders. Public case rows, ciphertexts and exact public query vectors are included. No recursive source-directory export is used. Reader keys, `.private`, encoder caches, raw witness files, read logs, answer files and receive-phase files are excluded. Replay checks the exact same file whitelist before reading bundled payloads.

The export prints the manifest, genesis, head and recipient digests. Retain those caller-selected values independently. To replay from the bundle, choose another fresh directory and supply all four values:

```sh
python3 export_public.py replay /absolute/new-public-bundle /absolute/new-public-replay \
  --manifest-sha256 MANIFEST_DIGEST \
  --genesis-sha256 GENESIS_DIGEST \
  --head-sha256 HEAD_DIGEST \
  --recipient-id RECIPIENT_DIGEST
```

[SOURCE] Replay reconstructs the public hash/parent/FIFO metadata and derives exact update and query expected bindings. It requires every retained update and every active class of each selected query, then calls the unchanged `pipeline.verify_update` and `pipeline.verify_infer` APIs. It does not generate new proofs, encrypt, decode with a reader key, or rerun an encoder. The expected manifest digest also pins the selected query identities, rather than accepting a substituted query from an untrusted bundle.

[LIMIT] The bundle is an unsigned snapshot, not a new source of model or recipient authority. The existing full BFV reader remains outside it. The initial live demonstration has two classes and one accepted query; the continuing controller permits1–1024 declared classes and eight observations per class, while the exporter requires the complete active set for each included query. Public setup/key validity, feature issuance, FIFO/lane/controller policy and parser/NTT/backend assumptions retain their existing scope. `DEPENDENCIES.json` records the current workspace's pinned sources, native executables, templates and linear plan. They are not vendored here: this is not a standalone portability claim. No private-state or natural-language ambiguity claim follows from excluding local private files.
