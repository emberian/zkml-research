# Fast-run public query dataset

[EXECUTED] The two actual class-query proofs from `proved_journal/fast_live_successor/results/fast001` both verify through the **unchanged existing JavaScript consumer and IR2 WASM module**. This is the same recorded run whose [source report](../../proved_journal/fast_live_successor/README.md) reports 21.20 seconds for the live workload. No proof, encryption or WASM build was performed here; the original `gated001` package remains frozen.

| Class | Saved proof bytes | Node WASM check |
| --- | ---: | ---: |
| `card_arrival` | 842,828 | Accepted, 1,523.82 ms |
| `cash_withdrawal_charge` | 842,376 | Accepted, 1,468.93 ms |

[EXECUTED] The single two-proof consumer invocation took 3,017.42 ms including local loading, pin checks and initialization. [Results](results/verify-node.json) and [command](results/node-command.json) record Node v26.8.1 WebAssembly on darwin/arm64, exit zero and empty stderr. These are shared-host Node observations, not browser or network timings. Exactly two proof verifications ran; no new changed-output control was run for this dataset.

## Exact site replacement

[SOURCE] Preserve the site's existing `query-consumer.js`, `shared-query-worker.js`, `verifier.js` and `pkg/` assets. Their copies here are byte-identical to the original frozen package. Replace only:

- `web/query-case.js` → the site's existing `proof/query-case.js` location.
- `fixtures/` → the same public query bundle directory used by the existing worker.

[SOURCE] The worker API is unchanged: `{id, bundleBaseUrl}` where the base ends with `/` and contains `fixtures/`. Its result must have both `verified === true` and `caseId === 'fast001-new-two-class-query'` to label this dataset as verified. The returned model root is `742982ae2402dc944074f0df249d412040ef273df392803810a92c434c807204`, revision 2. Both old and new runs use request ID `new-two-class-query`; the case ID and exact model/row/proof pins distinguish the saved runs.

[EXECUTED] Replacement case script SHA256: `d5b3af77c7c2cb379714f4e48501484e6d41e225f42f1b93b1824c95d3abc817`. The two proof hashes are `53ac28c1c9bd281f33bf1b8ddf7e54cb2ec4ba499d7685a79f56de1992b611bf` and `80ea26a3fcc615d5eb5ad69433c57f8d21d47236531878f0e2baff4acf3572bc`. `query-case.json` pins all exact public bytes and the unchanged backend fingerprint.

[EXECUTED] The complete replacement dataset (case script plus six fixture files) is **4,956,890 bytes**, or **2,439,929 bytes estimated gzip**. The template is unchanged; with that file already cached, changed files total 4,403,020 bytes, or 2,412,690 estimated gzip bytes. A fresh standalone load including verifier assets is 7,034,663 raw bytes, or 2,755,911 estimated gzip bytes. [DOWNLOADS.json](DOWNLOADS.json) retains individual counts; gzip estimates sum independent level-9 streams with `mtime=0` and are not observed HTTP transfer.

## Scope and provenance

[SOURCE] The unchanged Lean-emitted template proves the selected coefficient arithmetic of both ciphertext/plaintext products and their final subtraction, over 8,192 rows per class. It does not prove the encoder/NTT transform, decryption, winning class, authorization or current model head. Recorded request/model/ciphertext identities are fixed case context; this WASM consumer does not repeat the source journal's protocol checks. The template SHA256 remains `f42c5efcaa994656b0c9ef2d1270aa2d6eb7dae0e5ba85938d23dbb3dc46c10d`; the module SHA256 remains `96137c1ed0ad5fc7584ca72ef006ff70ac1951831408ee12ab22ce3879f6f908`. No new security claim follows.

[EXECUTED] `package_bundle.py` checks the frozen predecessor manifest, unchanged implementation pins and the source public acceptance/request/proof metadata before copying the public fixture bytes. `source_provenance.json` records those original paths and pins. `SOURCE_PINS.json` fixes all inputs of the retained run; its command was `python3 run_node.py`, launching `node web/verify-recorded-query.mjs` once with a 180-second cap. No private runtime path was followed. Browser QA, private reads, new proving, compilation and Web/Scry queries: zero.

[SOURCE] The complete directory also works standalone with the existing consumer/worker layout. Run `node web/verify-recorded-query.mjs` locally to check these public files without a verification server. `run_node.py` refuses to overwrite the retained run. `BROWSER_PACKAGE.json` seals this additive package; its predecessor manifest and files are preserved.
