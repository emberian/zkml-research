# Two recorded class computations, verified locally

[EXECUTED] Both real class-query proofs from `proved_journal/query_gate_successor/results/gated001` pass through the **unchanged existing IR2 WebAssembly verifier**. One changed public output is rejected by that same proof backend. This package adds public fixtures, an exported JavaScript consumer and worker entry points; it generates no proof and rebuilds no backend or WASM module.

| Recorded class | Proof bytes | Node WASM verification |
| --- | ---: | ---: |
| `card_arrival` | 842,647 | 1,493.54 ms, accepted |
| `cash_withdrawal_charge` | 842,459 | 1,446.51 ms, accepted |
| `card_arrival`, output digit changed 18 → 19 | same proof | 1,422.43 ms, rejected |

[EXECUTED] The exported two-class consumer completed in 2,956.62 ms, including local-file loading, pins and initialization. These are single observations in Node v26.8.1 WebAssembly on darwin/arm64, **not browser-engine or network measurements**. [The execution result](results/verify-node.json) records every result, identity and duration; [the command record](results/node-command.json) records exit zero, empty stderr, unchanged inputs and the 180-second cap. The complete process took 4.483 seconds.

## What the accepted statement means

[SOURCE] Each class statement has 8,192 public rows of width 57. The [frozen Lean-emitted query relation](../query_arithmetic/README.md) constrains both ciphertext/plaintext products and their final subtraction. For each serialized NTT slot and prime it enforces

```
O = ((A * Pplus) % q + q - (A * Pminus) % q) % q.
```

[SOURCE] This consumer checks that coefficient relation using the unchanged shared `FixedPublicPreprocessing` IR2 verifier. It does not decode ciphertext blobs, prove the query encoder or NTT transform, decrypt, prove the winning class, authorize a request, or establish the current model head. The recorded request ID, revision, model root, query and ciphertext hashes are **pinned context for this saved case**. Their original service checks remain in the predecessor journal package. No new security estimate follows from verification or this adapter.

[EXECUTED] `web/query-case.js` fixes the application-selected template, both exact row files, both proof files, request envelope and WASM hashes. The core independently checks the approved template hash and constructs its statement using the supplied rows. Both real verifier acceptances and their expected backend/shape identities are required for `verified: true`. The template SHA256 is `f42c5efcaa994656b0c9ef2d1270aa2d6eb7dae0e5ba85938d23dbb3dc46c10d`; the unchanged 2,063,586-byte WASM module is `96137c1ed0ad5fc7584ca72ef006ff70ac1951831408ee12ab22ce3879f6f908`. The complete unchanged backend fingerprint is in `query-case.json` and every result.

[EXECUTED] The changed-output control changes row 0, column 43, from 18 to 19 and calls the frozen generic verifier directly with the original proof. It reaches `proof rejected: IR v2 verification failed: InvalidOpeningArgument(InvalidPowWitness)`. The fixed-case application would reject those altered bytes earlier at the transport pin; the separate control deliberately bypasses that transport layer to exercise proof rejection.

## Site integration without duplicate verifier assets

[SOURCE] Keep the existing site's frozen `proof/verifier.js` and `proof/pkg/` assets. Copy only these three new modules into that same `proof/` directory:

- `web/query-consumer.js`
- `web/query-case.js`
- `web/shared-query-worker.js`

[SOURCE] Copy this package's `fixtures/` directory under a static bundle directory, for example `query-bundle/fixtures/`. Start the shared worker with a base URL **ending in a slash**:

```js
const worker = new Worker('./proof/shared-query-worker.js', { type: 'module' });
worker.onmessage = ({ data }) => {
  if (data.type === 'progress') { /* data.progress: stage, label, completed, total */ }
  if (data.type === 'result') {
    // Show success only when data.result.verified === true.
    // Suggested label: "Both class computations verified".
    // Scope: exact query arithmetic; no encoder, decryption or authorization proof.
  }
};
worker.postMessage({
  id: 'both-class-computations',
  bundleBaseUrl: new URL('./query-bundle/', document.baseURI).href,
});
```

[SOURCE] This worker loads the existing sibling `pkg/vfhe_browser_verifier_bg.wasm`, then loads the six pinned fixture files relative to `bundleBaseUrl`. The consumer hashes every loaded payload before use. Shared module imports resolve to the existing sibling `verifier.js` and `pkg` wrapper. All verification runs on-device; the server supplies static public bytes only. The shared worker's source syntax was checked; **its browser execution was not performed here**. It invokes the same exported consumer exercised with a local byte loader in Node.

[SOURCE] Alternatively copy this entire package, preserve `web/` and sibling `fixtures/`, and use `web/query-worker.js` with `{id}`. Direct callers can import `verifyBothClassComputations` from `web/query-consumer.js`; options are `{loadBytes, onProgress}`. The optional byte loader receives only fixed manifest-relative paths and returns `Uint8Array` or `ArrayBuffer`; the default fetches this standalone bundle. Results contain `verified`, `cases`, case/context identities, timings and any error. WebAssembly and Web Crypto are required; verification is synchronous inside the worker.

## Transfer size and retained evidence

[EXECUTED] [DOWNLOADS.json](DOWNLOADS.json) lists exact asset bytes and reproducible estimates from independent gzip level-9 streams. It does not measure a deployment's HTTP compression or caching.

| Delivery | Raw bytes | Estimated gzip bytes |
| --- | ---: | ---: |
| Standalone first load | 7,034,498 | 2,758,993 |
| New assets when existing verifier files are reused/cached | 4,962,403 | 2,445,196 |
| Shared deployment, existing verifier files also uncached | 7,035,436 | 2,759,372 |

[EXECUTED] The existing reused verifier assets total 2,073,033 raw bytes (314,176 estimated gzip bytes). The six public fixture files total 4,952,910 raw bytes. No new copy of the WASM module is needed in the shared deployment.

[SOURCE] `source_provenance.json` identifies the original frozen package and every copied public source; `SOURCE_PINS.json` fixes the consumer and public inputs used by the retained Node run. The later additive shared worker has its own source pin and syntax-check record in `results/shared-worker-syntax.json`. `BROWSER_PACKAGE.json` seals the final public handoff. No predecessor files were edited and no persistent private state or key files were read. Web/Scry query counts for this packaging task: 0/0.

[EXECUTED] Retained command was `python3 run_node.py`, which launched `node web/verify-recorded-query.mjs` once. A standalone consumer can replay the latter command locally using only this public directory. `run_node.py` deliberately refuses to overwrite the saved execution. `package_bundle.py` documents the source-copy/pin procedure; `seal_package.py` records runtime sizes and the final package manifest.
