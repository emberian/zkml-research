# Ring-matvec proof consumer

[EXECUTED] The saved **degree-4096, 64×8192 ring-matvec proof is accepted by
the actual verifier through WebAssembly**. The caller's changed expected output
is refused. The same module/API can run in a browser worker or directly in Node;
no server-side proof check or new prover is involved.

| Retained single-run measurement | Value |
| --- | ---: |
| Statement + proof + module file reads | 3.933 ms |
| WASM initialization | 13.627 ms |
| Genuine verification, including decoding/hashing/public preprocessing | 107.983 ms |
| Changed expected-output refusal | 31.052 ms |
| WASM module | 575,831 bytes |
| Public statement | 8,519,793 bytes |
| Complete proof | 4,433,968 bytes |

[EXECUTED] These are Node WebAssembly timings from the one retained
`node web/verify-fixture.mjs fixtures/matvec4096` run, not browser-network
measurements or a performance guarantee. `results/verify-wasm.json` records
both results; the command exited zero with empty stderr. The genuine call ran
the existing cryptographic verifier. The changed-output call was refused by
the existing caller-output equality gate **before** cryptographic verification;
it is not claimed as a PCS rejection. No extra test/prover cycle was performed.

## What runs

[SOURCE] `src/lib.rs` is a thin wrapper over the exact source supplied by
`../new_constructions/scaled/matvecmul`: `public_wire::decode_statement`,
`decode_proof`, `same_outputs`, and `Verifier::<4096,Field64_2>::preprocess/verify`.
The statement contains the caller-selected public matrix, ciphertext input and
expected output. Its checked header fixes the degree, Goldilocks base field,
quadratic extension and named WHIR configuration. The complete codec includes
both sumcheck claims and every round coefficient, output ciphertexts,
commitments, and all three required PCS openings with their claims and bytes.
No RNG state, saved transcript, prover-selected trusted dimension or verifier
configuration is imported. Public preprocessing is recomputed from the matrix.

[SOURCE security scope] The unchanged upstream WHIR configuration uses
**ConjectureList** and `SECURITY_LEVEL=100`. The result reads these constants
from the actual source. This configured level is not a certified security-bit
claim. The consumer adds no soundness theorem, encryption-security guarantee,
FHE correctness claim, or learner-authorization/FIFO claim. Rust, arkworks,
WHIR, the source codec, JS/WASM and runtime remain the implementation TCB.

## Compact JS API

Serve `web/` statically, keeping its `pkg/` directory alongside the JS modules:

```js
import { createVerifier } from './verifier.js';
const verifier = await createVerifier();
const result = verifier.verify({ statement, proof }); // two Uint8Array values
if (result.verified) {
  // The complete existing ring-matvec verifier accepted this selected statement.
}
```

[SOURCE] `createVerifier()` loads the WASM once and exposes `loadMs`. `verify`
returns `{verified, stage, verifier_ran, expected_output_matched, degree,
matrix_rows, matrix_columns, statement_bytes, proof_bytes, statement_blake3,
proof_blake3, whir_configured_security_level, whir_soundness_type,
security_scope, error}`. A runtime failure returns `verified:false` and
`stage:'runtime'`. The application must choose the statement it means to verify;
accepting arbitrary prover-selected matrix/output bytes changes the claim.

[SOURCE] The operation is synchronous. Use the supplied worker to keep UI
responsive, and discard a worker after a runtime trap:

```js
const worker = new Worker('./worker.js', { type: 'module' });
worker.onmessage = ({ data: { id, result, loadMs, verifyMs } }) => { /* render */ };
worker.postMessage({ id: 'matvec-1', request: { statement, proof } });
```

[SOURCE] Neither wrapper accesses secret keys or creates proofs. Either blob
is capped at 64 MiB; the shared codec additionally enforces canonical field
encodings, shape/count limits, all three PCS openings and no trailing bytes.
WebAssembly and Web Crypto are required in the browser. Results are actual
verification decisions; transport hashes are only artifact identities.

## Standalone use and build

```sh
node web/verify-file.mjs fixtures/matvec4096/statement.bin fixtures/matvec4096/proof.bin
```

[SOURCE] This standalone command invokes the same browser-target WASM, prints
the result and load/verification times, and exits 0 for acceptance or 1 for
refusal. The fixture runner additionally performs the one changed-output
control. Its edit changes the last caller-selected output coefficient to the
next canonical field value; the proof remains untouched.

```sh
sh build.sh
```

[SOURCE] Rebuilding requires `wasm32-unknown-unknown`, wasm-bindgen 0.2.127,
the dependencies pinned by this wrapper's `Cargo.lock`, and the prepared source
tree referenced by `Cargo.toml`. That source is reconstructible using
`../new_constructions/scaled/combined-matvec.patch` against upstream matvecmul
commit `00379074cad457367a86dde2ecee9d0f318a7e12`, as documented in its
`REPLAY.md`. The wrapper reuses those exact verifier/codec files without edits.
The first build seeded resolution from the original lock and added web-binding
dependencies; the final wrapper lock pins that complete build. Build outputs
stay here, and neither the previous browser verifier nor microsite was edited.

[SOURCE optional native entry point] `cargo build --release --locked --offline
--bin ring-verify -j 2` builds `target/release/ring-verify STATEMENT PROOF` from
the same core. This lane exercised the standalone JS/WASM path; it did not need
a native fallback or run another native verification cycle.

[EXECUTED handoff] `BROWSER_PACKAGE.json` freezes the static assets, actual
public fixture and result pins. Root owns microsite integration and any actual
browser-engine measurements. No WASM portability blocker remains.
