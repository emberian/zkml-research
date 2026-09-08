// Actual browser-target WASM API under Node. One genuine and one output refusal.
import { readFile } from 'node:fs/promises';
import { resolve, join } from 'node:path';
import { createHash } from 'node:crypto';
import { createVerifier } from './verifier.js';

const directory = resolve(process.argv[2] ?? new URL('../fixtures/matvec4096/', import.meta.url).pathname);
const started = performance.now();
const [manifestBytes, statementBytes, proofBytes, wasmBytes] = await Promise.all([
  readFile(join(directory, 'fixture.json')), readFile(join(directory, 'statement.bin')),
  readFile(join(directory, 'proof.bin')), readFile(new URL('./pkg/ring_browser_verifier_bg.wasm', import.meta.url)),
]);
const fileReadMs = performance.now() - started;
const manifest = JSON.parse(manifestBytes);
for (const [name, bytes] of [['statement.bin', statementBytes], ['proof.bin', proofBytes]]) {
  if (createHash('sha256').update(bytes).digest('hex') !== manifest.files[name].sha256) {
    throw Error(`fixture bytes changed: ${name}`);
  }
}
const verifier = await createVerifier(new Uint8Array(wasmBytes));
const statement = new Uint8Array(statementBytes);
const proof = new Uint8Array(proofBytes);
let mark = performance.now();
const genuine = verifier.verify({ statement, proof });
const genuineMs = performance.now() - mark;
if (!genuine.verified || !genuine.verifier_ran || !genuine.expected_output_matched) {
  throw Error(`genuine proof failed: ${JSON.stringify(genuine)}`);
}
// The complete public wire ends with the last expected-output base-field value.
// Change it canonically; this is a test input edit, not a verifier/decoder copy.
const changed = statement.slice();
const view = new DataView(changed.buffer);
const offset = changed.length - 8;
const original = view.getBigUint64(offset, true);
view.setBigUint64(offset, (original + 1n) % 18446744069414584321n, true);
mark = performance.now();
const changedOutput = verifier.verify({ statement: changed, proof });
const changedOutputMs = performance.now() - mark;
if (changedOutput.verified || changedOutput.stage !== 'expected_output' || changedOutput.verifier_ran) {
  throw Error(`changed output did not hit caller-binding refusal: ${JSON.stringify(changedOutput)}`);
}
console.log(JSON.stringify({
  claim: 'EXECUTED unchanged complete verifier/codec through browser-target WASM API',
  environment: 'Node WebAssembly runtime; timings are not browser-network measurements',
  fileReadMs, moduleInitMs: verifier.loadMs, genuineMs, changedOutputMs,
  wasmBytes: wasmBytes.length, statementBytes: statement.length, proofBytes: proof.length,
  genuine, changedOutput, mutation: { byteOffset: offset, field: 'last caller-selected expected output coefficient' },
  negativeScope: 'The existing caller-output equality gate refuses before the cryptographic verifier; it is not claimed as a PCS rejection.',
  newProofsGenerated: 0,
}, null, 2));

