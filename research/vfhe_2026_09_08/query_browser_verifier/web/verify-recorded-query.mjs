// A Node WebAssembly execution of the same exported consumer; no proof generation.
import { readFile } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import { QUERY_CASE } from './query-case.js';
import { verifyBothClassComputations } from './query-consumer.js';
import { createVerifier } from './verifier.js';

const loadBytes = async path => {
  if (!Object.hasOwn(QUERY_CASE.files, path)) throw new Error(`Unapproved fixture: ${path}`);
  return new Uint8Array(await readFile(new URL(`../${path}`, import.meta.url)));
};
const progress = [];
const genuine = await verifyBothClassComputations({ loadBytes, onProgress: event => progress.push(event) });
if (!genuine.verified || genuine.cases.length !== 2 || !genuine.cases.every(item => item.accepted)) {
  throw new Error(`Both recorded class proofs must verify: ${JSON.stringify(genuine)}`);
}

// This control intentionally uses the unchanged generic core directly. The exported
// fixed-case consumer would reject changed rows at its transport hash first.
const first = QUERY_CASE.cases[0];
const template = new TextDecoder().decode(await loadBytes(QUERY_CASE.templatePath));
const changedRows = JSON.parse(new TextDecoder().decode(await loadBytes(first.publicRowsPath)));
const originalDigit = changedRows[0][43];
changedRows[0][43] ^= 1;
const proof = await loadBytes(first.proofPath);
const wasm = await loadBytes(QUERY_CASE.wasmPath);
const verifier = await createVerifier(wasm);
const started = performance.now();
const changed = verifier.verify({ template, publicRows: changedRows, proof,
  expectedTemplateSha256: QUERY_CASE.expectedTemplateSha256 });
const changedMs = performance.now() - started;
if (changed.verified || !changed.error?.startsWith('proof rejected:')) {
  throw new Error(`Changed output did not reach proof rejection: ${JSON.stringify(changed)}`);
}

console.log(JSON.stringify({
  schema: 'recorded-two-class-query-node-wasm-execution-v1',
  status: 'PASS',
  claim: '[EXECUTED] Both recorded class computations accepted by the unchanged IR2 WebAssembly verifier; a changed output was rejected by the proof backend.',
  runtime: { engine: 'Node WebAssembly', node: process.version, platform: process.platform, arch: process.arch },
  wasmSha256: createHash('sha256').update(wasm).digest('hex'),
  expectedBackend: QUERY_CASE.expectedBackend,
  genuine,
  changedPublicOutput: {
    label: first.label, row: 0, column: 43, originalDigit, changedDigit: changedRows[0][43],
    transportPinsIntentionallyBypassedForControl: true,
    actualProofBackendRefused: true, verificationMs: changedMs, result: changed,
  },
  progress,
  newProofGenerated: false,
  wasmRebuilt: false,
  browserExecutionPerformed: false,
  privateFilesRead: false,
}, null, 2));
