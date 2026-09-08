// Exactly two saved-proof checks through the unchanged consumer in Node WASM.
import { readFile } from 'node:fs/promises';
import { QUERY_CASE } from './query-case.js';
import { verifyBothClassComputations } from './query-consumer.js';

const loadBytes = async path => {
  if (!Object.hasOwn(QUERY_CASE.files, path)) throw new Error(`Unapproved fixture: ${path}`);
  return new Uint8Array(await readFile(new URL(`../${path}`, import.meta.url)));
};
const progress = [];
const genuine = await verifyBothClassComputations({ loadBytes, onProgress: item => progress.push(item) });
if (!genuine.verified || genuine.cases.length !== 2 || !genuine.cases.every(item => item.accepted)) {
  throw new Error(`Both fast001 class proofs must verify: ${JSON.stringify(genuine)}`);
}
console.log(JSON.stringify({
  schema: 'recorded-two-class-query-node-wasm-execution-v1', status: 'PASS',
  claim: '[EXECUTED] Both fast001 recorded class computations accepted by the unchanged IR2 WebAssembly verifier.',
  runtime: { engine: 'Node WebAssembly', node: process.version, platform: process.platform, arch: process.arch },
  wasmSha256: QUERY_CASE.files[QUERY_CASE.wasmPath].sha256,
  expectedBackend: QUERY_CASE.expectedBackend,
  genuine, progress, actualProofVerifications: 2,
  newProofGenerated: false, wasmRebuilt: false, browserExecutionPerformed: false,
  privateFilesRead: false, originalGated001Preserved: true,
}, null, 2));
