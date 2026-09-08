import { readFile } from 'node:fs/promises';
import { createVerifier } from './verifier.js';
const [statementPath, proofPath] = process.argv.slice(2);
if (!proofPath || process.argv.length !== 4) {
  console.error('usage: node web/verify-file.mjs STATEMENT.bin PROOF.bin'); process.exit(2);
}
const start = performance.now();
const [statement, proof, wasm] = await Promise.all([
  readFile(statementPath), readFile(proofPath),
  readFile(new URL('./pkg/ring_browser_verifier_bg.wasm', import.meta.url)),
]);
const fileReadMs = performance.now() - start;
const verifier = await createVerifier(new Uint8Array(wasm));
const mark = performance.now();
const result = verifier.verify({ statement: new Uint8Array(statement), proof: new Uint8Array(proof) });
console.log(JSON.stringify({ result, fileReadMs, moduleInitMs: verifier.loadMs, verifyMs: performance.now() - mark }, null, 2));
process.exitCode = result.verified ? 0 : 1;

