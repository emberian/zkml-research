// Standalone consumer of the same browser/WASM API. Exit 0 accepts; 1 rejects.
import { readFile } from 'node:fs/promises';
import { createVerifier } from './verifier.js';

const [templatePath, rowsPath, proofPath, expectedTemplateSha256] = process.argv.slice(2);
if (!expectedTemplateSha256 || process.argv.length !== 6) {
  console.error('usage: node web/verify-file.mjs TEMPLATE.json PUBLIC_ROWS.json PROOF.bin EXPECTED_TEMPLATE_SHA256');
  process.exit(2);
}
const [template, publicRows, proof, wasm] = await Promise.all([
  readFile(templatePath, 'utf8'), readFile(rowsPath, 'utf8'), readFile(proofPath),
  readFile(new URL('./pkg/vfhe_browser_verifier_bg.wasm', import.meta.url)),
]);
const verifier = await createVerifier(new Uint8Array(wasm));
const started = performance.now();
const result = verifier.verify({ template, publicRows, proof: new Uint8Array(proof), expectedTemplateSha256 });
console.log(JSON.stringify({ ...result, elapsedMs: performance.now() - started }, null, 2));
process.exitCode = result.verified ? 0 : 1;
