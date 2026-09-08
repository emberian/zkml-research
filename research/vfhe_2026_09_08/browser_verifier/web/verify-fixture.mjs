// Runs the browser JS/WASM API directly in Node; no native verifier subprocess.
import { readFile } from 'node:fs/promises';
import { resolve, join } from 'node:path';
import { createHash } from 'node:crypto';
import { createVerifier } from './verifier.js';

const fixture = resolve(process.argv[2] ?? new URL('../fixtures/operation/', import.meta.url).pathname);
const manifest = JSON.parse(await readFile(join(fixture, 'fixture.json'), 'utf8'));
const template = await readFile(join(fixture, 'template.json'), 'utf8');
const publicRows = JSON.parse(await readFile(join(fixture, 'public_rows.json'), 'utf8'));
const proof = new Uint8Array(await readFile(join(fixture, 'proof.bin')));
for (const name of ['template.json', 'public_rows.json', 'proof.bin']) {
  const bytes = await readFile(join(fixture, name));
  if (createHash('sha256').update(bytes).digest('hex') !== manifest.files[name].sha256) {
    throw new Error(`fixture transport hash mismatch: ${name}`);
  }
}
const verifier = await createVerifier(new Uint8Array(await readFile(new URL('./pkg/vfhe_browser_verifier_bg.wasm', import.meta.url))));
const request = { template, publicRows, proof, expectedTemplateSha256: manifest.files['template.json'].sha256 };
let started = performance.now();
const genuine = verifier.verify(request);
const genuineMs = performance.now() - started;
if (!genuine.verified) throw new Error(`genuine proof did not verify: ${genuine.error}`);
// Both supported layouts start the output coefficient's digits at column 43.
const changedRows = publicRows.map(row => [...row]);
changedRows[0][43] ^= 1;
started = performance.now();
const changed = verifier.verify({ ...request, publicRows: changedRows });
const changedMs = performance.now() - started;
if (changed.verified || !changed.error?.startsWith('proof rejected:')) {
  throw new Error(`expected actual proof rejection for changed public output: ${JSON.stringify(changed)}`);
}
console.log(JSON.stringify({
  claim: 'EXECUTED same JavaScript/WASM verifier API used by browser consumers',
  fixture, genuine, changedPublicOutput: changed,
  genuineMs, changedPublicOutputMs: changedMs,
  proofBytes: proof.byteLength, browserEngine: 'Node WebAssembly runtime',
  noNewProofGenerated: true,
}, null, 2));

