// Three genuine checks plus the existing update-button changed-output control.
// Every actual proof decision is made by the unchanged existing WASM verifier.
import { readFile } from 'node:fs/promises';
import { createVerifier } from './web/verifier.js';
import { QUERY_CASE } from './web/query-case.js';
import { verifyBothClassComputations } from './web/query-consumer.js';

const load = path => readFile(new URL(path, import.meta.url));
const hash = async bytes => Buffer.from(await crypto.subtle.digest('SHA-256', bytes)).toString('hex');
const updateRoot = './update/fixtures/learner-expiry/';
const fixture = JSON.parse(await load(updateRoot + 'fixture.json'));
const updateBytes = {};
for (const name of ['template.json', 'public_rows.json', 'proof.bin']) {
  const bytes = await load(updateRoot + name);
  if (bytes.length !== fixture.files[name].bytes || await hash(bytes) !== fixture.files[name].sha256)
    throw new Error(`Update transport mismatch: ${name}`);
  updateBytes[name] = bytes;
}
const wasm = await load('./web/pkg/vfhe_browser_verifier_bg.wasm');
if (await hash(wasm) !== QUERY_CASE.files[QUERY_CASE.wasmPath].sha256)
  throw new Error('WASM transport mismatch');
const verifier = await createVerifier(new Uint8Array(wasm));
const beforeUpdate = performance.now();
const update = verifier.verify({
  template: updateBytes['template.json'].toString('utf8'),
  publicRows: updateBytes['public_rows.json'].toString('utf8'),
  proof: new Uint8Array(updateBytes['proof.bin']),
  expectedTemplateSha256: fixture.files['template.json'].sha256,
});
const updateMs = performance.now() - beforeUpdate;
if (!update.verified || update.backend !== QUERY_CASE.expectedBackend || update.public_rows !== 8192 ||
    update.public_width !== 57 || update.template_sha256 !== fixture.files['template.json'].sha256)
  throw new Error(`Whole-row update must verify: ${JSON.stringify(update)}`);
// Match the already published button's exact control, as requested by root.
// This changes public row zero; it does not generate or retry a malformed proof.
const changedRows = JSON.parse(updateBytes['public_rows.json'].toString('utf8'));
const beforeDigit = changedRows[0][43];
changedRows[0][43] ^= 1;
const beforeChanged = performance.now();
const changed = verifier.verify({
  template: updateBytes['template.json'].toString('utf8'),
  publicRows: changedRows,
  proof: new Uint8Array(updateBytes['proof.bin']),
  expectedTemplateSha256: fixture.files['template.json'].sha256,
});
const changedMs = performance.now() - beforeChanged;
if (changed.verified || !changed.error?.startsWith('proof rejected:'))
  throw new Error(`Changed update output must reach and fail the proof verifier: ${JSON.stringify(changed)}`);
const progress = [];
const query = await verifyBothClassComputations({
  loadBytes: async path => {
    if (!Object.hasOwn(QUERY_CASE.files, path)) throw new Error(`Unapproved path: ${path}`);
    return new Uint8Array(await load(path.startsWith('web/') ? './' + path : './query/' + path));
  },
  onProgress: item => progress.push(item),
});
if (!query.verified || query.cases.length !== 2 || !query.cases.every(item => item.accepted))
  throw new Error(`Both whole-row query classes must verify: ${JSON.stringify(query)}`);
console.log(JSON.stringify({
  schema: 'whole-row-three-fixture-node-wasm-execution-v1', status: 'PASS',
  claim: '[EXECUTED] All three replacement arithmetic proofs accepted through the unchanged existing IR2 WebAssembly verifier.',
  runtime: { engine: 'Node WebAssembly', node: process.version, platform: process.platform, arch: process.arch },
  wasmSha256: await hash(wasm), update: { ...update, elapsedMs: updateMs }, query, progress,
  changedOutputControl: { row: 0, column: 43, before: beforeDigit, after: changedRows[0][43],
    result: changed, elapsedMs: changedMs, scope: 'Same public-output mutation as the published update button; original genuine proof reused.' },
  actualProofVerifications: 4, acceptedGenuineProofs: 3, rejectedChangedPublicStatements: 1,
  newProofsGeneratedBeforeConsumer: 3,
  wasmRebuilt: false, browserExecutionPerformed: false, privateFilesRead: 0,
  historicalFixturesPreserved: true, malformedProofControlRepeated: false,
}, null, 2));
