import { createVerifier } from './verifier.js';
import { QUERY_CASE } from './query-case.js';

const utf8 = new TextDecoder('utf-8', { fatal: true });
const now = () => performance.now();

async function fetchBundleBytes(path) {
  const response = await fetch(new URL(`../${path}`, import.meta.url));
  if (!response.ok) throw new Error(`Could not load ${path}: HTTP ${response.status}`);
  return new Uint8Array(await response.arrayBuffer());
}

async function pinnedBytes(path, loadBytes) {
  const pin = QUERY_CASE.files[path];
  if (!pin) throw new Error(`Unapproved bundle path: ${path}`);
  const loaded = await loadBytes(path);
  const bytes = loaded instanceof Uint8Array ? loaded : new Uint8Array(loaded);
  if (bytes.byteLength !== pin.bytes) throw new Error(`Transport length mismatch: ${path}`);
  const digest = new Uint8Array(await crypto.subtle.digest('SHA-256', bytes));
  const hex = Array.from(digest, byte => byte.toString(16).padStart(2, '0')).join('');
  if (hex !== pin.sha256) throw new Error(`Transport SHA-256 mismatch: ${path}`);
  return bytes;
}

/**
 * Verify both recorded class computations locally using the frozen WASM core.
 * The fixed QUERY_CASE is application configuration, not prover-supplied input.
 * loadBytes permits an offline/local-file consumer; the default loads this bundle.
 * Use the worker entry point in a webpage: the underlying verification is synchronous.
 */
export async function verifyBothClassComputations({
  loadBytes = fetchBundleBytes,
  onProgress = () => {},
} = {}) {
  const started = now();
  const cases = [];
  let stage = 'transport';
  const context = {
    caseId: QUERY_CASE.id,
    requestId: QUERY_CASE.requestId,
    scope: QUERY_CASE.scope,
    expectedTemplateSha256: QUERY_CASE.expectedTemplateSha256,
    publicQuerySha256: QUERY_CASE.publicQuerySha256,
    recordedModelRoot: QUERY_CASE.recordedModelRoot,
    recordedRevision: QUERY_CASE.recordedRevision,
  };
  try {
    onProgress({ stage: 'loading', completed: 0, total: QUERY_CASE.cases.length });
    const [wasm, templateBytes] = await Promise.all([
      pinnedBytes(QUERY_CASE.wasmPath, loadBytes),
      pinnedBytes(QUERY_CASE.templatePath, loadBytes),
      // This pins the retained request context; it does not verify authorization.
      pinnedBytes(QUERY_CASE.requestPath, loadBytes),
    ]);
    const template = utf8.decode(templateBytes);
    stage = 'runtime';
    const verifier = await createVerifier(wasm);
    for (const item of QUERY_CASE.cases) {
      stage = 'transport';
      const [rows, proof] = await Promise.all([
        pinnedBytes(item.publicRowsPath, loadBytes),
        pinnedBytes(item.proofPath, loadBytes),
      ]);
      stage = 'proof';
      onProgress({ stage: 'verifying', label: item.label, completed: cases.length, total: QUERY_CASE.cases.length });
      const proofStarted = now();
      const result = verifier.verify({
        template,
        publicRows: utf8.decode(rows),
        proof,
        expectedTemplateSha256: QUERY_CASE.expectedTemplateSha256,
      });
      const verificationMs = now() - proofStarted;
      const expectedIdentity = result.backend === QUERY_CASE.expectedBackend
        && result.template_sha256 === QUERY_CASE.expectedTemplateSha256
        && result.public_rows === item.rows
        && result.public_width === item.publicWidth
        && result.proof_bytes === proof.byteLength;
      const accepted = result.verified === true && expectedIdentity;
      cases.push({ label: item.label, accepted, verificationMs, result });
      if (!accepted) {
        return { verified: false, stage, ...context, cases, elapsedMs: now() - started,
          error: result.error || 'Verifier result did not match the approved case identity' };
      }
      onProgress({ stage: 'accepted', label: item.label, completed: cases.length, total: QUERY_CASE.cases.length });
    }
    return { verified: cases.length === 2 && cases.every(item => item.accepted),
      stage: 'complete', ...context, cases, elapsedMs: now() - started };
  } catch (error) {
    return { verified: false, stage, ...context, cases, elapsedMs: now() - started, error: String(error) };
  }
}
