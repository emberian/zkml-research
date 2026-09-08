import init, { verify_bundle } from './pkg/ring_browser_verifier.js';

export async function createVerifier(wasm) {
  const started = performance.now();
  await init(wasm === undefined ? undefined : { module_or_path: wasm });
  return {
    loadMs: performance.now() - started,
    verify({ statement, proof }) {
      if (!(statement instanceof Uint8Array) || !(proof instanceof Uint8Array)) {
        throw new TypeError('statement and proof must be Uint8Array');
      }
      try { return JSON.parse(verify_bundle(statement, proof)); }
      catch (error) { return { verified: false, stage: 'runtime', error: String(error) }; }
    },
  };
}

