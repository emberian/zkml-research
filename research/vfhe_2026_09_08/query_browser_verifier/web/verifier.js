import init, { verify_receipt } from './pkg/vfhe_browser_verifier.js';

/** Load once; wasm may be a URL, Response, ArrayBuffer or Uint8Array. */
export async function createVerifier(wasm) {
  await init(wasm === undefined ? undefined : { module_or_path: wasm });
  return {
    /**
     * Verify caller-selected coefficient rows under an application-approved
     * template. expectedTemplateSha256 must come from trusted application config.
     * Run this in a Web Worker for large proofs; the actual check is synchronous.
     */
    verify({ template, publicRows, proof, expectedTemplateSha256 }) {
      if (typeof template !== 'string') throw new TypeError('template must be exact JSON text');
      if (!(proof instanceof Uint8Array)) throw new TypeError('proof must be Uint8Array');
      const rows = typeof publicRows === 'string' ? publicRows : JSON.stringify(publicRows);
      try {
        return JSON.parse(verify_receipt(template, rows, proof, expectedTemplateSha256));
      } catch (error) {
        return { verified: false, error: `verifier runtime failed: ${String(error)}` };
      }
    },
  };
}

