import { createVerifier } from './verifier.js';
const ready = createVerifier();
self.onmessage = async ({ data: { id, request } }) => {
  try {
    const verifier = await ready;
    const started = performance.now();
    const result = verifier.verify(request);
    self.postMessage({ id, result, loadMs: verifier.loadMs, verifyMs: performance.now() - started });
  } catch (error) { self.postMessage({ id, result: { verified: false, stage: 'runtime', error: String(error) } }); }
};

