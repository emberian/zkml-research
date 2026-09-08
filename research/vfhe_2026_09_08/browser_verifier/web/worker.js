// One actual verifier instance per worker. The application owns the approved pin.
import { createVerifier } from './verifier.js';
const ready = createVerifier();
self.onmessage = async ({ data }) => {
  const { id, request } = data;
  try {
    const verifier = await ready;
    const started = performance.now();
    const result = verifier.verify(request);
    self.postMessage({ id, result, elapsedMs: performance.now() - started });
  } catch (error) {
    self.postMessage({ id, result: { verified: false, error: String(error) } });
  }
};

