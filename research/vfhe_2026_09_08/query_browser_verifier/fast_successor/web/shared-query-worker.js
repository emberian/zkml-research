// Deploy beside the site's existing frozen verifier.js and pkg/ directory.
import { verifyBothClassComputations } from './query-consumer.js';
import { QUERY_CASE } from './query-case.js';

let running = false;
self.onmessage = async event => {
  const id = event.data?.id;
  if (running) {
    self.postMessage({ type: 'result', id, result: { verified: false, error: 'Verification already running' } });
    return;
  }
  running = true;
  try {
    if (typeof event.data?.bundleBaseUrl !== 'string') throw new TypeError('bundleBaseUrl is required');
    const bundleBase = new URL(event.data.bundleBaseUrl, self.location.href);
    if (!bundleBase.pathname.endsWith('/')) throw new TypeError('bundleBaseUrl must end with a slash');
    const loadBytes = async path => {
      const url = path === QUERY_CASE.wasmPath
        ? new URL('./pkg/vfhe_browser_verifier_bg.wasm', import.meta.url)
        : new URL(path, bundleBase);
      const response = await fetch(url);
      if (!response.ok) throw new Error(`Could not load ${path}: HTTP ${response.status}`);
      return new Uint8Array(await response.arrayBuffer());
    };
    const result = await verifyBothClassComputations({
      loadBytes,
      onProgress: progress => self.postMessage({ type: 'progress', id, progress }),
    });
    self.postMessage({ type: 'result', id, result });
  } catch (error) {
    self.postMessage({ type: 'result', id, result: { verified: false, error: String(error) } });
  } finally {
    running = false;
  }
};
