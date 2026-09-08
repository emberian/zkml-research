import { verifyBothClassComputations } from './query-consumer.js';

let running = false;
self.onmessage = async event => {
  const id = event.data?.id;
  if (running) {
    self.postMessage({ type: 'result', id, result: { verified: false, error: 'Verification already running' } });
    return;
  }
  running = true;
  try {
    const result = await verifyBothClassComputations({
      onProgress: progress => self.postMessage({ type: 'progress', id, progress }),
    });
    self.postMessage({ type: 'result', id, result });
  } finally {
    running = false;
  }
};
