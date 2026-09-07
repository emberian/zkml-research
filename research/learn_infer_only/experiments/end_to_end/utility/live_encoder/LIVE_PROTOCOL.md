# Live issuer encoder: four fixed records

[DERIVED protocol] Root authorized actual execution of the prepared encoder on
teacher records0/64 and held-out query records256/320. These are the earlier
metadata-selected illustrative records; no outcome-based replacement is permitted.
The existing original E2E fixture, model cache and encoder policy remain unchanged.

[DERIVED settings] Run CPU float32, eager attention, eval/inference mode,2 torch
threads and1 interop thread, seed7901, one prompt per process, all30 decoder
blocks while retaining direct block9 output. Pool excludes padding. Apply the
existing public teacher center/scale, bias1 and nearest-even signed-int8
quantization. All four use multiplier+1, so teacher contributions correspond to
the original positive label and query examples produce the public feature vector.
No token, label, plaintext vector or private input JSON is a host/authority input.

[DERIVED checks] Run the original issuer_encode_prepared.py without altering it.
Compare all577 emitted integers exactly with its named cached record. If a
single-prompt/batched numerical difference changes quantization, preserve the
failure and do not silently change settings or claim cache equivalence. Retain
raw process output, wall/CPU/RSS measurements, exit codes and before/after source
hashes. Live plaintext and vectors stay in ignored issuer/oracle paths. Existing
public synthetic text may be identified by record metadata in this analysis.

[DERIVED boundary] A reusable live command emits an issuer-only vector, followed
by the existing OS-random public-key issuer encryption. Authenticated Learn
submission and finalization still use the journal lane's actual command. This
frontend does not prove hidden input provenance or enforce no-master-read security.
