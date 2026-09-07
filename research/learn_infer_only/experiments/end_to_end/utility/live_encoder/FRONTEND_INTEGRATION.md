# Attaching live text to the existing journal coordinator

[DERIVED plumbing, not yet executed here] A trusted coordinator already has an
independently created `journal.run.Run` instance named`run`, with its initializer,
authority and reader roles running. Use a new demonstration/history, not either
frozen384/96 utility fixture history. Its public query policy should contain the
desired preauthorized query. The exact current authority head must be used for
admission; an old head is allowed to fail normally as stale.

The shortest integration reuses the existing ordinary Learn path after live
encoding. This snippet executes the tested original encoder, then delegates
encryption/signing/proposal/finality to the already-used journal methods:

```python
# Trusted coordinator/issuer context only. These are absolute configured paths.
import json
import subprocess
from pathlib import Path

source = Path(PRIVATE_TEXT_JSON)  # {"text": ..., "route": 0, "label": 1}
vector = Path(NEW_PRIVATE_VECTOR_JSON)
item = json.loads(source.read_text())
subprocess.run([
    UTILITY_VENV_PYTHON, "-B", ORIGINAL_ENCODER_SCRIPT,
    "--input", str(source), "--output", str(vector),
], check=True, capture_output=True, text=True)

# Run.prepare is the existing trusted coordinator, not the keyless host process.
# Its issuer subprocess alone receives vector; the host receives ciphertext.
request = run.prepare("Learn", item["route"], "live-text-001", vector=vector)
installed = run.accepted(request)

# Existing command authorization, reader registration and finalization path.
query = run.prepare("Infer", item["route"], "live-text-query-001", query_index=0)
delivered = run.accepted(query)
```

[DERIVED role audit] In the existing source, `Run.prepare` invokes `roles.py issue`
with the vector; `roles.issue` calls `issuer-encrypt` and signs the Learn action.
It then imports/uploads only the ciphertext and invokes `roles.py propose` with
host config, head, signed authorization and ciphertext CAS. Admission and reader
delivery remain unchanged. Root/driver code must preserve that distinction:
never copy the text, source vector or oracle labels into host/authority arguments,
events or logs. The trusted source/encoding logs should use mode0600 private paths.

[DERIVED separate-process alternative] `issue_text.py` combines the first
encoder and issuer stages and writes `fresh.ct` plus `authorization.json`.
After that wrapper, reproduce the public operations already present in
`journal/run.py:48`: import/upload `fresh.ct`, call `propose`, upload the proposed
result and call `accepted`. Do not call `Run.prepare('Learn', ...)` again on that
already-issued ciphertext; that method would encrypt/sign a second input.

[OPEN verification for the integration owner] For a fresh one-Learn history,
the test oracle can compare the finalized query score to a Python-integer dot
of the private live vector and the public query vector. Keep that plaintext
calculation and expected score outside host/authority roles. A match establishes
the composed computation for that example, not useful adaptation from one item,
hidden feature provenance or absence of the reader's full decryption capability.
