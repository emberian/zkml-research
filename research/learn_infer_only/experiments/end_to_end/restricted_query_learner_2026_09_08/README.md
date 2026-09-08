# Fixed-query semantic learner with restricted recipient keys

[SOURCE] This interface teaches two class memories and answers sixteen registered text queries. Each recipient has one independent projection key for its query. It can read that query's score on any retained issued input or class state. There is no general text-query endpoint or universal reader key.

The fixed registry is [registry.json](registry.json). It uses the first eight saved queries for `card_arrival` and `cash_withdrawal_charge`, with actual cached E5/projection vectors. [CONTRACT.md](CONTRACT.md) gives the one normal workload and parameter/range calculation. The fixture is already known public benchmark data, not a privacy challenge or fresh accuracy evaluation.

From this directory, the normal actor interface is:

```sh
TASK_PY=../../private_construction/public_setup_pq/ring_implementation/.venv/bin/python
$TASK_PY -B transport.py --registry registry.json --receipt recipient_query.json \
  query --key RECIPIENT_OWN_KEY.ring --models PUBLIC_MODELS.json
```

`PUBLIC_MODELS.json` names two actual class states and their hashes/counts at each requested checkpoint. The command uses the key's registered coordinate; it has no arbitrary-query argument. It returns that fixed text query's scores and exact mean ranking. The benchmark deliberately publishes the scores in its receipt.

For public teaching, the trusted plaintext issuer supplies its canonical 577-coordinate feature vector to `encode`, and the host updates the chosen class with `window`:

```sh
$TASK_PY -B transport.py --registry registry.json --receipt encode.json \
  encode --public PUBLIC.ring --input FEATURE_VECTOR.json --out FRESH.ring
$TASK_PY -B transport.py --registry registry.json --receipt learn.json \
  window --state CURRENT.ring --add FRESH.ring --expire OLDEST.ring \
  --capacity 2 --out NEXT.ring
```

Omit `--state` for the first item, and omit `--expire` until replacing the oldest item. Canonical lineage hashes bind expiry to the original ciphertext. Labels and routes are public. Setup commands `init`, `register` and `finalize` use the same full registry digest; changing any query requires a fresh registry/setup with freshly generated recipient rows. The inherited setup/transport algorithms are preserved in owned copies under `source/` and `codec/`.

[EXECUTED/SOURCE] `workflow.py` runs the fixed complete construction, with actor commands sandboxed against other recipients' private paths. The sole run writes to ignored `.runtime/normal_001/` and public `results/normal_001/`; it refuses an existing run directory. This is retained evidence, not a restart script. Keys and ciphertexts from prior experiments are never inputs.

[SCOPE] The coalition of all sixteen keys gets the whole sixteen-query span on each issued observation. It is not restricted to the final published means. Benchmark observations, query vectors, outputs, routing and timing are public. Conditional hardness, honest setup/registration, same-host administration and implementation side channels remain outside the execution result. The new basis is invertible on field vectors; that fact does not establish ambiguity of natural-language states.
