# Whole learner engine integration — apply after the active run

[EXECUTED] `python3 integration/check_interfaces.py` imported the proposed app in
an isolated sibling tree and checked the real byte-pinned profiles for all three
modes. `checks.json` records the result. No keys, ciphertext computation, proof
generation, private reads, or journal replay were run by this integration check.
`python3 integration/apply.py` also checked that the patch applies to the pinned
current sources. The running `core.py`, `backend.py`, and profiles were untouched.

[DERIVED: proposed implementation] The two-file patch updates `core.py` and adds
`engines.py`. It retains the existing BFV issuer/encoder, cyclic FIFO8, ciphertext
CAS, SQLite current-parent transaction, durable request identity/results, and
whole-phase recovery. The existing backend file is unchanged. Engine counts are
separate for update and inference:

| Genesis selection | Update proofs | Query proofs per active class | Private score |
| --- | ---: | ---: | --- |
| `squared / compact` | 8 | 116 | `sum_kernel / count`, eight squared dots |
| `linear / compact` | 8 | 88 | signed `sum_dot / count`, eight dots |
| `linear / matched` | 32 | 352 | signed `sum_dot / count`, eight dots |

The counts are the existing callers' required complete batches, not measurements
from an integration run. Linear production performs its own fresh eleven-stage
capture; the core does not run the quadratic capture first. Every active class
must independently verify before any private receive. Linear reads use the
native two-component dot decoder, check output/evaluation-key digests, eight
signed lanes bounded by 20000, their exact sum, and the repeated-slot contract.
The existing recipient/public-key check remains at the controller boundary.

The original default creates the original engine-absent genesis with its exact
policy. Reopening an old instance retains its head hashes, stored request/result
objects, phase names and proof counts. New linear instances bind a complete engine
descriptor at genesis: score/backend, per-operation counts, query caller/profile
byte pins, and signed reader/profile byte pins. The genesis hash binds every
request; new linear requests also carry `engine_sha256` explicitly. A different
score/backend in a repeated initialization is refused. No existing instance can
be switched between score rules.

## Apply and call

After the active workload and worker have stopped, from the repository root:

```sh
python3 research/vfhe_2026_09_08/continuing_system/integration/apply.py --apply
```

The script checks the manifest's base source hashes and patch hash before applying.
`proposed/backend.py` is an unchanged copy used only for isolated imports; it is
not in the patch. Launch with the existing encoder virtualenv, as documented in
the application `BUILD.md`.

```python
initialize(root, classes, score='linear', proof_backend='compact')
initialize(other_root, classes, score='linear', proof_backend='matched')
live = Live(root)
live.teach_vector(label, vector, text, request_id)
live.query_vector(vector, text, request_id)
```

CLI initialization adds `--score squared|linear` and
`--proof-backend compact|matched` (`--backend` is an alias). The other methods and
CLI commands retain their call signatures. Squared/matched is not a supported
combination. `CONTINUING_SYSTEM_LINEAR_PROFILE/WORKER` and
`CONTINUING_SYSTEM_MATCHED_PROFILE/WORKER` select profiles for *new* instances;
reopening always uses the exact recorded descriptor. The current
`CONTINUING_SYSTEM_PROFILE/WORKER` continues to select the shared issuer/compact
update backend. Matched uses its own update caller and the shared issuer.

For HTTP/UI integration, `core.metadata(root)` reads only genesis and
`Live.metadata()` returns the same display fields: `score_kind`, `proof_backend`,
`score_formula`, `score_signed`, `update_proofs_per_class`,
`infer_proofs_per_class`, `lane_values_key`, and `sum_key`. `head()` is unchanged;
display metadata must not be inserted into that hashed head.

Linear query results preserve `prediction`, `winner`, `ranking` (label array),
`classes`, `counts`, and exact rational `class_scores`. They add the engine display
fields. Each class has native `dot_values`/`sum_dot` and generic
`score_values`/`sum_score`; class-score rows contain `sum_dot`, `sum_score`,
`mean_numerator`, and `mean_denominator`. They do not contain `sum_kernel` or
`kernel_values`. Legacy squared results retain their existing keys.

Matched metrics derive accepted proof counts/bytes from its native chunk records,
retaining those records in receipts. Generated proof counts include successfully
self-verified retained producer reports; an interrupted partial matched phase
without a complete producer report is not counted as verified generation. A retry
can recover only a complete result or start a new whole phase. It never accepts a
partial proof batch.

[OPEN] Root owns the first actual alternate-engine whole-learner runs and HTTP/UI
integration. This patch does not establish those runs. The full reader, public
encoder and observations, setup/key validity, parser/NTT/controller/SQLite, and
native proof backend boundaries remain; changing engines does not remove custody
or supply a full native verifier-to-application soundness theorem.
