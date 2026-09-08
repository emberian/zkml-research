# Independent prelaunch disposition: one live semantic BFV input

[DERIVED review disposition, 2026-09-08] **Accept the exact source freeze for
the assigned one-attempt normal demonstration**, subject to the owner's
existing coordination with the priority TFHE worker. The accepted freeze is
`end_to_end/utility/semantic_axis_successor/encrypted_bfv/live_successor/freeze.json`,
SHA256 `a9f07b896f637f553819d4e0a2d6db78a443cb0194d1c4f4f54f41ec27eca882`.
No execution result is asserted by this disposition. The original unlaunched
freeze and changed source bytes are retained under `prelaunch_revision_001/`.
The author reports that the revised freeze preserves the same private text and
prepared prompts; the reviewer did not read those private objects.

[EXECUTED public-only preflight] Commands and output retained here:

```
python3 -B research/learn_infer_only/experiments/adversarial_review/live_semantic_bfv/verify_model.py > research/learn_infer_only/experiments/adversarial_review/live_semantic_bfv/model_preflight.stdout.json
python3 -B research/learn_infer_only/experiments/adversarial_review/live_semantic_bfv/verify_source.py > research/learn_infer_only/experiments/adversarial_review/live_semantic_bfv/source_preflight.stdout.json
```

Both exit zero. `model_preflight.json` independently hashes all nine cached
SmolLM3 files (6,167,529,097 bytes total), including both weight shards, against
the inherited frozen revision `a07cc9a04f16550a088caea529712d1d335b0ac1`.
`source_preflight.json` checks all 56 public source dependencies, 23 staged
source/binary pins, 28 archive entries, 16 query files, nine parsed Python
sources and all 171 parent-manifest entries (34 + 53 + 54 + 30). These checks
use only the Python standard library; they import no model/crypto code and
read no private file or answer database. The source pin map records exact
public paths and digests. The model check is byte provenance, not a reproduced
model forward or model-origin attestation beyond the pinned local cache.

[SOURCE: successor CONTRACT.md, prepare.py, encoder/score.py,
encoder/common.py, issue_semantic_text.py] The fixed path is Infer(q01),
one Learn on public route zero with supplied label +1, Infer(q01). The query is
the inherited first-coordinate vector `[127,0,...,0]`, fixed before scoring.
The cached SmolLM3-3B model runs the unchanged inherited tensor loop in one
two-example partial batch, maximum batch size eight. Framing A asks two public
plant axes (leaf flexibility and soil moisture); alternatives are token IDs
15/16. MPS float16 eager inference uses explicit left-padding positions;
likelihood arithmetic is float32 on CPU and ties select bit zero. The issuer
maps bits `(a,b)` to coordinate `2*a+b`, places 127 there in a 577-vector, then
uses the frozen signed BFV issuer. The teaching label is applied after scoring.
No label/oracle enters the model tensor input. Provenance helpers hash older
public manifest entries, including historical oracle files; this does not
establish process-level absence of all oracle-related bytes.

[EXECUTED / REPORTED freshness distinction] The checker independently verifies
the five named prior-corpus hashes, 384 records per corpus, and their combined
1,152 unique full text strings. `freshness.json` attributes one private text's
exact-string disjointness against that corpus to the author's prepare run.
The source implements that equality check before model or BFV execution. The
reviewer does not inspect the selected text or recompute its disjointness.
This is neither training-corpus absence nor a new-task or accuracy claim.

[SOURCE: driver.py and pinned journal/verified-reader core] The byte-identical
`LiveRun` class and frozen core are retained. The successor `admit` submits
once and syncs each authority envelope without an accepted/delivery retry.
Its verifier socket differs from the authority delivery destination, so both
Infer publications remain pending. The worker performs all three accepted
events, verifier syncs, full public arithmetic replay, actual public journal
and head equality, and zero received/decrypt checks before closing every
recorded service and the host. It writes `public_phase.json` only after their
processes are observed exited. `run.py` creates a process group per phase;
on timeout or exit it checks group absence independently of leader status,
escalates surviving descendants, and refuses the next phase on failure.
The ten-minute public-driver cap and one-attempt markers prevent an ordinary
failure from authorizing a retry or private continuation. No failure injection
was run for this review.

[SOURCE: public_verify.py, drain.py, run.py] A separate process, after shutdown,
uses public host configuration and an independent CAS to verify signatures,
recompute all three transitions, check actual durable public tables and
zero received answers, hash stored blobs and recheck source/model pins. Its
passing artifact binds the freeze, accepted envelopes and public phase. The
next separate private process checks those bindings and service absence before
calling unchanged `VerifiedReader.receive` on the two registered, finalized
Infer envelopes. Only then does it read scalar answers, reconstruct the bits
from retained logits and tie rules, reconstruct the one-hot vector and compare
both answers with direct integer arithmetic. Post-drain omission/pin auditing
is artifact validation; public protocol operations, replay and public services
have already finished. This is an honest source/orchestrator ordering contract,
not a proof that a malicious orchestrator cannot forge a passing JSON file.

[SOURCE / DERIVED credential and output scope] The network verifier's inherited
reader constructor loads the full BFV secret even though scalar decoding is
deferred. Only the separate post-shutdown public verifier is keyless. Offline
receipt does not acknowledge the closed authority outbox; both pending Infer
flags remain. This is a plaintext trusted semantic issuer and full-key BFV
recipient on one OS account, with four effective bins per public route,
ordinary authorized queries, and no no-master-read or end-to-end PQ claim.

[DERIVED ordinary-output disclosure] With a zero initial score, fixed +1 label,
127-valued one-hot contribution and q01, the after-score belongs to
`{0,127*127} = {0,16129}`. Thus the published change boolean determines this
selected after-score. The contract explicitly claims no selected-score secrecy.
All possible one-hot rows/hashes already occur in the public query dictionary;
their presence is not a newly published association to the selected row.
The omission audit excludes selected-feature fields and private text/prompt/
raw-score artifacts, with this dictionary qualification. The reviewer will
attribute actual private comparisons and omission scans to author execution.

[OPEN next step] Inspect the retained public normal-run records, chain hashes,
phase bindings, cost/log consistency and final public manifest after the
single authorized run. No model execution, BFV/DDH arithmetic, private drain,
routing/extraction experiment, stopped task, companion edit, shared-ledger
edit or commit was performed by this reviewer. No metered/web queries were used.
