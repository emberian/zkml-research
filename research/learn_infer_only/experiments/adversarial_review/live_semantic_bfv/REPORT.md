# Independent normal-path review: live semantic BFV successor

[DERIVED final disposition, 2026-09-08] **Accept the source-level integration
and retained normal-run evidence within the stated trusted-issuer/full-key
scope.** The single attempt performed Infer(q01), one live model-plus-Learn,
Infer(q01). No source repair or further model/crypto run is needed for this
review. This is one demonstration, not an accuracy estimate or a new security
construction. The prelaunch rationale and exact accepted gate remain frozen
in [SOURCE_REVIEW.md](SOURCE_REVIEW.md) and [source_review.json](source_review.json).

[EXECUTED immutable author pins] The accepted author freeze SHA256 is
`a9f07b896f637f553819d4e0a2d6db78a443cb0194d1c4f4f54f41ec27eca882`.
The completed author `REPORT.md` SHA256 is
`75d9d0f94c078767f923d651141d87993a21bcd97b02da86efe9f830c399e1d8`;
its 67-file `manifest.json` SHA256 is
`9e04634c8e7346697035372e363de4fb6a1abd5efd92e552eef6e1e6f86dce9f`.
All 67 public entries match their hashes, and all 171 parent-manifest entries
(34 + 53 + 54 + 30) still match after the run. The unfinished original live
draft and unlaunched first successor freeze are preserved. No author source
or runtime was changed by this reviewer.

[EXECUTED independent checks] These commands exit zero, with their output and
standard-library-only source retained here:

```
python3 -B research/learn_infer_only/experiments/adversarial_review/live_semantic_bfv/verify_public.py > research/learn_infer_only/experiments/adversarial_review/live_semantic_bfv/public_check.stdout.json
python3 -B research/learn_infer_only/experiments/adversarial_review/live_semantic_bfv/verify_author_manifest.py > research/learn_infer_only/experiments/adversarial_review/live_semantic_bfv/manifest_check.stdout.json
```

The earlier public preflight independently checked 56 source dependencies,
23 staged source/binary pins, 28 source-archive entries, 16 query files, nine
Python ASTs and all nine cached model files. Final checks rechecked source,
snapshot and query pins; compared retained model posthashes to the independently
hashed preflight; reconstructed the three-event canonical hash/state chain;
matched authority replay, verifier export and head state; and hashed all 33
stored public CAS blobs. Both queries are the same q01, with coefficients
`[127,0,...,0]`. Both offline receipt envelope digests and nonces agree with
the finalized Infer envelopes, and both logged decrypt ciphertext paths name
those exact finalized outputs. See `source_preflight.json`,
`model_preflight.json`, `public_check.json` and `manifest_check.json`.

[EXECUTED public records / SOURCE ordering] The saved sequential command record
has public driver, separate public verifier, private drain, then artifact
validation, all exit zero. No phase timed out or escalated cleanup; each records
its process group absent before the next phase. The public phase reports zero
received answers, three verified records and two registered tickets. Its exact
hash and the accepted-envelope hash are bound by the passing public-verification
artifact, SHA256
`94881d88c311aad345aa0838563bb45cff3e65d0da614acd3d4d9fed09551395`.
That artifact binds the accepted source freeze and unchanged model hashes
before private receipt. Reviewed source places all public protocol operations,
full arithmetic replay and service shutdown before the separate public gate
and then private drain. Post-drain file/pin/omission checks are artifact audits,
not another public protocol phase.

[EXECUTED log consistency] There are 52 retained public crypto CLI rows
(40 main, six verifier, six separate public verifier), all successful and none
`reader-decrypt`. The later receive log contains four rows: two inspections
and two successful decryptions, with scalar stdout/stderr omitted. The
persistent host has three requests and 26 full stored-blob reads/hashes.
The reviewer independently recomputed all 22 role/command cost groups from
these 56 rows and checked all 17 costs.csv rows against the source JSON values.

[REPORTED author execution; SOURCE audited] The actual signature checks and
BFV arithmetic replays, actual stopped-database equality and zero-answer
queries were executed by the author pipeline and retained in its public
artifacts. The reviewer checked the source and public records but did not
re-execute signature/BFV arithmetic or read the answer-bearing SQLite file.
The author reports one SmolLM3 forward on two axis examples, no cached feature
substitution, no generation or weight updates, two of two private direct
integer matches, and output-change true. The reviewed private audit source
reconstructs bits from saved logits and the tie rule, reconstructs the one-hot
vector, then compares both durable answers. The reviewer neither read those
private values nor reran the model or private audit. Private text freshness
against the five named prior synthetic corpora and private artifact/key omission
scans likewise remain attributed, with their precise instruments inspected.

[EXECUTED / REPORTED costs] The outer command record is 27.504062 seconds,
including source/model hashes. Its public-driver process interval is
19.676214542 seconds; the driver's inner phase clock is 19.486414625 seconds.
The later public-verifier, private-drain and validator subprocess intervals
are 3.889736208, 0.203700459 and 0.202328125 seconds. Intervals overlap with
model/crypto component clocks. The author records an actual 05:56:48 UTC start;
coordination.json attributes accepted overlap with subsequent TFHE Learn work
to that worker after its first Infer block closed. This is shared-load timing,
not a cross-fixture performance comparison.

[SOURCE / DERIVED scope retained] The network verifier loads the full BFV secret
during its public phase while scalar decoding is deferred; only the later
public verification process is keyless. The semantic issuer sees plaintext.
Offline receipt leaves the closed authority's two Infer publications pending;
completed authority delivery acknowledgement is not established. Roles share
one OS account, and the padded vector still has only four effective bins per
public route. No no-master-read, OS isolation, encrypted 3B cognition, exactly-once
physical delivery or end-to-end PQ claim follows.

[DERIVED output qualification] With fixed label +1, a 127-valued one-hot feature
and q01, the selected after-score belongs to `{0,16129}`. The disclosed change
boolean determines that scalar, so no selected-score confidentiality is claimed.
Omitted scalar/feature fields are an output-format boundary. Possible one-hot
rows and hashes already occur in the public query dictionary; their presence
is not a new selected-row association. This is arithmetic on the ordinary
public interface, not a routing or extraction test.

[EXECUTED reviewer boundary] Zero model/crypto imports, zero model forwards,
zero private-file reads, zero routing/extraction controls, zero stopped-task
reads, zero companion/shared-ledger edits and no commits. No metered or web
queries were used. Root owns the shared ledger disposition and commits.
