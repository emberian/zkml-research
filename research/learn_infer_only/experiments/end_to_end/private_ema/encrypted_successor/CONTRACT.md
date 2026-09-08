# Frozen semantic fixture through actual encrypted-address EMA

[EXECUTED authorization] Root authorized preparation and launch of the unchanged
384 Learn / 96 Infer schedule with all replays, per-invocation read-input hashes,
one sequential host worker and a deferred private drain. This is a new directory
and new setup; the previous two-step probe stays frozen.

[SOURCE utility] `../utility/REPORT.md` and its retained first evaluation show
7,486/8,192 final EMA labels correct (91.3818%) versus 7,462/8,192 for W32.
These are reused-data exploratory results with no demonstrated improvement.
The hard/wet stratum regresses from 696/1,024 to 672/1,024 (65.6250%). The fixed
integration subset is 28/32 for both. This run must preserve those caveats.

[DERIVED fixed workload] Consume exactly `../utility/materialized_fixture.json`:
histories 67000/67001, unchanged 384 Learn and 96 Infer event IDs/order, two
public routes and four encrypted signed-byte registers per route, starting
from freshly encrypted zeros per history/route. An issuer reads each public
synthetic source request privately and publishes only its encrypted two-bit
address plus encrypted signed label ±120. Learn computes every bin's candidate
`floor((7*s+u)/8)` and applies encrypted equality/MUX so only the selected bin
changes. Infer selects the encrypted negative bit at the encrypted query
address; zero is nonnegative. There are no expiry operations.

[DERIVED role limits] Reuse the previously built setup/issuer/host/reader binaries
whose SHA-256 values match `../source_manifest.json`; pin all Rust sources,
Cargo.lock, prior source manifest and the new Python wrapper before launch.
No Rust arithmetic change, model call, new text or new test selection is made.
One setup supplies public encryption/server keys and a full client key. Public
routes select separate four-bin ciphertext files; route privacy is not claimed.
The issuer sees the clear request. Host arguments contain only operation names,
public key/state/input/output paths, never clear address, label, state or answer.
All processes share the same operating-system account and the full client key
remains available to the reader. This does not remove read-all capability or
establish OS isolation, sign-only credentials, PQ security or a privacy theorem.

[DERIVED replay evidence] Every logical Learn and Infer is evaluated twice in
separate sequential processes from the same serialized server key, parent and
input/query bytes. Hash every such public input immediately before and after
each process; require unchanged file sizes/hashes, equal tuples between the
pair and complete output-byte equality. Pin the host executable before and
after every invocation. Stop at the first failure; retain partial progress
and all actual stdout/stderr and resource reports. Do not resample encryption
coins or retry a mismatch. No universal determinism/refinement theorem follows.

[DERIVED persistence] Every Learn continuation consumes the previous primary
ciphertext file. The public replay does not decrypt anything. Keep the other
route path unchanged and checkpoint both paths after each phase. The 16
preselected query records each receive one fresh query encryption, reused at
all six checkpoints; equality/reuse metadata is explicit. Runtime key and
ciphertext bytes live in ignored `runtime/`; public metadata, transcripts and
hashes remain reviewable. No secret-key value/hash or decrypted audit value is
written into public reports.

[DERIVED public-close/private-drain boundary] Finish all host/issuer processes
and all 480 byte replays, then persist and close the public transcript and its
hash before running `verify_public.py`. Only a passing public verification
allows `drain.py` to invoke the full-key reader. The drain compares all 96
encrypted negative outputs with the frozen integer oracle, plus every initial
and checkpoint route state (16 state opens, including repeated retained states).
Private plaintext audit files are kept in the ignored reader directory. They
never supply replacement state or influence subsequent host computation.

[DERIVED cost] `../utility/encrypted_cost_proposal.json` projects 7,470.984
seconds from prior measured per-process samples, excluding added hashing,
wrapper overhead and contention. Record measured original and replay costs
separately, source API gate counts as API calls (not measured bootstraps), key
and ciphertext sizes, actual wall-clock start and completion. The run uses one
sequential host process at a time and is bounded to four hours; each process
has a separate four-minute timeout. No resumable retry is implemented here;
an interrupted partial run remains partial and needs an explicit reviewed
continuation before more crypto execution.

[OPEN] This run tests actual useful-fixture encrypted continuation and its
public replay/cost under a pinned backend. It composes no journal, finality
gate, restricted release mechanism or full implementation proof. It is not
another utility estimate or an unknown-observation privacy experiment.
