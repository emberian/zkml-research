# Independent review: public-coin setup and normal durable journal

[DERIVED disposition; 2026-09-08] Accept the source-level public-coin setup
join and this completed normal journal integration within the stated honest
setup and fixed-span scope. Independent source/setup identity and exported
public record checks pass. This does not extend the accepted-value DDH proof
to timing-bearing genesis or the full instrumented transcript. No crypto, model, private-drain,
adversarial/routing or previously stopped artifact was executed by this
review. Only pinned sources, explicit public files, hashes/JSON and rational
matrix arithmetic were used.

[EXECUTED frozen run identity] The subject is
`public_coin_setup/journal/reports/normal_002/execution_pins.json`, SHA256
`12c614b917156b8f8a0e0cba0e3655e09c51e689a4a314dff73eba3819e5c390`.
Its canonical genesis digest is
`0c81dbc0158b6703c3cc50b1ba4b6ed4e4ad07aed2e7acd8b9c98909deb9e8d3`,
and context byte digest is
`b060f1ae45ae1df7d3ed31b20364a884aebdc537b8ad27036b817f04cc9757c6`.
The genesis file includes a newline, so its file hash differs from the
canonical digest; the review keeps these conventions separate.

## 1. Source dependencies and exact setup path

[SOURCE inspected code] References below are relative to
`research/learn_infer_only/experiments/private_construction/designated_span/public_coin_setup/journal/`.
I read `setup_join.py`, `driver.py`, `private_oracle.py`,
`source/public_setup/setup.py`, common/model/run/roles/authority/reader,
the verified-reader service, persistent host, public-log checker and the
relevant original crypto parser/setup/issuance/transition/decoder branches.
No runtime module was imported. The prior mathematical/implementation
reviews and adapter closeout were read as separate evidence.

[EXECUTED identities] `review.py` verifies all 28 origin/copy pairs in
`SOURCE_PINS.json`, all 33 launch source/contract pins, 79 installed signature
implementation files and the interpreter/native-library binaries. The normal
journal and its duplicate under the persistent host's `frozen_source` match.
No source-byte mismatch was found in this named corpus by SHA256 comparison.
This is an identity result, not validation of every operation in those modules.

[SOURCE constructor order] `setup_join.py:35` creates the fresh root and
role directories, calls params, creates registration authentication keys,
obtains all 16 recipient announcements, then calls public-build and
verify-public. It invokes uncached validate-context, finalizes all 16 existing
recipient scalars, removes their pending pathname copies, creates journal
signing keys and installs fixed queries/genesis/configs. `driver.py:35`
initializes `PublicRun` from that genesis without calling `Run.__init__`,
whose legacy setup would invoke the dealer path.

[SOURCE scalar generation] `source/public_setup/setup.py:20` uses bit-word
rejection on explicit intervals. Recipient-init samples private a and
publishes `A=g^a`; public-build samples tau directly in `[0,q)` and U directly
in `[1,p)`, computes `U^2`, and completes public group coordinates. Neither
the constructor nor the wrapper samples the scalar master s or computes
scalar projection deliveries. The logarithms in the mathematical coupling
are not executed algorithms. Unused initializer/keygen/recipient-register
branches remain in the unchanged backend.

[DERIVED credential inventory] Distinct credential roles remain:

| Artifact | Source generation / intended holder | Boundary |
| --- | --- | --- |
| 16 recipient scalars a | One per recipient-init, finalized into private envelopes | Full fixed per-input projection capability |
| 16 registration signing keys | Ed25519 keys from auth-init | Authenticate fixed slots; no proof of independent scalar sampling |
| Issuer, command, authority signing keys | Three Ed25519 keys from setup_join | Input/query authorization and journal finalization |
| Fresh input randomizer r | Backend issuer-encrypt | Private independent encryption randomness still required |
| tau, U, A and context | Accepted public transcript values | Public consistency, not an entropy or auxiliary-secret certificate |
| Scalar master / projection deliveries | No generation call on this constructor path | No dealer-master erasure event is needed here |

[DERIVED] Removing pending scalar pathnames removes redundant copies; it
does not prove physical erasure. Shared-account processes do not prevent
operator inspection of other roles. The known input fixture and zero initial
state allow reconstruction independently of cryptographic credentials.

## 2. Matrix, arithmetic and fixed recipient

[SOURCE] `source/public_setup/setup.py:55` checks the first-16-column
determinant, forms R over Fq, checks `Yp*R=I` and `Yp*L+Yf=0`, and completes
the public coordinates. First-16 pivots preserve original coordinate order
for this fixed matrix; no general permutation algorithm is claimed.

[EXECUTED independent arithmetic] Rational Gaussian elimination in
`review.py`, separate from the author's Bareiss/modular implementation,
reproduces determinant `-812032080`. It checks dimensions 16-by-577, the
fixed pivots/free columns, all 16 recipient/token/query JSON identities,
and the public bounded-integer no-wrap inequality. No group exponentiation,
signature verification or crypto import occurs. Group primality/order
remain inherited premises, not consequences of this determinant computation.

[DERIVED correctness] Under the reviewed group/matrix premises, public
completion gives `Y*s=a+tau`. Row i transforms an aggregate ciphertext to
`(g^r,A_i^r*g^(Y_i*X))`; its matching private a_i removes `A_i^r`.
Exact-original componentwise subtraction implements FIFO expiry. Backend
`crypto.py:136` bounds the signed score by `32*127*sum_j |Y_ij|`, with
`q>2*max(bounds)`, sufficient for honest bounded inputs and capacity 32.
Its variable-time integer decoder is not a cryptographic release policy.

[SOURCE identity chain] `registration` binds setup, row, A, recipient and
token digest; `pack/unpack` bind scalar/output envelopes to context, row,
recipient and token. Host-infer uses the exact registered query, and
reader-decrypt requires the matching row. Journal `model.validate_action`
requires the genesis query/route/recipient binding; `Reader.receive`
checks actual output metadata against those signed fields before storage.
The separately invoked private `drain.py` checks authority and verified-history
membership, the registered query ticket and matching output identity before
calling the decoder with that row's retained key. Its private database prevents
a second software decode of the same accepted envelope; it does not remove
the recipient's general credential capability. This is source review only.

## 3. The setup/genesis join and its trust boundary

[EXECUTED public bindings] Named public setup files, embedded canonical
announcements and their original public files, context, registration and
query bodies match every genesis-bound digest. Context ID, public-key
digest and key ID coincide with the same context bytes. The saved public
verification and uncached validation records name those exact source/context
bytes. Their group checks remain attributed to the author's executed output.

[SOURCE transitive binding] `setup_join.py:17` checks the extension's files,
source digests and transcript identities. The extension is included in the
full genesis digest. `common.load_genesis` checks that configured digest;
`identity_fields` carries it into every action and `initial_state` into
state. Model validation checks signed actions against genesis. Authority
and verified-reader databases pin genesis on open and check parent/next
state digests. Replay starts from that genesis and rechecks the chain. The
persistent host also checks fixed config/context bytes, core sources and
the trusted setup-validation record.

[DERIVED] This extension is a trusted initialization declaration. Unchanged
services bind its digest; they do not prove honest randomness or rerun the
new setup verifier on every transition. An arbitrary validation JSON object
is not a standalone cryptographic certificate. The actual full verification,
trusted initialization and pinned continuation are separate required evidence.

[SOURCE timing-bearing metadata] Genesis binds public verification and
context-validation records containing process-work timing. Public command
logs also retain setup/recipient-init durations, and the run reports public
workload timings.

[DERIVED confidentiality scope] The accepted-value setup theorem covers
the specified A/tau/U/context view under honest independent sampling. It
does not prove privacy for physical timing observations or their genesis
commitments, OS generator state, the entire instrumented journal transcript
or later aggregate correctness publication. The author retains this
qualification. This review asserts no new confidentiality theorem for the join.

## 4. Normal history and phase ordering

[SOURCE workload] `driver.py:105` schedules 40 Learn on route zero, Infer
after Learn 10/20/30/40 at rows 0/1/2/3, and eight exact FIFO expiries beyond
capacity 32. Route one stays empty. It then retries exact historical
learn-01 and infer-10 requests, checking the saved envelopes and final head.

[SOURCE reopen] At revision 22, PublicRun saves the authority head and
verified-reader status, calls Run.close, restarts those services and checks
exact equality. Run.stop uses process termination followed by wait. This is
a normal stop/reopen schedule, not a proof of graceful application cleanup
or a broad crash/rollback test. The persistent host continues across it.

[SOURCE acceptance/replay] The authority recomputes and commits before
publication. VerifiedReader recomputes independently before recording the
verified history. An Infer ACK follows durable ciphertext storage and
contains no private score. `driver.py:126` compares ordered authority/
acceptor envelopes and installed state; line 132 calls `Run.replay(True)`
to recompute the whole history.

[SOURCE shutdown before drain] Lines 135-159 check absence of the private
answer database through replay, audit public logs, inventory public storage
and source pins, stop the host and authority/acceptor processes, and require
terminal process states plus clean host exit. Lines 162-170 export public
records and write `public_complete.json`. Only lines 171-174 enter private
drain/comparison/retry. The earlier private-oracle prepare call writes the
known fixture and invokes no decoding.

[DERIVED evidence limit] Source assertions and the saved completion record
can support the normal process-order claim. They do not attest OS isolation,
scheduling or absence of unrelated processes. Private correctness will be
attributed solely to the author's source-pinned aggregate comparison; this
review never opens private answers, scalars, timings or private file hashes.

## 5. Completed public record review

[EXECUTED] `records.py` reconstructs the canonical state chain from the 44
exported envelopes without importing runtime code. All 40 Learn, four Infer,
eight exact-original FIFO expiries, nonce/request identities, parent/next
state hashes and designated query bindings match. The final route-zero queue
contains input ciphertexts 9 through 40; route one stays empty. The final
state digest agrees with the replay export and installed head:
`16ebef46e0c5d19d9601519482cc985ac7c49a09af2aade5109fffa2c8615e83`.

[EXECUTED] The 46 retained event records consist of those 44 accepted
envelopes followed by exact learn-01 and infer-10 retries. Both retries retain
their original request hashes/envelopes; the Infer delivery reports replayed.
The saved revision-22 reopen digest equals envelope 22's next-state digest.
The 44 host records each count one full blob hash for every CAS get. The four
service-start records are two authority and two reader starts, with no fault
flag. Source code explains the terminate/wait/reopen schedule; these normal
records do not establish crash or rollback resistance.

[EXECUTED] All 735 public command records report success and retain public
stdout. Each of host, authority, reader and independent_public_replay has 40
host-learn and four host-infer calls. The exact setup command order is
auth-init, 16 recipient-init, public-build, verify-public, followed by the
wrapper's validation/finalization/query work. No keygen, initializer,
recipient-register, reader-decrypt or inspect-recipient command occurs in
this named command-log corpus. Public arithmetic roles have only inspect,
host-learn and host-infer commands and no `--sk` or `--vector` argument.

[EXECUTED limited log audit] The seven exported JSONL gzip logs contain 917
JSON records and 823 nested JSON stdout/stderr documents. A recursive exact
field-name check finds none of `signed_score`, `sign`, `answer` or
`decode_elapsed_ns`. The public ciphertext inventory's counts and byte totals
match the saved report; this review does not reread those runtime blobs.
This schema result makes no claim about arbitrary strings, process timings,
environment observations or cryptographic secrecy.

[SOURCE / REPORTED executed author evidence] The source-pinned run's full
arithmetic replay succeeds for all 44 transitions. Its public completion
record reports exact authority/acceptor history equality, absence of the
private answer database through the final public checks, terminal public
service states and a clean host exit. The reviewed control flow writes that
record before invoking the first private drain. The final aggregate reports
four matching private integer comparisons and zero new decodes on retry.
No private comparison value or timing was read by this review. The author's
saved sealer additionally reports 16 registration, 44 authority and 44
issuer/command signature verifications; this review did not rerun signatures.

[EXECUTED frozen author identity] The final public report SHA256 is
`9d70fbdde313b91ae732af11d004597dfcf8f6a17a9bbdabd3fb535b0357d791`;
public_complete.json is
`d9defca4a105c268e31951098a1f18fc26d7c56e87742f954812a6b81376b278`.
The author's FINAL_MANIFEST.json SHA256 is
`1d5901a81cb0056f94878878af3737865bb804bf3cd16533e9a3582bb7d676a9`.
All 110 listed public code/evidence files match their byte lengths and hashes.
The author files remained unchanged during this review.

## 6. Reproduction and retained boundary

[EXECUTED] From repository root:

```
python3 research/learn_infer_only/experiments/adversarial_review/public_setup_journal/review.py > research/learn_infer_only/experiments/adversarial_review/public_setup_journal/source_review.stdout.txt 2> research/learn_infer_only/experiments/adversarial_review/public_setup_journal/source_review.stderr.txt
python3 research/learn_infer_only/experiments/adversarial_review/public_setup_journal/records.py > research/learn_infer_only/experiments/adversarial_review/public_setup_journal/record_review.stdout.txt 2> research/learn_infer_only/experiments/adversarial_review/public_setup_journal/record_review.stderr.txt
python3 research/learn_infer_only/experiments/adversarial_review/public_setup_journal/finalize.py
```

[EXECUTED] Both review commands exit 0 with empty stderr. `source_review.json` retains source
identities, public setup hashes, determinant and binding checks. The script
uses an explicit public allowlist, rejects private path components and
imports no reviewed runtime. `record_review.json` retains exported record
checks and exact public artifact hashes. `finalize.py` rehashes the frozen
author manifest and its public files and writes the independent
`review_manifest.json`; it never invokes author programs.

[EXECUTED earlier attempt] The review verifies all 33 source snapshots
against normal_001's own pins. Its only source change is removal of premature
registration-directory creation from setup_join.py. The retained commands
are params (exit 0) and auth-init (exit 1). [SOURCE] ATTEMPT.md and the
source path identify a directory-exists failure before registration,
sampling, services or events. Normal_002 is an intentional corrected fresh
run, not automatic partial resume; historical files remain unchanged.

[OPEN construction boundary] Honest sampling and scalar independence remain
premises; signatures and public consistency do not enforce them. The full
fixed-span credential coalition and timing-view qualification remain. No
additional runtime is needed to complete this bounded review.
Parent owns shared STATUS/NEXT, commits and integration. No network or
metered query was made; no field-wide absence claim is made.
