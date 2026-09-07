# Actual 577-coordinate fixed-span encrypted window run

[EXECUTED completed; 2026-09-07] All384 teaching inputs,96 original selected
score queries and256 expirations from the frozen public E2E fixture pass.
Every one of384 exact queue-product checks passes, and every selected score
matches the independent integer oracle. The uninterrupted cryptographic run
took1537.085seconds (25minutes37seconds), within its authorized two-hour bound.
`outputs/SUMMARY.json` records the complete results and costs; `comparison.json`
retains all96 matches, including every original utility failure.

[DERIVED exact interface] Honest private setup publishes the577-coordinate
DDH-IPFE public key and exactly16 fixed projection scalars. The master is
never serialized or passed to the issuer/evaluator. A private issuer encrypts
each bounded signed contribution under the public key with fresh randomness.
The host adds ciphertexts to two public-route windows, expires the exact old
ciphertexts, and evaluates the requested fixed projections. The host holds
all16 keys throughout: every input's full fixed projection span, group-valued
output, magnitude, retained past ciphertext and snapshot is permitted
information. This is a larger interface than sign-only selected release.

[DERIVED scope] `../GENERAL_FIXED_SPAN.md` states the conditional fixed-key
adaptive IND lemma. Every paired input must agree on the full fixed span;
equality of only current-window outputs is insufficient. Privacy assumes DDH,
private honest setup, master/copy erasure and an issuer boundary hiding raw
inputs and coins. Code/process boundaries do not prove physical erasure,
side-channel exclusion or OS isolation. All executed data here are a public
research fixture. Actual text-image nonvacuity is unproved; the matrix's
bounded ambient kernel witness is separate evidence.

[DERIVED exclusions] This run provides no recipient-only release, finality,
origin authentication, arbitrary future independent keys, post-quantum claim
or protected nonlinear learner. The host can retain all old ciphertexts. A
plaintext Yx implementation realizes the same observable learner; the FE
realization additionally retains raw vectors encrypted with the stated
conditional representation privacy. It is not the separate BFV/journal run
and does not replace that run's trusted-reader boundary.

## Evidence and process boundaries

[EXECUTED] `run.py` uses the exact group/parameters already tested in
the micro and the already installed OpenSSL backend from `../native_pow.py`.
The full-run manifest pins code, native library, source fixture/query files,
theory and the native micro's2315 Python equality checks. The timed full run
does not repeat private-exponent Python checks. No new keys or queries are
selected from observed outputs.

[DERIVED process contract] Initializer stdout contains only completion and
public artifact sizes. Issuer stdout contains only progress/byte counts;
private timing diagnostics and source paths stay in explicitly separate
issuer/coordinator files. The evaluator command stream contains only public
event IDs, routes, history IDs, query indices and ciphertext paths. The
evaluator never reads issuer commands, input vectors or an oracle. The
coordinator and standalone `oracle.py` may read the public research inputs.
Shared-account subprocesses demonstrate this data flow, not an adversarial
OS boundary. The implementation remains variable-time as a whole.

[EXECUTED integer control] `oracle.py` independently replays all384 signed
vectors and96 queries without importing any cryptographic code. It expires
before insertion and computes integer dot products directly. All96 results
match the previously landed oracle. The unchanged utility denominators are
52/96 overall,44/80 for nonempty windows and18/32 at final checkpoints.
Every success and failure is retained for encrypted-score comparison.

[EXECUTED verification] The host checked subgroup membership for every input
ciphertext, recomputes the exact current-queue product after every learning
update and decodes all96 selected scores with the bounded table. This is
honest-program correctness, not proof-carrying computation or authenticated
continuity. Checkpoint hashes detect accidental mismatch; they do not prevent
an operator from replacing a complete history.

## Replay and resume

[EXECUTED launch and independent integer preparation] From the repository root:

```sh
python3 -B research/learn_infer_only/experiments/private_construction/fixed_span/scaling/full_run/run.py
python3 -B research/learn_infer_only/experiments/private_construction/fixed_span/scaling/full_run/oracle.py prepare
```

[EXECUTED final comparison and cost summary; both exit0]

```sh
python3 -B research/learn_infer_only/experiments/private_construction/fixed_span/scaling/full_run/oracle.py compare
python3 -B research/learn_infer_only/experiments/private_construction/fixed_span/scaling/full_run/summarize.py
```

[DERIVED] A new isolated `--out` directory performs fresh setup/encryption;
the default existing directory resumes its saved progress. Resume checks its
source/command/public-key/credential hashes and current queue identity. A
deadline/failure creates `STOPPED.json`; no successful completion is written
for an incomplete run. A later authorized invocation supplies a new bounded
run budget. Actual crash/resume was not adversarially tested in this tranche.

[DERIVED replay caveat] A completed default directory takes the resume path
and skips work already saved. Use a fresh `--out` directory for a new timed
crypto run. The launcher records the current invocation's wall time, while
operation counters may include saved work; it does not aggregate wall time
across interrupted invocations. The delivered full-run timing is for one
uninterrupted invocation. Resume integrity/authentication and accumulated
multi-invocation performance remain separate follow-up work.

## Measured costs, all retained artifacts counted

[EXECUTED] Completed loop counters account for499,972 native exponent calls:
577setup,221,952input encryption plus1message-table setup,221,952subgroup
validation,55,488fixed projection and2decoder-setup calls. These count API
calls through completed loops, not low-level instructions or RNG rejection
trials. The full run performs no per-cipher Python private-exponent checks.

| Instrumented section | Seconds |
|---|---:|
| Honest setup and16 fixed-key issuance | 5.190 |
|384 public encryptions | 706.492 |
|384 full ciphertext subgroup validations | 562.603 |
| Insertion and256 exact-byte expirations | 90.540 |
|384 explicit queue-product audit recomputations | 135.490 |
|96 fixed group-valued projections | 18.245 |
|96 bounded integer decodes | 5.638 |
| Issuer ciphertext serialization | 7.316 |

[EXECUTED] Role wall times are5.760seconds for setup,716.941 for issuance,
and813.901 for evaluation. The whole measured invocation is1537.085seconds.
Instrumented sections do not exhaust wall time: process/library initialization,
metadata hashing, progress writes and other work remain included in the role
and total walls. These are one full run under shared load, not steady-state
latency estimates. Cached model execution/token encoding were not performed
and are excluded from these costs.

| Actual retained or live artifact | Bytes |
|---|---:|
| Public key | 147,712 |
| All16 fixed projection keys | 4,096 |
| One ciphertext | 147,968 |
| Final64 queued ciphertexts plus2 aggregates | 9,765,888 |
| All384 retained issued ciphertexts | 56,819,712 |
|30 retained aggregate checkpoint files | 8,878,080 |
| Other recorded evidence, excluding the summary itself and memory samples | 583,920 |

[EXECUTED] The384 input ciphertexts and30 aggregate checkpoints are retained;
window expiry does not erase the host's prior view. Current queue entries
refer to those same input files, so their bytes must not be added twice when
counting on-disk retention. The public key/keys are included in the last
"other evidence" row, which is a category total rather than an additional
disjoint sum of every displayed row. JSON manifests retain every file's hash.

[EXECUTED] The memory observer took104 samples at roughly10-second intervals,
starting after setup. Maximum observed RSS is25,280KiB for the coordinator,
29,600KiB for the issuer, and43,648KiB for the evaluator. These are per-role
sample maxima, not OS high-water marks, aggregate private memory or model
memory requirements. The one-shot decoder table size5333 and exact raw
payload counts are documented in the parent scaling note.

[EXECUTED utility] All96 encrypted scores preserve the original classifications:
52/96correct overall,44/80for nonempty windows and18/32at final checkpoints.
There is no new utility gain or claim of hidden nonlinear cognition. The
comparison record SHA256 is
`6f147d63b50cb8a041eb745fb2593d1a4a89dc9bef666aad89af2ddcdd72043e`.

[EXECUTED accounting] No Scry/Kagi/web queries, downloads, package installs,
model runs, training, private-user input trials, unissued queries, extraction
tests, companion edits or commits are performed. Existing earlier stopped
tasks remain stopped. Generated binary artifacts are gitignored; exact hashes
and sizes remain in the retained manifests and can be regenerated.
