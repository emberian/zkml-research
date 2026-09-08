# Public-coin setup and durable journal

[EXECUTED] The honest public-coin setup now joins the unchanged durable journal:
**40 Learn, four Infer, eight exact-original expiries and 44 finalized events**.
All 44 transitions pass full independent public arithmetic replay, and the
independent acceptor's complete ordered history equals the authority's history.
All four private signed integers match the independent fixture formula.
Orderly authority/acceptor reopening preserves revision 22; two exact authorized
historical retries preserve their signed envelopes and the final head. The second
private drain adds zero decodes. See [saved report](reports/normal_002/report.json).

[EXECUTED phase order] Every public history operation, full replay, source/log/
storage check and service shutdown finishes before the first private drain.
[public_complete.json](reports/normal_002/public_complete.json) is written
at that boundary. The public phase takes **1629.627796334 seconds**, including
**375.318291250 seconds** for the full independent replay. The setup timer records
55.352910125 seconds and starts after params; its exact scope and child costs are
in [COSTS.csv](COSTS.csv). Private answers, answer hashes and private durations
are omitted. Aggregate comparison publication is outside the host protocol.
These measurements are one normal run on a shared machine, not a speedup claim.

[DERIVED architecture; EXECUTED pins] [SOURCE_PINS.json](SOURCE_PINS.json) inventories
28 unchanged dependency copies: all eight journal/service modules, original four
crypto files (also copied beside setup), unchanged public setup adapter and
persistent host with its frozen source. The run pins 33 source/contract entries,
79 signature-library implementation files, interpreter and native OpenSSL library.
`setup_join.py` changes only setup orchestration. The new Run constructor consumes
the prepared genesis; normal issuance, authorization, acceptance and full replay
remain inherited. The host's inspection cache and full-byte blob hashing are
unchanged. [CONTRACT.md](CONTRACT.md) was frozen before launch.

[DERIVED / EXECUTED setup binding] Genesis binds the accepted public transcript,
registry, all 16 announcements, successful public-verification record, original
setup source, new join source and dependency inventory. Its digest is
`0c81dbc0158b6703c3cc50b1ba4b6ed4e4ad07aed2e7acd8b9c98909deb9e8d3`; context identity is
`b060f1ae45ae1df7d3ed31b20364a884aebdc537b8ad27036b817f04cc9757c6`. Existing canonical genesis binding propagates this
extension into each signed action, state, transition and installed head. The
unchanged services pin that complete genesis; they do not newly prove an honest
sampler or re-execute public setup. The trusted initializer fully verifies the
public completion equations and existing context algebra before continuation.

[EXECUTED credential path; DERIVED limits] The actual commands create independent
registration-signing keys, recipient-owned scalars, public tau/U construction,
full public verification and recipient finalization. No keygen, initializer or
recipient-register command executes; the scalar master and private projection
deliveries are absent from this setup path. The frozen backend still contains
those unused legacy commands. Registration authentication keys and all 16 dedicated
recipient scalars survive; redundant pending copies are removed without a
physical-erasure claim. The acceptance service has no recipient scalar path.

[DERIVED scope] Honest direct tau/U sampling and honest independent fixed-slot
registration remain premises. Each recipient holds its full per-input fixed
query credential; their coalition exposes the whole fixed span on all retained
ciphertexts, including expired inputs. Journal dedup is software behavior and
does not cryptographically restrict that coalition. Inputs use the preregistered
known formula `((n+3)*(j+5) mod 17)-8`, with zero initial state and fresh OS-backed
encryption randomness. This is arithmetic integration, not model utility or a
private learned lifetime. Shared-account processes provide no OS isolation or
operator confidentiality. Classical DDH, Ed25519 and SHA-256 remain separate
assumptions; no malicious-setup, selected-only release, nonlinear-learning,
hardware-finality or post-quantum result is claimed.


[DERIVED timing boundary] Genesis commits the complete setup verification and
context-validation records, including their public process-work timing metadata.
The emitted research logs also measure role durations. The reviewed DDH argument
for accepted tau/U/A values is therefore not a theorem for this whole instrumented
journal view. Physical timing and correlated environment observations remain
outside that theorem, including when committed into genesis. No stronger
confidentiality claim is inferred from this normal functional run.

[EXECUTED retained failure] The first wrapper launch stopped before registration
because it precreated the directory that unchanged auth-init must create itself.
Only params succeeded; no keys, public sampling, services or events were
produced. [normal_001/ATTEMPT.md](reports/normal_001/ATTEMPT.md), exact output and
all 33 source snapshot entries preserve that attempt. The corrected wrapper
removes only premature registration-directory creation. No frozen dependency
or original adapter workload was modified or rerun.

[EXECUTED reproduction/provenance] Exact launch argv and stdout/stderr are retained
in [normal_002/COMMAND.json](reports/normal_002/COMMAND.json).
`seal.py` checks saved signatures, complete ordered parent/FIFO identities and
source origins without DDH execution, RPC or private-file reads; private score
success remains attributed to the pinned executed report. `FINAL_MANIFEST.json`
pins public code and evidence, including the preserved failed attempt. Earlier
adapter closeout lives in [../adapter/CLOSEOUT.md](../adapter/CLOSEOUT.md).

```sh
python3 driver.py prepare --reports reports/FRESH_NAME
python3 driver.py run --root runtime/FRESH_NAME --reports reports/FRESH_NAME
python3 closeout.py --reports reports/normal_002
python3 seal.py --reports reports/normal_002
```

[DERIVED review boundary] Independent review has a separate parent-owned
disposition. No rerun is needed to seal this completed normal workload; no
full384/96 run is authorized by these example commands.

[OPEN next] A stronger recipient-release restriction and honest sampler
enforcement remain separate construction obligations. Root owns shared
STATUS/NEXT and commits. This lane used no network/metered queries or companion
edits and no adversarial, routing, extraction or malformed-input experiment.
