# Public-seed durable join: source handoff, unexecuted

[DERIVED disposition, 2026-09-08 14:35 UTC] **Preparation review only;
no prelaunch approval and no runtime authorization.** The inspected setup,
normal schedule and inherited identity/replay seams are coherent. The new
outer launcher, public closure checker and final preparation gate still need
their completed-source review. Root explicitly stopped launch consideration
at 14:31 UTC because a proposed 45-minute attempt cannot fit the 15:00 goal
deadline. No cryptographic execution occurred in this successor during this
review, and this reviewer ran no backend, XOF, signature or private operation.

[EXECUTED identity] The six current preparation files were copied into
`source_snapshot/`; these copies fix the scope while the author continues
preparation. Their source hashes are:

| File | SHA-256 |
|---|---|
| `setup_join.py` | `080536e9cc416a5f7fb9dcc33eeeebe185fa697c1d36c8d14fc7a4d3c186cff5` |
| `driver.py` | `2a93ab7da3451a91e87358a176739976c02fc8e68485c95b8fc9db2be13a5c30` |
| `private_oracle.py` | `5e384c9cacd8d7f5e232f1231a5215bd1ef03aa4016b0903f2b6c0d37f4f34c0` |
| `CONTRACT.md` | `1f806e688fd4588bfd8367ed94e01a0222662e08649ea8fee951179778a72812` |
| `SOURCE_PINS.json` | `ed78111662429aecadfe206244c458c4c97a1d7ded3032191f8a1ccdaf0edf24` |
| `WRAPPER_ORIGINS.json` | `0f73cbb6136acb6fd3dfaefcc580f3d3662fb01f4d68b67504c24e42ef3b0a81` |

[EXECUTED] Independent hashing and mode checks match all 36 copied
dependencies to their named unchanged origins. The nested seed adapter's
12 source/contract/helper pins remain the accepted adapter identity; its
manifest is copied rather than rewritten for the new path. Thirty-three
Python files parse without importing them. The retained `source_results.json`
and stdout distinguish this source snapshot from a final frozen launch packet.
No author artifact, predecessor, shared ledger or companion source was edited.

## What the proposed run would add

[SOURCE/DERIVED] The completed standalone public-seed adapter demonstrated
fresh complete registration, the full-domain concrete SHAKE recipe, normal
33/4/1 arithmetic and public-before-private closure. The earlier durable
public-coin journal demonstrated signed durable histories and replay with
independently sampled accepted tau/U values. This successor would join the
fresh registry-bound seed context to those actual durable services. It is a
new integration observation rather than a new confidentiality theorem.

[SOURCE] The new `PublicRun.__init__` initializes only transport fields
from the prepared genesis and does not invoke the old `Run.__init__` dealer
setup. All operational crypto, journal, verified-reader and persistent-host
sources remain byte-identical. The seed wrapper is separately copied with
its own original relative layout and source inventory, avoiding a silent
change to the source identity included in its transcript.

## Setup and genesis binding

[SOURCE] `setup_join.py:42–73` creates a fresh root, one complete
authentication registry and all 16 recipient announcements before the sole
seed public-build call. It delegates to `source/seed_setup/seed_setup.py`,
not the old public sampler. Full seed tape/context replay and uncached
context validation precede recipient finalization. The inherited completion
operates on public group values; no scalar master or scalar projection
delivery is called on this constructor path. All 16 recipient scalar keys
are deliberately retained. Pending-copy removal is not physical erasure.

[SOURCE/DERIVED] The genesis extension at lines 80–82 binds the entire
transcript, registry, all announcements, context and verification/validation
records. It additionally includes the transcript's complete `source_identity`,
unchanged nested adapter inventory, full domain digest, seed bytes, suite,
cap, join source and outer dependency inventory. `verify_binding:19–40`
rechecks the corresponding hashes, context/registry identities, rows, complete
raw-tape replay flags and all announcement records. The full transcript
contains the full domain; a digest is not substituted into the SHAKE recipe.

[SOURCE/DERIVED] Existing `common.py:55–65,145–151` pins the complete
canonical genesis and puts its digest in actions and states. Existing
`model.py:25–26` and CAS query checks bind the registered query, context,
row, recipient and token. Authority and verified-reader databases pin the
same genesis. Consequently the new extension is included in the existing
signed-history identity chain. Unchanged services trust the pinned setup
declaration; they do not independently prove honest registration or execute
a new public-seed verifier.

[DERIVED] The full verification and context-validation records contain
process timing/counters. Their commitments in genesis remain outside the
mathematical ROM/DDH transcript guarantee. Concrete SHAKE256, classical
programmable-ROM/DDH, independent honest scalar generation and Ed25519
authentication remain separate assumptions. No QROM/PQ, malicious setup,
operator isolation or timing-privacy result follows.

## Exact normal schedule and supported retry

[SOURCE/EXECUTED] The inspected driver and oracle both use Learn counts
1 through 33 and Infer rows 0/1/2/3 after Learn 1/16/32/33. An independent
index schedule confirms 37 finalized events, revision 18 after Learn16 and
its Infer, exactly original Learn1 expiry at Learn33, and final FIFO inputs
2 through 33. All records stay on route zero with capacity 32; route one
remains empty. The known public vectors are the existing fixture, not a
semantic learner or hidden-state experiment.

[SOURCE] The snapshot's orderly reopen closes/restarts authority and
acceptor and checks identical head and verified status. Its sole historical
retry resubmits the exact saved Infer1 request after revision37, requires
the original signed envelope and replayed reader status, and compares head,
received/selected counts and verified status before and after.

[SOURCE/DERIVED] This uses a supported existing path: authority
`submit:54–62` looks up an exact stored request before current-head checks;
verified-reader `sync` compares the stored envelope before new-transition
checks, and `receive` requires a matching recorded Infer finalization.
It is neither a crash test nor a stale-message bypass. These source facts
make the proposed test meaningful; successful runtime behavior remains
unobserved.

## Public/private boundary and unfinished gates

[SOURCE] `public_run` performs all normal events, full independent history
and arithmetic replay, final complete seed replay, source checks, public-log
checks and CAS inventories. It closes the persistent host and all recorded
authority/reader processes before writing its public-complete report. Its
AST contains no call to `private_call`. `private_run` is a separate entry
that requires `PUBLIC_GATE.json`, exact execution pins, public verification
and public seal hashes before one drain and one direct integer comparison.
There is no second private drain in the snapshot. The inherited drain returns
the exact count fields this wrapper checks.

[OPEN] This source separation is not yet acceptance of the complete phase
contract. `launch.py` and `public_close.py` are named dependencies but their
final source/phase-order checks and final execution pins were not reviewed
in this bounded snapshot. Before any later authorized attempt, review the
whole-group 2,700-second deadline and bounded cleanup, absence of descendants
even after a leader exits, failure/no-retry behavior, exact public seal
coverage, all public-group closure before private continuation, and immutable
source/environment checks at each gate. Confirm the final checker independently
validates the signed ordered history, original FIFO/query joins, source/context
bindings, public storage and final setup-replay record. A periodic elapsed
check alone is insufficient to interrupt a blocked inherited RPC.

[OPEN] No accepted reviewer gate is emitted by this handoff. The author may
finish and freeze preparation, but the inspected snapshot does not authorize
launch, continuation or a retry. Any future source changes require a fresh
exact-source gate review; any eventual public replay and private comparison
must be reported as execution only after they occur.

[DERIVED scope] The full 16-row recipient coalition retains per-input
capability for retained and expired ciphertexts. Four software-selected
answers and journal dedup do not attenuate it. Private scalar/answer material
would stay under ignored paths, and aggregate comparison results would be
outside the closed cryptographic transcript. Those are planned source
boundaries, not observed private outcomes or an OS-isolation proof.

[EXECUTED] Command:

```text
python3 research/learn_infer_only/experiments/adversarial_review/public_seed_journal/check_source.py > research/learn_infer_only/experiments/adversarial_review/public_seed_journal/source_check.log 2> research/learn_infer_only/experiments/adversarial_review/public_seed_journal/source_check.stderr
```

[EXECUTED] Exit zero; status `PASS_SOURCE_SNAPSHOT_ONLY`, stdout equals
`source_results.json`, stderr empty. This used file hashing/modes, AST parsing
and index arithmetic only. No crypto, production XOF, private read, service
start, network/Scry query or PDF download occurred. Corpus/instrument for
the no-private-call claim is the captured `public_run` AST; it is not a claim
about arbitrary operators or unreviewed future wrappers.
