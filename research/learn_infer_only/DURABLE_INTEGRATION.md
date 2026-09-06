# Materialized resident release through the existing durable path

[EXECUTED, 2026-09-06] The earlier empty-rootWrites witness now has a proposed
successor using actual `CellState.Materialized` / `ValidatedPatch` /
`DurableDataIntent` / `Candidate.ofData` objects. The public Bool cell changes
from false to true, its canonical bytes from `[0]` to `[1]`, and its existing
one-byte root from 0 to 1. Full data preflight accepts. No companion tree was
edited; the deliverable is a maintainer patch plus recorded local proof checks.

[SOURCE: implementation read] `Theory/CellState.lean:329`,
`ValidatedPatch.apply`, derives post bytes and root from the logical patch.
`Kernel/DurableDataIntent.lean:343`, `execute`, performs journal lookup before
preflight, then an explicit atomic install/crash transition. Its data snapshot
keeps canonical bytes coherent with installed roots (`:235`, `DataSnapshot.install`).
`Kernel/ReplicatedSettlementFinality.lean:89`, `Candidate.ofData`, retains the
exact erased payload. All paths refer to `/Users/ember/dev/minidregg/`.

[DERIVED scope] The earlier Context uses parent/next as public arithmetic values.
The integration is instantiated at the existing Bool-cell materializer, where
the canonical public value is also the one-byte root value. The result does not
make arbitrary hash digests add correctly. No encrypted state or private output
is constructed. Fixed charge 1 per lane is budget-premise inhabitation, not a
measured or proposed deployment cost.

## What the new path forces

[EXECUTED] Proposed source:
`formal/durable_integration/Assurance/ResidentDurableIntegration.lean`.

| location / theorem | checked claim |
|---|---|
| [EXECUTED] `:111`, `Plan.intent` | One derived write contains the validator-minted post bytes/root; genesis is read-only; slot token, exact charge, and full context packet are derived. There is no host rootWrites or event setter. |
| [EXECUTED] `:133`, `Plan.opens`; `:297`, `authorized` | Independent selection pins genesis/state ids, exact genesis bytes, recipient and authorization; actual snapshot bytes open the parent and genesis. The sole current prefix is the journal in chronological order. |
| [EXECUTED] `:403`, `materialized_durable_binding` | Accepted context/finality, full preflight and unrecorded transaction force actual execute to install the exact materialized post; receipt.next equals installed root.value; the slot token is consumed. |
| [EXECUTED] `:419`, `authorized_materialized_arithmetic` | With explicit descriptor satisfaction for that receipt word, the existing arithmetic lemma additionally forces the wrapped sum at the installed root. No unconditional per-receipt Fiat–Shamir soundness is asserted. |
| [EXECUTED] `:522`, `Closed.subject` | The same accepted FS receipt inhabits the descriptor premise, the nonempty state-changing materialized transaction, full preflight and real finality checker. |
| [EXECUTED] `:312`, `gatedExecute` | Journal-first wrapper delegates every store transition to existing execute. Fresh calls require authorization; retries recover the recorded old packet without rerunning inference. |
| [EXECUTED] `:375`, `consume_before_packet`; `:354`, `gated_retry_exact` | A fresh outward packet follows the modeled atomic consumed installation; retry returns the same journaled packet. Crashes return no packet. |
| [EXECUTED] `:336`, `installed_packet_cannot_be_relabelled` | The release helper takes no extra Plan; an accepted packet is read from the installed journal and cannot be substituted by passing a second context. |
| [EXECUTED] `:190`, `same_id_changed_packet_refused` | Altering any encoded context field, including recipient/output, under a recorded transaction id is a conflict, even with equal post roots. |
| [EXECUTED] `:254`, `DurableReachable`; `:264`, `reachable_preserves_genesis` | Actual ready/fresh data commits generate a reachable history; journal length is monotone and exact selected genesis bytes are preserved. Independent head/log/durable fields are absent. |
| [EXECUTED] `:444`, `finalized_context_unique` | Existing cross-epoch PrefixDiscipline reaches context uniqueness through Candidate.ofData, the complete replay envelope, and injective context encoding. |

[DERIVED] This closes the specific first-tranche arbitrary-effects seam: its
accepted Context could coexist with unrelated rootWrites and an unfunded charge.
Here the effects are generated from the selected validated materialized post and
the existing full preflight checks them. Independent review's old bad-effects
witness remains at `experiments/adversarial_review/RestoreSeamWitness.lean`.

[EXECUTED audit finding and repair] Independent review found that the
first version of `releasedPacket` accepted an extra caller Plan, permitting a
valid accepted outcome for one transaction to be labeled with another packet.
The same-Plan theorem was true, but the helper API left that substitution
expressible. The checked repair removes the caller Plan and derives accepted
packets from the installed journal itself. The red witness is
`experiments/adversarial_review/ReleasePacketSeamWitness.lean`,
`accepted_result_can_be_relabelled`, with unsafe source snapshot `b174ddb…`;
its command/output is `lean_release_packet_02.json`. This refutes the old helper
API composition, not its same-Plan theorem. The finite script now retains the
same red/green recipient substitution control.

## The remaining semantic gap has a checked falsifier

[EXECUTED] `formal/durable_integration/Assurance/ResidentDurableCollision.lean:90`,
`root_arithmetic_not_logical_step`, retains the lawful Bool codec but deliberately
uses a constant-zero root function. The real validator changes false to true;
the same accepted genuine FS receipt has a satisfying descriptor for root
arithmetic `0+0=0`; exact openings, full preflight and the actual finality checker
all accept. `:117`,
`exact_install_survives`, proves exact byte installation still holds.

[REFUTED: promoting root-value arithmetic to the logical Step for arbitrary
materializers] Exact installation and root arithmetic alone do not identify the
authorized computation on opened logical state. The constant root is an explicit
broken sibling, not an attack on a cryptographic hash or imported theorem.

[OPEN] An encrypted-state continuation needs separate context fields for state
commitments and arithmetic values, canonical openings tied to a genuine Step
descriptor, and the relevant binding/hiding assumptions. This lane's proof does
not supply that descriptor. The collision fixture must remain beside a future
refinement rather than being removed because its root is intentionally weak.

## Executed schedules and limits

[EXECUTED] `python3 research/learn_infer_only/experiments/durable_integration/audit.py`
writes `experiments/durable_integration/results/audit.json`. It is a finite
public schedule model, not an encryption or filesystem implementation. Its
recorded controls show:

- [EXECUTED] Crash before install leaves old bytes and emits no packet; crash
  after install keeps the complete new snapshot, and exact retry emits the
  original addressed context packet with no new authorization or budget debit.
- [EXECUTED] A restored host manifest is refused by the intact current authority;
  restoring the authority itself re-enables the old fresh transition.
- [EXECUTED] Same-root/different genesis bytes pass root-only preflight but fail
  the adapter's exact opening check. Recipient substitution on retry conflicts.
- [EXECUTED] The broken split check/install schedule yields two old-snapshot
  approvals; serial execution produces one fresh authorization. Lean's
  `Closed.split_check_install_duplicates` separately exhibits cached readiness
  for two distinct transactions, refusal at the second current preflight, and
  a blind bypass installation with two journal entries and two budget debits.

[OPEN physical ceiling] Reachability is a mathematical invariant to establish
for the independent authority. It does not stop an implementation from rolling
back or overwriting the authority's storage. The gate, proof check, preflight,
atomic install and outward delivery must be refined by the physical handler;
the existing `DurableDataIntent.ImplementationRefinement` remains uninstantiated
here. PrefixDiscipline, authenticated votes, live availability, signed command
authorization and recipient encryption remain separate premises/residuals.
An output already delivered can be copied; exact packet retries are allowed.

## Verification and resume

[EXECUTED verification] Final source-matching checks are
`lean_ResidentDurableIntegration_14.json` and `lean_ResidentDurableCollision_06.json`.
All 45 theorem inventories are exact-output pinned; each uses only `propext`,
`Classical.choice`, and `Quot.sound`. `review.json` records successful staged
Assurance umbrella elaboration, the existing Theory/Selvage import-boundary
script, read-only patch applicability, companion HEAD/status and source hashes.
The companion HEAD read was `6937394e1dc2c2aaff986c7d4b3a258aca5d16fd`.

[EXECUTED independent review; logs inspected] The adversarial lane independently
compiled the final main and collision modules in its own overlay:
`experiments/adversarial_review/lean_durable_04.json` and
`lean_collision_01.json`, both exit 0 with `inputs_unchanged: true`. They match
the hashes below. Its review identified the old packet-helper seam, verified
the repair, and confirmed that the collision subject carries the descriptor
premise for the same receipt. This is separate from this lane's own checks.

[EXECUTED] `inspect_sources.py` also counts one pin per local theorem and
red-tests its forbidden-token scan against explicit `sorry`, `admit`, and
custom-axiom strings. `source_inventory_overescaped.json` retains a superseded
overescaped regex attempt rather than treating it as evidence of absence.
All compilation failures remain recorded; they include namespace/elaboration
mistakes with transient `sorryAx` in failed output. Only the final source-matching
successful checks establish the result.

```sh
python3 research/learn_infer_only/experiments/durable_integration/audit.py
python3 research/learn_infer_only/experiments/durable_integration/check_lean.py
python3 research/learn_infer_only/experiments/durable_integration/review.py
```

[DERIVED handback] The patch adds two Assurance modules and root imports. It
depends on the first tranche's `ResidentReleaseContext` module from
`formal/minidregg-resident-release.patch`. Build output stays in a private ignored
overlay; the harness refuses output through companion symlinks. The umbrella
check uses existing dependency oleans, not a clean whole-source Minidregg build.

[EXECUTED hashes] Main source:
`80239c7fbc060c6f0c60a4a085c78b078987b46ffbf7b17017f3f92af57c022a`.
Collision source:
`b410206075a03338ef6d569c777c2d2a2420f3ddc8f3280cfcf6d062685a028c`.
Patch: `945d70ab4a7504f25bbc598f70951fae8f1a1a5318459a396bfe1fcbf8e57a5a`.

[DERIVED integration] The dependency is `ResidentReleaseContext`; the old
empty-rootWrites restore adapter is superseded as the intended runtime witness.
It remains useful research evidence for its scoped refusal/counterexamples,
not an alternative fresh-release endpoint beside `gatedExecute`.

[DERIVED proposed ledger updates] STATUS/NEXT may mark the nonempty materialized
data-preflight seam closed in this public witness. Keep encrypted-root/Step
refinement and physical authority durability as separate next tasks. CREDENTIALS
may replace separate head/log toy fields by the actual canonical snapshot and
exact journal prefix in this model. No NoSurvivingReadAll or Shielded/Dark claim
changes. VERDICTS §7 receives no new cryptographic or performance conclusion.

[EXECUTED search accounting] Scry queries: 0; web queries: 0. This bounded lane
used local source via `rg` and direct reads, including the named original
formal modules and actual companion kernel paths. No literature-absence claim
is made. No changes to minidregg, breadstuffs, VERDICTS, or shared lane ledgers.

## Second tranche — public signed-byte EMA semantic bridge

[EXECUTED] The new patch `formal/durable_integration/minidregg-ema-semantic-bridge.patch`
adds four modules, with 48 exact axiom pins (13+7+13+15). Its SHA-256 is
`3f5d9c6895b5a423ce134e586c02141e448052ed559bca0a1aeec707dd99232a`.
All first-tranche settled source/patch hashes above remain unchanged. This patch
needs the earlier resident-release and durable-integration patches. It is not
installed in minidregg; it proposes both Compiler and Assurance root imports.

[EXECUTED] The new keystone is
`formal/durable_integration/Assurance/ResidentEmaRelease.lean:178`,
`ema_durable_binding`, proving the statement `EmaDurableBinding` at line163.
An authorized **new EMA** receipt, descriptor satisfaction of that same receipt's
word, actual full preflight and fresh transaction imply actual logical
`post = floor((7*pre+input)/8)`, exact current canonical source bytes, exact
installed post bytes, receipt.next equal to the installed root value, a consumed
slot token, and the exact packet extracted from the installed journal.
`authorized_context` at line143 additionally exposes exact selected openings,
context equality, boundary linking, authorization and recipient selection.
`retry_exact_packet` at line196 returns the recorded packet through the existing
journal-first executor. No second store executor was introduced.

[EXECUTED] `Compiler/ResidentEmaCertificate.lean:32–37` composes existing
`rangeGadget` instances and source `Term` constructors, then calls existing
`emit`. Three byte scalars C,U,C′ and a three-bit remainder r obey
`7*C+U=8*C′+r`. `system_sound` proves the integer equality from accepted ranges:
left≤2040 and right≤2047 are both below BabyBear p=2013265921. The existing
compiler/evaluator/checker are used throughout; there is no handwritten gate
list or replacement AIR. `descriptor_shape` at line41 kernel-pins 4 public
scalars,31 variables,153 wires,122 gates and32 zero constraints.
`descriptor_semantic` at line79 proves mathematical floor, including negative
numerators. `ema_fullbyte_closed` at line87 proves [-128,127] closure; the narrower
[-127,127] contract is separately closed as well.

[EXECUTED] `Assurance/ResidentEmaCell.lean:44`, `biased_representation_exact`,
proves the explicit conversion from the HE program's two's-complement byte to
this codec's biased byte: adding128 modulo256 makes signed value `byte−128`
exactly equal to the two's-complement denotation. The lawful codec distinguishes
absence (`[]`) from every present byte (`[b]`). `canonical_opens` at line81
recovers the logical state from exact bytes, for **any** root function. Neither
this result nor the keystone assumes a collision-free or injective root function.

[EXECUTED] `ResidentEmaRelease.Linked` at line40 selects program1/version1,
deterministic randomness rule(0,0), command<256, fixed learn acknowledgement0,
and exact pre/input/post scalar boundaries. Parent and next refer to roots;
they are never substituted for logical EMA coefficients. `checked_fiatShamir`
at line64 reaches the existing generic FS verifier. `receipt_price` at line95
instantiates the existing generic committed-terminal soundness theorem on this
new descriptor, and `gate_price_explicit` at line104 proves its error term
`(t+9)*161/p^6`:154 residuals,8 sumcheck coordinates,9 FS rounds. This is a
classical lazily sampled ROM, full-word straightline-knowledge statement for
a fixed context instance, not a new adaptive-policy, QROM or succinct/ZK claim.
[SOURCE] The generic event reading at absolute companion
`/Users/ember/dev/minidregg/Compiler/CommittedTerminalFiatShamir.lean:614`
uses the exact-relaxation threshold δ<1/n. [DERIVED] For this153-wire instance the
false-logical-Step event reading needs δ<1/153. The earlier Stage0 adaptive
composition is not automatically a lifetime EMA price.

[EXECUTED] `ResidentEmaWitness.subject` at line81 builds a real `fsProve` receipt
whose own word both passes the new checker and satisfies the new descriptor.
`public_subject` and `constant_subject` at lines102/108 instantiate the full
preflight/finality/openings for state0→15 on input120, including the deliberately
constant-root materializer. Roots can remain equal while exact bytes change.
`constant_wrong_post_materializes` at line128 exposes a different validated
post0→16 with the same roots and successful opens/preflight. Its boundary-link
premise is inhabited by `forged_linked` at line134; the descriptor universally
refuses it at line146. `wrong_next_refused` at line158 independently tests the
root/currentness leg. These are scoped falsifiers of omitting the semantic
relation or next-root guard, not attacks on a cryptographic hash.

[SOURCE] The prior HE exhaustive contract is explicitly
`experiments/he_closure_costs/ema_bits.py:65`, `range(-127,128)`; the TFHE program
`tfhe_ema_probe/src/main.rs:37` takes raw8-bit vectors with length assertions.
The earlier65,025-pair experiment is not relabelled as covering−128.
[EXECUTED] `experiments/durable_integration/ema/audit.py` now independently runs
that same existing Python bit-circuit on all65,536 signed-byte pairs, checks the
QR equation/range and closure, and rejects65,536 in-range neighboring wrong
posts. It records63,516 changed-state cases and28,800 negative numerators with
nonzero remainder. Histories are0→15→−2 for[120,−120] and0→−15→1 for the reverse;
minimum cases give EMA(−128,−128)=−128 and EMA(−128,127)=−97. `audit.json` records
the imported source hash. The actual encrypted TFHE run remains its separately
recorded four updates; this additional exhaustive run operates on public bits.

[EXECUTED] Reproduction and retained outputs:

```sh
python3 research/learn_infer_only/experiments/durable_integration/ema/check.py Compiler/ResidentEmaCertificate.lean Assurance/ResidentEmaCell.lean Assurance/ResidentEmaRelease.lean Assurance/ResidentEmaWitness.lean
python3 research/learn_infer_only/experiments/durable_integration/ema/audit.py
python3 research/learn_infer_only/experiments/durable_integration/ema/inspect.py
python3 research/learn_infer_only/experiments/durable_integration/ema/review.py
```

[EXECUTED] Final source-matching Lean logs are
`lean_ResidentEmaCertificate_07.json`, `lean_ResidentEmaCell_07.json`,
`lean_ResidentEmaRelease_08.json`, `lean_ResidentEmaWitness_06.json` in `ema/`.
All exit0 with inputs unchanged;46 pins list only
`[propext, Classical.choice, Quot.sound]`, and the order/minimum-boundary pins
have no axioms. `review.json` records exact direct-import source/olean hashes,
source-scan scope and red-tested forbidden-token instrument, successful staged
Compiler/Assurance umbrella checks, read-only import-boundary script, and
`git apply --check`. Existing companion oleans were reused, not rebuilt here.
The command/result history retains failed elaboration and inspection attempts;
only source-matching successes support these claims. [EXECUTED] A separate unified overlay also rebuilt these frozen sources as
part of16 modules/265 pins, with four umbrella checks and actual combined-patch
apply/content comparison: `experiments/integration/results/run_002/report.json`
reports passed. This reuses companion dependency oleans and is not a clean
whole-tree rebuild. Independent adversarial source review subsequently passed at
these frozen hashes: `ADVERSARIAL_REVIEW.md` §9 and its four `lean_ema_*_01.json`
module checks. Its independently compiled census also checked all65,536 actual
descriptor candidates. A deliberately chosen zero-oracle false-receipt control
keeps the descriptor-premise/ROM distinction explicit; it is not a hash attack.

[OPEN] This closes the **public semantic** gap exposed by the first-tranche
constant-root tooth. The checker still sees canonical plaintext openings and
all153 field elements; even with acknowledgement-only learn packets the receipt
reveals its witness. It neither proves an encrypted-root opening relation nor
hides state/input/post. Required next refinement: bind actual ciphertext state
and input issuance to these exact logical openings and the HE transition,
without giving the host a surviving read-all credential, and replace the
full-word evidence with an appropriately proved hiding construction. The Lean
algebra/codec result plus exhaustive Python bit-circuit agreement is not a Lean
refinement theorem for TFHE-rs or a cryptographic proof of its encrypted circuit.
Physical durable atomicity, complete output mediation, secret entropy, recipient
transport, and the first tranche's setup/privacy residuals remain open.


## Third tranche: exact public ciphertext-window history

[EXECUTED] The new patch
`formal/durable_integration/bfv_window/minidregg-ciphertext-window.patch`
(SHA256 `630d2fa6c0ec0c2b049fcc0affeca6c9b22a5a264cf638890780e9e0fe5eb4eb`)
adds three modules with44 exact pins. Detailed statements, hashes, commands,
source paths, witnesses and residuals are in the owned
`experiments/durable_integration/bfv_window/README.md`; `review.json` records
green Theory/Assurance umbrella checks, actual patch apply/content comparison
and full copied Theory/Selvage import-boundary checks. First-tranche and EMA
patches remain frozen. Companion dependency oleans were reused.

[DERIVED] `Theory/CiphertextWindow.lean:294`, `reachable_queue_sum`, proves
accumulator=sum(exact current queue) and length≤W after every checked history
in any additive commutative ciphertext group. Admission sees canonical public
ciphertext bytes; expiry must match the current head id and exact canonical
bytes. `all_finite_horizons:339` constructively continues an admitted input
stream for every finite horizon, retaining admission/id provenance. There are
no plaintext fields, root assumptions, noise bounds or cryptographic claims
in this algebra theorem.

[DERIVED] `Assurance/CiphertextWindowCell.lean:188`,
`executed_history_invariant`, ties that logical history to actual canonical
DataSnapshot bytes, existing validated resource writes/preflight/installs and
the actual journal length **for exclusive window-admission histories**.
Separately journaled inference/no-op needs a journal admission projection;
generic authority revision is not a window counter. A constant-root witness includes
nonzero admission, exact oldest-ciphertext expiry and replay of the exact
recorded transaction without another subtraction. Wrong ciphertext, stale id,
denied input and a detached counter/journal history are refused; bypassing
expiry equality leaves precisely old−proposed ciphertext debt.

[EXECUTED] Actual vendored BFV serialization controls found two concrete seams:
the empty zero placeholder panics on serialization, and seeded/expanded
ciphertexts can have identical polynomials with different protobuf bytes.
A compatible public nonempty zero, obtained by public ciphertext self-
subtraction, normalizes both tested cases using `ct+zero`, preserving the
tested public-key bytes. `serde_check_02.json` retains commands, source hashes,
expected caught panic and positive controls. These findings do not attack
the existing public-key window; they refute calling raw serialization a
universal lawful canonical codec without its representation domain.

[OPEN] The actual Rust RNS/NTT/group/normalization refinement, admission source
and range proof, implementation phase/readout relation, BFV descriptor/FS
adapter, hidden evidence and physical persistence/output mediation remain
explicit obligations. The HE lane separately composes this exact queue sum
with a modular phase map and horizon-independent noise premises. The queue
proof itself neither decrypts nor proves absence of a reader. Scry0/web0.


## Fourth tranche: actual journal/process crashes

[EXECUTED] `experiments/durable_integration/persistent_journal/README.md` and
`results/run_005/report.json` record the local SQLite/Unix-socket fixture:
122 subprocess commands, four actual SIGKILL boundaries, twelve races through
pairs of separate authority workers, eight concurrent exact retries, sixteen
changed-identity refusals, host restore and two negative controls. Fixture
context/intent/token/packet bytes are exported from the existing accepted
Bool subject; computational validity is an explicit public allowlist premise,
not a new cryptographic verifier. No frozen Lean source changed.

[EXECUTED] Uncommitted installation rolls back; committed installation survives
restart. The publication/acknowledgment gap yields two identical transport
attempts and one retained recipient packet. Exact retry reads the installed
journal packet, never a caller-supplied replacement. Restoring only host state
leaves authority revision/currentness intact and refuses the stale fork.
Generic authority revision is kept distinct from any window-admission count.

[REFUTED: omitted continuity premises] Publishing before commit leaves an
orphan packet after the state rolls back. Restoring the authority database
itself re-enables a second committed packet at the same nonce; the still-current
recipient refuses that conflicting publication, but the authority history has
already forked. The local same-user files model separate roles and do not
constitute an independently protected finality resource. Recipient persistence
and deduplication are additional explicit assumptions; physical network
exactly-once delivery is not claimed.

[OPEN] This is an actual process-crash/concurrency fixture, not the kernel's
implementation-refinement proof, a power-loss/distributed durability theorem,
or a hidden-resident implementation. Full commands, source hashes, snapshots,
outputs and precise fixture/gate/serialization scope are in its owned README.
Trusted authority startup alone selects fault controls; normal client fault
fields are refused. Raw databases are hashed/compressed and gitignored.
No new private credentials, external messages or queries; Scry0/web0.
[DERIVED] The window bounds current state, not uncompacted replay history:
full canonical post-states retained per admission can cost T·W·ciphertext-size
payload without an additional sharing/compaction refinement.
