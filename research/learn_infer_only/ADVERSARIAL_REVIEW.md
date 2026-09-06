# Adversarial review of the resident research tranche

[DERIVED review scope, 2026-09-06] Independent review of committed first tranche
`64c7d3f`, followed by the bounded-tree/IPFE candidates and a second tranche on
the adaptive-context theorem and materialized durable wrapper. This file records
falsifiers and interpretation limits; it does not change `docs/VERDICTS.md`.
Review-owned code and command/output records are in `experiments/adversarial_review/`.
No companion source was edited and no patch was applied there. Metered queries: zero.

## 1. A real accepted-receipt / installed-state separation

[EXECUTED] `RestoreSeamWitness.lean` imports the proposed original modules and
constructs an exact prefix-disciplined singleton vote book. Its event remains the
valid public transition `1+2=3`. Its intent instead requests root write
`cell 0: pre-root 42 → post-root 99`, with charge one per lane against the original
zero budget. The original resident restore checker accepts it, an actual full-word
FS receipt for that same event exists, and `advance` installs root 99.
`accepted_receipt_with_unrelated_install` proves these facts together. Full durable
preflight refuses the identical intent as `.stalePreRoot`.

[EXECUTED] Reproduce with
`python3 research/learn_infer_only/experiments/adversarial_review/run_review.py lean`.
`lean_seam_02.json` records exit 0, input hashes, the exact command and empty
stdout/stderr; six `#guard_msgs` axiom pins pass. `lean_seam_01.json` retains the
failed first attempt (opaque-Prop decidability and initial axiom-inventory spelling),
which does not support any result. This is a kernel-checked falsifying instance,
not a cryptographic attack or a deployment execution trace.

[REFUTED: promoting the original restore adapter to a durable execution gate]
Receipt arithmetic and context equality do not force the arbitrary `Intent` effects
that `advance` installs. The accepted proof can be genuine while the installed
state differs. Source seam: original
`formal/Assurance/ResidentRestoreFinality.lean:70` (`check`) inspects finality,
log/pins/freshness/policy; `:79` (`advance`) passes the entire supplied intent to
`Snapshot.install`. Neither binds `rootWrites` to the context.

[SOURCE: source theorem read] This does **not** contradict
`ResidentRestoreFinality.authorized_step` at `:145`: its conclusion is
`Current ∧ receipt-context equality ∧ Forced context`, not equality of installed
cell bytes/root to the context. The original `formal/README.md` explicitly names
missing materialized roots and full preflight. The witness makes that existing
residual executable and prevents the narrower theorem from acquiring a stronger
prose interpretation.

[DERIVED repair criterion] The durable integration must derive intent effects
from the same validator-minted post that the arithmetic receipt certifies, enter
full preflight, and show installed bytes/root equal the certified next state.
Checking genesis, log, head and durable state independently also needs a reachable
state invariant or a representation that makes their consistency unavoidable.
An arbitrary `Authority` record can otherwise inhabit inconsistent combinations.
The active durable-integration lane has been sent this fixture and these criteria.

## 1a. The new materialized adapter closes that concrete seam

[SOURCE: source theorem read] The durable lane's
`formal/durable_integration/Assurance/ResidentDurableIntegration.lean` derives
`Plan.intent` from one `ValidatedPatch.apply`: singleton write, exact materialized
post bytes/root, fixed charge, derived slot nullifier and exact context packet.
`Plan.opens` checks independently selected genesis bytes, actual current canonical
pre-bytes, and a prior log derived from the durable journal. `DataSnapshot.coherent`
links actual stored canonical bytes to their roots. The old arbitrary `rootWrites`
substitution cannot be represented through this constructor.

[EXECUTED] The settled 31-pin version with SHA256
`e321bcc10af45c4fe29d7b29206ea2134a6284f6a6f559ac7bca9d84d75f97fa`
compiled independently, exit0, into the review directory. Record:
`lean_durable_02.json`. `_01.json` preserves the failed invocation with the wrong
Lean source root, not a mathematical failure. This check validates only that exact
source; the lane subsequently announced an additional gated-wrapper and explicit
arithmetic-composition revision, which this record does not cover.

[DERIVED remaining semantic limit] For a generic materializer, root equality is
not logical-state equality. This adapter's FS descriptor still computes addition
of `root.value`; it does not prove a resident's transition on hidden openings.
The closed Bool witness uses the actual encoded byte as root, so its0→1 arithmetic
is meaningful. A general encrypted-state version must bind opened logical inputs,
command, and logical post through its descriptor. Exact installation is an advance;
it must not be promoted to that unproved semantic transition. The durable lane is
adding its own constant-root collision falsifier after receiving this review.

## 2. What survives independent review of the original tranche

[SOURCE: source theorem read] `contextScheme` at
`formal/Assurance/ResidentReleaseContext.lean:56` carries context as an exact root
component. `check` at `:82` separately verifies exact expected context and `Linked`;
`Linked` at `:73` pins bounds, next/output equality, program/version, deterministic
randomness fields, and all 48 boundary values. `arithmetic_binding` at `:118`
then uses the actual Stage-0 theorem to force the addition. I found no weakening
that permits arbitrary context values while retaining these checks and the
satisfying descriptor premise in this reviewed source.

[SOURCE: source theorem read] `context_receipt_price` at `:143` instantiates the
existing theorem, which is fixed-context classical-ROM soundness. The source
`/Users/ember/dev/minidregg/Compiler/CommittedTerminalFiatShamir.lean:621`,
`gateProof_fs_sound_reading`, makes the false-word/descriptor event explicit;
`:725`, `stage0Receipt_price`, carries `(t+14)·4160/2013265921^6` and explicitly
reads the full 4,131-wire word. `fsCheck_ok_fiatShamir` at `:954` supplies the
accepted-checker reflection. No private witness is extracted by this public-word
instance. `formal/README.md` correctly declines an adaptive multi-context, concrete
hash, QROM, or release-hiding price.

[DERIVED review finding] A fixed-context price cannot be advertised as the
lifetime error of an adaptive resident that changes parent, command, recipient or
randomness context. Either reduce a clearly specified multi-context adversary to
a single common protocol/ROM game or prove the relevant sequential composition.
A union bound requires per-session conditional hypotheses that remain true after
the prior transcript; multiplying a standalone number by a session count is not
itself that argument. The previous tranche states this limitation rather than
silently applying the price.

[SOURCE: source theorem read] The original finality claims also stay within their
scope. `/Users/ember/dev/minidregg/Kernel/FinalityGate.lean:86` verifies an exact
candidate's recorded votes; it contains no online head/freshness check.
`checked_transaction_unique_at_slot` at `:159` requires `PrefixDiscipline`.
`/Users/ember/dev/minidregg/Kernel/ReplicatedSettlementFinality.lean:127` quantifies
prefix compatibility over every node's recorded votes, including across epochs.
This is a strong trusted vote-discipline assumption, not Byzantine robustness
inferred from quorum cardinality alone.

[EXECUTED] The original Python writer and restore audits reran unchanged and
passed. Commands, outputs, timing and source hashes are in `writer_recovery_01.json`
and `restore_release_01.json` in the review directory. Those runs reproduce
64 histories / 288 recovered values, the two continuing public additions, stale
restore refusal, and explicit authority-rollback/race/compromised-vote controls.
The existing no-op-independent Lean replay refusal remains meaningful because
its contradiction uses exact prefix length, not a requirement that values change.

[SOURCE: primary construction read] Local GKS23 ePrint `2022/1599.pdf`, printed
pp.55–58 (PDF pages57–60), was independently extracted; the rendered page with
Figures8–9 was inspected. `Enc.ST=(FPFE.msk,FE.ct)`, the stored `FPFE.sk_H_i`, and
H's evaluation of an attacker-supplied valid inner setup exactly match the symbolic
redirect path. Source hash and extraction/render commands are in
`source_extract.json`. The game/reduction was not independently reread in this
review; the earlier note's game analysis remains a sourced prior result.

[DERIVED scope] Missing-prefix/wrong-setup refusals in the symbolic model enforce
the prerequisites of its one chosen correctness path. They are not robustness
claims about malformed concrete SFE ciphertexts or proof of secrecy when that path
fails. The earlier note additionally explains why direct access to the concrete
inner setup can remove the prefix requirement. No finding here upgrades the
negative controls into a mitigation or refutes the paper's theorem.

## 3. Review of bounded behavioral compilation

[SOURCE: current source/read] `PRIVATE_CONSTRUCTION.md` and
`experiments/private_construction/bounded_tree.py` explicitly scope the candidate
to public commands, a complete finite response tree, independent history tokens,
full fork access and honest setup erasure. It discards the original raw-state
representation. Its equality-of-artifacts argument concerns states with equal
complete depth-H responses and does not depend on AEAD secrecy. This is a valid
bounded observational-quotient direction from the handoff, not a compact private
resident with indefinite learning.

[DERIVED strengthened ingress falsifier] The prototype token's public `node`
number reveals the entire command path directly. With branching B,
`lastCommand=(node−1) mod B` and `parent=(node−1) div B`; repeat to recover the
whole history. This attack uses zero AEAD decryptions, no parent key, and no
selected-child token comparison. The source's comparison attack is also valid,
but needs more privilege than this metadata-only path. The lane has been notified.
Public commands were already an explicit assumption, so this sharpens its stated
private-ingress obstruction rather than breaking the claimed construction.

[EXECUTED] The independent finite-word checker uses a separately written reference
transition and enumerates all depth-five command words. There are 62 behavioral
classes; zero's class is exactly `{0,…,7}`. It checked 15,066 full encrypted trace
paths (243 words per class) and exact coupled artifact equality within each class.
Public token metadata recovers all 243 depth-five histories with zero decryptions.
`tree_independent_review_02.json` retains the command, source hash, a verified
unchanged-source flag and results. The first run is retained in `_01.json`;
the second added explicit start-time/source-stability instrumentation and the
horizon partition rather than silently overwriting it.

[EXECUTED] At horizon eight every initial byte is recoverable using the permitted
forkable interface: restore root, apply k doublings and infer, for k=0,…,7; these
are the original bits from highest to lowest. The test recovered all 256 bytes
through actual encrypted artifacts: eight inference observations and 36 primitive
transition queries per byte. Independent partition refinement gives class counts
for horizons0…8 of `1,2,6,14,30,62,122,208,256`; both the full run and
`tree_horizon_partition.json` retain this result.

[REFUTED: extending this toy's nontrivial hidden-state challenge to horizon eight]
The depth-five hidden-state pairs disappear entirely at depth eight for this
command alphabet. This is an interface consequence, with no cipher break: a
longer-horizon compile can preserve more behavior while eliminating every distinct
admissible state pair. Any future horizon increase must recheck nonvacuity.

## 3a. Compact additive IPFE continuation

[SOURCE: prototype and ledger read] The private-construction lane's
`experiments/private_construction/additive_ipfe.py` instantiates a group-based
inner-product FE algebra and retains the raw vector in encrypted form. Its
selective-security/DDH source claim is from that lane's construction/theorem read;
this review independently checks the algebra, not the security reduction or a
security-strength calibration of its 2,048-bit MODP parameter choice.

[EXECUTED] A separate small check confirms coordinatewise ciphertext multiplication
equals direct encryption of the sum with summed coins, and its released group
element equals the direct group encoding of the intended projection. The pair
`(1,4,6)` / `(2,3,11)` has the same `(1,1,0)` projection. Command, source hash,
unchanged-source flag and results: `ipfe_independent_review.json`; source:
`ipfe_independent_review.py`. No counterexample to that equal-projection pair is
claimed. This is a useful compact algebraic closure control with a clearly weaker
functionality than a nonlinear private learner.

[EXECUTED strengthened leakage boundary] Inputs whose projection is65 and66 both
fail the prototype's declared integer decoder range `[-64,64]`. Yet the exposed
function-key holder computes distinct group elements `g^65` and `g^66` and can
identify each by comparison with the corresponding public guess. The same
independent run executes this witness. The private lane has been notified.

[REFUTED: treating bounded discrete-log decoding failure as a gate that hides
out-of-range projections] The actual exposed capability is the projected group
encoding, including scalar-span key derivations. The decoder interval is a
functionality/cost contract, not a cryptographic restriction on that capability.
This does not refute equal-projection selective challenge pairs, which agree on
the complete group element too. It does require the ideal leakage to name the
actual group output if out-of-range states are admitted.

[SOURCE: construction/game/proof-sketch text read] I independently read the lane's
saved primary text `experiments/private_construction/sources/2015-017.txt`,
§2.3/Fig.2 and Construction3.1/Theorem3.2, printed pp.6–8. The selective pair is
chosen before the public key; every issued function key must give equal challenge
outputs. The source proof sketch and algebra support the stated single-initial-
challenge reduction. This is not a proof audit of a concrete group implementation.

[DERIVED reduction scope] For fixed issued readouts and public known additions,
the FE reduction can form every new input ciphertext and multiply it
into the supplied initial challenge. It can run the exposed projection keys,
make all restored branches and expose all these snapshots. Thus a polynomially
bounded continuation is efficient postprocessing of that one FE challenge; no
independent per-step cryptographic hybrid is needed for this narrow claim. The
claim does not cover new unknown challenge-dependent observation histories,
adaptive choice of the initial challenge after the public key, surviving master
or initial encryption coins, or unbounded computation. Efficient integer decoding
also needs its own bounded-output contract.

[DERIVED lifetime exposure] With one master public key, the effective allowed key
set is the span of **all** function-key scalars ever exposed. Revocation of an API
cannot remove a copied scalar. A later key outside the prior span shrinks the
common kernel; full-rank scalars determine the master vector by linear algebra.
All challenge restrictions must use that accumulated set, not just the presently
advertised readout. Exact plaintext recovery additionally uses the declared
bounded discrete-log decoding; distinguishing known candidates only needs group
comparisons. The existing note correctly distinguishes its classical selective
claim from simulation, malicious setup and post-quantum security.

[DERIVED semantic limit] Addition preserves the hidden common-kernel differences
precisely because those differences never influence the allowed linear outputs.
The lane's nonlinear-square falsifier demonstrates why allowing a broader update
requires revisiting that invariant. Raw-state retention and compact continuation
are improvements over the finite tree; useful private adaptation and controlled
release are still distinct obligations.

## 3b. Policy evolution statement review

[SOURCE: source theorem read] The coordinator's
`formal/recovery_policy/Theory/PrivatePolicyEvolution.lean` reuses the actual
`PrivateTrace` machine. `Safe` requires output equality and relation preservation
for ordinary updates and admitted migrations; public admission and destination
avoid a hidden-state-dependent public version leak. `versioned_trace_eq` is the
appropriate deterministic all-horizon consequence. The swapping representation
witness preserves a hidden bit; its admitted no-swap sibling leaks it. This review
inspected statements/proofs but did not independently compile this module.

[DERIVED scope correction to preserve] `JointlyEquivalent` and
`all_policies_determine_state` apply several policies to the same state/carrier.
They show cumulative disclosure for actually jointly usable retained capabilities,
such as IPFE keys under one master public key. They do not alone prove an old
key can decrypt a rekeyed current ciphertext, or that an output about past state
s0 identifies later state s1 after private migration. Conversely, the first
`Evolution.machine` only exposes the active-version output: a claim against old
evaluator artifacts retained across migration must add their actual capabilities
to that ideal or supply a realization theorem that makes them unusable. The
coordinator has been sent this distinction; no contradiction in the stated ideal
trace theorem was found.

## 4. High-impact remaining tasks from the handoff

[DERIVED priorities; active-lane boundary] The ongoing private-construction,
durable-integration, randomized-composition, HE-closure/cost, BFV-lift and adaptation
lanes already cover the largest first gaps. The additional work below is not a
request to duplicate them.

- [EXECUTED/OPEN] The single-final-output adaptive-context theorem is reviewed
  in §5; the query-complete collected-output selector is reviewed in §7.
  Runtime schedules must still realize and charge the common oracle log.
- [OPEN] Connect authenticated issuer provenance, intended policy/version,
  recipient keys and command authorization through one typed relation. Numeric
  placeholders such as authorization19/recipient23 prove parameter binding only.
  Include retained setup coins and unauthorized policy replacement as falsifiers.
- [OPEN] Audit private witness production/extraction separately from public
  Stage-0 arithmetic. Private observations close the public-replay extractor route;
  state exactly which setup, incoming-witness or extraction premise replaces it.
- [OPEN] Build a complete implementation leakage/taint contract from private
  adaptation into subsequent public-backbone operations: lengths, memory addresses,
  expert choices, timing, failure behavior and debug caches. The state size alone
  does not give the private compute bill or observational equivalence.
- [OPEN] Assemble a whole-route post-quantum dependency/error ledger only after a
  concrete privacy-changing candidate exists: HE parameters, release primitive,
  proof/QROM, authentication, transport and recovery. The current FS theorem is
  classical ROM; no numeric PQ label should be borrowed from one HE component.
- [OPEN] Price the cost of the ideal interface as well as the real implementation.
  Forkable finite compilation may reveal all future responses immediately and
  destroy a small-query claim despite matching an unrestricted ideal exactly.
  Track state recovery, imitation, output extraction and unauthorized releases
  as separate attack objectives.

[DERIVED status] The strongest original claims reviewed so far survive in their
stated narrow scope. One checked falsifier blocks an unearned stronger durable
interpretation; the new bounded-tree candidate is being reviewed as a quotient
construction with explicit loss of future/private-ingress functionality. This
review is resumable from its saved scripts and records. The first review tranche
is complete; later revisions must be checked against their own hashes. No changes
are proposed to `docs/VERDICTS.md` by this file at this stage.

## 5. Second tranche: one common adaptive-context receipt game

[EXECUTED] Independently compiled
`formal/randomness_composition/Assurance/ResidentAdaptiveContext.lean`, SHA256
`9eb3318ca21240162355a7e166e258b085aaa038b66f466c2b8f90df777fd90e`.
`experiments/adversarial_review/lean_adaptive_01.json` records exit 0, unchanged
input hashes and all 13 exact axiom pins passing. Command:
`python3 research/learn_infer_only/experiments/adversarial_review/run_review.py adaptive`.
Only the review overlay receives build outputs; companion trees remain read-only.

[SOURCE: statement and proof read] `adaptiveReduction` at `:36` selects both the
commitment relation and verifier from the context inside the statement's root.
`localRbr` at `:45` is the actual inherited `gateRbr`; `adaptiveKState` at `:51`
uses it at that same root context. Within a statement that context is fixed;
across the adversary's oracle queries it may change. The challenge/message
alphabets and uniform per-round error are shared. `adaptiveRbr` at `:63` therefore
supplies the common reduction required by `adaptive_context_receipt_sound` at
`:76`; this is more than a union bound over unrelated fixed-context instances.

[SOURCE: wire and wrapper transport read] `query_bytes_match_live` at `:101` and
`concrete_oracle_match_live` at `:115` are definitional equalities because the live
address already encodes the full context in the root. Intermediate queries may
have arbitrary roots, words and prefixes; they are not assumed to pass the
external authorization wrapper. `wrapper_accepts_global_fiatshamir` at `:126`
first obtains exact expected-context equality, then uses the existing live-checker
reflection. `wrong_arithmetic_is_global_bad` at `:140` correctly maps an accepted
wrong arithmetic result to a false relation. I found no counterexample to these
statements or a mismatch between the root selected by the realizer and verifier.

[DERIVED exact scope] `adaptive_sound_reading` at `:150` prices **one final false
receipt** after a global total of t queries across contexts, in the inherited
uniform-Ext6 classical random-oracle game. `adaptive_price_numeric` at `:180`
retains `(t+14)·4160/2013265921^6`. Its `SrProver` is an arbitrary deterministic
adaptive strategy; independent randomized strategies can be averaged over their
coins. This does not price multiple released receipts or grant free correlated
history. If an application supplies prior honest-prover, verifier, or release
service transcripts dependent on the same oracle, the reduction must simulate
them and charge their oracle work to global t (or explicitly model that extra
resource). Earlier failed receipt checks can require up to 14 such queries each.
Independent public advice is different from preloaded oracle-dependent transcripts.
This budget boundary was sent to the composition lane and coordinator.

### 5a. Byte transport does not make field sampling uniform

[SOURCE: concrete conversion read] The inherited
`/Users/ember/dev/minidregg/Compiler/CommittedTerminalFiatShamir.lean:839`
(`digestToExt6L`) takes six base-p digits with p=2013265921. The source
`/Users/ember/dev/minidregg/Compiler/Sp800185Cshake256Core.lean:149`
(`outputBytes`) selects 32 bytes. Even replacing cSHAKE by an ideal uniform
256-bit digest would induce reduction modulo M=p^6, not an exactly uniform field
element. The adaptive module's byte/function equalities do not assert otherwise.

[EXECUTED] `challenge_sampler_review.py` computes the exact finite distribution
with rational arithmetic and checks its formulas against a small fully enumerated
analogue. `challenge_sampler_review.json` retains the command, source hashes,
integer counts, fractions and 1,024 small event checks. For N=2^256,
`N=aM+r` has `a=1738889707064933088846` and
`r=226743016697890581566590486987070183394949637919605170`.
The maximum atom is `(a+1)/N`; the total variation distance from uniform is
`r(M-r)/(MN)`, approximately `2^-78.7617`. The maximal density ratio is
`rho=M·ceil(N/M)/N`, with `rho-1` approximately `2^-70.5636`.

[DERIVED, not a new Lean theorem] Every fixed event satisfies
`Pr_D[E] ≤ rho·Pr_uniform[E]`. Independent n-draw product distributions satisfy
the corresponding `rho^n` domination, so applying the existing finite-game event
to hypothetical independent uniform-byte oracle samples yields the conservative
bound `rho^(t+14)·(t+14)·4160/p^6`. This avoids treating the additive total variation
distance as a purported security floor. A sharper route may transport each fresh
challenge's bounded bad-event mass before the Fiat–Shamir argument; that has not
been proved here. Neither route establishes security of concrete cSHAKE or QROM
soundness. The reviewed theorem remains explicitly uniform-field ROM soundness.

## 6. Second tranche: a real packet-composition bug, then its repair

[EXECUTED] The next durable revision, SHA256
`b174ddb157caa8ccc76443a2be7a9b49ceb899a8ceecd6b536bcfcb79997197e`,
compiled independently in `lean_durable_03.json` but contained a distinct helper
seam. `releasedPacket` accepted a caller-supplied Plan and an unindexed
`GatedOutcome`; on `.accepted` it returned that Plan's packet. The actual result
of a genuine gated execution could therefore be supplied with another Plan.

[REFUTED: the unsafe helper preserves authorized recipient through arbitrary
well-typed composition] `ReleasePacketSeamWitness.lean` constructs the actual
closed receipt, with `descriptorHolds` for that same receipt word, and executes
the genuinely authorized Plan for recipient 23. Passing its successful outcome
to the old helper with a Plan naming recipient 24 returns the second packet.
`accepted_result_can_be_relabelled` proves acceptance, descriptor satisfaction,
the helper result and the unauthorized recipient together. The same-Plan
`consume_before_packet` theorem remained true; its call-site equality did not
prevent the mismatched helper call. This was a new API composition defect, not a
counterexample to the inherited proof system or executor.

[EXECUTED reproducible old source] Three exact axiom pins pass in
`lean_release_packet_02.json`; `_01.json` retains the initial wrong expected axiom
list. The entire unsafe module is preserved byte-for-byte under
`experiments/adversarial_review/snapshots/b174ddb157caa8cc/Assurance/`.
Reproduce against the frozen source, never the repaired module, with
`python3 research/learn_infer_only/experiments/adversarial_review/run_review.py durable_unsafe release_packet`.
The runner isolates this dependency in `build_unsafe/`, separate from current
source checks. A clean frozen-source build and fixture pass are retained in
`lean_durable_unsafe_01.json` and `lean_release_packet_03.json`.
The old hash and falsifier remain evidence after repair.

[SOURCE: repaired API and theorem read] The repaired main module, SHA256
`80239c7fbc060c6f0c60a4a085c78b078987b46ffbf7b17017f3f92af57c022a`,
has `releasedPacket` at `:326` accept only the outcome. Successful fresh packets
are derived from the installed snapshot's journal head; replay packets come from
the recorded intent. `installed_packet_cannot_be_relabelled` at `:336` proves the
old substitution impossible for an actual installed outcome. `gatedExecute` at
`:312` retains journal-first exact retry; fresh attempts pass authorization before
full data preflight. `authorized_materialized_arithmetic` at `:419` explicitly
keeps `descriptorHolds` on the same accepted receipt word, then composes Forced
arithmetic with exact installation. It does not turn arbitrary receipt acceptance
into deterministic arithmetic soundness outside the ROM game.

[EXECUTED] The repaired main module's 39 pins passed independently, exit 0 and
source unchanged, in `lean_durable_04.json`. The final collision module's six pins
passed in `lean_collision_01.json`, SHA256
`b410206075a03338ef6d569c777c2d2a2420f3ddc8f3280cfcf6d062685a028c`.
Command:
`python3 research/learn_infer_only/experiments/adversarial_review/run_review.py durable collision`.
This checks the actual repaired sources, not their earlier green versions.

[SOURCE/EXECUTED scoped semantic falsifier] In
`formal/durable_integration/Assurance/ResidentDurableCollision.lean:90`,
`root_arithmetic_not_logical_step` combines an actual accepted receipt, its own
satisfying descriptor, finality, exact canonical openings and full preflight.
The lawful Bool codec is retained but the root function is deliberately constant.
A validator-minted false→true update then has the true arithmetic statement
`0+0=0`: parent and next roots agree while canonical bytes and the logical Bool
differ. `exact_install_survives` at `:117` proves exact installation still holds.
This rules out inferring logical Step semantics from arithmetic on arbitrary roots.
It is not a collision attack on a cryptographic commitment or an implemented hash.

[DERIVED final scope] The structural durable model now closes both witnessed
effect and packet seams. Its explicit state/journal transition is still a model:
the physical persistence, concurrency and output boundary must realize the
existing implementation-refinement contract. A public Lean outcome constructor
is not itself an unforgeable runtime capability. The abstract materializer's
logical Step/opening relation and private release remain separate obligations.
These checks cover the exact hashes named above. The subsequently announced
multi-output source is reviewed in §7; arithmetic-emission work was not covered.
No shared ledgers, companion sources or verdicts were edited.

## 7. Bounded follow-up: query-complete collected outputs

[EXECUTED] Independently compiled
`formal/randomness_composition/Assurance/ResidentMultiReceiptSchedule.lean`, SHA256
`fff98c92e7d12eba22ab590d777d826300e8afcf31bee37392cf58c2626f84f3`,
against the independently built adaptive module. `lean_multi_receipt_01.json`
records exit 0, unchanged input hashes and all 18 exact axiom pins passing.
Command:
`python3 research/learn_infer_only/experiments/adversarial_review/run_review.py multi_receipt`.

[SOURCE: statement and proof read] `AllOutputQueriesLogged` at `:46` requires
every verifier-prefix query of every final output to occur in the one query log,
for all sampled response histories. `final_challenge_is_logged` at `:56` then
removes the fallback final coins from each output's verification. `rebuild_actual_log`
at `:132` shows the entire query log is recoverable from the strategy and its
actual response list. The selector at `:169`–`:183` finds a false accepting
full-word output using that reconstructed log; it changes only `SrProver.out`.
It does not consult a new oracle, change `P.move`, or obtain an encrypted witness.

[DERIVED reviewed conclusion] `all_logged_outputs_bound` at `:202` therefore
earns the same `(t+14)·gatePrice` bound on any false accepting output in the finite
collection, without a separate M multiplier. All prover and verifier oracle work
is already included in t. `all_logged_bad_arithmetic_bound` at `:211` transfers
the actual wrapper's wrong-arithmetic event into that event. This is the inherited
query-bounded mathematical strategy model, not a computation-time or private
extraction theorem. Noncomputable selection is admissible in that theorem's
strategy quantifier; the full-word relation is also publicly available here.
The uniform-field/classical-ROM and concrete-sampler limits of §5 remain.

[DERIVED scope to preserve] The formal premise asserts completeness in the final
log. It contains no publication timestamps or proof that each prefix was queried
before its particular output was sent. That suffices for the collected-output
probability bound, even when later queries are present; a real online release
service must separately realize the intended order and charge its actual oracle
calls. Unknown or unqueried verifier responses cannot be supplied as free history.

[SOURCE: premise inhabitation read] `planned_verifier_logs_all` at `:265` gives
an explicit M·14-query schedule for fixed output receipts. The empty-log tooth
at `:277` refuses query completeness. `two_real_receipts_premise_inhabited` at
`:283` supplies receipts with distinct parents, acceptance under the zero oracle,
and completeness for all sampled logs. Its statement does not directly assert
that the same receipts accept under every sampled `loggedOracle`; they need not.
An all-zero response sample would connect the two positive facts in one actual
logged experiment. This distinction was sent to the author; it does not undermine
the theorem or make its query-completeness premise impossible to inhabit.

[DERIVED review status] The second tranche and this bounded follow-up are complete.
The new reproducible defect was the old release helper's Plan substitution, now
repaired and independently checked. No counterexample to the reviewed common-log
soundness statements was found. Future revisions require their own source hashes.

### 7a. The final positive witness now uses its actual shared log

[EXECUTED] The strengthened multi-receipt source, SHA256
`0dcbf2e07534bf430d0f17b969f9174fdd2bda533f537bccddb9f7cb6265ab82`,
passed independently with 20 exact axiom pins in `lean_multi_receipt_02.json`.
The bound and selector are unchanged. Its header now states final-log completeness
and separates runtime publication order.

[SOURCE: new proof read] `zero_sampled_trace_values` at `:284` proves by actual
`runFrom` induction that both fresh-query and cached-query responses are zero
when all sampled coins are zero. `zero_sampled_oracle` at `:315` includes both
logged and fallback addresses. The strengthened witness at `:326` now conjoins
acceptance under that actual sampled shared-log oracle with the two distinct
parents and universal query completeness. This closes the positive-witness
composition gap noted in §7. It asserts existence of a valid sample, not that
these fixed receipts accept under every random transcript. No new contradiction
was found.

## 8. Third tranche: exact BFV source arithmetic and its input domain

[EXECUTED] Independently compiled the original 27-pin dependency and the final
33-pin `formal/bfv_lift_refinement/engine_refinement/Compiler/FheRnsScaleDecomposition.lean`,
SHA256 `486e63dc09d79c10858f9b1e37cbf6b7a5b63841c23e8cbb914cc0e2b8b49167`.
Records `lean_bfv_reference_01.json` and `lean_bfv_engine_01.json` both have exit 0
and unchanged input hashes. The command is
`python3 research/learn_infer_only/experiments/adversarial_review/run_review.py bfv_reference bfv_engine`.
Both were built in the review overlay, without writing into either companion.

[SOURCE: theorem and source formulas read] `garnerScaleDecomposition` gives the
exact integer identity for any chosen Garner lift index. It does not assume
approximate rounding is exact. The deployed output is forced by the deterministic
formula

```text
v = nearest(sum_i r_i * thetaG_i / 2^126)
w = nearest(sum_i r_i * thetaF_i / 2^127)
Y = sum_i r_i * omega_i - v * gamma + w
```

[DERIVED] `deployed_output_exact` proves that formula. The separate
`deployed_source_arithmetic_envelope` diagnoses its distance from exact nearest
on the **source-selected lift**. Its interval is not a choice the prover may make.
In particular, the reference does not silently switch to the first tranche's
unsigned lift or to a strictly centered representative. `deployed_constructor_constants`
checks the numerical basis product, Garner CRT selectors, projections and fixed
constants. The proof concerns this one six-prime scalar parameter instance; it
does not quantify over arbitrary BFV parameters or the complete multiply pipeline.

[SOURCE: literal word operations read] The pinned Rust
`/Users/ember/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/fhe-math-0.1.1/src/rns/scaler.rs:250`
accumulates the Garner products modulo 2^256, shifts by s−1, casts to u128 and
uses `div_ceil(2)`. At `:269`–`:304` it accumulates signed correction products,
tests whether the upper bits above position 190 are nonzero, complements the
negative branch, shifts by 126, casts, and rounds. The Lean `wordV` and
`wordCorrection` definitions retain those wraps, shifts and truncations, rather
than replacing them without premises by integer division.

[DERIVED domain assessment] `wordCorrection_correct` needs
`-2^191 < T < 2^191`; the corresponding Garner lemmas need a nonnegative bounded
accumulator. The instantiated range proofs discharge these conditions from
`0 ≤ r_i < deployedBase_i` for **every** one of the six residues. The resulting
truncated values also fit well below the negative branch's u128 `+1` overflow
boundary. The source API itself accepts u64 arrays and only performs structural
debug assertions here; the theorem's canonical-range premise is not an API-level
validation theorem. A complete engine refinement must show that its actual input
path supplies these canonical limbs or validate them explicitly. No encryption
origin, noise bound, or freshness premise is needed for the scalar arithmetic
theorem, and none follows from it.

[EXECUTED independent arithmetic check] `bfv_scalar_review.py` recomputes the
numeric Garner, omega, gamma and theta tables from the source formulas, derives
shift 126, follows the word operations, and checks 1,065 canonical vectors: all
64 endpoint combinations, 1,000 seeded independent residue vectors and the
captured discrepancy row. All checks passed. The one discrepancy in this finite
set is the captured `172481` versus exact-nearest `172480` row. This is not a
failure-frequency estimate. `bfv_scalar_review.json` retains its command, seed
in the script, source hashes, unchanged-source check and results; it also verifies
that every source in the lane's retained engine manifest still matches its hash.

[EXECUTED retained engine evidence] Running the existing full-coefficient checker
against the preserved gzip succeeds in `bfv_retained_01.json`: 114,944 extension
coefficients, 86,208 full integer convolution coefficients and 86,208 output
coefficients agree with its literal source model across 11 recorded cases.
This independently reruns the checker over retained Rust outputs; it is not a
new encrypted-engine run. The five fresh encrypted examples and six constructed
boundary pairs remain distinct. Three constructed output coefficients disagree
with strict nearest by +1; one extension input chooses a lift shifted by −Q.
None of those observations establishes a fresh-ciphertext failure probability,
decryption error or cryptographic break.

[REFUTED: replacing the deterministic source certificate with its one-unit envelope]
The review-owned `BFVEnvelopeSeamWitness.lean` uses the actual canonical captured
residue vector and proves that `172480` is a canonical target residue admitted by
the nearest-or-nearest+1 envelope, while the deterministic source residue is
`172481`. Thus even the same genuine input row admits a false engine result under
that weakened relation. Its exact axiom pin passes in `lean_bfv_envelope_01.json`.
Reproduce after building the dependency with
`python3 research/learn_infer_only/experiments/adversarial_review/run_review.py bfv_envelope`.
The BFV certificate lane received this precise negative target and will bind the
two rounded quotients separately.

[DERIVED remaining source correspondence] The mathematical integer Y is a useful
representative of the target residues. Rust does not materialize that potentially
large integer: it projects omega/gamma per target modulus and performs Shoup and
lazy modular arithmetic. Relating those operations to `Y mod q_j`, actual arrays
to the Lean vector, and NTT/convolution to the scalar input still requires the
named implementation refinement. The reviewed module does not conceal those
premises. A public full-word certificate also does not provide private release
or remove a retained master-read credential.

## 9. Reprioritized review: the EMA logical-state and durable bridge

[EXECUTED] Independently compiled all four final EMA modules into the review
overlay, using the already checked `ResidentDurableIntegration` dependency:

| Module under `formal/durable_integration/` | SHA256 | Review record |
|---|---|---|
| `Compiler/ResidentEmaCertificate.lean` | `f6b9c07240bc4f5341a8412b7bc00a5c8c6e19e17743d86c3cecc8b3ea72588d` | `lean_ema_certificate_01.json` |
| `Assurance/ResidentEmaCell.lean` | `68cdb084b839364328bc0717c5b6fa763a8342efbfc4244c02181603af4a9437` | `lean_ema_cell_01.json` |
| `Assurance/ResidentEmaRelease.lean` | `470a6b5daf54cbd373799fa0b075137d06f5a115395d07ecbabfac130efbc8ee` | `lean_ema_release_01.json` |
| `Assurance/ResidentEmaWitness.lean` | `e412cad31eba9eac302a597239fcaee14987b79db6b134c0de884e2ca74f3eeb` | `lean_ema_witness_01.json` |

[EXECUTED] All 48 exact axiom pins pass; all four records report exit 0 and
unchanged sources. Reproduce with
`python3 research/learn_infer_only/experiments/adversarial_review/run_review.py ema_certificate ema_cell ema_release ema_witness`.
This review does not claim to have independently rerun the author's entire
umbrella/import-boundary patch validation.

[SOURCE: descriptor semantics read] `ResidentEmaCertificate.system` at `:32`
uses existing range gadgets for three biased bytes and a three-bit remainder,
plus the relation `7*C+U=8*N+r`. The range proofs bound both integer sides below
BabyBear before lifting the field equation. Since the bias is 128 on all three
bytes, this is exactly `N-128=floor((7*(C-128)+(U-128))/8)`, including negative
values and −128. `descriptor_semantic` at `:79` proves that implication for all
satisfying descriptor words. No truncation-toward-zero rule or unproved no-wrap
assumption replaces the declared floor operation.

[SOURCE: canonical state boundary read] The lawful cell codec maps absence to
`[]` and a present byte b to `[b]`. `canonical_opens` and `signed_opening` use its
decode/encode law to recover the actual logical state from exact bytes, without
hash injectivity. Although the auxiliary `signedValue` defaults absence to the
same integer as byte zero, `OpenedPlan` requires singleton pre/post openings and
therefore excludes absence from this semantic bridge. `biased_representation_exact`
explicitly connects the public biased-byte convention to two's-complement values;
it does not prove encrypted-wire implementation refinement.

[SOURCE: same-receipt and durable composition read] `ResidentEmaRelease.Linked`
at `:40` binds the three descriptor scalar values to that OpenedPlan's exact
pre-byte, public command and post-byte, alongside program/version, deterministic
randomness fields and acknowledgement zero. `check` enters the actual new FS
checker. `checked_logical_step` at `:77` uses a satisfying descriptor on **the same
accepted receipt word** to prove `LogicalStep`. `ema_durable_binding` at `:178`
then derives actual current canonical bytes, the executor's exact installed bytes,
next-root equality, consumed token and the repaired journal-derived packet from
one authorized Plan. Freshness, full preflight and descriptor satisfaction remain
explicit. Journal-first retry recovers the old exact packet; it is not fresh
authorization under a newly chosen policy.

[SOURCE: positive and negative poles read] The witness obtains a real FS receipt
whose retained word is the descriptor-satisfying word used by its positive proof.
It demonstrates a changed logical state under both the public root and a constant
root. The constant-root wrong post 144 still materializes and passes exact openings
and full preflight; its boundary-linked candidate exists, but every word linked
to that post fails the EMA descriptor. Thus this new opening-aware descriptor
closes the old constant-root **logical-Step** counterexample for its stated public
cell. It does not claim that root labels themselves bind the logical value.

[EXECUTED independent census and inhabitation] The review-owned
`EmaDescriptorReview.lean` reads the emitted descriptor itself: 4 public variables,
31 variables, 153 wires, 61 addition gates, 61 multiplication gates and 32 zero
checks. It also constructs and checks **all 65,536** biased-byte input pairs with
the actual `fillAux`/`descriptorHoldsCheck` path; all accept their floor-EMA output.
The wrong post 144 for inputs 128/248 is refused. These are compiled finite checks,
not additional kernel theorems. `lean_ema_census_01.json` retains exit 0, counts,
command and unchanged hashes. Reproduce with runner target `ema_census`.

[DERIVED independently recomputed price] The emitted descriptor has
`122+32=154` residuals. The inherited full-word gate price is the gamma term
`(154-1)/p^6` plus eight sumcheck terms `1/p^6`, hence **161/p^6** with
p=2013265921. The new FS instance has nine total rounds, so its fixed-context
price is `(t+9)·161/p^6`. A direct exact false-word/event reading needs the usual
relaxation threshold `δ<1/153`. The previous adaptive theorem for a 4,131-word
Stage-0 descriptor does not automatically provide adaptive-context or lifetime
composition for this 153-word EMA descriptor. The lane's note now states that
boundary explicitly.

[EXECUTED bad-oracle control] `EmaZeroOracleReview.lean` runs the actual new
`fsProve` and `check` on the wrong biased post 144 under a deliberately constant-zero
oracle. The receipt checker returns true while `descriptorHoldsCheck` on its same
word returns false. Record: `lean_ema_zero_oracle_01.json`; runner target
`ema_zero_oracle`. This is a concrete bad-oracle sample within the arithmetic
model, not a concrete hash attack or a contradiction of probabilistic ROM
soundness. It blocks the unearned deterministic implication from receipt acceptance
alone to logical Step and confirms why the keystone retains its descriptor premise.

[DERIVED scope] The scalar openings and entire receipt word are public. A packet's
output field of zero does not make this realization learn-with-only-acknowledgement
private. Genesis/authentication identities remain independently selected numeric
parameters; runtime persistence and publication ordering still need refinement.
Within those stated limits, I found no new substitution seam in the reviewed
descriptor→logical state→installed bytes/packet chain.

## 10. Final HE estimator framing and saved-result audit

[SOURCE: source/configuration read] The estimator snapshot is pinned at
`53da5982597709ba0fdf94ea37a84d822310fd84`. The executed wrapper supplies exact
Q83/Q109, n=4096, `Xs=Xe=ND.CenteredBinomial(20)`, and available sample counts
4096 or infinity. Independent source reads of `fhe-util`'s popcount sampler and
the secret/public-key constructors support eta 20 at variance 10. One public key
supplies one structured RLWE sample; its 4,096 coefficient equations have a
negacyclic matrix, so the generic-LWE calculation is a heuristic proxy, not a
reduction establishing ring-LWE hardness. Publicly manufactured ciphertexts do
not automatically add independent raw public-key samples with that same error
distribution. The retained test reader's full secret key is outside this attack
instance and still directly reads the state.

[EXECUTED source-model qualification] `he_source_review.py` independently checks
the pinned source alias and MATZOV call structure using Python's AST parser.
`LWE.dual_hybrid` aliases `lwe_dual.matzov`; its cost function defaults lattice m
to n, and its optimizer never supplies another m. Available `params.m` affects a
beta cap there. Consequently equal 4096/infinity outputs in that path do not
demonstrate optimization over sample count. This correction was incorporated into
the final lane note. The same review computes the exact ideal-bit CBD20 variance
as 10. As a small demonstration of the helper's approximation, its one-dimensional
99%-support formula returns 41 while the exact PMF needs only 17 most likely
values. This is not a corrected attack estimate. The estimator already flags
Gaussian-like behavior and an imprecise binomial support helper; several attack
subroutines use moments/Gaussian-shaped formulas rather than the exact PMF.

[EXECUTED final aggregation review] `he_results_review.py` independently parses
the saved result files and validates the final summary against their raw tuples,
cost fields, distinct attack coverage and selected source files. It verifies all
**144** artifact-manifest entries and eight pinned estimator source hashes.
All **72** primary lattice calls completed; all **16** displayed minimum candidates
match their saved fresh-process rechecks exactly. Outputs and input hashes are
in `he_results_review.json` and `he_results_parse_03.json`. No lattice-estimator
attack or encrypted benchmark was rerun by this review. `_01.json` preserves a
review-parser failure on a Sage symbolic arithmetic string; `_02.json` fixes
that using restricted scalar AST interpretation, and `_03.json` adds current
pinned-source verification. None is an estimator-code change.

[EXECUTED reviewed values] At m=4096, the completed named lattice suite's minimum
log2 estimated work is as follows. These are separate model outputs, not proved
security bits or interchangeable hardware costs.

| Model | Q83 | Q109 | Attaining attack |
|---|---:|---:|---|
| MATZOV classical | 172.579637 | 127.556093 | BDD |
| ADPS16 classical core-SVP | 145.708 | 98.112 | uSVP |
| ADPS16 quantum core-SVP | 132.235 | 89.040 | uSVP |
| MATZOV quantum depth×width, original partial coverage | 164.224491 | 123.749318 | BDD |

[SOURCE/EXECUTED limits retained] GSA and reduction-cost models remain named
assumptions. Quantum reduction-cost substitution does not optimize every guessing,
FFT, memory or other attack step into a quantum algorithm. Four original optional
quantum depth×width dual-hybrid runs failed; three recover in fresh processes and
the Q83/infinite-sample case still fails. Their costs/failures remain separate from
original coverage, and the successful retries do not lower the displayed minima.
Nonlattice BKW/Arora results include timeouts and infinite output, neither of which
proves attack impossibility or all-attacks coverage.

[DERIVED monotonicity correction] The literal optimizer's Q109 BDD return is
slightly larger with infinite samples than with 4096, even in the saved fresh
recheck. An adversary with more samples can reuse the finite-sample attack. The
review record therefore also computes the minimum with that reusable finite-sample
cost, rather than treating the small increase as stronger security. The final
lane note correctly labels it numerical search behavior.

[DERIVED final interpretation] Q83 exceeds 128 under the named ADPS16 quantum
core-SVP proxy while Q109 does not. This is useful distribution-matched research
evidence; it is not a whole-route PQ theorem, a production recommendation, a
ring-specific attack audit, or protection from the surviving reader/release key.
The latest requested review tranche, including the reprioritized EMA bridge, is
complete at the recorded hashes. No companion, shared ledger or verdict was edited.

## 11. Generic Air simplification and the 15,208-gate reference

[EXECUTED independent compilation] The stable generic module
`formal/integer_certificate_emission/optimization/Compiler/AirSimplify.lean`,
SHA256 `a731cf62061751104e97619c9804530987a9cd2271b039edefbdcdb8cb583f79`,
and its application `IntegerCertificateSimplification.lean`, SHA256
`0cf4b3cbc725e186264c13eac1b681b66f65bcc8a1d5544108b0da84c8b7c8ef`,
independently compile with their 19+8 exact axiom pins. Records are
`lean_air_simplify_01.json` and `lean_integer_simplification_01.json` under this
review's experiment directory. I also rebuilt their two preserved integer-certificate
dependencies into the review-only overlay; `lean_integer_certificate_01.json` and
`lean_large_integer_certificate_01.json` retain those source/dependency hashes.
The proposed optimization patch is
`389015b446a8a09b4327de4dcc1008ef0d0a8a8a95342dc2a9b8b4b65f2d375f`.

[SOURCE/DERIVED: proof statement audit] `AirSimplify.simplify_eval_hom:104` and
`simplify_preserves:110` use the existing Air signature and `fold_unique` initiality.
The quantifiers range over every source term and every assignment of the *same*
input type and indices. The smart constructors use only valid field identities.
`simplifySystem_accepts_iff:132` preserves the conjunction of assertions in both
directions: it drops a syntactically constant zero, but retains a nonzero constant
contradiction. There is no proposed field-to-integer inference here; the earlier
range/carry proofs remain responsible for that lift.

[SOURCE/DERIVED: emitter/CSE boundary] The actual existing `Emit.emit:187` retains
`nPublic`, `nVars` and the input map `ix`, placing generated gates only above the
original-variable region. Existing `EmitShare.cse_emit_accepts_iff:588` transports
satisfying vectors through its auxiliary substitution while proving original
variable indices fixed, using emitted SSA and the `ix i<nVars` premise. The new
`cse_emitSimplified_accepts_iff:191` composes exactly that theorem. The application
recovers its original source relation for the same decoded public/input values,
rather than asserting that all old auxiliary values remain meaningful after CSE.
No semantic or public-variable substitution defect was found in this composition.

[EXECUTED independent census and controls] `SimplificationReview.lean` reconstructs
the actual large descriptors through their Lean definitions and confirms
52,378 original gates, 17,344 after source simplification and **15,208** after
simplification+CSE: 7,717 adds, 7,491 multiplies, 4,555 zero checks, 3,773 original
variables and a 21,117-wire header. It reruns all 64 small signed inputs and their
wrong quotients through four pipelines: **256** honest/forged pairs. The contradictory
constant remains refused; a deliberately unsafe drop-all-constants control accepts.
Two additional pinned lemmas retain the exact input headers and show that an erased
`0*x` dependency already imposed no condition in the original source. The successful
record is `lean_simplification_review_02.json`; `_01.json` preserves reviewer fixture
syntax and incorrectly predicted axiom-pin failures. They were not source-pass failures.

[DERIVED scope] The large example retains `nPublic=0`, Q
649033470896967801447398927572993 and **t=1048576**, the earlier signed rounding
reference. It is not the deployed scaler's t=1032193 exact-source certificate.
`nPublic=0` does not authenticate an external coefficient/output claim; such pins
must enter the consuming statement or verifier. CSE preserves its wire header and
can leave unused auxiliary slots, so the gate decrease does not imply an equally
small dense vector or that every CSE hole is constrained. The count is an emitted
arithmetic cost, with no HE runtime, cryptographic price, convolution, source-binding
or confidentiality theorem implied. The current optimization note states these limits.

## 12. Exact-source emitted BFV certificate

[EXECUTED independent compilation] The following six frozen modules under
`formal/bfv_lift_refinement/source_certificate/Compiler/` pass all **23** exact
axiom pins in the review-only overlay. The corresponding command/output records
are `lean_bfv_cert_{semantic,layout,emit,optimized,verifier,witness}_01.json`, with
source and direct dependency hashes unchanged during each compilation.

| Module stem | SHA256 |
|---|---|
| FheSourceCertificate | `12da5937356804b74b3e429d712daa33f10d41c77506aba67e29c345a66fe887` |
| FheSourceCertificateLayout | `580b6540040be2383d98ea99eb3b33f070bfa1a25e1be1bef617540eba234e3e` |
| FheSourceCertificateEmit | `c5e1fa8c24b6a59d2f974043b3b458fc7e78fe0ac083a5d1c2f6cf45990dec81` |
| FheSourceCertificateOptimized | `8afd28c21adfb97210d55661711e13959e5a025e9c3e8a5cbc998d3183ae4c9b` |
| FheSourceCertificateVerifier | `ff91e93e771a133bc61ca5f9620f139f13bf94fedab9208f556b5fc8a1b13ccc` |
| FheSourceCertificateWitness | `8c0878724091c81606a89d8c4b835da08c5837d47a596db4214ddb4bc1bbe9e7` |

[SOURCE/DERIVED: internal premises] The semantic relation in
`FheSourceCertificate.accepts:29` fixes two exact signed integer quotient/remainder
equations, then one quotient equation for canonical output modulo Q. Its
`forced_roundings:47` derives the exact source V and W from remainder bounds and
the previously checked canonical-domain source theorem. In the emitted path,
`FheSourceCertificateEmit.sourceDescriptor_balanced:79` supplies those premises:
all 462 scalar digits have six-bit range gadgets, every weighted accumulator has
range-checked result/carry limbs, and the two column bounds 1,866,508 and 2,097,151
are strictly below BabyBear. Each left/right row shares its result indices, so
integer equality follows from the two checked accumulators.

[SOURCE/DERIVED: matrix audit] The twelve balances contain six input-residue
complement equations `r_i+s_i=base_i-1`, the Garner quotient equation and a
remainder complement, the signed correction quotient equation and a remainder
complement, and the final whole-Q output equation plus output complement.
`balanced_source_accepts:108` obtains canonicality and the strict remainder/output
ranges from these natural-valued complements. They are not hypotheses supplied
by the host to `sourceDescriptor_sound:106`. Offsets for the signed correction and
output quotient are carried explicitly into the generated positive/negative linear
forms and canceled in the integer proof. The simplification+CSE theorem retains
these same decoded original variables. No alternate `{nearest, nearest+1}` choice
appears in the emitted soundness statement.

[EXECUTED independent descriptor evaluation] `bfv_certificate_review.py` parses
the actual Lean matrix literals and checks them against the retained layout JSON.
It independently creates variable arrays from the literal source shifts/sign branch,
evaluates the emitted JSON gates over BabyBear, and checks every zero assertion.
Record `bfv_certificate_review_02.json` uses the final six source hashes;
`_01.json` preserves the earlier pre-pin run. The optimized descriptor's uncompressed
SHA256 is `e440eb248c5fa754debf1a6d4defe1bdeb64c2c22cc66ebae0ba3ac486cc7566`.
Its **132,675** gates and **36,498** zero assertions are independently recounted.
The captured output 172481 passes, 172480 fails, and the noncanonical residue and
radix-digit-64 attacks fail. Three additional canonical vectors pass. This is
independent execution evidence against the real emitted artifact, not a replacement
checker theorem or a rerun of an encrypted benchmark.

[DERIVED + EXECUTED falsifier] A coherent alternate correction changes encoded W
down by one, increases its remainder by 2^128, and changes the output to 172480
while adjusting the output complement. **Every one of the other eleven matrix
balances holds**; only row 9, the correction-remainder complement, fails. The actual
emitted descriptor refuses it. `BFVSourceRangeWitness.lean` independently proves
that exact matrix tooth in the kernel, with one standard-three-axiom pin in
`lean_bfv_cert_range_tooth_03.json`. Its `_01`/`_02` records retain reviewer fixture
errors around unfolding the overloaded `Balanced` name. This falsifies dropping
the range row, rather than claiming a flaw in the accepted certificate. The
independent noncanonical-input fixture similarly recomputes the other groups so
that only its canonicality row fails at the integer-matrix level.

[SOURCE/DERIVED: external statement boundary] The descriptor still has `nPublic=0`.
`pinnedSourceCheck:13` explicitly compares its decoded six residues and group-18
canonical output to the caller's claimed integers before running the full-assignment
descriptor check. Its soundness/refusal theorems bind those exact pins. This is
useful local verification, not a succinct proof protocol: authenticating the pins
and binding the input residue vector to a committed ciphertext computation remain
separate obligations.

[OPEN: precise output and completeness boundaries] This tranche constrains **one
canonical integer output modulo Q**, not the concrete array of output residues
modulo each target q_i returned by Rust. A constrained projection/array wrapper,
NTT/convolution/Shoup lowering and provenance remain open; the source lane confirmed
this scope after review. Universal `honest_accepts` proves semantic certificate
existence for every canonical input. It does not establish that every such witness
fits and inhabits the finite emitted layout. The captured matrix/capacity witness
is kernel-proved and the full emitted array is executed; universal emitted completeness
is still separate. No duplicate large kernel reduction was attempted by this reviewer.
The source lane's abandoned resource-heavy raw-checker reduction is not an axiom or
a theorem in these six modules. Within this scope, the exact-source certificate
closes the earlier nearest-neighbor verifier freedom rather than hiding it.

## 13. Reusable contextual gate and actual EMA adaptive instance

[EXECUTED independent compilation] The generic
`formal/randomness_composition/generic/Compiler/ContextualGate.lean`, SHA256
`d17239cd62b3f09ab6f4a3a0adfa117876a088e60061f2fcaeb1a81a5750fc00`,
passes its 24 exact pins. The actual adapter
`Assurance/ResidentEmaAdaptive.lean`, SHA256
`99dc9d24683880bb4a434c5e204185512e9212f7334910def85f4355d22b7ac9`,
passes its 18 pins against this review's already independently compiled EMA and
Stage-0 dependencies. Records are `lean_contextual_gate_01.json` and
`lean_ema_adaptive_01.json`; source/direct dependency hashes are retained and unchanged.

[SOURCE/DERIVED: generic statement] `ContextualGate.contextReduction:34` keeps
one descriptor d, public-word width n, and m sumcheck coordinates, while selecting
the local commitment context from the queried root. `contextKState:56` and
`contextRbr:69` delegate the actual existing gate RBR state/proof obligations at
that root context, which stays fixed within each statement. The whole-statement
context remains adversarially selectable. `sound_reading:134` uses the inherited
`relaxedMem_iff` at δ<1/n to turn the approximate relation into the exact descriptor
event. No descriptor-specific or fake local reduction is substituted for EMA.
The adapter's `stage0_reduction_is_existing:41` proves the old reduction definitionally
equal to the corresponding generic instance.

[SOURCE/DERIVED: shared-log bound] `all_logged_outputs_bound:317` uses the same
reviewed selector construction: rebuild the deterministic prover's actual query
log from its responses, choose a bad public full-word output, and preserve every
oracle query by changing only `SrProver.out`. `AllOutputQueriesLogged:177` requires
each candidate's entire verifier-prefix query list to occur in the *final* shared
log, for every sampled coin sequence. The selected query is then covered by the
same premise. No new oracle query is needed to select public full-word badness;
there is no computation-time efficiency claim. This earns the single
`(t+m+1)·gatePrice` expression without another output-count factor in this game.
All correlated prior prover/verifier service transcripts must be generated inside
that charged log; deterministic strategy parameters are fixed independently of
the oracle coins. Final-log completeness remains distinct from runtime publication
ordering or a physical finality gate.

[SOURCE/DERIVED: actual logical-step adapter] The EMA adapter's
`wrapper_acceptance_transport:51` first obtains the wrapper's checked context and
actual fixed-context FS acceptance for the same receipt, then transports it into
the generic reduction. `bad_step_is_global_bad:58` uses the prior same-receipt
descriptor-to-LogicalStep theorem. `all_logged_bad_steps_bound:95` consequently
bounds bad accepted *logical Steps of opened plans*, rather than an unrelated
algebraic predicate. The earlier independently recomputed descriptor census gives
154 residuals, 8 coordinates, 153 word entries, 9 queries and
**(t+9)·161/2013265921^6**, with δ<1/153. This supplies the adaptive EMA theorem
that §9 correctly left open at the earlier source hash. It does not by itself
prove execution/persistence/currentness across a physical history.

[SOURCE/DERIVED: premises and oracle transport] The same authorized, changed-state
128→143 receipt is inhabited under one oracle; the separate nine-query witness
uses a planned verifier and an actual all-zero sampled transcript, whose cached
and fresh query values are proved zero. The wrong 128→144 sibling links and
materializes but fails the descriptor, while an empty query log fails completeness.
These are genuine premises at the actual EMA interface. The previously executed
zero-oracle false-word control also shows why an unqueried `loggedOracle` default
cannot be interpreted as a free random-oracle answer: dropping completeness would
let an empty log supply constant-zero challenges. The current bound retains the
necessary premise.

[OPEN: mixed-program and concrete-oracle scope] The new encoder is injective for
its fixed type and agrees with the fixed-context byte encoder. The Stage-0/EMA
cross-program encoding theorem relies specifically on public word lengths 4131
versus 153. It does not provide separate namespaces for two arbitrary descriptors
of equal width; arbitrary queried contexts may themselves carry either numeric
program value. Such extensions need another domain/descriptor binding argument.
Even for the two proved-disjoint encodings, a mixed-program query-transcript
projection/coupling theorem is still absent. The inherited distribution is uniform
Ext6 classical ROM, not QROM or the concrete byte-hash sampler discussed in §5.
The generic note explicitly retains these limits. No contradiction was found in
the currently stated generic or EMA theorems.

## 14. Fair hidden seed, disjoint mixtures and one observation

[EXECUTED independent compilation] The root's
`formal/recovery_policy/Theory/PrivateDistributionBudget.lean`, SHA256
`2b17dd27ac821a50f7364a6ff6d116d93189c587f6ee765bf19f64300b927d52`,
passes all 14 exact pins in `lean_private_distribution_01.json`. Its preserved
policy-evolution dependency was independently rebuilt in
`lean_private_policy_01.json`; no shared source was edited.

[SOURCE/DERIVED: nonvacuity] A secret bit is encoded as the parity of
`(seed, seed xor secret)`, with an equally likely unknown Boolean seed. The two
worlds have disjoint parity predicates. Public coordinate flips/swaps commute
with pairwise complement, so each permitted coordinate read still has exactly
one zero and one one across the two seed samples. `oneRead_samples:84` proves
equality of the full two-sample multiset after arbitrary postprocessing; event
probabilities follow by dividing the counts by two. Both worlds use the same
policy. This is a valid distributional privacy example even though the set of
all coordinate queries separates every distinct pair of point states. It does
not require a universally indistinguishable point-state pair.

[SOURCE/DERIVED: precise observation game] Policies are fixed public lists of
flips/swaps before one coordinate read, then arbitrary postprocessing of that bit.
They have no earlier state-dependent output or side channel. The pointwise
`public_policy_family_equal:105` permits an independently selected public policy;
it is not a joint conditioning theorem when public coins correlate with the hidden
seed. The two-read falsifier recovers parity, so one observation is a total budget
over the same private world, not a separate quota for every copy or restored fork.
Enforcing that budget against an operator who can copy state remains an external
continuity/integrity problem; this is an ideal-interface theorem, not encryption.

[DERIVED + EXECUTED scope teeth] The review-owned
`PrivateDistributionScopeWitness.lean` adds three small kernel-checked facts:
revealing the seed plus one second-coordinate read recovers the secret; even a
fair seed gives different joint transcript distributions when it is public; and
a hidden seed biased 3:1 gives event counts 1 versus 3 under a second-coordinate
read, hence distinguishing probability difference 1/2. Successful pins are in
`lean_private_distribution_scope_02.json`; `_01.json` preserves an overestimated
reviewer axiom annotation, corrected to the actual smaller axiom set. These teeth
make fairness and unavailable correlated side information load-bearing; they do
not refute the scoped fair-seed theorem. No additional probabilistic library or
encryption construction is claimed by the example.

## 15. Exact ciphertext expiry, installed history and conditional phase decoding

[EXECUTED independent compilation] All 44 durable-window and 62 HE-window pins
pass together in the review-owned overlay. The source versions are:

| Module | SHA256 | Pins | Independent record |
|---|---|---:|---|
| `Theory/CiphertextWindow` | `ad2e496b8f8d1fbf7125cf6be9306a97c9933a66c7882066d087a2b04c8605ee` | 17 | `lean_ciphertext_window_01.json` |
| `Assurance/CiphertextWindowCell` | `7b215707ee631a3d04854f6dd2fd044511dbcfd6d59b21c602380ff1d4c8a77d` | 7 | `lean_ciphertext_window_cell_01.json` |
| `Assurance/CiphertextWindowWitness` | `8503df829d5f5bcd9aa13bb5febd578b533dd3f8e8a075a687fa4fd30ffe9d92` | 20 | `lean_ciphertext_window_witness_01.json` |
| `Theory/IntegerWindowNoise` | `b3d49c23cf627f4598d5c81ed36ba93541f8e0463fe54da8629f2ee7d924bd98` | 20 | `lean_integer_window_noise_01.json` |
| `Theory/CiphertextWindowNoise` | `20bcc3b442c5e86f6d6abe4aad439228d5c6e965aa15f49140faa3769e2e8702` | 4 | `lean_ciphertext_window_noise_01.json` |
| `Assurance/ResidentBfvWindowNoise` | `cc98b5498fb737b7cd5bf5ccd3b8bda079e9c7707aa7f1c83e0401da35b8ecb6` | 24 | `lean_resident_window_noise_01.json` |
| `Assurance/ResidentBfvWindowPhase` | `74b61e28fe43883aa3e96717f5fa881f2a16bb1b70eb6e42dc269a167d540fac` | 14 | `lean_resident_window_phase_01.json` |

[EXECUTED provenance repair] The first HE validation packet still named older
durable dependency hashes. The HE owner refreshed all four unchanged modules
against the final durable hashes above. The review-owned
`window_semantic_review.py` checks the refreshed module/dependency hashes and
retains its successful output in `window_semantic_review.json`. This is a resolved
packaging mismatch; the earlier green packet did not establish the final
dependency combination. Neither companion tree was edited by this review.

[SOURCE/DERIVED: exact expiry and current sum] In `CiphertextWindow`, the checker
at :66 requires a positive capacity, the next admission ID, admitted canonical
fresh bytes and, when full, the exact current head's ID and encoded ciphertext.
The codec's left-inverse law makes equal canonical encodings imply equal
ciphertexts. `advance:77` actually subtracts the *proposed* expiry, so the check
does necessary work: `replacement_debt:229` exposes the old-minus-proposed group
element if it is bypassed. `reachable_queue_sum:294` proves that the accumulator
equals the sum of the current queue and the queue has at most W entries. IDs and
the admission predicate supply the stated provenance; they do not prove an
encryption/noise contract for a malicious issuer. `all_finite_horizons:339`
constructs every finite logical continuation for a positive W and an everywhere
admitted stream. It is not a funding, machine-counter or runtime liveness theorem.

[SOURCE/DERIVED: same actual durable carrier] `CiphertextWindowCell` serializes
the entire logical queue, accumulator and counter. `canonical_state_opens:83`
uses exact bytes, so it remains valid with a constant digest. The actual
`WindowPlan` holds exact pre/post openings of one validated plan.
`ExecutedHistory:169` begins with the actual empty journal and encoded initial
state; each edge opens the current DataSnapshot, passes the window checker and
full intent preflight, has a fresh transaction ID, and uses the existing
`DataSnapshot.install`. `executed_history_invariant:188` connects that same
snapshot's bytes to the logical state and equates its counter with the actual
journal length. This closes the detached logical-history seam for this carrier.
The three-step witness uses three real installs, expires the first ciphertext,
and proves replay does not subtract it again. It also explicitly refutes a
detached two-admission logical state paired with an empty durable journal.

[DERIVED + EXECUTED history scope tooth] This history consists exclusively of
window admissions. In the review-owned `WindowJournalFrameWitness.lean`, an
ordinary valid transaction makes a nonempty no-op write to another cell after
the three-step witness. The existing executor accepts it, the window bytes stay
unchanged, and the journal length becomes four. It cannot satisfy the same
`ExecutedHistory`, whose logical counter is three. The exact pin passes in
`lean_window_journal_frame_02.json`; `_01.json` preserves a reviewer fixture with
an empty write list that correctly failed preflight before the fixture was fixed.
Mixed workloads need a frame-closed history or a projection counting window
admissions, or an explicitly exclusive scheduler. This limits the carrier's
scope; it is not a counterexample to the proved invariant. A branch history also
does not establish unique global continuation, currentness or physical storage
refinement.

[SOURCE/DERIVED: phase and decoding premises] `IntegerWindowNoise.Fresh:27`
means the exact integer equation phase = floor(q·message/t) + error and a
coordinate error bound. It does not mean cryptographic independence or honest
random sampling. Its residual includes the necessary floor carry, giving
`|t·phase-q·message| ≤ t(E+1)`. Signed query L1 and at most W current rows produce
the strict margin `2tWL(E+1)<q`. `window_correctness:134` then proves modular
rounding for every integer lift differing by q times any integer;
`window_signed_correctness:175` additionally needs `2|score|<t` for the signed
answer. The positive/negative query split preserves total L1, with no extra
factor of two. The support lemma's `2NS²+S` bound is conditional on the two
specified signed product expansions and each factor's support bound.

[SOURCE/DERIVED: the modular bridge is substantive and conditional]
`CiphertextWindowNoise.PhasePremises:20` uses a query-specific additive map
`Ct →+ ZMod q`, equalities between every current entry's modular phase and its
interpreted integer row, and the output lift's modular equality to the
accumulator phase. `queue_integer_lift:44` derives the integer wrap from these
equalities and the actual queue sum. `reachable_signed_decode:83` retains the
per-entry Fresh, margin, query and signed-range premises. The review-owned
`CiphertextWindowReview.installed_signed_readout` composes this theorem with
`ExecutedHistory` on the same installed state and returns both its exact bytes
and its signed result; no independent substitute queue is introduced.

[DERIVED + EXECUTED missing-issuer-contract tooth] The same reviewer module
constructs an admitted one-entry state over ZMod 17 with an exact modular phase
map, query L1 one and an advertised E=0 margin 6<17. Its row instead has error
three. It satisfies Reachable and PhasePremises but fails Fresh and decodes one
instead of the claimed zero score. This proves that the public admission check
does not itself establish the Fresh premise. Together with the codec tooth in
§16, all three reviewer pins pass in `lean_ciphertext_window_review_02.json`.
No contradiction was found in the conditional phase/decoding statements.

[EXECUTED constants and nonzero controls] Independent integer checks in
`window_semantic_review.json` recompute
Q = 9671406214650060397780993, E = 3276820, L = 73279,
the score bound 1191223424 and margin left side 264008552994527828978432.
They test 108 signed cases, including dense extremal W=128 rows, at three
integer wraps each. The frozen Lean modules inhabit the actual arithmetic
parameters with 128 nonzero rows and score −128. The phase module separately
inhabits its whole one-admission subject with a nonzero transparent ZMod Q
ciphertext and result −1. Neither witness is an encrypted Rust BFV execution.
The source falsifiers for missing margin, signed wrap and wrong-expiry debt are
nonvacuous. The scalar wrong-expiry example reaches an incorrect output at
1125936375139850 substitutions; this is an exact arithmetic witness, not an
executed attack history of that length.

[SOURCE/DERIVED + EXECUTED source-equation boundary] Local `fhe-dregg`
`bfv/plaintext.rs:51` multiplies by q_mod_t and the stored inverse of −t;
`bfv/parameters.rs:418` constructs those constants. Independent calculation
checks 260 signed/representative cases of the resulting congruence with
floor(Qm/t) modulo Q. The public-key source at `bfv/keys/public_key.rs:64`
also has the algebraic two-product-plus-one-error shape used by the support
bound. This is source inspection and arithmetic checking. The seven frozen
modules do not prove the Rust/RNS/NTT operations, readout map or source sampler
refine these hypotheses. The HE owner's subsequent source-equation tranche is
separate work and is not included in the 106-pin claim here.

## 16. Canonical bytes, public normalization and retained history cost

[SOURCE/DERIVED + EXECUTED codec scope] The logical coefficient/vector codec is
a canonical encoder for ZMod values and fixed vectors; it is not the Rust
protobuf format. A lawful left inverse makes its encoder injective but does not
force its decoder to reject every noncanonical byte string. The review-owned
`coefficient_decoder_accepts_alias` proves that the natural-number encoding of
18 decodes as 1 in ZMod 17 while differing from the canonical encoding of 1.
This does not defeat the window's exact comparison of *canonical encodings* or
its exact installed-byte opening. It prevents promoting the codec law to a
general rejection theorem about unnormalized external input.

[SOURCE + EXECUTED retained serializer evidence] I read the actual ciphertext
serde and add/sub implementations and checked the final recorded probe against
all five current source hashes. `serde_check_02.json` executes source
`435b6e955d88a013ca64569123c9194e8e95c395000776b63fe3bdcecd380bc5`.
Its polynomial comparisons now assert equal component counts before using
`zip().all()`, closing the prefix-only comparison ambiguity identified during
review. The old source hash
`8dba04b655824e51c64d734fdf80b065980b7f97732c06c98fcff079919580b3`
and saved earlier run remain available. The reviewer did not rerun encryption.

[EXECUTED: fixture scope] The retained probe shows that the empty initial zero
has zero polynomial components and panics on serialization; a compatible
nonempty group zero serializes and decrypts to zero. A seeded ciphertext and its
expanded form have equal polynomial arrays and plaintext but unequal serialized
bytes (42545 versus 85022). Adding a compatible nonempty exact zero normalizes
these tested aliases, serializes the empty zero, preserves the tested expanded
public-key ciphertext bytes, and agrees after deserialize/serialize. That zero
is constructed publicly as a public ciphertext minus itself. The test retains
a secret key only to check plaintexts; the normalization operation does not use
it. This is evidence for the specified cases, not a master-key absence claim.

[SOURCE/DERIVED: runtime domain still required] The actual add/sub code checks
parameter Arc identity and, for nonempty operands, compatible level and
component count. Empty branches and seed-clearing behavior matter to the
normalizer. A general law relating this operation and protobuf decoding to the
logical codec still needs a lawful runtime domain and a proof of the underlying
ring/group and representation refinements. Equal polynomial values alone did
not make raw serialization canonical in the executed seeded/expanded fixture.
These limits are explicitly retained by the durable lane's final README.

[DERIVED: active-window size versus retained durable payload] A bounded current
queue does not bound the whole composed durable carrier by O(W). The existing
`Kernel/DurableDataIntent.ReplayEnvelope:89` deliberately keeps the exact writes,
and `DataIntent.erase:118` journals their complete canonical post bytes.
`ResidentDurableIntegration.Plan.intent:111` writes the full materialized post;
`CiphertextWindowCell.stateStream:40` encodes the current queue, accumulator and
counter. `Kernel/DurableCommitProtocol.Snapshot.install:151` retains each intent
in the journal, and this history has no compaction operation. For T admissions
after a fixed-width ciphertext window fills, the accumulated serialized replay
payload can therefore scale as T·W·ciphertext_size, plus IDs, counters and other
transaction metadata. This is a semantic retained-payload accounting, not an
assertion that a runtime cannot share or compress storage. Current noise still
depends on W because the accumulator cancels exact expired ciphertexts. The
Rust current-queue benchmark does not exercise this complete durable journal;
its memory figure should not be used for the composed carrier without a
separate persistence measurement or compaction refinement.

## 17. Independent-key ladder and a uniform growing horizon

[SOURCE + DERIVED reviewed conditional positive] I independently read the local
2013/729 paper's Definitions 2.1–2.4, Remark 2.5, Lemma 2.9, construction §4,
simulator §5.1, eleven hybrids §5.2/Appendix A, correctness Appendix B and
SIM-to-IND argument Appendix C. The paper at
`/Users/ember/dev/gh/forks/IACR-eprint-mirror/2013/729.pdf` has SHA256
`58bb2eb72bc8e5c3eaf3193fefd6c72754ff428265231fb459b0de6c8db32e30`.
The exact `pdftotext -layout` command is retained in
`experiments/adversarial_review/horizon_review_01.json`; its full text output
is explicitly ignored scratch. No paper was downloaded and this review made
zero metered queries. The conditional source theorem and the reduction below
were reviewed mathematically; they are not a newly kernel-checked cryptographic
theorem or an implemented FE system.

[EXECUTED versions] The final reviewed `FINITE_LADDER.md` hash is
`3c94a21d5a529b568da5392702c65cda7e22ace8e5f7be40a783ae93c43cb71c`.
The revised `horizon/HORIZON.md` hash is
`f1415e2c95600e52a00c9fdb5e3b6c7bcf55cf2d726ffa9341f1abe9ff3d5743`;
its audit script and result hashes are respectively
`7fc7e24fc84152feb199cea4c83758557ff889f5b513fb902fa63e038950e6e9`
and `0ae1ec22377b36443aa0867e933a7f592fa9fbf0baf95a7f8573f0591b523b61`.
The independent final record is `horizon_review_01.json`; the earlier
`horizon_review.json` preserves the intermediate padded-selector version
before the explicit uniform-sampler paragraph was added. All recorded inputs
were unchanged during their respective checks. The four fixed-H=2 artifacts
were not changed by the growing-horizon repairs.

[SOURCE/DERIVED: simulator quantifiers and timing] Definition 2.3 pp.6–7 places
one simulator S before the quantifier over all PPT adversaries. Its A1 selects
the challenge plaintext before setup. Its q counts challenge plaintexts, not
function keys; key queries may occur in A2/A3. Theorem 4.1 and the explicit
S1/S2 in §5.1 pp.14–15 supply the same algorithms for every sampled ladder
node and side. S1 samples the current simulated setup and zero challenge without
the private plaintext. S2 obtains the ideal output of the requested function,
punctures a fresh PRF key, and obfuscates a program containing that output at
the challenge point. No adversary-dependent simulator is chosen separately at
each depth, and no preceding distinguisher's code is an input to the obfuscator.
The one-SIM comparison requires no equality or compatibility promise on two
plaintexts; its cryptographic assumptions remain the stated classical iO/OWF
source assumptions.

[SOURCE/DERIVED: full future exposure is included] For the fixed ladder,
Definition 2.4 pp.7–8 permits computational indistinguishability of the joint
pre-setup auxiliary/function-output law. Generating future layers first puts
the complete future package P_(i+1), including every issued future key, in that
auxiliary distribution before current setup. Each current transition function
embeds only the next public key. Appendix C p.25 footnote 8 explicitly discusses
adjoining the current setup secrets in the ideal-output argument; independence
from the current setup is the premise that makes this safe. It does not license
discarding future keys or assuming they are independent of future ciphertexts.
The candidate's common-P_(i+1) ciphertext hybrids keep these correlations and
sample only the other known candidate encryptions with independent coins.

[DERIVED: exact expansion] For one node's test A, the identity is
`Real(u)-Real(v) = [Real(u)-Ideal(u)] + [Ideal(u)-Ideal(v)]
                  - [Real(v)-Ideal(v)]`.
The middle test receives one whole future package and all B child ciphertexts.
It builds the current S1/S2 simulated package as independent postprocessing.
Telescope this vector one position at a time using the same future package;
the sibling positions use right candidates before the selected position and
left candidates after it. Equal current answers follow from R_i. At a terminal
node g(u)=g(v) makes the remaining ideal-output gap exactly zero. Recursive
expansion therefore gives 2N_H oriented one-SIM gaps. The right-side bit
complement is necessary to obtain the negative terms; there is no requirement
that all individual gaps have the same sign.

[DERIVED: selected-node challenge and ancestor interface] The sampled prefix
is chosen independently of setup randomness. Its two candidate states are
computed from the original state pair and public Step descriptions before
the selected instance's setup; neither computation needs its public key or a
future key. A1 can then generate the complete future package and retain it,
the prefix and candidate data. A2 requests only the selected layer's prescribed
keys. After the selected challenge arrives, the reduction constructs ancestor
packages using the same explicit S1/S2 and publicly generated sibling
ciphertexts. The host receives these ancestor packages as well as the complete
selected/future package. It receives neither the reduction's retained candidate
plaintexts nor its simulated raw setup secrets. This fits the source A1/A2/A3
syntax and accounts for ancestor exposure. Sampling a path in response to the
host's ciphertext-dependent behavior would not have the same selectivity
argument and is not performed here.

[DERIVED correction, now repaired: exact bounded-time sampling] The first draft
identified the arithmetic average Δ/(2N_H) directly with an exact strict-PPT
fair-coin implementation. Unless 2N_H is a power of two, a fixed bounded number
of fair bits cannot give each rank probability 1/(2N_H); those probabilities
are not dyadic. Root supplied the cleaner repair now present in the lane:
let M be the least power of two at least 2N_H, sample log2(M) bits, and assign
extra ranks a valid one-message source experiment with no key queries and a
constant final bit. Definition 2.3 permits this dummy: one challenge does not
require a function-key query, and projecting to the constant final output has
zero gap. Thus the strict-PPT reduction has the exact signed probability gap
Δ/M with `2N_H ≤ M < 4N_H`. The mathematical uniform average Δ/(2N_H) remains
correct as an arithmetic identity. For B=3,H=2, 26 real ranks are padded to 32,
requiring five fair bits and six dummies. This is a constant-factor correction,
not an obstruction to the logarithmic conclusion.

[DERIVED correction, now explicit: uniform inputs] A uniform one-SIM adversary
must also generate its initial state pair and public Step descriptions through
a uniform PPT pre-setup sampler, or use fixed uniformly computable families.
Polynomial description length alone does not supply such a generator.
Definition 2.3 uses A1(1κ), whereas Definition 2.4 explicitly admits nonuniform
adversaries and auxiliary z. The final note now states the uniform-sampler
premise rather than silently importing arbitrary advice into the uniform
corollary. A nonuniform or quantum-advice version needs the corresponding
security convention or another lift. The given width-m=λ, pair-(0,1), public
add/double/infer example meets the uniform premise.

[SOURCE/DERIVED: runtime bound survives the wrappers] Each ancestor wrapper
calls the previous distinguisher once. The source `Sim.G_f` contains one
bounded transition/encryption circuit, one next-public-key literal, a fixed
challenge and one fixed-format output; it does not contain future function-key
code or an obfuscation of its caller. Public FE encryption §4 itself does not
include f or its function key. With a common polynomial bound C for the
chosen state width, circuits, primitive algorithms and B fixed commands,
generating the future package and wrapping the ancestors takes O(H·C) extra
work, plus polynomial integer/rank arithmetic. It does not iterate the host's
runtime through a fresh polynomial at every depth. This is a source-level
uniform polynomial bound, not a concrete cost or efficiency measurement.

[DERIVED conditional consequence] A polynomial N_H and a uniform PPT host with
non-negligible signed output gap would give one uniform PPT source adversary
with non-negligible gap Δ/M. The explicit same-S reduction avoids a diagonal
argument over separately chosen negligible functions. For fixed B>1, H=O(log λ)
suffices; for B=1, polynomial H also has polynomial N_H. For branching
superlogarithmic H the audited expansion has a superpolynomial loss. Its path
implementation may remain polynomial, but ordinary negligible security no
longer pays for the loss. This is a limitation of this proof, not a lower bound
or an attack on every longer ladder. The deployed object count is linear in H;
the proof-tree size is a separate quantity.

[SOURCE/DERIVED: primitive bookkeeping is not the theorem] With zero external
decryption-oracle queries, H6→H7, H8→H9 and H10→H11 make no changes. The other
source transitions have three per-key iO switches, one per-key punctured-PRF
switch, one commitment-hiding switch, one NIWI-WI switch and two PKE switches
per SIM side. Local evaluation of exposed keys is host computation, not an
external oracle query. The displayed 272 computational edges at B=3,H=2
(126 iO, 42 PRF, 26 commitment, 26 WI, 52 PKE) are consistent with those
transitions. The extra NIWI bad-equivalence allowance is conservative conditional
bookkeeping. These counts do not instantiate any epsilon or prove a new
resource-indexed primitive theorem. Alternative imperfect correctness or
equivalence contracts need their errors added. In particular, Definition 2.1
and Appendix B describe computational randomized-output correctness, not exact
fresh independent randomness under repeated evaluation of the same key and
ciphertext. The ladder's deterministic Step and the source SIM argument do not
need to upgrade that statement to an unbiased lifetime-randomness guarantee.

[EXECUTED independent controls] `horizon_review.py` compares 1,408 independently
enumerated node/side labels with the owner's unranking and replays the owner's
pure audit functions without invoking their file-writing main. More
substantively, a separate deliberately insecure finite channel constructs
correlated exposed future packages and the actual nested ancestor-wrapper
shape, then enumerates exact probabilities through horizons zero, one and two.
The root gaps 3/4, −1/8 and 1/16 equal the sums of the oriented node gaps;
the padded reductions give 3/8, −1/64 and 1/256. Omitting the right complement
fails in all three cases. A shared-pad control has identical ciphertext
marginals but disjoint exposed-package joint worlds, making omission of the
future auxiliary information falsifiable. These are reduction-wiring controls,
not evidence that the intentionally transparent channel is secure.

[EXECUTED fixed-interface replay] `horizon_h2_replay.py/json` independently
replays all 256 states and 2,304 two-command paths, the 14 behavioral classes,
the seven exposed issued keys and the empty raw-master registry. An initial
raw-Python comparison failed because JSON converts integer dictionary keys to
strings; the retained record identifies that reviewer issue and the normalized
comparison matches the saved result exactly. These checks establish the stated
symbolic interface and schedule only. No cryptographic malformed-ciphertext
rejection, erasure or privacy follows from registry handles.

[OPEN / scope of the positive] No further simulator-interface, correlated-auxiliary
or recursive-runtime defect was found after the two repairs above. The result
remains a classical source-conditional, selective-state, preissued finite-horizon
privacy construction with honest erasure and public commands. It exposes all
issued program strings, permits forks, and has no private fresh-input join,
masterless horizon extension, receipt binding, finality/currentness guarantee,
concrete efficiency result or post-quantum theorem. The relation must continue
to admit nonidentical states as the horizon grows; the finite nonvacuity controls
do not make that automatic for another learner.
