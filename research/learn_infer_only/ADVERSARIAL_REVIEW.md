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
