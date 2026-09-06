# Recovery and policy evolution

[DERIVED scope] A recovery or upgrade credential belongs in the same accumulated
exposure game as writer and release credentials. Authorizing a new program is a
computational capability; a signature authenticates its use but does not establish
that the resulting program preserves the resident's intended private distinctions.
This lane studies the ideal functionality, not encrypted migration implementation.

[SOURCE: local definitions read] `Theory/PrivateTrace.lean:155`,
`trace_eq_of_preserved`, already gives adaptive trace equality for a relation blind
to output and preserved by every command. `Theory/PrivacyProfile.lean:126`,
`ReleaseSemantics`, separates permission from the selected output projection. Both
paths are relative to read-only `/Users/ember/dev/minidregg`. The proposed extension
will reuse these definitions, include the active version in public observations,
and quantify over migration commands as well as ordinary learning commands.

[EXECUTED] The proposed `Theory/PrivatePolicyEvolution.lean` compiles with fifteen
exact axiom pins. The main `versioned_trace_eq`, its output/step reductions, the
unsafe-migration contradiction and the joint-disclosure general theorems use no
axioms. Some finite witness proofs use standard `propext`/`Quot.sound`; the exact
inventory is pinned beside every theorem. `lean_policy_05.json` records the final
source-matching module check; `review_policy_01.json` records isolated Theory
umbrella, staged/original import boundary and `git apply --check` success. This is
not a full clean companion build; no companion source was edited.

[DERIVED] `Safe` has three explicit obligations: outputs respect the relation;
learning preserves it; every admitted migration maps related states to related
states at its destination. `Evolution.machine` includes the version in public
observations and takes both learning and migration as adversary-selected commands.
The general theorem follows through the existing adaptive-trace theorem for every
policy and every length. Admission and destination are functions of public version
and command. State-dependent rejection or destination metadata needs an enlarged
model; it is not silently hidden by this theorem.

[EXECUTED] The positive witness has two Boolean coordinates. Learning changes the
visible coordinate; migration swaps the coordinates and changes which one is read.
The representation really changes while the private distinction persists under
every interleaving. A sibling migration switches the reader but fails to swap the
representation: it is admitted and leaks the formerly hidden bit. Thus permission
alone does not inhabit the migration-preservation premise.

[EXECUTED] `python3 research/learn_infer_only/experiments/recovery_policy/policy_audit.py`
records 8,176 equal-trace checks over all command strings through length eight and
all sixteen related ordered pairs. This finite enumeration is a separate check;
the adaptive/all-length result comes from Lean. For the 25 states in F5², each of
the two coordinate policies alone leaves five classes of five states. Retaining
both policies produces 25 singleton classes. A compatible second policy `2a+1`
leaves five classes of five. Deleting the first policy from admission does not
delete its previously saved answer.

[DERIVED scope, independent review incorporated] `JointlyEquivalent` concerns
projections on the **same semantic state** and actually usable retained capabilities.
Its union theorem does not prove that an old epoch key decrypts a rekeyed current
ciphertext, or that an old answer about s0 identifies s1 after private migration.
It applies directly to multiple IPFE keys under the same public setup. The dynamic
version machine exposes only its active-version output; a cryptographic migration
claim against copied old evaluators must add their calls/artifacts to that machine
or separately prove their observational simulation. No such implementation result
is asserted here.

[DERIVED recovery split] Export recovery intentionally supplies a state-opening
capability. Keyless recovery may instead locate an already protected snapshot and
ask an independent continuity authority whether it is current; no decryption key
is logically required by that lookup. Equal manifest references alone establish no
storage confidentiality. The durable lane separately checks actual current-state,
preflight, journal and retry behavior. Neither this ideal migration theorem nor
the manifest toy supplies encrypted state transport or a surviving-key audit of it.

[OPEN] Next real migration target: give a concrete source/target ciphertext and
key-switch mechanism, name the union of old/new/translation credentials, show the
exact state relation before/after, and expose all old snapshots/capabilities. A
new privacy claim needs that cryptographic argument in addition to these semantic
conditions. Fresh private migration entropy requires the randomized coupling
extension and an explicit selective-abort model.

[EXECUTED] Search accounting: Scry 0, Kagi 0, web 0. `rg` over the companion's
`Theory/` and `Kernel/` located the existing privacy and revocation definitions;
no claim is made that an equivalent theorem is absent from all research literature.

[SOURCE: primary game read by entropy lane] The randomized-FE paper ePrint2025/330,
Definitions4.3–4.5, printed pp.22–25, checks compatibility across the complete
queried function-key set. Its displayed games do not remove old keys on revocation.
Exact local source hash/access record is in `RANDOMNESS_COMPOSITION.md`; this
supports cumulative-key accounting for that stated game, not a universal theorem
about every migration construction.
# Distributional nonvacuity needs its own observation budget

[EXECUTED] A follow-on module,
`formal/recovery_policy/Theory/PrivateDistributionBudget.lean`, distinguishes
point-state separation from distributional disclosure. It reuses the existing
coordinate reader. The protected bit b selects a uniformly sampled state
`(seed, seed XOR b)` with an unobserved fair seed. The b=0 and b=1 supports are
disjoint and their parities differ. Every distinct pair of point states can be
separated by some coordinate query; nevertheless, one coordinate observation
has exactly the same distribution in both worlds.

[EXECUTED theorem] `oneRead_samples` fixes the entire transcript multiset for
every finite public sequence of coordinate flips/swaps, one coordinate read,
and arbitrary postprocessing into any output type. It uses only `Quot.sound`.
`oneRead_worlds_equal` and `oneRead_event_count` give exact distribution/event
equality after dividing the two equal-count samples by two. An independent public
coin can select the policy before the read. `active_witness_uniform` inhabits a
nonempty update sequence; `worlds_disjoint` pins the protected-predicate difference.
`two_reads_recover` and `second_read_distinguishes` supply the budget falsifier.

[DERIVED scope] This is a finite ideal-interface statement, not encryption or a
claim about all adaptive learners. The only state-dependent view is that one bit;
public preprocessing and arbitrary continuation/output chosen from it are included
as postprocessing, but a second read or a hidden-state side channel is excluded.
The fair seed must be unknown to the observer. Retained initializer coins would
change this view. A relation between point states is a sufficient nonvacuity
instrument, not a necessary one for distribution-valued challenges.

[EXECUTED] `experiments/recovery_policy/distribution_audit.py` checks 2,912 Boolean
policies with zero through five public updates: 11,648 transcripts and 11,648 equal
event-count checks. It retains all six distinct point-pair coordinate separators
and the two-read parity outputs. The Lean theorem covers arbitrary finite update
lists and arbitrary postprocessing types; the finite script is an independent
control, not its universal proof. Command/result are in `distribution_audit.json`.

[EXECUTED verification] Fourteen exact axiom pins pass in
`experiments/recovery_policy/lean_distribution_03.json`; the staged Theory umbrella,
both import boundaries and patch applicability pass in `review_distribution_01.json`.
Source SHA256 `2b17dd27ac821a50f7364a6ff6d116d93189c587f6ee765bf19f64300b927d52`;
patch SHA256 `e0ff46cd158debc50d901a4059266eef1afc311f968462ad345b5a87eca2a188`.
The original policy source and its 15-pin patch remain unchanged. The common lane
harness now accepts `--module PrivateDistributionBudget --review`, retaining its
old default; on a fresh checkout run the default first to build the local dependency.
Eight pins have no axioms, four use only `Quot.sound`, one also uses `propext`, and
the concrete two-read multiset inequality uses the standard triple. Existing
dependency oleans were reused; a combined source integration is separately queued.
