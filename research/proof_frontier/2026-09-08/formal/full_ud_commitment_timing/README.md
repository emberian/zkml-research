# Arbitrary-root adaptive FRI: a finite semantic bridge

[EXECUTED] This package removes the honest-root-image premise from the adaptive
FRI consumer. A malicious strategy supplies only a level-n root as a function of
its first n challenges. Canonical opening resolution constructs the existing
`FriAdaptiveTranscript` over `idealCommitment`; accepted original query openings
map into that existing verifier or retain a selected-root double opening.
No word is assumed independently of future challenges: its prefix dependence is
derived from the actual root-selection function and the fixed opening scheme.

[SOURCE] The current companion already has correct adaptive timing:
`/Users/ember/dev/minidregg/Selvage/HalfThresholdFriQuery.lean:40`,
`FriAdaptiveTranscript.word/root : ∀ n, (Fin n → F) → ...`.
Its extra `root_eq_commit` field is stronger than position binding in
`Selvage/Commitment.lean:113`. By contrast, `FriCommittedStatement` in
`Selvage/HalfThresholdFriTranscript.lean:35` fixes all words/roots before the
challenge tuple; the frozen `FullUDFriConsumer` whole-opening head retains that
scope. We do not relabel the fixed theorem adaptive.

[EXECUTED] `OpeningResolution.honest_image_falsifier` proves the exact missing
implication is false. A binding scheme uses roots `(word, Bool)`, always commits
with tag `false`, and verifies values by the word component. Every `true` root
is fully openable with unique values and has no honest commitment preimage.
Thus `root_eq_commit` cannot be supplied by binding alone.

## Actual source timing

[SOURCE] The active Cargo patch is
`/Users/ember/dev/breadstuffs/Cargo.toml:247–250`, selecting
`vendor/plonky3-fri-82cfad73`. Actual vendored `src/prover.rs:218–233` commits and
observes the current root, obtains a proof-of-work witness, samples the fold
challenge, and folds; the next iteration chooses its root after that challenge.
The final polynomial is observed at `prover.rs:257`, before query indices are
sampled at `prover.rs:111`. This is source inspection, not execution equivalence.

[SOURCE] Actual `src/verifier.rs:213–238` replays root observation, proof-of-work
checking and fold-challenge sampling, checks the final coefficient-vector length,
and observes that vector. It samples query indices at line 268, authenticates
evaluation rows around line 447, and checks the carried fold against the final
polynomial evaluation at lines 319–325. There is no extra terminal Merkle root.
All inspected source hashes and locations are retained in `source-evidence.json`.

[DERIVED] The prefix index n is consequently the right timing interface for
round-n roots; the final polynomial belongs at prefix length m. Mapping actual
variable-arity row layouts and bit-reversed indices to our fixed binary
`FoldingTower`/modulo schedule remains a separate execution obligation.

## Statement and implemented bridge

[EXECUTED] `OpeningResolution.word S default root i` chooses an accepted value
at position i if one exists, otherwise the explicit default. It is a semantic
`Classical.choose` definition. Its theorem-first `Correctness` contract proves:

```
accepted(root,i,value,path)
  → value = resolvedWord(root,i) ∨ DoubleOpening(S,root)
```

[EXECUTED] `DoubleOpening` retains two values, two paths, the common position
and root, both acceptance proofs and inequality. The existing
`BinaryMerkle.accepted_different_values_imply_collision` consumes those witnesses
without an honest-root-image premise. Exact position binding removes this branch.
On an honest commitment, resolution recovers its original word.

[EXECUTED] `OpeningResolution.transparent` adjoins transparent word roots to
an original raw `OpeningScheme`. Its ordinary commitment/opening functions are
preserved using left injections; ordinary roots/paths invoke the original
verifier, while transparent right roots verify symbol equality. This models a
revealed final evaluation word without a terminal Merkle commitment.
`transparent_terminal` proves terminal attribution reduces exactly to the
existing Reed–Solomon membership check for such a root.

[EXECUTED] `FriRootResolution.SoundReduction` states and `sound_reduction` proves:

```
raw SampledAccepts(S,T,degree,rootStrategy,r,Q)
  → existing FriAdaptiveSampledAccepts(idealCommitment,T,degree,resolvedTranscript,r,Q)
    ∨ BadRoots(S,rootStrategy,r)
```

[EXECUTED] `BadRoots` ranges over roots selected at levels `n ≤ m` of that actual
challenge execution. Raw acceptance reuses the existing `FriRoundQueriesAccept`
and `OpenedFriQuery`, preserving existential malicious opening data. Its terminal
condition retains a low-degree word plus full attribution to the terminal root;
for transparent terminal roots, attribution is just equality. The existing
`FriAdaptiveTranscript.wordAt_congr` proves the resolved words are prefix-measurable.

[EXECUTED] `coherent_probability_reduction` is the exact finite event bound:

```
Pr[raw coherent acceptance]
  ≤ Pr[existing ideal coherent acceptance] + Pr_challenges[BadRoots].
```

[EXECUTED] `coherent_sound` feeds the existing coherent theorem directly and
obtains `m*b/card F + (1−tau)^q + Pr[BadRoots]`. It carries the original tower,
radius/fold transitions and initial resolved-word farness premises explicitly.
`coherent_sound_binding` removes the added term under proved position binding.

[EXECUTED] `BabyBearFriRootResolution` imports the frozen full-UD schedule and
actual BabyBear extension carrier. `fullUD_coherent_sound` discharges all schedule
and transition premises using that existing result. `babyBear_coherent_sound`
transfers its 3603-query result as `Pr[raw accept] ≤ 2^-55 + Pr[BadRoots]`.
This is an ideal challenge/query contribution plus an unpriced binding event,
not a total 55-bit security claim. No radius or query arithmetic is duplicated.

## Witnesses and limits

[EXECUTED] `FriRootResolutionWitnesses` uses the existing actual F5 one-round
multiplicative tower `{1,2,3,4} → {1,4}`. Its initial root is the off-image tagged
commitment to X; the transparent terminal word is the challenge itself. Raw
acceptance holds for every challenge and every query batch, the bad event is
refuted by proved binding, and the reduction reaches existing ideal acceptance.
The final resolved word varies with the challenge. Separate falsifiers reject
both a single fixed final word and letting the initial word depend on a future
challenge. The permissive-scheme witness also inhabits a real double-opening event.

[OPEN] Canonical resolution is semantic, not a polynomial-time extractor.
`BadRoots` asks whether two accepted paths exist at a selected root, including
paths from alternative executions or outside the supplied proof. Its probability
is **not** automatically a standard efficient collision-adversary advantage.
The deterministic Merkle implication does not price exhaustive path search or
rewinding. An efficient reachable-transcript extraction reduction is still needed
to replace this event with a deployed collision bound. No such bound is asserted.

[OPEN] Initial farness is of the root-resolved word. Under exact binding, an
honest initial root `commit w` resolves to w; the theorem does not derive a FRI
input-farness statement from a PCS/IOP relation. The generic and BabyBear heads
still need the actual folding tower, initial-farness reduction, protocol-to-source
index/layout connection, and Fiat–Shamir/challenger/PoW composition. The F5 witness
does not establish a 19-round BabyBear deployment witness.

[EXECUTED] Checks, exact source/patch hashes, theorem/pin census and integration
entry are packaged alongside the additive patch. Root owns full umbrella
integration. No companion or frozen predecessor was edited. This follow-on used
zero Scry SQL and zero web queries; it inspected current local source only.
