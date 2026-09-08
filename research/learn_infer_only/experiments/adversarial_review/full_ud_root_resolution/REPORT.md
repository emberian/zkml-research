# Independent audit: arbitrary-root adaptive FRI resolution

[DERIVED — accepted, scoped] No blocking proof or statement error was found in the frozen [five-module timing package](../../../../proof_frontier/2026-09-08/formal/full_ud_commitment_timing/README.md), patch SHA-256 `449608f151061051d3c2567d86d6b505c86ecf03906f990ffb7a5238995e4756`. It proves an acceptance-preserving finite semantic reduction from arbitrary prefix-selected roots into the existing ideal adaptive FRI event, with an explicit selected-root double-opening alternative. It does not assume the desired honest-image equation for raw roots.

[DERIVED — exact numerical scope] On the existing BabyBear extension carrier, existing 19-round full-UD schedule and existing coherent 3603-query sampler, the exported head is

```
Pr[raw acceptance] <= 2^-55 + Pr_challenges[BadRoots].
```

[DERIVED] The initial root-resolved word must be `2/5`-far from the specified initial Reed–Solomon code, and the actual folding tower remains an argument. `BadRoots` is semantic existence of conflicting accepted openings at a selected root. It is not an efficient collision-adversary advantage. Consequently this head is not total 55-bit security for an executed FRI/PCS protocol. No correction to the frozen mathematical source is requested.

## Exact source and validation scope

[EXECUTED] [check.py](check.py) independently reconstructs each new module from the additive patch and compares its exact bytes with the frozen source. It verifies the five source hashes, every theorem/lemma against its unique guarded axiom pin, the author's saved final-check hash/exit records and empty logs, eight pinned source-evidence files, and 16 dependency source hashes in the author's read-only isolated checkout. No Lean command was rerun; root owns combined kernel/build validation. Final execution exited zero; [check.log](check.log) and [results.json](results.json) retain the command's complete output.

| Module under `src/Selvage/` | SHA-256 | Declarations / pins |
| --- | --- | --- |
| `OpeningResolution.lean` | `1233c1c49f79e7d3581151b8151aac3aa2ae7e61f688bb316a30671e405710d4` | 14 / 14 |
| `FriRootResolution.lean` | `547338388ba7e6b8671056deaf7f75d1292034fede46e4a0f85fb8170f7218ef` | 6 / 6 |
| `FriRootResolutionSoundness.lean` | `12d283184598a1239457fcba9ddf74b5b523e0f1d005728d14745c79aec9468b` | 3 / 3 |
| `FriRootResolutionWitnesses.lean` | `dc43a2edb8b18e281e9dd5c9f43373e2a586715d4705d048ec3350dce8c199f0` | 10 / 10 |
| `BabyBearFriRootResolution.lean` | `88c696ef983143d22ce9720b3cada9efa06d63930b343e3b99280ed4cbc5c60c` | 3 / 3 |

[EXECUTED] The inspected five-module corpus has 36 theorem/lemma declarations and 36 exact guarded pins; lexical scanning after comment removal found no `sorry`, declared `axiom`, `admit` or `native_decide`. Pinned dependencies contain only the usual `propext`, `Classical.choice`, `Quot.sound`, or no axioms. This source/record audit does not substitute for root's combined Lean build.

```sh
python3 research/learn_infer_only/experiments/adversarial_review/full_ud_root_resolution/check.py > research/learn_infer_only/experiments/adversarial_review/full_ud_root_resolution/check.log 2>&1
```

## Resolver and timing argument

[SOURCE/DERIVED] `OpeningResolution.word` (lines 21–25) takes only a fixed scheme, default, root and position. It selects an accepted value when any exists and otherwise uses the default. `word_openable` produces an accepted path for the chosen value; `correctness` (lines 41–47) pairs that path with a conflicting supplied path if the values differ. Thus an accepted value equals the resolved value unless that same root admits a double opening. Unopenable positions do not make acceptance vacuous: they simply cannot supply a raw accepted opening. Their default values are fixed before sampling.

[DERIVED] The use of `Classical.choose` is noncomputable but not future-dependent. The definition is a fixed mathematical function of the root and scheme. `Strategy` is `∀ n, (Fin n → F) → Root n`, and `resolvedTranscript.word n p` resolves `st n p` under fixed `S n`. `resolved_word_prefix` invokes the existing `FriAdaptiveTranscript.wordAt_congr` to prove equality on executions sharing the first `n` challenges. Both scheme and strategy are quantified outside the challenge/query probability; neither accepts the sampled query seed. The level-zero root is fixed, level `n+1` may depend on challenge `n`, and the level-`m` terminal object may depend on all `m` fold challenges while remaining fixed before queries.

[SOURCE/DERIVED] The original adaptive interface, `/Users/ember/dev/minidregg/Selvage/HalfThresholdFriQuery.lean:40`, already supports this prefix timing but also requires `root_eq_commit`. The new resolved transcript supplies that equation only for the existing identity commitment, where root and word are definitionally equal. Original raw roots remain in the raw verifier and are not falsely asserted to be honest commitments. The earlier `FriCommittedStatement` at `HalfThresholdFriTranscript.lean:35` still fixes every word/root before the challenge tuple; this package does not broaden that predecessor theorem.

[SOURCE/DERIVED] `OpeningResolution.tagged` and `honest_image_falsifier` (lines 132–148) exhibit a complete position-binding scheme with two root tags and honest commits only at tag `false`. Tag-`true` roots have unique complete openings but no honest preimage. This refutes precisely the missing implication from binding/openability to `root_eq_commit`; it is not a manufactured empty accepting set.

## Raw acceptance and transparent terminal word

[SOURCE/DERIVED] `RoundAccepts` calls the existing `FriRoundQueriesAccept`, whose existential opening data are checked by the existing `OpenedFriQuery`. `round_resolves` retains each accepted `left`, `right`, `next` value and the exact fold equation. Under the local absence of double openings, those values agree with the resolved words at all three positions. Only their ideal equality paths become `Unit`. Malicious raw opening data can depend on the actual query batch; the proof does not assume an honest opening algorithm.

[DERIVED] `TerminalAccepts` requires a low-degree evaluation word with every position attributed to the terminal root. Although its word is existential, it cannot create hidden query dependence in the good branch: absence of double openings forces all attributed words to equal the one canonical root-resolved word. `terminal_resolves` proves that equality position by position, then transfers existing Reed–Solomon membership. `sound_reduction` splits on `BadRoots` and combines these two lemmas; it takes no acceptance-to-ideal implication as a premise.

[SOURCE/DERIVED] `OpeningResolution.transparent` (lines 71–80) extends the raw root type by an explicit word branch. Ordinary left roots with `some path` preserve the original verifier, and ordinary roots with no path reject. Right roots verify symbol equality with their revealed word. `transparent_terminal` proves attribution equivalent to that word's Reed–Solomon membership; `transparent_no_double` rules out a collision contribution from this branch. Therefore no final Merkle root is silently required. This is an evaluation-word model of a revealed terminal polynomial, not yet a proved decoder from p3's coefficient bytes to that word.

[DERIVED] Transparent roots are available at every level in the generic extension. The theorem is correspondingly more general; it does not force a runtime to use a particular left/right pattern. An execution adapter must map ordinary commitment rounds to left roots and the observed final polynomial to the right-root evaluation word, preserving the source degree and query equations.

## Probability transfer and collision boundary

[SOURCE/DERIVED] `BadRoots` is `∃ n ≤ m, DoubleOpening(S n, rootAt st r n)`. It depends on the challenge execution and fixed scheme/strategy, not on the query seed. The event inclusion from `sound_reduction`, a union bound and the existing finite-product marginal lemma give `coherent_probability_reduction` without a query-count multiplier on the bad term. The challenge tuple and coherent-query seed are uniform independent components; the query indices are the existing modulo projections with replacement.

[SOURCE/DERIVED] `coherent_sound` feeds the resolved transcript directly into `friAdaptive_coherent_sampled_sound`, retaining its radius/gap/fold and initial-farness premises. `fullUD_coherent_sound` and `babyBear_coherent_sound` directly invoke the frozen full-UD sampling heads; they introduce no replacement RS, folding, probability or numerical-budget semantics. The BabyBear head's additional term remains explicit. Exact position binding makes it zero in the corresponding specialization; computational collision resistance does not automatically instantiate this universal logical binding premise.

[DERIVED — critical limitation] The resolver's second opening is chosen from all accepted paths at that root. It need not be in the supplied proof, a previous query answer, or any efficient execution's output. `DoubleOpening` can hold even if the observed transcript contains one accepted value and no conflict. The existing `BinaryMerkle.accepted_different_values_imply_collision` correctly gives a deterministic leaf-or-node collision implication when both paths are supplied. Combining that implication with existential choice gives a semantic collision existence result, not an efficient algorithm that finds those paths or a standard collision-game probability bound. Fixed scheme/hash parameters and universal path existence may make this term much larger than an efficient attack advantage.

[OPEN] Pricing `Pr[BadRoots]` requires a separately justified efficient extraction/reachable-transcript game and its resource accounting, or another suitable soundness reduction. This audit assigns no collision bits, no extraction time bound and no Fiat–Shamir reduction to the package. The README and module comments explicitly maintain this distinction; the audit does not import stronger deployment readings from older binding-interface comments.

## Witnesses and bounded independent checks

[SOURCE/DERIVED] The Lean witnesses reuse the actual existing F5 multiplicative tower `{1,2,3,4} → {1,4}`, with section roots `1,2`. The initial tag-`true` root contains the evaluations of `X`; folding yields the challenge-valued constant terminal word. Raw acceptance holds for every challenge and every query batch, including positive counts. Proved binding eliminates `BadRoots`, and the reduction reaches existing ideal acceptance. Separate theorems refute a fixed final word and a level-zero word that tracks a future challenge. The permissive scheme inhabits an actual double opening.

[DERIVED — nonvacuity boundary] This is a nonvacuous witness for the resolver and raw-to-ideal acceptance reduction. Its initial `X` word is a codeword, so it does not inhabit the farness premise of the numerical soundness head. The package explicitly leaves the 19-round BabyBear tower/farness realization separate. No claim that its F5 witness discharges all BabyBear premises is accepted.

[EXECUTED] The independent finite check exhausts all 16 accepted-value relations on an extra arbitrary root with two positions and two values, and all 25 permitted canonical choices, verifying 60 accepted-value implications. This includes empty/unopenable positions and conflicts. Such an extra root can be adjoined to an ideal complete scheme without weakening completeness. The check also verifies 35 F5 challenge/query batches of lengths zero, one and two for the source witness.

[EXECUTED] An additional F5 example uses the off-image word `X^2=(1,4,4,1)`, whose exact distance to every affine codeword is at least `1/2`, hence greater than `2/5`. A prefix-selected constant terminal word accepts exactly half of the one-query executions. If one incorrectly allows that terminal word to depend on the sampled query, a suitable constant accepts all executions. This is a finite timing falsifier, not a 19-round tower or transition-premise proof. A separate two-path finite relation demonstrates semantic double opening despite a one-opening observed transcript; it does not claim computational hardness.

## Actual p3 source comparison

[SOURCE] The pinned active Cargo patch selects `/Users/ember/dev/breadstuffs/vendor/plonky3-fri-82cfad73`. In its `src/prover.rs:218–233`, each round commits and observes the current matrix root, performs commitment PoW, samples the fold challenge, then folds. Later roots can therefore depend on prior fold challenges. The final coefficient vector is observed at line 257; query PoW and query sampling occur afterward through lines 97–111. In `src/verifier.rs:213–238`, the verifier replays each root/PoW/challenge step, checks the final coefficient-vector length and observes the vector. It samples queries at line 268 and compares the carried fold with a Horner evaluation of the final polynomial at lines 319–325. There is no terminal Merkle-root operation in these inspected paths. The source hashes match `source-evidence.json`.

[DERIVED] This supports the prefix/terminal timing comparison, not execution equivalence. Remaining concrete mappings include variable folding arity, bit-reversed domains and index shifts, MMCS row authentication, extra query-index bits, coefficient/evaluation conversion, and challenger/PoW/Fiat–Shamir behavior. In addition, the active prover's lines 238–245 can inject a next-height input scaled by `beta^arity` after a fold. The pure binary fold equality is not an equivalence to that multi-input batching branch without an additional adapter/proof. These are precise limits on applying the finite theorem to this source, not defects in its stated abstract event inclusion.

[OPEN] The package does not derive initial FRI farness from a PCS/IOP relation, model actual transcript hashing/grinding as independent uniform randomness, provide efficient collision extraction, or prove full Rust verifier acceptance implies its raw event. No frozen source, companion tree or shared ledger was changed; no Lean/crypto/Rust run, private-file access or external search was performed by this audit.
