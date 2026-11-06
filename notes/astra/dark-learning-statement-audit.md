# Dark-learning statement audit — 2026-11-06 task

[READ] Scope: every theorem-shaped construction C1–C23 (including subcases), every distinct §5 target, and F12's envelope premise in `docs/DARK-LEARNING-PROGRAM.md` (DP below), `notes/dark-learning-foundations-critique.md` (F below), and `notes/dark-learning-codex-synthesis.md`, read in full. Duplicate appearances are cross-references, not extra audited statements. The five top-level properties P1–P5 map to DL10/DL35, DL01/DL02, DL27, DL18, and DL14. Numerical cost estimates, literature novelty and performance comparisons are outside this statement inventory.

[READ] Source snapshot: zkml-research `439da79ca95432ee5f428bb6b77c6d3b8347453d`; minidregg `c4ecabe0fad1c8b9eb32a6b3cc2340f689078f55`; breadstuffs `22fad151e9f118e3aa001a823e075918ffa139e8`. All companion trees were read-only. Paths below are relative to their named repository. No search queries or PDF downloads were used.

[INFERRED] **37 distinct statement obligations audited: 9 concrete defects or stale contradictory headlines, 9 underspecified targets needing explicit contracts, 1 deployment-realization gap, and 18 fine conditional targets.** Only the first category is counted as defects. “Fine” is neither a completed proof nor a deployed cryptographic instantiation. A defect is counted once per inventory row, even if several premises are missing. Material defects or scope gaps surviving yesterday's corrections include: step-proof bisection; public-coefficient expiry; sampled “exact” unlearning; zero-error proof gates; rejection-channel privacy; the gap from encoding simulation to physical execution prohibition; epoch-key security versus semantic historical-state secrecy; and the signed-decoder mismatch despite an already existing unsigned no-wrap theorem. Later-state leakage under C22 is a scope boundary, not a counterexample to cryptographic retirement. Missing formal signatures alone are not counted as defects.

## Inventory and verdicts

[INFERRED] Table verdicts refer to the current revised prose, not the withdrawn first drafts. Every defective row has its replacement below.

| ID | source / target | verdict | deciding reason |
|---|---|---|---|
| DL01 | DP:127–151 C1 encrypted step | fine conditional target | The prose already requires factors produced by forward/backward; preserve that clause and per-step no-wrap invariants. |
| DL02 | DP:155–187 C2 `displacement_bound`; §5 duplicate | underspecified target | Fill positive q, stopping convention and conditional-vs-global computational failure accounting; core 2B/q claim is sound. |
| DL03 | DP:166–168; F7:213–215 `bisect_localizes` | defect: false | Local validity is not monotone; cancelling bad steps can restore an honest endpoint. |
| DL04 | DP:191–212 C3 / F9 merge decider | underspecified target | Make merge arithmetic, complete state, all carried witnesses and fresh restart explicit. |
| DL05 | DP:217–240 C4 / F4 append-only noise | defect: too strong F4 formula | Missing base term, two-product composition, message magnitudes and relin noise. |
| DL06 | DP:244–258 C5 expert minimum | underspecified target | Minimum is over a nonempty exhaustive corruption cover and actual conditional probabilities. |
| DL07 | DP:262–274 C6 all-reduce | fine for field/ciphertext arithmetic | No range check is needed for modular addition; an integer-decryption claim would need a separate no-wrap bridge. |
| DL08 | DP:278–309 C7 conversion / segment sampling | fine conditional target | Revised text includes conversion semantics, all state, coverage and independence qualification. |
| DL09 | DP:313–316 C8 zero decryption failure | defect: stale zero-error headline | The first C8 target says probability 0; the later corrected target rightly includes proof/binding errors. |
| DL10 | DP:336–357 C8 restricted IND-CPA-D | underspecified target | Equal outputs alone do not specify admission/rejection and partial-share leakage; define the game. |
| DL11 | DP:363–384 C9 single-prime target | fine narrowed target | Removing limb indexing removes that quantifier swap, not content binding or rounding. |
| DL12 | DP:397–403 C10a exact unlearning | defect: sampled exactness | C2 as the allowed retraining certificate permits a wrong transition with positive probability. |
| DL13 | DP:404–410 C10b generic exact expiry | defect: false | Public coefficients permit propagation of old state; simple subtraction need not equal retraining. |
| DL14 | DP:417–430 C11 welded absence | realization gap; target fine | Proposed content-bound absence is valid; existing word-free DFA/lane-0 weld does not instantiate it. |
| DL15 | DP:434–441 C12a RL provenance | fine conditional target | Source pins sampler/reward dependencies; retain the full prescribed update and distinguish C2 receipts. |
| DL16 | DP:442–446 C12b eval DAG | underspecified target | Specify complete covered ancestry versus a checkpoint-relative path, and receipt type on edges. |
| DL17 | DP:459–462 C13 no unauthorized service | fine conditional security target | Revised scope excludes local FHE evaluation; formal game must charge cryptographic errors. |
| DL18 | DP:463–466 C13 single accepted timeline | fine conditional safety target | Honest intersection plus durable anti-equivocation proves compatible accepted prefixes, not liveness. |
| DL19 | DP:478–499 C14 seeded ZO | underspecified target | Make finite-difference denominator, integer rounding and two randomness stages explicit. |
| DL20 | DP:504–515 C15 MPC custody | defect: structural P3 overclaim | MPC privacy alone does not forbid computation deducible from authorized outputs. |
| DL21 | DP:519–539 C16 folding | underspecified target | Digit opening, ciphertext reconstruction, accumulation validity and model semantics need a common relation. |
| DL22 | DP:543–545 C17a TEE leg | fine conditional conjunction | Adding an attestation leg does not improve epsilon without a joint failure model. |
| DL23 | DP:546–550 C17b DP step | underspecified target | Define actual rounded noise distribution, release view, adjacency and adaptive composition budget. |
| DL24 | DP:556–568 C18 statistics deletion | fine conditional target | Active multiset and deterministic solver/invertibility are explicitly named. |
| DL25 | DP:572–581 C19 projected gradient | fine conditional target | Fixed U,V plus prescribed rounding defines a reduced learner; utility is separate. |
| DL26 | DP:585–595 C20 activation | fine as proof-object gate safety | No activation without a verified proof object can be exact; no false active model is a different probabilistic theorem. |
| DL27 | DP:599–608 C21 instance-bound encoding | defect: P3 scope overclaim | Simulation supports authorized-output leakage; it does not establish the advertised physical execution prohibition. |
| DL28 | DP:612–621 C22 epoch custody | fine conditional epoch-key target | Later-state leakage limits semantic historical secrecy but does not refute retired-key security. |
| DL29 | DP:625–635 C23 one-step contraction | fine conditional target | Use the same prescribed map, full state, and explicit nonnegative contraction constant. |
| DL30 | DP:625–635 C23 horizon-independent consequence | defect: unqualified horizon bound | Continuing rounding needs a uniform ceiling and C2 only bounds stopped/pre-alarm injection. |
| DL31 | DP:641 / F1:49–57 no-wrap iteration | defect: decoder mismatch / stale omission claim | Noise.lean:490 already has mi<t; symmetric range does not make unsigned decode return negatives. |
| DL32 | DP:643 / F4:141–150 `stepRR_noise_le` | fine open target | Ring multiplication bound includes N, scales, rounding and relin; implementation refinement remains open. |
| DL33 | DP:651 `BFVScaleLiftRefinement` | fine integer target | Quotient/remainder is over integers with exact lifted convolution, not mod Q. |
| DL34 | DP:652 / F2:89–95 paired derivative lookup | fine target | Address is the same input with fixed derivative and exceptional-input convention. |
| DL35 | DP:653 / F14:298–311 `F_dark` simulation | underspecified target | Define leakage, corruption, abort, erasure and public outputs before proving simulation. |
| DL36 | DP:654 / F15:313–325 reference learner refinement | fine target | Full-state simulation with trace/randomness alignment is the right theorem. |
| DL37 | F12:270–279 product-norm envelope | fine conservative target | Cap actual product/update, not a factor or lower spectral estimate. |

## Syntax and quantification convention

[INFERRED] Code blocks are **Lean 4 theorem signatures**, with proof bodies intentionally omitted: they are statements to implement, not `axiom` declarations, compiled proofs, or placeholder `sorry`s. Schematic abstract types/relations are explicit parameters or named interface obligations described beside the signature; they must be given executable definitions before an implementation claim. `Pr` always means probability in the named, fixed finite game (never an arbitrary unconstrained real-valued function); `adv` is its distinguishability advantage with a fixed normalization. Error terms bound the whole named experiment unless explicitly marked conditional. No existential “some epsilon” may replace the stated budget. A theorem receiving its whole conclusion as a premise would be tautological; the lower-level obligations below instead name arithmetic identities, transition rules, extraction/refinement or simulator interfaces whose realization is separately open.

### DL01 — complete encrypted transition

[READ] Current prose correctly includes “factors the step's forward/backward produced”. This is a fine conditional specification, not a source defect. Omitting that clause during formalization would recreate the error already exposed by minidregg `Selvage/Rank1GradientCheck.lean:368` (`rank1_blind_to_the_error`).

```lean
-- Faithful expansion: IntLearner and Witness hold ALL optimizer/scale/coin state.
theorem encrypted_step_refines (L : IntLearner) (s : PublicStep) (w : StepWitness)
    (henc : CiphertextTraceValid s w) (hlift : ExactIntegerLifts s w)
    (hnoise : AllDecryptMargins s w) (hforward : ForwardBackward L s w)
    (hupdate : IntegerUpdate L s w) (hbind : OpensAllNamedBoundaries s w) :
    DecodedTransition s w = L.step (DecodedPrestate s w) (DecodedBatch s w)
      (StepCoins s w)
```

[INFERRED] Witness: one-dimensional integer learner with identity activation, fixed batch, zero bounded noise and correctly committed trace. Falsifier: retain valid outer-product factors but choose δ unrelated to the declared loss. `rankK_sound` only rejects a wrong product of the supplied factors. A cryptographic acceptance theorem additionally bounds the chance that extraction of such `w` fails; it cannot simply conclude this equality from a Boolean verifier. The range invariant must be re-established for every evolving state, not inherited forever from the initial weight width: see the independent counts-audit lane's valid 4-bit-factor update that increases a weight beyond its originally priced 4-bit bound. Per-step `ExactIntegerLifts` and `AllDecryptMargins` must use the actual updated operand ranges; fresh encryption resets noise, not plaintext magnitude.

### DL02 — displacement, conditional detection, and the bad world

[READ] `Selvage/AuditSampling.lean:196–265` places corruption before the current coin; `:585–619` requires `0<q`; `:495–505` counts the corrupt step that **raises** the alarm. `:1036–1041` explicitly leaves semantic-corruption to δ-farness transport open. The repaired target below measures *injected* displacement up to and including that step, at each finite horizon.

```lean
noncomputable def injected (R : Round Ω) (delta honest : List Ω → V) : List Ω → ℝ
  | [] => 0
  | _ :: h => if R.stopped h then injected R delta honest h
    else injected R delta honest h + ‖delta h - honest h‖

theorem displacement_bound [Fintype Ω] [Nonempty Ω] [NormedAddCommGroup V]
    (R : Round Ω) (delta honest : List Ω → V) (B q : ℝ)
    (hactual : ∀ h, ‖delta h‖ ≤ B) (hhonest : ∀ h, ‖honest h‖ ≤ B)
    (hcoverage : ∀ h, R.corrupt h = false → delta h = honest h)
    (hq : 0 < q)
    (hdetect : ∀ h, R.stopped h = false → R.corrupt h = true →
      q ≤ uniformProb Ω (fun w => R.alarms h w)) (n : ℕ) :
    expOver Ω n (injected R delta honest) [] ≤ 2 * B / q
```

[INFERRED] The exact `hdetect` is implied by DetectionLegs with **per-history** `BindLeg`, not by ordinary global computational binding. If a hidden setup bit selects an insecure commitment with probability ε, observing that setup can leave a reachable history with binding failure probability 1. An unconditional bound ε says nothing like `∀h, Pr[bad|h]≤ε`.

[INFERRED] Use either a resource-bounded continuation binding assumption strong enough for every relevant history, or a whole-game coupling to an ideal bounded process. For the latter a finite horizon and an unconditional damage ceiling are necessary:

```lean
theorem displacement_bad_world (realLoss idealLoss : Ω → ℝ)
    (bad : Ω → Prop) (M eps B q : ℝ)
    (hM : 0 ≤ M) (hq : 0 < q)
    (hgap : ∀ w, realLoss w ≤ idealLoss w + if bad w then M else 0)
    (hbad : Pr bad ≤ eps) (hideal : E idealLoss ≤ 2 * B / q) :
    E realLoss ≤ 2 * B / q + M * eps
```

[INFERRED] Here `E` and `Pr` are expectation/probability under the **same explicit coupling**. `eps` may include the full-run envelope and binding reduction failures; it is not inserted back into a conditional q. Do not condition on the future “no proof ever fails” event and reuse unchanged beacon probabilities. If only a per-step damage ceiling D is universal, take M=nD. Without a ceiling, loss `M/ε` on a rare bad event defeats any fixed additive error bound.

[INFERRED] Nonvacuity: `AuditWitness.round` has q=1/2; use δ=1, honest=−1, B=1, producing the bound 4. Honest update is from the actual pre-state. Small semantic deviations require `hcoverage` to be false only where the checker detects them, or an extra bounded residual per step; δ-far soundness alone does not do this.

### DL03 — bisection needs prefix validity, not isolated steps

```lean
-- Old claim shape: false without a monotone dispute predicate.
theorem bisect_localizes_old (T : ℕ) (committed : ∀ t ≤ T, HasBoundary t)
    (alarm : ∃ t < T, ¬ StepValid t) :
    FindsFirstBadWithStepQueries (Nat.clog 2 T)
-- Repair target:
theorem bisect_localizes (T : ℕ) (hT : 0 < T)
    (prefix : ℕ → Bool)
    (hspec : ∀ k ≤ T, prefix k = true ↔ ∀ i < k, StepValid i)
    (hbad : prefix T = false) (hanswers : AuthenticatedPrefixAnswers prefix) :
    ∃ i < T, (∀ j < i, StepValid j) ∧ ¬ StepValid i ∧
      PrefixQueryCost i ≤ Nat.clog 2 T
```

[INFERRED] Each queried prefix requires a proof/check of **all transitions** in that prefix, including fixed initial state; a bare endpoint equality is insufficient. Those are not `⌈log₂T⌉` local step proofs. Falsifier: honest identity map, committed states `0,1,0`; both updates are corrupt, final state is honest. More generally a local validity bit vector can contain a unique bad bit at any position, so worst-case first-bad search with local queries needs linear queries. Witness: prefix true through k and false afterward, authenticated prefix proofs. Charge prefix-proof generation separately.

### DL04 — merge and restart semantics

```lean
theorem merge_discharges_carried_witness (epoch : Epoch) (a : Accumulator)
    (ws : CarriedWitnesses epoch) (m : MergeStatement)
    (hdec : DeciderAccepts a ws) (hchain : CarriesExactEpoch a epoch ws)
    (hmerge : MergeRelation epoch ws m)
    (hroot : FreshCommitOpens m.newRoot m.mergedState)
    (hrestart : RestartUses m.newRoot m.nextAccumulator) :
    EpochValid epoch ∧ ModelAt m.newRoot = EndModel epoch ∧
      InitialState m.nextAccumulator = EndModel epoch
```

[INFERRED] `MergeRelation` must tie the full optimizer state, base, factors and exact integer rounding; a decider for opening claims alone cannot discharge training validity. Witness: empty factor epoch followed by identity merge and correctly restarted accumulator. Falsifier: valid openings plus replacement of the recommitted model by zero. Computational roots add extraction/binding errors over *all* merges; a merge does not reset accumulated failure probability.

### DL05 — append-only noise is a sum of complete term bounds

```lean
-- F4's old numeric shortcut (not justified for the described depth-two pass):
theorem append_noise_old : OutputNoise ≤ T * N * (2 * Bfresh * t)
-- Repair target; termBound includes both products, input message magnitudes,
-- both rounding operations, key-switch noise, and ring expansion at each product.
theorem appendOnly_noise_history_free
    (hdecomp : outputError = baseError + ∑ s : Fin T, termError s)
    (hbase : ‖baseError‖ ≤ Ebase)
    (hterm : ∀ s, ‖termError s‖ ≤ termBound s) :
    ‖outputError‖ ≤ Ebase + ∑ s : Fin T, termBound s
```

[READ] `Bfv/Mul.lean:165–190` contains `M₁B₂+M₂B₁`, a quadratic/residue term, rounding `+1`, and `Bks`; freshness alone fixes none of the message magnitudes. `Bfv/Ring.lean:269–326` establishes expansion N and its tightness. [INFERRED] Witness: zero errors and zero noise, any finite history. Falsifier to old numeric form: T=0 with nonzero base noise; even for T>0, unconstrained relin noise is unbounded. Per-term bounds may be uniform, yielding `Ebase+T·Eterm`, but Eterm must be derived for the **two-product** evaluation schedule. No cryptographic crossing-reset theorem is supplied by this triangle inequality.

### DL06 — expert sampling

```lean
theorem stratified_detection [Nonempty Expert]
    (covers : History → Expert → Prop) (qE : Expert → ℝ)
    (hcover : ∀ h, Corrupt h → ∃ e, covers h e)
    (hlocal : ∀ h e, covers h e → qE e ≤ PrAlarm h)
    (hq : ∀ e, qmin ≤ qE e) :
    ∀ h, Corrupt h → qmin ≤ PrAlarm h
```

[INFERRED] Witness: one expert, all corrupt actions covered, honest random sampler. Falsifier: an unmodeled router/optimizer mutation is corrupt but in no expert stratum. `p_e` must be the actual probability of auditing the implicated object conditional on its corruption, not its nominal frequency among all expert draws. Stratification is sufficient, not logically necessary; auditing every expert in a selected step also has the advertised floor.

### DL07 — valid modular collective; separate integer lift

```lean
theorem allReduce_field_sound (hfixed : FixedBeforeChallenge shardRoots outputRoot)
    (hsz : CheckPolynomialNonzero inputShards output) :
    Pr (fun r => CommonPointAccepts inputShards output r) ≤ degree / fieldCard

theorem allReduce_integer_exact (xs : Fin nodes → Fin width → ℤ)
    (out : Fin width → ℤ) (p : ℤ) (hp : 0 < p)
    (hmod : ∀ j, out j % p = (∑ i, xs i j) % p)
    (hlift : ∀ j, |out j - ∑ i, xs i j| < p) :
    out = fun j => ∑ i, xs i j
```

[INFERRED] The source modular/ciphertext collective is fine: range checks are not required to prove modular addition. The added integer corollary is a distinct consumer obligation, inhabited by honest summed shards with ordinary range bounds. Falsifier to that stronger claim without a lift: out=sum+p passes every field equality and is a wrong integer. Computational commitment errors and random-evaluation error remain even when no sumcheck rounds are required. Sender/receiver openings must share message IDs and occurrence indices, not only reusable tensor content hashes.

### DL08 — conversion and coverage (fine after revision)

```lean
theorem conversion_sound (cIn cOut : Ct) (sIn sOut : Shares)
    (h : ProvedConversion cIn sIn sOut cOut transition) :
    Decode cIn = Reconstruct sIn ∧
    Reconstruct sOut = transition (Reconstruct sIn) ∧
    Decode cOut = Reconstruct sOut

theorem covered_segments_detection
    (hcover : ∀ h, Corrupt h → ∃ j, BadSegment h j)
    (hlocal : ∀ h j, BadSegment h j → qj j ≤ PrAlarm h)
    (hfloor : ∀ j, qmin ≤ qj j) :
    ∀ h, Corrupt h → qmin ≤ PrAlarm h
```

[INFERRED] `ProvedConversion` denotes arithmetic validity, not Boolean acceptance. Wire decoding, signed representations, key epochs and state metadata are part of the fixed conversion definition. Witness: plaintext identity conversion with correct fresh encryption. An actual proof-system acceptance theorem pays its errors. The independent product-of-misses bound is available only with the stated conditional independence; the min bound needs none.

### DL09–DL10 — proof gates and the restricted game

```lean
-- Old target mistakes proof acceptance for truth:
theorem gate_failure_zero_old : Pr (fun w => GateAccepts w ∧ DecFails w) = 0
-- Arithmetic repair, exact within the ideal certified relation:
theorem certified_decrypts (q : Query)
    (hprov : ExactCertifiedEvaluation q) (hnoise : FullNoiseMargin q)
    (hmsg : PrescribedIntegerNoWrap q) :
    CombineAndDecode q = IdealOutput q
-- Computational corollary:
theorem gate_failure_bound
    (hreduction : GateBadToProofOrBindingOrKeygenBad game)
    (hbudgets : GateGameBudgets game epsProof epsBind epsKeygen) :
    Pr (fun w => GateAccepts w ∧ DecFails w) ≤ epsProof + epsBind + epsKeygen
```

[INFERRED] FullNoiseMargin includes *combined* smudging/share coefficients, not only pre-release evaluation noise. Noise witnesses must describe the prescribed plaintext and exact derivation. Witness: honest zero-noise evaluation under a gate checked on every release. Falsifier to zero failure: a soundness-error event in which a forged proof admits an over-margin ciphertext.

```lean
structure PairedQuery where
  left right : IdealQuery
  samePublic : PublicMetadata left = PublicMetadata right
  sameAdmit : Allowed left = Allowed right
  sameRelease : Allowed left = true → IdealOutput left = IdealOutput right
  sameLeakage : IdealLeakage left = IdealLeakage right

theorem restricted_ind_cpa_d
    (hkeys : CPAWithIssuedEvaluationKeys scheme epsCPA)
    (hgate : WholeRunGateSound protocol epsProof epsBind epsKeygen)
    (hmpc : AdaptiveThresholdSimulation protocol ideal epsMPC)
    (hshares : ConditionalTranscriptHybrids protocol ideal epsTranscript)
    (hqueries : AdmissibleStatefulAdversary A PairedQuery)
    (hbudget : RealQueryCount A ≤ K) :
    DistinguishingAdvantage (RestrictedRealGame protocol A)
      (RestrictedIdealGame ideal A) ≤
      epsCPA + epsProof + epsBind + epsKeygen + epsMPC +
        ∑ i : Fin K, epsTranscript i
```

[INFERRED] All releases, rejections, scheduling/timing included in the adversary's modeled view must be covered by `sameLeakage` and the simulator. Novel falsifier: both worlds promise equal released output 0, but policy admits only when a hidden weight bit is 0. Reject/accept distinguishes perfectly while equal-output decryption holds vacuously for the rejected world. Require equal admissibility, or explicitly allow and account for that policy leakage. Proof witnesses must not be used as an unexplained decryption oracle by the CPA reduction; adaptive simulation/extraction is part of `hgate`/`hmpc`, with its actual reduction resources.

[READ] `Bfv/Smudging.lean:442–469` packages real-valued distances and assumed per-step hybrid bounds; no protocol inhabitation follows from `TranscriptHybridLedger.sound`. [INFERRED] A trivial constant-output protocol supplies a nonempty toy premise witness. A useful reactive BFV threshold instance remains [OPEN]. This is a target under a restricted oracle, not unrestricted IND-CPA-D or model secrecy against allowed identity release. Global error terms are aggregated over the whole run; per-query errors must first be summed or reduced.

### DL11 — single-prime provenance (fine in the narrowed scope)

```lean
theorem singleton_limb_source
    (Rel : Source → Fin 1 → Prop)
    (h : ∀ i : Fin 1, ∃ src, Rel src i) :
    ∃ src, ∀ i : Fin 1, Rel src i
```

[INFERRED] Witness any genuine single source. This only removes the cross-limb quantifier swap. Two different ciphertext handles at the sole limb, incorrect lifted multiplication, wrong public inputs or weak commitment roots remain possible. C9 now explicitly retains Hole B; DL33 is still required.

### DL12–DL13 — exact deletion

```lean
theorem shard_retraining_exact (D : Dataset) (id : RecordId)
    (hpartition : FixedIndependentShardPartition D)
    (htrain : EveryRetainedShardExactlyTrained D)
    (hretrain : AffectedShardExactlyRetrained (EraseRecordId D id))
    (hshared : InitialAndSharedStateIndependentOf D id)
    (hcompose : FixedAdditiveComposition) :
    ReassembledAfterDeletion D id = ReferenceLearner (EraseRecordId D id)
```

[INFERRED] A C2 receipt alone cannot inhabit `hretrain`; it proves a loss/detection guarantee, not that the retrained model is exactly the reference. Either require a full epoch proof (C20), or replace equality by the correctly stopped expectation bound and residual assumptions. Fix seeds/rounding for equality; randomized retraining instead needs a specified distributional comparator. Deletion is by record ID/multiplicity, not ambiguous value subtraction. Witness: independent deterministic one-record shards. Falsifier: one forged retraining step that escapes sampling.

```lean
-- Old public-coefficient generalization is false:
theorem expiry_old : PublicCoefficientLearner L →
    RemoveOriginalContribution (L.run D) id = L.run (EraseRecordId D id)
-- Useful additive-statistics repair:
theorem statistics_expiry [DecidableEq Record] [AddCommGroup Stat]
    (contrib : Record → Stat) (D : Multiset Record)
    (d : Record) (hd : d ∈ D) :
    (D.map contrib).sum - contrib d = ((D.erase d).map contrib).sum
```

[INFERRED] Falsifier over ℤ, all coefficients public: `s←2s+d`, s₀=0, teachings (1,0). Final state=2; subtract original contribution 1 gives 1; retraining on (0) gives 0. A general linear dynamical learner can remove the **transported** contribution `A_last⋯A_after d`, but that is a different theorem and may require stored transition history. Nonlinear prox/rounding breaks even that simple transport. The core-only witness is kept in `dark-learning/CoreCounterexamples.lean`.

### DL14 — valid content-bound absence target; realization gap

```lean
theorem batch_policy_valid (stmt : TrainingPolicyStatement) (w : PolicyWitness)
    (hdata : OpensBatch stmt.batchRoot w.batch)
    (hused : StepConsumesExactly stmt.step w.batch)
    (hcorpus : EveryRecordMember stmt.corpusRoot w.batch)
    (hlanguage : DfaRunOnExactBytes stmt.patternSemantics w.batch w.trace)
    (habsence : RejectsContainsPattern w.trace)
    (hencoding : CanonicalTokenizerAndByteEncoding stmt w) :
    ∀ record ∈ w.batch, MemberOfCorpus stmt.corpusRoot record ∧
      ¬ ContainsExcludedPattern stmt.patternSemantics record
```

[INFERRED] The source intends the correct shared-content relation. Its unfilled realization must make substring/whole-word language explicit, cover complete bytes with lengths, and use all digest lanes in the commitment relation. A cryptographic version concludes a bad-accept probability. [READ] Prior critique identifies the cited `AttestedAutomatonWeld8` as lane-0 only and the DFA statement as word-free; claiming its existing theorem fills `hlanguage` or `hused` is invalid. Witness empty exclusion set and an honestly opened finite batch. Falsifier: proof for safe bytes B and training on B′; content hash equality cannot be assumed perfect for a compressing hash. This proves batch-level absence; complete history requires DL16's ancestry coverage.

### DL15–DL16 — RL and evaluation lineage

```lean
theorem rl_step_refines (spec : RLSpec) (tr : RLTrace)
    (hpin : PinsAllDependencies spec tr)
    (hsampler : SamplerRefinesWithCommittedPolicy spec tr)
    (hrandom : NoSeedSelectionAfterSeeingRollouts spec tr)
    (hreward : RewardExecutionRefines spec tr)
    (hupdate : FullUpdateRelation spec tr) :
    tr.after = spec.step tr.before tr.batch tr.coins

theorem eval_lineage_valid (g : ProvenanceDAG) (r : EvalReceipt)
    (hclosure : CompleteAncestryIncludingInitialization g r.model)
    (hedges : AllEdgesFullyValid g)
    (habsence : AllTrainingInputsExclude g r.evalSet)
    (heval : EvalExecutionRefines r)
    (hidentity : FullInferenceIdentityPinned r) :
    r.result = ReferenceEval r.model r.evalSet r.harness ∧
      NoDeclaredEvalItemInCompleteTrainingLineage g r.model
```

[INFERRED] C12a is fine as the prescribed-step claim: the source already pins sampler and reward dependencies and supplies an unpinned-state falsifier. Its formal expansion includes tokenizer, optimizer, policy version, reward program/state, seed/counter and rounding. For an audit edge, carry its error/loss judgment instead of `AllEdgesFullyValid`. A public checkpoint of unknown ancestry cannot witness `hclosure`; the truthful claim starts at that checkpoint and names the residual. Witness: genesis empty training set, one fully verified update, deterministic reward/eval harness. Falsifier: omit a pretraining checkpoint containing the eval set, or select among many beacon seeds while each chosen rollout is individually reproducible. For finite corpora exact-item absence is not absence of paraphrases or all contamination.

### DL17–DL18 — service gates and one accepted timeline

```lean
theorem noUnauthorizedService
    (hthreshold : ThresholdSecurity epsThreshold)
    (hgate : EveryServiceEnforcesGate epsProof epsBind)
    (hconsensus : CanonicalAuthorizationLog epsConsensus) :
    Pr (fun w => ∃ e ∈ ServicesObtained w,
      ¬ AuthorizedAtLinearizationPoint (LogOf w) e) ≤
      epsThreshold + epsProof + epsBind + epsConsensus

theorem SingleTimeline (hinit : ValidGenesis)
    (hintersection : HonestQuorumIntersectionAcrossEpochs)
    (hsign : DurableHonestAntiEquivocation)
    (hauth : AuthenticatedCertificates)
    (hparent : CertificatesBindParentAndEpoch) :
    ∀ c1 c2, AcceptedChain c1 → AcceptedChain c2 →
      c1.IsPrefix c2 ∨ c2.IsPrefix c1
```

[INFERRED] These are fine within their stated assumptions. A cryptographic authentication implementation adds its failure probability; deterministic signature truth is the idealized premise. Witness: one honest durable signer, one chain. Falsifier if `hintersection` is removed: disjoint quorums certify children of the same parent. Neither conclusion is liveness, deletion of local copies, absence of withholding, or proof that a local FHE computation did not occur. Gate authorization must be checked at a serializable state transition, not a stale precheck.

### DL19 — integer seeded ZO

```lean
theorem seeded_zo_step (spec : ZOSpec) (tr : ZOTrace)
    (heps : 0 < spec.epsilonNumerator)
    (hpin : DirectionInputsCommittedBeforeSeed spec tr)
    (hdir : tr.direction = spec.generator tr.directionSeed)
    (hloss : ExactPairedLossEvaluation spec tr)
    (hround : tr.coefficient = spec.roundedDifferenceQuotient tr.lossPlus tr.lossMinus)
    (hupdate : IntegerScaledUpdate spec tr)
    (haudit : CoefficientCommittedBeforeIndependentAudit tr) :
    tr.after = spec.step tr.before tr.batch tr.directionSeed
```

[INFERRED] Witness one-dimensional integer quadratic loss with exact rational denominator and declared rounding. Falsifier: ε=0, or replace division by modular inverse while claiming real finite differences. Random direction does not prevent malicious coefficient selection after seeing it; cap the actual update for DL02. A seed is not a rank factor.

### DL20–DL23 — MPC, folding, attestation and DP

```lean
theorem mpc_custody_simulation
    (hcorrupt : AllowedAdaptiveCorruptions adversary threshold)
    (hprotocol : MaliciousSecureMPC protocol ideal epsMPC)
    (hstate : AuthorizationAndStateBinding protocol)
    (hpre : SecurePreprocessingWithErasure protocol) :
    ∃ sim, DistinguishingAdvantage (RealView protocol adversary)
      (IdealView ideal sim) ≤ epsMPC
```

[INFERRED] DL20 repairs the claim that no single host “runs anything.” An MPC output may reveal W or sufficient queries to reconstruct it. This theorem allows whatever is computable from ideal outputs; P3 needs DL27's narrower confinement game and cannot prohibit physical replay. Witness: ideal private addition of secret-shared constants with a fixed authorized output; useful deployment remains conditional on malicious security and preprocessing.

```lean
theorem folded_ciphertext_epoch_sound
    (hshort : BoundedDigits digits) (hreconstruct : ReconstructDigits digits = ciphertexts)
    (hfold : CarriedFoldRelation accumulator digits)
    (hdecider : DeciderRelation accumulator digits)
    (hsteps : CiphertextTransitionRelation ciphertexts)
    (hsemantic : CiphertextTransitionsRefineLearner ciphertexts) :
    DecodedFinalState ciphertexts = ReferenceEpoch InitialState Batches Coins
```

[INFERRED] DL21: witness honest finite digit decomposition and identity epoch; zero-absorb or unrelated accumulator/model pair falsifies the old “accumulator IS model” shortcut. Ring shortness and extraction are real obligations; ciphertext coefficients cannot be assumed short, and finite field Schwartz–Zippel cannot be transplanted to a split ring.

```lean
theorem tee_proof_join
    (hshared : BothEvidenceLegsBindSameTypedStatement)
    (hproof : ProofBadEventBound epsProof)
    (hquote : AttestationBadEventBound epsQuote)
    (hbind : JointBindingBadEventBound epsBind) :
    Pr JointFalseAcceptance ≤ epsProof + epsQuote + epsBind
```

[INFERRED] DL22 is fine as a union-bound conjunction with explicit occurrence/validity claims and assumptions. Multiplying errors or claiming improved ε requires a joint attack/independence model not supplied by a TEE. Witness ideal attester reporting an honest fixed execution; residual vendor trust remains.

```lean
theorem dark_step_dp
    (hclip : ExactPerExampleClipping spec)
    (hnoise : NoiseSamplerDistributionRefines spec)
    (hprivacy : ReferenceMechanismDP spec eps delta)
    (hrefine : ReleasedViewRefinesReferenceWithFailure epsRefine)
    (hpolicy : AdaptiveReleaseAccountant budget) :
    DifferentiallyPrivate ReleasedView eps (delta + epsRefine)
```

[INFERRED] DL23: `(eps,delta)` must be instantiated for the actual rounded finite sampler and adjacency relation; a secret seed is neither sufficient nor necessary for distributional DP. Host-observed randomness belongs in ReleasedView. Noise-source rejection/selective abort and extra outputs/partial decryptions can defeat the target. Witness a constant-output mechanism (ε=δ=0), or an actually proved discrete-noise mechanism; naming Box–Muller alone is not a proof.

### DL24–DL26 — statistics, subspace and epoch activation

```lean
theorem statistics_erase [DecidableEq Record] [AddCommGroup Stat]
    (phi : Record → Stat) (D : Multiset Record) (d : Record) (hd : d ∈ D) :
    (D.erase d |>.map phi).sum = (D.map phi).sum - phi d

theorem projected_core_transition (spec : CoreSpec) (tr : CoreTrace)
    (hfixed : tr.U = spec.U ∧ tr.V = spec.V)
    (hgrad : tr.coreGradient = spec.projectedGradient tr.before tr.batch)
    (hround : tr.after = spec.roundedUpdate tr.before tr.coreGradient) :
    tr.after = spec.step tr.before tr.batch
```

[INFERRED] DL24 and DL25 are fine conditional algebra. DL24's released model additionally uses the same deterministic solver; exact field solve needs invertibility as the source already says. Witness nonempty multiset with duplicate records, deleting one occurrence; for DL25 use U=V=[1]. Counterexamples to removed premises: deleting two duplicate occurrences, changing φ, changing U/V, singular system claimed uniquely solved. In a field, formulas prove field results until integer-lift/no-wrap obligations connect them to an integer learner.

```lean
-- Exact gate invariant, matching the source's "no unproved model active":
theorem activation_requires_verified_proof (htransition : ImplementsActivationGate system) :
    ∀ event ∈ system.events, Activates event →
      ∃ proof, VerifyEpoch event.statement proof = true

-- Different semantic-security consumer theorem:
theorem epoch_activation_sound
    (hgate : EveryObservableServiceRequiresActiveRoot)
    (hparent : ActivationBindsCertifiedCurrentParent)
    (hcheck : WholeEpochVerifierSound epsEpoch)
    (hbind : EpochAndServiceBinding epsBind)
    (hconsensus : AtomicActivationConsensus epsConsensus) :
    Pr (fun w => ∃ e ∈ ObservableServices w,
      ¬ CertifiedReferenceDescendant (ServedModel e)) ≤
      epsEpoch + epsBind + epsConsensus
```

[INFERRED] DL26 is fine as the exact gate invariant. It is not refuted by probabilistic proof soundness: “proof supplied and verified” is a syntactic property. The additional semantic conclusion that the activated model is actually valid is probabilistic. All release/action paths, including partial decryption, must satisfy `hgate`; sampled training does not. Witness honest full epoch proof followed by atomic activation. Falsifier: a stale-parent proof races with another activation, or an inference route bypasses active-root checking. Correctness of *speculative* private state is not obtained by withholding its outputs.

### DL27 — what C21 can and cannot promise

```lean
-- Privacy alone (necessary, insufficient for the prose P3):
theorem one_instance_view_simulation (hsecure : SecureEncodingProtocol protocol ideal epsSim) :
    ∀ A, AdmissibleHost A → ∃ S,
      ViewAdv (RealView protocol A) (IdealView ideal S) ≤ epsSim

-- Separate authenticity/confinement game:
theorem instance_bound_transition_authenticity
    (henc : AuthenticatedInstanceEncoding protocol epsEnc)
    (hinput : CommittedInputBinding protocol epsInput)
    (hstate : ParentNonceEpochBinding protocol epsState)
    (hgate : CanonicalCustodianRelease protocol epsGate) :
    Pr (fun w => ∃ o ∈ AcceptedDecodings w,
      ¬ MatchesIssuedAuthorizedInstance (IssuedInstances w) o) ≤
      epsEnc + epsInput + epsState + epsGate
```

[INFERRED] `MatchesIssuedAuthorizedInstance` must match **parent state, input, circuit/version, nonce, epoch and output decoding**. Cross-instance label/authentication attacks are excluded by an authenticated composition theorem, not merely by randomized-encoding privacy. The ideal view explicitly includes public metadata and all authorized outputs; computational consequences of those outputs are unavoidable leakage. Witness: one fixed-input one-time encoding with an ideal private custodian; no reusable model handle exported. Useful reactive implementation [OPEN].

[REFUTED: physical P3 from simulation] Copy a valid classical encoding and evaluate it twice; both copies have the same simulatable view and accepted result. Stronger: if an authorized output is W, the simulator can generate the host's later chosen-input computations from W, so view simulation holds while reusable evaluation is available. Even without identity release, a public sufficiently learnable function can be reconstructed from allowed outputs. Thus withdraw “C21 actually delivers P3” unless P3 is renamed **no accepted new transition beyond authorized instances and ideal-output leakage**. Neither cryptography nor this model decides whether duplicate evaluation constitutes experience. This is not a refutation of the usefulness of MPC custody.

### DL28 — valid epoch-key target; historical-state scope boundary

```lean
theorem retired_epoch_key_recovery_bound
    (hbound : PerEpochCorruptionBelowThresholdIncludingRefreshWindows)
    (herase : HonestErasureAndNoRollback)
    (hkeys : IndependentEpochKeyGeneration)
    (hmigrate : ForwardSecurePrivateMigration epsMigrate) :
    RetiredKeyRecoveryAdvantage ≤ epsEpochCrypto + epsMigrate

-- Optional stronger historical-state game, NOT the source's key-retirement claim:
theorem historical_state_secrecy
    (hbound : PerEpochCorruptionBelowThresholdIncludingRefreshWindows)
    (herase : HonestErasureAndNoRollback)
    (hkeys : IndependentEpochKeyGeneration)
    (hmigrate : ForwardSecurePrivateMigration epsMigrate)
    (hrelease : EqualAuthorizedLeakageAcrossChallengeHistories)
    (hlater : EqualPostChallengeStatesAndCorruptionLeakage) :
    HistoricalCiphertextDistinguishingAdvantage ≤ epsEpochCrypto + epsMigrate
```

[INFERRED] The source C22 retires key/decryption authority and a read-all credential; that conditional target is fine. Distinguish it from the stronger semantic historical-state claim in the optional second signature. Later compromise of a current state identical to the historical state reveals it without recovering any retired key. Equal later state/leakage is therefore needed for an historical-state indistinguishability game, or the claim must concern retired key recovery only. Erasure must cover old shares, backups and refresh/migration material; a bound only at each instant misses sequential corruption of enough parties within one refresh interval. Witness independent one-time epochs with erased old keys, constant public outputs and no model-preserving later leakage. This does not protect classical ciphertexts against a future break of the underlying cryptosystem; its security assumptions must be quantum-appropriate if that is the threat model.

### DL29–DL30 — contraction and its actual horizon bound

```lean
theorem contractive_step
    (hcontract : ∀ x y, dist (f t x) (f t y) ≤ rho * dist x y)
    (hactual : dist (actual (t + 1)) (f t (actual t)) ≤ inj t + rnd t)
    (hhonest : honest (t + 1) = f t (honest t)) :
    dist (actual (t + 1)) (honest (t + 1)) ≤
      rho * dist (actual t) (honest t) + inj t + rnd t

theorem contractive_unroll (hrho : 0 ≤ rho)
    (hstep : ∀ t < T, d (t + 1) ≤ rho * d t + err t) :
    d T ≤ rho ^ T * d 0 +
      ∑ t ∈ Finset.range T, rho ^ (T - 1 - t) * err t

theorem contractive_expected_bound (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hcouple : SamePrescribedMapsDataAndCoins)
    (hstop : InjectionStopsAtFirstAlarm)
    (hround : ∀ t, 0 ≤ rnd t ∧ rnd t ≤ RoundingCap)
    (hinject : E TotalInjected ≤ 2 * B / q)
    (hunroll : PathwiseContractiveRecurrence) :
    E (fun w => dist (actual T w) (honest T w)) ≤
      rho ^ T * InitialDistance + 2 * B / q + RoundingCap / (1 - rho)
```

[INFERRED] DL29 is fine for the same function `f t` on both states; if adaptive data selection changes with the altered state, either include that selector in the contractive transition or explicitly couple the comparator to the realized data/coins. “Same dataset distribution” is not pointwise same map. DL30 needs a uniform rounding ceiling (otherwise rounding may grow without bound) and stopped injection: C2 says nothing about arbitrary corruptions continued after the first alarm. Include the DL02 `M·ε` term when applying a computational envelope. Witness f(x)=x/2 on a bounded scalar domain with exact arithmetic; finite quantization may need a nonzero rounding term. This is an upper bound on full state, not a utility theorem.

### DL31 — no-wrap already exists; signed decoding needs a bridge

[READ] breadstuffs `metatheory/Bfv/Noise.lean:490–517`, `iter_decrypts_exact`, already assumes both a noise ceiling and `hmi : (mi:ℤ)=iterMsg S T m i`, `hlt : mi<P.t`. The critique's “nothing here carries a message ledger” is too broad. What is absent is a derived range invariant for the desired signed training iteration, and the signed-decoder refinement.

```lean
-- Unsigned decoder + a symmetric range assumption is not this theorem:
theorem signed_no_wrap_old (hsmall : |intended| < (t : ℝ) / 2) :
    unsignedDecrypt ct = intended
-- Repair target:
theorem iter_decrypts_exact_no_wrap
    (hnoise : IteratedNoiseSafe params S T ct msg)
    (hunsigned : UnsignedDecoderRefinesResidue params ct msg)
    (hcenter : CanonicalCenteredDecoder params centeredDecrypt)
    (hrange : ∀ i, CenteredMessageRange params (iterMsg S T msg i)) :
    ∀ i, centeredDecrypt (iterCt S T ct i) = iterMsg S T msg i
```

[INFERRED] Witness zero messages and safe zero noise, any bounded finite linear trajectory. Falsifier: intended −1, modulus t>2; `|−1|<t/2` but the unsigned residue is t−1. Do not “repair” the existing correct unsigned theorem by claiming it already returns centered integers. Also, the advertised deployed 42-step example has `tauDen=1`, not fractional-learning-rate denominator 16 (`Noise.lean:519–525`); calling that specific example wrapped because “tauDen>1” misidentifies its parameters.

### DL32–DL34 — primitive numerical targets

```lean
theorem stepRR_noise_le
    (hoperand1 : NormInfLE message1 M1 ∧ NormInfLE noise1 B1)
    (hoperand2 : NormInfLE message2 M2 ∧ NormInfLE noise2 B2)
    (hks : NormInfLE keySwitchError Bks)
    (hrefine : RingMultiplyScaleRelinRefinesIntegers ct1 ct2 ctOut) :
    NormInfLE (NoiseRelativeTo ctOut (negaMul message1 message2))
      (RingMultiplyBound N params M1 M2 B1 B2 Bks)

theorem BFVScaleLiftRefinement (Q t z y s : ℤ)
    (hQ : 0 < Q) (hs0 : 0 ≤ s) (hsQ : s < Q)
    (hcert : t * z + Q / 2 = Q * y + s) :
    y = (t * z + Q / 2) / Q

theorem paired_lookup_sound (table : Code → Code × Code) (x y dy : Code)
    (hrow : (y, dy) = table x)
    (hforward : ∀ z, (table z).1 = QuantizedActivation z)
    (hbackward : ∀ z, (table z).2 = SpecifiedDerivative z) :
    y = QuantizedActivation x ∧ dy = SpecifiedDerivative x
```

[INFERRED] All three are fine targets. DL32's `RingMultiplyBound` must be derived from the specified centered integer scale/relinearization operation and explicit N expansion; it is not a free scalar-bound copy. Witness N=1 bounded messages/noises, corresponding to scalar semantics. DL33's `z` must itself be linked to the integer lifted convolution; quotient/remainder alone proves only division of the supplied z. For nearest ties-up with integer numerator and integer positive Q, `(t*z + Q/2)/Q` is the specified rounding; do not use this to assert correctness of an unspecified library's different ties convention. Falsifier mod-Q-only certificate: Q=31,t=4,z=1 vs z=32. DL34 fixes the nondifferentiable point and NaN/infinity conventions or restricts the input domain. Sharing an address but opening different addresses in the two proof legs fails `hrow`.

### DL35–DL37 — ideal functionality, whole-machine refinement and envelope

```lean
theorem dark_ideal_simulation
    (hprotocol : RealizesReactiveIdealFunctionality protocol Fdark eps)
    (hcorrupt : ExplicitAdaptiveCorruptionAndErasureModel adversary)
    (hresources : AdversaryWithinReductionResources adversary) :
    ∃ simulator, ViewAdv (RealExecution protocol adversary)
      (IdealExecution Fdark simulator) ≤ eps

theorem integer_learner_refinement
    (R : ConcreteState → ReferenceState → Prop)
    (hinit : ∀ c r, InitPair c r → R c r)
    (hstep : ∀ c r input coins c', R c r → ConcreteStep c input coins c' →
      ∃ r', ReferenceStep r input coins r' ∧ R c' r' ∧
        PublicEvents c input coins c' = ReferenceEvents r input coins r') :
    EveryConcreteTraceHasMatchingReferenceTrace R

theorem product_envelope
    (hsub : frobenius (A * B) ≤ frobenius A * frobenius B)
    (hcap : frobenius A * frobenius B ≤ cap) :
    frobenius (A * B) ≤ cap
```

[INFERRED] DL35's signature makes the proof obligation visible but is not itself the reduction: a useful implementation must define Fdark's admission/release/abort/rollback/refresh events, allowed public metadata, corrupt-party views, and erasure boundaries, then **construct** `hprotocol`. A trivial simulator premise would be P→P; do not advertise this header as a construction. Witness: ideal protocol implementing Fdark internally gives perfect simulation but no distributed implementation claim. Identity releases are allowed leakage if authorized, never a proof of opacity.

[INFERRED] DL36 is a standard induction target; all components of optimizer state, rounding, clipping, derivative lookup, counters and key epochs must be in R. Silent concrete steps require a stuttering trace relation rather than falsely demanding one concrete instruction per reference training step. Witness identical reference/concrete machine; a real ciphertext implementation needs DL01/DL32/DL33 and custody refinements.

[INFERRED] DL37 is fine: submultiplicativity is independent lower-level mathematics; product-cap suffices and is conservative under gauge. For mutable factors apply it to the **actual delta** `ΔA·B+A·ΔB+ΔA·ΔB`, or sum three certified product bounds. Witness zero update or rank-one unit vectors with cap 1. Falsifier to factor-only cap: A very small and B arbitrarily large. Power iteration only supplies a lower norm bound, already withdrawn in the source.

## Validation and limitations

[EXECUTED] **Concrete repair:** `notes/astra/displacement-bound.patch` adds `Selvage/AuditDisplacement.lean` in namespace `Minidregg.Selvage.AuditDisplacement`. It proves the exact finite-horizon `2B/q` target, its pathwise domination lemma, an inhabited nonzero-damage q=1/2 witness, and a falsifier when the actual envelope is removed. The source carries a consumer-signature check and `#guard_msgs` axiom pins; no `sorry` or new axioms. `git -C /Users/ember/dev/minidregg apply --check /Users/ember/dev/zkml-research/notes/astra/displacement-bound.patch` exited 0; the patch was **not applied**.

[EXECUTED] The pinned v4.35.0 compiler cannot directly import the warm `AuditSampling.olean`: incompatible header (v4.30.0). Instead, `python3 notes/astra/dark-learning/check_displacement_adapter.py` assembled **exact current source fragments** of `Rbr.uniformProb`, the `Depth` counting lemmas, `AuditSampling` through its detection/expectation/sequential/leakage proofs, and `AuditWitness`, followed by the exact proposed module body. This source-fragment elaboration exited **0 on Lean v4.35.0** with all axiom pins matching. No stubs, assumed replacements or new axioms were used. `adapter-source-slices.json` identifies the source fragments and their hashes; `displacement-adapter-check.log` preserves the command/output. Deprecation warnings come from unchanged copied AuditSampling proofs; the helper also has a harmless unused-section-instance warning.

[EXECUTED] Separately, `DisplacementCore.lean` checks the isolated pathwise lemma and nonzero witness against current warm Mathlib; `CoreCounterexamples.lean` checks four exact counterexamples without imports. Both current-pin checks exit 0 with axiom guards. The four core counterexamples have no axioms; the norm and expectation theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

[EXECUTED] Import boundary: the actual minidregg `scripts/check-import-boundary.sh` exited 0, run read-only with `PYTHONDONTWRITEBYTECODE=1`. Parsing the proposed module with that script's own `lean_imports.header_imports` yields only `Selvage.AuditSampling` and `Mathlib.Analysis.Normed.Group.Real`: permitted Selvage roots and no new library edge. Output is `import-boundary-check.log`.

[OPEN] This is **source-fragment proof validation, not a complete current-toolchain minidregg module/integration build**. The cached closure is incompatible; no full Lean build or dependency download was attempted, and no companion file was modified. The integrator should apply the additive patch in its own lane and run the normal per-module check on the designated warm build host. `Displacement.lean` is the earlier audit-namespace candidate; the exact patch source is `dark-learning/source/Selvage/AuditDisplacement.lean`.

[OPEN] Most signatures above are intentionally statement/interface targets, not implementations. The physical/custody games need concrete protocols and proofs. No claimed attack on BFV, MPC or garbling follows from an interface counterexample. The repairs limit the prose to what the stated theorem would establish and preserve the useful construction work.
