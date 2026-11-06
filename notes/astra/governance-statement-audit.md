# Governance and silicon statement audit — 2026-11-06 task

[READ] This audits the working-tree text of:

- **G** = `/Users/ember/dev/degg-research/research/GOVERNANCE-CLAIM-LATTICE.md`, at clean HEAD `15db9784e2043bb170431203f3c63d88625933e2`.
- **S** = `/Users/ember/dev/redregg/designs/SILICON-TO-SEMANTICS-ALIGNMENT-2026-11-05.md`, at clean HEAD `d1540c5c1435ead2c01c92fe6a1cef3cc303c097`.
- The governance foundations critique and governance Codex synthesis at the same degg-research HEAD, read in full. They describe yesterday's defects, not evidence that their replacements work.

[MEASURED] [EXECUTED] `git rev-parse HEAD` and scoped `git status --short -- <files>` supplied these snapshots; both scoped status outputs were empty. The audit's source line numbers refer to those snapshots. No companion-tree files were changed.

[INFERRED] **44 statement contracts audited; 5 definite current defects with repairs, plus 11 qualification/interface obligations.** This count includes every named theorem in S, its replacements where one old theorem split into several obligations, S's unnamed construction-grade obligations (g)–(n), and G's mathematical/receipt claims. It does **not** count each topical governance claim row as a proposed theorem or count the eleven previously identified bad sketches again. The old sketches are explicitly marked false/incomplete in the source; the current prose repairs are the audit target. The table preserves their status so a maintainer cannot mistake an old code block for the recommended statement.

[INFERRED] The most important new correction is that **deduplication by evidence identity is not sound**. Identical bytes can support different predicates whose false-accept events are disjoint. An important interface qualification is that the advertised binding leg does no logical work in the displayed rule until local subjects and their semantic transport to the joint subject are formalized. A wording hazard is that `Pr[accept ∧ false] ≤ ε` must not be read as posterior reliability of an accepted receipt; §0 already defines the intended false-accept meaning correctly.

[OPEN] The Lean signatures below are **proposed interfaces**, not compiled implementation theorems. Domain names (`DeviceRun`, `ReceiptCheck`, `Experiment`, etc.) denote the semantics spelled out in each entry; they do not claim those types exist upstream. Proof bodies are intentionally not supplied, rather than hidden with `sorry`. Shared conventions: `G.prob E` is the probability of event `E : G.World → Prop` under one normalized experiment; `G.admissible a` is its resource/assumption restriction; `Gₐ` is the induced experiment for adversary `a`; `Budget` is a nonnegative rational plus its upper-bound interpretation. Cryptographic contracts quantify over admissible adversaries and their resource bounds. Deterministic reduction obligations are separate from computational advantage assumptions.

[MEASURED] [EXECUTED] The small, executable falsifiers and semantic event-transport lemma in `notes/astra/governance/GovernanceAudit.lean` were checked with `lean +leanprover/lean4:v4.35.0 notes/astra/governance/GovernanceAudit.lean`; output is in `notes/astra/governance/lean-check.txt`. This compiles only the small `Std`-based audit file, not a project. It contains no `sorry`, new axiom, `native_decide`, or implementation escape; the transport signature and printed axiom footprints are `#guard_msgs`-pinned. `projected_bad_subset` uses standard classical axioms; the finite dedup, record and projection counterexamples have no axioms. These checks prove counterexamples and an event inclusion, not the proposed device/crypto implementations.

## Inventory

[READ] Source locations; [INFERRED] classifications. **D** marks one of the 5 definite current defects. **Q** marks a useful formalization or conditional qualification, not a newly refuted theorem. “Fine” always means the stated contract has meaningful content under its explicit model, not that an implementation satisfies it.

| ID | Source | Statement | Current verdict |
|---|---|---|---|
| G01 | G:32–37 | semantic Boolean lattice | Fine, classical extensional semantics |
| G02 | G:41–47, 59–61 | evidence judgment | Fine with a fixed experiment and adversary class |
| G03 | G:50–65; S:471–475 | meet/composition | **Q:** true union bound; explicit transport is the remaining binding interface |
| G04 | G:77–89; S:457–482 | serialized `Judgment` | **Q:** schema needs an executable budget format and external checked interpretation |
| G05 | G:98–103 | discharge coverage assumption | **Q:** exact theorem discharge is valid; probabilistic receipt discharge pays its failure |
| G06 | G:116–120 | hypergeometric miss | Fine on the uniform, frozen, feasible-size domain |
| G07 | G:152–160 | tolerance implies at best T3 | **D: too strong**, conflates relation tolerance with proof error |
| G08 | G:375–380 | receipt “holds with error ε” | **Q:** intended false-accept meaning is fine; posterior reading is false |
| G09 | G:409–413; S:477–479 | evidence deduplication | **D: too strong**, identity does not identify failure events |
| G10 | G:350–360 | zero undeclared admissions | Fine after the explicit narrowing; not zero computations |
| G11 | G:361–374 | served/evaluated/trained/absent join | **Q:** formalize the one-root shorthand as typed components and relations |
| G12 | G:112, 139–141 | T2* drops verifier-implementation assumption | **Q:** verified binary route is fine; source export alone keeps compilation/FFI premises |
| S01 | S:88–111 | `ozaki_exact_under_acc` | Fine only with the prose's accumulator/refinement premises; old sketch too strong |
| S02 | S:95–107 | `field_dot_via_mma` | Fine with reconstruction/range/reduction; old sketch incomplete |
| S03 | S:159–162, 178–183 | `commit_before_forward` | Fine as occurrence-injective durable coverage; old sketch false |
| S04 | S:163, 184–186 | `leaf_binds` | Fine as a collision reduction; old equation trivial |
| S05 | S:164, 187–189 | `overflow_refuses` safety | Fine with fresh admission IDs; old sketch ill-scoped |
| S06 | S:189–190 | non-full forwarding companion | **D: too strong**, lacks progress/fairness and frame admissibility |
| S07 | S:165, 191–193 | `reboot_continuity` | Fine as accepted recovery under an authoritative durable anchor; old sketch false |
| S08 | S:243–246 | residue intersection/projection | Fine, definitional; projection only inclusion |
| S09 | S:248–254 | proof-leg interpretation independent of TEE | Fine as false-accept bound over an adversary class permitting a broken TEE |
| S10 | S:250–257 | TEE occurrence and confidentiality | **Q:** model confidentiality relationally; occurrence remains unary |
| S11 | S:306, 308 | `air_denotes` | Fine on supported syntax with field/word interpretation |
| S12 | S:307–308 | `air_sound` | Fine; follows from the forward half of S11 |
| S13 | S:309–310 | combinational `rtl_refines` | Fine under successful compilation, supported inputs and representation |
| S14 | S:311–312 | sequential RTL refinement | Fine as separate safety, with progress separate |
| S15 | S:313 | `receipt_means` | **D: too weak**, AST equality neither checks evidence nor proves denotation |
| S16 | S:355–356 | record agreement | **D: too strong**, omitted equality of authenticated terminal roots |
| S17 | S:357–358 | endpoint execution and acknowledged delivery | Fine under an explicit authenticated-ACK transition model |
| S18 | S:359–360 | terminal truncation obligation | Fine as deadline alarm; not a proof of malicious withholding |
| S19 | S:389–392 | tap feasibility | Fine as average work conservation, not a burst/service theorem |
| S20 | S:393–399 | tap assurance/detection | **Q:** make the intended adaptive per-history floor explicit |
| S21 | S:406–428 | attested choke-point coverage | Fine conditional composition; no inferred physical no-bypass fact |
| S22 | S:433–455 | vendor equivalence ⇒ device step | **Q:** source already names gaps; formal implication must include them |
| S23 | S:488–491 | checked accelerator cutpoints | Fine with output commitment preceding challenge and explicit nonlinear TEE leg |
| S24 | S:492–494 | consumable lease ⇒ once-only | **Q:** specify once-only authorization/receipt/billing separately from computation/delivery |
| S25 | S:495–496 | translation certificate | Fine with checker soundness for precisely the artifact semantics |
| S26 | S:497; G:235 | lineage capsules | Fine as transition/rooted-lineage proof target, not merely a hash chain |
| S27 | S:498–500 | proof-gated decryption + persistent DP budget | **Q:** specify adaptive DP and full release transcript game for this proposed direction |
| S28 | S:501–504 | leakage-preserving sharing | Fine as a relational trace/distribution obligation |
| S29 | S:511–520 | retirement accounting | Fine for completed architectural operations, not useful-work attribution |
| S30 | S:521–529 | authenticated operand reads | Fine for declared-dataset consumption; full lineage remains separate |
| S31 | S:530–538 | key retirement confidentiality | Fine only as the explicitly conditional cryptographic-erasure game |
| S32 | S:539–545 | PHY distance bound | Fine under the named timing/error/fraud model; no jurisdiction-continuity upgrade |

## G01–G12: lattice and judgment contracts

### G01 — semantic lattice

[READ] G:32–37 correctly separates the semantic lattice from evidence. [INFERRED] Lean's `Set Ω` is already extensional predicates; no extra AST quotient is needed for this mathematical layer. Classical complement makes it Boolean. A restricted executable AST is a separate representation and need not decide semantic equivalence.

```lean
theorem semantic_meet {Ω : Type} (P Q R : Set Ω) :
    R ⊆ P ∩ Q ↔ R ⊆ P ∧ R ⊆ Q

theorem semantic_complement {Ω : Type} (P : Set Ω) :
    P ∪ Pᶜ = Set.univ ∧ P ∩ Pᶜ = ∅
```

[INFERRED] Witness: `Ω := Bool`, `P := {true}`, `Q := {false}`. Nontrivial bottom/top and proper predicates exist. Do not demand decidable logical equivalence for arbitrary predicate ASTs merely because the semantic lattice exists.

### G02 — evidence judgment

[INFERRED] This is a sound definition when the probability experiment, verifier interpretation and resource-bounded adversary class are fixed:

```lean
def EvidenceSound (G : Experiment) (V P : G.World → Prop) (ε : ℝ≥0) : Prop :=
  ∀ a, G.admissible a → (G.withAdversary a).prob (fun w => V w ∧ ¬ P w) ≤ ε
```

[INFERRED] Witness: a verifier that recomputes a nonconstant Boolean function has error zero; admissible adversaries include a constant forgery, and a valid input is accepted. Falsifier for vacuous auditing: an empty adversary class or an always-reject verifier meets soundness but supplies no useful receipt. Require a separate accepted honest instance; this is not a reason to put completeness in the soundness definition.

### G03 — repair the unused binding leg

[READ] G:51 already gives bounds on `¬P₁` and `¬P₂` in one common world. Those two bounds alone imply the displayed conclusion by a union bound; `Bind` and `ε_b` add no logical content. [INFERRED] This is true mathematics but too weak a specification of the intended semantic join. The local statements must be about their own subjects, and alignment must transport them to the common target.

```lean
theorem projected_composition
    (G : Experiment) (acc₁ acc₂ bind local₁ local₂ aligned target : G.World → Prop)
    (ε₁ ε₂ εb : ℝ≥0)
    (h₁ : G.prob (fun w => acc₁ w ∧ ¬ local₁ w) ≤ ε₁)
    (h₂ : G.prob (fun w => acc₂ w ∧ ¬ local₂ w) ≤ ε₂)
    (hb : G.prob (fun w => bind w ∧ ¬ aligned w) ≤ εb)
    (transport : ∀ w, aligned w → local₁ w → local₂ w → target w) :
    G.prob (fun w => acc₁ w ∧ acc₂ w ∧ bind w ∧ ¬ target w) ≤
      min 1 (ε₁ + ε₂ + εb)
```

[INFERRED] `aligned` means the decoded local subjects agree under specified projections, not that an untrusted Boolean says they do. Witness: two checked openings of one typed request tuple with the same model/input/output and different evidence mechanisms. Falsifier: both local predicates are true of different requests while the target is false. [EXECUTED] `projected_bad_subset` proves the exact event inclusion needed for the repaired union bound; `no_transport_falsifier` supplies the propositional countermodel without transport. No independence assumption is needed.

### G04 — repair the receipt schema

[READ] G:81–88 is a record of claims; it has no verifier, experiment ID, semantic derivation or binding certificate. Its `ℝ≥0` cannot be a general finite serialized numeric type. `Finset Assumption` gives decidable membership only, not decidable satisfiability. [INFERRED] An attacker can fill this record with `eps = 0`, an arbitrary predicate, and unrelated references.

```lean
structure ReceiptClaim where
  subject : TypedSubject
  predicate : PredAst subject
  window : Window
  experiment : ExperimentId
  resources : ResourceBound
  budget : NonnegativeRational
  assumes : AssumptionFormula
  evidence : List EvidenceRef
  derivation : DerivationCertificate

theorem check_receipt_sound (r : ReceiptClaim)
    (hc : checkReceipt r = true) :
    InterpretedEvidenceSound r.experiment r.resources r.assumes
      (evidenceVerifier r) (denotePred r.subject r.window r.predicate) r.budget
```

[INFERRED] `checkReceipt` must validate a derivation in a restricted calculus whose primitive rules carry proofs/reduction bounds, authenticate all referenced bytes, check their subject/window/version, and round numerical bounds **upward**. Consistency is checked by a sound decision procedure for the chosen assumption language, or by a checkable satisfiability witness; “a Finset” does not suffice. Witness: a recomputation receipt with rational budget zero and an accepted derivation; falsifier: preserve evidence but lower its budget from `1/2` to zero. The repaired checker refuses. No type declaration itself establishes this theorem.

### G05 — exact discharge is valid; probabilistic discharge has a cost

[READ] G:98–103 proposes removing coverage from downstream assumptions after proving it as a predicate. [INFERRED] Exact implication supports this directly, which is the source’s stated device-step-theorem route. This is not a defect in that route. If it is replaced by a probabilistic receipt, that variant requires an additional error term and joint acceptance.

```lean
theorem discharge_coverage
    (G : Experiment) (accCover accClaim covers target : G.World → Prop)
    (εc ε : ℝ≥0)
    (hc : G.prob (fun w => accCover w ∧ ¬ covers w) ≤ εc)
    (hp : G.prob (fun w => accClaim w ∧ covers w ∧ ¬ target w) ≤ ε) :
    G.prob (fun w => accCover w ∧ accClaim w ∧ ¬ target w) ≤ min 1 (εc + ε)
```

[INFERRED] A conditional-on-coverage proof must be transported to the common experiment carefully; the second premise above is an **unconditional** bound on its restricted bad event. Witness: exact device coverage (`εc=0`). Falsifier: coverage fails with probability `δ`, and every failure hides an undeclared action; the other leg has error zero when coverage holds, yet the joint error is `δ`, not zero.

### G06 — fixed-population sampling

```lean
theorem fixed_population_miss (N b k : Nat) (hb : b ≤ N) (hk : k ≤ N)
    (bad : Finset (Fin N)) (hcard : bad.card = b) :
    missProbabilityUniformKSubset N k bad =
      (Nat.choose (N - b) k : ℚ) / Nat.choose N k
```

[INFERRED] Freeze `bad` before sampling; uniform sampling ranges over all size-`k` subsets and does not censor unavailable records. Witness: `N=4,b=1,k=2`, miss probability `1/2`. If `k>N`, the “uniform size-k sample” is uninhabited. If an adversary chooses `bad` after seeing the sample, the theorem's independence/freeze domain has been left. Those domains belong in the formal statement.

### G07 — tolerance is not soundness error

[READ] G:160 says tolerance claims are never stronger than T3 with error including the channel. [REFUTED: that general implication] An exact proof of `|y-f(x)| ≤ 1` can have proof error zero. Its statement is weaker than equality; it is not a randomly wrong equality proof. No probability law on allowed perturbations is implied by the tolerance.

```lean
def Within (f : X → ℝ) (δ : ℝ) (x : X) (y : ℝ) : Prop := |y - f x| ≤ δ

theorem tolerance_relation_sound
    (G : Experiment) (verify : G.World → Prop) (x : G.World → X)
    (y : G.World → ℝ) (δ : ℝ) (ε : ℝ≥0) :
    ProofSystemSoundFor G verify (fun w => Within f δ (x w) (y w)) ε →
    G.prob (fun w => verify w ∧ ¬ Within f δ (x w) (y w)) ≤ ε
```

[INFERRED] Repair the schema by carrying the actual tolerance relation, units and quantifiers. Do not convert tolerance into an error budget without an independently specified distribution/game. Witness: `f(x)=0,y=1,δ=1` is exactly within tolerance and not equal. A deterministic checker can accept it with zero false-accept error for `Within`. The allowed-output relation can indeed permit steering; that does not turn tolerance into a probability of relation falsity.

### G08 — false acceptance is not posterior truth

[INFERRED] G:41–43 already fixes the intended false-accept meaning; the following refutes only a stronger posterior interpretation of G:375, not its defined judgment. In a 100-point uniform experiment, accept only world 0 and let the asserted predicate be false everywhere. False-accept probability is `1/100`, but conditioned on acceptance the predicate is false with probability 1. [EXECUTED] `conditional_reliability_falsifier` checks the accepted/no-true-accept structure; `rare_accept_count` also checks exactly one accepted world among `List.finRange 100`; the probability numbers are the derived uniform count divided by 100.

```lean
theorem posterior_bound (G : Experiment) (acc P : G.World → Prop) (ε α : ℝ)
    (hα : 0 < α) (hacc : α ≤ G.prob acc)
    (herr : G.prob (fun w => acc w ∧ ¬ P w) ≤ ε) :
    G.conditionalProb acc (fun w => ¬ P w) ≤ ε / α
```

[INFERRED] The repair is primarily to say **“false-accept probability bounded by ε in experiment E”** on receipts. Use the posterior theorem only when its lower bound on acceptance and a meaningful prior distribution actually exist. This is independent of the adaptive composability issue.

### G09 — deduplicate events, not just evidence IDs

[REFUTED: S:477–479 and G:409–413 as a general sound dedup rule] Let the evidence be the same constant bytes in both legs and let both verifiers always accept. In a uniform Boolean world, `P₁(w)=w` and `P₂(w)=¬w` each have error `1/2`. Their conjunction is always false. Deduplicating by evidence identity to one `1/2` term undercounts the true joint error 1. [EXECUTED] `dedup_premises` and `dedup_by_identity_false` check this exact counterexample.

```lean
theorem dedup_same_failure (G : Experiment) (bad₁ bad₂ : G.World → Prop)
    (h : ∀ w, bad₁ w ↔ bad₂ w) :
    G.prob (fun w => bad₁ w ∨ bad₂ w) = G.prob bad₁
```

[INFERRED] Repair: deduplicate exact repeated **judgments** (same experiment, adversary/resources, accepted-false event, predicate/subject/window and assumption interpretation), or share one primitive failure event after a checked implication from every use to that event. A derivation DAG can record this proof. Identical evidence references alone are insufficient. Exact self-composition is harmless and should be idempotent; it is not a reason to undercount different uses.

### G10 — the narrowed admission claim is meaningful

```lean
theorem no_undeclared_admissions (r : DeviceRun)
    (hinit : InitialInventoryValid r)
    (hcoverage : EveryAdmissionRecorded r)
    (hlog : EveryRecordedAdmissionDeclared r) :
    ∀ e, AdmissionInWindow r e → DeclaredAtAdmission r e
```

[INFERRED] Witness: a nonempty execution admitting and forwarding a declared job, including a valid initial inventory. Falsifier to the broader claim: an already-approved persistent job performs a training update without a new admission. The displayed theorem says nothing false about that run. Initial inventory matters for a separate claim about active contexts, not for the bare universal statement over new admissions. A probability statement about evidence for these premises must compose their errors; the semantic implication above itself is fine.

### G11 — replace “one commitment” with one typed relation over multiple roots

[READ] G:361–374 now includes training lineage, correctly. [INFERRED] The remaining root shorthand is dangerous: model weights, corpus bytes and evaluation items are different objects; equal opaque digests cannot say they are related. A single tuple commitment is possible, but its fields and semantic edges must be explicit.

```lean
structure EvaluationServingSubject where
  modelRoot : ModelRoot
  dataRoot : DatasetRoot
  evalRoot : EvaluationRoot
  initRoot : TrainingStateRoot
  lineageRoot : LineageRoot
  inferenceSpec : InferenceSpecId
  trainingSpec : TrainingSpecId
  request : RequestId
  epoch : EpochId

def JoinedClaim (s : EvaluationServingSubject) (w : World) : Prop :=
  ServedWith w s.request s.epoch s.inferenceSpec s.modelRoot ∧
  EvaluatedModel w s.evalRoot s.inferenceSpec s.modelRoot ∧
  TrainedBy w s.trainingSpec s.initRoot s.dataRoot s.lineageRoot s.modelRoot ∧
  EvalItemsAbsentFrom w s.evalRoot s.dataRoot
```

[INFERRED] The repaired soundness statement is G03 instantiated with these projections and all relevant legs (not a single two-leg shortcut). The lineage includes pretraining/imported checkpoints or explicitly limits the claim to the declared training suffix. Witness: a one-step training run with distinct dataset/model roots, served and evaluated under one full inference spec. Falsifier: the same weights with a different tokenizer/system prompt passes a weights-only join but does not mean “the evaluated inference system answered.” A clean suffix starting from an undeclared pretrained checkpoint also does not prove lifetime absence.

### G12 — T2* must name the deployed machine semantics

[READ] G:112 removes “verifier implementation correct” at T2*. G:139–141 gives a Lean-decided export as the pattern. [INFERRED] Exporting a checked Lean predicate closes a source-level mirror; it does not prove the Lean compiler, runtime, FFI decoding, integer conversions or caller routing correct. Those remain named assumptions unless checked.

```lean
theorem deployed_verifier_refines (r : ReceiptBytes) (m : MachineState)
    (hdecode : decodeReceipt r = some claim)
    (hffi : FfiPrecondition m r)
    (hbuild : LoadedBinaryRefines checkedVerifier m) :
    machineAccepts m r ↔ checkedVerifier claim = true
```

[INFERRED] To remove the implementation assumption completely, `hbuild` must be discharged through a trusted compiler theorem/translation validator and the actual loaded artifact. Otherwise put it in `assumes`. Witness: a byte-pinned binary with a verified decode/refinement path; falsifier: a caller ignoring the Lean return value and returning “accept”. The Lean predicate remains proved while the deployed verifier is wrong.

## S01–S10: arithmetic, receipt device and evidence interpretations

### S01 — accumulator exactness

[READ] S:92–94's old code remains too strong; S:98–110 explicitly adds the missing premises. [INFERRED] Treat the replacement as a refinement theorem for an explicit accumulator transition, not as a bound on the final sum alone.

```lean
theorem ozaki_exact_under_acc (A : AccModel) (xs ys : List FP4)
    (hlen : xs.length = ys.length)
    (hrep : EveryOperandRepresented A xs ys)
    (hinit : A.initialAccumulator = A.encodeInt 0)
    (hschedule : ValidMmaSchedule A xs ys)
    (hexact : EveryIntermediateOperationExact A xs ys) :
    A.decodeInt (hwMma A xs ys) = integerDot (decodeOperands A xs) (decodeOperands A ys)
```

[INFERRED] `EveryIntermediateOperationExact` must be derived from **local** representability/range lemmas and concrete rounding/alignment semantics. Defining it as the final equality would be `P → P`. A useful lower lemma quantifies over representable inputs and proves the one-step transition commutes with integer addition/multiplication. Nonempty witness: one product `1×1`, zero initial accumulator, supported scale and enough exponent/significand range. Falsifiers to the old bound: nonzero initial accumulator, unequal input lengths, or a model whose alignment discards a small addend before cancellation. The GPU observation is evidence for the model, not a kernel proof that physical silicon follows it.

### S02 — field dot reconstruction

```lean
theorem field_dot_via_mma (p : Nat) (hp : 1 < p) (A : AccModel)
    (u v : Fin n → Fin p)
    (hlimbs : LimbDecompositionReconstructs 13 u v)
    (hmma : EveryLimbDotExact A u v)
    (hwidth : RecombinationHasNoOverflow A u v)
    (hreduce : ReductionImplementsIntMod p) :
    reduceMod p (recombine13 (limbwiseMma A u v)) =
      (∑ i, (u i).val * (v i).val) % p
```

[INFERRED] This integer-residue identity needs no primality premise. A field presentation can subsequently require prime `p`. Witness: `n=1,u=v=1` and exact integer semantics. Falsifier: a wraparound recombiner can corrupt the result while every individual limb dot is correct. Reconstruction, bit widths and reduction must be actual lemmas, not `hmma` defined as this conclusion.

### S03 — per-occurrence commit before forward

```lean
theorem commit_before_forward (r : DeviceRun)
    (hinit : ValidInitialState r.initial)
    (hrun : FollowsDeviceStep r)
    (hdurable : DurableStoreSemantics r) :
    ∃ commitOf : ForwardOccurrence r → DurableCommitOccurrence r,
      Function.Injective commitOf ∧
      ∀ f, (commitOf f).time < f.time ∧
        (commitOf f).record = admittedRecord r f.admissionId ∧
        PreservedInAuthenticatedHistory r (commitOf f)
```

[INFERRED] `admittedRecord` contains actual forwarded bytes (or a binding digest), occurrence ID, job/session, epoch and VJM root at admission; the transition relation connects these to what the output port emits. Durability is an acknowledgement from the persistent-store model, not a queued `persist` command. Witness: admit→durable-ack→forward one real frame. Falsifiers: emit forward before durable ack and crash; reuse one commit for two separate forwarding authorizations; mutate VJM before final root inspection. The current prose repairs all three. This proves forwarding coverage, not peer receipt, and it need not allow retransmissions to share one occurrence unless the specification explicitly says they are one event.

### S04 — leaf binding reduction

```lean
theorem leaf_collision_extract (r₁ r₂ : Record)
    (hne : r₁ ≠ r₂) (heq : leaf r₁ = leaf r₂)
    (henc : Function.Injective encodeRecord) :
    HashCollision outerHash ∨ HashCollision payloadHash
```

[INFERRED] `Record` uses actual payload bytes plus the full typed metadata. The reduction returns colliding preimages, not merely an existential axiom called “collision resistance.” Witness: an injective outer encoding and a toy constant hash allow a concrete nontrivial collision, showing the antecedent is inhabited and the extraction meaningful. In a cryptographic theorem the colliding inputs must be efficiently produced and the reduction's resource overhead charged. An injective hash is unnecessary; the old `leaf = H(...)` equation is just its definition.

### S05 — overflow safety

```lean
theorem overflow_refuses (r : DeviceRun) (j : AdmissionId) (f : Frame)
    (hrun : FollowsDeviceStep r) (hfresh : FreshAdmission r j)
    (hfull : InsufficientReservableDurableCapacity r.now f) :
    RefusedAt r.now j ∧ ¬ AuthorizedAt r.now j ∧
      ∀ t, r.now ≤ t → ForwardedAt r t j →
        ∃ k, FreshReadmissionBetween r j k r.now t
```

[INFERRED] The later forwarding occurrence belongs to a fresh readmission token; do not silently reuse `j`. Witness: a full one-slot device refuses a second distinct admission. Falsifier: refusal leaves a pending authorization which is forwarded later after a reset. This is a safety theorem; always-refuse is deliberately a model of it. S06 supplies useful progress separately.

### S06 — repair the non-full liveness companion

[READ] S:189–190 says a non-full execution does forward. [REFUTED: unconditional liveness] A non-full device can receive a malformed/unauthorized frame, crash forever before its durable ack, or be starved by its scheduler. No correct safety device must forward in those runs.

```lean
theorem admitted_frame_eventually_forwarded (r : InfiniteDeviceRun) (j : AdmissionId)
    (hrun : FollowsDeviceStep r)
    (hadmit : ValidFrameAdmittedWithReservation r j)
    (hready : FairDownstreamReady r j)
    (hstore : DurableWritesEventuallyComplete r j)
    (hsched : FairDeviceScheduling r)
    (hstable : EventuallyNoFurtherCrashBeforeCompletion r j)
    (hcancel : NotCancelled r j) :
    ∃ t, ForwardedAt r t j
```

[INFERRED] A bounded-latency variant needs quantitative service bounds, not just fairness. If the chosen abstract device instead makes persistence and forwarding one total atomic operation, state that synchronous model explicitly; fairness is then unnecessary inside that operation, but its refinement to a real asynchronous persistent device remains an obligation. Witness: the three-event admit/ack/forward trace extended by idle steps. Falsifier: the same admitted frame with downstream-ready false forever. This repair does not smuggle availability into safety.

### S07 — anchored recovery

```lean
theorem reboot_continuity (r : DeviceRun) (a : AuthoritativeAnchor) (s : Snapshot)
    (hanchor : AnchorTracksDurableCommitOrder r a)
    (hload : recover a s = some recovered)
    (hauth : SnapshotAuthenticationHolds s) :
    HistoryExtends recovered.history (authorizedPrefix r a) ∧
      recovered.nextId > maxPreviouslyAuthorizedId r ∧
      recovered.epoch = a.epoch

theorem stale_snapshot_refused (a : AuthoritativeAnchor) (s : Snapshot)
    (hstale : s.counter < a.counter) : recover a s = none
```

[INFERRED] These are accepted-recovery safety contracts; they do not promise recovery succeeds after every crash. The anchor update, log persistence and authorization protocol need a crash model that makes `AnchorTracksDurableCommitOrder` provable. Witness: matching authenticated snapshot and anchor after one durable commit. Falsifier: restore the empty snapshot after one authorized frame. A counter checked only after forwarding cannot repair the gap. The source's “preserves every previously authorized forward” must refer to persistent coverage, not actually resending every old frame.

### S08 — residual-set identity and projection

```lean
def Res {Ω : Type} (A E : Set Ω) : Set Ω := A ∩ E

theorem residue_intersection {Ω : Type} (A E₁ E₂ : Set Ω) :
    Res A (E₁ ∩ E₂) = Res A E₁ ∩ Res A E₂

theorem projected_residue_inclusion {Ω Subject : Type}
    (π : Ω → Subject) (A E₁ E₂ : Set Ω) :
    π '' Res A (E₁ ∩ E₂) ⊆ (π '' Res A E₁) ∩ (π '' Res A E₂)
```

[INFERRED] These are fine algebra, not evidence interpretation. Witness making inclusion strict: two worlds map to the same subject; `E₁` holds only in the first and `E₂` only in the second. [EXECUTED] `projected_intersection_strict` checks the incompatible hidden-witness core. Distinct predicate interpretations, not the definitional identity, carry assurance.

### S09 — proof leg independent of TEE integrity

```lean
theorem proof_leg_validity (G : ProofReceiptGame) (a : Adversary)
    (ha : G.proofAdmissible a) (hps : ProofSystemSound G a ε)
    (hbind : SubjectBindingReduction G a εb) :
    (G.run a).prob (fun w => ProofAccepted w ∧ ¬ OutputRelation w) ≤ min 1 (ε + εb)
```

[INFERRED] `proofAdmissible` must permit the adversary to break/control the TEE, and the proof statement must not use an unverified TEE-supplied assertion as an algebraic premise. Witness: a direct proof of `y=f(x)` over a public input/output relation while the TEE lies. Falsifier: the proof only establishes “the TEE signed y”; then its own relation is true and there is no theorem of output validity independent of TEE trust. The source correctly calls for per-leg interpretation.

### S10 — separate occurrence safety from confidentiality games

[READ] S:250–257 places occurrence and confidentiality in the same per-world predicate story. [INFERRED] Occurrence can be a trace property. Confidentiality compares adversarial observations across possible secrets; it is a hyperproperty or indistinguishability game. Putting the word `Confidential` into a unary predicate does not specify that game. Nor is a TEE the only possible mechanism for these goals; this is only the role of the chosen TEE leg in this construction.

```lean
theorem tee_occurrence (G : AttestationGame) (a : Adversary)
    (ha : G.admissible a) (hcode : MeasuredCodeRefinesEndpoint G)
    (hfresh : EpochAndChallengeFreshness G) :
    (G.run a).prob (fun w => QuoteAccepted w ∧ ¬ OccurredOnNamedDevice w) ≤ G.occurrenceError

theorem tee_confidentiality (G : ConfidentialExecutionGame) (a : Adversary)
    (ha : G.admissible a) (hcode : MeasuredCodeRefinesEndpoint G)
    (hobs : ExplicitLeakagePolicy G) (hisolation : TeeIsolationAndLifecycle G) :
    G.distinguishingAdvantage a ≤ G.confidentialityError
```

[INFERRED] Specify allowed outputs/metadata, corruption timing, migration, rollback, termination and side channels in the second game. Witness: two secrets with the same authorized public output and a constant public trace in an ideal isolated endpoint. Falsifier: a perfectly correct, freshly attested program that prints the secret; the occurrence theorem holds and secrecy fails. “Both share Stmt” repairs identity, not confidentiality.

## S11–S22: refinements, transcripts, taps and vendor devices

### S11 — AIR denotation

```lean
theorem air_denotes (e : SupportedAst) (x : Input e) (y : Output e) :
    (∃ aux : AuxTrace e, Sat (emitAir e) (encodeInput x) (encodeOutput y) aux) ↔
      y = denote e x
```

[INFERRED] Fine for a total supported fragment with proved range checks and field-to-word interpretation. The existential is necessary: wrong intermediate columns do not satisfy just because endpoints are right. Witness: a one-gate addition/multiplication with the genuine witness. Falsifier to a missing range bridge: a field value representing a different integer modulo the characteristic; a field equation alone cannot identify the intended integer.

### S12 — per-trace AIR soundness

```lean
theorem air_sound (e : SupportedAst) (x : Input e) (y : Output e) (aux : AuxTrace e)
    (h : Sat (emitAir e) (encodeInput x) (encodeOutput y) aux) :
    y = denote e x
```

[INFERRED] Fine; follows from S11's forward direction with witness `aux`. Witness: the same nontrivial gate. Negative test: alter a wire used by that gate and show either refusal or unchanged semantics, rather than test only the honest trace. No cryptographic probability is asserted here; this is the deterministic relation before the proof-system soundness leg.

### S13 — combinational RTL refinement

```lean
theorem rtl_refines (e : SupportedAst) (m : RtlModule)
    (hc : compileBookToRtlSat (bookOf e) = some m)
    (x : Input e) (hwf : WellFormedInput e x) :
    decodeOutputs e (evalModuleOutputs m (encodeEnv e x)) = some (denote e x)
```

[INFERRED] Prefer decoded outputs to equality with a singleton association list unless the port contract truly has exactly one output in that order. Witness: supported one-gate expression, successful compile, nonzero input. Falsifier to over-generalization: unsupported syntax causes `none`; no circuit follows. `WellFormedInput` must have a concrete inhabitant and only express representation constraints, not the desired output equality.

### S14 — sequential refinement is a separate contract

```lean
theorem rtl_trace_refines (m : SequentialRtl) (f : ReferenceMachine) (r : ClockedRun m)
    (hreset : ResetProtocol r) (hmem : MemoryOrderProtocol r)
    (hhs : HandshakeProtocol r) (hrel : InitialStateRelation r f) :
    ∃ a : AbstractRun f,
      visibleInputs a = acceptedInputs r ∧ visibleOutputs a = emittedOutputs r
```

[INFERRED] For infinite runs use a stuttering simulation and a prefix/safety formulation, then separately prove progress under fairness. This contract requires no spurious or reordered outputs; merely showing every emitted output is individually valid is weaker. Witness: one request, one stalled clock, then one correct response. Falsifier: duplicate a correct response; per-output validity passes but trace equality fails.

### S15 — repair `receipt_means`

[READ] S:313 states accepted receipt ⇒ its AST equals `Pred.graph f ...`. [INFERRED] If the receipt language permits other predicates, that is false; if the checker merely demands this AST, it is a syntactic tautology. Neither direction connects receipt evidence to the world's computation.

```lean
theorem graph_receipt_sound (G : ReceiptGame) (r : GraphReceipt f)
    (hc : checkGraphReceipt r = true)
    (hroute : DeployedCheckerRefines checkGraphReceipt G)
    (hderive : VerifiedDerivationSound r.derivation G) :
    G.prob (fun w => acceptsEvidence r w ∧ ¬ GraphHoldsForSubject f r.subject w) ≤ r.budget
```

[INFERRED] This is a G04 specialization with an indexed predicate type. Witness: a genuine graph proof whose model/input/output match the receipt and loaded checker. Falsifier: the right graph AST with garbage evidence; the old AST-equality statement can still hold, the repaired verifier refuses. A deterministic `GraphHolds` conclusion is possible only for an exact evidence checker with its full reduction premises, not a general positive-error proof receipt.

### S16 — record agreement needs root equality

[READ] S:355–356 says authenticated roots binding the same session, length and schema imply record agreement except binding failure. [REFUTED: literal current sentence] Two honest parties can authenticate different roots for different one-record histories with identical session/length/schema. There is no hash collision. [EXECUTED] `equal_length_different_records` checks the minimal record counterexample.

```lean
theorem equal_root_record_agreement (a b : TranscriptOpening)
    (ha : ValidOpening a) (hb : ValidOpening b)
    (hs : a.session = b.session) (hn : a.length = b.length)
    (hv : a.schemaVersion = b.schemaVersion) (hr : a.root = b.root)
    (hneq : a.records ≠ b.records) :
    ∃ c, EfficientHashCollisionWitness a b c
```

[INFERRED] Different authenticated roots are instead an **equivocation/conflict evidence** object, when obligations require one history. They are not a record-agreement premise. Witness: identical nonempty transcripts. Falsifier to the unrepaired form: `[false]` versus `[true]`, signed by the same legitimate session endpoint. Canonical length/root conventions must be checked; a root over an untyped list is insufficient.

### S17 — execution and acknowledged delivery

```lean
theorem endpoint_records_mean (r : EndpointRun)
    (hrun : FollowsVerifiedEndpoint r) (hauth : AuthenticatedPeerAcks r) :
    (∀ rec, ExecutionRecord r rec → ∃ e, ExecutionEvent r e ∧ BindsRecord rec e) ∧
    (∀ rec, DeliveryRecord r rec → ∃ a, PeerAcknowledged r a ∧ BindsRecord rec a)
```

[INFERRED] This is fine under the endpoint model. “Acknowledged” is the precise claim; it does not prove a human read or use of the result. The ACK itself binds the session/request/response digest, and the peer-key assumption is named. Witness: request→execution→response→authenticated ACK. Falsifier: log “delivered” immediately after a local socket send, then drop the packet; execution happened but no peer acknowledgement did.

### S18 — deadline/truncation alarm

```lean
theorem terminal_obligation_alarm (r : MonitorRun) (o : TerminalObligation)
    (ho : AuthenticatedAndAgreed r o) (ht : TrustedClockPastDeadline r o)
    (hm : MissingRequiredTerminalEvidence r o) :
    alarm r = true
```

[INFERRED] Fine as fail-closed alarm; it establishes an unfulfilled obligation, not malicious intent. Witness: terminal length/root agreed in advance, deadline elapsed, no terminal receipt. Falsifier to a broader malicious-truncation conclusion: a network outage after an honest endpoint completed. Detectability also requires the monitor to run and have the authenticated obligation; it cannot be inferred from inspecting an arbitrary shorter prefix.

### S19 — average work conservation

```lean
theorem sustainable_tap_feasible (s : TapSchedule) (p Btap Bengine : ℝ)
    (hnonneg : 0 ≤ p ∧ 0 ≤ Btap ∧ 0 ≤ Bengine)
    (hunits : UniformAuditCostUnits s Btap Bengine)
    (harrivals : LongRunSelectedWorkRate s = p * Btap)
    (hservice : LongRunServiceRate s ≤ Bengine)
    (hstable : SublinearBacklogGrowth s) :
    p * Btap ≤ Bengine
```

[INFERRED] Fine as necessity only. Averages do not prevent a finite burst overflowing the FIFO, and `Btap` bytes/sec cannot be compared with proof jobs/sec without a work conversion. Witness: constant input, constant per-item cost, service exceeding arrivals. Falsifier to sufficiency: arbitrarily large bursts under an acceptable long-run mean. Selection with value-dependent audit costs also changes the average-work expression.

### S20 — repair adaptive tap assurance with conditional floors

[READ] S:393–395 demands every bad item detected at the stated probability, but does not formalize its conditioning. [INFERRED] A marginal floor is inadequate for AuditSampling's adaptive stopping-time consumer: an adversary can corrupt exactly histories with no service. Service availability and corruption decision must precede fresh selection appropriately.

```lean
theorem tap_detection_conditional (G : AdaptiveTapGame) (h : G.History)
    (hh : G.reachable h) (hbad : G.nextCommittedItemBad h)
    (hcommit : ItemAndWitnessFrozenBeforeSelection G h)
    (hservice : UniformConditionalServiceGuarantee G h)
    (hbeacon : ConditionalSelectionUnpredictability G h εbeacon)
    (hcheck : ConditionalCheckerSoundness G h εchk)
    (hbind : ConditionalBindingFailureBound G h εbind) :
    G.nextAlarmProbability h ≥ max 0 (G.sampleRate * (1 - εchk) - εbind - εbeacon)
```

[INFERRED] A stronger unconditional bad-event hybrid can derive these legs if its conditioning losses are accounted for; one global adversary advantage must not be reused as an unchanged conditional bound on arbitrarily rare histories. Witness: fair fresh independent coin after each frozen item, sufficient reserved audit capacity, fail-closed timeout. Falsifier: service succeeds on half the histories; attacker recognizes the unserved half and corrupts only there. The overall service rate is `1/2`, detection on corrupt rounds is zero.

### S21 — coverage through an attested choke point

```lean
theorem choke_point_covers (r : FacilityRun)
    (hroute : EveryScopedExternalEffectCrossesDevice r)
    (hcode : DeviceExecutionRefinesReceiptStep r)
    (hdev : EveryDeviceForwardDurablyRecorded r) :
    EveryScopedExternalEffectDurablyRecorded r
```

[INFERRED] Fine conditional implication. Attestation establishes `hcode` only through code measurement, initialization and measured-code semantics. The external no-bypass premise is not proved by the number of NICs in a VM manifest. Witness: a model with one enforced output transition. Falsifier: GPU DMA or a management channel outside the modeled path. Both the source and the repaired statement keep this physical/runtime premise visible.

### S22 — vendor netlist equivalence is not deployed device equivalence

[READ] S:443–444 writes `(vendor attestation ∧ ZK equivalence ∧ public refinement) ⇒ device step = f`; S:449–455 acknowledges substitution and combinational limitations. [INFERRED] The deterministic implication still overstates positive-error proof evidence and a combinational check. A stateful receipt device requires state/reset/handshake refinement plus the loaded-bitstream/netlist and silicon bridge.

```lean
theorem deployed_vendor_device_sound (G : VendorDeviceGame)
    (hpub : PublicRtlSequentiallyRefines f)
    (hcec : EquivalenceProofSound G εcec)
    (hload : LoadedArtifactBindingSound G εload)
    (hatt : AttestationInterpretationSound G εatt)
    (hsilicon : PhysicalDeviceRefinesLoadedArtifact G) :
    G.prob (fun w => AllDeviceEvidenceAccepted w ∧ ¬ DeviceTraceRefines f w) ≤
      min 1 (εcec + εload + εatt)
```

[INFERRED] If equivalence is only combinational, restrict `f` to that combinational sub-block and retain a separate theorem for the sequential wrapper; do not quantify over the whole device. Witness: a one-step stateless device with pinned loaded artifact. Falsifier: equivalent combinational datapaths but a wrapper that forwards before durable ACK, or a correct proven netlist with a swapped bitstream. The honest physical premise is an assumption until an actual implementation bridge exists.

## S23–S32: the additional construction obligations

### S23 — proof-checked accelerator cutpoints

```lean
theorem checked_cutpoint_sound (G : CutpointGame) (a : Adversary)
    (ha : G.admissible a)
    (hfreeze : InputsAndClaimedOutputsCommittedBeforeChallenge G)
    (hfresh : FreshUniformFreivaldsChallenge G)
    (hlinear : LinearCheckerRefinesMatrixRelation G)
    (hnonlinear : TrustedNonlinearEndpointRefinesSpec G) :
    (G.run a).prob (fun w => CutpointAccepted w ∧ ¬ CutpointRelation w) ≤
      G.freivaldsError + G.bindingError
```

[INFERRED] This is a fine conditional target. The nonlinear trust leg must be named in the larger inference claim; the linear checker alone does not verify nonlinearities or all model identity. Witness: one fixed matrix/vector/output with a fresh challenge and correct nonlinear transition. Falsifier: reveal the challenge first, then choose a wrong output in its orthogonal kernel. “Post-commitment” must include the **claimed result**, not only the public matrix/input.

### S24 — once-only what?

[READ] S:492–494 burns a lease before releasing a result and claims O-2. G:233 combines unique receipt, no double billing and counted retries. [INFERRED] These are different events. Consuming a monotonic token is not enough to show one computation, one delivery, or one invoice: the same authorized result can be sent twice, a retry can duplicate computation, and a crash after burning can produce zero releases.

```lean
theorem lease_authorizes_at_most_one_release (r : LeaseRun)
    (hrun : FollowsAuthoritativeLeaseMachine r)
    (hanchor : DurableLinearizableCounter r)
    (hbind : ReleaseBindsLeaseRequestAndOutput r) :
    ∀ lease, (releaseAuthorizations r lease).length ≤ 1

theorem invoice_idempotent (r : BillingRun)
    (hrun : FollowsInvoiceMachine r)
    (hid : BillingKeyIsRequestAndLease r) :
    ∀ request, (chargedInvoices r request).length ≤ 1
```

[INFERRED] Repair the receipt predicate to say which of authorization, computation, send, acknowledged delivery or charge is once-only. Deduplicate retransmissions at the receiver if the service needs effective once-only delivery. State retry policy explicitly. Witness: consume lease then authorize exactly one result; falsifier: crash after consumption (no liveness), or replay a signed result on two network sends (one authorization, two transmissions). Do not assert exactly-once computation from this mechanism.

### S25 — translation validation

```lean
theorem translation_certificate_sound (src : SourceArtifact) (dst : TargetArtifact)
    (cert : TranslationCertificate)
    (hc : checkTranslation src dst cert = true) :
    Refines (targetSemantics dst) (sourceSemantics src)
```

[INFERRED] Fine; `Refines` must specify termination/exception/undefined-behavior and memory observations relevant to the consumer. The target's actual artifact digest is the one checked and loaded. Witness: a nontrivial one-block identity/addition translation. Falsifier: mutate an output instruction while retaining the certificate and confirm refusal. A checker defined as a constant `false` needs a separate accepted witness; a constant `true` requires proving a generally false refinement.

### S26 — optimizer lineage capsules

```lean
theorem lineage_sound (c : LineageCertificate)
    (hc : checkLineage c = true)
    (htrans : TransitionCheckerSound c)
    (hbind : CapsuleOpeningBinding c) :
    ∃ states : Fin (c.steps + 1) → TrainingState,
      states 0 = c.initialState ∧
      StateCommitsTo (states (Fin.last c.steps)) c.finalRoot ∧
      ∀ i : Fin c.steps,
        TrainingTransition c.spec c.dataset c.schedule i
          (states i.castSucc) (states i.succ)
```

[INFERRED] This is the deterministic core under exact checker/binding premises; real cryptographic certificates require an event bound instead of treating hash binding as perfect. `TrainingState` includes weights, optimizer moments, RNG, data cursor and imported-parent identities. Root hash chaining alone would be vacuous provenance, but the source's transition-grade target is fine. Witness: two states linked by one specified update and explicit initialization. Falsifier: valid-looking capsules containing unrelated optimizer moments or a smuggled initial checkpoint. “Trained on D” is relative to the initialized/declared lineage, not a claim about an unproven ancestral history.

### S27 — proof-gated release plus a DP counter is not a DP theorem

[READ] S:498–500 adopts a gate with a persistent DP budget. [INFERRED] A sound proof of computing a query says nothing about its differential privacy. A persistent counter can correctly account for queries whose privacy costs were falsely assigned, or ignore leakage from rejection, timing, threshold shares and repeated queries across rolled-back identities.

```lean
theorem adaptive_release_dp (G : ReleaseGame)
    (hneighbor : FixedDatasetAdjacency G)
    (hbudget : PersistentGlobalPrivacyFilterSound G ε δ)
    (hmechanisms : EachAdaptiveMechanismConditionallyDp G)
    (hrandom : MechanismCoinsSampledByAuthorizedProtocol G)
    (hgate : ProofGateBindsWholeReleasedDerivation G)
    (hsim : FullReleaseTranscriptSimulatableFromAllowedOutputs G εsim) :
    ApproximateDp G.adversaryView G.adjacency ε (δ + εsim)
```

[INFERRED] The approximation term depends on the simulator's distance definition; if `εsim` is computational indistinguishability, the conclusion is **computational DP**, not statistical DP. Keep that choice explicit. Counter scope includes every release under the same dataset/accounting identity across crashes, concurrency and migrations. Witness: one randomized-response mechanism with a trusted fresh coin and one-unit privacy charge. Falsifier: host chooses the random tape to reveal the raw bit while still proving correct execution for those supplied coins. A proof of knowing coins is not a proof they were sampled honestly. The proof-gated decryption game also needs release/share transcript simulation; the counter does not supply it.

### S28 — leakage-preserving accelerator sharing

```lean
theorem sharing_preserves_leakage (G : SharedAcceleratorGame)
    (hpartition : EnforcedPartitionAndScheduler G)
    (hreset : CrossTenantStateSanitization G)
    (himpl : AcceleratorRefinesLeakageModel G) :
    ∀ s₀ s₁, G.allowedLeakage s₀ = G.allowedLeakage s₁ →
      Indistinguishable (G.otherTenantView s₀) (G.otherTenantView s₁)
```

[INFERRED] Fine as a relational contract, not a unary “confidential run” assertion. The observer includes timings, contention, cache state and proof/FHE scheduling visible to other tenants. Witness: time-partitioned ideal accelerator with fixed-length public schedules and cleared private state. Falsifier: secret-dependent instruction count delays another tenant even when values never cross address spaces. The formal leakage function prevents an empty “all observations are allowed leakage” definition from masquerading as secrecy.

### S29 — completed architectural operation accounting

```lean
theorem retirement_counter_exact (r : AcceleratorRun)
    (hrun : FollowsCounterCoupledSemantics r)
    (hinit : r.counterInitial = 0)
    (hreset : ResetPreservesAuthoritativeAccounting r) :
    r.counterFinal = ∑ e ∈ completedArchitecturalOperations r, operationWeight e
```

[INFERRED] Fine for the source's explicitly named completed architectural operations. Define whether cancelled partial operations contribute; retries that really execute may contribute more than one event. Counter widths must avoid wrap or fail closed. Witness: two completed vector MACs with a stall and one pre-execution cancellation. Falsifier: a hidden completion path not incrementing the counter. This is not useful-work attribution or a count of all analog transistor activity; those require another relation to the declared job, precisely as S:520 notes.

### S30 — authenticated reads at the operand boundary

```lean
theorem consumed_sample_provenance (r : TrainingExecution) (D : DatasetRoot)
    (hrun : FollowsAuthenticatedLoaderAndCache r)
    (himmut : VerifiedPagesRemainImmutableThroughConsumption r)
    (hbind : DatasetOpeningBinding r D) :
    ∀ c, ConsumedTrainingSample r c →
      ∃ index version bytes,
        OpensDataset D index version bytes ∧ ConsumedBytes c = bytes
```

[INFERRED] Fine for dataset provenance at this boundary. Bind tags and **bytes** together through DMA/cache replay and version transitions; labels and sample preprocessing must be included in the declared training relation when relevant. Witness: one verified immutable page consumed once. Falsifier: verify page D, mutate its bytes while preserving tag D, then consume. This theorem does not establish the initial weights' origin or that the optimizer used all and only these samples; S26 and the typed join G11 supply those distinct obligations.

### S31 — cryptographic erase after epoch retirement

```lean
theorem retired_epoch_confidentiality (G : ErasureGame) (a : Adversary)
    (ha : G.admissibleAfterRetirement a)
    (hcopy : NoPriorSecretOrKeyCopyInAdversaryView G)
    (hclear : AllPlaintextBuffersAndKeyDerivationPathsDestroyed G)
    (hrollback : NoEpochRollback G)
    (henc : RetainedCiphertextEncryptionSecure G)
    (hleak : EqualAuthorizedPriorLeakage G) :
    G.postRetirementAdvantage a ≤ G.encryptionAdvantage + G.erasureFailure
```

[INFERRED] This gives the source's conditional confidentiality of retained ciphertext, not universal erasure. It must include persistent master-key derivation paths, in-flight DMA, caches and migration snapshots in the zeroization/lifecycle model. Witness: ideal one-use epoch key erased after draining buffers, same permitted pre-retirement leakage in both challenge worlds. Falsifier: erase a cached derived key but retain its derivable master secret. Without the encryption premise, destroying a key says nothing about ciphertext confidentiality.

### S32 — PHY-timed proximity

```lean
theorem distance_bound_sound (G : DistanceBoundingGame) (a : Adversary)
    (ha : G.admissible a)
    (hkey : ResponseKeyBoundToNamedDeviceEpoch G)
    (hclock : BoundedOneSidedTimingError G)
    (hphysics : PropagationDelayLowerBound G)
    (hrapid : RapidPhaseProtocolSound G) :
    (G.run a).prob (fun w => ProximityAccepted w ∧
      G.actualDistance w > G.claimedRadius w) ≤ G.fraudAdvantage
```

[INFERRED] Fine only under its explicit timing, error, response and adversary model. The radius derives conservatively from a **lower** bound on travel time per distance and a maximum timing underestimate; arbitrary software RTT does not inherit the rapid-phase fraud bound. Witness: an honest enrolled device at known short distance with timing margin. Falsifier: early guessing, a colluding nearby key holder, or timestamp under-reporting beyond the stated error. A successful exchange establishes proximity at that epoch, not continuous jurisdiction residence or that an inference ran on the nearby device.

## Historical defects, regression teeth and integration

[READ] The twelve-item historical inventory in `governance-codex-synthesis.md:113–126` corresponds here to S01, S02, S03, S04, S05/S06, S07, S08/S09/S10, S11/S12, S13/S14, S16/S17/S18, S19/S20 and G03/G09. The source already retracts the bad sketches. This audit does not report the old final-root, repeated-frame, bad-aux-trace or reversed-bandwidth examples as new discoveries.

[INFERRED] The **5 definite current defects** are G07, G09, S06, S15 and S16. Each has a repaired statement and a witness/falsifier above. The **11 qualifications/interface obligations** are G03, G04, G05, G08, G11, G12, S10, S20, S22, S24 and S27. They have useful explicit contracts but are not counted as newly refuted theorems: some source prose already names their missing premises, some are proposed directions without a claimed theorem, and others warn against interpreting the source more strongly than it says.

[INFERRED] Priority for implementation:

1. Reuse one computational-binding **bad event and reduction witness** for G03/S04/S16; do not instantiate `PositionBinding` by assuming global hash injectivity. Thread its advantage into the shared experiment's budget. A global cryptographic advantage cannot automatically become a uniform conditional advantage in S20 without proving that transport.
2. Build receipts as checked derivation DAGs with typed subjects, exact rational budget upper bounds and primitive-failure references. Dedup only proven-identical failure events or exact repeated judgments. This repairs G04/G09 and makes the binding budget reviewable.
3. Implement the small durable device state machine and prove S03/S05/S07, then add the independently stated progress premises in S06. Model ack-before-forward, crash at every boundary and stale snapshots; count occurrences, not frame values.
4. Keep output validity, occurrence, authorized release, delivery and confidentiality separate. Their conjunction is G03 instantiated with explicit transports, not an intuition supplied by a shared hash.

[OPEN] No device, compiler, TEE, DP or cryptographic implementation was built by this lane. No theorem signature above is a claim of an upstream implementation. The compiled artifacts deliberately prove only the reusable logical transport and concrete counterexamples. No paid search queries or PDF downloads were used; this is a source-statement audit, not a literature survey.
