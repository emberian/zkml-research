# Post-quantum composition audit for restricted release and finite ladders

[DERIVED reviewed correction, 2026-09-07] The conditional eleven-hybrid QIND_pre
lift now has completed independent review, and its qualified iO interface follows
from a standard worst-case equivalent-circuit iO game with arbitrary quantum
advice. The bound is `qualified gap <= Pr[E] * eps_wc`, with no efficient
conditioning or inverse-event-probability loss. The exact resource accounting
uses the stated nonuniform circuit model. See [QIO_INTERFACE.md](experiments/pq_composition/qio_interface/QIO_INTERFACE.md)
and [independent review](experiments/adversarial_review/qio_interface/REPORT.md).
This removes a bespoke qualification premise; it does not instantiate iO or the
other primitives. The further source audit and conditional xiO-to-iO lift are
now complete: the [bootstrap and pointwise-correctness supplement](experiments/pq_composition/qio_instantiation/bootstrap_lift/CLOSEOUT.md)
passed independent review under explicit one-copy quantum-advice primitive
games, with their exact privacy and correctness coefficients retained. The
[base-FE source audit](experiments/pq_composition/base_fe_audit/BASE_FE_AUDIT.md)
derives a conditional straight-line GKP lift but does not instantiate the
uniform short-key/depth-compactness interfaces or quantitative quantum
primitive rates needed by that bootstrap. [Independent review](experiments/adversarial_review/base_fe/REPORT.md)
accepts the conditional lift, clarifies direct all-block LWE loss accounting,
and proves a scoped obstruction for the literal full-key recursive payload:
raw GKP/GVW public-key width is at least four times its message bound. The
[public-environment representation](experiments/pq_composition/base_fe_audit/public_environment/PUBLIC_ENVIRONMENT.md)
now passed [independent review](experiments/adversarial_review/public_environment/REPORT.md):
future public keys can move into a correctly charged circuit environment, with
a simultaneous polynomial size bound under explicit compact encryption
circuit/output/randomness premises. This is a representation repair, not a
new primitive instantiation. The [depth-interface audit](experiments/pq_composition/base_fe_audit/depth_interface/DEPTH_INTERFACE.md)
affirms the source's Boolean compactness theorem, counts the literal bitwise
Q*M key substitution, and identifies a full-output constructor conditional on
compact Turing-machine randomized encoding. Its [independent review](experiments/adversarial_review/depth_interface/REPORT.md)
accepts the scoped result with explicit normalizations: PRF-correlated real
instances, clocked equal runtimes, zero inactive fields, and the standard
advantage interpretation of a printed probability typo. The extra primitive
and the complete quantum parameter chain remain open.
In particular,
quantum external advice does not by itself require quantum-valued aviO KeySamp.
Earlier first-pass wording below about that requirement is superseded here.

[DERIVED decision, 2026-09-06] The inspected sources support a **conditional post-quantum iO primitive**, but they do not yet instantiate the resident's randomized-FE ladder or receipt composition against quantum adversaries. The fixed independent-key ladder uses the older, classical `IND_pre` theorem. It avoids the newer construction's weak-extractability and quantitative compatibility requirements. Its finite horizon does not itself extend that theorem to QPT adversaries.

[SOURCE / scope] This audit reads seven named local primary PDFs, with exact versions, commands and access levels in [source_manifest.json](experiments/pq_composition/source_manifest.json) and [ACCESS_LOG.md](experiments/pq_composition/ACCESS_LOG.md). It is a theorem-interface audit, not a literature-wide absence claim. The ladder proof and its experimental witnesses belong to [FINITE_LADDER.md](experiments/private_construction/FINITE_LADDER.md); this note does not duplicate them. The single current-truth file `docs/VERDICTS.md` and both companion trees were left untouched.

## Assumptions and composition interfaces

[DERIVED notation] `QPT` below means a quantum polynomial-time adversary. Distinguish three resources: classical auxiliary data, quantum work state retained during a protocol, and an externally supplied quantum auxiliary register. A quantum adversary can have the second even if every command, ciphertext and public key is a classical string.

| Needed interface | What the inspected source supplies | Consequence for this route |
|---|---|---|
| [SOURCE] General-circuit PQ iO | Branco-Jain-Srinivasan, [2025/2215](https://eprint.iacr.org/2025/2215), Theorem 2 p.3: standard-model iO from subexponentially secure LWE **and** subexponentially secure average-case iO (`aviO`). The text explicitly claims PQ security when both assumptions have PQ subexponential security; its reduction is straight-line and invokes the adversary once. | [DERIVED] This is a valid conditional primitive route. It is not an iO construction from LWE alone, nor an instantiated aviO candidate. |
| [SOURCE] Average-case premise and auxiliary input | 2025/2215 Definition 6 p.16 uses PPT `KeySamp` and `Sim`, classical keyed circuits, and joint truth-table/auxiliary distributions in (5.1)-(5.2). In Lemma 5 pp.18-20, the actual auxiliary value is the classical tuple `(y,r,hk,ek_k)`. | [OPEN] Arbitrary quantum auxiliary registers, their generation, and a simulator preserving correlations with them are not specified in these equations. Do not infer that stronger game solely from the phrase “post-quantum.” |
| [SOURCE] PROM route and oracle access | 2025/2215 Theorem 1 and following discussion p.2 give xiO in a PRF-specific pseudorandom oracle model. The authors explicitly exclude superposition oracle queries, claim only classical security, and explain that the stated xiO-to-iO transformation cannot use this oracle-aided obfuscator. | [REFUTED: this proposed theorem application] Theorem 1 cannot be cited as a QROM-secure general-purpose release obfuscator. This does not contradict the separate standard-model Theorem 2. |
| [SOURCE] Exact functionality of the obfuscator | 2013/729 Definition 3.1 p.10 and 2025/330 Definition 3.9 p.18 require probability-one functionality. 2025/2215 Definition 3 p.10 permits all-input correctness failure; Lemma 4 p.18 and Corollary 1 p.11 yield a negligible-error result. Lemma 4 itself assumes perfectly correct underlying aviO. | [OPEN] The cited output primitive does not literally meet the randomized-FE papers' perfect-correctness premise. An error-tolerant restatement and propagation argument, or a different perfectly correct iO instantiation, is required. |
| [SOURCE] Old randomized-FE security | Goyal-Jain-Koppula-Sahai, [2013/729](https://eprint.iacr.org/2013/729), Definition 2.4 p.8 quantifies over nonuniform PPT adversaries with classical `z` and `st1`; functions/messages precede that scheme's public key. Theorem 4.1 p.14 gives 1-SIM from iO and OWFs; Lemma 2.9 p.9 gives unbounded `IND_pre`. | [DERIVED] This is the relevant classical primitive theorem for the reverse-setup ladder. It does **not** require subexponential iO or weak extractability. [OPEN] No QPT version of these games or theorem is stated in this PDF. |
| [SOURCE] Old construction's actual primitive suite | 2013/729 §§3-4 pp.10-14: semantically secure PKE, puncturable PRF, strongly unforgeable one-time signatures, computationally hiding/perfectly binding commitments (a statistically binding two-round alternative is discussed), statistically sound NIWI with perfect completeness and computational WI, and iO. | [OPEN] A PQ claim needs the corresponding quantum security games and compatible correctness for every computational leg. Substituting one PQ iO theorem does not automatically instantiate the NIWI/PRF/PKE/signature derivations used to compress this list to “iO + OWF.” |
| [SOURCE] New randomized-MIFE parameters | Datta-Guan-Korb-Sahai, [2025/330](https://eprint.iacr.org/2025/330), §6.1 p.48 and Theorem 6.1 p.50 require `(1,2^(-3ns-lambda_iO))` weak-extractable iO, two puncturable PRFs at separately enlarged parameters, and an injective OWF with both tiny success probability and subexponential-time hardness. Compatibility is required at `epsilon=2^(-2ns-lambda_iO)`. | [DERIVED] “Subexponential” includes actual advantage/time inequalities here. It cannot be replaced by an unspecified negligible PQ advantage. The same-key output-compatibility obstruction is already recorded in [RFE_RECURRENCE.md](experiments/private_construction/RFE_RECURRENCE.md). |
| [SOURCE] Weak extraction and auxiliary-state reuse | Boyle-Chung-Pass, [2013/650](https://eprint.iacr.org/2013/650), Definition 6.1/Theorem 6.2 printed pp.31-36; Goyal-Jain-O'Neill, [2015/1113](https://eprint.iacr.org/2015/1113), §2.4 PDF p.8 and Appendix A PDF pp.21-23. The latter's Figure 8 repeatedly invokes the adversary with the same classical auxiliary string `z`; its MIFE reduction PDF pp.17-18 resumes the distinguisher from a fixed transcript. | [OPEN] A single unknown quantum residual/auxiliary state cannot simply be supplied afresh on every call. These explicit classical extraction algorithms do not establish the required QPT composition with that resource. This is an unproved lifting, not an impossibility of quantum weak extraction. |
| [SOURCE] xiO bootstrapping and quantitative security | 2025/2215 Lemma 1 p.11 cites Lin-Pass-Seth-Telang, [2016/006](https://eprint.iacr.org/2016/006). Its Theorems 6-7 pp.9-11 preserve subexponential security through succinct FE and xiO; the formal notation and proofs use PPT/nonuniform classical algorithms. | [DERIVED] The cited construction supplies an asymptotic path for stronger classical parameters. [OPEN] For the newer randomized-FE application, a PQ audit must retain the needed exponents, adversary time, auxiliary access and correctness through the inherited transformations. Theorem 2's PQ statement alone does not state the weak-extraction game. |
| [SOURCE] SMS/LWE parameters under the PQ iO theorem | 2025/2215 Theorem 3 p.10 needs LWE with subexponential modulus-to-noise ratio and a stated small correctness error; Appendix A pp.25-26 supplies equivocal hashing and decomposable decryption. The referenced SMS construction, [2025/096](https://eprint.iacr.org/2025/096), §5, uses depth-dependent noise bounds and superpolynomial modulus-to-noise ratio. | [DERIVED] An ordinary chosen LWE parameter point is not a substitute for this parameter family. The source gives a conditional asymptotic theorem, not a concrete security/latency instantiation for the resident. |
| [SOURCE: repository read] Public receipt proof | `SECURITY_GAME.md`, “Assumption ledger,” identifies the current FS proof as uniform-field **classical ROM**. | [OPEN] Neither standard-model PQ iO nor finite FE composition supplies a QROM lifting of that separate receipt. Authentication, private ingress, release authorization and recovery likewise need their own stated PQ games. |

## What the positive iO theorem actually supports

[SOURCE: construction and proof read] A supported conditional instantiation is the following **primitive-level** one. Assume the post-quantum subexponential LWE families used by 2025/2215 Theorem 3 and its xiO bootstrap, and assume a perfectly correct, sufficiently succinct aviO satisfying Definition 6 with the post-quantum subexponential security required by Theorem 2. Then the paper claims standard-model post-quantum iO for classical polynomial-size circuits, with the correctness error tracked by Lemma 4, Lemma 1 and Corollary 1. This keeps the aviO assumption explicit. No concrete aviO implementation or finite security parameter is supplied by this audit.

[SOURCE: reduction read] The main xiO construction releases public encodings and aviO obfuscations of circuits computing a decomposable SMS decryption bit XOR a circuit bit (§6.1 p.17). Lemma 5 makes the aviO precondition hold by a sequence of SMS-security and statistical-equivocation hybrids; the postcondition then switches equivalent circuits. Claims 4-5 p.20 generate the remainder of the classical view, invoke the distinguishing adversary, and forward its bit. This supports the authors' explicit straight-line PQ explanation for **this** transformation.

[DERIVED boundary] The above statement does not promise obfuscation of quantum circuits, hiding against arbitrary quantum side information correlated with key generation, or randomized-FE security. The printed aviO game is about classical truth tables and classical auxiliary values. A stronger quantum-auxiliary interpretation must be defined and then included in its hypothesis; it cannot be silently borrowed for a downstream extractor that repeatedly needs that auxiliary register.

[SOURCE / DERIVED] For correctness, 2025/2215 Lemma 1 gives `2^eta * poly(eta) * epsilon` when bootstrapping an epsilon-correct xiO to eta-input-bit iO. Corollary 1 chooses `eta=lambda^delta` below the exponent in `epsilon=2^(-lambda^epsilon_exp)`. Thus its own claimed negligible-error result has an explicit reason. This is not a proof of perfect correctness.

[DERIVED possible repair] If every issued object has a **uniform all-input** failure probability at most `epsilon_i`, a union bound gives at most `sum_i epsilon_i` probability that any issued object computes the wrong function on some input. Independence is unnecessary. Fixed/polynomially many preissued keys make this a plausible correctness repair, including all local evaluations of a good object. [OPEN] This observation does not reprove randomized-FE security, construct the NIWI primitive, or discharge quantum auxiliary-state obligations; no perfect-correctness claim is made.

## Why the finite ladder has a better PQ audit target

[SOURCE: full reduction read] The older randomized-FE simulator in 2013/729 §5.1 pp.14-15 extracts a submitted ciphertext's plaintext using its own simulated-setup PKE secret key and sends that plaintext to the ideal functionality. It does not use a knowledge extractor that rewinds the adversary. Its hybrid sequence is `H0,...,H11` (§5.2); the explicit reductions in Claims A.4/A.5 and Lemmas A.6/A.8/A.9 pp.20-23 proceed through one experiment, answering classical queries and replacing one challenge object. Appendix C pp.24-25 handles `SIM -> IND_pre` using the joint output-compatibility premise and independence of the current public key from the preselected functions.

[DERIVED] This is evidence that a carefully specified QPT lifting is a reasonable bounded follow-up for the ladder. If the interfaces remain classical and each computational primitive is secure for quantum distinguishers retaining their work state, straight-line simulation can retain that state without copying it. [OPEN] This note has not established the complete new quantum game, its advice convention, all auxiliary-input primitive hypotheses, or the resulting quantum `SIM -> IND_pre` composition. Accordingly the current ladder remains classical and source-conditional.

[DERIVED first unmet application] To invoke the recorded ladder theorem against a QPT resident adversary, the first missing interface is a QPT `IND_pre` theorem with the **joint** compatibility view, including the entire exposed future-key package and any permitted retained quantum state. 2013/729 Definition 2.4 is a classical theorem. If that game is explicitly lifted, the next direct source mismatch is perfect obfuscator correctness versus the negligible-error result of 2025/2215, followed by the full PQ primitive suite. This is a finite checklist of theorem obligations, not evidence that the ladder cannot work.

## Why the newer extractor cannot be imported by relabeling iO

[SOURCE: algorithm and parameter read] 2015/1113 Definition 3 PDF p.8 requires extraction from a distinguisher with gap `epsilon > delta`, for circuit pairs differing on at most `d` inputs, in time polynomial in `1/epsilon,d,t_A,n,k`. Its single-differing-input extractor (Appendix A, Figure 8 PDF p.22) runs an inner loop `t=k/epsilon^2` per input bit. It estimates acceptance probabilities by repeated calls using the same `z`. In the actual MIFE reduction PDF pp.17-18, the repeated distinguisher continues from transcript `tau` at the function-key query.

[DERIVED] For `epsilon=2^(-B)`, the displayed inner-loop count is `k*2^(2B)`. At `B=2ns+lambda_iO`, this factor is `k*2^(4ns+2lambda_iO)`. These are algebraic consequences of the source loop, not cryptographic parameter recommendations or measured costs. The injective-OWF assumption's adversary-time bound matters precisely because this reduction may take that long. Restricting the learner's horizon to two transitions does not bound this count by two or make quantum state reusable.

[DERIVED / OPEN] If `z` is classical and the quantum circuit implementing the adversary is freshly runnable from a known initial state, repeated independent quantum runs can produce ordinary classical samples. If `z` includes a single unknown quantum state, or is the adversary's quantum state at an adaptive checkpoint, the same sampler requires an additional preparation/reset resource. A quantum rewinding or extraction theorem could change the conclusion; the inspected classical algorithms do not provide it. In particular, the straight-line property claimed by **2025/2215's** reduction does not transfer to this different extraction-based composition.

## Evaluation access and final boundary

| Access mode | Audited consequence |
|---|---|
| [DERIVED] A QPT attacker is handed classical obfuscated circuit code | It can implement that polynomial-size classical circuit reversibly and use local superpositions. A genuine QPT security game giving code must account for such local computation. This does not require a remote quantum oracle. |
| [SOURCE / OPEN] Classical online randFE APIs | The inspected FE games accept classical functions, ciphertexts and messages. Coherent decryption, key-generation or challenge-oracle queries are a different interface and were not proved here. |
| [SOURCE] PROM handle | 2025/2215 p.2 expressly excludes superposition queries in its PROM result. That exclusion cannot be erased by compiling other public algorithms reversibly. |

[DERIVED final status] Retain the finite independent-key route as a **classical conditional construction**. Retain 2025/2215 as a **conditional PQ-iO dependency**, with aviO, subexponential LWE families and nonzero correctness error stated. Do not label their conjunction, the newer randomized-FE construction, or the current classical-ROM receipts as an audited PQ resident.

[OPEN next decisive work] Write the QPT `IND_pre` game for classical APIs and one retained quantum state, replay the older eleven hybrid transitions with explicit primitive hypotheses, and budget the all-input correctness failures. A successful result would justify a conditional quantum ladder without needing the newer weak extractor. A source-backed primitive instantiation and a separate receipt/QROM proof would still be required for the combined resident claim.

[EXECUTED accounting] Seven local PDFs, seven pinned hashes, zero Scry SQL/schema queries, zero Kagi, four web search queries, three HTML landing-page opens and zero network PDF downloads. The reproducible extraction/provenance run passed all fourteen subprocess calls. It is not a cryptographic implementation or a kernel-checked composition proof.

[DERIVED reviewed successor, second authorized run] The conditional QIND_pre
game and eleven-hybrid lift at [QIND_PRE_LIFT.md](experiments/pq_composition/qind_pre/QIND_PRE_LIFT.md)
now has a completed independent source/proof review: no blocking error was found
under its explicit quantum-auxiliary primitive games. [REVIEW_COMPLETION.md](experiments/pq_composition/qind_pre/REVIEW_COMPLETION.md)
pins the exact reviewed pre-closeout bytes, reviewer attribution, full error
formula and successful replay of the saved finite premise controls. The current
draft's historical closeout paragraph is superseded by that completion note.
The source-backed primitive suite and whole-resident PQ conclusion remain open;
in particular, the stronger quantum auxiliary-state iO premise was not obtained
from the inspected PQ iO theorem.
