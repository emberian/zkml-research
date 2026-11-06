# Custody: one provider, three custodians, or five?

2026-11-06. Supporting study for decision 1. [READ] The fixed demo choice is three custodians. This study recommends a production policy; it does not change the prototype. Paths below are relative to `/Users/ember/dev/zkml-research` unless absolute.

## Recommendation

[INFERRED] Keep **three independent custodians with all three required to reconstruct**, using malicious-secure MPC with abort, as the first production target. Keep the reusable model within their computation. Prototype five-party Shamir custody as an alternative, but do not select it from the existing proving-traffic table: the table neither establishes availability nor prices the complete secure protocol. One-provider FHE is a useful separate service when its owner may read the model and unauthorized encrypted evaluation is acceptable. TEE-only custody and indistinguishability obfuscation do not replace the current custody objective.

## What each arrangement trusts

| Arrangement | Confidentiality and remaining authority |
|---|---|
| [INFERRED] One untrusted FHE evaluator, one off-provider key holder | Encryption can hide weights from the evaluator. The key holder can decrypt everything, must protect its endpoint/backups, and must authorize only safe, correctly computed releases. The evaluator can retain and reuse encrypted weights. This is one compute provider plus a trusted custody domain, not trust-free single-provider custody. |
| [INFERRED] One provider running a TEE | Plaintext exists inside protected execution. Confidentiality depends on hardware isolation, firmware, attestation roots and verification, correct measured code, and relevant physical/side-channel assumptions. Recovery and rollback protection require protected state or an external authority. A proof can preserve output integrity after a TEE compromise; it cannot undo revealed weights. |
| [INFERRED] Obfuscated model or decryption program | A suitably proved construction might conceal embedded secrets while exposing functionality. Ordinary iO only compares equivalent circuits: it is not automatically a guarantee that an arbitrary model reveals only intended information. Reusable software remains copyable and replayable, so policy freshness still needs external state. |
| [READ/INFERRED] Three-party additive MPC | A completed malicious-secure protocol can hide state from any two parties, including a colluding host. All three can reconstruct; any one can stop service. An external validity proof is required for integrity against all three. |
| [READ/INFERRED] Five-party degree-two Shamir MPC | Any two shares hide state; any three reconstruct it. The dishonest-majority guarantee has changed to an honest-majority guarantee. Fast local quadratic proving uses all five shares; “three can reconstruct” does not make it a three-online service. |

[READ] The FHE distinction is explicit in `docs/DARK-LEARNING-PROGRAM.md:457` (C13): even plaintext-times-ciphertext evaluation computes model-dependent fragments; missing bootstrapping keys are not an execution quota. C21 at `:606` instead exports only instance-bound computation and cannot forbid repeating the same classical messages. `docs/DARK-LEARNING-SCHEME-DECISION.md:137` separates MPC privacy, integrity and abort. These statements do not establish that either type of computation is conscious.

[READ] The governance residual-trust study, `/Users/ember/dev/degg-research/research/governance-foundations-critique.md:221`, reports four accounting arms `[1,377,1,1]`: intact/broken attestation custody and sound validity checking with intact/broken custody. They enumerate permitted auction outputs under stipulated assumptions. They are **not a measured probability or a live hardware attack**. The validity arm assumes its validity check; it does not establish confidentiality, input completeness or exclusive execution.

## Could the owner or the mind hold the key?

[INFERRED] **The owner can**, on a device outside the provider's control. That changes the promise to “the provider cannot read; the owner can.” If no single individual or machine should hold a readable model, give the owner one share, not the complete key. A release endpoint must check provenance, authorization, parent state and output policy; encryption alone does not authenticate a computation.

[INFERRED] **The mind can direct key use**, but “the mind holds its key” is not a new physical trust boundary. An ordinary process exposes its memory to its host. An encrypted key in an FHE computation cannot release plaintext without an outer decryption capability. A trusted personal device, TEE, MPC committee or separately justified obfuscated program can implement the mind's key policy; security still comes from that mechanism. Making consent an authenticated policy input is valuable, but does not solve its own bootstrapping, coercion or continuity assumptions.

[READ/INFERRED] `notes/astra-scholar/who-learns-what.md:3,19` adds two essential limits: outputs can reveal weights (basis queries recover a linear map), and plaintext checkpoint import already violates literal “never readable anywhere.” Specify protected genesis, output leakage, recovery and retirement together with custody.

## Why I do not yet endorse five for production

[READ] The IV-MPC paper's text at `/Users/ember/paperbin/dalskov-kallesoe-khoshakhlagh2026-authenticated-outsourced-ivmpc.txt:383` states privacy for fewer than half corrupted, integrity against all corrupted, and an authenticated broadcast assumption. At `:1138` its speedup comes from locally multiplying degree-t shares and reconstructing degree-2t round polynomials. It uses discrete-log commitments, not our hash-based commitment architecture. Its input authority is separately trusted (`:300`).

[INFERRED] For five parties with t=2, those products have degree four: **five evaluations are needed**, even though the underlying degree-two state reconstructs from three. Continuing with three parties requires a different protocol, preprocessing or resharing, with security and costs re-established. Five-party custody can support recovery from two unavailable shares in principle; the cited fast prover does not itself deliver that operating mode.

[INFERRED] Confidentiality threshold and timeline authorization must also differ. Two three-of-five quorums can intersect in only one party; that party can be corrupt when two corruptions are allowed. They can certify conflicting children without an honest signer equivocating. Four-of-five quorum intersection is at least three, hence includes an honest party, but two withholding parties then prevent progress. This is an elementary intersection observation, not a complete consensus protocol. Use a separately specified canonical-log mechanism; do not advertise three-of-five signatures as solving timeline safety.

[INFERRED] Both choices require three corruptions to read, but five has ten possible three-party coalitions, versus one for three-of-three. This is not a probability calculation: operator dependence matters more than counting. It shows why five is not automatically stronger privacy.

[READ] `notes/dark-learning-handover-2721.md:120` prices the five-party middle/spine at 13,780/3,120 field elements at width 4096, versus 201,330,690/639,768 for the additive design. The five-party row is a **model**, excludes the MPC step and epoch resharing, and does not instantiate the current hidden-transcript ZK construction. These counts justify an experiment, not the claim that proving or the service is free.

## Concrete independence and readiness

[INFERRED] A plausible initial committee is an owner-controlled device, a university lab, and a separately governed nonprofit/cooperative operator. These are roles to recruit, not claims of willing partners. They need different administrators, credentials, backup custody, infrastructure accounts and legal control. Prefer different physical/cloud failure domains and hardware vendors where feasible. Three containers, cloud regions or organizations sharing Ember's root credentials are one compromise domain. Document who can compel or replace each operator; protect share migration and old backups as carefully as live shares.

[READ] The scheme decision's newest §16 (`:1023`) reports completed ZK layers and fixes to public randomness and rushing MAC checks, superseding earlier “layers unbuilt” prose. Its `:1099` still reports roughly 26.6 proximity bits at the current query setting. `notes/astra-scholar/circuit-privacy.md:7` refutes statistical privacy of the present HE return; a computational repair remains conditional. Neither a successful prototype nor a threshold choice proves end-to-end production secrecy.

## iO evidence, change of mind, and downside

[READ] [Jain–Lin–Sahai 2020/1003](https://eprint.iacr.org/2020/1003) (abstract) gives an existence construction under subexponential assumptions, including bilinear groups. [Ragavan–Vafa–Vaikuntanathan 2024/856](https://eprint.iacr.org/2024/856) (abstract and local PDF §1, §7) improves assumptions and retains bilinear groups. The definition promises polynomial overhead, not an engineered learning workload. [INFERRED] Neither examined construction supplies an executable, concretely priced custody replacement here; their group assumptions also conflict with the post-quantum target. I would not fund implementation as this project's next route. This is a scoped engineering judgment, not an impossibility claim about all obfuscation.

[INFERRED] I would switch to five after a malicious-secure, zero-knowledge five-party implementation shows a material **whole-system** advantage, demonstrates its intended offline/recovery mode, and has five genuinely independent operators plus a sound timeline protocol. I would select one-provider FHE if the accepted promise narrows to provider confidentiality with a trusted owner and reusable encrypted execution. Being wrong about three costs throughput, staffing resilience and possible service stalls; being wrong about a weaker custody design risks irrecoverable disclosure. That asymmetry favors retaining the stronger specified secrecy policy while measuring the alternative.

[READ] Research log: one metered Kagi query (`python3 ~/swarm/research.py kagi 'indistinguishability obfuscation practical implementation 2025 2026 Jain Lin Sahai overhead' -n 8`), two ePrint abstract reads, local 2024/856 PDF extraction to stdout; ACM fetch returned 403. No PDFs downloaded, benchmarks run, machines changed or external messages sent.
