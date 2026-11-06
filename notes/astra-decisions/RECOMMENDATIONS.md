# Recommendations on the open decisions

2026-11-06 · Codex Astra scholar · Research and recommendations; no implementation or publication changes.

| # | Decision | Recommendation I would defend |
|---|---|---|
| 1 | Dark-learning custody | Three independent, all-three-required custodians as the first production target. One-provider FHE works for a narrower promise. Test five-party custody before adopting it. |
| 2 | VCF H100 application | Apply through the ordinary program; request an H100, 512 GB host RAM and eight initial GPU-hours, with publication freedom and interview disclosure. |
| 3 | Session-derived publication | Replace the public real-session artifacts with synthetic fixtures; remove current copies, retain history unless a concrete sensitive disclosure warrants rewriting it. |
| 4 | Multi-turn R3 | Introduce a faithful single-tick descriptor and new verification key; bind each turn and the final attestation. |
| 5 | Linux Lean seed | Publish a seed for the current source closure. Linux assets already exist; this is an update, not first publication. |
| 6 | Bridge ledger and vacuous demos | Policy B at the machine-code boundary; repair the demos with state preconditions and inhabited witnesses. |
| 7 | Chokepoint home | One canonical, core-only minidregg target. Keep Lean compilation; investigate CakeML separately. |
| 8 | Mac Mathlib cache | Move to toolchain/manifest-keyed package stores after normal Lake checks pass; preserve the old files. |
| 9 | ArkLib | Offer the native Merkle-adapter blueprint; finish the bridge and retire only the FS/Depth proofs it actually replaces. |
| 10 | Tensor experiment GPU | Package the probes, then rent one H100 SXM hour; proposed $10 cap. Blackwell follows a ready Blackwell-specific experiment. |
| 11 | Call-tree notary | Use bb2 for the runnable integration demo; use an independent operator for the stranger-facing provenance claim. |
| 12 | Tower256 profile/codec | Integrate registered work 9104 and finish bounded binary framing in the development cut; retain prefix caching. |
| 13 | Other pending items | Finish approved binding/schema repairs; keep capture, identity, deletion and aggregation claims within their actual evidence. |

These are my recommendations, not a request to approve thirteen engineering steps. Today's fixed choices remain: pinned self-signed demo certificates, GLM through the specified endpoint, three demo custodians, freedom to change shapes, and the Lean-compiled chokepoint.

`[READ]` means inspected source, paper, website or a lane's recorded result; it does not mean I reproduced that result. `[MEASURED]` means a read-only measurement performed during this study, with command/output retained in the supporting note. `[INFERRED]` means my reasoning or recommendation. In §§3–5 and §11, unprefixed implementation paths are relative to breadstuffs. Elsewhere, repository paths beginning `breadstuffs/`, `minidregg/`, `degg-research/` or `whatember/` are under `/Users/ember/dev/`; unprefixed `docs/`, `notes/` and `research/` paths are in zkml-research. Branch/commit qualifiers matter: several lane results are absent from the main checkout. Supporting studies carry fuller source locators and limitations.

## 1. Can dark learning use one untrusted provider?

**Question:** What trust replaces multiple custodians, and should production use three or five?

**Options:** One FHE evaluator plus an off-provider key holder; one provider with trusted hardware; obfuscated software; three all-required custodians; or five with any three able to reconstruct.

**Recommendation [INFERRED]:** Retain three independent custodians using malicious-secure multiparty computation (MPC) as the first production target. This is a target security policy, not a claim that today's prototype is production-ready.

One-provider fully homomorphic encryption (FHE) **can hide the weights from that provider**. An off-provider key holder must protect the key and gate plaintext release on authorization and valid computation. That key holder can decrypt the model. The provider can still copy encrypted weights and perform unauthorized encrypted computations. Encryption therefore answers confidentiality, not a prohibition on execution. The owner can hold the key if owner access is acceptable; otherwise give the owner one share. The mind can direct a key-use policy, but an ordinary process has no secret memory from its host. It needs a trusted device, hardware enclave or MPC implementation; encrypting its key merely moves decryption to an outer key holder. [READ/INFERRED: `docs/DARK-LEARNING-PROGRAM.md`, C13/C21; `docs/DARK-LEARNING-SCHEME-DECISION.md` §3; `notes/astra-scholar/who-learns-what.md`.]

A trusted execution environment (TEE) permits one provider by trusting hardware isolation, firmware, attestation and measured code, with rollback and relevant side-channel assumptions. Output proofs cannot repair leaked secrets. The governance critique's `[1,377,1,1]` residual-trust experiment counts permitted outputs under stipulated assumptions, not attack probabilities. Indistinguishability obfuscation (iO) is not a practical alternative I would fund here: the examined [2020 construction](https://eprint.iacr.org/2020/1003) and [2024 improvement](https://eprint.iacr.org/2024/856) supply no concretely priced learning system and retain bilinear-group assumptions contrary to the post-quantum target. Copyable software also needs external state to enforce freshness. This is scoped engineering judgment, not an impossibility theorem. [READ/INFERRED]

**Why three now?** Five-party degree-two sharing lets any three reconstruct, but the advertised fast prover locally multiplies shares into a degree-four polynomial: **that computation needs five evaluations**. Any-three reconstruction does not establish any-three operation. Two three-of-five signing quorums can intersect only in a corrupt party, so they also do not establish one timeline under two corruptions. The five-party cost model omits the full secure step and recovery. [READ/INFERRED: `dark-learning-handover-2721.md:120`; IV-MPC paper text `:383,1138`.]

Independent custodians could be an owner-controlled device, a university lab and a separately governed nonprofit/cooperative: separate administrators, credentials, backups, infrastructure accounts and legal control. These are prospective roles, not recruited partners. Three regions under one administrator are not independent. [INFERRED]

**Change my mind / risk:** A complete five-party protocol with measured total savings, recovery, timeline safety and independent operators would change the choice. A narrower owner-trusting promise would favor one-provider FHE. Three-party unanimity costs availability; an unjustified custody relaxation risks irreversible disclosure. Output policy also matters: basis queries can reveal a linear model despite encrypted storage. Current ZK progress does not close circuit privacy or the security ledger. See [CUSTODY.md](CUSTODY.md) for the current §16 corrections and source details.

## 2. Is applying for VCF's H100 worth it?

**Question:** What would cluster access add to FlashProve, and does the Lucid interview compromise it?

**Options:** Continue stored-proof replay; rent commercial capacity; or apply for donated research access.

**Recommendation [INFERRED]:** Apply through the ordinary VCF program for one exclusive H100 80 GB, **512 GB host RAM**, at least 500 GB local scratch and eight initial GPU-hours. These margins are a proposed allocation, not measured requirements. Stop to assess after the first fresh exact-match proof. Disclose the interview relationship, retain publication of negative as well as positive results, and acknowledge donated compute. Keep the hiring and allocation decisions separate. This manageable potential conflict is not a reason to refuse access; do not call the result an independent audit of Lucid's own product.

**Evidence [READ]:** [VCF](https://verifiablecompute.ai/) now reports two operational H100 nodes. Its linked specification lists an 8×H100 DGX with 2 TiB RAM and a separate confidential-computing H100 NVL node. The [Slurm default](https://docs.vcf.lucidcomputing.ai/guides/running-jobs/gpu-jobs/) is only 200 GB RAM per GPU. `/Users/ember/src/FlashProve/README.md:55–69` requires 10 GB for small synthetic proving, 280 GB for full-size synthetic and 330 GB for real Maverick weights. The 330 GB figure is not a requirement for every fresh proof. Confirm the CUDA/compiler and scratch setup before the allocation starts.

`notes/flashprove-audit/GROUNDING.md` §§1,3,5 already has real verification and withholding tests using two stored triples. Fresh proofs add new requests and outputs, the producer path from inputs to commitments/proofs, and producer failure or adversarial-modification experiments. They **do not** close the C++/Lean correspondence gap, prove a remote service logs every call, or identify weights beyond the committed statement. Start with small synthetic proofs, then full-size and public real weights. Ordinary DGX capacity suffices; hardware attestation is a separate experiment. [READ/INFERRED]

**Change my mind / risk:** Publication veto, incompatible tooling, insufficient RAM or a queue slower than commercial rental would favor buying time. The main costs are setup delay and perceived sponsor influence. Preserve a commodity-cloud reproduction path. Sources and the interview-brief grounding are in [GPU.md](GPU.md).

## 3. Should the public session-derived data stay?

**Question:** What should remain public, and can synthetic data replace every demonstration?

**Options:** keep it; remove the current files while preserving history; rewrite history.

**Recommendation — remove it from the current tree, including its revealing derivatives;
do not rewrite history on the evidence inspected.** [INFERRED] Make the already-built
synthetic variants the public default. Preserve the real experiment privately and its
aggregate findings in public prose. This does not undo the disclosure: old commits,
clones and previously published pages may retain it. Audit derived facts, certificates,
receipts and page payloads rather than removing only `transcript.json`.

[READ] `demo/datalog-governance/project_transcript.py:39` retains tool-use identifiers,
timestamps and file paths; `:69` also publishes the session identifier and hashes of
full redacted exports. [MEASURED] A schema-only Python read of
`demo/datalog-governance/data/transcript.json` counted 73 transcripts, 3,382 calls and
871 calls containing paths; no message contents or individual paths were printed.
[INFERRED] Paths disclose workspace structure, project relationships and subjects named
in files; names can be sensitive even without contents. Timestamps expose activity
patterns. Session, agent and call identifiers are correlation handles, not automatically
credentials; together with spawn edges they expose the work graph. Export hashes let a
holder of another copy confirm a match.

**Salted commitments deserve a different answer.** [READ]
`grain-session/src/lib.rs:265` derives each call's secret salt from a 32-byte owner
secret and call identity; `:278` hashes the salt with length-delimited input and result.
But `CallPublic` at `:73` still publishes paths, timestamps and identifiers, and `:315`
binds those fields into each window leaf. [INFERRED] The hiding commitment does not hide
those accompanying fields. Publish a deliberately minimal commitment artifact only
after reviewing its metadata; retain a fresh per-session master secret privately.
Leaking that master exposes every derived salt; reusing it and call identities permits
cross-publication linking. A window root does not establish that the original host log
was truthful.

**Are synthetic data enough for every demo?** No. [READ]
`demo/datalog-governance/README.md:6` already has deterministic violating/fixed examples.
[INFERRED] They suffice for the policy checker and tamper demonstrations, but cannot
substantiate a real `cv` integration or real HTTPS transport. Run a new, intentionally
public session and real GLM call tree with harmless inputs for those claims; keep the
historical session as private integration evidence.

**What changes my mind / wrong-cost:** keep a particular real artifact if it adds a
specific result synthetic data cannot and ember deliberately wants that disclosure.
Rewrite history if review identifies exposed credentials, private third-party data or
especially sensitive filename contents; rewriting alone cannot recall clones. Removal
costs convenient reproduction of this exact historical run. Keeping unnecessary
metadata imposes a lasting privacy cost.

Supporting source and measurement record: [SESSIONS.md](SESSIONS.md).

## 4. What is the faithful single-tick fix for R3?

**Question:** How do we prove actual multi-turn executor state rather than a related model?

**Options:** keep the honest model-head demonstration; change executor nonce semantics;
build a descriptor that proves the executor's actual transition.

**Recommendation — build the faithful descriptor and rotate its verification key.**
[INFERRED] The approved flag day removes the reason to treat this as a preference
question. Keep old receipts explicitly versioned as model-head receipts, not as proofs
of the new relation. Do not change executor semantics merely to fit the old prover.

[READ] `grain-turn/src/finalize.rs:28` explains the mismatch: one executor turn updates
several fields but advances the nonce once; the EffectVM advances it per effect.
`turn/src/executor/execute.rs:661` places fee debit and nonce advancement in turn-level
Phase 1. `finalize_session_threaded` at `finalize.rs:286` threads the modeled state,
yielding a foldable chain whose nonce differs from the ledger (`:277`). It therefore
solves continuity, not state fidelity.

[INFERRED] Specify the grain transition once: permitted field updates, preserved
fields, authority/capability and fee invariants, exact pre/post commitment encoding,
and a single nonce increment with its actual overflow behavior. Generate the
descriptor and witness from that specification, bind it to the new key, and test a
multi-turn sequence against captured executor states. Refuse mutations of the nonce,
each changed field, unchanged state, ordering and descriptor/key identity. A passing
fold alone is insufficient.

**One adjacent gap must be included.** [READ] `grain-turn/src/lib.rs:274` assigns the
call-tree commitment to `ATTESTATION_SLOT = 8`; `finalize.rs:96` and `:209` explicitly
refuse that slot because the old AIR state carries only eight field slots and the rest
falls into its authority residue. [INFERRED] The new descriptor must faithfully carry
slot 8 or its residue update before claiming call-tree R3 composition. Fixing only the
nonce would leave the attested call-tree route unable to finalize.

**What breaks:** [INFERRED] descriptor identities, verification-key pins, shape-dependent
setup results, old aggregates and their golden fixtures. Reissue the new version's
receipts and renter anchors. Reuse the verify-only interface from
`grain-session/GROUNDING.md:66`, with a key independently derived or pinned by the
verifier, never accepted merely because it appears in the bundle. Fewer legs might
reduce proving cost; this review did not measure that.

**What changes my mind / wrong-cost:** if the product intentionally attests only to a
derived EffectVM execution, the current model is an adequate named claim. That is
weaker than the stated real-ledger R3 goal. The risk of the change is circuit and
integration work plus invalidated fixtures; the risk of postponement is advertising a
proof about a different state machine.

Supporting source and measurement record: [SESSIONS.md](SESSIONS.md).

## 5. Should we publish a Linux Lean seed?

**Question:** What Linux verifier artifact should be published, with what provenance?

**Options:** require each verifier to build from source; publish a current-source
Linux seed on demand; restore automatic publishing on every change.

**Recommendation — publish a current-source Linux seed on demand, with authenticated
build provenance; keep source rebuilding available.** [INFERRED] Do not restore the
cron or push trigger. The seed is an ordinary platform-specific compiled verifier
archive, not secret setup material.

**The stated absence is stale.** [MEASURED] An unauthenticated GET of
[`releases/tags/lean-seed`](https://api.github.com/repos/emberian/dregg/releases/tags/lean-seed)
returned HTTP 200 with 154 assets, all named for Linux, on 2026-11-06. The newest archive
listed was `libdregg_lean-Linux-x86_64-v4.30.0-0cf8f1b585f6a18f.a.zst`, updated
2026-08-11, 39,569,367 compressed bytes. Thus `grain-session/GROUNDING.md:16`'s
“No Linux seed is published” cannot be carried forward. A missing current-source
asset is a different problem from a missing release.

[MEASURED] Running `bash scripts/lean-seed-key.sh` read-only, then recomputing its
four-line SHA-256 key with platform `Linux-x86_64`, found 365 in-tree closure modules
and expected asset `libdregg_lean-Linux-x86_64-v4.30.0-c5b665e744919694.a.zst`.
That name was absent from the release API's asset list. This is a working-tree
snapshot while other lanes are editing; recompute at the chosen release commit.

[READ] `scripts/lean-seed-key.sh:9` keys assets by platform, Lean version, mathlib
revision and the FFI source closure; `:28` deliberately hashes working-tree contents.
`.github/workflows/lean-seed.yml:80` preserves ember's explicit removal of automatic
builds and provides manual dispatch at `:85`. Its existing pipeline rebuilds the
closure, checks required exports and runs a strict Lean-backed smoke test before
publishing. Reuse it on the designated build host under its resource controls.

[INFERRED] Pin the source commit, complete dependency manifest, native compiler and
archive-tool versions, build flags and platform; publish these with full artifact
SHA-256. Add GitHub/Sigstore build attestation, verified against the expected repository
and workflow identity, or a release signature under a separately pinned maintainer
key. [READ] GitHub's
[artifact-attestation guide](https://docs.github.com/en/actions/how-tos/secure-your-work/use-artifact-attestations/use-artifact-attestations)
documents signed build provenance and `gh attestation verify`. [INFERRED] A checksum
downloaded beside an archive is not independent authentication; signing does not prove
source equivalence. Demonstrate that a second build reproduces the bytes, or publish
the exact differences and avoid claiming bit reproducibility.

[READ] `scripts/fetch-lean-seed.sh:165` has a missing-checksum warning path that proceeds.
[INFERRED] Publication consumers should fail closed on missing/mismatched checksum or
provenance and on absent Lean exports. Test a fresh Linux consumer with
`DREGG_REQUIRE_LEAN=1`, including one real accept and one refusal through the FFI, not
just symbol presence. Never silently fall back to the Rust-only marshal path.

**What changes my mind / wrong-cost:** a small standalone Lean verifier with equally
strong provenance could replace the large archive later. For now, withholding it
makes stranger verification unnecessarily expensive. Publishing a stale or substituted
archive is worse than an explicit build failure; an uncontrolled publication schedule
also repeats the documented host-contention problem.

Supporting source and measurement record: [SESSIONS.md](SESSIONS.md).

## 6. Which bridge ledger policy, and what replaces the vacuous demos?

**Question:** What justifies machine-code claims, and should the three impossible-premise certificates be repaired or deleted?

**Options:** A explicitly trusts identification of Lean and HOL definitions; B proves the boundary statement in HOL4; or A adds printed-statement comparison without a HOL proof. For the demos: retain, delete or repair.

**Recommendation [INFERRED]:** Choose **B for the statements used in machine-code composition**, beginning with the two concrete serve branches. Keep A-labelled conditional research results while those proofs are unfinished. This does not require porting approximately 20,000 supporting Lean lines. A statement comparison can detect mismatched statements; it cannot supply their proof.

Repair the useful demos using the existing state-conditioned `RefinesClk`/`RefinesClkPan` form. State which inputs must be bound and which memory/scoping conditions hold. Supply an inhabited initial state, a successful nonconstant run and an unbound-input counterexample. Retire the old vacuous certificate interfaces; retain `wf_reading_local_uninhabited` as a regression theorem. The examples are `redirectStatusStage`, `httpStamp` and `crlfStamp`.

**Evidence [READ]:** `degg-research/research/BRIDGE-KNOT.md` §4.2 describes A/B. Its §1 records a signed-to-unsigned comparison bug that passed structural/equation checks; §4.1 retains generic-printer and uniqueness assumptions. The reverse device already has HOL proofs `commit_before_forward` and `stepS_refines` in `DreggNet/docs/engine/probes/p3-bridge/reverse/hol/chokeProofScript.sml:70,95`. This demonstrates the approach, not completion of whole-program compiler premises.

`breadstuffs/orb-compiler/Pancake/LadderPanSem.lean:468` proves the universally bound-local premise impossible; `ProofProducing.lean:288` still uses it. `EmitCorrectClock.lean:75` already supplies the state-conditioned framework. The defect does not invalidate separate HOL stage certificates.

**Change my mind / risk:** If the two boundary proofs require rebuilding the entire compiler infrastructure, I would accept A plus statement comparison for an explicitly conditional release. B costs proof maintenance and can drift unless tied to the emitted concrete program. Permanent A risks advertising an unchecked identification as checked composition. [GOVERNANCE-BUILDS.md](GOVERNANCE-BUILDS.md) gives the exact remaining boundary.

## 7. Where should the chokepoint permanently live?

**Question:** Should runnable device definitions remain in degg-research or move into minidregg?

**Options:** Research remains canonical; minidregg owns the device; or maintain both copies.

**Recommendation [INFERRED]:** Make minidregg the sole canonical home of the step function, codec, proofs and exported entry point, in a **small core-only build target**. Keep experiments and trust analysis in degg-research. Connect the HOL exporter, Microkit integration and host adapter to that source before retiring its old copy. Avoid turning a small device build into the full minidregg umbrella.

Keep the Lean-compiled deployment, as already decided. CakeML should be a separately tested compiler route, not a blocker. Its next useful evidence is the actual summary step compiled for the target architecture, a wrapper meeting the compiler theorem's entry/exit conditions, and an external-call contract implemented by Microkit. Compare output bytes and demonstrate refusal when persistence returns the wrong acknowledgment.

**Evidence [READ]:** `degg-research/experiments/chokepoint-step/{README.md:17,check.sh:11}` already depend directly on minidregg's `Compiler/Blake3.lean`. `CHOKEPOINT-VEHICLE-DECISION.md` preserves the portable first-order core and proposes minidregg as its home. The requested `CAKEML-ROUTE.md` was absent; the governance lane transcript still names it as upcoming. `BRIDGE-KNOT.md` §6 leaves machine-code compilation and the Microkit entry point unfinished. A compiler theorem alone does not establish that outputs are performed in order or that the device cannot be bypassed.

**Change my mind / risk:** A maintained standalone package with external consumers could justify its own repository. Today that would add a boundary. Migration can break toolchain pins, source paths and export generation; validate those consumers, not a repository-wide rebuild. See [GOVERNANCE-BUILDS.md](GOVERNANCE-BUILDS.md).

## 8. What should happen to the Mac's shared Mathlib cache?

**Question:** Keep, delete or replace a writable package tree shared across incompatible Lean toolchains?

**Options:** Repair in place; delete and rebuild; or move consumers to separate keyed stores.

**Recommendation [INFERRED]:** Finish the active lane's keyed-store repair and then switch consumers to matching stores. Preserve the old files and `~/src/mathlib4` for unconverted consumers. In-place repair cannot solve incompatible writers; deletion risks other sessions' work.

Key stores by the complete dependency manifest and Lean toolchain, validate the full identity behind any abbreviated directory name, and include architecture/native-library identity for cross-machine reuse. Freeze compiled artifacts only after needed metadata exists. If Lake needs mutable metadata, provide a per-consumer overlay; if that is impractical, use separate keyed writable copies per worktree.

**Evidence:** [READ] The iteration lane and Mac helper were read first. The requested iteration report had not yet appeared. The helper already created separate 4.30/4.35 stores and checked their headers, but its isolated `timings3.log` still showed ordinary Lake failures caused by writes to frozen metadata. Direct Lean invocation succeeding is insufficient for a drop-in package replacement.

[MEASURED] The read-only census found **5,964 of 8,776** Mathlib artifacts with the 4.35 header, slightly different from the earlier 5,969. The command and aggregate output are retained in [GOVERNANCE-BUILDS.md](GOVERNANCE-BUILDS.md). Root toolchains remain 4.30 for breadstuffs and 4.35 for minidregg while their links reach the shared artifacts. This identifies contamination, not the process responsible.

**Change my mind / risk:** Normal `lake lean` and scoped `lake build` must work before switching shared roots. If immutable stores make routine rebuilding fragile, prefer isolated writable copies. The price is disk and warmup time; premature replacement breaks active work, and deletion can lose another session's files. This is an integration task, not a fresh request to bless cache destruction.

## 9. Should we contribute to ArkLib and retire FS/Depth?

**Question:** Is the Merkle-adapter blueprint useful upstream, and when may our duplicated proofs disappear?

**Options:** Maintain both stacks; offer our existing stack upstream; or contribute the missing adapter and consume upstream's general theorems.

**Recommendation [INFERRED]:** Choose the third. Offer a focused native-API blueprint on [#627](https://github.com/Verified-zkEVM/ArkLib/issues/627), crediting its existing author and coordinating where the native successor belongs. First adapt VCVio's guarantee that accepted openings agree with data extracted from the commitment-phase query log; then build the interactive compiler and compose with Fiat–Shamir. Do not advertise our accumulator instance or that adapter alone as a complete BCS compiler. This run posts nothing.

Finish the existing bridge and retire **exactly the theorems it derives**, including their migrated consumers. Preserve uncovered generality rather than an entire redundant tower. The approximately 2,600-line deletion is an intended outcome, not a present eligibility test.

**Evidence [READ]:** The corrections note and the actual `StateRestorationGame.lean:102` show upstream's merged `(Q + rounds.length) * error` theorem. Live [PR #1277](https://github.com/Verified-zkEVM/ArkLib/pull/1277) remains open: its more general single-salt Fiat–Shamir theorem is not yet released. Upstream's `CONTRIBUTING.md:14–25` asks for discussion before substantial implementation; its roadmap `:191–198` names the missing native Merkle adapter and says to reuse VCVio's game. The issue's existing work targets the legacy layer and deserves acknowledgment.

The bridge at minidregg `681b3c7d9`, `bridges/arklib-ud/SelvageArkLib/StateRestoration.lean`, establishes preservation and local boundedness for finite message types. Its transcript leaves cached-oracle coupling, extractor equality, full game correspondence and infinite-alphabet closure unfinished. Those obligations must precede retirement. The upstream `Q=0` example is nonvacuous; add a fresh/repeated-query bridge client to exercise the harder accounting, without calling that test gap a theorem defect.

**Change my mind / risk:** An existing adapter owner would favor review and client work. An indispensable infinite-alphabet consumer may require a retained fragment. The costs are dependency/API churn and possible game mismatch; a pinned optional bridge limits exposure. More detail: [PROOF-LIBRARIES.md](PROOF-LIBRARIES.md).

## 10. Which GPU should the tensor experiment use?

**Question:** What one-hour rental answers the next uncertainty without borrowing another project's machine?

**Options:** Wait for VCF; rent H100; rent B200/B300; or stop at the counts model.

**Recommendation [INFERRED]:** Prepare the runnable probes, then rent one exclusive **H100 SXM hour**, with a proposed **$10 total cap** for setup/storage. Use VCF if access has arrived. SXM matches the published TensorZKP comparison better than cheaper PCIe. Rent Blackwell only with its specific probes ready; B300 is more relevant than B200 to the lane's B300-specific INT8/FP8 hypothesis.

**Evidence [READ]:** `/Users/ember/swarm/MACHINES.md` records no GPU among the designated build machines; the other SSH aliases belong to other projects. They are not available experimental capacity. `notes/tensor-core-holography/{GROUNDING.md,F3-MODEL.md}` identify accumulator behavior, bandwidth, binary-matrix instruction rate and hashing as unresolved. The actual accumulator probe covers only the C-accumulator path and remains uncompiled; the within-instruction probe is still a recipe. A promised one-hour test is not yet a prepared one-hour artifact.

| Advertised price, fetched November 6 | H100 per hour | B200 per hour |
|---|---:|---:|
| [Runpod Pods](https://www.runpod.io/pricing) | SXM $3.99; PCIe $2.89 | $7.99 |
| [Modal](https://modal.com/pricing), GPU component only | $3.9492 | $6.2496 |

[READ/INFERRED] Modal figures convert its per-second rates and exclude CPU/memory charges. Runpod also lists B300 at $8.99. Availability and extra charges are unconfirmed; these are not reservations. Lambda's displayed new prices take effect November 16 and should not be quoted as today's price. Two Runpod hours, H100 then B200, are $11.98 in GPU charges; propose $20 total if both stages are justified. No spending is executed here.

**Change my mind / risk:** Immediate VCF access or a ready Blackwell experiment can change the provider/order. The direct downside is the proposed $10–20 budget; the larger risk is extrapolating peak matrix speed to a mostly hash-bound prover. Preserve compiler/driver/GPU settings and raw outputs, and distinguish a hashing proxy from the actual prover workload. [GPU.md](GPU.md) contains the source snapshot.

## 11. Whose notary should the call-tree demo use?

**Question:** What does a stranger trust when the notary is bb2 or an independent operator?

**Options:** ember's separate bb2 process; an independently controlled operator;
let the recipient run the MPC verifier themselves.

**Recommendation — target an independent operator for the public evidentiary demo;
use bb2 to develop and reproduce it, labeled “ember-operated notary.”** [INFERRED]
Independence is control of the signing key and execution, not a second hostname.
Choose an operator the intended verifier accepts, who keeps the key outside ember's
accounts, does not let the prover upload arbitrary signing code, and runs the
agreed MPC mode. Alternatively the recipient can participate directly as verifier.
No unsolicited operator contact is authorized by this recommendation.

[READ] `calltree/GROUNDING.md:12` reports that the old roundtrip helper spawned the
notary inside the prover process; moving it to bb2 removes that immediate co-residence.
`GROUNDING.md:28` and the primary
[TLSNotary introduction](https://tlsnotary.org/docs/intro/#tls-verification-with-a-general-purpose-notary)
say a transferable notarization is accepted by parties who trust that notary.
The protocol's soundness requires the notary not to collude with the prover.
[INFERRED] On bb2, a stranger still trusts ember not to fabricate both sides. Separate
processes improve deployment fidelity and accident isolation but do not establish
independent testimony about ember. An independent operator removes that common
controller, but the stranger still trusts that operator's key custody, implementation
and non-collusion; this is not trustless verification.

Keep today's decisions: GLM through the coding-plan endpoint and verifier-pinned
self-signed certificates. [INFERRED] A pinned certificate authenticates the chosen
tool server, not the truth of its replies. GLM transport evidence authenticates the
provider endpoint's returned bytes, not the model identity or correctness of an
inference. The notary key and server pin must arrive through an authenticated channel
outside the proof bundle. Keep authorization secrets redacted.

[READ] `calltree/GROUNDING.md:65` distinguishes transport authenticity and tree binding
from completeness: the agent can bypass the recorder. [INFERRED] Neither operator
choice proves no omitted outside calls, external factual truth or freshness without
an explicit time/challenge rule. The public claim should be “these authenticated
responses and checked dataflow edges form this committed tree,” with the named
notary assumption. It should not be “every action was captured.”

**What changes my mind / wrong-cost:** if the immediate demo's only claim is that the
components run, bb2 suffices and need not wait for an operator. If the recipient wants
actual third-party evidence, independent operation is part of the experiment, not
cosmetic polish. The cost is coordination and availability dependence; the cost of
using bb2 without the qualification is a persuasive-looking proof that adds no
independent witness against the party producing it.

Supporting source and measurement record: [SESSIONS.md](SESSIONS.md).

## 12. Should the Tower256 profile and binary codec flag day proceed?

**Question:** Freeze the current bytes or finish the bounded binary framing before native adoption?

**Options:** Retain unary framing; defer all changes; or integrate work 9104 and version the binary format now.

**Recommendation [INFERRED]:** Integrate the registered profile and finish bounded `u32` little-endian framing in this development cut. Keep prefix caching. This is a smaller, conventional interface before adoption, not a large speedup claim. Today's shape-change approval removes the old permission question.

An unbounded `Nat` cannot be silently truncated: use a length type below `2^32` or a checked encoder. Prove prefix-freeness, `basisPrefix` injectivity and round trips. Change suite/transcript versions and relevant artifact/codec pins, regenerate roots and receipts, and reject wrong-version proofs. Receipt compression and transcript framing are separate changes. Native work remains opaque; only Lean's decoding and checking authorize the reply.

**Evidence [READ]:** The requested work note is absent from the main checkout but exists at minidregg `107697663` on `lane/tower256-prover-exe`. Section 5 already registers work `9104`, request `9011`, response `9013` and a new artifact catalog `[9101,9104]`. `Tower256FriNativeDeployment.acceptResponse_iff` ties accepted bytes to `SuccinctAccepts`; the original v1 catalog remains unchanged. Its source still says the Rust prover is unwritten. Compiled Lean examples are not that kernel.

The same note records prefix caching and compact openings already implemented, superseding the older “cache first” task in `LEAF-PROVER-DECISION.md` §7. [MEASURED] Re-evaluating that note's **older cost model**, retained in [TOWER-COUNTS.json](TOWER-COUNTS.json), gives `ell=14`: seed permutations 7,666 → 316 with caching → 161 with binary framing; prefix bytes 6,824 → 1,832. After caching, its verifier total falls only about 1.1%. These are neither runtime measurements nor updated totals for the compact receipt.

**Change my mind / risk:** If a deployed consumer already pins these bytes, or the framing proof delays a working verifier materially, ship the cached unary version and defer framing to the next explicit cut. The main risk is overflow or ambiguous mixed-version parsing; old roots and fixtures will change. Never fall back to an older format automatically after verification fails. Details: [PROOF-LIBRARIES.md](PROOF-LIBRARIES.md).

## 13. What else needs a recommendation rather than another permission question?

**Question:** Which remaining items represent policy choices, stale findings or already-authorized engineering?

**Options:** Preserve the whole “waiting on ember” queue; accept every lane's revised bar; or make claim boundaries explicit and return approved repairs to their owners.

**Recommendation [INFERRED]:** Choose the third, with these concrete dispositions:

- **Finish approved content binding.** Public trace length, the table/weld routing chain and Dyck canonicalization are authorized. Current table routing still identifies a transition multiset/trail rather than an arbitrary public word; test a spliced-word refusal before making the stronger claim. The opening-heap witness repair is already present and should not be reassigned blindly. [READ: `breadstuffs/docs/automata/HANDOFF.md:40`; `AttestedAutomatonBound.lean:30–46,215`; `DfaRoutingTableBound.lean:16–46`.]
- **Repair the real schema gap; scope the alleged descriptor drift correctly.** The transfer descriptor literal is inside `cfg(test)` and explicitly a historical parser fixture. Keep it, fix commentary claiming equality with the live emitter, and test the served artifact separately. That finding alone does not warrant a verification-key rotation. Epoch 27 versus ledger 26 is a real source discrepancy: repair the ledger from its defining change and repair the self-test. [READ: `circuit/src/lean_descriptor_air.rs:2065,7628,7797`; `persist/src/lib.rs:882–903,958`; `docs/VK-REGEN-LOG.md`.]
- **Remove the hidden automaton restriction.** Prove a sentinel-safe edge encoding and a dense-to-indexed-tree adapter, pricing any range/capacity changes. The served test's `step(0,0)=0` restriction is a temporary domain limit, not the general interface. [READ: `circuit/src/heap_root.rs:71,433–456`; `circuit/tests/weld8_served.rs:21–25`.]
- **Keep stronger claims as actual next rungs.** A complete committed prefix does not prove capture of every real execution; a finite unanswered prompt is a pending obligation, not proved eventual response. A demo eval signature does not establish an evaluation of the exact quantized committed model. Exact unlearning can certify current-state recomputation, not erase historical releases; production deletion keys must hide guessable records. [READ: `breadstuffs/docs/stream/GROUNDING.md`; `research/model_identity_receipt_2026_11_06/GROUNDING.md`; `notes/unlearning/GROUNDING.md`.]
- **Choose aggregation topology explicitly.** Prototype stateful aggregation for one operator, retaining distributed handoff as a separate requirement. Private witness state does not automatically transfer between distrustful aggregators. Keep the warm hbox automata checkout for scoped gates; no deletion benefit was established. The combined policyc compile has finished, so the two-table workaround question is obsolete. [READ: `notes/holography-accumulation-verdict.md` §5; automata handoff's root notes.]

**Change my mind / risk:** A deployed capture theorem, real evaluator, hiding deletion-key construction or mandatory distributed aggregation would change the relevant recommendation. A served user of the old descriptor literal would escalate that finding. The costs of being wrong are false assurance or an unnecessary migration. These items should retain the original end-to-end ambition, with narrower intermediate claims rather than quietly lowered completion bars. Further evidence: [REMAINING.md](REMAINING.md).
