# Source register for this tranche

## Second timed run, 2026-09-07

[SOURCE / EXECUTED] New primary-source access and exact versions are recorded
by the owning lanes below. Their mathematical reductions are labeled separately
from what the papers state. No companion tree or eprint PDF was written from
this run; PDF extractions use the local mirror.

| Source and location read | New use and provenance |
|---|---|
| [SOURCE]2025/330, Definitions4.1–4.4 pp.21–23; §6.1 pp.48–50; hybrids pp.51,57–58; Lemma6.7 p.65 | Separates current PKE input-ciphertext width from function/randomness/output widths. [Parameter note and reviewed correction](experiments/private_ingress/provenance_review/PARAMETER_REVIEW_COMPLETION.md) preserve the lambda/ellR syntax issue and exact L>E support bound. |
| [SOURCE]2007/155, §9 pp.24–25 and proof definitions | Exact hiding-mode commitment equivocation equations and their limits for a common-parent transition. [DUAL_MODE.md](experiments/private_ingress/provenance_review/DUAL_MODE.md) pins local source and derived mode ordering. |
| [SOURCE]2023/265, §4.1 p.19 and Definition4.3 p.20 | Nonuniform QPT/quantum advice and worst-case equivalent-circuit iO convention. [QIO_INTERFACE.md](experiments/pq_composition/qio_interface/QIO_INTERFACE.md) derives the qualified-event lemma; independent review records its resource-model qualification. |
| [SOURCE]2025/2215 and bootstrap dependencies2016/006,2015/720 | The [source audit](experiments/pq_composition/qio_instantiation/INSTANTIATION.md) traces the actual xiO reduction, average-case precondition and correctness amplification. The separately derived [quantum-advice bootstrap and pointwise-correctness supplement](experiments/pq_composition/qio_instantiation/bootstrap_lift/CLOSEOUT.md) now have independent review; exact base-suite instantiation remains open. |
| [SOURCE]2012/733,2012/521,2013/364 and the six additional local sources pinned by the base lane | The [base-FE audit](experiments/pq_composition/base_fe_audit/BASE_FE_AUDIT.md) follows actual static-FE, garbling, ABE/TOR and amplification reductions. Its own conditional one-copy advice lemma is distinct from source claims. Nine PDFs are pinned; four metadata web searches, no Scry or PDF downloads. |
| [SOURCE]2017/276 Definition2.4/§3.1 and2017/274 Definition3.4;2019/1010 follow-up | [Lockable gate audit](experiments/private_construction/lockable_gate/README.md) checks full auxiliary-input lock unpredictability and source-game applicability. This lane adds two Scry SQL queries, zero schema calls and two web searches. |
| [SOURCE]2015/017 Construction3.1 and selective security theorem | Actual fixed-span DDH window control and a separately derived adaptive specialization; [fixed_span](experiments/private_construction/fixed_span/README.md) preserves the source and exposed-interface boundary. |
| [SOURCE / EXECUTED] Pinned local fhe-dregg sources and Cargo.lock | [Crypto manifest](experiments/end_to_end/crypto/README.md) supplies literal role/serialization dependencies and the caller-RNG versus internal-RNG distinction. Production keys use OS randomness; the public-seed historical secret-recovery warning remains. |
| [SOURCE / EXECUTED] Pinned local SmolLM2-135M model/tokenizer/config and encoder | [Live integration consolidation](experiments/end_to_end/utility/live_encoder/FINAL_INTEGRATION.md) verifies actual model execution and exact source/binary agreement. New feature studies keep their own frozen contracts, cost and data-provenance manifests. |

[EXECUTED search scope] First-run aggregate was12 Scry SQL/two schema. The
lockable audit adds two SQL/zero schema; other new source-access counts are
recorded in their lane manifests, with web accesses separate. The root's second
run has made no Scry query directly. It made two metadata searches for functional
proxy re-encryption/designated inner-product FE. The completed
[designated-span source audit](experiments/private_construction/designated_span/sources/PRIOR_ART.md)
adds two Scry SQL/zero schema and thirteen lane web queries. It corrects the
Feng publication to ICASSP 2024, distinguishes predicate PRE from numeric
projection output, and does not import a recipient-exposure theorem from
incompatible games. The combined recorded Scry total is now **16 SQL/two schema**.
This is not a literature-wide absence claim.

## Historical first-tranche register

[EXECUTED provenance] Run date: 2026-09-06. `experiments/results/environment.json`
records Python/OS/Lean versions, repository revisions, the initial companion dirty
state, local PDF SHA-256s and the `pdftotext -layout` commands. `source_hashes.json`
pins the cited companion source files and their available imported oleans. Source
and olean hashes are recorded separately; this is not a clean rebuild of every
upstream dependency. Lean is 4.30.0; dependencies were consumed from the existing
absolute LEAN_PATH. Nothing was installed in either companion source tree.

[EXECUTED first-tranche access accounting] Kagi queries: 0. Scry queries: 0. Web searches: 0.
One browser-tool open of the primary DROPS metadata/abstract page, linked below.
No eprint PDF downloads. Three PDFs read from the local mirror using `pdftotext`;
full extracted texts are ignored scratch artifacts, reproducible from recorded
paths/hashes. The earlier lanes' search counts belong to those notes and are not
this run's consumption. API-credit/token consumption is not exposed by this harness.

## Primary papers and application specifications

| ID | Version / exact source | What this run actually inspected | Used for |
|---|---|---|---|
| [SOURCE] GKS23 | `/Users/ember/dev/gh/forks/IACR-eprint-mirror/2022/1599.pdf`, SHA `46481fa2d839add77603839f85c6fc7551475e2c926719816903b4a537afe067` | Extracted construction §6.2, printed pp.57–58, Figures 8–9; parameter discussion pp.55–56; no full reduction audit | Static writer state and H/G correctness path in executable symbolic transcript |
| [SOURCE] sPCE26 | `/Users/ember/dev/gh/forks/IACR-eprint-mirror/2024/1294.pdf`, SHA `97b945e84c2daf3ca3a96411c9f4cc96e78a3b7dcab4bb56fae5baf934f7ae5b` | §3.1 syntax pp.15–16; single-function FHE construction p.22; landed lane identifies revision 2026-02-05; no fresh full reduction audit | One-hop transition attempt, retained underlying FHE.sk, precise scope of static-function restriction |
| [SOURCE/REPORTED] BKS25 | `/Users/ember/dev/gh/forks/IACR-eprint-mirror/2024/1213.pdf`, SHA `2bc6e43d8d06cac140557f7c0e1e6e3916b9ab93374d8ba841a8a427a4a5a1da` | Extracted text and targeted construction/credential lines; algorithm audit pp.49–50 and game interpretation inherited from landed note | Role-swapped comparison; not the executed symbolic model |
| [SOURCE] PCE22 | [Primary DROPS page](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITCS.2022.4), ITCS 2022, DOI `10.4230/LIPIcs.ITCS.2022.4` | Metadata and abstract only in this run; page says publication 2022-01-25, pp.4:1–4:20 | PCE's constrained setup-authority purpose; construction/iO analysis is [REPORTED] from landed audit, not newly proved |
| [REPORTED] KORB26 | Korb dissertation, Figure 3.2, printed p.94 / PDF p.107 | Landed `notes/streaming-fe-credential-audit.md` §1–2, including copied algorithms; dissertation not downloaded/read afresh | Cross-reference to the handoff's precise credential location; executable supported directly by GKS23 instead |
| [SOURCE: design] LOOM | `/Users/ember/Downloads/ARCHITECTURE.md:21`; `/Users/ember/Downloads/COGNITIVE_ORGANS.md`, §3 | Interface and state-family description; two-records/provenance paragraphs | Proposed beneficiary and restore surface, not implementation or scientific findings |

## Companion theorem/implementation locations

[SOURCE: code and theorem statements read] Every path below is absolute. These are
the existing imported objects, not new claims of having rerun the whole companion build.
Their source/olean hashes are in `experiments/results/source_hashes.json`.

| Location and name | Actual claim consumed |
|---|---|
| `/Users/ember/dev/minidregg/Theory/PrivateTrace.lean:155`, `trace_eq_of_preserved` | Preserved deterministic relation gives equal adaptive finite traces; main theorem's source pin reports no axioms |
| `/Users/ember/dev/minidregg/Theory/PrivateTrace.lean:215`, `flip_trace_eq_of_highR`; `:221`, `highR_zero_five` | Honest nontrivial byte relation and distinct admissible states |
| `/Users/ember/dev/minidregg/Theory/PrivateTrace.lean:351`, `search_recovers`; `:371`, `no_policy_recovers_seven` | Arbitrary-offset recovery and universal seven-observation lower bound; not re-proved |
| `/Users/ember/dev/minidregg/Assurance/ReleaseGateRouting.lean:322`, `settlement_is_binding_gate` | Existing kernel Settlement pins released base by type |
| `/Users/ember/dev/minidregg/Assurance/ReleaseGateRouting.lean:368`, `stage0_statement_carries_word` | Full word visible in Stage-0 statement; no witness hiding |
| `/Users/ember/dev/minidregg/Assurance/ReleaseGateRouting.lean:399`, `stage0_released_output_forced` | Descriptor plus public boundary forces wrapped sum; used directly in new arithmetic theorem |
| `/Users/ember/dev/minidregg/Assurance/ReleaseGateRouting.lean:488`, `stage0Receipt_is_bound_evidence` | Existing deployed-check reflection and FS soundness pair |
| `/Users/ember/dev/minidregg/Compiler/CommittedTerminalFiatShamir.lean:621`, `gateProof_fs_sound_reading` | Classical lazy-ROM failure event and query accounting; Unit witness, not private-state extraction |
| `/Users/ember/dev/minidregg/Compiler/CommittedTerminalFiatShamir.lean:725`, `Stage0.stage0Receipt_price`; `:748`, `Stage0.stage0Price_value` | Fixed-context full-word price `(t+14)*4160/2013265921^6`; arithmetic factor bound is not a whole-system security level |
| `/Users/ember/dev/minidregg/Compiler/CommittedTerminalFiatShamir.lean:831`, `encodeMove_injective`; `:875`, `FsReceipt` | Existing transcript codec theorem and exact receipt carrier extended here |
| `/Users/ember/dev/minidregg/Kernel/FinalityGate.lean:86`, `check`; `:159`, `checked_transaction_unique_at_slot` | Exact-vote quorum checker; prefix-disciplined safety through that checker |
| `/Users/ember/dev/minidregg/Kernel/ReplicatedSettlementFinality.lean:127`, `PrefixDiscipline` | Cross-epoch compatibility requirement; not Byzantine security inferred from quorum intersection alone |
| `/Users/ember/dev/minidregg/Kernel/DurableCommitProtocol.lean:117`, `Snapshot`; `:151`, `Snapshot.install`; `:179`, `Snapshot.install_consumes` | Actual durable carrier and monotonic consumption update used in restore proof |
| `/Users/ember/dev/minidregg/Kernel/DurableCommitProtocol.lean:266`, `Intent.nullifiersFreshCheck` | Actual consumed-token check used by the proposed adapter |
| `/Users/ember/dev/minidregg/Kernel/FinalityLiveness.lean`, §2–4 | Safety/liveness split and closed carrier witnesses read; no new availability theorem or deployment model inferred |

## Repository evidence and priority

[SOURCE: notes read] `README.md`, `docs/VERDICTS.md` (especially §3/§7.5),
`SLVG_THOUGHT.md` §I–II, `notes/README.md`, the handoff then companion, and the landed
route/trace/routing notes supplied the starting state. VERDICTS was not modified.
The two scope refinements in `CANDIDATES.md` are proposals for the maintainer; the
existing central truth file remains authoritative. The downloaded handoff and repo
copy differ in provenance preamble/formatting; the companion's corrections and
remaining-work list governed the continuation.

[SOURCE: rules read] Companion `CLAUDE.md`, `ATLAS.md` §6–7 and
`scripts/check-import-boundary.sh` supplied the patch discipline. The discovery
instrument `rg --files ... -g AGENTS.md` found no companion AGENTS.md; its root
CLAUDE/ATLAS instructions were read instead. This absence claim is only about that
local file inventory, not about other instructions or repositories.

## Autonomous swarm additions: root discovery, 2026-09-06

[EXECUTED] Root used **1 Scry SQL query, 0 new schema calls, 0 Kagi queries** for
updatable/homomorphic/reusable FE discovery. The schema was reused from the HE
lane. `experiments/results/scry_updatable_fe_01.json` retains SQL, complete result,
duration and source coverage; Scry reported `spend_nanodollars=0`. Root then used
one web search and opened two publisher pages to resolve the exact papers. The
search result is discovery metadata only. Other lanes keep separate counts in
their own source manifests; checkpoint totals follow below.

| ID | Primary source / pinned local file | Access and scope |
|---|---|---|
| [SOURCE] AIT-UFE | `/Users/ember/dev/gh/forks/IACR-eprint-mirror/2016/1179.pdf`, SHA256 `4b60ee7dca5ff2e0346205af88f180b74fbba544a06b222f67e5ac61c4edcf86`; [publisher](https://link.springer.com/chapter/10.1007/978-3-319-61273-7_17) | Local §3 pp.9–15: syntax, displayed selective game, construction and complete proof outline; Figure 9 p.17 transition circuit; §4 future work. Extra DI-obfuscation sampler requirement is a source assumption, not a reduction verified by us. |
| [SOURCE] CUFE | `/Users/ember/dev/gh/forks/IACR-eprint-mirror/2022/1284.pdf`, SHA256 `30e8daf540902da9c2e386cf9326a3bf1b2cba28e06a6f4effc03671f0f64e52`; [published full text](https://link.springer.com/article/10.1007/s00145-023-09486-y) | Published §1.1, §3 Definition 5 and §5.2 read: one-hop access-tag changes, master-issued update tokens, lattice/ROM branch. Local PDF extracted/pinned; full lattice reduction not audited. |

[EXECUTED] `experiments/recovery_policy/source_reads.json` records local extraction
commands and text hashes. No PDFs were downloaded; ignored extracted text can be
regenerated from the absolute mirror paths. `CANDIDATES.md` records the scoped
closure/migration consequence and the displayed-game exposure residuals.

## Swarm source and execution register

[EXECUTED checkpoint accounting, 2026-09-06 04:46 EDT] Six Scry SQL queries and two
schema calls were recorded: private construction 3+1, HE 2+1, parent 1+0. Returned
spend was zero; Kagi queries were zero. Primary web reads/fetches and local corpus
reads are distinct from those metered queries and are listed in the lane registers.
No secret key was printed and no eprint PDF was downloaded.

| Register | Actually inspected / executed | Boundary |
|---|---|---|
| [SOURCE/EXECUTED] PRIVATE_CONSTRUCTION.md; experiments/private_construction/sources_manifest.json | Local 2015/017 Construction 3.1/Theorem 3.2 and §6; 2015/608 §4.1/§4.2; DDH implementation and insecure LWE equation controls | Selective initial-vector game versus adaptive/stateful issuance distinguished; no full resident/QPT reduction |
| [SOURCE/EXECUTED] experiments/private_construction/RLWE_AUDIT.md; results/rlwe_source_results.json | Local 2021/046 §2.3/§4/§5 and 2023/721 §3.4; pinned author repositories, literal PRG call sites and extracted native decoder | Native full build fails on AVX2/arm64; source findings and isolated decoder execution do not establish a full exploit or working scheme |
| [SOURCE/EXECUTED] HE_CLOSURE_COSTS.md; experiments/he_closure_costs/ | Pinned fhe-dregg/fhe-math source, TFHE-rs1.6.3 Boolean EMA, exact BFV window; local 2024/463 parameter guidance and pinned Apple tables | Source-equation noise bound, actual ciphertext controls and table assumptions separated; pinned estimator follow-on completed with exact model/attack census in estimator/AUDIT.md |
| [SOURCE/EXECUTED] BFV_LIFT_REFINEMENT.md; experiments/bfv_lift_refinement/engine-run.json | Actual breadstuffs dependency paths and hashes, integer/extension/scaling code and retained full fixtures; primary SEAL source comparison | Independent literal source-model match and Lean scalar refinement; NTT/Rust lowering and encrypted relation binding unproved |
| [SOURCE/EXECUTED] INTEGER_CERTIFICATE_EMISSION.md; formal/integer_certificate_emission/VALIDATION.md | Existing weighted/range gadgets, Emit/DescriptorEval/checker/CSE; generated small/full 109-bit descriptors | Kernel-proved universal relations and small inhabitant; large positive assignments are compiled checks |
| [SOURCE/EXECUTED] RANDOMNESS_COMPOSITION.md; experiments/randomness_composition/source_manifest.json | Local 2025/330 Def 4.3–4.5 and Thm 6.9 context; exact ciphertext-tuple cache; actual companion FS reduction | No unbiased-delivery consequence inferred from rFE; new uniform-field ROM composition is a separate local theorem |
| [SOURCE/EXECUTED] DURABLE_INTEGRATION.md; experiments/durable_integration/results/review.json | Actual Materialized/ValidatedPatch/DataIntent/Candidate/execute paths; positive full-preflight witness and retained broken siblings | Mathematical atomicity/prefix assumptions are not a physical handler implementation |
| [SOURCE/EXECUTED] ADAPTATION_UTILITY.md; experiments/adaptation_utility/model_manifest.json | Cached SmolLM2-135M pinned revision/license/model card/runtime and 673 synthetic model prompts; disjoint controls and integer audits | Local plaintext synthetic utility, not protected execution or broad language-model evaluation |
| [SOURCE/EXECUTED] ADVERSARIAL_REVIEW.md; experiments/adversarial_review/ | Independent Lean overlays, source-pinned packet/collision/ROM/BFV checks and executable arithmetic controls | Each review pins its own source hash; later source edits require a new matching record |

[DERIVED provenance discipline] These pointers reuse the lane's exact source
register rather than copying a second set of version claims. Full extracted paper
texts and vendored/runtime build trees are ignored; hashes, extraction/build
commands, relevant source excerpts with attribution, finite results and failure logs
remain reviewable. Absence statements in lane notes name their actual local corpus
and search instrument; none is a literature-wide impossibility claim.

## Second checkpoint additions

[EXECUTED accounting, 2026-09-06 06:00 EDT] Completed private-construction work
adds five SQL queries to its first register: cumulative eight SQL and one schema.
HE remains two SQL/one schema and parent UFE one SQL. Completed totals are
**11 Scry SQL and two schema calls; Kagi zero**. The initial PQ audit adds no
Scry calls, four web searches and three HTML opens. Active continuation lanes
record their own later calls; these counts do not silently include unfinished
searches. No eprint PDFs were downloaded.

| Register | Actual source/evidence access | Scope |
|---|---|---|
| [SOURCE/DERIVED] experiments/private_construction/FINITE_LADDER.md | Local 2013/729 Def 2.4, Remark 2.5, Lemma 2.9, §4 syntax and Thm 4.1; root independently read Appendix C footnote 8 | Classical fixed-H2 conditional induction; joint future-package exposure; no practical implementation |
| [SOURCE/DERIVED/EXECUTED] experiments/private_construction/PREDICATE_CLOSURE.md | arXiv 1302.1192v2 predicate-preserving operations; local 2025/361 Construction 1/Thm 3.1; 2007/404,2016/691,2015/029 named algorithms/games | Static predicate positive, scoped update/known-state probes and exact syntax limitations |
| [SOURCE/DERIVED/EXECUTED] experiments/private_construction/RFE_RECURRENCE.md | Local 2025/330 Def 3.8/4.3, Construction 2 and Thm 6.1; 2012/733 and 2013/729 randomness/timing syntax | Fixed-coin compatibility obstruction is not a cryptographic break |
| [SOURCE/DERIVED] PQ_COMPOSITION.md; experiments/pq_composition/source_manifest.json | Seven local PDFs, fourteen extraction/pdfinfo calls; 2025/2215 main theorem, auxiliary-input definition, algorithms/reductions and named dependencies | Conditional PQ primitive, literal correctness mismatch, quantum residual-state/extraction obligations |
| [EXECUTED] experiments/adaptation_utility/representation_PROTOCOL.md and representation_audit.json | Preregistered extraction locations, selection, held-out histories and independent aggregate audit | Local synthetic utility; teacher-only feature transforms and held-out selection distinguished |
| [SOURCE/EXECUTED] experiments/adaptation_utility/encrypted_window/results.json | Frozen fixture, actual pinned Rust source/dependency files, original reference implementation and 96 score comparisons | Real encrypted arithmetic with full test reader and public reproducibility coins; no new utility population estimate |
| [SOURCE/EXECUTED] formal/bfv_lift_refinement/source_certificate/REPORT.md and target_projection/REPORT.md | Source-model scalar equations, compiler Emit/simplification and actual Rust coefficient fixtures | Exact deterministic correction and three-limb projection; separate input provenance and Rust lowering |
| [EXECUTED] experiments/integration/results/run_009/report.json | 39 modules,499 exact theorem pins, four umbrellas, source-copy patch application and both import-boundary instruments | Existing dependency oleans; no companion edits or clean rebuild |

[EXECUTED parent review] experiments/recovery_policy/finite_ladder_review.py/json
pins all four H2 artifacts and independently enumerates all 15 two-step adaptive
policies. It confirms the 14 behavioral classes on 32,640 distinct-state pairs and
checks that the same private pair fails at a longer horizon. This is an ideal
interface audit and source-premise review, not a cryptographic reduction proof.

## Final collection and interrupted-source register

[EXECUTED] Completed metered total is 12 Scry SQL plus 2 schema calls, Kagi0.
The additional query is private-ingress provenance (one SQL,25 rows,reported
spend0); its exact response is retained. No new network query or PDF download
was made by the parent during final collection.

[SOURCE/EXECUTED] The provenance source manifest reconstructs five exact local
PDF/extract pairs:2020/137,2016/629,2023/268,2019/238 and 2023/629. The last was
abstract-only; construction/game access for the others is stated in the note.
Their pdftotext -layout bytes were reproduced exactly during collection. The
2025/330 source was already registered in the parent ingress audit. The final
independent provenance review was interrupted; these are scoped delegated
source readings, not a verified resident composition.

[EXECUTED] Final source/proof collection: experiments/integration/results/run_011/report.json
records 49 modules,651 exact pins, all four umbrellas, actual patch application
and both import-boundary checks. The final guarded horizon witness was checked
without changing its proof body. Source-phase 45 and modular-word38 are included;
unpinned mixed-journal and failing source-window successors are excluded.

[EXECUTED] Independent journal review is experiments/adversarial_review/persistent_journal/REPORT.md.
It pins original/repaired protocols, both full runs and a separate concurrent
retry-after-install schedule. QIND finite controls are retained against the
exact pre-closeout draft snapshot; final review/primitive instantiation remains open.

## Third overnight source/evidence checkpoint — 2026-09-08

[EXECUTED] Root's `experiments/end_to_end/overnight_checkpoint_002.py/json`
rehashes392 public source/evidence files across ten inventories. It reuses saved
execution reports without running cryptography or reading private runtime state.
The public-coin journal, emitted/runtime controls, sealed replay failure,
independent reviews and proposed full-UD sources are included.

[SOURCE/DERIVED] Exact source locations and access depth for ALS IPFE and nearby
transparent constructions are in
`experiments/private_construction/public_setup_pq/notes/SOURCES.md` and its
SOURCE_MANIFEST. The fixed-coordinate QPT derivation has a separate independent
review. Its finite regularity derivation uses MP2011/501 and GPV2007/432, including
prime-power subgroup counts, not a prime-field hashing shortcut. The cost note
retains source equations and the exact public integer script. These are source
and mathematical artifacts, not an implemented PQ cryptosystem.

[EXECUTED source accounting, completed first source tranches] Capsule audit:
eight web queries/two Scry SQL; initial PQ setup audit:eight web queries/four
Scry SQL submissions (two errors); proof-frontier orientation:four web queries,
one Scry SQL/two schema,11 direct web operations and nine GitHub API reads.
Finite regularity:two web discovery queries, zero Scry. Later alternatives and
finite-reduction lanes are still active and keep their own counters; these
figures are not a final nightly aggregate. No eprint PDF was downloaded.
