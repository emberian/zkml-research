# Source register for this tranche

[EXECUTED provenance] Run date: 2026-09-06. `experiments/results/environment.json`
records Python/OS/Lean versions, repository revisions, the initial companion dirty
state, local PDF SHA-256s and the `pdftotext -layout` commands. `source_hashes.json`
pins the cited companion source files and their available imported oleans. Source
and olean hashes are recorded separately; this is not a clean rebuild of every
upstream dependency. Lean is 4.30.0; dependencies were consumed from the existing
absolute LEAN_PATH. Nothing was installed in either companion source tree.

[EXECUTED access accounting] Kagi queries: 0. Scry queries: 0. Web searches: 0.
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
