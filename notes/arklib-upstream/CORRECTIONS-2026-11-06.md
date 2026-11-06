# Corrections, 2026-11-06: ArkLib's state-restoration and Fiat–Shamir status

Initiative 15 lane. Evidence and pins are in [GROUNDING.md](GROUNDING.md) (ArkLib `main` at
`34613d617`; open PR heads fetched read-only as local refs in `/Users/ember/src/ArkLib-fork`).
Astra's files are not edited; this note supersedes the lines below. The critique is ours and is
amended in place with a dated strike that points here.

## The fact that was missed

`ArkLib/Interaction/Oracle/Security/StateRestorationGame.lean:102`, `stateRestoration_knowledge_soundness`,
merged in #1263 (`ea6f76502`, 2026-10-08), is an ancestor of the audited SHA `4d9d67be`
(`git merge-base --is-ancestor` succeeds). It proves round-by-round knowledge soundness ⇒ state-restoration
knowledge soundness at `(Q + rounds.length) * error`, in VCVio's cached random oracle, for an adaptive
`Q`-query adversary, with arbitrary `Rin`/`Rout`. #1264 adds the per-round form `Q * max_j ε_j + Σ_j ε_j`.
The state-restoration ⇒ Fiat–Shamir bridge is open and CI-green in Quang Dao's stack #1267 → #1283
(#1277: `singleSalt_knowledge_soundness_queryBound`, `Interaction/Oracle/FiatShamir/SingleSaltSecurity.lean`).
BCS is absent in both libraries. On the shared fragment, upstream's theorem is at least as strong as Selvage's
`FsOfRbrSound` (gpt-6-astra: "the SR mathematics is duplicated").

## Lines superseded

`notes/selvage-foundations-critique-2026-11-05.md` (ours; amended in place):

| Line | Stale claim | Corrected |
|---|---|---|
| 35-41 | "The FS/BCS compilation layer is still where Selvage is ahead of both … This is the piece to keep, harden and upstream." | RBR⇒SR knowledge soundness is merged upstream with the same `(t+k)ε` and a sharper per-round bound; SR⇒FS is in review upstream. Selvage is not ahead here. Nothing to upstream; the open question is whether to retire `Depth.lean`/`FiatShamir.lean` onto upstream (initiative 15 (b)). |
| 60 | ArkLib column: "**absent** (stub; SR game in interaction layer, no bridge)" | "RBR⇒SR knowledge-soundness **theorem** merged (#1263/#1264); SR⇒FS in review (#1274/#1277/#1283); BCS stub." Selvage column: "general RBR⇒SR⇒FS in a deterministic finite-coin game; BCS only as one accumulator instance over a perfectly binding commitment." |
| 72-75 | "The compiler … accumulation depth (including the machine-checked corner refutation of a published theorem) and BCS at the deployed alphabet. Neither comparator has a reusable compiler." | `OB2_depth_composition_false` (`Selvage/Depth.lean:544`) refutes Selvage's own transcription of WARP Thm B.4 (its "specialization 7", which admitted negative `ε`), and the file says the paper never meets that corner. It is not a refutation of a published theorem. ArkLib has a reusable RBR⇒SR theorem; neither has a reusable BCS compiler. |
| 200 | "RBR→FS, BCS, state restoration, depth: **DIVERGE** (ours is ahead), and offer upstream" | "RBR→SR, FS: **MIRROR → candidate IMPORT** (upstream at least as strong on finite alphabets; bridge in progress, initiative 15 (b)). BCS: neither has it; upstream's design is `04-oracle-elimination-compiler.md`." |

`notes/astra/arklib-rigor-audit.md` (Astra's; not edited):

| Line | Stale claim | Corrected |
|---|---|---|
| 98 (§3 table, row "FS / BCS / restoration / depth") | "**DIVERGE / KEEP native** … No ArkLib soundness transport found" | Restoration: ArkLib has it (`stateRestoration_knowledge_soundness`, `StateRestorationGame.lean:102`). FS: in review. BCS: absent on both sides. |
| 130 (§4 heading) "Fiat–Shamir / BCS: retain our compiler" | | Retain only until the bridge in initiative 15 (b) lands; then decide on retirement. |
| 136 (§4, absence instrument) | Lexical search `fiatShamir.*(sound\|Sound)`, `bcs.*(sound\|Sound)`, plus reads of `OracleReduction/FiatShamir/` and `OracleReduction/BCS/` | The instrument's scope missed the native layer, `ArkLib/Interaction/Oracle/Security/StateRestoration*.lean`, whose declarations are named `stateRestoration_*`. Its conclusion ("No FS/BCS soundness declaration") is literally true for FS and BCS but was read as covering state restoration, which it does not. |
| 138 (§4) | "DIVERGE / KEEP our FS, state restoration and depth compiler; there is no corresponding ArkLib soundness theorem" | There is a corresponding state-restoration soundness theorem; see above. `:544` refutes Selvage's own unguarded statement, not a published one. |
| 149 (§5 table) "FS / BCS compiler absent → **Persists**" | | "RBR→SR knowledge soundness: present since #1263. SR→FS: open PRs by the maintainer, CI green. BCS: **persists**." |

## Method note for future absence claims

Search by mathematical object, not by expected name. A grep for `sound` near `FiatShamir` cannot
see a theorem named `stateRestoration_knowledge_soundness` in a sibling directory. Read the
library's own status file (`docs/design/00-current-status.md`) for the object's section, and list
open PRs by title and touched paths (`gh pr list`, `git diff --stat main...pr-N`) before calling
something absent.
