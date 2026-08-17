# Artifacts — what is on disk, where, and in what state

Surveyed 2026-08-16. Every path absolute. State is one of:

- **landed** — committed, referenced from a note, reproducible.
- **partial** — real work, incomplete or uncommitted.
- **orphaned** — the work exists; its pointer does not. ⚑ These are the ones
  this file exists for.
- **superseded** — replaced by something better, kept as history.

## ⚠ TWO STRATA — and this file's own headline changed

Unmarked entries are the **2026-08-16** survey. Entries tagged **`[08-17]`**
were re-measured on **2026-08-17**, after ~42 further commits.

⚑⚑ **The single most important update: O1 was FIXED, and the class it belongs
to RECURRED WITHIN A DAY.** `~/src/ring-ro-hash` is a git repository now — and
it already holds **696 lines of untracked work written today.** The remediation
worked and did not stick, which is the same shape O2 records about
`IntegerFingerprint.lean` (found once, remediated with a table row).

> ⚑ **And the orphan count went UP, not down.** O1 closed; **O5 is new and
> larger** — **1,593 lines of committed Lean that `lake build` has never
> compiled**, of which we knew about **one file of three.**

**Second-stratum orphan ledger, in one place:**

| | 08-16 | 08-17 |
|---|---|---|
| O1 `~/src/ring-ro-hash` not a git repo | ⚑ 25 files at risk | ✅ **fixed** (2 commits) — ⚠ **696 new untracked lines, same day** |
| O2 `Theory/IntegerFingerprint.lean` | orphaned (in the build, no write-up) | **unchanged** |
| O3 three claude.ai memos | URLs nowhere | **unchanged** |
| O4 uncommitted units | 2 notes untracked, 3 files `MM` | ✅ notes committed; ⚠ **the `MM` was a STALE INDEX, not an edit** |
| **O5 unrooted committed Lean** | *not detected* | ⚑ **3 modules, 1,593 lines, orphaned at HEAD** |

---

# ⚑ Read this section first — the orphans

Four kinds of orphan, in descending order of what is at risk. **`[08-17]`** a
fifth was found, and it is the largest.

## O1. `/Users/ember/src/ring-ro-hash/` — **not a git repository**

25 files, 216 KB, all written 2026-08-13 between 11:07 and 15:51 — a single
4.7-hour session. **No `.git`. No remote. No backup through git anywhere.**
This holds the design and cryptanalysis of the ring-native
arithmetization-friendly hash, which is the campaign's most original
construction (`02-LANDSCAPE.md` §1.4).

**Nothing it computes is persisted.** There is no results file, no log, no
output of any kind in the directory. Every number lives on stdout from
`run_all.sh`.

⚑ **And the rescue copy is partial in exactly the wrong way.**
`/Users/ember/dev/zkml-research/notes/ring-hash-scripts/` holds **10 of the 25
files**, byte-identical (`cmp` clean). **15 were left behind, including
`run_all.sh` — the only reproduction driver — and every one of the 13 scripts
it actually invokes.** The rescue copied the seven `design_*.py` plus
`costmodel.py`, `density_repricing.py`, `sigma_poseidon.py`, and left behind
everything needed to *run* them.

**Not copied**: `avalanche.py` · `branch.py` · `conditions.py` ·
`decomp_direction.py` · `frog.py` · `galois_span.py` · `msis_correction.py` ·
`order_check.py` · `sbox_law.py` · `slot_diffusion.py` · `system_impact.py` ·
`run_all.sh` · `RingHashPlan.lean` · `RingSponge.lean` · `__pycache__/`.

> **If `~/src/ring-ro-hash` is deleted, the committed copy cannot be executed.**

⚠ It also carries a **hard cross-repo dependency out of an unversioned
directory**: `run_all.sh` shells into `~/dev/minidregg` and elaborates
`RingSponge.lean` with `lake env lean`. And `RingSponge.lean` /
`RingHashPlan.lean` are in **no repo at all**.

⚑ **Three of the seven `design_*.py` scripts self-identify as a "revival lane,
2026-08-13"** — so this directory was *already itself a recovery effort* before
it became an orphan again.

What the seven design scripts compute, since none of it is written up outside
`notes/ring-hash-design.md`:

| script | what it establishes |
|---|---|
| `design_branch_frontier.py` (17.7 KB, largest) | The branch laws. For `L = Σ_{k∈K} c_k σ_k`, `branch(L) = \|K\|+1` exactly; composite with free R_q-MDS across t elements measures `t + \|K\|` (MDS **adds** t−1, does not multiply); the dense layer is Cauchy-programmable slot-MDS by theorem. ⚑ **The price of support is halved** — because σ₅ and σ₋₁ both appear in one R1CS row, support s costs `ceil((s−1)/2)`, not `s−1`. |
| `design_branch_law_check.py` | Extends the `t+\|K\|` law. The frontier script measured only t=2, where the law *coincides* with 2\|K\| at \|K\|=2 — so the evidence was thinner than it read. Splits into a constructive exact upper bound and an exhaustive lower bound, each row labelled EXHAUSTIVE vs partial against a work budget. |
| `design_ceiling_decomposition.py` | Why the gadget-Feistel (92,257) beats a peer's "perfect ring sponge" ceiling (~1.4e5). **Not a modelling slip**: `rows/element = (rows/permutation)/(elements absorbed/permutation)`, so a design can win on rate *and* on permutation cost; the ceiling holds the second factor at Poseidon's. |
| `design_gadget_feistel.py` | The MSIS-Feistel candidate, developed: R_q = Z_q[X]/(X^16+1), gadget base B=2^16, K=4 planes, state (L,R) ∈ R_q^4 × R_q^4, t=8, rate 7, capacity 1 element = 1024 bits. Bijectivity checked at full Frog-class parameters with explicit inverse and roundtrip. |
| `design_mds_interleave.py` | How few dense slot-MDS rounds suffice, on four axes: composite support as boolean matrix products, MDS-ness sampled + exact-to-cap at d=8, slot diffusion of the real nonlinear permutation, cost per absorbed element at t=9, RF=8, RP=22, α=7. |
| `design_subfield_invariance.py` | ⚑ The τ=4 risk made concrete as a checkable **invariant subspace**: at τ=4, `x^α` maps F_q into F_q and Frobenius fixes F_q pointwise, so both layers preserve `V = {states whose every slot lies in F_q}` (dim 4 of 16). Yields **design condition C6**: σ-layer coefficients and round constants must not lie in the base field. |
| `design_tau_tradeoff.py` | Puts the τ=1-vs-τ=4 fork on one axis (rows per absorbed element; baseline to beat 716.8). **Cost half only — the security half is prose in `notes/ring-hash-design.md` §4 and was never scripted.** |

**Recommended first action for whoever picks this up**: `git init` in
`~/src/ring-ro-hash`, or copy the remaining 15 files into
`notes/ring-hash-scripts/`. Ten minutes. Currently one `rm -rf` from
unreproducible.

### ✅⚠ `[08-17]` DONE — and the class came straight back

**`git init` happened.** Toplevel `/Users/ember/src/ring-ro-hash`, **2
commits**: `7eeb35b` *"version the design scripts, which were one rm -rf from
unreproducible"*, then `737ea7b` *"weft_branch: [WEFT-subspace] settled"*.
**28 source files, 4,253 lines, 26 tracked entries.** `run_all.sh` and every
script it invokes are now in it.

⚑ **And the settling instrument for the Weft kill lives only here**:
`/Users/ember/src/ring-ro-hash/weft_branch.py` — **456 lines, 20,794 bytes**,
committed at `737ea7b`. **It exists nowhere else on the system** (searched
`~/src` and `~/dev`). Every branch number in `03-MEASUREMENTS.md` §1.11 and
`04-DEAD-ENDS.md` §D7 comes out of that one file in that one repo.

⚠⚑ **THE CLASS RECURRED THE SAME DAY. Three files, 696 lines, untracked,
written 2026-08-17 between 01:28 and 02:54:**

| file | lines | what it is |
|---|---:|---|
| `post_weft_branch.py` | 332 | the successor-design branch work, after Weft died |
| `xhash_m31_branch.py` | 258 | XHash-M31 — **the candidate §1.3b's Kagi sweep concluded we should ADOPT** |
| `mark32_sysrs_branch.py` | 106 | Mark-32 / Vision-family branch numbers |

> **The newest hash work in the campaign — including the measurements on the
> family the Kagi sweep recommends adopting — is unversioned.** The
> remediation for O1 was applied and then not repeated for the next four hours
> of output. ⟨inference⟩ The lesson is not "run `git init`" — that was done —
> it is that **a one-shot remediation does not create a habit**, and the only
> durable fix is a commit step inside whatever loop produces these.

⚠ **`[08-17]` And the "rescue copy" is now a TWIN, not a rescue.** All **10**
of the shared files in `notes/ring-hash-scripts/` are **byte-identical copies
(md5-verified)** of `ring-ro-hash` files: `costmodel`, `density_repricing`,
`design_branch_frontier`, `design_branch_law_check`,
`design_ceiling_decomposition`, `design_gadget_feistel`, `design_mds_interleave`,
`design_subfield_invariance`, `design_tau_tradeoff`, `sigma_poseidon`. The only
content unique to `zkml-research` is `dual_mode_costs.py` (40 L) and
`dual_mode_modsearch.py` (31 L), committed at `297a389`.
⚑ **Two shapes that agree today are two shapes that will disagree later** —
the house doctrine, and it now applies to this directory. **Prefer deleting the
copy and pointing at the repo.**

## O2. `/Users/ember/dev/minidregg/Theory/IntegerFingerprint.lean` — the 476-line file

**476 lines, 28 theorems. Exact match on both numbers.** Two commits, both
2026-08-12: `2047207` ("state the integer relation and its random-prime
fingerprint") and `7d24e4f` ("record Limber's two field obstructions and its
Table 3 gap").

It **is** in the build — `Theory.lean:63`:

> `import Theory.IntegerFingerprint  -- the Zaratan/Limber integer relation`
> `a*b = c + u*m` and its random-prime fingerprint: counting core proved,
> prime-counting denominator left as a named hypothesis`

**State: landed in Lean, in the build, no write-up.** No note in
`~/dev/zkml-research/notes/` matches it. It appears in exactly two markdown
files:

1. `notes/ingredient-inventory.md:276` — one cell of a table row it shares with
   `Theory/Bignum.lean` (377 lines, 22 thms) and `Theory/CrossModulus.lean`
   (207 lines, 13 thms). Names `Row`, `fingerprint_complete`, and
   ⭐`adaptive_quotient_defeats_fingerprint`.
2. `swarm/BRIEF-TEMPLATE.md:86` — **which cites it as a recovered orphan, not
   as documentation.**

⚑ **So it was found once, and the only remediation applied was a table row.**
That is worth pausing on: the orphan-detection worked and the *repair* did not.

Its two table-row neighbours are equally thin. And its provenance matters — it
is the Lean scaffold from the **Limber (eprint 2026/1635)** deep read, one of
the papers ember hand-dropped on the Desktop.

## O3. Three claude.ai decision memos whose URLs appear **nowhere**

Verified: `grep -rn "claude.ai/code/artifact"` across `~/dev/zkml-research`,
`~/dev/minidregg` and `~/dev/breadstuffs` returns **zero hits** other than this
file and `02-LANDSCAPE.md`.

| memo | URL | what it holds |
|---|---|---|
| **Field-choice decision memo, v4** | `https://claude.ai/code/artifact/d671d644-87e3-4e51-b711-459e74c620e5` | ⚑ Recommends **"KoalaBear everywhere. Keep binary towers as the committed second field. Not Goldilocks, not M31, not the BFV limbs."** Argues BabyBear's only edge is two-adicity 27 vs 24 — *a property FRI consumes and sumcheck does not* — against the cost that `3 \| p−1` forces a degree-7 S-box. |
| **Hash frontier decision memo** | `https://claude.ai/code/artifact/1167978c-21a9-4c43-94e3-75e1c1c46adc` | The Poseidon3 / Poseidon2b / EF-initiative adjudication, with 23 papers pulled to `~/paperbin`. |
| **The prover speed floor, from first principles** | `https://claude.ai/code/artifact/ea569fc8-5482-4d9c-85f1-9d8003d6124c` | *"The prover is hash-bound at every blowup ≥ 2, and the floor is hashing too — the wall and the floor are the same object."* Script + output survive at `paper/scripts/prover_floor.py`; the derivation does not. |

⚠ **`swarm/BRIEF-TEMPLATE.md:86` says "two claude.ai decision memos."** There
are **three.** The orphan record itself undercounted, which is a small, exact
instance of the class.

⚑ **The field memo is the highest-stakes orphan in the repo**, because it says
the opposite of `docs/VERDICTS.md` §1b. See `02-LANDSCAPE.md` §1.1 — VERDICTS
is current truth and the memo is history, but the memo's *reasoning* is
outweighed, not refuted.

## O4. Uncommitted units nobody named

| what | where | state |
|---|---|---|
| **The "uwueave preo projection v2" unit** — Lean spec + generated Rust + test, one coherent change | `minidregg/Compiler/UwueavePreoProjectionV2.lean` (113 L) · `prover/generated/uwueave_preo_projection_v2.rs` (49 L) · `prover/tests/uwueave_preo_projection_v2.rs` (117 L) — plus modified `Compiler.lean`, `Selvage/MultilinearExtension.lean`, `prover/src/lib.rs` | ⚑ **untracked, all mtime 2026-08-11 17:40–17:43, untouched for five days.** Appears in **no** zkml-research note. This is a complete unit sitting outside git since before the campaign proper started. |
| Two notes from the last day | `zkml-research/notes/basis-binding.md` (95 L, 08-16 21:09) · `notes/sumcheck-batched-opening.md` (56 L, 08-16 21:12) | **untracked.** The newest content in the repo, written by live sibling lanes in the same three minutes as the first `forcodex/` commits. ⚑ `basis-binding.md`'s own first finding is that **its brief's file path was wrong.** |
| Three partially-staged files (`MM`) | `breadstuffs/circuit-prove/tests/leaf_vs_recursion_sweep.rs` · `fhegg-fhe/src/bin/ntt_four_step_bench.rs` · `fhegg-fhe/tests/kpz_encoding_depth.rs` | **staged AND unstaged changes on top of the last commit**, in exactly the leaf-vs-recursion and FHE-NTT lanes. ⚠ A bare `git commit` by any lane commits the *staged* halves. |

### `[08-17]` O4, re-measured — one row resolved, one row diagnosed

- ✅ **The two untracked notes are committed.** `notes/basis-binding.md`
  (`96a56e9`) and `notes/sumcheck-batched-opening.md`
  (`b458936`…`0232918`). Both were complete, not cut off — which answers a
  question the 08-16 survey left open at the bottom of this file.
- ⚠⚑ **The three `MM` files are a STALE INDEX, not partial work — and that is
  worse in a specific way.** Re-measured: **all three have worktree content
  byte-identical to HEAD**, and the staged and unstaged diffs are **exact
  inverses** (−12/+6 then +12/−6). Nothing is half-done; the index simply
  never refreshed.
  > **A bare `git commit` by any lane would not commit "the staged half of
  > someone's work" — it would RESURRECT a 6-line-shorter variant of the
  > measurement harness that nobody wrote today.** That is the recorded
  > shared-index mass-revert hazard, in its quietest form: the diff is small,
  > the file compiles either way, and the harness would just measure something
  > slightly different.
  **Left untouched** (a synthesis lane must not unstage another lane's index).

## `[08-17]` O5. ⚑ 1,593 lines of committed Lean that `lake build` has never compiled

**The largest orphan in the repo, and two thirds of it was undetected.**

`minidregg`'s `lakefile.toml` sets `defaultTargets = ["Minidregg"]` and **no
`lean_lib` declares `globs`** — so every library roots *solely* at its
`<Name>.lean` umbrella file. A module the umbrella does not import is not built,
not checked, and not in any axiom sweep. **At HEAD: 484 `.lean` files, 475
reachable, 9 unreachable — 6 are intentionally standalone `scripts/*.lean`, and
three are not.**

| module | lines | committed | orphaned since |
|---|---:|---|---|
| `/Users/ember/dev/minidregg/Compiler/EvmAddAir.lean` | **722** | `8c5a732`, 2026-08-17 | landing day — **and it was declared at landing** (`docs/VERDICTS.md` §3d) |
| `/Users/ember/dev/minidregg/Compiler/ZkmlTraceCheck.lean` | **580** | `3f90089`, 2026-08-13 | ⚑ **four days, undetected** |
| `/Users/ember/dev/minidregg/Compiler/ZkmlEltwiseAir.lean` | **291** | `3f90089`, 2026-08-13 | ⚑ **four days, undetected** |

⚑ **The mechanism is `minted-caller-committed-callee-not`, inverted**: the
*callee* was committed and the *caller* was not. `git show HEAD:Compiler.lean |
grep EvmAddAir` → **no match**; the worktree's `Compiler.lean:98` has the
import. Commit `8c5a732` landed the module, `Theory.lean`,
`Theory/EvmFragment.lean`, `Theory/EvmResidual.lean` and the descriptor JSON —
**but never `Compiler.lean`.** `3f90089` did the same thing four days earlier,
touching five files, none of them the umbrella.

⚠ **And the umbrella edit CANNOT be committed on its own to fix it.** The dirty
`Compiler.lean` adds **four** imports and the dirty `Selvage.lean` adds one; **two
of those five point at untracked files**:

- `Compiler.UwueavePreoProjectionV2` → `Compiler/UwueavePreoProjectionV2.lean`
  (113 L, **untracked** — the same unit O4 records as sitting outside git since
  2026-08-11)
- `Selvage.HashRelationInverse` → `Selvage/HashRelationInverse.lean`
  (303 L, **untracked**)

> **Committing the umbrellas as-is breaks the build; committing them without
> those files breaks the build; leaving them dirty leaves 1,593 lines
> unchecked. The knot has to be untied with the two untracked files, and only
> their author knows whether they are ready.**

⚑ **Why this matters more than a missing import**: `ZkmlEltwiseAir.lean` holds
`addDemoDescriptor_means_denotation`, and `EvmAddAir.lean` holds
`evmAddDescriptor_means_semantics` and the kernel-decided shape theorem that
`03-MEASUREMENTS.md` §1.12 quotes. **Those theorems are cited as landed and no
default build has ever elaborated them.** A `sorry`, a broken import or a
degraded `decide` in any of the three would be **invisible to every gate we
have** — which is precisely the class `minted-behavioural-evidence-cannot-see-a-proof-hole`
records, arriving through the build graph instead of through a proof.

**Cheap detection, and it should be a gate**: compare the transitive import
closure of the default target against the tracked `.lean` file list. It is one
script, it runs in seconds, and it would have fired on 08-13.

---

# 1. `/Users/ember/dev/zkml-research` — the research repo

Branch **`dev`** only (there is no `main`). HEAD at survey time
`d4efd0ca` → now moving as this handoff lands. **180 MB. 266 commits, all
inside the campaign window** — first commit `6df8cbf`, 2026-08-12 09:43. The
repo is exactly coextensive with the campaign.

`.gitignore` is two lines (`__pycache__/`, `*.pyc`), so `vendor/` is untracked
by **omission**, not by rule.

## `docs/` — 18 files, 3,884 lines. The current-truth layer.

| lines | file | note |
|---|---|---|
| 788 | `docs/VERDICTS.md` | ⚑ **The single densest file in the repo. Read it before anything else.** No history, no ⚠ markers, no superseded claims — that is deliberate (`01-STEERS.md` §6). |
| 414 | `docs/COST-MODEL.md` | the phase model everything checks into |
| 374 | `docs/BINARY-POSITION.md` | |
| 353 | `docs/AGENDA.md` | |
| 220 | `docs/SELVAGE.md` | |
| 218 | `docs/FRONTIER-QUEUE.md` | |
| 196 | `docs/COMPOSITIONS.md` | produced by the "I don't care what's ours" steer |
| 176 | `docs/mx-formats.md` | |
| 163 | `docs/the-position.md` | |
| 143 | `docs/bf16-exact-arithmetization.md` | |
| 130 | `docs/SYSTEM.md` | *"we did not arrive at a faster prover, we arrived at a different STATEMENT"* |
| 127 | `docs/PHASE0-RESULT.md` | the 1.4× negative |
| 122 | `docs/DARK-TRAINING.md` | |
| 110 | `docs/HARDWARE.md` | |
| 95 | `docs/PHASES-AND-TENSOR.md` | |
| 93 | `docs/LEAF-VS-RECURSION.md` | |
| 88 | `docs/INGREDIENTS.md` | |
| 74 | `docs/RESEARCH-STANCE.md` | |

⚠ **Nothing in `docs/` was touched on 08-15 or 08-16.** Newest is
`COST-MODEL.md` at 08-14 20:07. The last two days of work are in `notes/` and
`forcodex/` only, so **`docs/` does not reflect the final state.**

## `notes/` — 101 files, 31,453 lines. The evidence layer.

Largest fifteen:

```
1692  multilinear-pcs-landscape.md      858  boundary-statements.md
1451  koalabear-migration.md            829  gkr-substrate-design.md
1204  binaryspartan-position.md         807  moe-router-binding.md
1078  ring-hash-design.md               675  spartan-over-what-we-hold.md
1077  ingredient-inventory.md           650  leaf-vs-recursion.md
1036  hash-landscape.md                 634  inspiration-sweep-pl.md
 888  fold-as-opening.md                624  inspiration-sweep-cc.md
                                        604  grind-phase.md
```

⚑ **The mtime distribution is the campaign's shape.** The bulk land 08-12
23:57 → 08-14 13:49, then **a two-day silence with zero note activity**, then
the two untracked orphans on 08-16. The note corpus stops when the credits
ran out.

- `notes/archive/` — 8 files, all ≤ 08-13 17:47. **Superseded by design**;
  its README says plainly *history, not truth; do not cite.*
- `notes/hash-landscape-scripts/` — one file, `crossover.py` (8.7 KB).
- `notes/ring-hash-scripts/` — 10 files. **See O1: this is a partial rescue.**

## `paper/` — landed, then stopped

`CLAIM-LEDGER.md` (19 KB) · `DRAFT.md` (32 KB) · `HONEST-ASSESSMENT.md` ·
`PRIOR-ART-COLLAPSE.md` · `SUBMISSION-GATES.md`. **All mtimes 08-13 12:38 →
15:14 — the paper thread ran for under three hours and nothing after touched
it.** State: **partial.** The red-team pass forced two claims to change and
those changes landed; the draft was never revised past that.

`paper/scripts/` — 8 files, tracked:

```
koalabear_limb.py       27.5 KB   ← largest; 41/41 checks
prover_floor.py         24.0 KB   ← the memo's script (memo itself orphaned, O3)
lattice_estimate.py      7.3 KB
verify_candidate.py      7.7 KB  + verify_candidate.out  ← the ONLY persisted output
poseidon2_virtualization.py 7.6 KB
boundary_exchange_rate.py 5.2 KB
tower_table.py           3.3 KB
```

⚠ **Seven scripts, one output file.** Six of them persist nothing — their
numbers exist only in whichever note quoted them.

## `phase0/` — 120 MB, of which 119 MB is data

| item | state |
|---|---|
| `phase0/bf16_tables.py` + `results_bf16_tables.txt` | **landed** |
| `phase0/cost_model.py` + `results_cost_model.txt` | **landed** |
| `phase0/e8m0_spread.py` + `results_e8m0_spread.txt` | **landed** — the 100%-of-1,382,400-rows measurement |
| `phase0/v0_to_v1.py` | **partial** — no paired results file; emits `mnist-trace-v1.json` (2.3 KB) |
| `phase0/product_exact/` | **landed** — a real Rust crate, `src/main.rs` 413 L, results one level up |
| `phase0/h2-rns-vs-single-prime/` | **landed** — Rust crate, 957 L across 3 files, **with its own in-crate `results_2026-08-13_m2max.txt`.** The H1/H2 measurement. |
| `phase0/data/` | 119 MB of safetensors headers + 8 `.u8` expert-scale blobs from gpt-oss layers 0/5/11/17/23 |
| `phase0/catgrad-proving-backend.rs.txt` | ⚠ **a `.rs` file saved as `.txt`** — a captured artifact, not a build target. Easy to mistake for dead code. |

## `registry/` — 9.6 MB. **Landed and rejected.**

`registry_tool.py` is **48 KB, the single largest script in the repo.** Plus
`gates.sh`, `run_registry.sh`, `COMMITMENTS.md`, `MANIFEST-FORMAT.md` (24 KB),
`README.md`, `WHAT-THIS-IS-NOT.md`, **8 manifests** (Qwen3-8B, gpt-oss-20b,
Qwen3-0.6B, Llama-3.1-8B-Instruct, gemma-3-27b-it, gpt-oss-120b, DeepSeek-V3.1,
Kimi-K3) and **27 run records** including a 50 KB `MASTER.log`.

⚑ **All mtimes 08-13 12:37 → 14:18 — the whole lane ran and finished in about
100 minutes and was never touched again**, because ember rejected the object
the same evening (`01b-STEERS-RECOVERED.md` §22). **State: landed, correct as
code, wrong as an object.** A SHA-256 manifest commits to weights in a way no
prover can open. `docs/VERDICTS.md` §5 names the right object; nobody built it.

⚠ `registry/runs/deepseek-ai__DeepSeek-V4.gated.log` exists with **no
manifest** — that is the HTTP 404 finding (`02-LANDSCAPE.md` §3.6).

## `swarm/` — 4 files

`PREFLIGHT.md` (the hazards file — **read it before touching anything**) ·
`BRIEF-TEMPLATE.md` (§9 is the HANDOFF RULE and §7b is the "upstream is a
temptation" clause) · `WORKSTREAMS.md` · `OPEN-QUEUE.md`.

## `vendor/` — 34 MB, **untracked, and both are nested git repos**

Not submodules — nested `.git` directories, so they are **invisible to the
parent repo's history.** Both cloned in one event, 08-13 18:41.

- `vendor/moma/` — 10 MB. GAP/SPIRAL-family source (`mxpmethod.gi` 79 KB,
  `rewrite.gi` 57 KB, `cuda/`, `examples/`).
- `vendor/morph/` — 24 MB. Python crypto-kernel codegen/profiling
  (`multiscalar_multiplication_context.py` 96 KB, `finite_field_context.py`
  41 KB, `number_theory_transform_context.py`, `profiler.py`, `c_kernels/`).

⚠ **Both were later dropped from the tensor thread** — MoMA does not use tensor
cores at all, MORPH's GEMM is base conversion for 256–753-bit moduli
(`docs/VERDICTS.md` §4b). **State: superseded**, but retained. I did not read
their `.git/config`, so I cannot say whether they are re-cloneable.

---

# 2. `/Users/ember/dev/minidregg` — the Lean artifact repo

HEAD `e4037255` ("selvage: the heterogeneous-stack seam Reduction cannot
type"). **3.9 GB. 502 commits in the campaign window.**

Commit-touched directories in-window: `Selvage` 131 · `Assurance` 106 ·
`Compiler` 56 · `Kernel` 34 · `Theory` 31 · `Loom` 24 · `prover` 18 ·
`native` 17 · `scripts` 15 · `docs` 14.

⚑ **The log has a visible texture change.** The top ~12 commits are
prose-titled research commits (selvage / spartan / ligerito / char-2 /
BaseFold). Everything below `e087a5d` is machine-cadence proof engineering
("normalize…", "expose…", "lift…", "reduce…") — hundreds of them, all on the
BaseFold / RO-freshness / transcript-coupling thread. **That earlier band is
not part of this campaign**; do not read it as such.

| directory | `.lean` files | lines |
|---|---|---|
| `Selvage/` | 132 | 63,876 |
| `Assurance/` | 119 | 54,430 |
| `Compiler/` | 100 | 40,598 |
| `Theory/` | 59 | 25,518 |
| `Kernel/` | 47 | 23,802 |

**Global census: 50 raw `sorry` tokens across non-`.lake` `.lean` files; 0
top-level `axiom` declarations.** ⚠ The 50 is a raw grep and does not separate
live proof holes from comments or strings — treat it as an upper bound and
check with `#print axioms`, which is the discipline this tree actually uses.

## The campaign's Lean deliverables

Theorem counts are `grep -c '^\s*\(theorem\|lemma\)'` — **lower bounds**; they
miss `private`/`protected`/same-line-attribute declarations.

| file | lines | thms | state |
|---|---|---|---|
| `Theory/CyclotomicInertia.lean` | 1,184 | 88 | **landed** — the family law, 67-digit counterexample. Cited from `paper/DRAFT.md`, `CLAIM-LEDGER.md`, `SUBMISSION-GATES.md`, `PREFLIGHT.md`. |
| `Selvage/AuditSampling.lean` | 1,173 | 49 | **landed** — the commit-then-audit theorem, first machine-checked one we can find. 20 axiom pins, all clean. Carries the fail-open wound class *as a theorem*. Ten named residuals still open. |
| `Assurance/TwoRegimeQueryBudget.lean` | 950 | 37 | **landed** — regime in the *type*; three regimes, and the withdrawn capacity one is unrepresentable. Every cell kernel `norm_num` over ℚ; no `native_decide`, no `#guard`, no floats. |
| `Selvage/AdditiveBaseFold.lean` | 838 | 44 | **landed** — 13 `#print axioms` pins, all `[propext, Classical.choice, Quot.sound]`. |
| `Assurance/ZkmlLowRankUpdate.lean` | 758 | 45 | **landed** — 21 clean axiom pins. |
| `Selvage/LigeritoInterleaved.lean` | 567 | 20 | **landed** — dependency surface is three imports. |
| `Selvage/Rank1GradientCheck.lean` | 551 | 32 | **landed** |
| **`Theory/IntegerFingerprint.lean`** | **476** | **28** | ⚑ **ORPHANED — see O2** |
| `Selvage/HashFamily.lean` | 420 | 16 | **landed** |
| `Theory/ZkmlMatmulSum.lean` | 375 | 19 | **landed** |
| `Selvage/CharTwoWall.lean` | 279 | — | **landed** — the char-2 trap closure |
| `Selvage/HeteroComposition.lean` | 254 | — | **landed** — 0 sorry, 4 axiom pins |
| `Selvage/BinaryLookup.lean` | 165 | 11 | **landed** |
| `Selvage/EqPolynomial.lean` | 155 | 11 | **landed** — came in at 11 theorems rather than the 3 estimated; the adjacent facts fell out free |

## `[08-17]` The second stratum's Lean deliverables

**All re-measured on disk at minidregg HEAD `820f0cb`. Every file below: 0
`sorry`, committed, clean.** ⚠ The handful of raw `sorry` grep hits in
`LigeritoInterleaved`, `SpartanR1CS` and `AirSumcheckCubic` are **docstring
prose claiming "no `sorry`"** — checked line by line. `pins` = `#guard_msgs …
in #print axioms` sites.

| file | lines | pins | commit | state |
|---|---:|---:|---|---|
| `Selvage/AccRbrFold.lean` | **1,448** | 16 | `bc29222` 08-17 | **landed** — folding at the commitment alphabet; the norm wall tight both ways |
| `Compiler/TwistMultisetInvariant.lean` | **679** | 8 | `820f0cb` 08-17 | **landed** — Nebula Lemma 2, both directions |
| `Selvage/MultisetFingerprint.lean` | **372** | 5 | `820f0cb` 08-17 | **landed** — the sharp `max(\|A\|,\|B\|)·(k+1)/\|F\|` bound |
| `Assurance/TwistMemoryFingerprintJoin.lean` | **238** | 4 | `820f0cb` 08-17 | **landed** — the join; sole importer of the Compiler file |
| `Compiler/EvmAddAir.lean` | **722** | 5 | `8c5a732` 08-17 | ⚑ **ORPHANED — see O5** |
| `Theory/EvmFragment.lean` | **281** | 3 | `8c5a732` 08-17 | **landed** |
| `Theory/EvmResidual.lean` | **276** | 3 | `8c5a732` 08-17 | **landed** — the TV theorem is literally `rfl` |
| `Selvage/AdditiveBasisBinding.lean` | **483** | 15 | `9679a16` 08-16 | **landed** — the ordered-basis binding, closed both directions |
| `Compiler/Tower256AdditiveFriController.lean` | **718** (was 428) | 12 | `9679a16` 08-16 | **landed** — +300 lines, the `basisPrefix` splice |
| `Compiler/Tower256AdditiveFriRawDeployment.lean` | **289** | — | `9679a16` 08-16 | **landed** |
| `Selvage/HashRelation.lean` | **342** | — | `c2dd38c` 08-16 | **landed** — the relation view; its first build's pin caught a `decide` degraded to `sorry` |
| `Selvage/DecomposableTable.lean` | **437** | 6 | `feef028` 08-16 | **landed** — Lasso's decomposition + a *general* non-decomposability theorem |
| `Selvage/RingSwitching.lean` | **791** (was 568) | 19 | `37c6b33` 08-16 | **landed** |
| `Assurance/AirSumcheckCubic.lean` | **650** | — | `37c6b33` 08-16 | **landed** — the cubic partial-sumcheck rung |
| `prover/testdata/evm_stage0_add_descriptor.json` | 4,154 L / **231,487 B** | — | `8c5a732` 08-17 | **landed** — Lean-written, ⚠ **no Rust-side reader test yet** |

⚑ **A convention correction that matters when you read any pin count in this
directory**: **minidregg has NO `#assert_axioms` machinery at all.**
`Kernel/Camera.lean:30` says so outright — *"minidregg has no `#assert_axioms`
yet — that tool is Assurance-lane territory."* What minidregg uses is
`#guard_msgs (whitespace := lax) in #print axioms`, which is equivalent in
force and **invisible to any sweep that greps for `#assert_axioms`.**
⚠ **breadstuffs is the other convention** — `metatheory/Bfv/*.lean` carry
`#assert_all_clean` and `#assert_namespace_axioms`. **A cross-repo audit that
uses one repo's grep on the other will report a false zero.**

⚠ **`[08-17]` Two line counts in the table above this one are stale, and both
grew rather than drifted**: `Selvage/AdditiveBaseFold.lean` is **856**, not 838
(`9679a16` added 24, removed 6); `Selvage/RingSwitching.lean` is **791**, not
the 568 it landed at. **The 838 and 568 are landing figures**, correct as
history and wrong as inventory — which is the same two-strata problem this
whole directory has, one level down.

⚑ **Near-orphans — rooted, but with an umbrella as their ONLY importer and
zero downstream consumers.** These are not broken; they are *unconsumed*, which
is the state just before O2's: `Selvage/LigeritoInterleaved.lean` ·
`Selvage/DecomposableTable.lean` · `Selvage/AccRbrFold.lean` ·
`Assurance/SpartanR1CS.lean` · `Assurance/TwistMemoryFingerprintJoin.lean` ·
`Compiler/TwistMultisetInvariant.lean` (whose sole importer is the Assurance
join, **not `Compiler`**).

⚠ **Rooted only via UNTRACKED files** — these vanish on a clean checkout while
the umbrellas that need them get committed:
`Selvage/HashRelationInverse.lean` (303 L) · `Compiler/UwueavePreoProjectionV2.lean`
(113 L). See O5.

⚠ **`Theory/ZkmlOps.lean` does not exist.** The zkML vocabulary is spread
across `Theory/ZkmlTensorOps.lean` (1,011 L, 27 thms — ⚑ **referenced from
exactly one note**, `notes/zkml-build-log.md`, the thinnest pointer of the
set), `Theory/ZkmlMatmulSum.lean`, `Compiler/ZkmlTraceCheck.lean`,
`Compiler/ZkmlEltwiseAir.lean`, `Selvage/ZkmlPoseidon2Data.lean`,
`Selvage/ZkmlSuiteRegistry.lean`, and **eight** `Assurance/ZkmlMatmul*.lean`
files (`Checker`, `Commitment`, `AuditTurn`, `BaseFold`, `Sumcheck`,
`Conformance`, `FramedWal`) plus `ZkmlLowRankUpdate`. **If you are looking for
"the zkML module", there isn't one.**

Also thin-or-unreferenced, found while hunting O2 (⟨inference⟩ these are
probably *not* campaign artifacts — 7–9 theorems each — but nothing points at
them): `Compiler/DeclaredActionAir.lean` (507 L, 0 refs) ·
`Assurance/SemanticAdditiveFriCheckpoint.lean` (499 L, 0 refs) ·
`Compiler/BignumKernelABI.lean` (468 L, 0 refs).

## `minidregg/prover/src/bin/` — 4 binaries

- `low_rank_commit_cost.rs` (11.4 KB, 08-14) — **counts only, no clock in the
  file**, by design.
- `rank1_gradient_bench.rs` (10.0 KB, 08-13)
- `native_dispatch_bench.rs`, `sparse_equality_bench.rs` (both 08-09) —
  **pre-campaign.**

---

# 3. `/Users/ember/dev/breadstuffs` — the deployed system

HEAD `8983bd9ca` ("rig: the grind cell had stopped falsifying, and hbox was
running the SCALAR Poseidon2"). **70 commits in window.** Touched:
`metatheory` 102 · `circuit` 94 · `circuit-prove` 31 · `fhegg-fhe` 24 ·
`poa-web` 20 · `scripts` 11 · `vendor` 6 · `sumcheck-toy` 4.

## Measurement instruments — all landed

| file | lines | mtime |
|---|---|---|
| `circuit/tests/ir2_field_op_counts.rs` | 2,245 | 08-14 06:38 |
| `circuit/tests/hbox_rig.rs` | 1,707 | 08-14 13:48 |
| `circuit/tests/grind_phase_measure.rs` | 1,464 | 08-14 02:02 |
| `circuit/tests/fri_blowup_global_knob_survey.rs` | 1,103 | 08-14 02:20 |
| `circuit-prove/tests/recursion_tower_profile.rs` | 939 | 08-14 06:19 |
| `circuit-prove/tests/leaf_vs_recursion_sweep.rs` | 514 | 08-14 13:44 ⚠ `MM` |

⚑ **`hbox_rig.rs` (13:48) and `leaf_vs_recursion_sweep.rs` (13:44) on 08-14 are
the last two files the measurement lane ever touched** — the same hour as the
last note (`notes/hbox-rig.md`, 13:49). That hour is where the campaign stops.

The rig enforces `COST-MODEL.md`'s four rules **by construction**: counts and
clock are separate arms, and `Counts` has no duration field.

## Build and FHE artifacts

| file | lines | state |
|---|---|---|
| `fhegg-fhe/src/gpu_arena.rs` | 1,763 | **landed** — 9 device sites → 1 |
| `metatheory/Dregg2/Circuit/Emit/Poseidon2RoundGates.lean` | 1,565 | **landed** — `permEmissionNarrow` (§8, +842 L): 352 → 141 gates, degree 7 pinned on both emitted arms |
| `fhegg-fhe/src/bfv_coeff_matmul.rs` | 1,238 | **landed** |
| `fhegg-fhe/src/bin/ntt_four_step_bench.rs` | 1,129 | ⚠ `MM` |
| `metatheory/Bfv/Ring.lean` | 510 | **landed** — the noise model lifted to the ring |
| `metatheory/Bfv/CrossLimb.lean` | 453 | **landed** — the hole exhibited; `#assert_namespace_axioms Bfv` 90 → 113 |
| `fhegg-fhe/tests/kpz_encoding_depth.rs` | 356 | ⚠ `MM` |

⚠ **`metatheory/Bfv/` has 8 files and only 2 were touched in-window.** The
other six (`Fold`, `Mul`, `Noise`, `NoWrap`, `Params`, `Smudging`) are July,
pre-campaign. See `swarm/PREFLIGHT.md` for the corrected claim about which of
them are in a build target — **the uncorrected version of that claim was
quoted by a later lane before anyone checked.**

### `[08-17]` breadstuffs, re-measured

| file | lines | git | commit | `sorry` | pins |
|---|---:|---|---|---:|---|
| `metatheory/Bfv/Ring.lean` | 510 | clean | `36dd4578e` | 0 | 3 `#assert_all_clean` sites / **25 decls** |
| `metatheory/Bfv/CrossLimb.lean` | 453 | clean | `5b653ba5d` | 0 | 3 sites / **23 decls** |
| **`metatheory/Bfv/ZqSumcheck.lean`** | **407** | clean | `c4c1e5835` | 0 | 3 sites / **22 decls** |

✅ **All three are FULLY ROOTED** — `Bfv` is a `defaultTarget`, `metatheory/Bfv.lean`
imports all three, and **its import list is byte-identical in HEAD and
worktree.** ⚑ *No orphan question here, in deliberate contrast to O5* — and the
difference is that this repo's umbrella was committed in the same commit as its
modules.

⚑ **The `#assert_namespace_axioms Bfv` ladder is the campaign's cleanest
progress metric**: **90 → 113** (CrossLimb, `5b653ba5d`) **→ 137**
(ZqSumcheck, `c4c1e5835`) kernel-clean theorems.

⚠ **But the namespace sweep still does not reach everything**: `Bfv/Mul.lean`
and `Bfv/Smudging.lean` are **not imported by `Bfv.lean`** — orphans *within*
the library, exactly as `swarm/PREFLIGHT.md`'s corrected entry describes. They
are rooted through `Market` and carry their own per-file `#assert_all_clean`,
so they are checked; the **namespace-wide** sweep is what is incomplete.

**The Rust measurement harnesses, re-measured** — all committed, and cargo
auto-discovers all five (no `autotests = false`, no `[[test]]` stanzas):

| file | lines | `#[test]` | `#[ignore]` | runs by default |
|---|---:|---:|---:|---:|
| `circuit/tests/hbox_rig.rs` | 1,707 | 6 | 4 | 2 |
| `circuit/tests/ir2_field_op_counts.rs` | 2,245 | 14 | **0** | **all 14** |
| `circuit/tests/grind_phase_measure.rs` | 1,464 | 7 | 2 | 5 |
| `circuit-prove/tests/recursion_tower_profile.rs` | **1,440** (was 939) | 5 | **5** | **0** |
| `circuit-prove/tests/leaf_vs_recursion_sweep.rs` | 514 | 4 | **4** | **0** |

⚑ **`recursion_tower_profile.rs` grew 939 → 1,440 lines** — that is the K16
prove-and-refuse test (`a8e8842a5`, falsifier repaired `44d0dea45`), the only
arm in the campaign that *proves and verifies through the production entry point
and then forges a cell.*

⚠ **Read the `#[ignore]` column before trusting a green CI**: **nine of the
thirty-six tests across these five files never run by default**, including
**every test in both `circuit-prove` harnesses.** The two files that carry the
tower census and the K16 proof are **entirely opt-in.**

## `breadstuffs/sumcheck-toy/` — tracked, 698 lines, **superseded**

`src/lib.rs` (278) · `tests/roundtrip.rs` (295) · `tests/folding_price.rs` (95)
· `Cargo.toml` (30). A library crate with **no binary** — its only entry points
are the two test files.

⚑ **This is the crate ember shut down**: *"why are we doing a fhe toy with
p3-sumcheck tbh though? like why do we care about p3/sumcheck at all, Selvage
doesn't...use that."* It still builds and is still in the workspace.
`01b-STEERS-RECOVERED.md` §18.

## Untracked in breadstuffs

`before-full.png` · `dp-paper-b64.txt` · `eprint2152.json` ·
`rack-after-unblock.yml` · `metatheory/wip/Measure19d.lean` (4.7 KB, mtime
**08-09** — pre-window, an orphan from an earlier session).

---

# 4. `/Users/ember/src/` — 210 entries

Every campaign-relevant checkout **is** a git repo **except `ring-ro-hash`**
(O1). Most are `--depth`-limited clones taken during the campaign.

## Proof systems

| dir | HEAD | date | depth | size |
|---|---|---|---|---|
| `sp1` | `f66b4bf` | 2026-08-12 | shallow (471) | 203M |
| `openvm` | `c65f9fa` | 2026-08-11 | shallow (200) | 54M |
| `openvm-stark-backend` | `362c7ad` | 2026-08-06 | shallow (5) | 8.7M |
| `ceno` | `ccd49f1` | 2026-08-13 | shallow | 11M |
| `risc0` | `3bbcd44` | 2026-07-20 | shallow | 391M |
| `nexus-zkvm` | `f2ad126` | 2026-01-06 | shallow | 13M |
| `expander` | `096581e` | 2026-07-20 | shallow (1) | 3.4M |
| `jolt` | `3094eea` | 2026-08-12 | shallow (6) | 36M |
| `binius64` | `45c9745` | 2026-08-13 | shallow | 10M |
| `ezkl` | `e196b11` | 2026-02-20 | shallow (1) | 475M |
| `deep-prove` | `9d1a53e` | 2026-05-26 | shallow | 1.1G ⚠ **378 dirty entries** |
| `gkr-backend` | `5c9c8a6` | 2026-07-23 | shallow | 2.1M |
| `Plonky3` / `plonky3-lookupcost` | both `a31a144` | 2026-08-05 | shallow | 572M / 318M — **same commit, different build artifacts** |
| `plonky3-recursion` | `0a4a554` | 2026-07-15 | shallow | 6.5M — ⚠ **the read-only reference copy**; the working fork is `~/dev/plonky3-recursion` |
| `leanMultisig` | `9c1d590` | **2025-07-25** | full (8) | 268K — ⚑ **a dead personal fork, empty scaffolding.** Recorded so nobody reads it as Binius-adjacent again. |

## FHE

`hpu_fpga` (`6c8b3fa`, 2026-07-21, 150M — **the Zama HPU, 553 `.sv`, 162,770
LOC under `hw/`**) · `openfhe-development` (`ed361af`, **full, 771 commits**) ·
`lattigo` v6 (`5dbffbd`) · `tfhe-rs` (`779c7c5`) · `Fheanor` (`2ba0053`, 260M,
⚠ 3 dirty) · `SEAL` · `HElib` (⚠ **2023-07-18**) ·
`swift-homomorphic-encryption` · `heir` (58M) · `concrete` · `fhe.rs` ·
`phantom-fhe` · `Pyfhel` · `HELIOPOLIS` (full, 7 commits) ·
`matvecmul` (`0037907`, full, 400M) · **`matvecmul-p61`** (`c789c8d`,
2026-08-13, full, 4 commits, 399M) — ⚑ **our own p61 fork of Zama's
matvecmul; the modulus-swap experiment.**

## ML / compilers / formal

`catgrad` (`faf053f`, 2026-05-14, 144M) · `catena-lang` (`16487c7`,
2026-08-10, 482M) · `catgrad-spike` (`253dd37`, 2026-08-13, 415M, ⚠ 1 dirty —
**the tripwire held: nothing in it was touched by the Lean work**) ·
`vllm` (`8cd174fa3`, full, 16,099 commits) ·
`ArkLib` (`9349870`, 2026-08-13) ·
`formal-proofs` (`d0dd827`, 2026-06-04, **full, 5.9 GB** — the StarkWare/Avigad
S-two AIR formalization) ·
`mathlib4` → **symlink** into `/Users/ember/dev/breadstuffs-codex/metatheory/.lake/packages/mathlib`, rev `1c2b90b130`.

⚠ **Uncommitted work that a clean checkout would lose**: `deep-prove` 378
entries · `dregg-posters` 54 · `Fheanor` 3 · `catgrad-spike` 1 ·
`formal-proofs` 1 · `matvecmul` 1.

---

# 5. `/Users/ember/paperbin` — **not a git repo**

**1,895 files, 1.5 GB.** 1,260 `.pdf`, 613 `.txt`, 11 `.html`, 9 `.md`, 1
`.tex`. **1,632 sit loose at the top level**; only 263 are foldered.

| subdir | files | pdf | txt | size |
|---|---|---|---|---|
| `paperbin/joshibot/` | 198 | 100 | 98 | 172M |
| `paperbin/uweave/` | 44 | 44 | 0 | 32M |
| `paperbin/attestable/` | 21 | 21 | 0 | 13M |

⚑ **Mtimes are entirely inside 08-10 → 08-14** — 1,081 files on 08-13 alone,
761 on 08-12. Nothing before, nothing after. This corpus *is* the campaign's
reading, acquired during it.

⚠ **It is not under version control and is 1.5 GB.** Losing it loses every
absence claim's evidence base. And note it is *not* the same thing as
`~/dev/gh/forks/IACR-eprint-mirror/`, which is the complete eprint archive
(2026→1053+) and is a separate, larger corpus.

### `[08-17]` Re-measured — and the extraction gap is bigger than it looks

**1,907 files · 1,269 PDFs · 616 `.txt`.** But ⚑ **only 452 PDFs have a
matching extracted-text file — 817 PDFs have NO text at all**, and 164 of the
`.txt` files are unpaired.

> ⚠⚑ **This re-prices every absence claim made by grepping `~/paperbin`.**
> `swarm/PREFLIGHT.md` calls paperbin *"the only durable extracted corpus"* and
> says *"all 1,218 PDFs have full text."* **They do not: 64% of the PDFs are
> grep-invisible.** A full-text sweep over this directory sees **452 papers**,
> not 1,269. **State the extracted count, not the file count, with any absence
> claim.** (`05-ERROR-CLASSES.md`'s corpus-blindness entry, one layer deeper:
> the instrument is blind *inside* the corpus it does have.)

**Twelve files newer than 2026-08-16 — 9 PDFs + 3 `.txt`**, and they are exactly
the Kagi sweep's reading list (`02-LANDSCAPE.md` §1.3b) plus the BinarySpartan
read: `2026-1656-binaryspartan-setty` · `cheaplunch-extending-freelunch-2025-2040`
(+txt) · `latticefold-l2-norm-checks-2026-721` (+txt) ·
`perrin-security-analysis-xhash-2024-605` ·
`rijmen-cryptanalytic-audit-xhash-2024-656` ·
`rpo-m31-xhash-m31-circle-starks-2024-1635` ·
`rpo-rescue-prime-optimized-2022-1577` · `xhash-security-perrin-2024-605` (+txt)
· `xhash8-xhash12-stark-friendly-2023-1045`.

⚠ **Two of those are the same paper.** `perrin-security-analysis-xhash-2024-605.pdf`
and `xhash-security-perrin-2024-605.pdf` are **byte-identical** (md5
`54ba10fc…`, both 311,445 bytes) — eprint 2024/605 fetched twice under different
names 19 minutes apart, **and only the second has extracted text.** A trivial
instance of the class the file above documents, and a reminder that
`~/paperbin`'s filenames are lane-chosen, not canonical.

---

# 6. Other repos that matter

| path | HEAD | note |
|---|---|---|
| `/Users/ember/dev/plonky3-recursion` | `52e1fab`, 2026-08-14, **16 GB** | ⚑ **Ours. The working fork.** Holds the `num_queries` pin: *"recursion FRI: the query count is CONFIGURED, not read off the proof"*. ⚠ **`breadstuffs/Cargo.toml:370-373` still pins `rev = "fc3c6df"` — the pin does not reach breadstuffs until `52e1fab` is pushed and those four lines bumped.** Dirty: `circuit-prover/Cargo.toml` modified, plus two untracked files (`shrink_symbolic_constraints.json`, `tests/emit_shrink_symbolic.rs`). |
| `/Users/ember/dev/soundcalc-lean` | `361782e`, 2026-08-13, 8.2 GB, clean | ⚠ **Not ours** — upstream symbolicsoft. Read and built green (17,049 jobs). Recent upstream commits *removed* material: "Drop the FRI and WHIR sensitivity commentary", "Remove the proof-size monotonicity theorems". |
| `/Users/ember/dev/gh/forks/IACR-eprint-mirror/` | — | The complete eprint archive, 2026→1053+. ⚑ **Distinct from the scratchpad full-text cache, which stops at 2026/777.** Every absence claim made against the cache was missing ~276 recent papers, *in exactly the window where the current binary-field work lands.* |

---

# What I could not determine

- **Whether `vendor/moma` and `vendor/morph` are re-cloneable.** I did not read
  their `.git/config`.
- **The live-vs-dead split of minidregg's 50 `sorry` tokens.** Raw grep;
  includes comments and strings.
- ~~**Whether `notes/basis-binding.md` and `notes/sumcheck-batched-opening.md`
  are complete**~~ ✅ **`[08-17]` ANSWERED: both complete, both committed**
  (`96a56e9`; `b458936`…`0232918`). They grew substantially after this survey
  saw them at 95 L and 56 L.
- ~~**Whether the `forcodex/` numbering gaps were intended.**~~ ✅ **`[08-17]`
  `08-ATTACK-BRIEFS.md` now exists**, so the run is `00`–`08` with `01b`. The
  sparseness was parallel lanes, and it closed on its own.
- **The contents of the three claude.ai memos.** I have their URLs and the
  one-line summaries their lanes returned. ⚑ **They can be read with WebFetch
  and should be, before anyone re-derives the field decision.**

### `[08-17]` Still open after the re-measure

- **Whether `Compiler/UwueavePreoProjectionV2.lean` and
  `Selvage/HashRelationInverse.lean` are ready to commit.** They are untracked,
  they are imported by dirty umbrellas, and **O5's 1,593 orphaned lines cannot
  be rooted without resolving them.** Only their authors know. **This is the
  one item in this file that blocks another item.**
- **Whether the 817 text-less PDFs in `~/paperbin` were never extracted or
  were extracted and lost.** The mtime distribution does not distinguish them,
  and it changes whether the fix is `pdftotext` over a list or an
  investigation.
- **What `~/src/ring-ro-hash`'s three untracked scripts conclude.** They are
  the newest hash measurements in the campaign — including on **XHash-M31, the
  family the Kagi sweep recommends adopting** — and no note cites them. ⚑ *This
  is O2's shape forming again in real time: work on disk, no pointer.*
