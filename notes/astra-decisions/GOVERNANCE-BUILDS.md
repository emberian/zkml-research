# Bridge, device home, and Mac packages — supporting recommendations

2026-11-06. These are recommendations, not executed changes. `[READ]` means source or another lane's recorded result inspected; `[MEASURED]` means a read-only measurement performed in this study; `[INFERRED]` means my judgment. No builds or machine changes were performed.

## 6. Which bridge ledger, and what happens to the vacuous certificates?

**Question:** What justifies joining a Lean theorem to CakeML's HOL4 compiler theorem, and should the three impossible-premise demos survive?

**Options.** [READ] A accepts the identification of the Lean and HOL definitions as an explicit trusted assumption. B proves each statement that reaches machine code again inside HOL4. A's proposed middle form also compares the statement printed into HOL; this checks which statement is being discussed, but supplies no HOL proof. See `/Users/ember/dev/degg-research/research/BRIDGE-KNOT.md:405` (§4.2).

**Recommendation.** [INFERRED] Choose **B at the machine-code boundary**, keeping the Lean development and automation. Re-prove the two concrete serve branches first; do not port the approximately 20,000 supporting Lean lines. Continue using A-labelled, conditional research results while those proofs are unfinished. The current small device already demonstrates the shape of B. This policy gives a stranger a single checked chain at the boundary where the project promises machine-code behavior. I would not turn the printer's remaining semantic identification into a permanent ledger assumption merely because there are already other assumptions about hardware and external calls: those assumptions answer different questions.

[READ] The same-printer bug is concrete: replacing signed word comparison with unsigned comparison passed structural and equation checks and failed selected vectors (`BRIDGE-KNOT.md:56`, §1). Contracts substantially improve this, but the generic literal/binder/case printer and the relative uniqueness argument remain trusted (§4.1, lines 374–402). The current reverse device has its own HOL proofs, including `commit_before_forward` and `stepS_refines`: `/Users/ember/dev/DreggNet/docs/engine/probes/p3-bridge/reverse/hol/chokeProofScript.sml:70` and `:95`. Neither A nor B removes the unfinished connection from function evaluation to whole-program compiler premises (`BRIDGE-KNOT.md`, §4.2).

[INFERRED] **Repair, do not discard, the three useful demos.** Change their certificates to “for every state satisfying P” where P binds the inputs and satisfies the memory/scoping conditions. Reuse `RefinesClk`/`RefinesClkPan`; do not create another refinement framework. Supply an explicit state satisfying P, a successful nonconstant run, and a counterexample with an unbound input. Retire the old impossible-premise certificate interfaces when the replacements land; keep `wf_reading_local_uninhabited` as a regression theorem.

[READ] `/Users/ember/dev/breadstuffs/orb-compiler/Pancake/LadderPanSem.lean:468` proves that the universally bound-local premise is impossible; `ProofProducing.lean:288` still uses it. `EmitCorrectClock.lean:75` already defines the state-conditioned form. The three names are `redirectStatusStage`, `httpStamp`, and `crlfStamp`; this finding does not invalidate the separate HOL stage certificates.

**What would change my mind / cost of being wrong.** [INFERRED] If a measured prototype of the two HOL top-rung proofs requires reconstructing the full compiler proof infrastructure, I would accept A plus statement comparison for an explicitly conditional release. B risks slower iteration and two specifications drifting; bind the HOL statement to the emitted concrete program and compare the statements. Keeping A permanently risks presenting an independently unchecked identification as a formal composition.

## 7. Where should the chokepoint live, and what is the CakeML route?

**Question:** Should runnable device definitions remain in a research experiment or become a maintained minidregg component?

**Options.** [INFERRED] Keep research as the canonical source; move the device into minidregg; or maintain two copies. The third option buys recurring drift and has no compensating benefit here.

**Recommendation.** [INFERRED] Make **minidregg the sole canonical home** of the step function, encoding, proofs, and exported entry point. Give it a small core-only build target: moving the source should not force a full minidregg or Mathlib build for a three-second device check. Keep research results and the explanation of the deployment assumptions in degg-research. Point the HOL exporter, Microkit integration, and host adapter at the same canonical source; retire the old source copy after import paths and build consumers are connected.

[READ] This is already one implementation split across repositories: `/Users/ember/dev/degg-research/experiments/chokepoint-step/README.md:17` and `check.sh:11` compile minidregg's `Compiler/Blake3.lean` directly. The device exports `dregg_chokepoint_arrive`; its core is first-order and its summary-state refinement is proved. `/Users/ember/dev/degg-research/research/CHOKEPOINT-VEHICLE-DECISION.md`, “Export-friendliness commitment” and “Next steps,” explicitly preserve that portable core and propose minidregg as its permanent home.

[INFERRED] **Keep the Lean-compiled deployment, as decided.** Treat CakeML as a separately gated compiler improvement, not a reason to postpone the working route or redesign the device. Its next evidence must be the actual summary step compiled for the target architecture, an entry/exit wrapper matching the compiler theorem, and an external-call contract implemented by the Microkit adapter. Then compare output bytes on the existing vectors and demonstrate persist-before-forward under a bad persistence acknowledgment. Compiler correctness does not prove that the host executes outputs in order or that a device has no bypass path.

[READ] `BRIDGE-KNOT.md:289`–§4 describe the reverse route: reflected definitions, HOL re-proofs, and CakeML translator certificates. Its §6 still lists machine-code compilation plus a Microkit `main` as unfinished. The requested `experiments/chokepoint-step/CAKEML-ROUTE.md` was absent when inspected; `cv show --frozen 78fef112-a52f-425f-8503-f3fa24ff087c --agent a99f1d45 --last 14` ends with the lane naming that note as its next task. Thus there is no completed route comparison here to endorse. The existing vehicle note names the unresolved FFI and entry-point questions; it is not evidence of their resolution.

**What would change my mind / cost of being wrong.** [INFERRED] A maintained standalone device package with real external consumers could justify an independent home. Today minidregg owns the runtime-facing primitives and avoids a cross-repository research dependency. The migration risks breaking source paths, toolchain assumptions (the experiment pins Lean 4.33.1), and bridge generation. A small independent target and byte/theorem checks at those consumers contain that cost. Do not turn a source move into an unreviewed compiler migration.

## 8. What should replace the shared Mac Mathlib cache?

**Question:** Keep, delete, or replace a shared writable package tree used by incompatible Lean toolchains?

**Options.** [INFERRED] Repair the current shared directory in place; delete it; or move consumers to separate immutable stores keyed by their dependency manifest and Lean toolchain. Choose the last. **Preserve the old files and stop using the cross-toolchain links after the replacement is proven.** Neither in-place repair nor deletion solves incompatible writers.

[READ] I checked the active iteration lane's transcript and its Mac helper first. The requested `/Users/ember/dev/redregg/landscape/ITERATION-SPEED-2026-11-06.md` did not yet exist. `cv show --frozen 78fef112-a52f-425f-8503-f3fa24ff087c --agent ae3d964b --json`, message 99, identifies the link graph and intended replacement; `cv show --frozen 78fef112-a52f-425f-8503-f3fa24ff087c --agent a54b413f` records the implementation and tests. The helper has already created `/Users/ember/tools/lean-packages/lean-packages`, keyed by `SHA256(lake-manifest.json || lean-toolchain)` (first 12 hex characters), with separate stores for 4.30 and 4.35. Its stored `ensure-bs.log` and `ensure-md.log` report matching headers, respectively 8,105 and 8,643 Mathlib artifacts; these are the lane's results, not my build measurements.

[MEASURED] My read-only census returned **5,964 of 8,776** artifacts with the 4.35 commit header, rather than the question's earlier 5,969. The exact command and full aggregate output are below. The link graph still connected minidregg's Mathlib to breadstuffs' and then through `~/src/mathlib4` to breadstuffs-codex. The two root `lean-toolchain` files read 4.35.0 and 4.30.0 respectively. [INFERRED] These observations establish incompatible shared artifacts, not which particular process wrote each file.

**Recommendation.** [INFERRED] Finish the helper's isolated trials, including ordinary `lake lean`/`lake build` dependency checks, then coordinate switching each shared root to its matching store. Preserve the existing package directories/links as rollback material and leave `~/src/mathlib4` intact for unconverted consumers. Precompute required package metadata before freezing stores; otherwise use a per-consumer writable overlay for metadata, never make shared compiled artifacts writable again. Verify full manifest/toolchain identity, not only the short directory name; add architecture/target and native-library identity for any cache that carries native code between machines.

[READ] The helper is **not yet a finished drop-in repair**: at inspection its `trial/timings3.log` had failures in `CertifiedInterval` and `Conservation`; the latest transcript traced these to permission-denied writes to build metadata inside the frozen store. `Theory/Noun` passed. The lane subsequently warmed missing hash metadata with a writable store and was still checking the repair. Direct `lake env lean` passing earlier did not establish that ordinary dependency rebuilding worked. Do not announce this migration complete on header checks alone.

**What would change my mind / cost of being wrong.** [INFERRED] If immutable stores cannot support normal Lake workflows economically, use separately keyed writable package copies per worktree. The extra disk and warmup cost is preferable to recurrent contamination. A premature switch breaks active builds; deleting the old tree can destroy another session's work. This research performs neither action.

### Read-only census record

[MEASURED] Command (2026-11-06):

```sh
python3 -I /Users/ember/tools/lean-packages/olean-census.py /Users/ember/dev/breadstuffs/metatheory/.lake/packages/mathlib/.lake/build/lib/lean
```

Output:

```text
   5964  eb6cafb7290e8bd5f2937522d8d804f58f02bafc  mtime 2026-10-30 08:15 .. 2026-10-30 08:29
   2812  d024af099ca4bf2c86f649261ebf59565dc8c622  mtime 2026-07-17 13:01 .. 2026-11-06 09:46
```

[READ] The helper's `ensure-md.log` identifies `eb6caf…` with its Lean 4.35 build; `ensure-bs.log` identifies `d024af…` with 4.30. No query to a paid search service was needed for these repository and local-build decisions.
