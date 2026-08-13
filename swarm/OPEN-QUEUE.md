# The wide-open queue — everything named and unmoved (main-context sweep)

2026-08-13. Swept the full window for items we named and never progressed.
**The stalls have a shape**: things die here when they are (a) small-but-formal
(no lane feels "worth" a 200-line change), (b) deployment glue falling between
pillars, or (c) gated items whose gate silently cleared — nobody re-checks.

## A. Gates that cleared while nobody was looking
- **Phase 0′ — the MXFP4 alignment-window constraint harness.** Gated on
  "Spain/Celer reads"; both landed days ago, and the E8M0 measurement already
  answered the data side (width-8 covers 100%). **The constraint-count harness
  — the number that turns "the cheap path is the only path" into a prover cost
  — was never dispatched.** This is the zkML pillar's next measured number.
- Celer spike: gate now moot (NO-GO, see convergence note).

## B. Fully specified, high value, never dispatched
- **The two-regime security calculator** (formalization-frontier move 3):
  ErrorBudget/MixedFieldBudget/PowGrinding generalized over {regime, code,
  field, extension, grinding}, reproducing S-two's tables as Lean-computed
  two-sided bounds **with the regime tag in the type**. Everyone's "100 bits"
  problem; ours to solve; untouched.
- **The sponge re-aim: extraction-friendly indifferentiability.** Vanilla
  indifferentiability does NOT close [FS-ROM] for knowledge soundness; the
  re-aim "gets the first AND the closure." Arguably Selvage's deepest open
  formal item. Never became a card.
- **Verified table contents** — a thing worth building right, queued since week one, cheap,
  zero motion.
- **Chiesa–Orrù Corollary 1 plug** (move 2) — FRI into the state-restoration
  framework where our assets are the scarce half. Move 1 is in flight; move 2
  has nothing.

## C. Deployment glue for the audit theorem (theorem landed, deployment didn't)
- **The beacon assembly** (composition C): `pqvrf` + fhegg's threshold
  ceremonies = the G=1 threshold VUF that takes ε_beacon → 0. **Nobody has
  checked pqvrf's actual state since it scrolled past in a Cargo listing.**
- **The inference ledger** (composition 6): the audit game's Merkle ledger as
  a minidregg Hyperdocument instantiation (verified WAL + append-only log
  already exist). The registry covers weights; the per-turn ledger is undesigned.
- **AuditSampling's own ten residuals** are a ready queue — BeaconLeg/BindLeg
  realizers, and the spatial floor that is "expressible but not derived"
  (= composition J, the OracleLogLinkedOpenedSampling leg, untouched) — now
  upgraded in importance by the zkML negative (q ≤ p/N).

## D. Small-but-formal (bundle into one lane)
`num_queries` pin (a soundness fix!) · **Ext5 decision** (upgraded: three
independent sources say Ext4 is under the bar, and the pin must land before
the engine's FS rung) · the hardware rate spreadsheet (hours, "prices
everything else") · fhegg-rtl word-level BitVec verdict · G3 ring noise lift ·
G4 CPA-D/determinism hinge (the Smart–Walter analogue — a Lean-shaped first).

## E. Zero motion since first mention
**zkQMC** (2022/1007 — proving randomized computation by replacing randomness
with low-discrepancy quasi-random sequences; the mine's genuine surprise, a
direct answer to "prove the sampling was honest" that nobody has touched) ·
LoRA inference-side proving + registry deltas · layer-fold sumcheck ·
streaming prover ("70B on a 64 GB box") · proof-aware QAT · **the
catgrad-vs-catena question to hellas.ai — ember's thread, and the seam note
says it should come BEFORE committing engineering (card Z2 is where a private
clone stops being reversible)**.

## E2. Debt to DELETE, not to grow
The `sumcheck-toy` leaf crate (M0 recon) is p3 surface in our tree. It served
its purpose — the measured API facts are recorded — and it should be deleted
once the Lean-authored engine covers the same ground. Do not extend it, do not
promote it out of non-default-members, and do not let "we already have a p3
harness" become an argument for anything.

## F. Resume-from-transcript (died on credits mid-work)
KPZ encryption fix (at a num-bigint dev-dep question) · S-two carrier census
(one namespace fix from running) · ring-hash design refinement (developing the
gadget-Feistel second candidate).
