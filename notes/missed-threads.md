# Fresh-eyes review: what the log already contains and never synthesized

2026-08-11, Fable. Ember asked whether the research missed ideas. Reading the
whole arc back: yes — and the miss has a shape. Every iteration stayed on one
axis, "which numeric format makes per-op constraints cheap" (bf16 → fails → MX),
while the log's own strongest results were **systems results** that got filed as
side quests. The prover is a parameter. The audit game and the amortization
structure are the product.

Ranked by leverage, with the evidence already in our notes.

## 1. Sampling amortization IS the economics — we derived it, then demoted it

`E[Λ] ≤ b/q` with `q = p(1−ε_snd) − ε_bind − ε_beacon`. We derived this, the
lane confirmed *nobody writes the composition down*, and then the whole thread
got downgraded to "not a first" because the *statement* is folklore
(Rinberg et al., covert security, PoR/PDP…).

Novelty and deployability are different axes. Run the arithmetic we never ran:
DeepProve's measured prover overhead is ~24× inference. Audited at p = 1%, the
*system* overhead is `1 + 24·0.01 ≈ 1.24×` plus the always-on commitment path.
**Sampling turns a 24× prover into a ~1.24× deployment today, with existing
provers, at a proved leakage bound.** That is Attestable's actual architecture —
their blog says so — and it is why they can ship without winning the
constraint-count war. We kept trying to win the constraint-count war.

And the machine-checked version — the part that IS a first — has a proof
skeleton **already closed in our own tree**: `Loom/LightClientSound.lean` is
structurally a commit-then-audit theorem (commit to a chain, sample ONE uniform
schedule, catch any false link except with probability ≤ n·(err⋆+1/|F|), sharp,
with keystones). ⚠ 2026-08-13 correction: "a refactor, not a campaign" was too strong. Two
legs ARE machine-checked in Loom (`lightClientSound` = the checker leg,
`lightClientGrinding_sound` = a beacon leg with the try-count factor proved
necessary), but the sequential composition, stopping time, and ε_bind are
new work — the existing theorems enter as cited lemmas. See
`audit-theorem-statement.md` for the exact statement.

## 2. The memory-bubble fusion was dropped on a misread refutation

The roofline lane: batch-1 decode is memory-bound at <1% ALU utilization;
sumcheck matvec proving costs O(#weights) small-field ops — the same order as
the weight traffic inference is *already paying*; Attestable's 53 tok/s ≈ 50%
of roofline is exactly the signature of proving-costs-one-inference.

I then carried two cautions as if they killed it: GPU sumcheck is only 2.6–4.0×
over CPU, and ZK field ops use the integer pipeline whose throughput is flat
across GPU generations. **Those refute a different claim** — "GPU accelerates
standalone sumcheck." The bubble claim is about *co-location*: during
memory-bound decode the integer pipeline is idle and the operands are already
in flight, so a fused inference+witness+sumcheck kernel gets its field ops
nearly free. Nobody has costed that kernel. It is the strongest pure-efficiency
idea in the log and it never got a phase.

## 3. The deferral trick — our own crown jewel, never connected

`bridge/src/mina_accumulator_discharge.rs` — in our own tree, with a docstring
that says "**the deferral IS the innovation**": N claims collapse to ONE MSM
over |G|+N points by random linear combination, discharged natively, amortized
over a chain.

The zkML analogue is direct: don't prove each layer's matmul; accumulate RLC'd
residual claims across layers and tokens, discharge once at the end of the
chain (batched Freivalds/sumcheck). Limber's commit-then-draw-the-prime
fingerprinting is the same shape, and that lane noted the reduction itself is
"PCS-independent and free." And the formal backbone for chained accumulation —
`VerifiedHistoryHead`, `AccClaim`, fold rounds with proved recommitment — is
the machinery minidregg is best at. The tree's most distinctive trick was never
pointed at the new domain.

## 4. IVC over the decode loop — every ingredient assembled, never stated

catgrad lane: KV cache is explicit graph I/O, "exactly what you need for
per-token IVC"; one term, two circuit shapes (prefill, decode). GKR lane: below
batch ≈14 a plain AIR wins — fixed costs must amortize. Landscape lane:
Attestable's backwards batch scaling shows per-token linearity is the enemy.
Conclusion nobody drew — **CORRECTED 2026-08-12: partially drawn.**
eprint 2024/480 "Folding-based zkLLM" proposes IVC/NIVC over a RAM machine for
LLM inference (no implementation, no evaluation). What remains unclaimed: the
**KV-cache-as-accumulator-state** formulation, and any measurement at all.
Narrow the claim to those.

## 5. MX element widths make BINARY op tables total

Mentioned twice, developed never: fp8 pairs are 2^16 — a full binary-op table
is the size of our unary bf16 table. MXFP4 pairs are 2^8. At MX element widths
*two-argument* operations become single exact lookups. This compounds the MX
redirect and nobody has it (the verified-absence sweep covers it).

## 6. The inference ledger is a minidregg Hyperdocument

Rinberg's design (and Attestable's) needs a Merkle inference ledger and model
ledger. Our tree has the formally verified append-only event log, the durable
WAL handler with idempotent retry, and root-CAS discipline. The non-prover half
of the audit system is already built and verified. Nobody connected it.

## 7. Verified artifacts are worth building correctly

The tables' *contents* proved equal to the reference function's graph in Lean;
constraint semantics Lean-emitted per house law; ezkl's dead `TableOOR` check
(soundness bug in the most-cited "open" tool) as the cautionary tale. "The
lookup table is proved correct" is cheap for us, unique to us, and compounds
with every other item.

## Smaller dropped threads

- **catena-lang** — flagged "may be a better target, look before building";
  never looked.
- **Hollow-LLM registry** — called "the most defensible thing on this list";
  absent from the plan's phases.
- **Multilinear vs univariate fork** — the GKR lane said it "decides everything
  downstream"; still undecided in PLAN.md (now `notes/archive/PLAN.md`; the
  fork is settled in `docs/VERDICTS.md` §4 — materialize-vs-virtualize, with
  the route in `notes/multilinear-pcs-verdict.md`).

## The meta-error, named

Each correction in this log was *local* — fold the finding into the nearest
section, keep the axis. Nobody re-asked "is format the right axis?" after each
kill. It wasn't. The log's own evidence says the deployable system is:

**commit everything · sample audits at p (item 1) · prove sampled tokens with a
folded/deferred chain (items 3–4) · fused with inference (item 2) · over
whatever honest format wins Phase 0′ (MX, probably) · with Lean-verified
artifacts and ledger (items 6–7) · and the soundness §5 already proved.**

Format is one slot in that sentence, and it is the slot we spent the day on.
