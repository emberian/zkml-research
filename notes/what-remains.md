# What remains — checked against the first commits, not recalled

2026-08-13. Ember: *"seemingly nothing we identified initially was actually
worthwhile?"* Checked against `git log --reverse` and the artifact list.

## The premise is half right, and the half that is right is specific

**What died is the NOVELTY framing.** The original agenda carried an
"unclaimed-claims ledger" and a stance section arguing "the open position is
vacant, not crowded." **Essentially every entry in that ledger was refuted** —
MoE router binding, proof-aware QAT, the MX exponent measurement, the
registry-as-open-position, the vacuity instruments, the boundary principle,
`fold_add`-as-one-opening, the prime family. Not one of those survived as
"first."

**What did NOT die is the technical content**, and it is worth separating:
- **Pillar I** (bit-exact formats): the *bf16 thesis was refuted by our own
  harness in the first three commits* — and the exactness *requirement*
  survived intact, with a better reason than we started with (no ε for an
  adversary to steer, which is Zamir's non-composability applied).
- **Pillar II** (audit game): **survived and became an artifact.**
- **Pillar III** (registry): **framing dead** (four groups had it; ours can't
  be opened by a prover), **need real**, re-spec known.
- **Pillar IV** (vFHE): **converged rather than died.** Transciphering,
  bootstrapping and scheme-switching are all closed *with reasons*, which
  narrowed the target to something buildable — and the coefficient matmul got
  built.
- **Pillar V** (verified artifacts): verified table contents still undone; the
  vacuity instruments turned out to be standard practice with a 25-year
  literature.

## What is actually on disk from this window

**Lean, kernel-checked, zero `sorry`:** `Selvage/AuditSampling.lean` ·
`Theory/CyclotomicInertia.lean` · `Assurance/TwoRegimeQueryBudget.lean` ·
`metatheory/Bfv/Ring.lean` · (plus the `Selvage` rename landed end-to-end).

**Rust, tested:** `fhegg-fhe/src/bfv_coeff_matmul.rs` + oracle tests ·
`fhegg-fhe/tests/kpz_encoding_depth.rs` (a *constructive* falsifier) ·
**`fold-opening/` — a whole crate with a bench and a
`fold_is_an_opening` test** · `sumcheck-toy` (recon, and debt to delete).

**Measurements that repriced things:** sumcheck is **2–17%** of prover time ·
the exchange rate **3,120 mults per committed felt at lb=4 vs ~40 to
virtualize** · deployed depth is **2** · the deployed noise expansion is the
**proven δ_R = N** · `lb=6` is **2.9× off** the measured optimum · 100 proven
bits costs **86 queries with the commit phase unchanged**.

**Well-priced dead ends** — transciphering, bootstrapping, scheme-switching,
Celer, the 109-bit joint prime, delegation-instead-of-a-ring-hash. **These are
not failures; they are months not spent**, each with the number that closed it.

**A simplification that shrank the plan**: the multilinear seam is **one RBR
instance**, not a new abstraction — and the route runs through two theorems we
already hold that turn out to be *the same operator*.

## The method finding, which is the real answer

**An agenda organized around "what is unclaimed" produces refutations. An
agenda organized around "what would the best system do" produces artifacts.**

Every one of the five best things in this window — the audit theorem, the
exchange rate, the prover-floor derivation, the seam simplification, the
coefficient matmul — came from **doing a measurement or writing a proof**, and
**four of the five were not on the initial list at all.** The initial list was
a *parameter-selection* document (which format, which field, which hash), and
parameter selection turned out to be either already settled by others or
lower-impact than believed — because, as the floor derivation showed, the
parameters move terms that are 2–17% of the cost.

## So: what remains

**A narrower, buildable programme with its dead ends already priced, five
machine-checked artifacts, a decision rule nobody else has (the exchange
rate), and one open question whose answer is a profiling run.** That is less
than the agenda promised and more than it would have produced, because the
agenda was measuring the wrong thing.
