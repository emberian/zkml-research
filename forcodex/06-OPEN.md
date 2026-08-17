# What is genuinely open

**Rewritten 2026-08-17** — the first version was written before the second half
of the campaign and listed as open several things now closed. ⚠ **If you are
reading a forcodex file other than this one, `08-ATTACK-BRIEFS.md`, or
`00-ORIENTATION.md`, check its date: 02/03/04/07 are snapshots from 08-16 and
the tree moved ~42 commits since.** Live documents are
`~/dev/zkml-research/SLVG_THOUGHT.md` (shape) and `docs/VERDICTS.md` (facts).

## Closed since the first version — do NOT treat these as open

| was open | now |
|---|---|
| ordered-basis binding | ✅ **closed** — `transcript_determines_table`, FALSE before `9679a16`; the obligation had been living in a *docstring* whose only inhabitant was nine bytes spelling `"minidregg"` |
| partial-sumcheck realizer | ✅ **landed** — soundness half was already `{v d}`-generic; `RingSwitchSecure` went obligation → theorem |
| `TwistContinuity` | ✅ **discharged** — Nebula Lemma 2 both directions; the `free` gap *dissolved* (with `Option` cells, free is a write of `none`) |
| `AccRbrFold` | ✅ **landed** — norm wall proved tight at **T = 2⁴⁷** |
| wrap at K≠2 | ✅ **banked** — proves + verifies through the deployed pipeline, forged cell refuses |
| `[WEFT-subspace]` | ✅ **settled** — branch 6 exact, sketch killed as specified (⚠ **being re-opened**, see below) |
| EVM decompilation feasibility | ✅ **Stage 0 landed** — and the TV theorem is literally `rfl` |
| "is the prover hash-bound?" | ✅ **settled** — hash-bound by 5.0–7.2×, as a conditional with X exact |

## Genuinely open, ranked by what it blocks

1. ⚑ **Everything in `08-ATTACK-BRIEFS.md`** — four unrun attacks on our own
   novel constructions. **Nothing custom ships until those have answers.** The
   sharpest: *we chose τ=2 on the strength of a result measured at τ=4.*
2. **The one-handle PCS obligation** (Z_Q) — else per-limb selection reappears
   at the opening index. Blocks the zero-emulation vFHE architecture.
3. **`[TWIST-FP-BIND]`** — six named legs, the cryptographic half of the
   memory result whose combinatorial half is now proved.
4. **`[ACC-rbr-fold-resid](a)`** — the per-absorbed-commitment `ε_MSIS` home.
   ⚠ And `MsisHardEx` is *nonexistence*, proved at a toy and **expected false
   at production sizes** — the computational reading is a named residual.
5. **Weft-2** — live re-opening: branch 6 may not be disqualifying (it clears
   128 bits in two rounds with `x⁻¹`), and a **free lane rotation** breaks the
   suffix-shaped flag. **A new flag search is the open question.**
6. **The dual-mode's O2** (sponge indifferentiability) — the one wall, and it
   predates the question.
7. **H1** at the new limb primes — H2 collapsed *into* it; not independent.
8. **Knowledge soundness, tree-wide** — most soundness theorems quantify over
   a *given* witness; `Unit` extractors in places.
9. **The ℓ2 norm-check question** — our budget is ℓ∞, which
   eprint 2026/721 identifies as the *dominant prover cost*, with a modular ℓ2
   replacement. We priced the wall, never the enforcement.
10. **`max_log_arity` unpinned** in the recursion verifier — same mechanism as
    the closed `num_queries` hole. ⚠ **Direction and magnitude NOT derived —
    do not quote a number.**

## Needs ember, not a lane

- ⚑ **The `num_queries` pin does not reach breadstuffs.** Landed in
  `~/dev/plonky3-recursion` at `52e1fab`; `Cargo.toml` pins an older rev.
  **Pushing is outward-facing. Until it is pushed, the hole is open here.**
- **Whether to cut over** `permEmissionNarrow` (1.076×/batch, 1.000× in tower,
  costs a VK rotation) and the **K16 packing** (×2.011, banked, needs a
  coordinated flip because `rec4` changes the wrap's *shape*).
- **The limb-prime swap** (zero-emulation vFHE) — an FHE parameter change;
  same bit sizes, but H1 gets re-measured.

## Measurement debt

`ThreadPool::install` (advertised 2.2–2.5× from the laptop, **1.14–1.80× on
hbox**); the ×1.4554 latency figure's phase shares are **still
laptop-derived**; and two headline numbers of mine remain **unconditioned** —
*"sumcheck is 2–17%"* and **`ρ_nat = 2.78`** (the anchor of the Poseidon2
argument, though the verdict survives a wide error bar on it).
