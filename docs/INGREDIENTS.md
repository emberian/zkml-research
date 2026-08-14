# The bag of ingredients: what we hold, and the one thing it lacks

2026-08-14. Survey of `~/dev/minidregg` at `323a7b3` as a *library of composable
primitives*. Full inventory: `notes/ingredient-inventory.md` (1,077 lines),
from 473 files / 16,097 declarations, a name-blinded body-hash twin detector, a
token reverse-index island detector, an import DAG, and both in-tree censuses.

## ⚑ THE SINGLE INGREDIENT THAT UNBLOCKS THE MOST

**The partial-sumcheck realizer**: `scChain_*Honest_partial` at `k ≤ m`,
landing on the residual sum over `SuffixCube m k` rather than on `mle f r`.
**`roundSum` already sums over `SuffixCube`, so the partially-folded object is
already the primitive** — what is missing is the honest-side chain that stops
early.

**It unblocks five of five target systems**: Ligerito B1/B2/B3 · the *only*
undischarged leg of `RingSwitchSecure` (the ℓ′-round degree-2 transfer) · the
GKR layer hand-off · Spartan's phase-1→phase-2 join · BaseFold
descend-then-switch.

> ***It is the composition operator the bag lacks; everything else in the bag
> is a complete protocol.***

⚠ Cost unpriced — the lane did not attempt the proof and said so.

## ⚑ THE RECURRING CLASS: work priced as open that was already done, THREE TIMES

- **Ligerito A6** (`openingSchemeV`) was priced *"mechanical but wide — every
  consumer of `verifyOpen` re-types."* **Zero new Lean needed**:
  `OpeningScheme (Root F ι Op)` carries `F` as a **bare `Type*` with no
  instance binder** (`[Field F]` first appears 130 lines later).
- **Ligerito A7** (`positionBinding_columns`), priced *"likely direct."*
  **Already there** — `BinaryMerkle.HashSuite` has **no carrier at all**;
  instantiate at `Value := Fin m → F` and the column commitment *plus its whole
  binding theory* comes with it.
- **`AcceptsFalse`'s terminal clause mentions no cube, no variable count, and
  no final oracle evaluation** — so `sumcheck_soundness`, already `{v d}`-
  generic, **IS partial-sumcheck soundness at every `v`.**

> ***All three were priced as work because the PROSE said "the commitment
> layer" and nobody re-read the binder.*** **Read the binders, not the
> docstrings.**

## Generality: mostly REAL

**455 `omit` lines, 63 of them `omit [Field F]`** — marking four genuinely
field-free sublayers. **Exactly one TRAP** (`FoldingData`'s `two_ne`, 58
dependents), already detected and **gated on the finding at zero across 29,276
declarations.**

⚠ And the `0 IsPrimitiveRoot` census result is **a different API, not a gap**:
`CyclotomicInertia`'s `exists_unitsZMod_orderOf_eq` **is** the smooth-domain
constructor — and it is an **island** (110 declarations, 1 consumed).

## Twins and islands — both are composability failures we find by accident

- **111 cross-module identical-text groups.** The substrate is nearly clean;
  **the mass is application-layer**, worst being `SemanticHistoryFamily`
  re-declaring the entire `VerifiedHistoryHead` API *of a module it imports*.
- **17 modules with zero declarations consumed anywhere else**, including the
  whole additive cone.
- ⚑ **And the pattern worth naming: an island does not close, it MOVES.**
  `basefoldSumcheckRbr`'s island was repaired with a **same-file** consumer —
  so `basefoldSumcheck_fs_sound` is the island now. **Same blindness as a
  per-file `lake build` failing to see a twin.**

## ⚑ The refactor was REFUSED, and the refusal is the finding

The tree **already has role-level interfaces in the three places a second
instance justified one**, each with a refutation proving the parameter
load-bearing. **And the pattern reproduced itself mid-survey**: a concurrent
lane landed `Selvage/HashFamily.lean` with **two instances on two
characteristics and a proved impossibility.**

> ***Composability here was bought by NOT adding structure, and `omit` is what
> keeps it honest.***

Three narrow exceptions named instead — one carrying a trigger so it fires
without anyone remembering.

## ⚠ Two instrument defects

- ⚑ **The carrier census cannot see `private` producers** — name mangling
  defeats its `ours` test, so **it reports `FoldingData` unwitnessed when
  `ReceiptClaim.data₄` builds one.** A vacuity detector with a blind spot for
  a whole visibility class.
- `HalfThresholdFri`'s docstring claims *"no characteristic assumption"* —
  **true of the proof, false of the carrier.**
