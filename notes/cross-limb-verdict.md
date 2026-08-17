# Cross-limb binding: one name, two holes, and a fix that can never refuse

2026-08-14. `metatheory/Bfv/CrossLimb.lean` (`5b653ba5d`), `Bfv` namespace
**90 → 113 kernel-clean theorems**. Full note: `notes/cross-limb-binding.md`.

## ⚑ It was one name carrying TWO holes, with different fixes

- **Provenance**: the *checked* system is `∀i ∃source`; the *honest* one is
  `∃source ∀i`. **A quantifier swap — invisible to every completeness test.**
- **Expressibility**: `⌊t·x/Q⌉` reads the **CRT reconstruction**, so **there is
  no per-limb equation to bind at all.**

Both exhibited (`perLimb_not_imp_bound`, `rescale_not_limb_local`). **Neither
fix touches the other.**

## The forgery is a wrong ANSWER, not an unbound proof

`exhibit_accepted_value_is_dishonest`: the accepted output reconstructs to
**1 ∈ ℤ/15** where every honest pair yields 10, 6 or 0. Satisfiable side
pinned too, so the exhibit is not vacuous in either direction.

## ⚑ My suggested fix is a TAUTOLOGY

I proposed *"a CRT-consistency relation over the limbs"* as a candidate.
**It can never refuse: the CRT map is a bijection, and the forgery is itself
CRT-consistent.** And `perLimb_pins_modProd` shows the hole is **not in the
arithmetic** — with operands fixed, the per-limb conjunction **is** the mod-Q
relation. ***The fix has to be a binding, not a relation.***

## ⚑ Why nobody had exhibited this in months

**Every Lean BFV carrier in the tree makes the attack UNREPRESENTABLE** — and
`Market/DarkBazaarSameOpeningPoly.lean:45` says so in its own residual list.
**True of the model, and exactly why the model could not go red.**

> **A new vacuity shape: not a theorem about nothing, but a MODEL too weak to
> express the attack it is supposed to rule out.** The check passes because the
> forgery cannot be written down.

## The closure is free; the bill is somewhere else

**Interleaving the limbs into one row makes the row the shared opening: +0
committed felts, +0 permutations.** The real cost is the **2-felt BabyBear
bridge that row-sharing forces** (already deployed): **+220,201–294,912 perms
per ciphertext at lb=6.** An RLC binding costs **+293,601 more for only a
probabilistic** guarantee; keeping per-limb-native tables costs ~4× that again
— ⚑ **so the soundness argument and the field-choice work converge on the same
verdict from opposite directions.**

## ct×pt is narrower — on one axis only

**Expressibility is ABSENT there**, and ⚑ **it is the same property that gives
that route its provable noise budget** (a public integer scalar acts
coefficientwise). **Provenance SURVIVES**, at `K^L` rather than `(K²)^L` —
6-of-8 vs 60-of-64 forgeries at the deployed tower. **A singleton pool closes
it outright, so the hole tracks how many ciphertexts the transcript exposes**
— and deployed depth 2 with 132 results/multiply is exactly the
many-ciphertext regime.

## Scope, said plainly

**There is no ct×ct arithmetization anywhere in the tree** (absence verified —
the `relin` greps were all `relink`). **The hole is in the design; the file is
what a future emitter must refute.**

## ⚠ Corrections

- **PREFLIGHT was wrong**: `Bfv/Mul.lean` and `Bfv/Smudging.lean` are **not**
  outside a default target — both are rooted through `Market`, and both carry
  their own `#assert_all_clean`, a *stronger* per-keystone pin. ⚑ **The premise
  ("the `Bfv` lean_lib has no globs") was true and the conclusion false,
  because a module can be rooted from a DIFFERENT library.** The lane repeated
  the stale claim in a draft before checking; the check was two greps.
- **New fact for `ε_chk`**: it **cannot be instantiated limb-locally** — a
  faithful-execution checker must decide *provenance*, and provenance is
  invisible to any per-limb check **by construction.**

## Remainder

Hole B (expressibility) has an exhibit and **no closure**, unpriced —
single-prime dissolves both, gated on H1. `A,B` correctness untouched;
nonlinearity boundary unchanged; accumulated exactness over many steps still
unstated.


---

## ADDENDUM (2026-08-16): the Z_Q algebraic closure — and an impossibility that sharpens Hole B

`metatheory/Bfv/ZqSumcheck.lean` (`c4c1e5835`), `Bfv` namespace **113 → 137
kernel-clean**. Full note: `notes/zq-sumcheck.md`.

**Hole A now has TWO closures of ~equal cost.** The forgery is not refused
over Z_Q — **it is unwritable**: `boundMul_iff_zqBound` shows the honest
`∃∀` statement IS one ring equation (that quantifier shape is what a ring
equation *means*), and `zq_same_forgery_refused` shows the identical
frankenstein from `CrossLimb.lean` is over Z_Q **a flatly false sentence**.
⚠ My "3×" price was against the wrong baseline — vs the row-interleaved
closure it is **~1× in limb-mul counts** (3 limbs *replace* 2 bridge felts +
a doubled table). Real deltas: a **one-handle PCS obligation** (else per-limb
selection reappears at the opening index) and machinery that exists nowhere
in Rust. **No product selection made**: both routes close Hole A, neither
closes Hole B, and the limb-prime-swap route dissolves the comparison.

⚑ **THE IMPOSSIBILITY, and it half-refutes my claim**: polynomials over a
product ring compute **exactly the limb-local functions**
(`ringHom_eval_comm`), so **NO Z_Q polynomial computes the rescale**
(`rescale_not_zq_polynomial`). `⌊t·x/Q⌉` is *nameable as a function, never a
polynomial identity over Z_Q*. **Hole B is not merely open — it is CLOSED to
this entire approach**, and any proof of the rescale must go through the
redundant-basis witness or the single-prime route. Corroboration from the
other side: **CCKP19 chose `Z_{p^e}` (non-CRT) precisely to keep rounding
polynomial.**

**The mathematics, tightened against my brief:**
- Soundness is `v·d/|A|` — **rounds ADD by union bound**; my "36 bits/round"
  was a per-round *error*, not a rate.
- `|A| ≤ min qᵢ ≈ 2³⁶` is a **theorem** (`deployed_sampling_ceiling`),
  attained by the diagonal embedding.
- ⚑ **"Extension of each factor" and "shared extension" are the SAME RING**
  (CRT-lift: `Z_Q[y]/(y⁴−c)` for a simultaneous QNR `c`). **Shared Ext2
  (2⁷²) does NOT clear the ~124-bit bar; shared Ext4 (2¹⁴⁴) does** —
  repetition is dominated.
- **`Field` is load-bearing in exactly ONE lemma** (root counting via
  `IsDomain`) — **and the bite is NOT cosmetic**: field-wide Schwartz–Zippel
  is *FALSE over Z_Q*, proved (`zq_fieldwide_sz_false` — distinct degree-<2
  polynomials agreeing on 5 > 2 points). The repaired statement
  (`zq_agree_card_lt`, A-relative counting via coordinate projection) is
  proved.

**Consequence for the zero-emulation architecture**: the limb-native-provers
route (ECFFT note §8) has its cross-limb binding — Z_Q sumcheck at ~1× with
shared-Ext4 challenges clearing the bar — **modulo the one-handle PCS
obligation.**

⚠ Hygiene find, recorded for the next lane: a missing
`Mathlib.Algebra.Field.ZMod` import (+ `Fact (Nat.Prime p)`) presents as a
**`whnf` heartbeat TIMEOUT, not a clean synth failure.**
