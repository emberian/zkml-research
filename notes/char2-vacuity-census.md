# Characteristic-two hypothesis census — minidregg

**Measured 2026-08-14** against `~/dev/minidregg` at `0dd9a48`/`44fcac4` (465 `.lean`
files, `.lake/` excluded). Instrument: exhaustive `grep` sweep over ten patterns plus a
Lean environment walk (`scripts/CharTwoVacuityCensus.lean`, 29 085 declarations).

The question this answers: **before anyone starts binary-field work, which hypotheses in
this tree are uninhabitable at characteristic two — and for each, is that a real
constraint to keep, a wall to name, or a latent vacuity trap to fix?**

---

## Verdict in one table

| Site | Kind | Classification | Status |
|---|---|---|---|
| `Selvage/Proximity.lean:190` `two_ne : (2 : F) ≠ 0` | structure field of `FoldingData` | ⚑ **LATENT VACUITY TRAP** — real constraint, silent refusal | **FIXED** — `Selvage/CharTwoWall.lean` |
| `Selvage/Proximity.lean:381` `data : ∀ j, j < m → FoldingData …` | structure field of `FoldingTower` | ⚑ **LATENT VACUITY TRAP** (transitive, positive height only) | **FIXED** — same |
| `Compiler/FriQueryVerifierAir.lean:138,281` `(2 : F) * half = 1` | theorem hypothesis, unconstrained `[Field F]` | ⚑ **CHAR-2 WALL, prose-only** | **FIXED** — `no_half_of_charTwo` |
| `Assurance/Tower256AdditiveFriControllerAdmission.lean` | quantified over empty `MerklePcs` | ⚑ **SPRUNG VACUITY** (not char-2; cardinality) | **RETRACTED**, machine-checked |
| `Assurance/Tower256AdditiveFriActualReduction.lean` | same | ⚑ **SPRUNG VACUITY** | **RETRACTED**, machine-checked |
| `Compiler/Logup256ReceiptClause.lean:221`, `Compiler/Tower256CshakeMerkleController.lean:306` `characteristic : CharP F 2` | structure field | **REAL CONSTRAINT (inverse)** — empty over ODD char, correctly | keep |
| `Theory/AdditiveNTT.lean:463,479,724`, `AdditiveNTTTransform.lean:662` | char-2-*requiring* theorems | **REAL CONSTRAINT** — false in odd char, correctly hypothesised | keep |
| `Fact (Nat.Prime p)`, ~45 sites | typeclass instance | **NOT A WALL** — every concrete prime is odd; the 11 generic binders do not exclude 2 and do not need to | keep |
| `ringChar F ≠ 2` | — | **ABSENT** — zero mentions repo-wide | n/a |
| `Invertible 2`, `CharZero`, `¬ CharP F 2`, odd-characteristic hypotheses | — | **ABSENT** | n/a |
| Root-of-unity / 2-adic smooth order | — | **ABSENT** — all `orderOf` use is 3-adic in `Theory/CyclotomicInertia.lean` | n/a |
| ~150 `/ 2` and `(1 ± ρ)/2` sites | ℝ/ℚ soundness arithmetic | **FALSE POSITIVE** — decoding radii, birthday bounds, rates; not field elements | n/a |

**Headline: exactly one structure in `Selvage/` or `Theory/` had a char-2-false field**, out
of 345 structures/classes enumerated. The multiplicative and additive cones were already
disjoint by construction — no file carried both `[CharP F 2]` and a `FoldingData`
hypothesis. The danger was never a live collision; it was that nothing would have *noticed*
one.

---

## Trap 1 — `FoldingData.two_ne`, and why the hypothesis stays

`FoldingData F dom domSq` is empty whenever `CharP F 2`, so **all 185 declarations across 27
files that take a `FoldingData` or `FoldingTower` are vacuously true over a binary field** —
on a green build, passing their `#print axioms` pins, with no diagnostic anywhere.

The hypothesis is **not** removable. The multiplicative fold divides by `2` and by `2x`
(`foldEven = (f x + f (-x)) / 2`, `foldOdd = (f x - f (-x)) / (2x)`); at char 2
`f x + f (-x) = 2 f x = 0`, and squaring is the Frobenius, so the `{x, -x}` fibres are
singletons and there is nothing to halve. **Multiplicative FRI does not exist over a binary
field.** Migrating `FoldingData` to a char-2-compatible shape would not be a migration, it
would be a different protocol — and that protocol already exists here (below).

So the fix targets the *silence*, not the hypothesis. `Selvage/CharTwoWall.lean`:

- `foldingData_charTwo_False`, `foldingTower_charTwo_False` — the emptiness, named.
- `foldingData_vacuous_of_charTwo` — **the consequence, named**: at char 2 every predicate
  holds of every `FoldingData`, including `False`. This is the citation for reviewing a
  purported char-2 result over the multiplicative carrier: not weak evidence, *no* evidence.
- `foldingTower_charTwo_inhabited_at_height_zero` — **the wall's exact location.** A
  height-`0` tower does no folds and *is* inhabited at char 2. The refusal is therefore
  satisfiable and refutable, not blanket-provable. ⚑ This is a genuinely subtler trap than
  full emptiness: a theorem over `FoldingTower F ι m` with `m` free is not fully vacuous at
  char 2 — it survives only at the degenerate `m = 0`.
- `strippedCharTwoWitness` — **a machine-checked negative control.** `FoldingData` minus
  `two_ne` is *inhabited* over `ZMod 2` (`neg = sq = sec = id`; `-1 = 1` makes `neg` lawful,
  Frobenius makes `sq` a bijection). So `two_ne` is the whole wall, and deleting it to
  "enable the port" cannot be papered over — `CharTwoWall.lean` goes red in the same commit
  and there is no alternative proof to fall back on.

Axiom footprint: the five wall theorems are `[propext, Quot.sound]` — no choice.

### The honest char-2 path, which already existed and is proved

`Selvage/AdditiveFriTower.lean:4-6` already said in prose that the multiplicative tower
"cannot be instantiated in characteristic two", and `:402-411` named the exact remaining
boundary. The replacement is the **additive** tower, folding along a coset `{x, x + β}` and
never halving:

- `Selvage.AdditiveFriTower` — `additiveTowerFold`, `additiveTowerEmbedding`,
  `additiveTowerPivot_ne_zero`, `additiveTower_domain_eq_pairDomain`;
- `Selvage.AdditiveProximity` — `additiveProximityGap_UD`, `additiveFold_distance_UD`,
  proved unconditionally on `δ < (1−ρ)/3`;
- `Selvage.AdditiveFriQuery` — `AdditiveFriTower`, the char-2-**native** structure carrying
  `[CharP F 2]` instead of `two_ne`, and
  `additiveFriAdaptive_coherent_sampled_sound_UD`.

---

## Trap 2 — two Assurance modules vacuous at positive height (RETRACTED)

Not a characteristic-two trap; a cardinality one, and already sprung.

`Tower256AdditiveFriControllerAdmission` and `Tower256AdditiveFriActualReduction` are
quantified over `pcs : MerklePcs ell`. `merklePcs_empty_of_positive` proves that carrier
**empty for every `0 < ell`**: `MerklePcs` demands *unconditional* position binding from a
256-bit cSHAKE root, binding plus completeness makes the whole-word commitment injective,
and a positive-height Tower256 column has more than `2^256` words. Pigeonhole.

Both are **retracted**, with the retraction machine-checked *in the file*
(`commonGameFamily_impossible`, `actualReductionFamily_impossible`) rather than asserted in
prose. Worth stating plainly: `ActualReduction`'s "exact UD price" and three-event cover
hold of no PCS at any height that folds, and `CommonGameFamily.failureCover` — advertised as
"the one hard field", the remaining PCS/ROM reduction — was never a real obligation.

⚑ Height zero is not a rescue. It performs no folds, and the carrier census reports
`MerklePcs` unwitnessed at *any* height. There is no `ell` at which these modules are known
to say something.

**A structural finding worth carrying forward.** The refutation could not previously be
stated where it was needed: `Tower256MerkleBindingCardinality` imports the checkpoint game
and is therefore *downstream* of the modules it refutes. The cardinality argument moved into
a new `Assurance/Tower256MerkleCardinalityCore.lean` sitting directly above
`Compiler.Tower256AdditiveFriController`, so every module quantified over `MerklePcs` can
now import its own retraction. **When an impossibility proof lives downstream of its
subject, the subject cannot cite it — and that is exactly how a refuted module stays in the
build looking healthy.**

Replacements exist and are live: `Tower256AdditiveFriRawAdmission`,
`Tower256AdditiveFriCanonicalExecutionGame`, over `RawMerklePcs`, which retain extracted
collision events with an explicit CR price instead of postulating an injective finite hash.

---

## Trap 3 — the AIR divided-fold label (found by the sweep)

`Compiler/FriQueryVerifierAir.lean` (Lean-authored AIR; no Rust involved) states
`friFoldVal_eq_div_twoX` and `friQueryVerifier_correct_div` under `(2 : F) * half = 1`, over
an **unconstrained `[Field F]`**. Instantiate at `Tower256` and both are vacuous.

The file's header was already honest — "over characteristic 2 no `half` satisfies it and the
divided fold does not exist". That is prose. It is now `no_half_of_charTwo` and
`dividedFold_vacuous_of_charTwo`.

⚑ Note what is *not* walled: `friQueryVerifier_correct`, the keystone iff, holds for every
`half` and the gadget arithmetizes fine over a binary field. Only the *divided reading* dies,
because that is the multiplicative even/odd fold. Arithmetizing `additiveTowerFold` is the
honest binary-field task; relaxing `2 * half = 1` is not.

Transitive `half`-parameter consumers, all unconstrained `[Field F]`, all vacuous if the
premise is demanded: `Compiler/FiatShamirAir.lean:246,259,278`,
`Compiler/MerkleBindAir.lean:303,317`,
`Assurance/SemanticHistoryRecursiveAir.lean:199,212,266,304,317,325,335`. None currently
mentions `Tower256` or `CharP`, so no live collision.

---

## The detector (because none of the above notices a *new* trap)

The theorems answer a vacuous claim once it is in front of you. They do not notice one being
written — which is the whole failure mode: port the cone "to a binary field", everything
compiles, every axiom pin passes, 185 declarations become vacuously true.

`scripts/CharTwoVacuityCensus.lean` + `scripts/check-char2-vacuity.sh` walk the environment
for declarations mentioning a char-2-refuted carrier together with char-2 evidence (a `CharP`
binder, or a field whose characteristic is two by a proved theorem here). It gates on the
**finding**, not merely on a self-test: the honest number is zero and the tree is at zero.

Today: `29 085 scanned · 2 dead carriers registered · 5 exempt (the wall itself) · 0 vacuous`.

⚑ **Proved red-capable twice, not assumed:**

1. Before the wall module got its structural exemption, the run reported 5 hits and exited 1.
2. Renaming the exempt module makes the run *fail* — `wallModule names no emptiness theorem` —
   rather than read clean. Deleting `Selvage/CharTwoWall.lean` cannot present as a green tree.

The exemption is by **home module**, not a list of declaration names, so it cannot quietly
grow to cover a real hit. The allowlist beyond it is empty by design.

---

## Documentation repaired against the theorems

- `docs/SELVAGE-COMPLETE.md` — the checkpoint-game paragraph claimed to "close the two-ledgers
  residual"; `jointGameFamily_impossible` refutes it. Labelled retracted, and the following
  "conditional **P** shape" corrected (vacuous is strictly weaker than conditional).
- Same file, the open-obligations list — the raw non-binding Merkle/PCS interface **landed**
  and the collision *extraction* direction is **proved**; what remains is the collision
  **price**. `PositionBinding` unconditionally is not a residual but an impossibility. The
  "far-word/proximity" bullet is Fiat–Shamir/`oracleTransport` only.
- `docs/PROVER-PLAN.md:63`, `docs/DEPLOYMENT-MANIFEST-JOIN.md:41` — "proximity" listed as
  remaining where `additiveProximityGap_UD` proves it. Ext6/BabyBear and Johnson-regime
  proximity are the genuinely open ones and are now named as such.
- `Theory/AdditiveNTTTransform.lean` — eight docstrings labelled the additive gap
  "RESIDUAL HYPOTHESIS" / "NAMED, not proved" / "the floor". ⚑ The nuance was **kept, not
  flattened**: within `Theory/` it genuinely *is* a hypothesis, because the boundary forbids
  naming `Selvage`. Labels now read "hypothesis HERE; PROVED one import layer up", name the
  discharging theorem, and state the genuine remainder — the band at and above `(1−ρ)/3`.
  **An auditor reading "residual" as "unproved anywhere" was being misled by an import
  boundary.**

---

## Open, and not fixed here

- `Assurance/SemanticHistoryTower256CheckpointGame` and `SemanticHistoryTower256DeployedBcs`
  still build on the retracted admission module and are vacuous for the same reason. Deleting
  the four together is the follow-up; they were kept only because the retracted modules are
  still imported.
- ⚠ **The full tree is RED at HEAD from a concurrent lane**, unrelated to this work:
  `Assurance.SpartanR1CS` and `Assurance.ZkmlLowRankUpdate` both declare
  `Minidregg.Assurance.matVec`, so `Assurance.lean:8` fails to import. Every module touched
  here builds; `lake build Minidregg` does not.
- The census registry (`charTwoDead`) holds two carriers. It should grow whenever a new char-2
  wall is *proved* — never on a believed emptiness, since a registered name with no evidence
  fails the self-test by design.
