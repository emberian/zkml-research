# The anti-vacuity tooth that was itself vacuous — verification, repair, sweep, gate

**Lane:** LEAN REPAIR, 2026-08-16. Repo `~/dev/breadstuffs`, branch `main`.

---

## 1. Verification at source — the reading was CORRECT

`metatheory/Dregg2/Circuit/RecursiveAggregation.lean` §5, as of `8983bd9ca`:

```lean
abbrev RealProof := Unit
def acceptAll : RealProof → Bool := fun _ => true
def zCH … := fun _ _ => 0    -- and zRH, zcmb, zcompress, zcompressN, all constant zero

/-- … So `EngineSound` is INHABITED — the headline is not vacuous. -/
theorem real_engine_sound :
    EngineSound RealProof acceptAll zCH zRH zcmb zcompress zcompressN
      realAggregate teethGenesis realSteps := by
  refine { recursive_sound := ?_, … }
  · intro _
    refine ⟨fun p hp => ?_, rfl⟩
    rfl                        -- ⚑ `hp` unused: `acceptAll p = true` for EVERY p
```

Confirmed on all three axes: `RealProof := Unit` (one inhabitant), `acceptAll ≡ true`
(no `false` in its range), portal constant-zero.

**Two corrections to the brief, both in the direction of the brief being slightly generous:**

1. **"a `P → P` witness with extra steps" understates one leg and overstates another.**
   `leaf_sound` is discharged by `honestStep.commits`, a genuine `recCexec` witness — that
   leg has real content. The dead legs are `recursive_sound` (unconditionally true at a
   constant verifier) and, at the zero portal, `binding_sound`'s `ChainBound`. The precise
   charge is not "P → P" but: **at this instance `EngineSound` cannot be REFUTED from the
   verify side at any aggregate whatsoever**, so exhibiting a satisfying one says nothing.

2. **"the file does not disclose it" is right for §5 and wrong for §5b.** §5b (added
   2026-08-01) discloses the constant portal loudly and *uses* it: "a LOSSY sponge blinds
   it … every root is `0`, so `ChainBound` holds by `rfl` across a seam that dropped a
   receipt". What was undisclosed is the **proof/verifier** axis, which §5b never mentions,
   and which is the axis the "INHABITED" claim rides.

**A third thing the file was already telling us and nobody read.** Baseline elaboration
emitted `RecursiveAggregation.lean:670: warning: try 'simp' instead of 'simpa'` on
`real_chain_first_turn_executed` — i.e. `simp [honestStep]` closes the goal and the
light-client attestation `h` is **discarded**. A free conclusion, reported in the build
output on every build. Same shape at `GroundedApex.lean` ×2 and `R3Verify.lean` ×1.

---

## 2. The repair

Not a retraction — the claim is repairable, so it was repaired.

### `RecursiveAggregation.lean` §5 / §5a

- `RealProof` is now `inductive RealProof | honest | forged deriving DecidableEq, Repr`.
- `acceptAll` is **deleted**; `realVerify : RealProof → Bool` matches `honest ↦ true`,
  `forged ↦ false`.
- `realVerify_discriminates` — stated **before** every verdict, so an edit that collapses
  the carrier or re-flattens the verifier fails there rather than silently re-vacuifying
  the section while leaving it green.
- `zero_portal_chainBound_is_free (steps) : ChainBound zCH … steps` — the portal
  degeneracy promoted from prose to a **theorem**: at this portal `ChainBound` holds for
  every list of steps, so `AggregateAttests.ordered` here is free. Negative result, named.
- Refusal teeth, each preceded by its forgery-differs assertion:
  `forged_root_differs` / `light_client_refuses_forged_root`;
  `forged_leaf_differs` / `engineSound_refutable_at_forged_leaf` (⚑ the one that matters —
  a forged leaf under a **verifying** root contradicts `recursive_sound`'s own conclusion);
  `forged_binding_differs` / `engineSound_refutable_at_forged_binding`.
- `engineSound_is_a_real_boundary : EngineSound(honest) ∧ ¬ EngineSound(forgedLeaf)` —
  **the theorem to cite.** Satisfiable ∧ refutable at one instance.
- `real_chain_first_turn_executed` now closes with `exact h`, so the proof term genuinely
  routes through the headline; docstring states the conclusion is independently available
  from `honestStep.commits` and that this theorem establishes the *route*, not the fact.

### §9 / §9a — found by the new gate, in the same file

`real_seg_sound` had the identical shape at status `fun _ => True` + combiner `zH`.
Added `misCountTree_differs`, `segSound_refutable_at_miscounted_leaf` (a leaf exposing a
segment other than its genuine `leafSeg` refutes `SegSound` **even at the free status**),
`segSound_is_a_real_floor`, and `real_tree_ordered_is_free_at_this_portal`.

### `RecursiveSoundFromNodes.lean` §7 / §7a — the second instance

`accept : Unit → Bool := fun _ => true` over `honestTree : PTree Unit`, claiming "the
carrier is INHABITED" / "the fold FIRES". At that instance `NodeCarrier` admits **every**
tree and `honest_all_leaves_verify` is `fun _ _ => rfl` with `all_leaves_verify` inert.
Migrated to `RealProof`/`realVerify`; added `forged_leaf_tree_differs`,
`forged_leaf_tree_has_no_carrier`, `nodeCarrier_is_a_real_floor`.

### Red-proof of the repair (mutation, verdict read after the mutation is asserted)

Two mutants built from the repaired file, each asserting the anchor existed and the text
actually changed before running Lean:

| mutant | change | result |
|---|---|---|
| A | `realVerify`'s `forged` arm `false → true` (restores the old degeneracy) | **RED** at `realVerify_discriminates`, `light_client_refuses_forged_root`, `engineSound_refutable_at_forged_leaf`, `…_at_forged_binding`, `engineSound_is_a_real_boundary` |
| B | `forgedLeafAggregate.leafProofs` `[.forged] → [.honest]` (the forgery stops forging) | **RED** at `forged_leaf_differs` and the refutation |

Mutant A is the direct proof of the charge: **every new tooth is unprovable at the
instance the file used to sit on.**

### Propagation — `acceptAll` was re-exported into eight files

All updated (`realVerify`, `.honest`, membership-driven discharges), and the prose that
marketed the degeneracy ("over the **ACCEPTING** verifier") rewritten:
`AssuranceCaseGrounded.lean`, `Circuit/GroundedApex.lean`, `Circuit/ChainStepNonTautology.lean`,
`Distributed/FinalizedLightClient.lean`, `Distributed/SelfSettlement.lean`,
`Grain/R3Verify.lean`, `Verify/ApexPremiseVacuity.lean`, `Verify/KeystoneAuditRunnable.lean`.

---

## 3. The sweep — it is a class, ~13 announced instances plus a long tail

Delegated broad search + a mechanical census. Highlights beyond the two repaired:

| file:line | declaration | claim | substrate |
|---|---|---|---|
| `Distributed/SelfSettlement.lean:579,594,603` | `settle_fires_on_real_child`, `real_settlement_binds_child_fold`, `real_settlement_advances` | "NON-VACUITY … all four crypto legs are discharged" | old `RealProof`/`acceptAll` |
| `Distributed/FinalizedLightClient.lean:281,295` | `finalized_light_client_fires_for`, `fired_attestation_is_real` | "THE THREE-LEG HEADLINE IS WITNESSED … non-vacuous" | same |
| `Verify/KeystoneAuditRunnable.lean:311` | `argus_strand_light_client_satisfiable` | file header: "non-vacuity demands a GENUINE runnable instance" | same |
| `Circuit/PremiseInhabitabilitySweep.lean:394` | `aggFriExtract_inhabited_nondegenerately` | "a **non-degenerate** model" | `verify := fun _ => true` **and** `ChildVerifierSat := fun _ _ => True` — degenerate on both; disclosed only in a *different* file (`…Settled.lean:26`) |
| `Circuit/GroundedApex.lean:327,370,403` | `engineSound_grounded_constructs`, `grounded_light_client_fires(_v2)` | discloses the free `leaf_sound` leg; **markets** the verifier axis | same |
| `Exec/CapTP.lean:425` | `section NonVacuity`, `demoVerifiable := ⟨fun _ _ => true⟩` | weakest disclosure in the report | cheapest fix: port `AuthModes.lean` §6¾ verbatim |

Those six substrate-sharing sites are fixed *by construction* — they now run on a verifier
that refuses. Their **claims** are still one-sided (satisfiability only); each still wants
its own refusal companion.

**Good in-tree patterns to imitate** (found by the sweep, worth knowing):
`Exec/AuthModes.lean:651` (names the `Rights := Unit` wound, rebuilds at `Bool` with an
order-REFUSED cert); `Circuit/Spec/*AbstractBinding.lean` (every `*_nonvacuous` immediately
followed by a `¬ Fpu …`); `Polis/PolisStreamCarrier.lean:217` (exemplary — proves its own
collapse); `Crypto/*Regrounded.lean` `*_satisfiable_vacuously` (self-labelling by NAME).
⚠ `Lightclient/NonOmissionAttack.lean:267` `grounded_mmr_fires_honest` has statement
`mrange L lo hi = mrange L lo hi` — a literal tautology; only its companions carry content.

⚠ **Correction to the brief.** It cites `scripts/check-char2-vacuity.sh` as precedent.
**That file does not exist** anywhere in the repo, and nothing named `char2` appears in
`scripts/local-gates.sh`. The gate below is modelled on `check-guard-discipline.py`
instead, which does have the described shape.

---

## 4. The gate — `scripts/check-anti-vacuity-witness.py`

Rule: an **announced** anti-vacuity declaration (§A, by name or docstring phrase) whose
statement rides a **degenerate** substrate (§B: a same-file constant-`true`/`True`
predicate, or a `Unit`/`PUnit`-carried witness) must have a **refusal companion** in the
same file (§C: any declaration whose statement negates and mentions the same symbol).

Gates on the **finding** against `scripts/anti-vacuity-witness-allowlist.txt`, two red arms,
both verified to exit 1 (checked without a pipe — the wrapper eats the code otherwise):

- unlisted finding → exit 1
- **stale row** (listed site that no longer triggers) → exit 1, forcing retirement

`--self-test` plants a `fun _ => true` + "(NON-VACUITY) … is INHABITED" pair and fails if
the detector misses it. Wired into `scripts/local-gates.sh` as
`anti-vacuity-witness` + `anti-vacuity-witness-red`.

**Census: 37 rows** after the three repairs (the three retired the same day — that is the
ledger's intended motion). Runtime 3.8 s over the tree.

⚑ **The rows are UNTRIAGED and the ledger says so.** They are undone work, not theorems of
the model; a row is not an absolution. The header states the repair recipe and points at
the three finished templates.

⚑ **Performance note worth carrying.** The first two drafts of the detector used
multi-star line regexes (`fun(?:\s+[^\s=>]+)+\s*=>`, then
`[^\n]*:[ \t][^\n]*(?:Unit|PUnit)[^\n]*$`). Both backtracked super-linearly in line length
and the census did not finish in **6+ minutes** over ~3k files; Lean files here have very
long lines. Rewritten line-based with `in` tests: **3.8 s**. The file carries a "do not
tidy these back into one regex" comment.

---

## 5. What a green on all of this does NOT mean

- The gate does not read proofs. A witness at a rich type still discharged by `rfl` is
  invisible.
- It does not count inhabitants — a two-constructor type both of whose constructors the
  verifier accepts passes §B and is just as degenerate.
- §C accepts any negation mentioning the symbol, so a refusal companion pointing at a
  **different axis** than the announced claim counts as present.
  `metatheory/scripts/free_conclusion_canary.lean:114-121` documents exactly this evasion
  and that `#keystone_audit` CHECK 2 cannot catch it.
- The `RecursiveAggregation` §5 portal is still constant-zero. That is now a theorem
  (`zero_portal_chainBound_is_free`) rather than a caveat, but it is still true: §5
  witnesses the **engine**, not the hash portal.
