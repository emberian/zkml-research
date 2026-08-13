# Impl-gating verification: the Selvage legs, mechanically confirmed

> **ARCHIVED — history, not truth. Do not cite this file.**
> A truncated fragment. Everything in it, plus the two precision corrections
> and the ε_beacon transport obligation, is in **`notes/impl-readiness.md`** §1.

2026-08-13. Skeptical lane re-elaborated the light-client files from source
and ran #print axioms on fresh oleans — NOT trusting docblocks.

**Verified**: `lightClientSound` (Selvage/LightClientSound.lean:520, exact
claimed shape), `lightClientGrinding_sound` (:455, (t+n) factor with
necessity exhibited at 9/25 > 1/5 strict), `lightClientFS_sound`
(LightClientFS.lean:303). All nine theorems: [propext, Classical.choice,
Quot.sound] only. No #guard anywhere in the three files.

**Precision flags for any citation**: "bound attained" is true of the
EXACT-WORD sibling (`lightClientSound_exact`, equality at 1/5); the
de