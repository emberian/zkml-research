# Actual supplied BinaryMerkle opening: deterministic checkpoint adapter

[DERIVED, kernel checked] `suppliedOpeningSound` proves that a concrete value and
path accepted by the existing `BinaryMerkle.openingScheme.verifyOpen` equal the
word extracted from the commitment-time prefix, provided the explicit finite
transcript event `Bad` is absent. The proof uses the supplied path throughout.
It does not replace that path by an existential `verifyOpen` witness.

The new module reuses `OracleLog` and proves its computable reverse lookup equals
`OracleLog.answerOf` on swapped cells. Typed leaf/node queries distinguish the
existing hash-suite inputs. `openingLog` contains the supplied opening's leaf and
node records, computed using the existing `BinaryMerkle.recompute`. The final
log is explicitly `P ++ middle ++ openingLog`; extraction depends only on `P`,
the fixed root, and the chosen default. `Bad` is a recorded response collision,
or a record absent from `P` whose response hits the root or a child of a node
recorded in `P`. `badCheck_eq_true_iff` supplies a finite Boolean test for exactly
this event, with no quantification over unseen accepting openings.

[DERIVED] `Far_E` is farness of this extracted prefix word under the existing
`close`; it is deliberately preserved as a new event. An explicit field-five,
depth-one witness inhabits absence of `Bad`, actual acceptance, and `Far_E` for
the zero code at radius 2/5. Falsifiers cover a late root, a late child even when
the root query is already present, and an observed response collision with no
late target. A further witness shows why extraction from the final log changes
the word. All witnesses use actual BinaryMerkle acceptance.

[EXECUTED] The package records a single-module Lean check, exact axiom guards,
the root integration census, clean additive-patch application and the companion
import-boundary script, all in an isolated checkout. See `manifest.json` and
`logs/`. The companion tree was read only. The patch introduces one module and
makes no umbrella import edits. The proposed integration entry is included.

[OPEN] This is the deterministic seam, not a computational binding theorem.
The source audit's probability bound, actual oracle execution/log completeness,
typed-leaf runtime interface, multiple roots, MMCS, Fiat–Shamir and QROM are not
formalized here. No probability is assigned to `Bad`. The accepted opening adds
exactly k+1 **recorded entries**. This is not a runtime hash-evaluation count for
`openingLog`: its `pathLog` constructor recomputes child suffixes. Prefix timing
is explicit through the separate arguments; a protocol must still prove that
`P` and the root were fixed before its later challenges. No crypto is executed.

[SOURCE] Source locations, frozen prior-audit pins and the bounded existing-module
search are recorded in `source-evidence.json`. This lane made zero web or Scry
queries; the accepted source audit is reused without alteration.
