# Native row and query-event bridges

[DERIVED] `Ir2Fri.native_eq_foldStep j row f beta` proves actual native interpolation on `nativeRowNodes j row` with the existing `rowSourceIndex` values equals `foldStep j f beta (nativeParentIndex j row)` for all five rounds. The parent coordinate is the natural exponent obtained by reversing the native parent-row bits.

[DERIVED] `native_domain_source` derives `domain n i = omega(17-stage n)^i.val` from the actual omega17 tower. `nativeRowNodes_domain` identifies every existing packed-row node with that actual source-domain point; `nativeRowSourceIndex_squareStep` identifies its actual composed squaring fibre. The final theorem applies `native_eq_fold8` four times and `native_eq_fold4` once, with those premises proved here and no desired fold-equality premise.

[DERIVED] The node/fibre/equality premises are jointly inhabited at the actual last row. A nonconstant domain word is evaluated as X at every scalar, and `native_scalar_falsifier` proves native evaluations at zero and one differ. The native helper includes its node-hit branch, so the equality holds at every scalar.

[EXECUTED] The native-row module passes a source-stable, warning-free individual Lean check with all 12 theorem declarations axiom-pinned. Import boundaries pass; the complete source scan finds no `sorry`, `native_decide`, or declared axiom. Exact checks and copied dependency snapshots are in `CHECKS.json`. Dependency source modules were preserved.

[OPEN] Root owns the native admission/event adapter and combined integration. This checked addon is supplied through that shared IR2 outcome, with no broad build or standalone manifest.

[DERIVED] `Ir2Fri.native_query_iff_counted` in `Ir2FriNativeEvent.lean` proves that literal native interpolation checks on raw parent rows equal `QueryAccepts (initialMask s) (stepMasks s r)`. `rawParentRow` uses the full raw query divided by `2^stage(j+1)`; its native parent exponent equals the existing coherent runtime index. The native predicate includes the initial carried-input equality.

[DERIVED] Actual global zero words inhabit native acceptance at 38 queries; changing their input to one produces an initial-check rejection even with valid zero interpolation rows. The event contract has no ideal-fold equality premise. Packed-root extraction into those global words remains explicit and separate.

[EXECUTED] The added event module passes its own source-stable, warning-free check with six theorem guards. The previous native-row module's frozen source hash is unchanged. The existing `CHECKS.json` retains both checks; no extra artifact hierarchy was created.
