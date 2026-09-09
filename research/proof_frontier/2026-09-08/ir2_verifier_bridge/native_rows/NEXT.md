# Integration handoff

[OPEN] Copy the two frozen `Selvage/Ir2FriNativeRows.lean` and `Selvage/Ir2FriNativeEvent.lean` addons into the root integration isolate. Import the event module and use `native_query_iff_counted s r q raw` to replace the ideal-fold acceptance event with literal native interpolation checks. The earlier `native_eq_foldStep j row f beta` remains available unchanged.

[OPEN] Root owns packed-root extraction into global `Words`, terminal acceptance, and the final combined dependency check. No native-to-ideal fold equality premise is required by these addons.
