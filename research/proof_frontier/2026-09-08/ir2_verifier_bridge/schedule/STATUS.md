# Concrete IR2 consistency schedule

[DERIVED] `Ir2FriSchedule` fixes `stage n = min (3*n) 14`, `Index n = Fin (2^(17-stage n))`, and the five actual modulo projections. Its fibre cardinalities are eight for the first four rounds and four for the fifth; the terminal domain has eight entries. `runtimeIndex_eq_naturalIndex` proves that reversing the raw index after dropping stage bits equals projecting the full seventeen-bit reversed source.

[DERIVED] `Ir2FriConsistency` takes an explicit `initial : Index 0 → Prop` and five later supplied masks. Initial weights are the initial predicate's indicator; each transition averages its actual project fibre and applies its supplied mask. `consistency_mass_exact` proves exact source counts at every prefix and subset.

[DERIVED] `coherent_query_exact initial mask q` proves that `QueryAccepts`, including every initial carried-value check, has exact probability `(terminalFraction initial mask)^q` under independent uniform full seventeen-bit raw indices. `fresh_query_exact` and `fresh_query_bound` derive the corresponding actual BabyBear canonical-modulo law for fresh independent uniform base words, retaining the extra mass at raw zero. No event bound, code, farness, or Fiat–Shamir distribution premise is hidden in these statements.

[DERIVED] Witnesses inhabit the mask/counting contract with accepting raw zero and rejecting raw bit16. Separate falsifiers prevent replacing the final radix by eight or omitting the initial consistency check; the latter uses the reported 38-query batch.

[EXECUTED] Both frozen modules pass source-stable, warning-free individual checks, with every theorem declaration axiom-pinned. The import-boundary check passes and the complete new-source scan finds no `sorry`, `native_decide`, or declared axiom. `CHECKS.json` contains exact source hashes, commands, outputs, and source observations.

[REPORTED] The concrete schedule and initial native carried-value condition come from the parent replay handoff. Root owns their executable trace evidence and the instantiation of masks with native coefficient-fold equalities. Main minidregg and breadstuffs remained read-only.
