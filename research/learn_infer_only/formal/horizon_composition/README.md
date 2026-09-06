# Completed finite horizon arithmetic

[EXECUTED final collection] The two saved modules have40 exact guards and pass the final 49-module/651-pin integration, including Theory umbrella and import boundaries. Proposed patch: minidregg-horizon-arithmetic.patch. The final guarded witness check is experiments/horizon_composition/compile_HorizonCompositionWitnesses_06.json. This proves finite rational identities/counting, not the FE/PPT construction or a runtime randomness sampler. The statement-first brief below is retained as history.

# Horizon arithmetic proposal

[OPEN; statement-first 2026-09-06 10:03 UTC] Formalize the candidate-independent
finite identity in the private lane's `experiments/private_construction/horizon/HORIZON.md`.
For a full B-ary tree containing depths 0 through H, N_H is the total node count.
At every node a frame has four rational probabilities (RealL, IdealL, IdealR,
RealR). Its signed root gap decomposes into left SIM gap, ideal middle gap,
and negative right SIM gap. Internal middle gaps equal the sum of child root
gaps. Terminal middle gaps are zero. These explicit premises should force the
root gap to be the sum of all oriented node-side gaps; uniform averaging over
the 2*N_H choices should equal root_gap/(2*N_H).

Required nonvacuity: an inhabited B=2,H=1 frame tree with rational probabilities
in [0,1], nonzero root gap, nonzero averaged gap, and explicit coherent frames.
Required teeth: uniform depth is biased without node-count weights; omitted
terminal middle gap invalidates the identity; dropping a node term or failing
to complement the right output can invalidate it. Prove depth weights B^d/N_H.

[SCOPE] This is an arithmetic conditional over finite functions and rational
probabilities, not a formalization of PPT, FE, iO, simulator code, selectivity,
cryptographic security or the private lane's complete horizon theorem. Use
existing Mathlib finite sums, no new cryptographic probability machinery.
No companion edits, new searches, commits or previous-artifact changes.
