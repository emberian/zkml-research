# Ring-hash candidate: cryptanalysis verdict

2026-08-13. The leg that was explicitly missing. **Verdict: the direction
SURVIVES — no feasible break on the reference instance — with priced
weaknesses the design lane must address before this is more than a candidate.**

## What held (proceed)

- **The σ-layer genuinely kills the 2026/1127 §D distinguisher.** Measured:
  integral over one input element stays balanced FOREVER with σ off
  (= §D's object) and saturates with σ on. The slot-mixing claim is real,
  by execution.
- **No Chaghri-style degree stall** at τ=1 or τ=2 — degree grows
  multiplicatively because x^α (α=7) is not a q-power map. ⚑ And the lane
  **retracted its own initial false positive** (a "persistent τ=2 integral"
  that was q=7 statistical noise, checked across seeds).
- No invariant slot-support subspace, no round-function subspace trail on the
  reference instance.

## The priced weaknesses (all must be addressed)

1. **Branch number is O(t) — ~7.2× weaker than a true MDS at frog width**
   (≤9 vs 65), and *independent of d*: one active input cell → 2t active
   output cells, rigorously. Slot-diffusion to full takes ~log₂d rounds
   (measured 7 at d=16). This is the design's own flagged weakness, now
   quantified.
2. **A real top-degree deficit, but data-bounded.** The full-element integral
   persists ~2.7× longer than a same-width real-MDS Poseidon (dies at r≈13 vs
   r=5 at d=4, robust across seeds). Costs q^d data ⇒ **infeasible at real
   parameters** (2^1024 at frog d=16), and lower-order integrals do NOT lag.
   So: not a break, but the quantitative signature that **the round budget
   assumed an MDS the design does not have.**
3. **C5 is a mislabeled gate** — it checks multiplicative order while claiming
   the Poseidon2/Out-of-Oddity criterion, which is minimal-polynomial
   irreducibility. The composite L badly fails irreducibility (char poly
   splits, e.g. degrees [1,1,1,1,4]). The property C5 names is actually
   delivered by C3 + the MDS. Replace with a real subspace-trail/min-poly
   check.
4. **Two unstated load-bearing requirements**: mixing coefficients must be
   generic ring elements — **a scalar/real MDS (a tempting optimization)
   REVIVES a t-cell invariant subspace with trivial distinguisher and
   preimages on it**; and per-round σ-support is 2, not 3 (support-3 is only
   achieved across rounds).
5. **The round count is borrowed, not derived** — RF=8/RP=22 is a width-~12
   Poseidon set, but the object is a width-144 SPN with an O(t)-branch layer,
   and Poseidon's derivation assumes MDS. **Deriving it for the actual width
   and the measured degree curve is the design lane's first job.**
6. Minor: one splitting toy fails C4 (capacity 2^208 < 2^256); and security
   still rests on the same ideal-permutation heuristic as Poseidon, now with
   a weaker linear layer and thinner margin.

Not executed: a direct Gröbner/CICO attack (no Sage; sympy timed out at n=4)
— priced via the degree data instead, and said so.

**Handoff**: keep τ=1 (load-bearing); derive the round count; fix the two
validator gates; carry the degree deficit as a known margin cost.
