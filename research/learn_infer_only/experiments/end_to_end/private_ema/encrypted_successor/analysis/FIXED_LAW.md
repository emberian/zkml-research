# Exact dynamics of the unchanged signed-floor update

[DERIVED] For one selected register, write `F_u(s)=floor((7s+u)/8)` with
`u∈{-120,120}`. This note analyzes the already frozen law; it chooses no new
learner or fixture. Unselected registers are unchanged, so each register
follows the same recurrence on its own subsequence of teaching events.

[DERIVED invariant] For `-120≤s≤120`, the numerator lies in [-960,960], hence
`-120≤F_u(s)≤120`. Monotonicity of integer floor makes each `F_u` monotone.
For positive teaching the worst initial state for a correct sign is -120;
for negative teaching it is +120. Their first six selected updates are:

```
u=+120: -120 → -90 → -64 → -41 → -21 → -4 → 11
u=-120:  120 →  90 →  63 →  40 →  20 →  2 → -14
```

[DERIVED] Therefore six consecutive consistent labels **at that same bin**
guarantee a correct sign from every state in the invariant range. Five do
not suffice for either endpoint witness. Once correct, another identical
label preserves the sign. This is a deterministic property of the finite
learner, not a guarantee that the semantic issuer supplies consistent labels
or that six arbitrary routed updates suffice.

[DERIVED quantization] Let the real-valued recurrence on the same selected
label subsequence be `x_(n+1)=(7*x_n+u_n)/8`, with the same initial integer
state. Each floor adds `e_n∈[-7/8,0]`. Unrolling gives

```
s_n - x_n = Σ_(i=0)^(n-1) (7/8)^(n-1-i) * e_i
-7*(1-(7/8)^n) ≤ s_n-x_n ≤ 0.
```

[DERIVED] Signed-floor quantization is biased downward. Solving
`s=F_u(s)` over integers gives `u-7≤s≤u`. Within [-120,120], positive constant
input has fixed points 113 through 120; negative constant input has only
-120. From the specified zero initialization, constant positive labels
converge to 113 and constant negative labels to -120. Thus a claim of
symmetrical ±120 asymptotes for the exact integer law would be false.

[EXECUTED] `fixed_law.py` checks all 482 state/label cases and adjacent-state
monotonicity using Python integers and exact `Fraction` residuals. Breadth-first
closure from zero reaches all 234 values in [-120,113]. Constant input from
zero reaches each named fixed point after 25 selected updates. It also checks
the six-update worst cases and retains every orbit in `fixed_law.json`.

[DERIVED scope] The invariant-range counterexample `113,120` under repeated
positive input preserves a difference forever, so exact state forgetting
does not follow merely from the real EMA contraction formula on that larger
domain. State 120 is unreachable from this run's zero initialization; this
counterexample is not a claim about its reachable-state behavior.

[EXECUTED command] `python3 -B research/learn_infer_only/experiments/end_to_end/private_ema/encrypted_successor/analysis/fixed_law.py > research/learn_infer_only/experiments/end_to_end/private_ema/encrypted_successor/analysis/fixed_law.stdout`.
Script SHA-256 is
`04939ae8ba8f0006c1e3bf269d2d196866149fe3d7c08932a0fae940fd7ecbea`.
This is a short mathematical derivation and exhaustive finite check, not a
Lean/kernel proof, new utility evaluation or encrypted execution.
