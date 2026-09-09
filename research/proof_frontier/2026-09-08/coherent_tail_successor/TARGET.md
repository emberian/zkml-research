[DERIVED — implemented] The prior finite-schedule proof used `earliest_transition_cover` to pick one round with a radius gap, then used only that round’s uniform query marginal. Five gaps gave τ=1/25. Summing lifted disagreement cardinalities is invalid because their sets can overlap under coherent seeds.

[DERIVED — theorem first] For the existing actual BabyBear tower 0→3→6→9→12→15, prefix-adaptive `Words`, degree 2^(19−3n), initially 2/5-far source, and independent scalar challenges plus q independent shared coherent seeds, prove:

```
Pr[Schedule.Accepts firstFifteen s degree q r seeds]
 ≤ 1198336 / 2013265921^4 + (4/5)^q.
```

[DERIVED — implemented invariant] Start consistency weights at one. At every transition average the prior weights over each actual eight-element folding fibre, then set the result to zero where the literal fold differs from the supplied next word. Maintain one weighted-agreement threshold θ=1/5 across every round. The degree-eight challenge term is unchanged. The injected input is fixed by the existing prefix-only `Words.input` interface before that round’s β; its term is β^8 g. The next word may depend on that β. Weights never depend on query seeds.

[DERIVED — minimal reuse] The frozen `hasGeometricMutualCorrelatedAgreement_fullUD` already controls failure on an arbitrary caller-specified dense agreement set. Since each weight is ≤1, a set of sufficient weight is sufficiently dense. Negating weighted correlated agreement on that same set therefore implies its existing mutual-CA failure event. No new root-union, unique-decoder, BW or gluing proof is needed. `curve_weighted_uniform_sound` derives the bound M*n/|F| directly from that existing theorem.

[DERIVED — exact consumer connection] `consistency_query_exact` proves terminal normalized consistency mass raised to q is exactly the existing coherent acceptance probability, conditional on terminal RS membership. It derives source squaring/modulo transport from the certified actual tower. It does not assume balanced maps or a desired query bound. Independence is used across q coordinates, never across the rounds of a shared query.

[DERIVED — controls] Nonconstant weights [1,4/5] on the existing F17 degree-seven example have actual weighted good scalars and fail weighted coefficient agreement. An overweight singleton refutes the density-domination step if weights≤1 is omitted. Identical Fin2 rejection sets refute naïve additive marginals. The actual full-size monomial strategy has initial farness, accepted zero queries and rejected seed-one queries; its normalized mass is strictly between zero and one. A separate finite-digest execution inhabits all causal/log certificates and deliberately rejects malformed paths.

[SOURCE] The consistency recurrence is motivated by local mirror 2020/654, printed pp42–44, Claim8.5 and the proof of Lemma8.2. That paper’s Johnson/rational-weight constants are not imported. Local mirror 2026/532, printed pp57–58, Theorems28/29 and Remark30 describes caller-specific agreement sets and arbitrary [0,1] weights, including the UD threshold; its pp61–66 give consistency-weight protocol use. Only the generic weight argument is adapted, not its circle protocol theorem. `SOURCES.json` pins both PDFs and records two orientation-only web searches, zero Scry SQL, zero PDF downloads.

[OPEN — execution boundary] This result controls the existing ideal/scalar supplied-opening consumer. A deployed IR2 verifier-to-model adapter covering actual packed MMCS, batching, serialized transcript and parameter schedule is still missing. Classical fresh-query coins are distinct from Fiat–Shamir/QROM coins. No ErrorBudget or deployed security claim changes here.
