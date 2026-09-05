# eprint 2026/1792 (nonlinear subspace trails) evaluated at our Merkle node — 2026-09-04

**Paper**: Li–Liu–Wang, *"Beyond Linear Subspace Trails: Nonlinear Subspaces for Gröbner Basis
Attacks on Poseidon/Poseidon2 and Neptune"*, eprint 2026/1792, 49 pp.
Local: `/Users/ember/dev/gh/forks/IACR-eprint-mirror/2026/1792.pdf` (read via `pdftotext`, plain
and `-layout`; page numbers below are the PDF's printed page numbers).
**Script**: `notes/gsr-scripts/nst_1792.py` (no dependencies; `python3 nst_1792.py`, < 2 s).
**Charge**: what does 1792's own cost model give for a preimage/CICO attack on our deployed
Merkle internal node `TruncatedPermutation<Perm16, 2, 8, 16>` = Trunc₈(P(x‖y)) (compression
mode, c = 0, d = 8, no feed-forward) and on the leaf sponge `PaddingFreeSponge<Perm16,16,8,8>`
(c = 8, d = 8), at BabyBear p = 2013265921, t = 16, α = 7, R_F = 8, R_P ∈ {13, 20}?
[OURS] type aliases: `breadstuffs/circuit/src/plonky3_prover.rs:71-72`, `stark_zk.rs:79-80`.

---

## 0. The answer in three lines

1. **[DERIVED, 1792's formulas, ω = 2] Every attack model in the paper costs ≥ 2^511.9 on the
   Merkle node at R_P = 13** (cheapest: the *basic* attack, 8 variables, degree capped at p − 2;
   the nonlinear-trail models cost 2^816–2^878; at ω = 2.37 the cheapest is 2^606.6). That is
   **+384 bits above 2^128**, +388 above the 2^124 collision bar, +412 above the 100-bit bar,
   and **+264 bits above the 2^248 generic preimage bound** — the model never beats generic.
   **R_P = 20 changes nothing at the floor** (the cheapest model does not use partial rounds
   beyond the p − 2 cap): still 2^511.9; the trail models rise to 2^996–2^1136.
2. **The trail does cover all 13 partial rounds** (E_c = t − d = 8, nonlinear trail 2E_c + 1 = 17
   > 13) — hash-delta §7.2's structural reading is confirmed — **but in this model coverage is
   not cost**: after the trail, 8 full rounds at α = 7 with n ≥ 16 variables leave a Macaulay
   binomial of 2^408–2^439 (squared: 2^816–2^878). The 2^128 line is not "crossed by the first
   un-absorbed partial round"; it is crossed ~380 bits below the flat cost of the full rounds.
3. **The compression node is NOT weaker than the leaf sponge in this model.** Both floor at the
   identical 2^511.9 (basic attack, n = d = 8, degree p − 2). The node has *more* models
   available (E_c = 8 vs 0) but each carries ≥ 16 variables and is dearer than the basic attack.
   So for 1792, VERDICTS §5h's sentence *"the instances GSR breaks are not the instances
   carrying our security claim"* **holds by ≥ 264 bits** — and holds for the node, not only the
   sponge.

Regime: **far above 2^128, and the binding quantity is the number of output constraints d = 8
(→ ≥ 8 variables) times the p − 2 degree cap, not R_P.** Caveats in §4 — this is a
semi-regular Macaulay *estimate*, which the paper itself calls "a loose upper bound" (p. 10).

---

## 1. The cost model, quoted [READ]

- **E_c** — *"In compression mode, the corresponding budget is Ec = t − d"* (§2.2, p. 9; again
  §3, p. 10); *"we take min{c, d} = d without loss of generality. Then Ec = r − min{c, d} = r − d
  = t − (c + d). In compression mode, one has Ec = t − min{c, d} = t − d"* (§4.1, p. 23).
- **Trail length** — *"when s = 1, the length is extended from Ec to 2Ec"* (§3, p. 10);
  *"after the intermediate state passes through 2⌊Ec/s⌋+1 partial rounds, its degree grows only
  from degree one to degree α"* (§3.3, p. 21). So 2E_c + 1 partial rounds contribute one factor α.
- **Gröbner cost** (§2.3, p. 10): *"the degree of regularity is estimated by the Macaulay bound
  dreg = 1 + Σ(δᵢ − 1). Hence, the complexity of the F4/F5 stage is estimated as C_GB =
  O(binom(dreg + n, n)^w) = O(binom(Σδᵢ + 1, n)^w), where 2 ≤ w < 3."* FGLM: *"C_FGLM =
  O(n·D_I^ω) … the Bézout bound D_I ≤ Πδᵢ"*. Tables use **ω = 2 for C_GB, ω = 3 for C_FGLM**
  (Table C.1 caption, p. 48; Fig. 5 caption "Here ω = 2", p. 27).
- **Univariate (d = 1)**: *"C_Graeffe(δ) = O(δ log δ (log p − log δ + 1) log log δ)"* (§2.3, p. 9);
  bivariate (d = 2): C_RES(δx, δy) = O(δy M(δxδy) log(δxδy)).
- **Degree cap**: *"if the digest side equations reach degree p − 2 in some instances, we
  estimate their degree as p − 2"* (§4.1 (6), p. 25). For BabyBear the cap binds at 7^12
  (7^11 = 1977326743 < p − 2 = 2013265919 < 7^12).
- **Model 3, Forward+Substitution+Nonlinear** (§4.1, p. 24): *t* equations of degree α^{r_f+τ}
  at the subspace, *E_c* equations of degree α, *d* digest equations of degree α^{r_f'+r_P−τ−2E_c};
  *"The total number of variables is r + t = 2t − c"*; **C_GB = min over 0 ≤ τ ≤ r_P − (2E_c+1)
  of binom(1 + t·α^{r_f+τ} + d·α^{r_f'+r_P−τ−2E_c} + E_c·α, 2t − c)^w.** Model 5
  (Nonsubstitution+Nonlinear): binom(1 + d·α^{r_F+r_P−2E_c} + E_c·α^{r_f+1}, r)^w with r = t − c.
  Model 1 (basic): *d* equations of degree α^{r_F+r_P}; d = 1 → Graeffe, d = 2 → resultant,
  d ≥ 3 → GB (§4.1 (1), p. 23). Models 2/4 are the linear-trail analogues (E_c rounds, no
  degree-α constraints).
- **"Round number"** (§4.2, p. 26): *"the minimum number of internal partial rounds required
  for the corresponding algebraic solving complexity to reach or exceed 2^128 … we fix the
  security target at 128 bits and keep the number of external full rounds unchanged."*
  [INFERRED, confirmed by reproduction] the minimum is taken over r_P at or above the model's
  trail floor (2E_c + 1 for nonlinear, E_c for linear — the τ-range is empty below it).

---

## 2. Reproduction (calibration before use)

**Table C.1** (p. 48; Poseidon2 sponge, r_F = 6, ω_GB = 2 / ω_FGLM = 3, entries C_GB/C_FGLM):
**58/58 cells reproduced exactly**, including the three cells where the *cost* rather than the
trail floor decides, and the FGLM column (evaluated at the C_GB-optimal τ):

| cell | paper | computed | intermediates at the crossing |
|---|---|---|---|
| d: p≈2^256, α=3, t=4 | **10/9** | 10/9 | r_P=9: τ*=2, n=7, Σδ=1707 → GB 2^125.7 (<128), FGLM 2^135.9; r_P=10: Σδ=3165 → GB 2^138.2 |
| d: t=6 | **10/10** | 10/10 | r_P=9: τ*=0, n=11, Σδ=255 → GB 2^124.9, FGLM 2^127.1; r_P=10: Σδ=417 → 2^140.7 / 2^131.8 |
| e: α=5, t=4 | **6/5** | 6/5 | r_P=5: n=7, Σδ=1135 → GB 2^117.4, FGLM 2^128.2; r_P=6: τ*=1, Σδ=3135 → GB 2^138.0 |
| f: α=7, t=4 | 5/5 | 5/5 | r_P=5 (= floor): Σδ=3787 → GB 2^141.8 — already above 2^128 at the floor |
| all other 54 cells | 2E_c+1 | 2E_c+1 | cost at the floor ≥ 2^164.9 (smallest: row b, t=8) — floor binds |

(⚠ Column alignment: `-layout` shows row a's first entry under **t = 12**, not t = 10;
hash-delta §7.2's "t=10, p≈2^64: E_c=2 → 9" read the wrong column. Row a at t = 12 is
E_c = 4 → 9. Every α = 3 cell in rows a–c is also 2E_c + 1.)

**Table C.2** (p. 49; compression mode, c = 0, r_F = 6): **21/21 entries reproduced** —

| instance | baseline / margin | basic | sub+lin | sub+nonlin | nonsub+lin | nonsub+nonlin |
|---|---|---|---|---|---|---|
| p≈2^64, t=24, d=4, α=3, E_c=20 | 39 / 42 ✓ | **4** ✓ (r_P=3: 2^120.9; r_P=4: 2^133.6, n=4) | 20 ✓ | 41 ✓ | 20 ✓ | 41 ✓ |
| p≈2^256, t=22, d=1, α=7, E_c=21 | 43 / 47 ✓ | **34** ✓ (Graeffe, 7^39: 2^126.2; 7^40: 2^129.1) | 21 ✓ | 43 ✓ | 21 ✓ | 43 ✓ |
| p≈2^256, t=24, d=1, α=7, E_c=23 | 43 / 47 ✓ | 34 ✓ | 23 ✓ | 47 ✓ | 23 ✓ | 47 ✓ |

Baseline = 1 + ⌈min(κ, log₂p)/log₂α⌉ + ⌈log_α t⌉ − r_F, margin = ⌈1.075·r_P⌉ (§2.1, p. 8;
the r_GB term never binds here) [DERIVED, 6/6]. The basic-attack rows only reproduce with
**n = d variables** (the r − d spare inputs fixed) — that convention is carried to our point.

What the reproduction does and does not certify: the three non-floor cells and the basic-attack
crossings pin the formula's *constants* (exact binomials, ω = 2, no hidden factor, log = log₂ in
Graeffe, FGLM at the GB-optimal τ); the 55 floor cells certify only that the cost at the floor
is ≥ 2^128 there (script prints the six lowest floor costs; 55/58 cells are ≥ 2^128 at the
floor, the other three being exactly the cost-decided cells). No fitted parameter anywhere.

---

## 3. Our point — every intermediate (ω = 2 unless stated)

Inputs: p = 2013265921 (≈ 2^30.9), t = 16, α = 7, r_f = r_f' = 4 (R_F = 8). Bars: 2^128
(paper), 2^124 (our 8-element collision claim), 2^100 (VERDICTS §1 realized soundness), 2^248
(generic preimage of 8 elements). "Literal" = the paper's formula with all E_c constraints;
"attacker-optimal" = my extension letting the attacker use E_c' ≤ E_c constraints and fix the
unused inputs (fewer variables) [INFERRED, marked].

### 3a. Merkle node — compression, c = 0, d = 8: E_c = 8, nonlinear trail 2E_c+1 = 17, linear E_c = 8

| model | R_P = 13 | R_P = 20 |
|---|---|---|
| trail vs R_P | 17 > 13: **all 13 partial rounds absorbed**, 4 rounds of trail to spare; τ-range empty | 17 ≤ 20: 3 un-absorbed |
| 1 basic (n = d = 8; 7^21 → **capped p−2**) | Σδ = 8(p−2) = 1.61e10, d_reg ≈ 1.61e10 → **2^511.9** | 7^28 capped → **2^511.9** |
| 2 sub+lin (n = t+d = 24) | τ*=2, deg_sub 7^6, deg_dig 7^7, 3 un-absorbed → 2^946.6 (FGLM 2^1284.7) | τ*=6, 7^10/7^10 → 2^1409.5 |
| 3 sub+nonlin literal (n = 2t−c = 32) | τ=0 flat: 16·7^4 + 8·7^5 + 8·7 = 172928, d_reg 172897, log₂binom = 439.1 → **2^878.3** (FGLM 2^948.3) | τ*=2, deg_dig 7^6, 1 un-absorbed, Σδ = 2823632 → 2^1136.1 |
| 3 attacker-optimal | E_c' = 6 (trail exactly 13), n = 30 → 2^828.6 | same as literal |
| 4 nonsub+lin (n = r = 16) | deg_con 7^4, deg_dig 7^13 capped → 2^996.5 | 7^20 capped → 2^996.5 |
| 5 nonsub+nonlin literal (n = 16) | flat: 8·7^5 + 8·7^9 = 322963312 → **2^816.0** (FGLM 2^947.3) | 7^12 capped → 2^996.5 |
| 5 attacker-optimal | collapses to E_c' = 0, n = 8 = basic → 2^511.9 | 2^511.9 |
| **cheapest** | **2^511.9 (basic)**; ω = 2.37: 2^606.6 | **2^511.9**; ω = 2.37: 2^606.6 |
| distance | +383.9 / +387.9 / +411.9 bits vs 2^128 / 2^124 / 2^100; **+263.9 vs generic 2^248** | identical |

### 3b. Leaf sponge — c = 8, d = 8, r = 8: E_c = r − min{c,d} = 0 (no trail of either kind)

| model | R_P = 13 | R_P = 20 |
|---|---|---|
| 1 basic (n = 8; 7^21 capped) | **2^511.9** | 2^511.9 |
| 2/3 sub (n = 2t−c = 24; deg_dig 7^17 capped) | 2^1469.5 (FGLM 2^1285.4) | 2^1469.5 |
| 4/5 nonsub (n = r = 8; E_c = 0 → identical to basic) | 2^511.9 | 2^511.9 |
| **cheapest** | **2^511.9** — same floor as the node | same |

### 3c. CICO-d sweep on the node at R_P = 13 (context; only d = 8 is the Merkle claim)

| d | E_c | 2E_c+1 | cheapest model | cost | generic 31·d |
|---|---|---|---|---|---|
| 1 | 15 | 31 | basic, Graeffe on degree p−2 | 2^38.2 | 2^31 |
| 2 | 14 | 29 | basic, resultant | 2^107.2 | 2^62 |
| 3 | 13 | 27 | basic, GB n=3 | 2^189.8 | 2^93 |
| 4 | 12 | 25 | basic, GB n=4 | 2^254.1 | 2^124 |
| 8 | 8 | 17 | basic, GB n=8 | 2^511.9 | 2^248 |

The trail models (n ≥ 23 with substitution) are never cheapest at any d on our node. **At no d
does 1792's model beat the generic bound on our permutation** — including d = 1, where GSR's
different (resultant + Cantor–Zassenhaus, 1-variable) route gave 2^27.4 (§5h). That is the
whole difference between the two papers' reach at our point: variable count.

---

## 4. Caveats — what would change the number

1. **This is a model, and the paper says which kind.** *"Structured polynomial systems from
   symmetric cryptography often do not satisfy the regularity assumption … the regular system
   estimate is still commonly used as a loose upper bound in design analyses"* (p. 10). The
   2^512 is a Macaulay/semi-regularity *estimate* of F4/F5 work; it is not a lower bound on any
   attacker, and the paper tested semi-regularity only for its α = 3 systems (§4, p. 22). GSR's
   2^27.4 at CICO-1 (a 1-variable resultant route) is the standing demonstration that a
   different solver shape can sit hundreds of bits below this estimate at small d. **What
   would move our number: a technique that solves the d = 8 CICO with fewer than 8 effective
   variables** (none is claimed by 1792, GSR, or CheapLunch; GSR is vacuous at k = 8, §5h).
2. **Validity envelope.** 1792 tabulates p ≥ 2^64, d ≤ 4, r_F = 6. Our p ≈ 2^31 enters only
   through the p − 2 cap (their rule, inherited from GKR25 §5.1's saturation regime), which
   *helps* the attacker and is applied here; R_F = 8 and d = 8 are ordinary parameter values
   of the same formulas (r_f, r_f', d are free in every model) — inside the model, outside the
   tables. Nothing in §3.3's construction depends on p, and the construction uses "only the
   partial round structure" (p. 10) — so the trail itself reaches us; the cost does not.
3. **Attack shape.** 1792 models *preimage/CICO* (fixed inputs, fixed outputs). Our Merkle claim
   is *collision* resistance of Trunc₈∘P (2^124 birthday) plus preimage (2^248). No collision
   model appears in the paper; the CICO-8 number is the relevant preimage number and the sweep
   shows nothing below generic at any d. Both bars reported in §0.
4. **ω.** Paper: ω = 2 for C_GB (Table C.1 caption, Fig. 5) and ω = 3 for C_FGLM; the model's
   own range is "2 ≤ w < 3". Reported at ω = 2 (their choice, the most attacker-favourable) and
   ω = 2.37 (+95 bits at the floor). FGLM at every point is *higher* than C_GB, so it never
   binds — consistent with their "we treat the F4/F5 stage as the main bottleneck" (p. 26).
5. **Fixed-inputs convention.** The basic attack's n = d (fix r − d inputs) is forced by
   reproducing Table C.2's basic-attack entries (4 and 34); with n = r the cost would be far
   larger. This convention is what makes the basic attack the cheapest model at our point.
6. **The literal formula is undefined at R_P < 2E_c + 1** (empty τ-range). I report the flat
   extension (degree α at the end of the trail regardless of unused trail length — §3.3's own
   statement) and an attacker-optimal variant; both are ≥ 2^816 at the node, and neither is the
   binding model.
7. **Round-number semantics** — corrects hash-delta §7.2. Its reading *"six full rounds at α=7
   plus ZERO un-absorbed partial rounds sit BELOW 2^128 — the 2^128 line is crossed by the first
   partial round the trail cannot reach"* is not what the tables encode: the entry 2E_c + 1 is
   the **model's trail floor** (the minimum r_P at which the full-E_c model is defined), and at
   that floor the cost is already ≥ 2^128 in 55/58 cells (≥ 2^164.9 for every t ≥ 8). Only three
   cells (t ≤ 6, α ≤ 5, p ≈ 2^256) need partial rounds beyond the trail. So "security rests on
   the full rounds alone" is right; "the full rounds are below 2^128" is not, at any t ≥ 8.
8. **R_P 13 → 20**: in this model it moves only the trail-based costs (2^878 → 2^1136 for
   Model 3) and leaves the floor untouched; it is not an argument for or against the §5h
   repair. hash-delta §7.2's "1792 is a second, independent argument for going straight to 20"
   does not survive the computation — the number that argument needed (a sub-2^128 flat cost)
   does not exist at t = 16, α = 7.

---

## 5. Script

`/Users/ember/dev/zkml-research/notes/gsr-scripts/nst_1792.py` — `python3 nst_1792.py`.
Prints: Table C.1 (58 cells, printed vs computed, with the crossing intermediates), Table C.2
(21 entries), then both objects × R_P ∈ {13, 20} × ω ∈ {2, 2.37} with n, E_c, E_c', τ*, per-class
degrees, un-absorbed partial rounds, Σδ, d_reg, C_GB, C_FGLM, and the distance to each bar; then
the CICO-d sweep. Pure `math.comb` on exact integers; no fitted constants.
Companion: `gsr_calc.py` (GSR 2026/1692, Table 1 5/5) — the two models are not commensurable
(resultant/Cantor–Zassenhaus with k variables vs Macaulay-bound F4/F5 with 2t − c), and this
note does not compare their numbers except to name why they differ (§3c).
