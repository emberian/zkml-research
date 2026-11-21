# Machine-Checked Formalization of `EinSumcheck` in Lean 4 ("Selvage")

**Date**: 2026-11-20
**Artifacts**:
- `research/zktransformer_2026_11_20/formal/Theory/ZkmlEinsum.lean`
- `research/zktransformer_2026_11_20/formal/Assurance/ZkmlEinSumcheck.lean`
- `research/zktransformer_2026_11_20/formal/minidregg-einsumcheck.patch`
- `research/zktransformer_2026_11_20/formal/build_and_verify.sh`
**Companion base tree (read-only)**: `/Users/ember/dev/minidregg` (`leanprover/lean4:v4.35.0`)

---

## 1. Executive Summary & Findings

We formalized the general two-operand `EinSumcheck` arithmetization and sumcheck reduction of Chen, Tang, and Kang (*zkTransformer*, CCS 2026) [`[SOURCE: zkTransformer.txt:276-438, 1130-1242, §3 & App. F]`] against `minidregg` ("Selvage"), reusing `Theory/ZkmlTensorOps.lean`, `Theory/ZkmlMatmulSum.lean`, `Selvage/MultilinearExtension.lean`, `Selvage/EqPolynomial.lean`, `Selvage/MultilinearZeroTest.lean`, `Selvage/Rank1GradientCheck.lean`, `Assurance/AirSumcheckCubic.lean`, `Assurance/ZkmlMatmulSumcheck.lean`, and `Assurance/ZkmlMatmulCommitment.lean` with zero duplication.

### Four Main Formal Verdicts

1. **Theorem 3.1 (`EinSumcheck` Arithmetization) & App. F Eq. (10) (Unequal-Variable-Count Reduction) are Sound and Characteristic-Free `[EXECUTED / PROVED]`**:
   - `einsum_mle_identity` proves that for any trace-free two-operand contraction, binding degree-1 free indices $(x_L, x_R)$ ($F_1$) directly inside operand partial evaluations while summing shared free indices $h \in \{0,1\}^{\mu_S}$ ($F_{\ge 2}$) against $\widetilde{\mathrm{eq}}(x_S, h)$ yields an exact identity of 3-block multilinear extensions at **every** field point $(x_L, x_R, x_S) \in \mathbb{F}^{\mu_L} \times \mathbb{F}^{\mu_R} \times \mathbb{F}^{\mu_S}$.
   - Rather than appealing to polynomial uniqueness (`multiAffine_ext`), the proof composes `Selvage.eqMle_fold` on $\mu_S$ with `Assurance.mle₂_contraction` on $(\mu_L, \mu_R, \kappa)$ at each corner $h$.
   - `mle_extendRight` and `mle_extendLeft` prove over any `CommRing` that viewing an $m$-variable hypercube table as an $(m+n)$-variable table ignoring extra coordinates preserves `mle` identically. Instantiating `Assurance.cubicForm` (`einsum_is_cubicForm`, `einsum_asymmetric_terminal_factored`, `canonicalEq10_terminal_factored`) yields completeness (`einsumHonest_complete`), zero wiring commitments (`einsum_terminal_factored`), deployed-verifier equivalence (`einsumReal_iff_sumcheckAccepts`), and **characteristic-free** degree-3 rounds (unlike `zkTransformer` Alg. 1 [`[SOURCE: zkTransformer.txt:1205]`], whose $\{0,1,2,3\}$ evaluation grid requires $\mathrm{char}(\mathbb{F}) > 3$ and fails on binary towers $\mathrm{GF}(2^k)$).

2. **`zkGPT` Eq. (8)'s Naive `eq`-Free Batched Matmul Check Violates Completeness `[REFUTED: zkGPT Eq. 8 naive batched-matmul multilinearity]`**:
   - `zkTransformer` §3 [`[SOURCE: zkTransformer.txt:340-360]`] argues that checking `bij,bjk->bik` via $\tilde{Z}(r_b, r_i, r_k) \stackrel{?}{=} \sum_j \tilde{X}(r_b, r_i, j)\tilde{Y}(r_b, j, r_k)$ fails completeness because $r_b$ has degree 2 on the RHS and degree 1 on the LHS.
   - `NaiveBugRefutation` exhibits concrete honest 2-batch $2\times 2$ tables `bA, bB` over `ZMod 7` where the naive RHS agrees with $\tilde{Z}$ at **all** $2^3 = 8$ Boolean corners (`naive_batched_matmul_agrees_on_cube`), yet disagrees at $x_S = [2]$ (`4 ≠ 2`, `naive_batched_matmul_incomplete`) and rejects the **honest** witness on **5 of the 7** challenges in $\mathbb{F}_7$ (`naive_batched_matmul_rejects_five_of_seven`), whereas `EinSumcheck` passes (`einsum_batched_matmul_complete_at_two`) — all kernel-decided by `decide`.

3. **`zkTransformer` Lemma 3.2 Has Two Soundness Bugs; Repaired in `einsumcheck_soundness` `[REFUTED: zkTransformer Lemma 3.2 bound (m+1)·v/|F|]`**:
   `zkTransformer` Lemma 3.2 [`[SOURCE: zkTransformer.txt:370-388]`] claims total soundness error $\le \frac{(m+1)\cdot v}{|\mathbb{F}|}$ where $v = \max_t |\mathcal{I}_t|$ is the maximum variable count of a single input polynomial. This statement fails in two independent ways:
   - **Gap 3a — Omitted outer 3-block Schwartz–Zippel term**: When certifying a claimed output tensor $Z \neq \mathrm{einsumTable}(A, B)$, the outer random point $(x_L, x_R, x_S)$ can land on a root of $\tilde{Z} - \widetilde{\mathrm{einsumTable}(A, B)}$ with probability up to $\frac{\mu_L + \mu_R + \mu_S}{|\mathbb{F}|}$. `einsum_forged_survives` and `einsum_forged_accepts_end_to_end` construct a forged table `einsumForged ≠ einsumTable bA bB` over `ZMod 7` where at $o = ([1], [3], [2])$, running the **honest** sumcheck prover causes `EinSumcheckAccepts` to accept across **100% of sumcheck challenges $r$**! (In particular, at $\mu_S = \kappa = 0$, Lemma 3.2's sumcheck bound is $0$ while a forged outer-product table survives with positive probability $\frac{\mu_L + \mu_R}{|\mathbb{F}|}$.)
   - **Gap 3b — Wrong round count parameter $v = \max_t |\mathcal{I}_t|$**: When two operands carry disjoint summation indices ($\kappa_L > 0$ and $\kappa_R > 0$), the sumcheck runs $\mu_S + \kappa_L + \kappa_M + \kappa_R$ rounds, which **strictly exceeds** $v = \max(\mu_L + \mu_S + \kappa_L + \kappa_M,\, \mu_R + \mu_S + \kappa_M + \kappa_R)$ whenever degree-1 free indices are smaller than the opposite summation block (`lemma32_v_not_upper_bound_on_rounds`: for `bp,bq->b` with $\mu_S=1, \kappa_L=\kappa_R=2$, $v = 3$ while actual sumcheck rounds are $5$, so inner sumcheck error bound is $15/|\mathbb{F}| > 9/|\mathbb{F}|$). Conversely, when degree-1 free indices are large (such as GQA), $\mu_S + \kappa < v$.
   - **Repaired Theorem (`einsumcheck_soundness`)**: Against any wrong output table $Z \neq \mathrm{einsumTable}(A, B)$ and any adaptive degree-$\le 3$ prover (including provers that inspect $(x_L, x_R, x_S)$ before choosing round polynomials),
     $$\Pr[\mathrm{EinSumcheckAccepts}] \le \frac{\mu_L + \mu_R + \mu_S}{|\mathbb{F}|} + (\mu_S + \kappa)\cdot \frac{3}{|\mathbb{F}|}.$$

4. **Grouped-Query Attention (`igrc,jgc->grij` and `grij,jgc->igrc`) Saves $\log_2 G$ Rounds and Avoids $G\times$ `K`/`V` Commitment Blowup `[PROVED]`**:
   - In both GQA contractions (`einsum_gqa_scores_eq`, `einsum_gqa_valueOut_eq` in `Theory/ZkmlEinsum.lean`; `repeatKV_einsum_agrees`, `gqa_einsumcheck_soundness`, `gqa_rounds_saved` in `Assurance/ZkmlEinSumcheck.lean`), the query-within-group index $r \in \{0,1\}^{\mu_G}$ ($H = \mathrm{KV}\cdot G$) sits in left-only free $\mu_L$ ($F_1$) rather than shared free $\mu_S$ ($F_{\ge 2}$).
   - Consequently, sumcheck runs $\mu_{\mathrm{KV}} + \mu_C$ rounds instead of $(\mu_{\mathrm{KV}} + \mu_G) + \mu_C$ rounds, and commits native $K$ (and $V$) without `repeat_kv` duplication.
   - At `gpt-oss-20b` dimensions ($\mathrm{KV}=8=2^3$, $G=8=2^3 \Rightarrow H=64=2^6$, $\mathrm{HD}=64=2^6$, $S=1024=2^{10}$, `gptoss_20b_gqa_savings`), each attention score contraction runs **9 rounds instead of 12** and commits **524,288 `K` felts instead of 4,194,304** ($8\times$ smaller).

---

## 2. Theorem & Axiom-Pin Inventory

Every declaration below is machine-checked with zero `sorry`, zero `axiom`, and zero `native_decide`, and pinned with `#guard_msgs (whitespace := lax) in #print axioms`.

### 2.1 `Theory/ZkmlEinsum.lean` (`namespace Minidregg.Theory.ZkmlEinsum`)

Direct imports: `Theory.ZkmlMatmulSum` only (obeys `minidregg/scripts/check-import-boundary.sh` row `Theory -> Mathlib Lean Std Theory`).

| Declaration | Role / Mathematical Statement | Axiom Footprint |
|---|---|---|
| `einsumFold` / `einsumContract` | General 6-block canonical two-operand Einsum over `(mL, mR, mS; sL, sM, sR)` as nested `List.finRange` left fold (`ScalarOps α`) and unordered `Finset.sum` (`Semiring α`) | (defs) |
| `foldl_finRange_add_eq_sum` | General accumulator step reusing `ZkmlMatmulSum.foldl_add_eq_listSum` + `listSum_finRange_eq_sum` | `[propext, Classical.choice, Quot.sound]` |
| `einsumFold_addMonoid_eq_listSum` | Step 1 (associativity `AddMonoid α` alone): nested `foldl` equals nested ordered `List.sum` | `[propext, Quot.sound]` |
| `einsumFold_eq_contract` | Full `IsRingReading S` bridge: `einsumFold S A B iL iR h = einsumContract A B iL iR h` | `[propext, Classical.choice, Quot.sound]` |
| `einsumContract_factors` | Semiring marginalization: `∑_{pL,pM,pR} A·B = ∑_{pM} (∑_{pL} A)·(∑_{pR} B)` | `[propext, Classical.choice, Quot.sound]` |
| `einsumContract_eq_unified` | Equivalence of 6-block `(sL, sM, sR)` contraction with unified 4-block `Fin (sL * (sM * sR))` contraction ignoring unused coordinates | `[propext, Classical.choice, Quot.sound]` |
| `padded_einsum_summation` | Zero-padding summation blocks `(sL+tL, sM+tM, sR+tR)` leaves `einsumContract` pointwise invariant | `[propext, Classical.choice, Quot.sound]` |
| `padded_einsum_free` | Zero-padding free blocks `(mL+dL, mR+dR, mS+dS)` commutes with `einsumContract` (`= padFreeZ …`) | `[propext, Classical.choice, Quot.sound]` |
| `padded_einsum` | Simultaneous 6-axis dyadic zero-padding theorem | `[propext, Classical.choice, Quot.sound]` |
| `einsum_matmul_eq_run` | Specialization (i) `ij,jk->ik` (`mS=1`): equals `ZkmlTensorOps.run S (matmulTrace …)` | `[propext, Classical.choice, Quot.sound]` |
| `einsum_hadamard_eq_denote` | Specialization (ii) `i,i->i` (`sL=sM=sR=1`): equals `(TOp.bin .mul …).denote` | `[propext, Classical.choice, Quot.sound]` |
| `einsum_batchedMatmul_eq` | Specialization (iii) `bij,bjk->bik` (`mS=B`): equals batchwise `ZkmlMatmulSum.contract` | `[propext, Classical.choice, Quot.sound]` |
| `einsum_gqa_scores_eq` | Specialization (iv-a) GQA scores `igrc,jgc->grij` (`mL=G*Sq, mR=Skv, mS=KV, sM=HD`) | `[propext, Classical.choice, Quot.sound]` |
| `einsum_gqa_valueOut_eq` | Specialization (iv-b) GQA value output `grij,jgc->igrc` (`mL=G*Sq, mR=HD, mS=KV, sM=Skv`) | `[propext, Classical.choice, Quot.sound]` |
| `einsum_asymmetric_eq` | Specialization (v) `bsdhv,btdh->bsth` (`zkTransformer` App. F Eq. 9, `sL=V > 1`) | `[propext, Classical.choice, Quot.sound]` |
| `EinsumExample.gqa_witness_computes` | Kernel-decided `ℤ` GQA witness (`7` vs `11` across intra-group query heads sharing `K`) | `[propext, Classical.choice, Quot.sound]` |
| `EinsumExample.einsum_sat_bridge_fails` | Tooth (`decide`): non-associative `SatExample.satOps` breaks `einsumFold = einsumContract` (`5 ≠ 9`) | `[propext, Classical.choice, Quot.sound]` |
| `EinsumExample.bad_repeat_pad_summation_breaks` | Tooth (`decide`): repeat-padding `sR` instead of zero-padding `B` alters `einsumContract` (`12 ≠ 6`) | `[propext, Classical.choice, Quot.sound]` |

### 2.2 `Assurance/ZkmlEinSumcheck.lean` (`namespace Minidregg.Assurance`)

Direct imports: `Assurance.ZkmlMatmulCommitment`, `Theory.ZkmlEinsum` (obeys `minidregg/scripts/check-import-boundary.sh` row `Assurance`).

| Declaration | Role / Mathematical Statement | Axiom Footprint |
|---|---|---|
| `mle_extendRight` / `mle_extendLeft` | Suffix/prefix projection MLE invariance over any `CommRing` (`zkTransformer` Alg. 1 core) | `[propext, Classical.choice, Quot.sound]` |
| `mle₂_ignore_snd` / `mle₂_ignore_fst` | Curried 2-block projection invariance | `[propext, Classical.choice, Quot.sound]` |
| `mle₃_agrees` / `mle_flatten₃` | 3-block MLE cube agreement and equivalence with 1-cube `mle (flatten₃ f)` | `[propext, Classical.choice, Quot.sound]` |
| `mle₃_zero_uniform_bound` | 3-block multilinear Schwartz–Zippel: `f ≠ 0 → Pr[mle₃ f = 0] ≤ (μL + μR + μS)/|F|` | `[propext, Classical.choice, Quot.sound]` |
| `einsum_mle_identity` | **Theorem 1** (`zkTransformer` Thm 3.1): `Ẑ(xL,xR,xS) = ∑_{h,p} eq(xS,h)·Â(xL,h,p)·B̂(xR,h,p)` | `[propext, Classical.choice, Quot.sound]` |
| `einsum_zero_shared_is_matmul` | At `μS = 0`, `einsum_mle_identity` collapses identically to Thaler's `mle₂_contraction` | `[propext, Classical.choice, Quot.sound]` |
| `naive_batched_matmul_agrees_on_cube` | `zkGPT` Eq. 8 naive sum agrees with `Ẑ` on all $2^3$ corners over `ZMod 7` (`decide`) | `[propext, Classical.choice, Quot.sound]` |
| `naive_batched_matmul_incomplete` | **Theorem 2** (`decide`): at `xS = ![2]` in `ZMod 7`, naive `eq`-free sum `4 ≠ 2 = Ẑ` | `[propext, Classical.choice, Quot.sound]` |
| `naive_batched_matmul_rejects_five_of_seven` | Naive check rejects honest `bA, bB` on 5 of 7 challenges in `ZMod 7` (`decide`) | `[propext, Classical.choice, Quot.sound]` |
| `einsum_is_cubicForm` / `einsum_claim_total` | **Theorem 3a**: `(μS+κ)`-cube summand is `AirSumcheckCubic.cubicForm` (`C≡0, D≡1`) summing to `Ẑ` | `[propext, Classical.choice, Quot.sound]` |
| `einsumHonest_complete` | **Theorem 3b**: `einsumHonest` passes `SumcheckAccepts` at every outer & round challenge | `[propext, Classical.choice, Quot.sound]` |
| `einsum_terminal_factored` | **Theorem 3c**: terminal check factors as `eqMle xS r_S * (Â(xL,r_S,r_κ) * B̂(xR,r_S,r_κ))` (0 wiring commits) | `[propext, Classical.choice, Quot.sound]` |
| `einsum_asymmetric_terminal_factored` | **Theorem 3d**: unequal summation variable counts `(κL+κM)` vs `(κM+κR)` project cleanly onto `r_κ1, r_κ2` | `[propext, Classical.choice, Quot.sound]` |
| `canonicalEq10_terminal_factored` | `zkTransformer` App. F Eq. (10) `∑_{x,y,z} eq(r,x)·T₁(x,y)·T₂(x,y,z)` factored terminal check | `[propext, Classical.choice, Quot.sound]` |
| `einsumReal_iff_sumcheckAccepts` | Discharges idealization: `EinsumRealAccepts` (no honest side) $\iff$ `SumcheckAccepts` under authentic openings | `[propext, Classical.choice, Quot.sound]` |
| `einsumcheck_soundness` | **Theorem 4** (repairs Lemma 3.2): `Z ≠ einsumTable A B → Pr[Accepts] ≤ (μL+μR+μS)/|F| + (μS+κ)·(3/|F|)` against adaptive outer-aware degree-$\le 3$ provers | `[propext, Classical.choice, Quot.sound]` |
| `einsumcheck_soundness_fixedOuter` | Corollary for outer-independent sumcheck provers | `[propext, Classical.choice, Quot.sound]` |
| `SoundnessTeeth.einsum_forged_survives` | Tooth (`decide` over `ZMod 7`): `einsumForged ≠ einsumTable bA bB` agrees with truth at `o = (![1],![3],![2])` | `[propext, Classical.choice, Quot.sound]` |
| `SoundnessTeeth.einsum_forged_accepts_end_to_end` | Tooth: at `o = (![1],![3],![2])`, `EinSumcheckAccepts` holds for **every** sumcheck challenge `r` | `[propext, Classical.choice, Quot.sound]` |
| `SoundnessTeeth.lemma32_v_not_upper_bound_on_rounds` | Tooth (`decide`): `bp,bq->b` has $v = 3$ variables per operand yet runs $5$ sumcheck rounds | `[]` (no axioms) |
| `repeatKV_einsum_agrees` | Native GQA `gqaCubeScores Q K` equals `repeatKV` batched matmul at every `(g,r,i,j)` | `[propext, Classical.choice, Quot.sound]` |
| `gqa_einsumcheck_soundness` | Native GQA soundness in `μKV + μC` rounds (`μG` confined to outer SZ numerator) | `[propext, Classical.choice, Quot.sound]` |
| `gqa_rounds_saved` / `gptoss_20b_gqa_savings` | **Theorem 5**: saves `μG` rounds (`9` vs `12` in `gpt-oss-20b`) and `2^μG`× (`8×`) `K` table size | `[propext, Classical.choice, Quot.sound]` |

---

## 3. Reproducible Verification & Patch Application

### Standalone Read-Only Verification (`[EXECUTED]`)

`formal/build_and_verify.sh` compiles the `minidregg` dependency cone (`leanprover/lean4:v4.35.0`, reading Mathlib `.olean`s via `lake --dir /Users/ember/dev/minidregg env` and placing local `.olean`s in `formal/build/` without touching `/Users/ember/dev/minidregg`):

```bash
/Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/formal/build_and_verify.sh
```

Recorded execution output (`[EXECUTED]`, 2026-11-20, zero warnings, zero errors):

```text
  [LOCAL  9.17s] Theory.ZkmlEinsum -> rc=0
  [LOCAL  4.97s] Assurance.ZkmlEinSumcheck -> rc=0
Verified cleanly in 14.14s
Import boundary OK for Theory/ZkmlEinsum.lean: ['Theory.ZkmlMatmulSum']
Import boundary OK for Assurance/ZkmlEinSumcheck.lean: ['Assurance.ZkmlMatmulCommitment', 'Theory.ZkmlEinsum']
Wrote /Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/formal/minidregg-einsumcheck.patch (109608 bytes)
git apply --check against /Users/ember/dev/minidregg: OK
```

`/Users/ember/dev/minidregg` status remained untouched throughout (`git -C /Users/ember/dev/minidregg status -s` unchanged).

Once `formal/build/` is populated, incremental kernel verification of both files runs in seconds:

```bash
FORMAL=/Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/formal
LEAN_BIN=/Users/ember/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean
LAKE_BIN=/Users/ember/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake
PKG_PATH=$("$LAKE_BIN" --dir /Users/ember/dev/minidregg env printenv LEAN_PATH | tr ':' '\n' | grep -v '^/Users/ember/dev/minidregg' | paste -sd: -)
LEAN_PATH="$FORMAL/build:$PKG_PATH" "$LEAN_BIN" -R "$FORMAL" -o "$FORMAL/build/Theory/ZkmlEinsum.olean" "$FORMAL/Theory/ZkmlEinsum.lean"
LEAN_PATH="$FORMAL/build:$PKG_PATH" "$LEAN_BIN" -R "$FORMAL" -o "$FORMAL/build/Assurance/ZkmlEinSumcheck.olean" "$FORMAL/Assurance/ZkmlEinSumcheck.lean"
```

### Applying to `minidregg`

`formal/minidregg-einsumcheck.patch` is a clean `git apply`-ready unified patch adding `Theory/ZkmlEinsum.lean`, `Assurance/ZkmlEinSumcheck.lean`, and their root barrel imports in `Theory.lean` and `Assurance.lean`.
