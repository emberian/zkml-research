# MoE router binding: a protocol spec for proof cost ∝ active parameters

2026-08-13, Fable. Pillar III item, mapping **C** of `notes/ml-to-crypto-mappings.md`.

> ## ⚑ RETRACTION FIRST: the absence is FALSE, and the refutation was in `~/paperbin/`
>
> Mapping C was recorded as **"zero hits across 7,090 swept papers"** and
> **"absent from the log and from every zkML paper we read; all of them prove dense
> models"** — an absence the agenda repeats as `[measured absence]`. **It is wrong.**
> Two papers refute it, and **both were already sitting in `~/paperbin/`, pulled and
> correctly named, on the same day the absence was declared** (2026-08-12):
>
> - **`zkdeepseek-2511.19902.pdf`** — ZK-DeepSeek. Builds a SNARK-verifiable
>   DeepSeek-V3, **proves top-k expert selection including the grouped two-round
>   routing**, and proves only the dynamically-loaded selected experts. Pulled
>   Aug 12 09:49; text extracted Aug 12 23:39.
> - **`zk-frontier-ai-training-2606.05433.pdf`** — its **OP-10, "Mixture-of-experts
>   verification"**, names routing commitment, top-K verification, and deterministic
>   tie-breaking as protocol sub-problems. Present in paperbin under *three*
>   filenames.
>
> The sweep that reported the absence read first-2-page caches; both papers bury MoE
> in a §4.3 and an appendix A.5. **A keyword sweep over abstracts cannot see a
> contribution that lives in a subsection**, and "verified absence, twice" was two
> runs of the same blind instrument, not two witnesses. This is a
> `documented ≠ detected` instance with the documents *in our own hands*.
>
> §7 gives the corrected prior art and the distance that actually remains. The
> spec's contribution is now **a cheaper statement, a soundness bug in the published
> construction, and the identity-binding problem neither paper addresses** — not
> priority.

Every number below is **derived**, and the derivation is in this repo and runnable:
**`notes/moe-router-binding-cost.py`** (`python3 notes/moe-router-binding-cost.py`
reprints every table in §2.2, §3.2, §5.4 and §6.3). Model
shapes come from the real `config.json` and the real reference implementations,
pulled at HEAD — **not from the brief**, which was wrong about the router in three
ways (§1). Design decisions are marked **DECIDED** or **OPEN** with reasons.

---

## 0. The result in one paragraph

For DeepSeek-V3 the honest sparse-proving discount is **18.3× at short context and
2.7× at 128k context** — the "~18×" figure in the agenda is a *single-token* number
and decays with sequence length (§3.4); nobody has published this decay. The router
binding that makes the discount sound costs **0.72% of committed elements and 1.09%
of lookup rows** on top of proving the 9 active experts; the selection argument
proper is **0.36%**. So the binding is not the problem — *it was never going to be
the problem, because the router matmul is dense and every logit the argument needs
is in the trace already.* The four real problems, of which **three are open against
the published work**: **(i)** the top-k tie-break — ZK-DeepSeek's sorted form admits
ties and is **unsound** without it, and 2606.05433 calls ties "rare with BF16", which
§5.4 shows is **backwards: at bf16 boundary ties are the common case**; **(ii)**
binding expert *identity* naively costs a full-dense MLE opening, destroying the
entire discount unless weights are committed **per expert** (§5.3) — neither paper
addresses it, and that per-expert commitment is exactly the Pillar III registry;
**(iii)** the router is the one place in a transformer where a 1-ulp numerical
difference produces an **O(1) output difference**, so exact arithmetization is
strictly binding there (§5.7); **(iv)** the threshold statement (§2.3) is **Θ(N)**
against the **Θ(N log K)** decomposition 2606.05433 assumes, and drops the multiset
argument ZK-DeepSeek pays for.

---

## 1. The object: what a real MoE router computes

Three reference implementations read at source. **The brief's model — "softmax over
selected logits, plain top-k" — is not what DeepSeek-V3 does**, and the differences
are load-bearing for the proof.

### 1.1 DeepSeek-V3 (`config.json` + `modeling_deepseek.py`, HF @ main)

```
hidden_size 7168 · moe_intermediate_size 2048 · num_hidden_layers 61
first_k_dense_replace 3            → 58 MoE layers, 3 dense
n_routed_experts 256 · n_shared_experts 1 · num_experts_per_tok 8   → E=257, k_active=9
n_group 8 · topk_group 4           → GROUPED routing, 32 experts/group
scoring_func "sigmoid" · topk_method "noaux_tc" · norm_topk_prob true
routed_scaling_factor 2.5
```

`MoEGate.forward`, exactly:

1. `l = W_r · h`, `W_r ∈ R^{256×7168}`, computed in **fp32**
2. `s = sigmoid(l)` — **not softmax**
3. `c = s + b`, `b = e_score_correction_bias ∈ R^256` — a trained per-expert bias
   used for **selection only**
4. per group g of 32: `G_g = sum of the top-2 of {c_e : e ∈ g}`
5. `topk_group=4` groups selected by `G_g`; experts outside them masked to `-inf`
6. `top_k=8` experts selected from the surviving 128 by `c`
7. `g_e = s_e` (the **un-biased** sigmoid) `/ (Σ_{j∈S} s_j + 1e-20) × 2.5`

**Three consequences the brief missed:**

- **The selection is three nested top-k's, not one.** top-2-of-32 (×8), top-4-of-8,
  top-8-of-256-masked. A spec that binds only the outer selection binds nothing: the
  group scores determine which 128 experts are even eligible.
- **The bias is added *after* the sigmoid.** This is what forces the sigmoid to be
  evaluated at all 256 experts. Had `b` been added to the logits, monotonicity would
  reduce the whole selection to comparisons on raw logits (§1.2). It is not.
- **`torch.topk(..., sorted=False)` at both stages.** Tie-breaking is
  implementation-defined and is *not part of the model contract*. See §5.4.

Verified param accounting (`moe_cost.py`): one expert `3·7168·2048 = 44,040,192`;
total **671,025,397,760 ≈ 671.0B**; active/token **36,624,596,992 ≈ 36.6B**. These
reproduce DeepSeek's published 671B/37B to within the MTP module, so the
config-derived model is the right one.

### 1.2 Mixtral / Qwen3-MoE / gpt-oss — the softmax family, and a free reduction

Read at source (`transformers` @ main). Mixtral and Qwen3-MoE both do
`softmax(all E) → topk → divide by the sum of the selected`:

```python
router_probs    = softmax(router_logits, dim=-1)
router_top_value, router_indices = topk(router_probs, top_k)
router_top_value /= router_top_value.sum(dim=-1, keepdim=True)
```

**The global partition function cancels exactly**:
`g_e = (e^{l_e}/Z) / Σ_{j∈S}(e^{l_j}/Z) = e^{l_e} / Σ_{j∈S} e^{l_j}`.
And softmax is strictly monotone, so `top-k(softmax(l)) = top-k(l)`.

Therefore for this family the router binding needs **zero transcendental evaluations
over non-selected experts**: selection is comparisons on **raw logits**, and `exp` is
needed only at the k selected indices. This is not an optimization I am proposing —
**gpt-oss's reference implementation already computes the reduced form**:

```python
router_top_value, router_indices = torch.topk(router_logits, self.top_k, dim=-1)
router_scores = softmax(router_top_value, dim=1)          # exp at k, not E
```

so the reduction is *verified by an existing implementation agreeing with it*.
(gpt-oss's router bias is added to the **logits**, before top-k — harmless, unlike
DeepSeek's post-sigmoid bias.)

**Architecture-dependent router-nonlinearity cost, derived:**

| family | selection needs | gate needs | nonlinear evals / token / layer |
|---|---|---|---|
| Mixtral, Qwen3-MoE, gpt-oss | raw-logit comparisons | `exp` at k | **k** (4–8) |
| DeepSeek-V3 (`noaux_tc`) | `sigmoid` at all E, then group sums | reuse `s` at k | **E = 256** |

**A 32× architecture-induced difference in router nonlinearity cost, caused by one
design choice (bias after the nonlinearity) that has nothing to do with proving.**
Worth stating to model authors: *put the routing bias on the logits.*

---

## 2. The statement

### 2.1 What must be bound

For token `t`, MoE layer `ℓ`, with committed hidden state `h`, committed router
weights `W_r`, committed bias `b`, and a committed expert registry `{W_e}`:

```
BIND(t,ℓ) ≡  l = W_r·h                                        (router matmul)
           ∧ s = σ(l)                                          (exact table)
           ∧ S = TopK(c=s+b) under the canonical total order    (§2.3)
           ∧ g = normalise(s|_S) · 2.5                          (§2.5)
           ∧ y = Σ_{e∈S} g_e · Expert_e(h) + Shared(h)          (identity-bound, §5.3)
```

The load-bearing conjunct is the **third** and, silently, the **fifth**: nearly all
published intuition about MoE proving worries about `S` and forgets that
`Expert_e` must be *the committed expert e*, not some expert.

### 2.2 The three variants, priced

Cost is per token per MoE layer, for the **selection argument only** — both variants
additionally pay the 256 logits and (for DeepSeek) 256 sigmoid lookups, which are
architectural, not variant-specific. Range checks assume a 29-bit composite key over
BabyBear split into 16+13-bit limbs (2 lookups each).

| variant | committed | range checks | rc lookups | LogUp terms | extra mults |
|---|---|---|---|---|---|
| **(a)** sorted permutation | 548 | 538 | 1,076 | 1,040 | 3,117 + 1 inversion |
| **(b)** threshold, slack virtual | **530** | **530** | **1,060** | **0** | **0** |
| (b) threshold, slack materialised | 1,050 | 530 | 1,060 | 0 | 0 |

**(b) dominates (a) on every axis.** The interesting part is *why my prior was wrong*:
I expected (a) to cost ~2× (b) in columns. It does not — both are Θ(E) columns,
because (a) commits an E-wide sorted array and (b) commits an E-wide indicator
vector. The real difference is that **(a) needs a multiset argument and (b) does
not**: 1,040 LogUp terms, 3,117 batch-inversion multiplications and a field inversion,
per token, per layer, per stage — 60k LogUp terms per token across 58 layers, bought
for nothing.

**DECIDED: variant (b), the threshold form.**

**Against the published alternatives.** ZK-DeepSeek implements variant **(a)**
verbatim (characteristic-polynomial multiset + monotonicity, §7.1) and measures its
`experts selector` at **2,447 s for 24 tokens of one layer** — so the multiset
argument (b) deletes is a measured cost in a real system, not a hypothetical one.
2606.05433's OP-10 assumes the other decomposition, *"pairwise comparisons… scales
with **N log K** per token"*. **Variant (b) is Θ(N)**: one range check per element,
independent of K, because the threshold collapses the ordering problem into a
predicate. For DeepSeek-V3's `N=256, K=8`, `log K = 3`, so the threshold form is
~3× under the assumed decomposition and carries no multiset argument at all.

### 2.3 Variant (b), stated precisely — including the two traps

For a stage selecting `k` of `n` elements with values `v_1..v_n`:

```
witness:  σ ∈ {0,1}^n  (selection indicators),  τ ∈ F  (the threshold)
constrain:
  (C1)  σ_i·(1-σ_i) = 0                      for all i          [n booleanity]
  (C2)  Σ_i σ_i = k                           [1 constraint]
  (C3)  key_i := v_i·2^⌈log2 n'⌉ + (n'-1-i) + 1                 [canonical total order]
  (C4)  d_i := σ_i·(key_i - τ) + (1-σ_i)·(τ - key_i - 1)
        RangeCheck(d_i ∈ [0, 2^B))            for all i          [n range checks]
  (C5)  RangeCheck(τ ∈ [0, 2^B))              [1 range check]  ⚠ NOT OPTIONAL
```

**Soundness.** Keys are injective by (C3). (C4) says every selected key is `≥ τ` and
every unselected key is `< τ`; hence `S = {i : key_i ≥ τ}` exactly, and with `|S| = k`
from (C2) and distinct keys, `S` is the top-k. No permutation needed. ∎

**Trap 1 — (C5) is load-bearing.** Without a range check on `τ` itself, a malicious
`τ` near the field modulus makes `τ - key_i - 1` wrap to a small value and *both*
branches of (C4) pass. The threshold form is **unsound without it**. This is the
class of check that is easy to omit and impossible to notice: every honest proof
passes, and the gate never goes red.

**Trap 2 — (C3) is where the tie-break lives.** `key_i` packs the value with the
*complemented index* so that ties in `v` are broken toward the lower index, matching
de-facto `torch.topk` behaviour. Without this, ties make (C4) satisfiable by two
different `S` — see §5.4 for why this is a live attack, not a corner case.

### 2.4 The DeepSeek-V3 instance: three stages

| stage | n | k | reps | indicators | range checks |
|---|---|---|---|---|---|
| group-inner top-2 | 32 | 2 | 8 | 256 | 264 |
| group top-4 | 8 | 4 | 1 | 8 | 9 |
| expert top-8 (masked) | 256 | 8 | 1 | 256 | 257 |
| **total** | | | | **520** | **530** |

Group-mask composition: define `key'_e = groupsel_{g(e)} · key_e`. Since (C3) forces
`key_e ≥ 1`, a masked expert has `key'_e = 0`, strictly below every live key —
`-inf` is implementable as `0` with no special casing. One multiplication per expert
(256), plus the implication `σ_e = 1 ⟹ groupsel_{g(e)} = 1`, which the masked key
already enforces.

Group score assembly `G_g = Σ_{e∈g} t_{g,e}·c_e` with `t` the stage-1 2-hot: 256
multiplications.

### 2.5 Gate values (the brief's item 2)

`D = Σ_{j∈S} s_j`, `g_e = 2.5 · s_e · D^{-1}`.

- Witness `D^{-1}`, constrain `D · D^{-1} = 1`. **One field inversion per token per
  layer.** Fail-closed: if `D = 0` the constraint is unsatisfiable and no proof exists.
- **The zero trap, and its fix.** `σ(x) > 0` in exact arithmetic, but a fixed-point
  sigmoid table *can* underflow to 0, and then `D = 0` and the honest prover cannot
  prove. **DECIDED: the sigmoid table is clamped to `≥ 1 ulp`**, giving `D ≥ k` ulps
  `> 0` unconditionally, and the reference `+1e-20` guard is dropped rather than
  arithmetized (in fixed point it rounds to 0 and is therefore a no-op that reads as
  a safety property — exactly the kind of retained no-op that misleads a later reader).
- **Interaction with the exact-table softmax story: for DeepSeek-V3 there isn't one.**
  There is no softmax in the router. What is needed is a sigmoid table — same
  machinery, same 2^16 exact-table + LogUp-GKR substrate, and the global exp/σ table
  registry of mapping **H** covers it. For the softmax family the *renormalized*
  softmax reduces to `exp` at k indices (§1.2), so the expensive part of the exact
  softmax story — the E-wide sum and its reciprocal — **never arises in a router at
  all**. Only attention needs full softmax.
- Gate weights bind transitively: `g` is a constrained function of `s`, which is a
  table image of `l`, which is a matmul of committed `W_r` and `h`. Nothing about `g`
  is free for the prover to choose. Gate-weight inflation (§5.2) is closed by
  construction, not by a check.

### 2.6 Variant (c) — and why the "key design fork" is not a fork

The brief poses (c), *"S was fixed before the beacon"*, as the alternative to
per-token proof. **It is not an alternative; it is the outer envelope, and (b) is
the checker inside it.** The two compose, and the composition is the design:

```
outer:  commit the whole trace (all tokens, all routing) → beacon → Sel fires at rate p
inner:  on a fired audit, the checker verifies BIND(t,ℓ) for the sampled token
```

Choosing (c) *alone* means the checker is "re-execute and compare", which requires the
auditor to hold the weights — fine for a registry replica, useless for a light
verifier. Choosing (b) *alone* means proving every token — the expensive path, and
the one the sampling layer exists to avoid. **DECIDED: (c) is the envelope, (b)
instantiates `ε_chk`.** §6 does the composition arithmetic.

The reason the fork looked sharp and isn't: one expects the per-token statement to be
expensive. It costs 0.36% of the sparse proof. Once that is derived, there is no
tension to resolve.

---

## 3. Cost model

### 3.1 Accounting conventions

- Matmuls proved by sumcheck ⟹ **only inputs and outputs are committed**, never inner
  products. Per expert: `gate_out 2048 + up_out 2048 + silu_out 2048 + hadamard 2048
  + down_out 7168 = 15,360`.
- **Weights are preprocessed and read-only**, committed once globally — not per
  token. This is the read-only lever from `notes/lookup-ram-verdicts.md` (SP1's
  preprocessed ROM at complexity 0; no timestamp range checks).
- Requantization is **per-element**, one lookup per matmul output element.
- Baseline = *prove all 257 experts*, which is what soundness costs you without a
  router binding.

### 3.2 Per token, per MoE layer

| | committed | lookups | MACs |
|---|---|---|---|
| 9 active experts (8 routed + shared) | 145,408 | 119,808 | 396,361,728 |
|  — of which SiLU nonlinearity | | 18,432 | |
|  — of which requantization | | 101,376 | |
| router matmul + binding, variant (b) | **1,059** | **1,316** | 1,835,008 |
|  — of which sigmoid table | | 256 | |
|  — of which range checks | | 1,060 | |
| **sparse + bound (the proposal)** | **146,467** | **121,124** | 398,196,736 |
| baseline: prove all 257 experts | 3,955,747 | 3,422,500 | 11,320,164,352 |
| **discount** | **27.0×** | **28.3×** | **28.4×** |

**Price of soundness** — the router binding as a share of the sparse proof:
**0.72% committed · 1.09% lookups · 0.46% MACs**. The selection argument proper is
**530 committed elements = 0.36%**.

Per token across 58 MoE layers: 8,495,086 committed sparse vs 229,433,326 baseline;
the binding is 61,422 committed and 76,328 lookup rows. The selection itself is
**464 bytes per token** (8 one-byte indices × 58 layers).

### 3.3 Why the binding is cheap — the structural reason

`W_r` is dense: **all 256 logits must be computed to know the top-8.** No protocol
avoids this. So the argument's inputs are in the trace whether or not you bind
anything, and the marginal cost is comparisons on already-committed values over a
domain of size 256. This is why "proof cost ∝ active parameters" is precise only up
to an additive router term:

```
cost = Θ(k_active · d · f)  +  Θ(E · d)
router share = E / (3 · k_active · f) = 256 / (3·9·2048) = 0.463%
```

**The router term crosses 10% when `E > 0.3·k·f`** — for DeepSeek-V3, `E > 55,296`.
Safe by two orders of magnitude, but the industry trend is *fine-grained* experts
(larger E, smaller f), so this is a real future constraint worth stating now.

### 3.4 ⚠ The discount decays with context length — the "18×" is a single-token number

The agenda's "~18× architectural discount" is `671.0B / 36.6B = 18.32×`, **verified**.
But it is the discount at context length 1. Attention is paid in full by both the
sparse and dense proofs, and MLA's context-dependent work is `40,960·C` MACs per
layer:

| context C | dense-proof MACs | sparse MACs | discount |
|---|---|---|---|
| 1 | 6.70e11 | 3.66e10 | **18.30×** |
| 512 | 6.71e11 | 3.79e10 | 17.71× |
| 4,096 | 6.80e11 | 4.69e10 | 14.52× |
| 16,384 | 7.11e11 | 7.76e10 | 9.17× |
| 32,768 | 7.52e11 | 1.19e11 | 6.35× |
| 65,536 | 8.34e11 | 2.00e11 | 4.16× |
| 131,072 | 9.98e11 | 3.64e11 | **2.74×** |

Attention's context work equals the active FFN work at **C ≈ 9,677**.

**Quote the 18× only with the context caveat attached.** At the 128k context
DeepSeek-V3 advertises, MoE sparsity buys 2.7×, and the dominant proving cost is
attention — which redirects effort toward mapping **D** (layer-uniform sumcheck) and
the KV-cache RAM verdicts, not toward the router.

---

## 4. Attack surface

Cheats the binding must exclude. Each is either **closed by construction**, **closed
by a named constraint**, or **OPEN**.

| # | attack | status |
|---|---|---|
| A1 | route-to-cheap-expert | closed: (C1)–(C5) |
| A2 | gate-weight inflation | closed by construction (§2.5) |
| A3 | expert-swap | closed **only** by per-expert commitment (§5.3) |
| A4 | tie manipulation | closed by the canonical key (C3) — **live without it** (§5.4) |
| A5 | group-stage forgery | closed: stage 1 is itself a variant-(b) argument |
| A6 | uncommitted bias `b` | closed by a registry requirement (§5.6) |
| A7 | honest-on-sampled, cheap-on-unsampled | closed by commit-before-beacon (§6.2) |
| A8 | shared-expert omission | closed: unconditional, part of the layer circuit |
| A9 | precision-boundary divergence | **OPEN** — the hardest one (§5.7) |
| A10 | capacity-drop cheat | **OPEN** — production-only (§5.8) |

### 5.3 Expert-swap: the attack that eats the discount

**The attack.** Prove expert *i*'s matmul against expert *j*'s committed weights. If
weight commitment does not bind the *index*, a prover routes to expert 7 and proves
against expert 3's (cached, or cheap, or previously-opened) weights.

**Why the obvious fix destroys the discount.** Commit the layer's weights as one
tensor `W^ℓ ∈ F^{E×3×d×f}` with MLE `W̃(e⃗, u⃗, v⃗)`, `e⃗` = 8 boolean variables. The
sumcheck binds `e⃗` to a random point, and the prover must open `W̃` there — **and
evaluating the MLE of the full weight tensor at a random point costs Θ(E·d·f), the
full dense cost.** The discount is gone. This is the real technical obstacle behind
"how does the weight commitment index bind expert identity", and it is not
mentioned in the mapping note.

**DECIDED: commit each expert separately; resolve the index verifier-side.**

- Each expert `e` of each layer `ℓ` gets its own commitment `R_{ℓ,e}` (a FRI/Merkle
  root). Opening the 9 active experts opens 9 commitments — cost proportional to what
  was actually used.
- The vector `R_ℓ ∈ F^{257}` of roots is **public and tiny**: 257 × 32 B = 8 KB per
  layer, **477 KB for the whole model**. The verifier evaluates `R̃_ℓ` at the
  committed index bits **itself**, in O(E) = 257 field operations per layer —
  14,848 field ops per token for all 58 layers. Negligible verifier work, and no
  commitment-scheme requirement at all.
- Identity is then bound because the index bits feeding `R̃_ℓ` are the same committed
  bits the selection argument produced.

**This is why the Twist/Shout one-hot machinery is not needed here.** We are not
doing RAM: there are no writes, no timestamps, no address space. We are doing a
*single read of a preprocessed, read-only table of 257 fat rows*, where the table of
*handles* is small enough for the verifier to hold. The three-member commitment law
(`notes/lookup-ram-verdicts.md`: MSM zeros / binary-tower bits / lattice sparsity,
none of which BabyBear+Poseidon2+FRI has) constrains schemes that must commit one-hot
*data*. Here the k-hot selection vector is a **witness column in the trace** — 256
field elements, 0.36% of the proof — never an argument to the PCS. **The law does not
bind this problem.** [Independently derived; the Twist/Shout lane's reading of
2025/105 is folded in at §7.]

**Composition, and it is the good kind:** per-expert commitment granularity is
*exactly* the publicly-checkable weight registry Pillar III wants for Hollow-LLM.
The MoE binding does not merely coexist with the registry — **it requires it, and
its requirement is a strictly finer granularity than "commit the model", which is
what makes the registry useful for LoRA deltas (mapping B) too.** One artifact,
three consumers.

### 5.4 Tie manipulation is a live attack, not a corner case

`torch.topk(..., sorted=False)` has no contractual tie-break. Two experts with equal
`c` at the k-th boundary let the prover choose — and the prover chooses the expert it
would rather prove.

**How reachable is a tie?** With scores at `b`-bit fixed point spread over the
representable range, the gap between adjacent order statistics of `n` samples is
~`1/n` of the range, so `P[boundary tie] ≈ n/2^b`. Summing DeepSeek-V3's three
boundaries (top-2-of-32 × 8 groups, top-4-of-8, top-8-of-256):

| fixed-point bits | P[some boundary tied] | adversarial forward passes to find one |
|---|---|---|
| 16 | 7.9e-3 | ~126 |
| 20 | 5.0e-4 | ~2,016 |
| 24 | 3.1e-5 | ~32,264 |
| 28 | 1.9e-6 | ~516,222 |

**At every practical precision an adversary who chooses inputs finds a tie in a
feasible search.** 32k forward passes at 24-bit is minutes of GPU time. The canonical
key (C3) closes it for one packed multiplication per expert.

#### ⚑ The bf16 claim in 2606.05433 is backwards

OP-10 states: *"Ties between expert scores (**rare with BF16** but possible) must be
resolved by a documented rule."* The parenthetical inverts the truth, and the
criterion is one line:

```
expected gap between the k-th and (k+1)-th of n scores  ≈  spread / n
representable step at m mantissa bits                    ≈  spread / 2^m
ties DOMINATE when   step > gap   ⟺   2^m < n
```

bf16 has **7 explicit mantissa bits → 128 steps per binade**, against **n = 256**
experts. `128 < 256`: **the quantization step near the boundary is about twice the
expected gap, so the k-th and (k+1)-th scores landing on the same representable
value is the *expected* outcome, not a rarity.** fp32's 23 mantissa bits give
`2^23 = 8.4M ≫ 256` → `P ≈ 3.1e-5`, matching the b=24 row above — which is where the
"rare" intuition comes from, and it is an fp32 intuition applied to a bf16 claim.

Two consequences: a deterministic tie-break is **mandatory rather than hygienic**;
and any MoE served with bf16 router scores has a routing function that is *already*
underdetermined by its own reference implementation, before anyone tries to prove it.

**And it lands on ZK-DeepSeek's construction directly.** §3.7 requires `L'` to be
*monotonically **non-decreasing*** — `L'[i−1] ≤ L'[i]` — then takes the first k. With
a tied pair straddling the boundary, two different `L'` satisfy both the multiset
check and the monotonicity check while selecting **different expert sets**. The
construction is **unsound on tied inputs**, which §5.4 shows an adversary can reach.
(Separately, and probably editorial: their text says the first k of a non-decreasing
sort proves *"the chosen elements are indeed the k **smallest**"* — top-k routing
needs the k largest.)

⚠ **A consequence to state plainly:** the spec *fixes* a total order the reference
implementation leaves open, so on a tied input the circuit's output may differ from a
given PyTorch run. That is a model-contract change, not a proof bug — but it must be
written into the registry entry, or the "same model" claim is false on a measure-zero
set the adversary controls.

### 5.6 The bias vector must be in the registry

`e_score_correction_bias ∈ R^256` per MoE layer determines *which* experts fire while
never touching the output value. If it is outside the weight commitment the prover
chooses the routing freely and every constraint in §2.3 is satisfied by a lie.
14,848 field elements model-wide (58 × 256) — trivial to commit, catastrophic to
forget. **The registry schema must enumerate router weights, router bias, and
per-expert weights as three distinct committed objects.**

### 5.7 ⚠ OPEN — the router is a discontinuity, and that makes exactness binding

Everywhere else in a transformer, a 1-ulp arithmetic difference produces a 1-ulp
output difference. **At the router it produces an O(1) output difference**: flipping
the 8th-ranked expert changes the layer output by `g_e·(Expert_i(h) - Expert_j(h))`.

Consequences:

- The circuit's router arithmetic must be **bit-exactly** the deployed model's, or
  the proof is of a different function on the boundary set — which, per §5.4, the
  adversary can steer into.
- The reference implementation already has a precision seam: the router runs in
  **fp32** (`hidden_states.type(torch.float32)`) inside a bf16/fp8 model. A prover and
  a verifier disagreeing about that cast disagree about routing.
- Therefore the "three regimes" of `notes/float-in-zk-three-regimes.md` do **not**
  apply uniformly: error-tolerant / approximate regimes are admissible for expert
  matmuls and inadmissible for the router. **The router must be in the exact regime
  even in a system that tolerates approximation elsewhere.**

**OPEN:** whether to specify the router in exact fixed point (and require the served
model to match, a QAT-style co-design per mapping **G**) or to specify exact fp32
semantics and pay for them. This is a genuine design fork — both answers are
defensible — and it is the one place in this spec where I am not recommending.

### 5.8 ⚠ OPEN — capacity limits and token dropping

DeepSeek-V3's reference `moe_infer` has no capacity factor, but production MoE
serving drops tokens when an expert is oversubscribed. **If dropping is permitted and
unbound, "this token was dropped" is a universal excuse for skipping work** — the
route-to-cheap-expert attack with extra steps. The spec currently assumes no
dropping. **OPEN:** either forbid capacity limits in the served configuration (making
the proof's model differ from the deployed one under load) or make the drop decision
a committed, bound function of the batch — which couples tokens within a batch and
breaks the per-token statement's independence. Neither is free; nobody has looked at
this because nobody has proved an MoE.

---

## 6. Composition with sampled audits

Against `~/dev/minidregg/Selvage/AuditSampling.lean`:
`q = p·(1 − ε_chk) − ε_bind − ε_beacon`, with per-round detection `Round.detect` and
`sequential_bound` / `leakage_bound` giving expected corrupt rounds ≤ `1/q` and
expected leakage ≤ `b/q` for per-round payload cap `b`.

### 6.1 Instantiating the checker

A round is one generation request of `n` tokens. The corrupt-round predicate is
*"at least one token was routed dishonestly."* The checker, on a fired audit,
re-derives `BIND(t,ℓ)` for a uniformly sampled token.

**Audit whole tokens, never (token, layer) cells.** Re-deriving all 58 routers for
one token is `58·256·7168 = 106,430,464` MACs against `36,624,596,992` for a full
honest forward pass — **0.29%**. Sampling cells instead of tokens would dilute
`ε_chk` by a further factor of 58 for a saving of 0.29%. Derived, and decisive.

Two checker instantiations, both admissible:

- **Auditor holds the weights** (a registry replica): checker = re-execute.
  `ε_chk` = dilution only.
- **Public verifier**: checker = verify a variant-(b) proof for the sampled token.
  `ε_chk` = dilution + SNARK soundness error.

### 6.2 The audit-specific attack — and why it is closed by typing, not by assumption

*"Can a prover route honestly on sampled tokens and cheaply on unsampled ones?"*

**No — and the reason is structural.** In `AuditSampling`, `corrupt : List Ω → Bool`
takes the history but **not the current round's coin**; the file's own docstring calls
this "exactly `F_{t−1}`-measurability, enforced by the type rather than assumed."
Translated: the prover must commit the trace — *including every token's routing* —
before the beacon emits. A decision to cheat on token *i* is then made without
knowing whether token *i* will be sampled.

Two protocol obligations follow, and they are the only two:

1. **The routing for every token is inside the pre-beacon commitment.** This forbids
   the tempting "lazy routing" optimization where the prover derives routing only
   when audited. Cost of obligation: 464 bytes/token of indices, or nothing at all if
   the whole trace is Merkle-committed — which the prover computed anyway.
2. **The beacon is not prover-grindable.** This is `ε_beacon`, and the file's
   `BeaconRefutation` shows the sequential bound is **FALSE** if the term is dropped:
   a prover who re-rolls until the audit will not fire gets three expected corrupt
   rounds against a claimed bound of two.

If either fails, the attack succeeds completely and the bound is vacuous. These are
not soundness margins to be traded off; they are hypotheses.

### 6.3 The stolen-work bound, and its pleasant shape

Let the prover cheat on `c` of `n` tokens, saving `w` per token. A uniformly sampled
token misses the cheat with probability `1 − c/n`, so `ε_chk = 1 − c/n` and

```
q(c) = p·c/n − ε          where ε := ε_bind + ε_beacon
```

Applying `leakage_bound` with payload `b = c·w`:

```
stolen work before the first alarm  ≤  b/q  =  c·w / (p·c/n − ε)  =  w·n·c / (p·c − n·ε)
```

**At `ε = 0` this is `w·n/p`, independent of `c`.** The prover gains nothing by
tuning its cheating intensity: stealing one token per round and stealing every token
per round give the same expected total theft before detection. Cheating harder is
detected proportionally sooner, exactly cancelling. (At `p = 1%`, `n = 4096`: 409,600
tokens' worth of skipped expert work before the first alarm, in expectation.)

**At `ε > 0` the independence breaks and a floor appears.** `q(c) > 0` requires

```
c  >  c* := n·ε / p
```

Below `c*` the theorem is **silent** — not "the attack is hard", *silent*, which is
the correct verdict and not a defect. For a hash commitment `ε_bind ≈ 2^-100` and an
unbiasable beacon `ε_beacon ≈ 0`, so `c* ≈ 0` and there is effectively no floor. The
floor is a statement about **beacon quality**, not about MoE: at `ε = 10^-3`,
`n = 4096`, `p = 1%`, `c* = 409.6` tokens per round go undetected, and just above the
floor the bound degrades sharply (at `c = 500`, the bound is 5.5× the `ε = 0` value;
at `c = 1000`, 1.7×).

**The residual, named:** `1/q` rounds' worth of dishonest routing is expected to
occur before the first alarm, and the audit game bounds a *rate*, not a total. A
system that needs "no token was ever mis-routed" cannot get it from sampling; it must
prove every token — at 0.36% marginal cost for the selection argument, which §3 says
is affordable. **Sampling is the right answer for the expert matmuls and arguably the
wrong answer for the router**, because the router binding is the cheap part.

That inversion is the most useful thing in this section: **sample the expensive
conjunct, prove the cheap one always.** A hybrid — every token's routing proved,
expert arithmetic audited at rate `p` — costs 0.72% of a full sparse proof per token
plus `p` full proofs, and removes A7 and the `ε_beacon` dependence from the *routing*
statement entirely. It is not what either pure design does.

---

## 7. Prior art — corrected

⚠ **Coverage caveat.** Two verification lanes were dispatched (a fresh-spelling
absence re-check over the local IACR mirror + web; a technical read of Twist/Shout).
**Both died on API usage credits without reporting.** Everything below is my own
sweep — `~/paperbin` full-text grep plus targeted web search — and it is *narrower*
than the lanes would have been. It nonetheless refuted the absence twice, which is
the point: the absence did not need a wide sweep to fall, only a full-text one.

### 7.1 The two refutations

**ZK-DeepSeek — arXiv 2511.19902, Yunxiao Wang (Zhejiang University), 25 Nov 2025.**
Kimchi/PLONKish over o1js (the Mina stack), KZG, recursive composition, universal
updatable SRS. Quantizes DeepSeek-V3 to Int32/Int64 (Int128 intermediates). Open
source at `github.com/arcstar-lab/ZK-DeepSeek`.

- **It does the sparse thing.** §5.2: *"Run the MoE gating logic to determine the
  top-k experts. Dynamically load the selected experts and compute their outputs.
  Combine the outputs of selected experts with those of the shared experts."*
- **It handles the grouped router.** Its `experts selector` component: *"Each row
  again contains 256 experts, grouped into eight groups… two experts per group, and
  then selects eight final experts from these candidates, requiring two rounds of
  top-k selection."* Independent confirmation of §1.1's reading of `noaux_tc`.
- **Its top-k is my variant (a), exactly.** §3.7 builds characteristic polynomials
  `P_A(t) = Π(t − a_i)`, invokes Schwartz–Zippel for the multiset equality, adds
  monotonicity, and takes the first k. That is the sorted-permutation form §2.2
  prices at 1,040 LogUp terms and 3,117 batch-inversion mults per token per layer.
- **Measured**: `experts selector` = **2,447 s** and `sigmoid gate` = **2,874 s**,
  each for 24 tokens of one layer. For scale, `wkv_a1` — *one* of MLA's projections
  — is **204,138 s** for the same 24 tokens. So in their own numbers the selection
  argument is ~1.2% of a single attention submatmul, which corroborates §3.2's
  derived ~1% share from a completely different direction.
- **It is a component benchmark, not a working full-model prover**, and says so
  ("we benchmark several core components"). Scaling `wkv_a1`'s 204,138 s for 3.67M
  params to the 36.6B *active* params is ~65 years for 24 tokens. The
  discount matters exactly because of numbers like this.

**Verifiable frontier-AI-training protocol — arXiv 2606.05433, §A.5 OP-10
"Mixture-of-experts verification."** MoE is explicitly *out of scope for the base
protocol* and listed as an extension. It names four of this spec's concerns:

> *"Routing commitment. A per-step Merkle root R(routing_t) must join the hash
> chain, committing to which top-K experts were selected for each token. Without
> this, routing decisions are not bound to the proof."*

That is variant **(c)**, §6.2's commit-before-beacon obligation, stated as an open
problem. It also names *Top-K selection verification* ("decomposition into pairwise
comparisons… scales with **N log K** per token"), *Deterministic tie-breaking*,
*All-to-all canonicalisation*, and *load-balancing losses in `arch_spec`*. Its cost
framing — *"per-step proof cost for MoE scales with per-token active compute, not
with total parameters"* — is mapping C's claim, stated qualitatively and undated.

**CryptoMoE (Zhou et al., NeurIPS 2025)** — via the SoK at `2026/1544`. The
*opposite* direction: privacy-preserving MoE inference that keeps expert routing
secret-shared. It is the MoE instance of the phenomenon Pillar III flags — *"two
2026 systems race to make zkML architecture-private, which would make the effort gap
undetectable by construction."* An unbound router is ghost routing; a **hidden**
router is ghost routing that cannot be audited even in principle. Must be cited as
the counter-current.

### 7.2 What actually remains — the corrected gap

| item | ZK-DeepSeek | OP-10 | this spec |
|---|---|---|---|
| sparse expert proving | ✅ implemented | ✅ named | costed (§3) |
| top-k argument | variant (a), measured | "N log K pairwise" | **variant (b), Θ(N), no multiset (§2.2–2.3)** |
| **tie-break** | ❌ *non-decreasing* sort admits ties → **unsound** | ✅ named, but "rare with BF16" | **§5.4: not rare — backwards at bf16** |
| **τ range check** | n/a (different form) | not discussed | **§2.3 Trap 1 — silent unsoundness** |
| **expert-identity binding** | ❌ not discussed; W-proof *reuse* is where a swap hides | ❌ not discussed | **§5.3 — the discount-eating problem** |
| discount arithmetic | not reported | qualitative | **derived, incl. context decay (§3.4)** |
| sampling composition | ❌ | routing commitment only | **§6, against a machine-checked theorem** |
| capacity/dropping | ❌ | ❌ | **§5.8, open** |

Three of these are *soundness* gaps in published work, not merely unclaimed
territory. The strongest is **expert-identity binding**: ZK-DeepSeek's headline
matmul optimization is that *"once a proof for the weight matrix W is generated, it
can be reused in subsequent multiplications"* — reuse of a weight-matrix proof is
precisely the mechanism an expert-swap (§5.3) would exploit, and the paper never
says what binds a reused W-proof to the expert index the router selected. I have not
read their code; **this is a stated suspicion, not a demonstrated break**, and it is
the single highest-value thing to check next.

### 7.3 Still-required citations

- **2025/105 (Twist and Shout)** — the three-member law's source. §5.3 argues it does
  not bind here (we do a read-only indexed open, not RAM). ⚠ **The lane that was to
  verify footnote 3's "tiny memories work anywhere" concession never ran; that
  specific quotation is UNVERIFIED and must be checked at
  `/Users/ember/archive/IACR-eprint-mirror/2025/105.pdf` before being cited.** The
  §5.3 argument does not depend on it.
- **2025/611** — points non-curve projects at Lasso+Spice, if anyone tries the RAM framing.
- **Data-parallel GKR / Thaler '13** — `moe_infer`'s argsort-then-group-by-expert is
  literally a data-parallel regrouping, so mappings **C** and **D** meet here (O4).
- **Hollow-LLM (arXiv 2607.28884)** — an unbound router is a second effort gap.
- **2026/1390** — ⚠ *not* a general Ω(m) commitment floor (a lookup-specific
  restricted-model separation; `notes/virtualization-verdict.md` §4). The point
  here survives without it: against the `Ω(|w|)` floor, the router adds 1,316
  rows to the experts' 119,808, so it does not move the floor.

---

## 8. Decision register

**DECIDED**

| # | decision | reason |
|---|---|---|
| D1 | Variant **(b)**, threshold form | dominates (a) on every axis; kills a 1,040-term multiset argument per token per layer (§2.2) |
| D2 | Canonical composite key with complemented index (C3) | ties are adversarially reachable at every practical precision (§5.4) |
| D3 | `τ` is range-checked (C5) | otherwise field wraparound satisfies both branches — silently (§2.3) |
| D4 | **Per-expert** weight commitment + public root vector | the monolithic-tensor alternative costs Θ(E·d·f) and erases the discount (§5.3) |
| D5 | Verifier resolves the expert index by evaluating `R̃_ℓ` itself, O(E) | E=257 is tiny; needs no one-hot-friendly PCS, so the three-member law is moot (§5.3) |
| D6 | Sigmoid table clamped to ≥ 1 ulp; drop the `+1e-20` | makes `D>0` structural rather than a retained no-op (§2.5) |
| D7 | (c) is the envelope, (b) instantiates `ε_chk` — not a fork | (b) costs 0.36%; there is no tension to trade (§2.6) |
| D8 | Audit whole tokens, never (token,layer) cells | 58× better `ε_chk` for 0.29% more checker work (§6.1) |
| D9 | Registry commits router weights, router bias, per-expert weights separately | an uncommitted bias frees the routing entirely (§5.6) |

**OPEN**

| # | question | why it is genuinely open |
|---|---|---|
| O1 | Exact fixed-point router (+QAT co-design) vs exact fp32 semantics | the router is a discontinuity, so exactness is binding; both answers defensible, cost differs by a lot (§5.7) |
| O2 | Capacity limits / token dropping | forbidding it makes the proved model differ from the served one under load; binding it couples tokens within a batch and breaks per-token independence (§5.8) |
| O3 | Hybrid split — always-prove routing, sample expert arithmetic | §6.3 argues it dominates both pure designs; not costed end-to-end here |
| O4 | Batching tokens through the same expert (mapping D ∩ C) | `moe_infer`'s argsort-and-group is a data-parallel regrouping; the sumcheck saving is unpriced |
| O5 | Whether the sparse-sumcheck formulation of `Σ_e σ_e·g_e·Expert_e(h)` gives the k/E discount without the per-expert commitment of D4 | it should — the summand is k-sparse — but the final PCS opening is the catch, and I have not proved it |
| O6 | Does ZK-DeepSeek's reused weight-matrix proof bind the expert index? | their headline matmul optimization is W-proof *reuse*; §7.2 argues that is exactly where an expert-swap hides. **Suspicion, not a break** — the code is open, go read it |

---

## 9. What to build first

Reordered by the §7 correction: priority is no longer "be first", it is **the three
soundness gaps in work that already exists**.

1. **Read `github.com/arcstar-lab/ZK-DeepSeek` for O6.** If a reused W-proof does not
   bind the expert index, that is a concrete break in a published, open-source
   verifiable-inference system, and it is the highest-value hour in this document.
   Check the tie-break too (§5.4 predicts unsoundness on tied inputs).
2. **The selection argument, standalone, in Lean** — three nested variant-(b) stages
   over the DeepSeek-V3 shape. It is 530 committed elements and five constraint
   families; the smallest object in this spec and the one everything else hangs on.
   ⚠ House law: this is a constraint system, so it is **authored in Lean**, emitted,
   and called from Rust — never hand-written in Rust.
3. **The refutation tests before the construction**: a witness satisfying (C1)–(C4)
   with an out-of-range `τ` (must be *rejected* once C5 lands and *accepted* before
   it — prove the floor false), and a tied-key witness admitting two distinct `S`
   (must be rejected once C3 lands). Both are also the differentials against
   ZK-DeepSeek.
4. **The registry schema** for D4/D9 — per-expert roots, router weights, router bias.
   Pillar III's artifact; the MoE binding is its first real consumer and pins its
   granularity to *per expert*.
5. Only then cost measurement, against the derived table in §3.2 — and ZK-DeepSeek's
   published component timings give a real system to measure against.

**Re-run the sweep properly.** Both verification lanes died on credits (§7), and the
absence fell to a full-text grep of a directory we already had. The instrument that
failed was *first-2-page keyword caching*; the fix is full-text extraction over the
mirror, and until that runs, no absence claim in this repo should be quoted as
`[measured]`.
