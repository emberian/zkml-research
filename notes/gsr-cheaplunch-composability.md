# CheapLunch's `M_E` skip vs. GSR's partial-layer absorption — do they compose?

**Question**: the GSR lane (`notes/gsr-poseidon-2026-1692.md` §6) left one open path by which our
Poseidon2 verdict could get worse — CheapLunch (eprint **2025/2040**) §D.1 flags, *at our exact
`t=16, k=1`*, that Poseidon2's non-MDS `M_E` lets **two rounds be freely skipped**, and those two
rounds live in the **initial full rounds, which are our entire 3-round margin**. If that skip
composes with GSR's absorption, the margin goes **3 → 1**.

**Read and computed 2026-08-18.** Everything below is quoted from the papers, read from our
source, or computed by `notes/gsr-scripts/cheaplunch_me.py` (plain `python3`, no deps, ~30 s).
Sibling lanes referenced, not duplicated: the GSR read (`gsr-poseidon-2026-1692.md`, and its
`krylov.py` / `gsr_calc.py` / `all_inst.py`).

---

## VERDICT IN ONE PARAGRAPH

**The skip reaches us — and it does not compose. Both halves are computed, not argued.**
CheapLunch's `M_E` is **not** our `M_E` (they use the Poseidon2-paper `M_4 = [[5,7,1,3],…]`, we
deploy Plonky3's `MDSMat4 = circ(2,3,1,1)`), so their published vector does not transfer — but the
*phenomenon* does, because it rests on the **outer block form `[[2A,A,A,A],…]` alone**, not on `A`.
I **constructed and verified a 2-round chain on our deployed constants** (BabyBear, α=7, real
`RC_EXT_INIT`), CICO-1 input zero satisfied, checked by re-running the deployed rounds on 256
random inputs. `α=7` does not dodge it (the construction is α-independent given α odd and
`gcd(α,p−1)=1`, both of which hold); neither does our width nor our constants (12/12 random
`M_4`+RC sets also chain). **But composition fails, and the obstruction is structural rather than
numerical: GSR's 16 free state dimensions exist *only because rounds 1–3 are dropped*, while
CheapLunch's saving exists *only if rounds 1–2 are kept*.** Counted on the shared resource —
the dimension of the state family entering GSR's window — GSR needs **≥ 15** and any 2-round
front-end skip leaves exactly **1**; and that "1" is not an artifact of CheapLunch's particular
line, it is forced: **a Grassmannian count shows a 2-round front-end skip admits `D = 1` and
nothing larger, and even a 1-round skip caps at `D = 7`, still 8 short of 15.** **Margin stays 3
of 21; the binding result remains GSR's CICO-1 on 18/21 at 2^27.4.** Recommendation on `R_P`
is unchanged and I concur with the sibling lane: **do `R_P` 13 → 20 now** (+5.0%), not the
`R_P`=15 containment — with the added finding that **`R_P` buys nothing against a front-end skip**,
so the obstruction below is load-bearing and belongs in the repair rationale.

---

## 1. What §D.1 actually says — quoted, not paraphrased

### 1a. The MDS baseline (this is the part the brief did not have)

> *"**Case of an MDS matrix** In this section, we show how reduce the ideal degree of the ideal by
> partially skipping the first round. Let `M` an MDS matrix, and `s = ⌊t/k⌋ − 2 ≤ k`. […] Setting
> the state after the affine layer to*
>
> `(a₁·x₁^{1/d}, …, a_s·x_s^{1/d}, Σ_{l=s+1}^k a_l·x_l + b)`
>
> *we get after the layer of S-boxes the state*
>
> `(a₁^d·x₁, …, a_s^d·x_s, P₁(x_{s+1},…,x_k), …, P_{t−s(k+1)}(x_{s+1},…,x_k))`
>
> *where the `P_i` have degree `d`. Multiplying the weight of `x₁,…,x_s` by `d` […] our new weights
> only increase the denominator in the weighted Bézout bound by a factor `d^s`, dividing the upper
> bound on `D_I` by the same factor."*

⚑ **Read `s = ⌊t/k⌋ − 2 ≤ k` carefully: the `≤ k` is binding, not decorative.** The construction
re-parameterises `s` of the `x_1..x_k` **input variables**, so `s ≤ k`. At our `t=16, k=1`,
`⌊t/k⌋−2 = 14` but `s ≤ k = 1`, so **`s = 1`: one round is freely skippable against *any* invertible
`M_E`, MDS included.** (The main text's p.21 sentence *"the first `s = ⌊t/k⌋ − 2` variables"* reads
as 14 in isolation; the appendix's `≤ k` is what the construction actually supports. This is my
reading of a genuinely loose main-text sentence — flagged as such.)

⚠ **Consequence, and it corrects the brief's framing:** the non-MDS penalty is **one extra round,
not two**. The paper says so itself — *"we reduce `D_I` by a factor `d²` **instead of `d`**"*.

### 1b. The non-MDS observation — our exact parameters

> *"**Case of a non-MDS matrix** Though we did not manage to do an extensive study of the
> round-skipping tricks in the non-MDS case, we have made some observations that tend to show that
> non-MDS matrices such as the ones defined in Poseidon2 may be weaker against such tricks than MDS
> ones. We provide here an example of a vector allowing to skip two rounds in the case where `M_E`
> is defined as in [35] and where **`t = 16, k = 1`** (ie. we reduce `D_I` by a factor `d²` instead
> of `d`). This tends to show that contrary to what was believed by the designers of Poseidon2,
> using non-MDS matrices not only weakens the security against statistical attacks, but also
> **against some algebraic attacks**."*

and the construction itself:

> *"We can have a subspace chain of the form:*
>
> `a₀·X + b₀ --[S_E∘(C⁽¹⁾+M_E(·))]--> a₁·Y + b₁ --[S_E∘(C⁽²⁾+M_E(·))]--> a₂·Z + b₂`"

> *"We leave as an open problem a more systematic study of this phenomenon."*

### 1c. So, precisely: what does it require, where does it apply, and what does "freely" mean?

**What it requires of `M_E`.** Nothing about MDS-ness *positively* — it requires the opposite. The
chain needs an affine line whose image under `M_E` is **sparse**, twice in a row. Written out, one
step `v ↦ S_E(M_E v + C)` maps `{a X + b}` into a line iff, on `supp(M_E a)`, the vector
`M_E b + C` is **proportional to** `M_E a` (all active coordinates share one root `ρ`), giving
`Y = (X−ρ)^α`, `a' = (M_E a)^{∘α}` on the support and `b' = (M_E b + C)^{∘α}` off it.

- **At which rounds**: the **first two external rounds**, counted from the permutation input — for
  us, initial full rounds **1 and 2** of 4. It is a front-end construction and cannot be moved.
- **What "freely" means**: **probability 1, and no cost in CheapLunch's own DoF budget.** It is a
  *change of variables* (substitute the solving variable by its α-th root), not a filtering
  condition — nothing is guessed and nothing is thrown away *for that attack*, because at CICO-1
  the algebraic system only ever has **one** input variable. ⚑ **It is emphatically not free for
  an attack that needs more than one input dimension. That is the entire composability story
  (§4).** It does restrict the input to a specific affine line, which is exactly the resource GSR
  requires and cannot get.

---

## 2. Checked against our deployed `M_E` — it reaches us, constructed

### 2a. First, their `M_E` is not our `M_E`

| | `M_4` block | source |
|---|---|---|
| **CheapLunch §D.1** | `[[5,7,1,3],[4,6,1,1],[1,3,5,7],[1,1,4,6]]` (Poseidon2-paper, their ref [35]) | printed in the appendix |
| **Ours (deployed)** | `circ(2,3,1,1) = [[2,3,1,1],[1,2,3,1],[1,1,2,3],[3,1,1,2]]` | `Poseidon2BabyBearW16.lean:mat4`; `circuit/src/poseidon2.rs:15` *"External linear layer: MDSMat4 circulant [2,3,1,1]"* |

16×16 matrices **identical: False** (stage 1). Their field is KoalaBear and `d=3`; ours BabyBear
and `α=7`. **Their published `a₀/b₀` is inert against us.** What *is* shared is the outer form
`M_E = [[2A,A,A,A],[A,2A,A,A],[A,A,2A,A],[A,A,A,2A]]`, verified on our matrix as the identity

```
M_E(u) block_j  =  A · ( u_j + Σ_j' u_j' )          [stage 2, 200/200 random vectors]
```

### 2b. The mechanism, named — an invariant subspace, and it is `A`-independent

That identity has an immediate consequence nobody states in either paper:

> **`W = {(0, v, −v, 0)}` (dim 4) is `M_E`-invariant, with `M_E|_W = A`.**
> Both blocks 0 and 3 of `M_E a` vanish, so **`|supp(M_E a)| = 8, not 16`.**
> [stage 2, 200/200]

and the S-box layer preserves `W`'s antisymmetry **because α is odd** (`(−x)^α = −x^α`). This is
the whole engine. It is a property of the *outer* block structure and holds for **any invertible
`A`** — which is why our different `M_4` changes nothing.

**Branch-number witness, measured**: our built chain has `a₁` of weight 8 with `M_E a₁` of
weight 2, i.e. `wt(a) + wt(M_E a) = 10`. An MDS 16×16 layer would force **17**. That gap of 7 is
the non-MDS penalty, made concrete.

### 2c. Does α=7 / our width / our constants dodge it? — **No, no, and no**

| candidate escape | verdict | evidence |
|---|---|---|
| **α = 7** (vs their `d=3`) | **does not dodge.** The alignment condition is α-*independent*; α enters only as (i) α odd — 7 is; (ii) `x↦x^α` a bijection so α-th roots exist — `gcd(7, p−1) = 1` ✓ (`p−1 = 2^27·3·5`). ⚠ Note this is the *opposite* of GSR, where α=7 is what saves us. | stage 4 |
| **our width `t=16`** | **does not dodge.** The form needs `t = 4m, m ≥ 2`; `t=16 ⇒ m=4`. | stage 2 |
| **our `M_4`** | **does not dodge.** 12/12 random invertible `M_4` also chain. | stage 5c |
| **our round constants** | **does not dodge.** 12/12 random constant sets also chain; ours does. | stage 5c |

### 2d. The chain, built on our deployed constants

Ansatz `a₀ = (0, v, −v, 0) ∈ W`; sparse round-2 design (`A w = γ·e_{q₀}`, which is what CheapLunch's
own `a₂` turns out to be); the two residual equations reduce to **one degree-7 univariate over
`F_p`**, solved by Cantor–Zassenhaus.

```
q0 = 0,  CICO-1 input zero at coordinate 0:  a0[0] = 0,  b0[0] = 0     ✓ both zero
a0 = [0,0,0,0, 0x51c105ad,0x23ace9cf,0x6d869204,0x74f67919,
                0x263efa54,0x54531632,0x0a796dfd,0x030986e8, 0,0,0,0]
b0 = [0, 0x4739a214,0x20cb4b4e,0x64a7caf6, 0x3ba0be0d,0x4d7e6438,0x2d188fee,0x59c98ed1,
      0x61b49eac,0x4797236a,0x22008839,0x6d8ff2ee, 0x2709e3d2,0x3aef8d77,0x30e93689,0x304f38b6]

supports:  |a0| = 8   ->   |a1| = 8   ->   |a2| = 2
** 2-round chain HOLDS on our deployed constants: True **
   verified by RE-RUNNING the deployed rounds on 256 random X       [stage 4]
```

⚑ **Two guards that make this a measurement rather than a reconstruction**, in the spirit of the
sibling lane reproducing Table 1 5/5:

1. **Our permutation model reproduces both Lean `#guard` KATs** (`perm([0..15])`, `perm([0]*16)`)
   before anything is concluded from it (stage 0). The chain is verified by running *those* rounds.
2. **CheapLunch's own published chain replays exactly** on their `M_E`/KoalaBear/`d=3` constants —
   2 rounds, verified against the real rounds, and their `a₂` comes out as `e₄ − e₈` with entries
   `0x1` and `0x7f000000 = −1` (stage 3). My model of their construction is theirs, not my
   invention.

### 2e. Why exactly two — derived, which the paper leaves open

Two independent budgets, both computed:

**Offset (alignment) budget.** Available: `t − 1 − D = 14`. Cost of round `r`: `(t − z_r) − 1`
where `z_r` = zeros of the image. A 2-round chain needs `z₁ + z₂ ≥ 16`.
- **MDS `M_E`**: `wt(a) + wt(M_E a) ≥ 17` forces `z₁ + z₂ ≤ 15`. **Short by exactly 1.**
- **Poseidon2's `M_E`**: the invariant subspace replaces the 16×16 branch bound with `A`'s 4×4 one;
  our chain gets `z₁ = 8, z₂ = 14`, i.e. `22 ≥ 16` with **8 to spare**.

⚑ **That is the precise content of CheapLunch's "may be weaker than MDS" — MDS misses the second
round by one degree of freedom, and the invariant subspace is exactly that one degree of freedom.**

**Direction budget — the binding one.** `v` carries 3 projective DoF. Round 2's alignment forces
`A w ∝ (C⁽²⁾_i − C⁽²⁾_j)` on its support, which **consumes all 3**. Round 3 then needs its direction
`A((τ₂·1_J)^{∘α})` parallel to `C⁽³⁾_i − C⁽³⁾_j` — **3 projective conditions with zero free
parameters** (the free scalar `c` rescales but cannot rotate: `(cτ)^{∘α} = c^α τ^{∘α}`).

**Exhaustive check, all shapes** (every ordered block pair × every support subset): **180 shapes
enumerated on our constants; best case 3 violated conditions; a 3-round chain exists: False**
(stage 5b). Per shape this is a ~`p^{-3} = 2^{-93}` coincidence.
⚠ *Named gap*: CheapLunch publish only `C⁽¹⁾, C⁽²⁾`, so I could not run the same exhaustive check
on their KoalaBear instance — their round-3 constant is not in the paper.

---

## 3. The DoF budgets, both sides, on the same resource

The resource they compete for is **the dimension of the affine family of states entering the
attack's window**.

**GSR (2026/1692) at `t=16, k=1`** — from the sibling lane's read:

| item | count |
|---|---|
| state `X₁` at window start | **16** |
| backward CICO-in condition (§5.3) | −1 |
| forward partial linearisation (§5.2), `min(R_P, t−2k) = min(13,14)` | −13 |
| must retain ≥ 1 free variable to solve CICO-out | −1 |
| | **needs `D ≥ 15`; has 16, with 1 to spare** |

⚑ **Where those 16 dimensions come from matters more than the number**: the state entering round 4
is unconstrained **precisely because the attack is on the 18-round `(1,13,4)` variant** — rounds
1–3 are *dropped*. Free dimensions are the *purchase price* of round-reduction.

**CheapLunch `M_E` skip (ours, as constructed)**:

| item | count |
|---|---|
| free: `g₀`(4) + `g₃`(4) + `γ`(1) + `ρ₁`(1) | **10** |
| spent: round-2 sum condition (1) + CICO-1 input zero (1) | −2 |
| **spare** | **8** |
| **delivers**: the state entering round 3 is a **1-parameter curve** | **`D = 1`** |

⚑ And its saving exists **only if rounds 1–2 are kept** — it is a re-weighting of the *real* input
variable. Drop those rounds and there is nothing to skip.

---

## 4. Compose or not — **NOT**, with the arithmetic

### 4a. The direct check

Push our verified line through the remaining initial full rounds and ask GSR's very first question.

```
after external round 3: state is a degree-7  curve in Z
after external round 4: state is a degree-49 curve in Z

GSR's FIRST forward-linearisation condition: coordinate 0 of the state entering
partial round 1 must be a CONSTANT delta^(1), known in advance.
   that coordinate as a polynomial in Z : degree 49
   non-constant coefficients that must vanish : 48
   is it constant (can GSR linearise even ONE partial round)? False        [stage 6]
```

**48 coefficient equations against 8 spare parameters. Short by 40 — for *one* of the 13.**
Geometrically the same count: a degree-49 curve in `F_p^16` meeting a codimension-13 affine
subspace has expected point count `49·p^{−12} = 2^{−366.4}`. **Empty.**

⚑ **So composition does not merely fail to improve GSR — it destroys it. GSR contributes *zero*
partial rounds on top of the skip.** The composed attack is strictly worse than GSR alone.

### 4b. The steelman: is a smarter, dimension-preserving skip possible?

The above kills *CheapLunch's* line. The brief is right that this must be earned against the
general shape, so: what is the **largest** affine family that can survive a front-end external
round at all? Let `U ⊆ H` (the CICO-1 input hyperplane, dim 15) have dim `D`, and `R = M_E·basis(U)`
be the 16×`D` matrix of linear parts. Zero rows become constants (`z` of them, `z·D` conditions);
the remaining rows must fall into exactly `m = D` projective directions (`m<D` impossible since
`rank R = D`; `m>D` leaves the new variables algebraically dependent), costing `(16−z−D)(D−1)`;
alignment costs `(16−z−D)` on the offset against `15−D` available, forcing `z ≥ 1`. Available on
the direction side: `dim Gr(D,15) = D(15−D)`.

| `D` | `Gr(D,15)` | conds, 1 round | 1 rd? | conds, 2 rounds | 2 rd? |
|---|---|---|---|---|---|
| **1** | 14 | 1 | **yes** | 2 | **yes** |
| 2 | 26 | 15 | yes | 30 | no |
| 5 | 50 | 45 | yes | 90 | no |
| **7** | 56 | 55 | **yes** | 110 | no |
| 8 | 56 | 57 | no | 114 | no |
| 14 | 14 | 27 | no | 54 | no |
| **15** | 0 | 15 | **no** | 30 | no |

> **Largest family surviving ONE front-end external round: `D = 7`.**
> **Largest family surviving TWO: `D = 1`.**
> **GSR requires `D ≥ 15`.**

⚑⚑ **A 2-round front-end skip *forces* `D = 1`. That is a fact about the shape, not about
CheapLunch's published vector. And even a 1-round skip caps at `D = 7`, still 8 short of 15. The
front-end-skip line and the GSR line are mutually exclusive at every depth.**

**Calibration**: the count says `D=1` is feasible for two rounds — and `D=1` for two rounds is
exactly what §2d built and verified. At the one point where the count is testable, it is right.

⚠ **Honest limit, stated because this obstruction is now load-bearing**: §4b is a *generic*
dimension count. A degenerate configuration of a specific `M_E` could beat it. What it settles is
that **no generic construction exists**, and it names precisely the degeneracy a future paper would
have to exhibit: *an affine family of dimension ≥ 15 that survives a front-end external round.*
That sentence is the tripwire to watch.

### 4c. The obstruction, stated at the right resolution

**It is prior to the arithmetic, not a near-miss.**

> GSR's 16 free dimensions exist **only because rounds 1–3 are dropped**.
> CheapLunch's saving exists **only if rounds 1–2 are kept**.
> They are statements about **different objects**. The composition is **ill-posed before it is
> overdetermined.**

This is the good outcome the brief hoped for, and it is *earned*: the two constructions are dual —
one collapses the state to a line so a single variable can be re-weighted, the other keeps the state
nearly free so linear conditions can be imposed on it. **You cannot have both.**

---

## 5. The recomputed margin

| line of attack | reach | cost | verdict |
|---|---|---|---|
| **GSR alone** (`R_P`=13 deployed) | CICO-1 on the `(1,13,4)` = **18 of 21** rounds | **2^27.4** vs generic 2^31 | **PRACTICAL** — the binding result |
| **CheapLunch `M_E` skip alone** | **full 21 rounds**, `D_I` 7^21 → 7^19 | `D_I` = 2^53.3; root-finding alone ~`D_I²·log p` = **2^111.6** | **not an attack** |
| **Composed** | — | — | **DOES NOT EXIST** (§4) |

> ⚑ **Margin: UNCHANGED at 3 of 21 rounds. The brief's 3 → 1 scenario does not occur.**

**What *would* have happened, priced so the decision is not made on a guess.** If a future
dimension-preserving front-end skip did compose (2 initial full rounds skipped + GSR's 1 + partials,
leaving 1 initial full round uncovered):

| `R_P` | GSR alone | margin | composed, on the FULL 21 rounds |
|---|---|---|---|
| **13 (deployed)** | 2^27.4 | 3 | 2^33.0 — *still above 2^31* |
| 15 | 2^33.0 | 4 | 2^38.6 — still above 2^31 |
| 20 | 2^61.1 | 9 | 2^66.7 — still above 2^31 |

⚑ Worth saying out loud: **even a perfect composition would not break the full 21-round permutation
at CICO-1** (2^33.0 > 2^31). It would give a *practical CICO-1 on 20 of 21 rounds*, i.e. margin 1.
Bad, but the full permutation would stand.

---

## 6. The `R_P` decision — plainly

**Do `R_P` 13 → 20 (+5.0%, margin 3 → 9). Now, not as a phase 2.** I concur with the sibling lane
and this pass gives no reason to soften it; the house rule against shipping the containment while
naming the fix as later applies unchanged. `R_P`=15 is a **containment** — it lands above the
CICO-1 cliff but leaves the margin at 4, and 4 is the same species of number as 3.

**What this lane adds to that recommendation — two things, and the second is the important one:**

1. **The margin did not get worse, so the decision is not more urgent than it was.** It is exactly
   as urgent as the GSR lane said. Nothing here is a reason to escalate, and nothing is a reason to
   defer.

2. ⚑ **`R_P` buys *nothing* against a front-end skip.** The `M_E` skip lives in the initial full
   rounds; `R_P` is invisible to it. The only parameter that adds margin against it is `R_F` (≈+11%
   per round, 16× worse per round of margin than `R_P`). **So the case for `R_P`=20 rests entirely
   on the GSR half, and our safety against the front-end half rests entirely on the §4b
   obstruction.** That obstruction is now **load-bearing for the security argument** and must be
   recorded as such in the repair rationale — not as background.

**The tripwire to watch** (the concrete thing that would flip this): *any result exhibiting an
affine family of dimension ≥ 15 that survives a front-end external round of Poseidon2.* That —
not a better `M_E` vector, and not a better Gröbner solver — is what turns margin 3 into margin 1.
If it appears, the response is **`R_F`**, not `R_P`.

⚠ **Not recommended: changing `M_E`.** The invariant subspace is a property of Poseidon2's outer
block form for every `t = 4m`, holds for **any** `A` (12/12 random, stage 5c), and is not removable
by rotating constants or picking a different `M_4`. Removing it means a genuinely MDS 16×16
external layer, which is the cost Poseidon2 declined to pay in the first place. **There is no cheap
matrix fix here, and pretending otherwise would be the expensive mistake.**

---

## 7. What stands regardless — say it exactly

- **The full 21-round permutation.** No attack, before or after this pass. The composed attack does
  not exist; and even if it did, it lands at 2^33.0 against a 2^31 generic bound.
- **The sponge's ~124-bit collision/preimage claim.** Untouched. It lives at CICO-`k` for `k` at the
  capacity (8 base elements, 248 bits). **GSR is identically vacuous there** (`t−2k = 0`), and
  **CheapLunch's skip is worth at most a factor `α²`** off an ideal degree of `7^{k·R_F+R_P}` —
  nothing at `k=8`. Neither construction touches the claim that carries our security.
- **The other instances**, unchanged from the sibling lane: **BN254-w3** immune to GSR (`t−2k=1`) and
  to this (`t=3` has no 4-block outer form); **Pasta/Mina Poseidon** has 0 partial rounds and no
  Poseidon2 `M_E`.
- ⚠ **BabyBear w24** (segment-digest sponge) — **derived, not constructed.** It has the same outer
  block form (6 blocks of 4), so `W` exists there too and the alignment budget is *looser*
  (`t−1−D = 22` available against 7+7); the 2-round skip should apply. It inherits the same
  non-composition with GSR by the same §4b count (`D = 1` vs GSR's `D ≥ 15` — at `t=24, k=1`, GSR
  needs `1 + min(21,22) + 1 = 23`). **I did not build the w24 chain**; if the w24 instance ever
  becomes load-bearing, that is a 20-minute extension of `cheaplunch_me.py`.

---

## 8. Corrections this pass makes to the brief and to the record

1. ⚠ **"Two rounds" is not two rounds of non-MDS penalty.** At `t=16, k=1` an MDS `M_E` already
   gives **one** free round (`s ≤ k = 1`). Poseidon2's non-MDS form buys the **second**. The brief
   (and a fast read of the paper's main text) reads `s = ⌊t/k⌋−2 = 14`; the appendix's `≤ k` is what
   the construction supports.
2. ⚠ **CheapLunch's `M_E` is not our `M_E`.** Their `M_4` is the Poseidon2-paper one; we deploy
   Plonky3's `circ(2,3,1,1)`. Anyone citing their §D.1 vector against our instance is citing an
   inert object — the *phenomenon* transfers, the *witness* does not.
3. ⚑ **The mechanism has a name the papers do not give it**: an `M_E`-invariant subspace
   `W = {(0,v,−v,0)}` with `M_E|_W = A`, preserved by the S-box because α is odd. This makes the
   result `A`-independent and explains "why exactly two" (§2e) — which CheapLunch explicitly leaves
   open.
4. ⚑ **α=7 cuts the opposite way here.** Against GSR, α=7 is what saves us (residual degree `7^r`
   not `3^r`). Against this, α is irrelevant — it only has to be odd with `gcd(α,p−1)=1`, which is
   *forced* by Poseidon2 needing a permutation. **Do not carry "α=7 protects us" across from the
   GSR note to this one.**

---

## Provenance

- **Papers**: `~/paperbin/cheaplunch-extending-freelunch-2025-2040.txt` (§D.1 re-extracted with
  `pdftotext -layout -f 40 -l 45` — the plain `.txt` sidecar **interleaves the six column vectors
  `a₀,b₀,a₁,b₁,a₂,b₂` into an unreadable stream**; the layout pass is mandatory for this appendix).
  `~/paperbin/gsr-sbox-skipping-poseidon-2026-1692.txt`.
- **Script**: `notes/gsr-scripts/cheaplunch_me.py` — stages 0–7, `python3`, no deps, ~30 s.
  Companion to the GSR lane's `krylov.py` / `gsr_calc.py` / `all_inst.py`; the GSR complexity model
  used in §5 is theirs (validated 5/5 against paper Table 1), re-stated in 3 lines, not re-derived.
- **Our parameters read from `/Users/ember/dev/breadstuffs/`**:
  `metatheory/Dregg2/Circuit/Poseidon2BabyBearW16.lean:63-199` (`mat4`, `mdsLight`, `rcExtInitial`,
  and the two `#guard` KATs that gate stage 0), `circuit/src/poseidon2.rs:1-110`.
- ⚑ **Trap paid for here, for the next lane**: `pow(a, p-2, p)` is Fermat and is **silently wrong
  for a composite modulus**. The α-th root needs `pow(alpha, -1, p-1)` — `p−1 = 2^27·3·5` is not
  prime. The symptom was not an exception: the chain simply failed to verify at round 2, which
  reads exactly like "the skip does not reach us." **A wrong inverse renders as the hoped-for
  verdict.**
