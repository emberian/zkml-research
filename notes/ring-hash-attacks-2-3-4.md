# The ring hash's three standing attack items — MITM, the free norm check, Gröbner/CICO

2026-08-18. `forcodex/08-ATTACK-BRIEFS.md` Brief 1 named four things "we named and
never ran". Item 2 (the τ=2 integral settling) closed 08-17. **This lane runs the
other three.** Defensive posture: we are deciding whether to ship an unshipped
primitive, and **a break here is a win.**

**Verdict in one breath.** ⚑ **One item flips from "named risk" to *the* binding
question, and it is not the one the brief expected.** MITM (item 1) is **closed with
a computed, calibrated round requirement of 12 rounds against NR=16 — a 1.33× margin,
not the 4× a naive model reports.** Gröbner/CICO (item 3) is **closed and clears by
hundreds of bits** — it does *not* reach past the integral floor, so σ-Poseidon is not
in the trouble the brief flagged as possible. **The free-norm-check (item 2) is the
one that moved**: the law is now exact and measured, the forgery is exhibited at
deployment parameters, and the design's own obligation **O5 — filed as a *cost*
question — turns out to determine whether the hash is a function at all.**

| item | status | the number |
|---|---|---|
| 1. the gadget-Feistel's binding leg | ⚑ **PARTIAL — reached, not closed** | the one technique that **reaches** a decomposition layer (carry-DDT, 2024/1900) **reaches 2 rounds and stalls**, with a *named cause*. A calibrated MITM bound gives **12 rounds vs NR=16 ⇒ 1.33×**. **NR=16 remains precedent.** |
| 2. the free-norm-check assumption | ⚑ **PARTIAL — and it is the one that should gate shipping** | **K·s bits of forgery per coefficient, 64s per ring element**; s=1 ⇒ **2^64 free FS choices per absorbed element** against a credited **2^52** grinding *cost* |
| 3. Gröbner / CICO on σ-Poseidon | ⚑ **CLOSED (computed)** | leg satisfied at **4 rounds** vs the **24-round integral floor**. Integral remains binding; the ~6-round margin is unchanged |
| — (aiming device) prime q vs Rubato | ⚑ **CONFIRMED, and the framing was wrong** | prime q kills 2023/822 structurally — but that attack's expensive leg bought **noise removal we never needed**, and the cheap leg (linearization) is modulus-agnostic |
| — (found en route) σ schedule | ⚑ **NEW DEFECT** | **47% of σ-Poseidon's rounds do not mix CRT slots at all**, with a run of **4 consecutive** slot-diagonal rounds. Zero-cost fix. |

Scripts: `notes/ring-attack-scripts/rha_{norm_slack,feistel_structure,mitm_dof,groebner_cico}.py`.
Every guard below was **proved live by injection** — and one of them **caught itself dead**
on the first run (§0.1).

---

## 0. What is measured, what is read, what is derived

| claim | tag |
|---|---|
| admissible plane vectors per value = `B'^K/q`, exactly, at three knife-edge toys × three slacks | ⚑ **[measured, exhaustive]** `rha_norm_slack.py` |
| a 1-bit-slack forgery at deployment parameters moves the round-function output | ⚑ **[measured]** same |
| `F_r` is a sum of `w` independent per-element functions | ⚑ **[measured 12/12, guard live]** `rha_feistel_structure.py` |
| the top plane `Y_3` is never multiplied ⇒ `F_r` exactly affine in it | ⚑ **[measured, guard live]** same |
| cell-level diffusion complete in one round | ⚑ **[measured 4/4]** same |
| the order-2 differential dies at **2 rounds** of the permutation | ⚑ **[measured]** same |
| MITM colour-propagation reach = 3 rounds at ring-element granularity | ⚑ **[computed, exhaustive over 3^8]** `rha_mitm_dof.py` |
| the model underestimates published reach by up to 4× | ⚑ **[calibrated against 2 published targets]** same |
| CheapLunch Eq.(10) reproduced on 4/4 rows of its own Table 2 to <0.1 bit | ⚑ **[measured]** `rha_groebner_cico.py` |
| the 2024/1900 carry automaton reproduces our decomposition's measured limb-transition rate | ⚑ **[measured, exact count + 40k samples]** `rha_carry_ddt.py` |
| exactly one cheap limb-difference pattern (limb 3 alone); reach **2 rounds**, stall cause = density of `g_3` | ⚑ **[measured, falsifier live]** same |
| σ schedule: 14/30 rounds slot-trivial, run of 4; group transitive overall | ⚑ **[computed, exhaustive]** `rha_sigma_slots.py` |
| 2023/822 Assumption 1 unsatisfiable at prime q; its costly stages buy noise-removal only | **[read at source]** §3a |
| 2025/932's scope is `(F_{q²})^8` **by name** | **[read at source]** §3a |
| Perrin's rule, and the **correction to the brief's paraphrase** | **[read at source]** 2024/605 Abstract, §2.1–2.2 |
| MITM model requirements; the right paper is **2023/1359**, not 2025/2213 | **[read at source]** §1.2 |
| CheapLunch formulas and Table 2 | **[read at source]** 2025/2040 §3.4–3.5, §4.2 |

**Corpus statement.** Paper claims rest on `~/paperbin` + the full IACR eprint mirror.
That corpus is **cryptology-only** — no arXiv, no ToSC/TCHES-only papers, no grey
literature. No absence claim below is stronger than *"absent from the IACR corpus."*

### 0.1 ⚑ A guard that caught itself dead, kept because the class is recorded

`rha_norm_slack.py`'s GUARD C originally compared `count_reps(v=7, q=251)` against
`count_reps(v=7, q=257)` and asserted they differ. **Both are 1.** The mutation was a
**no-op on that value**, so the guard would have passed forever while asserting
nothing — `minted-a-falsifier-that-stopped-falsifying`, in this lane, on the first
run. It is rebuilt **constructively**: the discriminating statistic is the number of
values with *zero* representations, which is 0 when `B^K > q` and necessarily >0 when
`B^K < q` by pigeonhole. The history is written into the script.

⚠ This matters for how to read the rest: **the brief warned that the τ=2 script shipped
with a dead guard row. The failure recurred here immediately.** Guards are not
self-validating; only injection validates them.

---

## 1. The gadget-Feistel's binding leg — **REACHED at 2 rounds, not closed**

### 1.0 ⚑ The retarget, and why it is the right one

The lane began on MILP/MITM (§1.1–1.7 below, and that work stands). **It was retargeted
mid-flight**, correctly: every *automated* instrument in the decomposition-hash family
declines to start at full size — Monolith's own word for full-size instances is
*"computationally intractable"* — and **four instruments reporting nothing is one fact
about our instruments, not four about the primitive.**

The one published technique that **reaches** a decomposition layer is hand-built:
**Liu, Koschatko, Grassi, Yan, Chen, Banik, Meier, eprint 2024/1900, *"Opening the
Blackbox: Collision Attacks on Round-Reduced Tip5, Tip4, Tip4' and Monolith"*.** *(Title
verified on page 1. ⚠ A corrupt title index pairs this title with 2024/270, which is
YPIR, a PIR paper. Fetch by number.)*

⚠ **TWO CORRECTIONS TO THE FRAMING I WAS HANDED, and the second one matters most.**

1. **"Independent of the S-box" is §3 — the *baseline this paper beats*, not the
   carry-DDT machinery.** §3 skips the S-box by forcing its differences to zero. §4, the
   carry-DDT, exists to **open** it — the paper is called *Opening the Blackbox*. What it
   does not need is the S-box's **high-degree polynomial over F_p** (*"we do not know the
   high-degree expression of the S-box over F_p"*, §3.1). What it absolutely **does**
   need is the S-box's internal limb structure. **The technique is maximally
   S-box-dependent.** Reading it as "S-box-agnostic, therefore applies to any
   limb-decomposing design" is the error the framing invites.
2. ⚑ **It runs at FULL parameters and it is CHEAP.** No toy primes anywhere: Tip5/Tip4/
   Tip4'/Monolith-64 at `p = 2^64−2^32+1`, Monolith-31 at `2^31−1`, 10^6 random queries,
   **15–32 table lookups per query**. **So the "every instrument in this family only runs
   at toy primes" pattern does NOT retire this one** — which makes what follows a
   statement about the primitive rather than about our budget.

Published reach: **3/5 rounds (Tip5), 2/6 (Monolith-64), 4/5 SFS (Tip4), 3/6 SFS
(Monolith-64)** — collisions and semi-free-start collisions; no preimages, no
distinguishers.

**So the question became: how far does it reach into ours?** `rha_carry_ddt.py`.

### 1.0a What transfers, and what does not

2024/1900's machinery has two halves:

- **(i) a carry automaton over the base-B limb decomposition** (§4.2:
  `carry_{i+1} = 1 iff carry_i + Δw_i + w_i ≥ 2^{l_i}`). ⚑ **This is our step 1
  verbatim** — our decomposition at `B = 2^16`, `K = 4` is exactly the object it
  propagates. **It transfers with no changes, and it was run:**

```
   limb m  delta   P exact (counted)   P measured        n
        0      1            0.999985     1.000000    40000
        2      7            0.999893     0.999875    40000
        3      7            0.999786     0.999925    40000
```

- **(ii) a per-limb DDT for the S-box, combined across limbs by (i).** ⚑ **We have no
  analogue.** The technique's axiom is `z_i = S_i(w_i)` — output limb `i` a function of
  input limb `i` **alone** — and ours fails it **three independent ways**:

  | break | why | severity |
  |---|---|---|
  | 1. `Z_j = Y_j·Y_{j+1}` couples **adjacent limbs** | no `S_j` to call; patching it means carrying `(Y_j, Y'_j)` in the automaton state, i.e. **`4·B² = 2^34` states and a `2^66` transition table** at `B=2^16` | expensive |
  | 2. the product is a **negacyclic convolution** in `R_q` | output coefficient `k` depends on **all 16** coefficients of both operands — **there is no limb order under which a bounded-width state suffices** | not statable |
  | 3. ⚑ **the dense `g`/`h` ring mixing destroys the limb structure before recomposition** | `F_r(R)_i` is a dense `R_q`-combination of *every* limb of *every* element. There is no `S_i`, so **`DDT_{i,j}` has no definition on our primitive** | **fatal alone** |

  The honest substitute — computed exactly rather than heuristically — is to ask directly
  which limb-difference patterns make the round output cheap.

  ⚠ **The near-miss worth keeping.** §7.1 *is* the paper's recipe for a coupled
  nonlinearity — Monolith's type-III Feistel `x_i + x_{i-1}²` — and it works by keeping
  Algorithm 2 as an **unmodified per-element subroutine** under an outer backtracking
  search, at `O(p)` to land one transition. **That recipe would be the template against
  us if our product were `R_i·R_{i+1}` (element-coupled, post-decomposition) instead of
  `Y_j·Y_{j+1}` (limb-coupled, intra-decomposition).** ⚑ **Standing design refusal: never
  move the product to element granularity for cost.** That single change would hand an
  attacker a published, full-size, measured attack recipe.

  ⚠ **And two structural facts about our own parameters, logged because they cut both
  ways.** (a) Their Theorem 1 (§4.5) requires *"the `l_{h−1}` most significant bits of
  `p` be all 1"* — `q = 2^64−257 = 0xFFFF_FFFF_FFFF_FEFF` has **top 16 bits all 1**, so
  **our modulus satisfies the hypothesis exactly, as Goldilocks does** — shared with every
  prime this paper broke. Not exploitable given break 3, but it is the property that would
  resurface in any variant that reintroduces limb-locality. (b) If we *were* limb-local,
  the precompute is `16·h·2^{2l}` tuples: **`2^38` ≈ 1.25 TB at `B=2^16`, versus `2^23` ≈
  42 MB at `B=2^8`.** ⚑ **`B = 2^16` is a 65536× tax on this attack and `B = 2^8` would
  land us squarely inside the attacked regime — an argument FOR the current base.**

### 1.0b The answer, and it is exactly one pattern

```
  limb set with a difference      distinct dF over 8 states            verdict
  [3]                                                     1      DETERMINISTIC
  [2]                                                     8    state-dependent
  [0]                                                     8    state-dependent
  [2, 3]                                                  8    state-dependent
  [0, 3]                                                  8    state-dependent
  [0, 1, 2, 3]                                            8    state-dependent
```

`ΔZ_0 = 0 iff ΔY_0 = ΔY_1 = 0`; `ΔZ_1 = 0 iff ΔY_1 = ΔY_2 = 0`. So `ΔF` is
state-independent **iff the difference lives in limb 3 alone** — the top plane, which
`P = 2` never multiplies. This is §1.3's affine slope arriving as a *differential*.

### 1.0c How far it reaches: **2 rounds**, and the stall has a cause

```
  round 1  free      (difference in L only, dR = 0 so F is not crossed)
  round 2  p ~ 1     (top-plane difference crosses F deterministically)
  round 3  STALLS    (dF is dense; no limb pattern is cheap for it)

  freedom  (top-plane content of a 4-element difference) : 1024 bits
  condition(dF_i == 0 mod B^3, all coeffs, all 4 outputs): 3072 bits
  deficit                                                : 2048 bits
  MEASURED: is dF top-plane for a top-plane input difference?  False
```

### 1.0d ⚑ The falsification — and my first falsifier was DEAD

A search that finds a short attack is worthless unless it would find a long one. So the
same search is re-run on a **deliberately weakened** design where the characteristic
provably chains.

⚠ **My first falsifier set `g_3` to the ring identity and asserted it would chain. It did
not** — the guard went red on the weakened design *and* the real one, distinguishing
nothing. **That is the second dead guard this lane produced** (§0.1 was the first), and
the reason is the mechanism of the whole section: `Y_3` is the top limb's *value*, a
small integer in `[0,B)`, so `g_3 = 1` re-injects it at the **bottom** of the next word.
The correct falsifier is **`g_3 = B^3`**, which re-injects at the top plane:

```
  MEASURED (weakened g_3 = B^3): is dF top-plane?  True
  GUARD: real design chains = False, weakened design chains = True  -> LIVE
```

⚑ **THE DESIGN CONDITION THAT FALLS OUT, and it is the useful part: the reach is bounded
by the DENSITY of `g_3`, not by the round count.** A sparse, structured or scalar
top-plane coefficient — exactly what a cost pass reaches for — **reopens an unbounded
deterministic characteristic.** This is the Chaghri lesson (*"the vulnerability of
Chaghri exists in the usage of a SPARSE affine transform"*, and *"our attacks apply to
ANY choice of M"*) arriving at the gadget-Feistel through a different door. **Standing
refusal: `g` must stay dense, and the top-plane block `g[·][·][3]` most of all.**

### 1.0e What this is and is not — stated carefully, because it is easy to over-read

**The published attack of 2024/1900 does NOT apply to the gadget-Feistel.** Break 3 is
fatal on its own: with no limb-local `S_i`, `DDT_{i,j}` is undefined. **That is a
verdict about the primitive, not about our budget** — precisely because this instrument,
unlike the other three, runs at full size and cheaply. It is the one refusal in this
family that cannot be explained by scale.

**What was actually run is narrower**: the technique's **carry half**, which does
transfer verbatim and was validated against 40k samples at deployment parameters, plus an
**exact** (not heuristic) substitute for the half that has no analogue. That combination
yields a **2-round** deterministic characteristic with a named stall cause.

**It is weaker than a break**: a characteristic that stalls at round 2 says `NR ≥ 3`,
which every other computed leg already said.

⚑ **NR = 16 remains precedent.** Nothing here reaches the design. Per the standing
epistemic rule: NR is set when something *reaches* it, not when enough tools refuse it.
⚠ **And note the asymmetry this leaves**: we now know one real attack *cannot be stated*
against us for three structural reasons — which is a stronger negative than we had, and
still not a positive.

---

### 1.1 The MILP/MITM leg — the blocker the brief sent me to read first does not survive at source

`notes/feistel-classical-tooling.md` §4 concluded **"no published MITM model can be
instantiated"** on three grounds: the nonlinearity (a) re-partitions the cell 64→4×16,
(b) `Z = Y_j·Y_{j+1}` is two-input and non-bijective, (c) ring multiplication is not
coefficient-local. **All three are true at bit or coefficient granularity.** Read at
source, none of them is a modelling obstruction:

- ⚑ **The brief and the sibling lane both went to the wrong paper.** eprint **2025/2213**
  (Degré–Derbez–Schrottenloher, the "unified MILP model" the brief surfaces as new
  tooling) is **AES-based SPN only** and says so: *"it would be useful to extend our
  approach beyond AES-based primitives"* (§7), and it cites the Feistel line as work it
  does **not** subsume. The relevant papers are **2022/189** and, decisively,
  **2023/1359** (Hou et al., *"Automated Meet-in-the-Middle Attack Goes to Feistel"*,
  ASIACRYPT 2023) — **which appears in neither the brief nor the sibling lane's
  twelve-paper sweep.**
- **Ground (b) — expanding/non-bijective — is handled, and the model change is one line.**
  2022/189 §3.1 introduces *b-branching cells* (expanding) and *b-XOR cells*
  (contracting), explicitly noting *"the difference with Present-like designs is that
  Eq. 1 is not satisfied anymore"*; §4.3 says the MILP fix is to allow a **negative
  contribution**, and: *"This is the only required change."* Bijectivity of the round
  function is explicitly **not** required: *"The round functions do not need to be
  permutations; the attacks have a complexity at least the size of one branch"* (§7.1).
- **Ground (c) — non-locality — is Ascon's defining feature**, and 2024/298 handles a
  two-input nonlinearity mixing colours by declaring the product **white** and buying it
  back with **cancellations** at one DoF each (30 of them for 4 rounds of Ascon).

⚑ **So the sibling lane's "no model can be instantiated" is NOT supportable at source.**
It is a true statement about the *granularity it chose*, generalised into a statement
about the literature. Per `feedback-honest-label-hides-transmutable-mediocrity`: that
caveat was **undone work in a theorem's clothing**, and this section is the work.

### 1.2 The structural fact that makes a model legitimate — measured

`rha_feistel_structure.py`, against the versioned spec:

```
S1  sum of per-element contributions == full F_r : 12/12
    GUARD  with one contribution omitted:  0/12   -> LIVE (refused)
```

**`F_r(R)_i = Σ_{i'} f_{r,i,i'}(R_{i'})`** — the nonlinearity **never couples two input
elements**. All coupling is the public linear layer. So with the cell taken to be a
**ring element**, the round is exactly the shape every MITM model assumes: a *unary,
cell-local* nonlinear map `S : R_q → R_q^6` followed by a public linear layer.

### 1.3 ⚑ A new structural weakness, found here: the top plane is never multiplied

`P = 2` gives `Z_0 = Y_0·Y_1` and `Z_1 = Y_1·Y_2`. **`Y_3` — the top 16 bits of every
64-bit coefficient — appears only in the linear sum.** Measured:

```
S2  top-plane delta: distinct output differences over 10 random states = 1
      -> AFFINE (state-independent slope)
    GUARD  LOW-plane delta, same magnitude: distinct differences = 10  -> LIVE
```

⚑ **`F_r` is *exactly affine* in the top plane, with a state-independent slope, with
probability 1, on a set of size `B^{d·w} = 2^1024`.** That is an **order-1** relation
holding deterministically — strictly stronger than the order-2 property the design note
flagged as its first attack-me item.

**25% of the state traverses every round through a purely linear path.** `P = 3` (adding
`Z_2 = Y_2·Y_3`) closes it at `w = 4` more rows/round — **12 → 16 rows, +33%.**

⚠ It does **not** extend past one round: the round-1 output difference is `g·δ`, a dense
ring element, so round 2 sees a full-range input and the carry structure is destroyed.
It is a one-round relation, like the order-2 one, and it is why the reach in §1.4 is what
it is. **Reported as a design finding, not as an attack.**

### 1.4 The order-2 differential: the design note's claim is true, and its scope is one round

The note says *"the order-2 differential does NOT die in one round"* and files it as the
first attack-me item. It measured `D²` of **one round function**. Measured here for the
**permutation**, which nobody had done:

```
(a) ONE round function F, D^2 constant in 40/40      [note says 40/40 -- reproduced]
(b) PERMUTATION at 1 round : constant in 20/20   -> STRUCTURE PRESENT
(b) PERMUTATION at 2 rounds: constant in  0/20   -> dead
(b) PERMUTATION at 3 rounds: constant in  0/20   -> dead
```

⚑ **The property is a property of one round function; the permutation kills it at two
rounds.** The design note's sentence is correct and its scope is narrower than its
placement as "the first attack-me item" implies.

### 1.5 The model, instantiated, and the round requirement it computes

`rha_mitm_dof.py`. Unroll the Feistel: `X^{r+1} = X^{r-1} + F_r(X^r)`. Colours
`{G, B, R, S, W}` with the **superposition** rule (2021/575) that the Feistel's add is
linear and therefore does *not* destroy separability — `join(B,R) = S` — while `F`
applied to a formal sum goes white. Exhaustive over all `3^8 = 6561` colourings of the
two starting states.

```
MAX ROUNDS COVERED = 3
  X^(s-1) = GGGB   X^(s) = GGGR    DoF_blue = 1, DoF_red = 1
  forward  states: GGGB GGGR RRRS WWWW
  backward states: GGGR GGGB BBBS WWWW

GUARD 1  inject "F is linear" (S->S)      : reach 129  -> LIVE
GUARD 2  all-blue (no backward chunk)     : rounds 0   -> LIVE
GUARD 3  inject "F depends on cell 0 only": reach 129  -> LIVE
```

### 1.6 ⚑ Why 3 is not the answer — the calibration that refutes the comfortable number

**A reach of 3 with NR=16 reads as a 4× margin. Shipping that would be a cost table
wearing security clothes, and the model's own calibration refutes it.**

The model is structural: its answer depends only on the 2-branch Feistel recurrence and
on `F` having full 1-round diffusion. **Both published 2-branch Feistel MITM targets have
exactly those two properties**, so the model returns the same reach for them — and their
true reach is published.

| target | cells/branch | model says | **published** | underestimate |
|---|---|---|---|---|
| Feistel-SP-128 | 8 | 3 | **12** | **4.00×** |
| Simpira-2 | 16 | 3 | **7** (of 15) | 2.33× |

The gap is not mysterious. **2022/189's branch-level automatic tool marked b=2
"Inapplicable"; 2023/1359 got the rounds by going *finer* — byte level with
cancellations** — and says so: *"to simplify the model, the attacks are of branch-level.
However, in our model, all attacks are found at the byte-level, which is more
fine-grained."*

⚑ **This inverts my own entering hypothesis.** I expected the sibling lane's obstruction
to dissolve by choosing a *coarser* cell. The coarse cell is exactly what produced
"Inapplicable" in the one recorded instance where this question was settled. The coarse
model is instantiable — that part held — but it is the model that reports nothing.

```
raw model reach                        :  3 rounds
x worst published underestimate factor : x4.0
⚑ CALIBRATED MITM ROUND REQUIREMENT    : 12 rounds
deployed NR                            : 16 rounds
⚑ MARGIN                               : 1.33x
```

**Carry 12 and 1.33×, never 4 and 4×.**

### 1.7 The leg that actually bears on shipping: MITM *gain*, not reach

Reach is not a break. Published MITM gains against 2-branch Feistels, as a **fraction of
the target** (the scale-free comparison):

| target | generic | attack | gain |
|---|---|---|---|
| Feistel-SP-128 | 2^128 | 2^113 | 15 bits = **11.7%** |
| Simpira-2 | 2^256 | 2^225 | 31 bits = **12.1%** |

Ours, at capacity 1024 bits and λ=128:

| target | generic | gain needed | vs. state of the art |
|---|---|---|---|
| collision | 2^512 | 384 bits = **75.0%** | **6.2×** |
| preimage, 256-bit digest | 2^256 | 128 bits = **50.0%** | **4.1×** |

⚑ **A MITM would need 4–6× the largest relative gain ever published against a 2-branch
Feistel before the 128-bit claim moves.** That is the honest defence — **and note what
it rests on: the 1024-bit capacity, not the round count.** The round count is defended
by §1.6's 1.33×, which is thin; the *security level* is defended by the capacity, which
is enormous. Those are different arguments and the design record has been running them
together.

### 1.8 What would unblock a sharper answer

The finer model that the literature needed is **not available here, and the reason is
structural**: base-B decomposition is **coefficient**-local; ring multiplication is
**slot**-local (`R_q ≅ (F_{q²})^8`); the change of basis between them is dense. **No
single cell decomposition makes both nonlinear steps local** — `feistel-classical-tooling.md`
§4.1 derived this and it is exactly the obstruction to the byte-level refinement that
took Simpira-2 from 5 rounds to 7. That refinement would have to be *invented*, not
copied. **Undone work, not an impossibility** — and it is the same sentence the sibling
lane owed.

---

## 2. The free-norm-check assumption — **PARTIAL, and it is now the binding item**

### 2.1 The law, exactly, measured

The design pins its plane decomposition uniquely only because `B^K` barely exceeds `q`:
`B^K = 2^64`, `q = 2^64 − 257`, `γ = 257`, ambiguity rate `γ/q = 2^-56`. **That is the
whole reason the modulus moved off the deployed Frog value.**

⚑ **That entire analysis is conditional on the enforced ∞-norm bound being EXACTLY `B`.**
If the host certifies only `‖Y‖_∞ < B' = 2^s·B`, the admissible plane count per
coefficient is `B'^K/q`. Measured exhaustively at three knife-edge toys × three slacks:

```
B=4,K=4,q=251   s=0: 1.0199   s=1: 16.3187   s=2: 261.0996   (= B'^K/q, exact)
B=2,K=6,q=61    s=0: 1.0492   s=1: 67.1475   s=2: 4297.4426  (exact)
B=8,K=3,q=509   s=0: 1.0059   s=1:  8.0472   s=2:  64.3772   (exact)
```

**LAW (measured, exact — it is a counting identity):**

> **`K·s` bits of forgery freedom per coefficient ⇒ `d·K·s = 64s` bits per ring element
> ⇒ `448s` bits per permutation call at rate 7.**

Guards, all live by injection: a plausible-but-wrong law (slack buys one plane, not `K`)
refused 0/2; a structural control with `B^K < q` refused; the counter's own
modulus-sensitivity (rebuilt after going dead, §0.1).

### 2.2 The forgery, exhibited at deployment parameters

```
both plane sets recompose to the SAME ring element : True
canonical  ||Y||_inf = 65472   (< B = 65536)
forged     ||Y||_inf = 107140  (< 2B, passes a 1-bit-slack check, FAILS an exact one)
round-function outputs differ : True   (16/16 coefficients differ)
GUARD  no-forgery control: outputs identical -> LIVE
```

A **constructive** borrow family (borrow `t_j ∈ [0,c)` units from plane `j+1` into plane
`j`) gives `c^3` representations per coefficient — at `s=1`, **8 per coefficient, `8^16 =
2^48` per ring element**; the exhaustive law gives `2^4` and `2^64`. Both are stated;
the construction is the lower bound, the law is the count.

### 2.3 ⚑ The finding: O5 is a soundness obligation wearing a cost obligation's clothes

The design credits itself with a **grinding cost of ~2^52** (design note says 2^54; that
was computed at `q = 2^64−59` with `γ=59`. **At the deployed dual-mode modulus
`2^64−257`, `γ=257` and the figure is `2^52`** — the modulus move cost 2 bits, correctly
better than the `−279` point it was compared against, but 2 bits worse than the value the
Feistel was designed around. Minor, and worth correcting where quoted.)

**Against that credited 2^52 *cost*, one bit of slack hands the prover 2^64 free
*choices*.** That is not a degradation of the margin; it is the **inversion** of it —
the prover stops paying and starts choosing.

Now the link, and it is the part that had not been made:

- `ring-hash-dual-mode.md` §5c already names the free-norm-check hazard and already
  observes that *"strong-sampling challenges have unbounded coefficient norm, so
  commitment folding grows witness norms."*
- The fix is the LatticeFold-family decomposition machinery, whose price is the
  **"×1–2 norm-control factor"** in §4b.
- That schedule is obligation **O5**, and O5's own row reads: *"the norm-control schedule
  … undone; **bounds the ×1–2 factor in §4b**; transmutable."*

⚑ **O5 is filed as a COST obligation. It is also the obligation that determines the
enforced ∞-norm bound — and therefore whether the hash is a function at all.** The
binding layer is structurally safe (`Op` is a short-plane subtype, so an unchecked norm
is unrepresentable). **The hash mode has no such structure**: in-circuit Fiat–Shamir
computes the sponge on *witnessed* planes, and the only thing pinning them is the host's
norm check.

This is `feedback-a-cost-verdict-outlives-its-premise` firing exactly: a verdict priced
against a resource nobody re-checked binds.

### 2.4 What would close it

**Not** a new gate — a **statement of the enforced bound**. O5 must return not a cost
factor but an answer to: *what ∞-norm bound does the host's check certify on a single
plane vector, exactly?* If the answer is `B`, item 2 closes at `s=0` and the 2^52
grinding figure stands. If it is anything above `B`, §2.1's law prices it directly, and
**`s ≥ 2` is already fatal to a 128-bit claim per absorbed element.**

⚠ **I could not run this leg**: it needs 2026/1127's decomposition schedule, which is
that paper's own and is not in our tree. **I did not verify that slack exists** — I
verified that *if* it exists it is priced by the law above, and that the obligation which
would settle it is open and mis-classified. Stated that way and not more.

---

## 3. Gröbner / CICO on σ-Poseidon — **CLOSED, and it does not reach the integral floor**

### 3.1 ⚑ Perrin's rule — the brief's paraphrase is wrong in the way that matters

The brief relays: *"argue from the elimination step, not from computing the Gröbner basis
— the latter is 'sometimes literally non-existent.'"* Read at source (2024/605, Abstract):

> "our survey of the literature suggests to base a security argument on the complexity of
> the variable elimination step rather than that of the computation of the Gröbner basis
> itself. Indeed, it turns out that **the latter complexity** is hard to estimate—and is
> sometimes litteraly non-existent."

⚑ **The antecedent of "the latter" is THE COMPLEXITY, not the basis.** Every ideal has a
Gröbner basis. What can be non-existent is its **cost**: for a suitable weighted monomial
order the natural modelling *already is* a Gröbner basis, so the `GröbFind` step costs
**zero** — the FreeLunch phenomenon. §2.2: *"it is possible to find monomial orderings
such that the system obtained during the SysGen step is immediately a Gröbner basis."*

**The rule is therefore stronger than the paraphrase**: never price security on an F4/F5
estimate, because it can **evaporate to zero**. Price it on the elimination step, whose
cost is governed by the **ideal degree `D_I`**.

⚠ Perrin gives **no explicit elimination cost formula** — no `D_I^ω`, no field-size term.
His operative model is `D_I^2`, recoverable only from his own arithmetic (`D_I^1.5 →
2^126` at `D_I = 7^30`). The formulas are in **CheapLunch**, not in Perrin.

### 3.2 The model, calibrated against its source before being pointed at us

`rha_groebner_cico.py` implements CheapLunch's `D_I ≤ δ^{k·R_F}·d^{R_P}`, round-skipping
`s = ⌊t/k⌋−2`, and the designer-conservative Eq.(10) `D_I^2·wt/deg`. **Reproduced on all
four rows of its own Table 2:**

```
lambda  d   t  k  R_F  R_P  published  computed   delta
  1024  3  24  8    8   85     456.47    456.47   -0.00
   512  5  12  4    8   57     390.08    390.08   +0.00
   384  7   9  3    8   47     370.57    370.57   +0.00
   256  3  49  7    6   46     253.59    253.59   +0.00
worst absolute disagreement = 0.004 bits over 4/4 rows
```

Guards live by injection: dropping the round-skipping term → 0/4 rows match; dropping the
`/d^{R_F}` factor → 0/4; and **the model does not report a break on instances CheapLunch
publishes as unbroken** (Poseidon-128 t=3 → 2^274; t=9 → 2^148.6).

⚠ The λ=384 calibration row is `d=7, t=9, R_F=8` — **our S-box degree and our width.**
The calibration is close to our parameters, not a distant analogy.

### 3.3 ⚑ The answer depends entirely on granularity, and only the wrong reading is scary

A Gröbner attack is a system **over a field**. `R_q` is not a field, so granularity is a
correctness question, not a modelling taste.

| reading | t | k | n_S | log₂ D_I | cost | verdict |
|---|---|---|---|---|---|---|
| (A) ring-element — **INVALID** | 9 | 1 | 1 | 64.6 | **2^106.7** | *BREAK* |
| (B) CRT slot, `F_{q²}` | 72 | 8 | 8 | 654.1 | 2^1285.8 | safe |
| (C) `F_q` coordinate | 144 | 16 | 8 | 833.8 | 2^1645.1 | safe |

⚑ **Reading (A) is the only one that produces a break, and it is the one that is wrong.**
It treats the state as 9 branches and the S-box as one degree-7 equation, when `x^7` over
`R_q` is **8 independent degree-7 maps over `F_{q²}`**. Undercounting the S-boxes 8× is
what manufactures the break. Recorded because a careless modeller lands on (A) first —
and it is the exact mirror of the MITM granularity trap in §1.6, in the opposite
direction.

*(Reading (C) is the granularity at which the σ layer is genuinely linear: at τ=2 the
automorphisms carry a Frobenius twist, so they are `F_q`-linear but only semi-linear over
`F_{q²}`.)*

### 3.4 The comparison the brief asked for

```
Grobner / CICO leg (this script)  :   4 rounds
char-p INTEGRAL floor (measured)  :  24 rounds
borrowed budget                   :  30 rounds
```

⚑ **Gröbner does not reach further than integral — it is satisfied an order of magnitude
earlier.** The integral property remains the **binding** algebraic constraint on
σ-Poseidon, and the ~6-round margin over the budget is **unchanged** by this leg.
**σ-Poseidon is not in the trouble the brief flagged as possible.**

**CheapLunch's reach past CICO-1 does not help an attacker here either.** Its extension
matters when capacity forces `k > 1`; our capacity of 1 ring element *is* `k = 8` slots
(reading B), and the `k`-amplification `δ^{k·R_F}` works **for** us — it is why (B) sits
at 2^1286 rather than (A)'s 2^107.

### 3.5 Residuals, named

- `D_I ≤ δ^{k·R_F}·d^{R_P}` is **conjectured tight**, not proven; Perrin's MIDC is
  likewise a conjecture. **A defence needs a *lower* bound on `D_I` and neither is one.**
- The `n_S = 8` extension of the `R_P` term is **mine**, not CheapLunch's — their Poseidon
  row assumes one S-box per partial round. It is the natural reading of their XHash8 case
  (`D_I ≤ α^{(n_S+2k)R}`) but is not stated for Poseidon, and **it is the single largest
  lever in §3.3's table.**
- ⚑ **The cost model assumes `p` is large enough that one coordinate cannot be guessed.
  Ours is `q ≈ 2^64`.** Perrin flags this for Goldilocks; FreeLunch **abandoned** its
  XHash8 attack for it (*"since the size of one branch is roughly 64 bits, this CICO
  problem could simply be solved by making 2^64 queries"*). **Any future attack that
  reduces to guessing a small number of `F_q` coordinates is cheap for us in a way it is
  not for a 256-bit-prime design. Live residual, not priced above.**
- **Neither CheapLunch nor FreeLunch says anything about extension fields or
  product-of-fields rings.** The nearest precedent is XHash8's `F_{p³}` S-box, which both
  papers dissolve back to the prime field — reading (C). *Absent from the IACR corpus.*
- ⚠ **Poseidon appears zero times in FreeLunch 2024/347.** Every Poseidon bound quoted
  here is CheapLunch's. Steiner 2024/310 duplicates that analysis independently and was
  **not** cross-read.

---

## 3a. The aiming device: prime q vs Rubato — **confirmed, and the framing was wrong**

The brief's instruction was to **confirm** that prime q saves us rather than assume it.
Done, at source, and the confirmation is structural rather than rhetorical:

- 2023/822 §8.1 opens *"The easiest way to prevent our attack is to simply restrict q to
  be prime"* and, read **in full**, carries **no qualification against the countermeasure**.
- **Structurally**: their Assumption 1 is *"There exists an integer m such that m|q"* with
  `m ≤ m_max := ⌊2^{λ/n}⌋`. At prime q the only divisors are 1 and q, and `q^n ≫ 2^λ`, so
  **Assumption 1 is unsatisfiable identically.** Not a preference — a dead hypothesis.
- Their Lemma 1 was verified at source, **and its proof is pure homomorphism reasoning**
  (*"the result now follows from the linearity of monomials"*) — it uses `u | q` nowhere.
  So the *descent* transfers to our 254 nontrivial CRT ideals with full force.

⚑ **But the framing in `ring-hash-cryptanalysis.md` PA1 aims at the wrong leg, and this
is the finding.** Splitting their attack by what each stage actually requires:

| stage | requires | transfers to our `F_{q²}` slots? |
|---|---|---|
| recover key+noise mod m | **exhaustive search** (`m^n < 2^λ`) **and Gaussian noise to distinguish** | **NO** — our slot quotient is `2^128`, and **we have no noise** |
| locate noise-free positions | same | **NO** |
| **key recovery by linearization** | **only a ring hom + low degree.** No smallness anywhere | ⚑ **YES, fully** |

And the cost inversion, from their own §7.3: *"apart from Rubato-128S, `C_relin` is
negligibly small compared to doing steps 1 and 2."* **The composite-modulus machinery is
the expensive part, and all it buys is stripping Rubato's Gaussian noise.**

⚑ **We have no noise, so we never had the defence that machinery was buying through, and
prime q does not touch the leg that applies.** Corroborated in the wild: **HERA** is
*"explicitly defined over a prime field for security"* and adds no Gaussian noise — and
was broken anyway by linearization (2023/1800).

**The live threat is the one we already knew, now confirmed as in-scope by name.**
Beyne–Verbauwhede **2025/932** generalizes integral cryptanalysis to *"finite rings of
prime characteristic p that are isomorphic to a product of fields"* — `R_q ≅ (F_{q²})^8`
is **that class by construction, not by analogy** — and finds HADES/Poseidon-family
degree estimates *"overly optimistic"* (HadesMiMC: claim 88, actual 168 rounds; ⚠ that
row is footnoted 256-bit state, **partial rounds only, d=3** — *not* our parameter set,
and it is not quoted here as our round count). **This is the same paper that already
produced our 24-round integral floor.** So the two verdicts agree: **integral in
characteristic p is the binding algebraic constraint on σ-Poseidon, and Rubato was never
the threat.**

## 3b. ⚑ Found en route: 47% of σ-Poseidon's rounds do not mix CRT slots

The prime-q lane named one cheap decisive check — *do the σ exponents generate a
**transitive** subgroup of the 8 CRT slots?* — because if σ is conjugation `X → X^31` the
cipher **splits into 8 independent `F_{q²}` ciphers**. Run against the versioned schedule
(`rha_sigma_slots.py`), where `exps[r] = (2d−1) if r%3==2 else pow(5, 1<<((r//3)%4), 2d)`:

```
  group generated by ALL exponents used: order 16
  its orbit on slot 0: [0,...,7]  -> TRANSITIVE (C3 satisfied)

  rounds whose sigma layer acts TRIVIALLY on the slot index:
      [2, 5, 8, 9, 10, 11, 14, 17, 20, 21, 22, 23, 26, 29]   = 14/30 = 47%
  longest run of CONSECUTIVE slot-trivial rounds: 4
```

**The good half:** taken as a whole the schedule **is** transitive, so C3 holds, the
worst case does not occur, and `rha_groebner_cico.py` reading (B) — on which the whole
item-3 verdict rests — **stands.**

⚠ **The bad half, and it is new.** `31 = 2d−1` is exactly `q mod 32`, so `σ_31 ∈ ⟨q⟩` and
acts as the **identity on the slot index** — Frobenius *within* each slot, nothing
between them. And the `r//3` schedule cycles `5 → 25 → 17 → 1`, with `5^8 ≡ 1 (mod 32)`,
so **one block in four uses the identity automorphism outright**, whose layer
`x + c·σ_1(x) = (1+c)·x` is a pure `R_q`-scalar.

⚑ **Over rounds 8–11 nothing mixes slots at all** — the S-box is slot-wise, the `R_q`-MDS
is `R_q`-linear and therefore slot-wise, and both σ exponents in that window are
slot-trivial. **For four consecutive rounds the permutation is slot-diagonal: it
decomposes into 8 independent maps over `F_{q²}`.** That is precisely the 2026/1127 §D
structure the σ layer exists to destroy, and precisely the round-skipping resource an
algebraic attacker wants — **free.**

**It breaks nothing measured here** (surrounding rounds restore transitivity; item 3
clears by hundreds of bits). **But it is a schedule defect with zero cost to fix**:
choose exponents so no round is slot-trivial — drop the `5^8 = 1` block and pair every
`σ_31` round with a slot-moving one. **A round that costs constraints and mixes nothing
is the cheapest thing in this design to correct**, and C3 as currently stated cannot see
it: C3 checks the group generated *across the whole schedule*, not *per round*.
**Recommend C3 be strengthened to a per-round condition.**

---

## 4. What this changes about shipping

**The brief's ordering turned out to be the reverse of the risk ordering.**

1. **The binding leg was REACHED, not closed.** The one technique that reaches a
   decomposition layer gets **2 rounds** and stalls, with a named cause. The calibrated
   MITM bound gives **12 rounds against NR=16 — 1.33×**. ⚑ **NR=16 is now *precedent plus
   a calibrated attack bound plus a technique that was actually run against it*, which is
   materially more than it had, and still not a derivation.** Nothing reaches the design.
2. **Gröbner/CICO clears by hundreds of bits** and removes a worry the brief raised
   explicitly. σ-Poseidon's binding algebraic constraint remains the integral floor at 24,
   and the aiming device (§3a) independently lands on the same paper.
3. ⚑ **The free norm check is the item that should gate shipping.** It is the only one
   where a plausible parameter — one bit of slack in a check the design **does not own** —
   converts a 2^52 attacker *cost* into 2^64 attacker *choices*, per absorbed element,
   with the forgery exhibited at deployment parameters. **And the obligation that would
   settle it is open and filed under the wrong heading.**

**Three recommendations, stated as claims to be attacked rather than verdicts:**

- ⚑ **Do not ship the gadget-Feistel in hash mode until O5 returns an *exact enforced
  ∞-norm bound*, and re-file O5 as a soundness obligation.** It is currently a cost row.
- **Standing refusal: `g` stays dense**, and the top-plane block `g[·][·][3]` most of all
  (§1.0d). Sparsifying it for cost reopens an unbounded deterministic characteristic.
- **Strengthen C3 to a per-round condition** (§3b) and re-pick the σ exponents. 47% of
  rounds mix no slots and 4 consecutive rounds are slot-diagonal; the fix costs nothing.

**And one cheap hardening worth pricing:** `P = 3` (§1.3/§1.0b) removes the purely linear
path through 25% of the state — the single cheap differential pattern this lane found —
at **12 → 16 rows/round, +33%**. Against the ~0.5%-of-circuit sensitivity the pipeline
note established for round count, that is a real cost and a real gain, and it is a
decision rather than an obvious call.

---

## 5. What I could NOT run, and what would unblock it

| not run | why | what would unblock |
|---|---|---|
| the **exact enforced ∞-norm bound** (item 2's open half) | needs 2026/1127's own decomposition schedule; **not in our tree** | O5, re-scoped as a soundness question |
| a **finer-than-cell MITM model** (the thing that bought 2023/1359 its rounds) | structural: **no single cell decomposition makes both nonlinear steps local** (digits are coefficient-local, ring products are slot-local, the change of basis is dense) | new work — a colour-propagation rule for a nonlinearity that re-partitions its cell. **Undone work, not an impossibility.** |
| **2025/932's tooling pointed at σ-Poseidon directly** | the integral floor of 24 came from running its machinery at our base prime, not from running it on the deployed σ-layer | its artifact against the actual σ schedule — **and §3b says the schedule has a defect that a per-round run would surface** |
| a **lower** bound on `D_I` | CheapLunch's bound is *conjectured tight*; Perrin's MIDC is a conjecture. **A defence needs a lower bound and neither is one** | open research |
| **Steiner 2024/310** cross-read | time; it independently duplicates CheapLunch §4.2's Poseidon bound | a second lane |

⚑ **The epistemic line this note must not cross.** Counting §1, four instruments have now
been pointed at the gadget-Feistel and reported little: the algebraic pipeline (no
statement possible), CLAASP-MP (saturated), the MITM family (reach 3, calibrated to 12),
and the carry-DDT automaton (reach 2). **That is one fact about our instruments, not four
about the primitive.** The carry-DDT run is the only one of the four that *reached* the
design at all, and it reached 2 rounds. **NR = 16 is not justified by this note. It is
better-defended than it was and it is still precedent.**
