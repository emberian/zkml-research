# The gadget-Feistel against the CLASSICAL toolchain — CLAASP-MP, and MITM

**Lane question.** `formal-cryptanalysis-pipeline.md` §4 concluded that the gadget-Feistel's
round count **cannot be set**: every computable leg is satisfied at NR ≈ 2–3, the binding leg
(order-2 differential / MITM) is OPEN, and NR=16 is *"precedent, not attack-tested."* The
hypothesis this lane exists to test: **the gadget-Feistel is structurally CLASSICAL, not AO**
— base-B decomposition, Feistel rounds, word operations — **so the classical automated tools
that cannot reach an AO hash may reach it directly**, and would close the open leg.

**Verdict, in one breath.** The hypothesis is **half true, and the half that is false is the
half that decides the answer.** The primitive *is* expressible as a CLAASP component graph —
constructively, exactly, verified against the versioned spec. Two of its three layers are
genuinely classical: **base-B decomposition costs literally zero components** (it is bit-slicing),
and the plane products are exactly CLAASP-MP's own modular-multiplication shape. But the third
layer — the dense public-constant ring combination `F_r` over `Z_q`, q a 64-bit **prime** — has
no primitive in any classical tool, and emulating it costs **14.5 million components and 943
million wire bits per round.** ChaCha, the paper's headline target, is 512 bits of state.

**But the answer did not have to wait for the solver.** The quantity CLAASP-MP bounds — the F₂
algebraic degree — is directly measurable, and it was measured on the real primitive at deployment
parameters. **The only integral property that exists is the trivial 1-round Feistel branch copy**
(which the harness correctly finds, 1024/1024 against a chance baseline of 1); the round function
itself saturates the cube in **one** round, and at r=2 and r=3 nothing survives above chance.
So the F₂ leg says **NR ≥ 2** — agreeing with every other computable leg, and setting nothing.

**And the binding leg is still open.** Twelve automated MITM papers, read at source: **none can be
instantiated.** Not because it is a Feistel and not because it is unkeyed — both of those are
covered in the literature — but because every model needs the nonlinearity to be a *cell-local,
width-preserving bijection*, and base-B decomposition **re-partitions the cell**.

**So NR is still not set, and the reason has moved.** It was "the instrument does not apply"
(§4's verdict). It is now: **the instrument applies, cannot be run at scale, and the quantity it
bounds is saturated at 2 rounds anyway; and the binding leg fails on one named, statable
requirement.** That is a sharper refusal, and §5 argues it is worth more than the old one.

⚠ **Nothing here is an attack, and nothing here clears the design.** Three instruments now report
that they see nothing, and per `feedback-every-instrument-is-blind-to-the-next-wound` that is
**one** fact about our instruments, not three about the primitive. Two of the findings below are
about the *tools*, not about us.

---

## 0. What is measured, what is read, what is derived

Per `feedback-a-brief-is-a-claim-and-lanes-execute-it`, every load-bearing claim carries its tag.
Scripts: `notes/feistel-tooling-scripts/`.

| claim | tag |
|---|---|
| CLAASP-MP reproduces its own published SIMON-32 example, 6/6 rows, all refutable | ⚑ **[measured]** `fct1_claasp_mp_guard.py` |
| CLAASP's `modulus` field never reaches any constraint model | ⚑ **[measured]** `fct2_modulus_trap.py` |
| `check_anf_correctness` misses that divergence with p=0.54 at the default sample count | **[measured]** `fct2b_selfcheck_reach.py` |
| every mod-q operation the primitive needs is EXACTLY expressible in CLAASP's vocabulary | ⚑ **[measured, exhaustive]** `fct3_modq_primitives.py` |
| a full round reproduces the versioned spec | ⚑ **[measured]** `fct5_round_expressibility.py` |
| 14.5M components / 943M wire bits per round at deployment | ⚑ **[computed by the verified encoder]** `fct7_deployment_cost.py` |
| no F₂ integral property beyond chance survives 2 rounds; the r=1 branch-copy property IS found | ⚑ **[measured, 10 base states]** `fct6_f2_degree.py` |
| no published automated MITM model can be instantiated on this shape | ⚑ **[read at source, 12 papers]** §4 |
| CLAASP-MP's component vocabulary and mod-mul model | **[read at source]** eprint 2026/735 §3.3, Alg. 4 |
| SS22 marks 2-branch Feistel "Inapplicable" to the automatic MITM tool | **[read at source]** eprint 2022/189 §7.1, Table 3 |
| the LINEAR_LAYER evaluator/model transpose | ⚠ **[REFUTED — my source reading was wrong]** see §1.4 |

**Corpus statement**, per the PREFLIGHT corpus-blindness rule: the MITM sweep (§4) was run over
`~/paperbin` and the **full local IACR eprint mirror** (`~/dev/gh/forks/IACR-eprint-mirror/`,
1996→2026/1053+). That corpus is **cryptology-only**; it cannot see arXiv, ITP/CAV, or grey
literature. No absence claim below is stronger than "absent from the IACR corpus."

---

## 1. Can the gadget-Feistel be expressed as a CLAASP component graph? **YES.**

The brief said: *if no, say exactly which component has no encoding — that is the finding.*
The answer is yes, so the finding is elsewhere. Here is why, precisely, because the "yes" is
narrower than it sounds.

### 1.1 What CLAASP-MP actually models

Read at source, eprint 2026/735 §3.3 and the installed tree. The vocabulary is **bit-level over
F₂**: XOR, AND, NOT, OR, COPY, ROTATE, SHIFT, S-box (via its ANF), linear layer (an F₂ matrix),
MODADD, MODSUB, FSR. The new modular-multiplication model (§3.3.4, Algorithm 4) is
`z = (x·y) mod 2ⁿ`, expanded as bitwise-AND partial products accumulated by exact modular
addition, with bits `i+j > n−1` **truncated** — mod-2ⁿ by construction.

⚑ **CLAASP-MP's model has no odd-prime arithmetic at all.** Its `word_operation` dispatch covers
exactly `XOR, ROTATE, SHIFT, AND, NOT, OR, MODADD` and then
`raise NotImplementedError`.

There is **one** odd-prime component in the library — `idea_modmul`, IDEA's multiplication
mod 2¹⁶+1 — and it is **evaluator-only**: `sat_constraints`, `cp_constraints`,
`smt_constraints`, `cms_constraints` and `algebraic_polynomials` every one of them raise
`NotImplementedError("... are not yet implemented")`.

> ⚑ **The same library contains the honest refusal and the silent misanswer, side by side.**
> `idea_modmul` refuses to be modelled. `MODADD` with an odd modulus is modelled — as something
> else (§1.2). The behaviour that protects a user is the one that says no.

⚠ **A capability in the paper that is not in the tree.** The modular-multiplication model the
brief was most interested in (2026/735 §3.3.4, Algorithm 4) and the MSX target it is demonstrated
on are **not present in the public repository** — there is no MSX cipher and the MP dispatch has
no MODMUL branch. *Absence claim, stated with its instrument*: checked on 2026-08-18 against refs
`origin/main`, `origin/develop`, tag `v3.2.0`, and branch `feat/monomial_prediction_new_feats`.
So Table 1's MSX rows are not reproducible from the public tree, and neither is the mod-mul model.

### 1.2 The trap: `modulus` is a field that goes nowhere

CLAASP's `MODADD`/`MODSUB` components take a `modulus` argument, which reads like the escape
hatch. It is not. Measured (`fct2`), with sensitivity controls that pass (a width change and a
MODADD→XOR swap both move the fingerprint):

```
width fixed at 8, modulus 2^8 vs 251 (odd prime)
  EVALUATOR    differs = True   (33,910 / 65,536 inputs disagree)
  MODEL TEXT   differs = False  (SAT/CP/SMT/CMS constraint text byte-identical)
  CLAASP-MP ANF of output bit 0 differs = False
```

The `modulus` field is honoured by the **scalar evaluator only**. Every constraint model — and
CLAASP-MP with them — emits the mod-2ⁿ ripple-carry encoding regardless. **A primitive declared
over Z_p, p odd, is silently analysed as a primitive over Z_{2ⁿ}**, and the wrong answer arrives
in the same format as a right one.

This is precisely `minted-refusal-renders-as-the-expected-verdict` in someone else's tool. The
mitigation is that CLAASP-MP ships `check_anf_correctness`, which compares the model's ANF to the
evaluator. Measured how well it catches this (`fct2b`), because a single lucky run is not evidence:

| output bit (lsb=0) | disagreement rate | P(20 samples all agree) |
|---|---|---|
| 7 (MSB — the bit `output_bit_index=0` tests) | 0.0300 | **0.544** |
| 3 | 0.3270 | 3.6e-4 |
| 0 | 0.5167 | 4.8e-7 |

`check_anf_correctness(0)` returned **True at num_tests=10 and 20** and False from 50 up. So the
self-check is a real detector but a *probabilistic* one, and on the bit its own default tests it
is **a coin flip at the default sample count.** ⚑ **If we ever point CLAASP at anything, run
`check_anf_correctness` at ≥200 samples on a low-order bit, or it is not a check.**

### 1.3 The encoding, and what each layer costs

Since mod-q is not primitive, it is emulated. All three emulations are verified **exhaustively
exact** against Python ground truth (`fct3`, n=6, q=61, with a live guard: the same comparison
against a wrong modulus q+1 goes red on 1,830 pairs).

| operation | encoding | components |
|---|---|---|
| **base-B decomposition** `Y_j = digits_B(c)` | ⚑ **bit-slicing — a wire relabel** | **0** |
| `addq(a,b)` | MODADD/MODSUB at width n+1, broadcast the borrow, select | 6 |
| `subq(a,b)` | mirror of addq | 4 |
| `mulq_const(v, g)`, g public | double-and-add over `addq`; no Barrett, no wide arithmetic | ~2n·6 |
| `Y_j · Y_{j+1}` (plane products) | ⚑ **mod-2ⁿ exact** — operands < B, and `d·B² < q` so no reduction | 5n each |

⚑ **Two of the three layers are exactly as classical as the hypothesis predicted.**
Base-B decomposition with `B = 2^16` over a 64-bit modulus *is* bit-slicing and costs nothing —
the very step that makes the primitive opaque to the *algebraic* instrument (it does not commute
with affine maps, §4 of the pipeline note) makes it **free** for the *bit-level* one. And the
plane products land exactly on CLAASP-MP's new Algorithm 4: `d·B² = 16·2³² = 2³⁶ ≪ q ≈ 2⁶⁴`, so
the whole product layer needs **no modular reduction at all**.

**The third layer is where it dies.** `F_r = Σ g·Y + Σ h·Z` is a dense combination with public
constants **in R_q**. `v ↦ g·v mod q` is Z-linear but **not F₂-linear**, so it gets no linear-layer
encoding and must be built from ~2n modular additions per coefficient product — and there are
`w²·(K+P)·d² = 4·4·6·256 = 24,576` such coefficient products per round.

### 1.4 ⚠ A claim I made and then refuted

While building this I read CLAASP's two LINEAR_LAYER implementations as transposes of each other
(`generic_functions.linear_layer` computes `out[c] = ⊕_r in[r]·M[r][c]`; the MP model's
`add_linear_layer_constraints` reads `M[row]` as an output row). I wrote a test to report it as a
tool bug. **The test refuted me** (`fct4`): on an asymmetric matrix the evaluator and the MP model
agree, with a symmetric-matrix control passing. The reading was wrong; the claim is withdrawn and
is recorded here only so nobody re-derives it from the same two files.

What was real is smaller and worth keeping: **CLAASP's LINEAR_LAYER cannot change width**, because
the evaluator emits exactly `input.len` output bits. A 1-bit broadcast must be built another way
(`0 − x mod 2ⁿ` via MODSUB, which is convention-free).

---

## 2. The instrument is armed — and then cannot be pointed

### 2.1 The falsification guard passes, on the paper's own numbers

Per the brief, and per this repo's own history of a guard row asserting a number its source paper
does not contain (`formal-cryptanalysis-pipeline.md` §8 C1): before pointing CLAASP-MP at
anything of ours, it reproduces a result **published in eprint 2026/735 itself**, Appendix B
Listing 1, SIMON-32 at 3 rounds. Expectations transcribed from the paper, **not** from CLAASP's
test suite.

```
6/6 paper rows reproduced, 6/6 rows LIVE, in 1.0s
  find_upper_bound_degree_of_specific_output_bit(0)            = 5
  find_exact_degree_of_specific_output_bit(0)                  = 5
  find_upper_bound_degree_of_all_output_bits()                 = [5]*16 + [3]*16
  find_exact_degree_of_superpoly_of_specific_output_bit(0,p16) = 2
  find_upper_bound_degree_of_cube_monomial_...(0, p16)         = 1
  find_keycoeff_of_cube_monomial_...(0, p16)  = k33*k57 + k50*k57 + k51*k57 + 1
```

Each row was then re-run against a deliberately wrong expectation and **refused it**. The
instrument works and its check can go red.

Environment, for reproduction: **CLAASP-MP is not in the PyPI release.** PyPI's latest is
`claasp==3.0.0`, which predates it and ships only the older `division_trail_search`. The MP module
is in the repository on `main`, `develop` and tag **`v3.2.0`** (and on the branch
`feat/monomial_prediction_new_feats`, used here). It needs **SageMath + Gurobi**. Both were
obtained without a system Sage: `passagemath-standard` wheels (pip, ~2.0 GB) supply the three Sage
imports (`sage.crypto.sbox`, `sage.rings.polynomial.pbori`, `sage.all`), and `gurobipy`'s bundled
size-limited licence runs SIMON-32 fine.

### 2.2 And then the size

The same encoder verified at toy scale, run against a counting-only builder at deployment
parameters (`fct7`):

| | toy (verified exact) | **deployment** |
|---|---|---|
| parameters | n=12, d=4, w=1, K=4, B=2³, P=2 | n=64, d=16, w=4, K=4, B=2¹⁶, P=2 |
| state | 96 bits | 8,192 bits |
| components / round | 11,495 | **14,512,940** |
| wire bits / round | 147,490 | **942,685,586** |
| digit extractions | 16, **0 components** | 256, **0 components** |
| NR=16 | — | **232M components, 15.1G wire bits** |

*(The toy row is what CLAASP actually built and evaluated; the counting builder
reports 11,494 / 147,479 — one constant apart, from a cache that differs by one
entry. The deployment column is that same verified encoder, counted.)*

**The full round was checked against the versioned spec, not asserted:**
40/40 random states agree, and the guard — the same spec with different round
constants — disagrees 40/40. Expressibility is constructive.

**Cross-checked by hand**, so the headline number does not rest on one script. The `F` layer
dominates: `w²·(K+P) = 96` constant ring products × `d² = 256` coefficient multiplies ×
`mulq_const` at ~94 `addq` (63 doublings + ~32 additions for a random 64-bit constant) × 6
components ≈ **13.9M**, plus ~0.66M for the `Y·Y` layer and ~0.8K for the two mod-q addition
layers → **≈14.67M**. Measured: 14,512,940. The 1.1% gap is the actual popcounts of the sampled
constants. ⚑ **97% of the cost is one line of the spec** — `F_r = Σ g·Y + Σ h·Z`.

CLAASP-MP allocates at least one binary exponent variable per wire bit, plus COPY variables per
fan-out. Against that, the instances the paper actually solves: SIMON-32 3 rounds (32-bit block,
1.0s here), **ChaCha 6.75 rounds at 512 bits of state**, Trivium at 288, MSX-128 at 128.

**One round of ours is ~9.4×10⁸ wire bits against a 512-bit headline.** This is not a licence
problem — the bundled Gurobi caps at ~2,000 variables, but a full licence does not close six
orders of magnitude either. ⚑ Per `feedback-a-cost-verdict-outlives-its-premise`, this cost is
re-derivable and it is not a cost estimate standing in for a constraint: it is what the verified
construction emits.

---

## 3. ⚑ The measurement that settles it anyway: the quantity is already saturated

The scale wall would be an unsatisfying place to stop — "we could not run it" says nothing about
the primitive. But the quantity CLAASP-MP *bounds* is measurable directly, and the answer does not
need the solver.

CLAASP-MP computes an **upper bound on the F₂ algebraic degree**, and turns
`degree < cube dimension` into an integral distinguisher. The **exact** degree is computable by
Möbius transform wherever 2^m evaluations are affordable, and the MILP bound is always ≥ it. So
an exact degree that already equals the cube dimension **settles the question before the solver
runs**.

Measured at **deployment parameters** (q = 2⁶⁴−257, d=16, K=4, B=2¹⁶, P=2), against the versioned
spec, over a cube of the low 16 bits of one input coefficient — exactly one plane `Y₀`
(`fct6_f2_degree.py`):

The key identity: **the ANF coefficient of the full monomial `x₀…x_{m−1}` over an m-cube is the
XOR of the function over all 2^m cube points.** So a nonzero cube sum on an output bit means its
exact degree in the cube variables is already `m`, the maximum — and no upper bound the MILP could
prove can go below it. One XOR per evaluation, and it runs on the real primitive.

And **one base state is not enough**: for a random permutation each output bit has a zero cube sum
with probability ½, so "half the bits balanced" *is* what randomness looks like. A genuine
integral property is a bit balanced for **every** base state. So each row runs 10 independent base
states and counts bits balanced in all of them, against the chance baseline `2048·2⁻¹⁰ = 2.0`.

Measured (`fct6_f2_degree.py`, w=1, m=12, 10 base states, controls C1–C3 pass):

| rounds | exact degree 12 (single base) | L branch | R branch | **balanced in ALL 10 bases** | L | R | chance |
|---|---|---|---|---|---|---|---|
| 1 | 512/2048 (25.0%) | 0/1024 | **512/1024 (50.0%)** | 1025/2048 | ⚑ **1024/1024** | **1/1024** | 2.0 |
| 2 | 1015/2048 (49.6%) | 47.6% | 51.6% | **3**/2048 | 3 | 0 | 2.0 |
| 3 | 1002/2048 (48.9%) | 49.3% | 48.5% | **2**/2048 | 1 | 1 | 2.0 |

⚑ **Read the r=1 row first — it is the measurement's own positive control.** The left branch shows
`1024/1024` bits balanced across every base state, against a chance expectation of 1. That is a
**real integral distinguisher**, and the harness finds it — it is the copied Feistel branch, a
property of 1-round Feistels and not of `F_r`. So the instrument demonstrably *can* see an integral
property when one exists.

**And on the branch that actually passed through `F_r`, it sees 1/1024 — chance.** The round
function saturates the cube in **one** round. By r=2 the trivial branch property is gone and the
whole output sits at the chance baseline (3 against 2.0 expected); at r=3, 2 against 2.0.

*Corroborated at a wider cube*: a separate single-base run at m=16 gave 533/2048 at r=1 (0 left,
533/1024 = 52.1% right) and 1027/2048 = 50.1% at r=2. The 10-base run at m=16 was abandoned
part-way — the box was at load average 195 from sibling lanes — so the m=12 grid is the complete
one and is what the table reports.

The mechanism is not subtle: step (1) of the round is a **64-bit modular addition**, whose carry
chain alone drives the F₂ degree of the high bits to the full width of the addend in **one**
operation, before any plane product or ring multiplication is applied.

⚑ **Reading.** CLAASP-MP computes an *upper* bound on this degree, and an upper bound is never
below the exact value. So wherever the exact degree already equals the cube dimension, the tool
**cannot certify an integral distinguisher over that cube no matter how well the MILP is solved.**
The ~10⁹-variable model would return "no distinguisher" — which 2¹⁶ evaluations of the real
primitive settle in 18 seconds.

⚠ **This is not a security result.** "The F₂ degree saturates immediately" means the F₂ degree
instrument is **blind** here, not that the primitive is strong. It is the same shape of statement
as §4's "the algebraic instrument does not apply" — a *third* instrument reporting that it has
nothing to say. ⚑ And per `feedback-every-instrument-is-blind-to-the-next-wound`: three
instruments agreeing they see nothing is **not** three pieces of evidence.

⚠ **A methodological trap this measurement walked into and had to be pulled out of.** The first
version reported "1515/2048 bits balanced at 1 round" as though that were an integral
distinguisher. It is not — that is the chance baseline plus the trivial branch copy, and the
multi-base test above is what separates them. **A single base state cannot tell a distinguisher
from a coin.** The same error is available to anyone reading a CLAASP-MP balancedness output
without asking over what it is balanced.

### 3.1 Two controls that matter

**The one that caught me.** The degree harness's first control asserted that bit `k` of
`x + c mod 2^M` has exact F₂ degree `k+1`. It went red. **The analytic claim was wrong, not the
harness** — the carry into bit k depends only on `x_0..x_{k−1}`, so the degree is `max(k,1)`. Kept
in the script with that history in its docstring, per `minted-a-falsifier-that-stopped-falsifying`.

⚑ **The one inside the measurement.** The r=1 left branch is a *known-true* integral property, and
the run finds it at `1024/1024` against a chance baseline of 1. That is the control that makes
every "nothing found" row below it mean something: **the harness demonstrably sees an integral
property when one is there.** A "we found nothing" result whose instrument has never been shown to
find anything is the shape this repo has been burned by before.

---

## 4. The binding leg: MITM. **No published model can be instantiated.**

This is the leg `formal-cryptanalysis-pipeline.md` §6 item 1 named as binding and never ran.
Twelve papers read at source from the local IACR mirror — the CiC 2026 unified model
(Degré–Derbez–Schrottenloher, eprint **2025/2213**), the ASCON models paper (2024/298), Bao et al.
(2020/467), Dong et al. (2021/427), Superposition-MITM (2021/575), Schrottenloher–Stevens for
permutations (2022/189) and block ciphers (2023/816), Qin et al. on sponge hashing (2022/1714),
Dong et al. generic sponge frameworks (2024/604), Hou et al. on Feistel (2023/1359) and on binary
matrix linear layers (2025/082), Michel et al. differential-MITM on Feistel (2025/1911).

⚠ **Provenance, stated exactly**: the twelve-paper sweep was executed by a delegated reader against
the local mirror. Per `feedback-read-the-blocker-before-you-relay-it` I **re-opened the two
load-bearing quotes myself** instead of relaying them — SS22's `b=2 → MITM (automatic) Inapplicable`
table row, and the CiC paper's *"additions of constants and application of S-Boxes do not change the
colors of individual bytes"*. Both check out verbatim. The remaining rows carry the sweep's reading,
not mine.

**What every model requires**, and where ours fails:

| requirement | every published model | the gadget-Feistel |
|---|---|---|
| state unit | a **cell or bit** over F₂, each independently coloured (blue/red/grey/white/green) | 64-bit prime-field coefficients |
| nonlinear layer | a **unary, cell-local, width-preserving bijection** (S-box); its *contents* are never consulted | ⚑ **fails on all three**: digit decomposition **re-partitions the cell** 64→4×16; `Z = Y_j·Y_{j+1}` is **two-input and non-bijective**; ring multiplication is **not coefficient-local** |
| linear layer | MDS over GF(2⁸) with cell-wise cancellation tracking, *or* (Hou 2025/082) a literal 0/1 F₂ matrix scored by rank | dense combination over `Z_q`; neither regime is defined |
| size | Michel et al. cap at **n < 128 bits**; Hou's DoF check "**can not be applied to large binary matrix (n > 4)**" | 8,192 bits |

⚑ **Two things that are NOT the blocker, and must not be cited as one.** Being a **Feistel** is
fine — Hou 2023/1359 is a dedicated Feistel MITM model, and Camellia, Simpira, Areion and
Lesamnta-LW are all attacked. Being **unkeyed** is fine — Schrottenloher–Stevens 2022/189 covers
permutations outright, and the Aria-DM attack draws all its degrees of freedom from the state.

Two limits worth quoting exactly:
- SS22 §7.1 makes **no structural assumption on the round functions** and represents any
  generalised Feistel as a graph of 2-XOR cells — but **Table 3 marks the b=2 case (2-branch
  Feistel) "Inapplicable"** to the automatic tool. Only a hand-built guess-and-determine reached
  5/15 rounds on Simpira-2. **Our design is b=2.**
- Michel et al. §6 leaves **modular addition** an open problem for their model; Qin et al. handle
  ARX only by expanding it into its **carry ANF over F₂**.

**Prime-field / arithmetization-oriented targets: zero papers.** A grep for
`prime field | arithmetization | Poseidon | Rescue | MiMC | F_p` across all twelve returns
nothing. Monolith (2023/1025) — a prime-field hash whose nonlinearity is *also* chunk
decomposition plus lookup, the closest structural cousin we could find — has **no MITM analysis at
all**.

⚠ **This is the sentence that matters, and it is the one it is tempting to skip.**
"No model can be instantiated" means **there is no published attack AND no published analysis.**
The adversary's path is "extend the nonlinear-layer colour rules to a
decomposition-plus-multiplication primitive" — work nobody has done, **not work known to be
impossible.** Per `feedback-honest-label-hides-transmutable-mediocrity`: this caveat is
**UNDONE WORK in a theorem's clothing**, not a theorem of the model. The MITM leg is still OPEN.

### 4.1 A structural fact derived here, and it sharpens the picture

At `q = 2⁶⁴−257`: `q ≡ 3 (mod 4)`, `q mod 32 = 31`, so `ord_32(q) = 2` and `X¹⁶+1` factors into
**8 irreducible quadratics** — `R_q ≅ (F_{q²})⁸`. (This is our τ=2 point; consistent with
`ring-hash-dual-mode.md` §5a.) So ring multiplication **is** cell-local — in the CRT basis, over
8 cells of 128 bits. But digit decomposition is cell-local in the **coefficient** basis, and the
change of basis between them is a dense F_q-linear map.

⚑ **No single cell decomposition makes both nonlinear steps local.** That is a sharper statement
of why the cell-colouring framework has nothing to grip — and it is a property of the design, not
of the tools.

### 4.2 The rest of the classical toolchain, assessed rather than tried

The brief also named CryptoSMT and the `Deadlyelder/Tools-for-Cryptanalysis` catalogue. **[derived,
not run]** — and the reason is structural rather than an effort budget:

- **SAT/SMT differential search (CryptoSMT, ArxPy, CLAASP's own SAT/CP/SMT models) hits the same
  wall twice.** First the encoding wall: they are bit-level over mod-2ⁿ words, so every mod-q step
  pays the §1.3 emulation and the toy round is already 11,495 components. Second, and worse, they
  search **XOR-differentials**, which is the wrong notion here — the differential that matters for
  this design is **additive mod q** (that is what `P ≥ 1` exists to kill, and what the prior lane
  measured dead at order 1). A tool that enumerates XOR trails through a mod-q emulation would be
  answering a question nobody asked.
- **This does not make them useless forever.** The right use would be a SAT search over the
  *additive* differential in the emulated graph — but that needs a differential model for the
  emulation, which is new work, and it duplicates a leg the prior lane already computed.

---

## 5. NR: what the computed evidence says, and what remains precedent

The brief: *report NR honestly; if it says more than 16, that is the instrument working, and at
~0.5% of the circuit there are no cost grounds for resisting.* There are no cost grounds and no
answer above 16 to resist.

| leg | instrument | says | mark |
|---|---|---|---|
| skip family A1–A4 | GSR-style, computed | NR ≥ 2 | EXACT-ATTACK (prior lane) |
| diffusion | measured | NR ≥ 2 | measured (prior lane) |
| generic algebraic A5 | Gröbner/resultants | **no statement possible** | N/A by construction (prior lane) |
| order-1 additive differential | computed | NR ≥ small | EXACT-ATTACK (prior lane) |
| **F₂ integral / monomial prediction** | ⚑ **CLAASP-MP, this lane** | **NR ≥ 2** — the only integral property is the trivial 1-round Feistel branch copy; nothing above chance at r=2 or r=3 | ⚑ **measured, new** |
| **order-2 / MITM / boomerang** | ⚑ **12 automated MITM models, this lane** | ⚑ **no model instantiable** | ⚑ **STILL OPEN** |

**NR = 16 remains precedent, not attack-tested.** This lane adds one computed leg and it agrees
with all the others at NR ≈ 2. The binding leg is unmoved.

⚑ **What changed, and it is not nothing.** §4 of the pipeline note left MITM as *"the first
attack-me item, never run."* It has now been run **as far as the published state of the art can
be run**, and the result is a named, sourced impossibility-of-instantiation with the two
plausible excuses (Feistel, unkeyed) explicitly eliminated. The open leg is the same leg; the
*reason* it is open is now specific: **it needs a colour-propagation rule for a nonlinearity that
re-partitions its cell.** That is a statable research problem, not a gap.

**Legs that remain precedent-only**, named as the brief requires:
1. **MITM / order-2 / boomerang.** The binding one. No instrument reaches it.
2. **Indifferentiability.** NR=16 rests on HKT's 14-round result for 2-branch Feistel **with ideal
   round functions**, and nothing about `F_r` is an ideal round function. Untouched by this lane.
3. **Rebound / differential over ≥2 rounds in the F_q metric.** Neither the F₂ instrument (§3,
   saturated) nor the algebraic one (§4 of the pipeline note, non-polynomial) measures it.

⚑ **And the honest cost note.** The pipeline note's ~0.5%-of-circuit figure for NR 16→18 is a
reason not to defer the *fix*; it is not a reason to treat 16 as safe. **Nothing computed
justifies 16 rather than 14 or 24.** If a number must be defended outward today, the defensible
sentence is *"16 is a structural precedent with a 2× margin over every leg any instrument can
compute, and the binding leg is unanalysed."*

---

## 6. ⚑ The generalizable finding, and the gate amendment

The hypothesis was: *AO-resistant does not mean unanalyzable — it may mean analyzable by
CLASSICAL tools instead.* **Measured, the correct form is narrower and more useful:**

> ⚑ **A primitive can be classical in its NONLINEARITY and arithmetic in its LINEARITY, and the
> classical toolchain prices the linearity.** Base-B decomposition over a 64-bit modulus is
> *free* in a bit-level tool — literally zero components. The plane products are free too. What
> costs 14.5M components per round is the **dense public-constant multiplication over Z_q**, the
> part that looks most innocuous in the spec and is written `Σ g·Y` on one line.

So "is it classical-shaped?" is the wrong question, because the answer is *partly*, and the
partly is not where the cost is. The question that predicts the outcome is:

> **In which layer does the odd-prime modulus survive?**

If the modulus is reduced away before the linear layer (as in our product layer, where
`d·B² ≪ q`), that layer is classical and free. If it survives into the linear layer, that layer
costs `Θ(n)` modular additions per multiply and the analysis is over.

✅ **LANDED as `swarm/BRIEF-TEMPLATE.md` §7d-bis** (2026-08-18) — six ordered steps, each paid for
by something that went wrong in this lane:

1. **Name the substrate of each LAYER separately**, not of the primitive. A layer whose values are
   provably small relative to the modulus is a **classical layer**, priced against bit-level tools.
2. **Check the tool's arithmetic field before its capability list.** A `modulus` parameter the
   models ignore is worse than an absent one; run the tool's self-check at ≥200 samples on a
   low-order bit.
3. **Before "the tool cannot be run", ask what QUANTITY it bounds and whether it is directly
   measurable.** A scale wall is not a verdict; the quantity behind it usually is.
4. **One base state cannot tell a distinguisher from a coin**, and the grid must contain a
   known-true property the harness has to find.
5. **"No published model can be instantiated" is UNDONE WORK**, stated with the failing
   requirement *and* the plausible non-blockers eliminated by name.
6. **Count the instruments and do not add them up.**

---

## 7. Reproduce

```bash
# environment (no system SageMath needed)
python3.12 -m venv sageenv && ./sageenv/bin/pip install passagemath-standard gurobipy bitstring networkx sympy
git clone --branch feat/monomial_prediction_new_feats https://github.com/Crypto-TII/claasp claasp-mp-src
#   ⚠ PyPI claasp==3.0.0 does NOT contain the monomial-prediction module.

cd notes/feistel-tooling-scripts
export PYTHONPATH=/abs/path/to/claasp-mp-src:.
PY=/abs/path/to/sageenv/bin/python

$PY fct1_claasp_mp_guard.py         # the falsification guard, ~1s
$PY fct2_modulus_trap.py            # the modulus trap
$PY fct2b_selfcheck_reach.py        # how blind the self-check is  (~10 min, 2^16 evals)
$PY fct3_modq_primitives.py         # exhaustive mod-q exactness
$PY fct4_linear_layer_transpose.py  # the claim I made and refuted
$PY fct5_round_expressibility.py    # full round vs the versioned spec (~25 min)
$PY fct7_deployment_cost.py         # deployment-scale graph size, seconds

# fct6 needs NO claasp, sage or gurobi -- any python3 with sympy will do
FCT6_CONFIGS="1:12:10" FCT6_ROUNDS="1,2,3" python3 fct6_f2_degree.py   # ~4 min
python3 fct6_f2_degree.py           # the default grid: w=1 m=16, w=4 m=12.
                                    # ⚠ hours on a contended box; the m=16
                                    # 10-base row was abandoned at load avg 195.
```

⚠ `fct5` patches the versioned spec's ring degree `D = 16 → 4` by textual substitution and
**asserts the substitution happened**. If `~/src/ring-ro-hash/design_gadget_feistel.py`'s parameter
block is ever reformatted, that assertion fires rather than the harness silently testing nothing.
