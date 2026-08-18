# The computed line: can we provision hash rounds by arithmetic instead of by nerve?

2026-08-18. STRATEGY + BUILD lane. Written incrementally.

The thesis under test, in ember's words: *everyone provisions hash rounds against
guesswork; a designer runs the attacks they know, survives, adds a margin they cannot
justify precisely — because they cannot compute where the line is. If you can COMPUTE
the line, you ship AT it: fewer rounds than a heuristic designer dares, with a BETTER
security argument rather than a worse one.*

The brief named the make-or-break and demanded it first. Here it is.

---

## 0. THE MAKE-OR-BREAK, ANSWERED: the naive thesis is REFUTED — six times, none opposed

**The level form of the thesis — "compute the line, ship fewer rounds" — is false for
AO hashes, and we found SIX independent instances of it being false in the same
direction and none in the other.** Every time someone replaced a heuristic estimate with a
computed one, the line moved *outward*: the attack reached **further** than the designers
believed, so the computed provisioning is **more** rounds, not fewer.

The premise of the thesis, though, is not merely right — **it is the designers' own word.**
Poseidon, eprint 2019/458 §5.4, verbatim:

> *"Given the minimum number of rounds necessary to provide security against all attacks
> known in the literature, **we arbitrarily decided to add** (1) two more rounds with full
> S-box layers, and (2) 7.5% more rounds with partial S-box layers, i.e., +2 R_F and
> +7.5% R_P."*

**"Arbitrarily."** ember's framing — *a margin they cannot justify precisely* — is not our
inference about the field; it is the field's own description of itself, in the paper that
defines the family. What is wrong is only the expectation that computing it comes back
cheaper.

This is not the failure mode the brief feared, and the difference matters. The brief
worried about *defense-side looseness* — that our provable bound would sit further out than
a designer's confident guess. **That worry is exactly right, and it is also exactly
inapplicable, for a reason that turns out to be the organizing fact of this whole note.**
See "the sign of the error" below.

### Instance 1 — GSR against Poseidon (KoalaBear, t=24, α=3)

`eprint 2026/1692`, Bhati–Tariq–Ashur, in paperbin as
`gsr-sbox-skipping-poseidon-2026-1692.pdf` (+`.txt`).

Their gadget is *closed-form arithmetic*, not a search: it absorbs **one initial full
round and t−2k partial rounds**, and the residual system has degree exactly
`α^(Rp + Rf1 − t + 2k)` (§7.1). We re-implemented the degree and solver-cost formulas
and **reproduced all five rows of their Table 1 to within 0.6 bits** — a falsification
guard, in `notes/ring-hash-scripts/computed_line.py` §1. It passes.

Now the comparison the brief asked for — *our computable bound vs the designers'
provisioned rounds*, at the shape the attack occupies (Rf0 = 1):

| target | family | computed line demands | deployed | ratio |
|---|---|---|---|---|
| 2^100 | CICO-1 | Rp ≥ 48 | Rp = 23 | **2.1×** |
| 2^128 | CICO-1 | Rp ≥ 57 | Rp = 23 | **2.5×** |
| 2^160 | CICO-1 | Rp ≥ 67 | Rp = 23 | **2.9×** |
| 2^128 | CICO-2 | Rp ≥ 36 | Rp = 23 | 1.6× |

**The computed line sits 1.6–2.9× further out than the deployed parameter.** Shipping at
our computable line here means shipping *more* rounds. That is the refutation, stated
plainly, on the case the brief chose.

### Instance 2 — integral/division property in characteristic p, and this one is ours

The heuristic instrument designers actually use for integral attacks is *algebraic-degree
saturation*: once the degree saturates, the integral dies. Measured on a real-MDS
Poseidon of our width, that instrument says the full-element integral dies at **r ≈ 5**
(`ring-hash-cryptanalysis.md`, priced-weakness 2, d=4, robust across seeds).

The exhaustive instrument — Beyne–Verbauwhede's propagation machinery (eprint 2025/932),
run verbatim at our base ~2^64 by this repo on 2026-08-17
(`ring-hash-scripts/integral_char_p_settling.sage`, guarded against the authors' own
published 1/13/20 and it caught a real harness bug — but see §8) — says the τ=2 property survives
to round **24**.

**4.8× further out.** And B–V's own verdict on the estimates they replaced is that they
were *"overly optimistic"* — the authors themselves report the line moving outward.

### Instance 3 — our own deployed Poseidon2, from the sibling lane

`notes/gsr-poseidon-2026-1692.md` (landed 2026-08-18, commits `d741c96`, `1f880a3`) ran
GSR against our deployed BabyBear w16 instance and computed the repair: **R_P 13 → 15**
kills the practical CICO-1 attack, for +1.4% in-circuit. Deployed R_P is **13**.

**The computed line is again further out than the deployed parameter — 1.15×.** Third
independent instance, same direction.

### Instances 4 and 5 — and by now it is a pattern, not a coincidence

**4. Ashur, Buschman & Mahzoun, eprint 2023/537** (*"Algebraic Cryptanalysis of the HADES
Design Strategy"*). They audited Poseidon's own Gröbner provisioning and found **four
distinct defects, every one of them in the designers' favour** — including a literal
transcription error (a `3` where a `2` belongs) and an upper bound used where a lower bound
was required. Abstract, verbatim:

> *"we show that **the complexity of the attack is lower than claimed** with the direct
> implication that **there are cases where the recommended number of rounds is insufficient
> for meeting the claimed security.**"*

Concretely (§3.2): the designers' equation *"would imply that 6 full rounds and 22 partial
rounds are sufficient for α = 3, t = 2, p ≈ 2^1024, and a desired security level of 128
bits, **whereas to gain that security level for these parameters, at least 35 partial rounds
are required.**"* **35 vs 22 — 1.6× further out.** Their conclusion: *"partial rounds are not
providing the claimed resistance"*, and *"the ongoing erosion in the security of HADES
instances."*

**5. Merz & Rodríguez García, eprint 2026/306**, §6 — and this one is behavioural rather
than analytic:

> *"the number of external rounds in [GKK+26] was **increased** after disclosing a
> preliminary report of our findings to Ethereum's Poseidon initiative."*

**The deployed round count has already moved outward once, on the R_F axis, in response to
an attack.** That is the LEVEL claim being falsified by the ecosystem in real time.

### ⚑⚑⚑ The sign of the error is PREDICTED BY THE INSTRUMENT — this is the organizing fact

Six instances outward, none inward, is a pattern that wants an explanation, and there is a
clean one. Sort the families by whether a *provable defense-side bound exists at all*:

| leg | is there an EXACT-DEFENSE bound? | direction of the designers' error | their own words |
|---|---|---|---|
| **statistical** (differential/linear) | ⚑ **YES** — the wide-trail argument, via branch number | ⚑ **CONSERVATIVE, and they say so** | Poseidon2 §7.1: *"Note that this is a **pessimistic** estimate."* |
| **algebraic** (Gröbner, CICO, skipping) | ⚑ **NO** — Perrin's point; there is nothing to be loose | ⚑ **OPTIMISTIC, corrected ≥4 times** | Ashur et al.: *"the complexity of the attack is **lower than claimed**"* |

> **The brief's fear — "formal bounds are looser than heuristic ones" — is TRUE exactly on
> the families where a formal bound already exists, and those are the families that are NOT
> BINDING. On the binding families there is no formal bound to be loose, and the heuristic
> errs the other way.**

That single sentence resolves the make-or-break, and it also explains why the thesis
*felt* right: in symmetric cryptography generally, provable-security looseness is the
dominant experience. In **AO** cryptography the binding constraint moved to a family with
no provable bound at all, and the error flipped sign with it. Nobody has said this out
loud, and it is the most defensible thing this lane produced.

⚠ **The corollary is uncomfortable and should be stated first in any pitch.** If we build
the pipeline and it works, its output on the binding family is *"you need more rounds than
you thought."* A cheaper hash is a possible side effect of better allocation (below), never
the headline.

### What survives — four forms, labelled (A)–(D)

Four forms survive, labelled (A)–(D). Each is weaker in ambition and stronger in
evidence than the LEVEL claim it replaces.

**⚑ (A) THE ALLOCATION FORM — supported, and GSR is the proof.** At t=24, GSR absorbs
`1 + (t−2k) = 23` rounds at k=1, of which **22 are partial — 96% of the entire
partial-round budget.** One partial round survives. Poseidon at t=24 pays for 23 partial
rounds and gets one round of resistance to this family from them. Computing the line does
not tell you to ship fewer rounds; **it tells you which rounds are buying nothing.**

**⚑⚑ (B) THE AXIS FORM — supported, and this is the real finding.** The gap between GSR
and full Poseidon is **exactly 3 rounds, and all three are initial-full rounds**:
31 − 28 = Rf0 − 1, and 31 = 4 + 23 + 4 pins the deployed schedule at Rf0=Rf1=4, Rp=23.
100% of Rp and 100% of Rf1 are inside the attack. The attack is blocked by, and only by,
`Rf0 ≥ 2` — because §5.3's backward linearization pushes the *known* value `S_in[j]=0`
forward through exactly **one** `x^α`; with Rf0 ≥ 2 the other input coordinates are free
and the state entering the partial layer is no longer affine in X1, so the gadget does not
compose.

Now the provenance of the parameter that saves it. **R_F = 8 was derived against
statistical attacks, not algebraic ones.** The parameter Poseidon derived *algebraically*
— R_P, the one that carries the designers' algebraic margin — is the one GSR eats whole.
**The design survives its most advanced algebraic attack because of a budget line
provisioned for differential cryptanalysis.** That is an accidental defense. Nobody knew
until 2026 that `Rf0 ≥ 2` was load-bearing for algebraic security, and no amount of
margin on R_P would have found it, because *margin on the wrong axis is not security, it
is cost*.

So the honest pitch is not "we ship fewer rounds." It is:

> **Everyone provisions rounds against guesswork — and the guess is not merely imprecise,
> it is aimed at the wrong axis.** A computed line tells you *which axis is load-bearing*.

⚠ **The brief's "nobody in the AO-hash space is pressing this" is REFUTED — see §8 C2.**
They are pressing it, and Perrin says so on a slide: *"security arguments based on D_I are
the future!"* What is absent is narrower — the feasibility-region formulation, regime
labels that travel, and machine checking. Do not make the broad claim.

### ⚑⚑ (C) THE VALUE FUNCTION IS KINKED — and that is the whole finding

At first the two lanes' results look opposed. This lane: *at t=24, 22 of 23 partial rounds
buy zero.* The sibling lane: *beyond R_P=15, every additional partial round buys one round
of margin at ~0.7% each — the cheapest margin in the repo.*

Both are right, and reconciling them produces the result the brief was actually reaching
for. **The value of a partial round is piecewise, with a kink at the absorption threshold
`R_P = t − 2k`** (`computed_line.py` §10):

```
bits bought by R_P  =  0                                if R_P ≤ t − 2k
                    =  2^k · (R_P − (t−2k)) · log₂ α    if R_P > t − 2k
```

**⚑ A multiplicative margin rule is blind to a kink BY CONSTRUCTION.** A percentage of a
quantity cannot see a threshold in that quantity's *value*. And the blindness is not
hypothetical — it is measured, on our own hash:

| instance | kink `t−2k` | deployed R_P | position | what "+7.5% R_P" buys |
|---|---|---|---|---|
| Poseidon KoalaBear t=24 | 22 | 23 | above by **1** | 1.0 useful round |
| **our Poseidon2 BabyBear t=16** | 14 | **13** | ⚑ **BELOW** | **0.0 — nothing** |
| **our Poseidon2 BabyBear t=24 sponge** | 22 | **21** | ⚑ **BELOW** | **0.0 — nothing** |

**Every one of our deployed partial rounds — 13 at w16, 21 at the w24 sponge — buys zero
against this family.** No percentage margin could ever have found that.

### ⚑⚑⚑ (D) THE LEVEL CLAIM'S REPLACEMENT: same budget, 48× the margin

⚑ **And this is not an exotic move — it is the designers' own optimization.** Poseidon
§4 *"Minimize Number of S-Boxes"*, verbatim: *"the goal is to find the best ratio between
R_P and R_F that minimizes **number of S-Boxes = t · R_F + R_P**."* **They already solve
the allocation problem. Our contribution is not a method — it is a NEW CONSTRAINT (the
kink) in an optimization they run themselves.** And the objective function below is theirs,
not ours.

Once the kink is computed, the two axes have *different shapes* and the allocation problem
becomes arithmetic (`computed_line.py` §11):

- **`R_f0` is a BINARY STRUCTURAL GATE.** GSR §5.3's backward step crosses exactly one full
  round, so `R_f0 ≥ 2` blocks the family outright. Rounds beyond the gate are
  unknown-attack margin at `t` S-boxes each.
- **`R_P` is LINEAR ABOVE THE KINK**, at 1 S-box each.

Poseidon KoalaBear t=24, α=3. Objective `t·R_F + R_P` held at **215**. Poseidon's own
statistical floor is `R_F ≥ 6`; GSR's structural gate is `R_f0 ≥ 2` i.e. `R_F ≥ 4`; and
`R_f0 = R_f1` so `R_F` is even (GSR footnote 2).

| R_F | R_f0 | R_P | `t·R_F+R_P` | rounds above the GSR kink | gate margin `R_f0−2` | |
|---|---|---|---|---|---|---|
| 8 | 4 | 23 | 215 | **1** | 2 | ← **DEPLOYED** |
| 6 | 3 | 71 | 215 | **49** | 1 | ← statistical floor |
| 4 | 2 | 119 | 215 | 97 | 0 | ← below the statistical floor |

**⚑ THE TRADE, AS A RATIO.** Poseidon's *arbitrary* `+2 R_F` costs `2t = 48` S-boxes and
buys **one** extra round of margin on the GSR gate axis. The same 48 S-boxes spent on `R_P`
buy **48** rounds of margin above the kink.

```
48 S-boxes  →   1 round of gate margin    (what was bought)
48 S-boxes  →  48 rounds of kink margin   (what they buy)
```

**Ratio 48 : 1.** And the third-party confirmation that `R_F = 8` is exactly `6 + margin`
is explicit — eprint 2026/967 §2.1: *"The final recommended parameters also include a
security margin: two additional external full rounds and 7.5% more internal partial rounds.
**This raises r_F = 6 to r_F = 8.**"*

**That is the thesis, correctly stated. Not "ship at the line and pay less" — "spend the
same and stop buying the flat part of the curve."**

⚠ **The honest counter, and it is real.** The `+2 R_F` is unknown-attack insurance on
*exactly* the axis GSR §5.3 attacks. Spending all of it is the wrong lesson if the next
paper extends the backward step past one full round — which the sibling lane names as *"the
thing to watch"*, and which instance 5 shows the ecosystem already doing. `R_F = 6` keeps
**one** round of gate margin, not zero.

⚠ **Priced against one family.** `R_P` is also priced by A4 (CheapLunch, ideal degree
`≤ α^(k·R_F+R_P)`) and by Ashur et al.'s corrected Gröbner conditions; `R_f0` by nothing
computable. This is a **demonstration of the method** on the family we hold in closed form,
**not a recommendation to reparameterize Poseidon.** See open item 2.

---

## 1. The four claims, separated, so none of them can borrow the others' evidence

| claim | status | evidence |
|---|---|---|
| **LEVEL**: compute the line → ship *fewer* rounds | ⚑ **REFUTED** | GSR at t=24: 1.6–2.9× outward · integral: 4.8× · our own Poseidon2: 1.15× · Ashur et al. 2023/537: 1.6× · Poseidon initiative *already raised* R_F after 2026/306 · resultants 2025/259 broke Rescue-512 and put Griffin/Arion/Anemoi below claim. **Six instances, same direction, none opposed.** |
| **ALLOCATION**: compute the line → stop paying for rounds that buy nothing | **SUPPORTED** | 96% of Poseidon t=24's partial budget absorbed; **100%** of ours, at both widths |
| **AXIS**: compute the line → learn which parameter is load-bearing | **SUPPORTED** | Poseidon t=24 is saved by R_F (statistically derived), not R_P (algebraically derived); the deployed margin defends by accident |
| ⚑ **BUDGET**: compute the line → same cost, far more margin | **SUPPORTED, and it is the one to pitch** | 1 → 25 rounds above the kink at identical S-box budget; the kink is invisible to every multiplicative margin rule in the literature |

The LEVEL claim should not be made again in this repo, and if it appears in a pitch it
should be cut. **BUDGET is its replacement and it is a stronger claim, because "more
security for the same money" survives a cryptanalytic surprise and "less money" does not.**

---

*(§2 attack-family table, §3 composition rule, §4 gadget-Feistel end-to-end, §5 the Lean
scope — below.)*

---

## 2. The attack-family table, with computability marked

The brief said the honest shape of this table is the deliverable even if the thesis
fails. The thesis did partly fail, and this is still the deliverable.

Three marks, and the distinction between the first two is the one that decides
everything:

- **EXACT-ATTACK** — a closed form or terminating computation giving *how far the
  attack reaches* at fixed parameters. Cheap, sharp, and it moves the line **outward**
  when it disagrees with the heuristic.
- **EXACT-DEFENSE** — a terminating computation giving *a ceiling no attack in the
  family can pass*. Rare. This is the only mark that lets you ship at a line rather
  than behind one.
- **HEURISTIC** / **OPEN** — an estimate, or nothing.

| # | family | governing quantity | mark | cost to compute | held? |
|---|---|---|---|---|---|
| A1 | round skipping (Bariant et al.) | skipped S-boxes `2t−k` | **EXACT-ATTACK** (closed form, and it is the papers' own stated maximum) | instant | ✅ |
| A2 | **S-box skipping / GSR** | absorbed rounds `1+(t−2k)`; residual degree `α^(Rp+Rf1−t+2k)`; **applicability** = `dim Krylov(M_I,e₀) ≥ t−2k` | **EXACT-ATTACK**, and the applicability test is exact linear algebra | instant | ✅ reproduced, guard passes; Krylov computed by sibling lane |
| A3 | **DoF ceiling on A1–A2** | `1+(t−k)` absorbed rounds | ⚑ **EXACT-DEFENSE** | instant | ✅ derived here |
| A4 | FreeLunch / CheapLunch | ideal degree (system is already a Gröbner basis) | **EXACT-ATTACK** (closed-form upper bound) | instant | partial |
| A5 | generic Gröbner / CICO | degree of regularity, solving degree | ⚠ **HEURISTIC, and its best replacement is CONJECTURED** — see below | — | rule verified at source |
| A6 | resultants / univariate root-finding | degree of the resultant; Cantor–Zassenhaus `O(d² log p)` | **EXACT-ATTACK** | instant | ✅ (it is GSR's own solver) |
| S1 | differential | max characteristic probability | **HEURISTIC**; the wide-trail *bound* is EXACT-DEFENSE but loose | — | — |
| S2 | branch number (the S1 defense) | `branch(M)`, via the `branch(M)=branch(M⁻¹)` duality | ⚑ **EXACT-DEFENSE**, self-certifying | minutes | ✅ four-pass exhaustion |
| S3 | linear | as S1 | as S1 | — | — |
| S4 | **integral / division property, char p** | last round carrying a mod-p² property | ⚑ **EXACT-ATTACK** (terminating propagation) | minutes, sage | ✅ **executed**, guarded |
| T1 | invariant subspaces (linear layer) | minimal polynomial / rational canonical form | ⚑ **EXACT-DEFENSE** | instant | ✅ gate exists |
| T2 | **invariant quotients** | existence of an autonomous quotient | **EXACT-DEFENSE** *in principle* — ⚠ **our own gate missed one and it killed Weft**; the script's loop skipped the level | instant | ✅ gate amended (§7d) |
| T3 | subspace trails | longest trail; for the *linear layer* the invariant-subspace test is exact | **HEURISTIC** in general — but ⚑ **exact where it matters: `dim Krylov < t` ⟺ invariant subspace exists, and that is the complement of A2's applicability. See §3's pincer.** | instant for the linear part | ✅ via A2's Krylov computation |
| T4 | subfield / Galois families | `σ(c) ≠ c` on every coefficient and constant | ⚑ **EXACT-DEFENSE**, **cost zero** | instant | ✅ |
| M1 | meet-in-the-middle / boomerang | — | **OPEN** | — | ❌ |
| M2 | carry / additive differentials (gadget designs) | carry-free probability | **EXACT-ATTACK** in the order-1 case; **OPEN** at order ≥ 2 | fast | order-1 only |
| U | **unknown attacks** | — | ⚑ **NOT COMPUTABLE BY CONSTRUCTION** | — | this is what the margin is for |

**Read the marks column, not the rows.** Of seventeen entries, **five are EXACT-DEFENSE**
(A3, S2, T1, T2, T4) and they are the only ones that can carry a "ship at the line"
argument. Four more are EXACT-ATTACK, which tells you where you *must not* be but never
where you may stop. **The single most load-bearing family in AO design — A5, generic
Gröbner — is the one with no computable bound in either direction**, and that is not an
accident of our effort: it is Perrin's point.

### ⚑ A5 in detail — the binding family's best bound is in the CONJECTURED regime

Perrin, eprint 2024/605 (`~/paperbin/xhash-security-perrin-2024-605.txt`), abstract,
verbatim — note the typo is his:

> *"For algebraic attack relying on the computation and exploitation of a Gröbner basis, our
> survey of the literature suggests to base a security argument on **the complexity of the
> variable elimination step rather than that of the computation of the Gröbner basis
> itself.** Indeed, it turns out that **the latter complexity is hard to estimate—and is
> sometimes litteraly non-existent.**"*

That is the methodological rule the brief carried, and it holds at source. **But read the
next clause**, which the brief did not carry and which is the more important half:

> *"we propose a generalization of the "FreeLunch" approach which, **under a reasonable
> conjecture about the behaviour of the degree of polynomial ideals of dimension 0**, is
> sufficient for us to argue that both XHash8 and XHash12 are safe against such attacks."*

**So even the repaired route is CONJECTURAL, and its author says so in the abstract.** The
binding family in AO design has: no defense-side bound, a known-unreliable attack-side
estimate, and a best-available replacement that is explicitly a conjecture validated
"at least experimentally."

⚑ **This is where our regime discipline earns its keep and the literature's does not.** Our
calculator already refuses to conflate *proven / conjectured / withdrawn*, and
`cbr_not_reportable` is a theorem. A "ship at the computed line" argument whose binding leg
is conjectural is honest **only if the regime travels with the number.** Every mark in the
table above exists for that reason, and A5's mark is the one that decides whether the whole
argument may be made at all.

⚠ **T2 is the entry to distrust.** It is marked EXACT-DEFENSE and our own instance of it
was *vacuously green* — the loop skipped the level at which the autonomous quotient
lived, and branch number provably could not see the property that broke Weft. A
decidable check that is not actually deciding the thing it names is worse than an
admitted heuristic. That is why the amended design gate (`swarm/BRIEF-TEMPLATE.md` §7d)
runs structure / quotient / subfield / minpoly **before** branch.

---

## 3. The composition rule — and it is not `max` over families

The naive rule everyone writes is

> `R = max_f R_f + margin`

**That rule cannot express what GSR does, and a design provisioned by it would have
missed the attack entirely.** GSR's constraint is not on `R`. It is on `Rf0`. A design
with `R = 31` and `Rf0 = 1` is broken; a design with `R = 28` and `Rf0 = 4` is not. The
scalar `R` does not separate them.

**⚑ THE CORRECTED RULE.** Each family `f` defines an **infeasibility region** `I_f` in the
full parameter vector — `(t, α, τ, Rf0, Rp, Rf1, B, K, P, …)`, whatever the design's
shape variables are. The provisioning obligation is

> **the design point must lie outside `⋃_f I_f`, and the margin is a distance from the
> boundary of that union measured in the directions the union is not known to bound.**

A round count is the projection of that region onto one axis. **The projection loses the
constraint whenever a family binds on shape rather than level** — and A2 binds on shape.
So "add 7.5% more partial rounds" is not merely an imprecise operation; against GSR it is
the *wrong* operation, and 7.5% of 23 is 1.7 rounds against an attack that eats 22.

### ⚑⚑ The pincer — where the region formulation earns its keep, and `max` cannot follow

The sibling lane computed the following on our **deployed** constants
(`gsr-poseidon-2026-1692.md` §1c, script `krylov.py`), and it is the sharpest object either
lane produced:

```
dim Krylov(M_I, e₀) = t   ⟹  GSR's t−2k constraints are INDEPENDENT  ⟹  the gadget applies in full
dim Krylov(M_I, e₀) < t   ⟹  M_I has a nontrivial invariant subspace ⟹  broken by SUBSPACE TRAILS
```

and Poseidon2's own design criterion — Grassi–Rechberger–Schofnegger, ToSC 2021, *"Proving
resistance against infinitely long subspace trails: How to choose the linear layer"*, which
is GSR's own reference [14] — **requires** no nontrivial invariant subspace, i.e. requires
full Krylov. CheapLunch reaches the same identity from the other side.

> **`I_{A2} ∪ I_{T3}` covers the entire Krylov axis. No linear layer defeats both.** The
> sibling lane's words: *"There is no matrix that fixes this."*

**This is why the rule has to be regions and not a max.** Under `R = max_f R_f + margin`
you take a max and ship, and you *never learn that an axis is exhausted* — there is no max
to take, because neither family is about `R`. Under the region formulation the union is
computable and the conclusion "**this axis is closed, pay on a different one**" falls out
mechanically. A designer who computed this would not have gone looking for a better matrix;
a designer who did not, will.

⚠ And note what it does to a hopeful reading: Krylov dimension *looks* like a free design
lever — an EXACT, cheap linear-algebra check you could design against. **It is a trap, not a
lever.** Checking cost us one script; asserting it would have cost a design cycle.

### What the margin is FOR, once the families are computed — the distinction nobody states

A heuristic designer's margin is doing **two jobs at once** and is honest about neither:

1. **known-attack slack** — "my estimate of where Gröbner dies could be off by a bit"
2. **unknown-attack risk** — "someone will invent something"

Compute the EXACT-ATTACK families and **job 1 goes to zero for those families**. It does
*not* go to zero for A5, S1, S3, T3, M1 — and those remain, so a margin remains. But the
margin's *purpose* becomes statable:

> **The margin is a bet on the rate at which new attack families appear, priced against
> the cost of a round. It is not slack against known attacks, and it must never be
> quoted as though it were.**

This matters because the two jobs want opposite behaviours. Slack against a known attack
should be spent on the axis that attack occupies. Insurance against unknown attacks
should be spent where it is *cheapest per round*, because you have no information about
direction — which in Poseidon-like designs means partial rounds. **Poseidon's `+7.5% R_P`
is a defensible unknown-attack margin and an indefensible known-attack margin, and it is
described as neither.**

To Poseidon's credit, the framing *is* unknown-attack — *"given the minimum number of
rounds necessary to provide security against all attacks known in the literature"*. The
defect is not the intent; it is that a **multiplicative** margin is the wrong instrument for
insurance against attacks whose value functions have thresholds, and that the "minimum
number of rounds against all known attacks" it sits on top of has since been corrected
outward at least four times.

⚠ **And the stated margin is not even stable within one spec.** Poseidon2 (eprint 2023/323)
says **7.5%** in §3.2 — consistent with the `1.075` factor in its own Eq. (1) — and
**12.5%** in §7.3, where the larger figure is used to argue that the Bariant et al.
round-skip is absorbed. **A margin quoted at two different values in one document, with the
flattering one deployed in the argument that a known attack is survivable, is the
`⚑ HONEST LABEL HIDES MEDIOCRITY` pattern in its native habitat.** Flagged here; not our
spec to fix.

⚑ And the corollary that decides our own design work: **when a family is EXACT-DEFENSE
(A3, S2, T1, T4), the margin against that family is legitimately ZERO.** That is the
entire cash value of the thesis, and it is worth exactly as much as the EXACT-DEFENSE
column is long — which today is five rows, none of which is the binding one.

---

## 4. The gadget-Feistel, end to end — and the verdict is uncomfortable

The brief asked what the computed line says NR should be for the ring-hash front-runner
(92,257 constraints, NR=16, which our own note calls *"precedent, not attack-tested"*).
Answer, family by family. Design: `R_q = Z_q[X]/(X^16+1)`, `q ≈ 2^64`, state
`(L,R) ∈ R_q^4 × R_q^4`, base `B = 2^16`, `K = 4` planes, `P = 2` adjacent-plane products
`Z_{i,0}=Y_0Y_1`, `Z_{i,1}=Y_1Y_2`, `F_r` public dense linear in planes and products.

### A1–A4, the skip family: **absorbs at most ONE round.** Computed, and this is a win.

The GSR analogue *exists*: because `P=2`'s two products share `Y_{i,1}`, fixing that one
plane makes `Z_{i,0}=δY_{i,0}` and `Z_{i,1}=δY_{i,2}` — **one plane linearizes the whole
round's nonlinearity**, cheaper per round than Poseidon's one-δ-per-S-box.

**But it does not chain, and the reason is exact.** GSR chains because fixing an S-box
input makes its *output a constant*, so the state map becomes affine **in the state
variables**, and affine composes with affine — [GSR] §5.2 says this in as many words:
*"Because the mapping is affine, every state S^(r) with 1 ≤ r ≤ t−2k remains an affine
combination of the variables in X1."* That sentence is the entire attack.

Here, fixing `Y_{i,1}` makes `F_r` affine **in the plane variables of round r**. Round
r+1's plane variables are `digits_B(R_{r+1} + a)`, and **digit extraction of an affine
function of digits is not affine** — measured constructively, `digit_0(u+v) ≠
digit_0(u)+digit_0(v)` in **1019/2000** random plane pairs (`computed_line.py` §8). The
linearization is per-round and dies at the boundary.

> ⚑ **The family that just ate 23 of Poseidon-t=24's 31 rounds absorbs exactly 1 round of
> the gadget-Feistel, and the property that stops it — base-B decomposition not commuting
> with affine maps — is the design's defining feature, not a tuned parameter.** This is the
> SELECTION form of the thesis working, and it is the strongest result in the note.

### A5–A6, generic Gröbner and resultants: **the instrument does not apply, in either direction.**

The degree-2 count above is only valid with the planes as *free* variables. The real
primitive pins them: `Y` are the base-B digits of `R_i + a_{r,i}`, a relation whose
vanishing ideal has degree `B = 2^16` per plane and **no low-degree expression over F_q at
all**. So the attacker's low-degree system has ~`2^(16·planes)` spurious solutions and the
solving cost is not the root-finding cost.

**Neither a bound nor a refutation is computable by the degree machinery.** That is not a
gap in our effort; it is a property of the design.

### S2 branch / T1 minpoly / T4 subfield: **not applicable — there is no MDS and no σ-layer.**

Diffusion is measured, not bounded: one flipped input slot reaches 33.0/64 active slots
after 1 round and 64.0/64 after 2 (`design_gadget_feistel.py` §3). **Measured full
diffusion in 2 rounds.** That is an EXACT-ATTACK-style datum, not a defense.

### M2 carry/additive differentials: **order 1 computed and dead; order 2 OPEN and live.**

`P ≥ 1` is a hard requirement — at `P=0` a fixed input difference maps to a fixed output
difference through all 16 rounds (40/40). At `P=2` the order-1 differential is dead
(0/40 at every round count). **But the second derivative of a single round function `F` is
state-independent up to carries — constant in 40/40.** Meet-in-the-middle / boomerang from
both ends is the named first attack-me item, and it is **M1: OPEN**.

### ⚑ THE VERDICT: the pipeline CANNOT set NR, and NR=16 remains precedent

| leg | says | mark |
|---|---|---|
| skip family (A1–A4) | NR ≥ 2 | EXACT-ATTACK |
| diffusion | NR ≥ 2 (measured) | measured |
| generic algebraic (A5) | **no statement possible** | N/A by construction |
| order-1 additive differential (M2) | NR ≥ small | EXACT-ATTACK |
| **order-2 / MITM / boomerang (M1, M2)** | ⚑ **binding, and OPEN** | **OPEN** |
| composition | **max = OPEN** | |

**Every leg the pipeline can compute is satisfied at NR ≈ 2–3. The binding leg is the one
it cannot compute. So the computed line does not justify NR=16, and it does not refute it
either — it says nothing.** NR=16 is still the HKT 14-round indifferentiability precedent
for 2-branch Feistel *with ideal round functions*, plus margin, and nothing about `F` is an
ideal round function.

⚠ **Do not read the A1–A4 immunity as clearance.** The same non-polynomiality that blocks
the skip family blocks the pipeline. **The gadget-Feistel is structurally immune to the
algebraic family AND structurally opaque to the algebraic instrument, and those are the
same fact.**

### ⚑ The consequence the lane should actually act on

**If we believe the thesis, it argues against the current front-runner.** A design whose
round count the pipeline can price (σ-Poseidon: A2/A3/A4/S2/S4/T1/T4 all apply, and S4 is
already executed at our parameters) is worth more to a "we compute where the line is"
position than one that is 26× cheaper and unpriceable. That is a genuine design fork —
CLAUDE.md's category 4, taste — and it belongs to ember. The lane's job was to make the
fork visible, and it is: **27.4 rows/elt with an OPEN binding leg, versus 143.8 rows/elt
with every leg computed but one.** In whole-circuit terms that is Fiat–Shamir at **4.0%
versus 11.9%** (`ring-hash-build-verdict.md`), so the question is whether **7.9 points of
circuit** is the price of an argument.

And the cost of *being wrong about NR* is small enough that there is no excuse for leaving
it open. Each round is 6.2% of the permutation, so NR 16 → 18 moves the 92,257-constraint
Fiat–Shamir bill by ~12.5% — which, at FS = 4.0% of the whole circuit, is **~0.5% of the
circuit.** **The round count is not where this candidate's cost is decided. M1 must not be
deferred on cost grounds, because there are no cost grounds.**

---

## 5. What is machine-checkable — scoped down, deliberately

The brief warned against overreaching toward Lean where computation is the right
instrument, and that warning is correct: **an exhaustively-computed bound with a
falsification guard is already stronger than this literature's norm.** GSR's own Table 1
is not machine-checked and neither is Poseidon's round derivation.

So the scope is small on purpose.

| object | Lean-reachable? | why |
|---|---|---|
| **A3, the DoF ceiling `absorbed ≤ 1 + (t−k)`** | ⚑ **YES — and it is still the one worth doing** | pure counting over a finite index set; no field arithmetic, no `Poseidon2` perm, no reduction bomb. It is a theorem about **attacks not yet written**. ⚠ The *bound* is GKR's (§8 C3), which makes it a better Lean target, not a worse one: formalizing a published DoF-counting argument is a contribution; formalizing our own restatement of it would have been a twin. |
| **S2, branch numbers** | **YES** | already exhaustive and self-certifying via `branch(M)=branch(M⁻¹)`; the four-pass exhaustion is a finite check a `decide` can carry |
| **T1/T4, minpoly irreducibility and `σ(c) ≠ c`** | **YES, cheap** | finite predicates over the deployed constants; `#assert_axioms`-clean |
| **T2, invariant quotients** | **YES, and it should be** — our gate was vacuously green once | a decidable predicate stated as a named theorem cannot skip a level the way a Python loop did |
| S4, integral / division property | **NO — computation is right** | the propagation is a large finite search over a mod-p² lattice; Lean buys nothing and `native_decide` through the deployed hash is a **reduction bomb** (one Poseidon2 perm = 47.6 GB / 68 min) |
| A2/A6, GSR reach and CZ cost | **NO** | closed-form arithmetic already; a Lean restatement adds a name and no assurance |
| A5, Gröbner complexity | **NO, and never** | there is no bound to check; Perrin's rule says the object is sometimes literally non-existent |
| M1/M2 order ≥ 2 | **NO** | there is no statement yet |

**⚑ The one recommendation: A3 in Lean.** `absorbed_rounds ≤ 1 + (t − k)` is a finite
counting statement about a named attack family, it is the only EXACT-DEFENSE bound in the
table that is *binding* on an algebraic family, and a machine-checked version is a real
object — a theorem that constrains future papers. Everything else on the YES list is a
ratchet on gates we already run and got wrong once (T2).

And the discipline that makes any of it worth having, which we already hold and the
literature does not: **the regime separation.** `cbr_not_reportable` is a theorem; the
calculator refuses to conflate proven / conjectured / withdrawn. A "ship at the line"
argument is only honest if the line's regime travels with it — and every row of §2's table
carries its mark for exactly that reason.

---

## 6. Open items, named

1. ⚑ **M1 for the gadget-Feistel** (order-2 / MITM / boomerang). The binding leg. Nothing
   in this note touches it and NR=16 rests on it.
2. ⚑ **A4 + the corrected Gröbner conditions must be intersected with A2 before the 48:1
   ratio is quoted outward.** CheapLunch's ideal-degree bound `α^(k·R_F+R_P)` and Ashur
   et al.'s **three** (not two) corrected conditions — now in 2019/458's current Eq. (4) —
   both price `R_P`, and the `R_F=6, R_P=71` point has not been checked against them.
   **The 48:1 figure is a demonstration that the method finds things, not a verified
   design point.** This is the one place in the note where the arithmetic outruns the
   verification, and it is named here so it cannot be quoted without the caveat.
3. **A3's k-round headroom.** The ceiling is `1+(t−k)`, GSR attains `1+(t−2k)`. Closing
   the gap needs the CICO input constraints satisfied without spending DoF. Nobody has;
   whether anybody can is open, and it is exactly the shape of the next paper.
4. **T2's vacuity.** The gate is amended but the amended gate has not been re-run
   adversarially against a design known to have an autonomous quotient.
5. **The Poseidon t=24 KoalaBear schedule has no single authoritative local source.**
   `R_F=8, R_P=23, sum 31` is assembled from three papers (2026/306 §5.3 for `R_P=23` and
   Table 1 for `R_F=8`; 2026/967 §2.1 for `6→8`; 2026/1692 for the sum and
   `R_f0=R_f1`). All three agree and GSR's own arithmetic `31−28 = R_f0−1` closes it, but
   **no spec document in the corpus states the pair.** If this number ever becomes
   load-bearing outward, get it from the Poseidon initiative directly.
6. ⚠ **Poseidon2's newer versions were not checked** — eprint returned HTTP 429. The local
   copy is dated 2024-02-08 and the 7.5%/12.5% discrepancy is read from that copy.

---

## 7. Provenance — what is measured, what is quoted, what is inferred

Per `feedback-a-brief-is-a-claim-and-lanes-execute-it`, every load-bearing claim tagged.

| claim | tag |
|---|---|
| GSR's degree and solver-cost formulas | **[read at source]** 2026/1692 §5.2, §5.3, §6.1, §7.1, §7.2 |
| our reproduction of GSR Table 1 (5/5 rows, ≤0.6 bits) | ⚑ **[measured]** `computed_line.py` §1 — falsification guard, passes |
| `31 = 4+23+4`, so `R_F=8, R_P=23` at t=24 | **[inferred, triangulated]** from GSR fn. 2 + 2026/306 + 2026/967; see open item 5 |
| *"we arbitrarily decided to add …+2 R_F …+7.5% R_P"* | **[read at source]** 2019/458 §5.4, both PDF versions |
| `R_F^stat ≥ 6`, R_F set by statistical attacks | **[read at source]** 2019/458 §5.5.1 |
| *"number of S-Boxes = t · R_F + R_P"* is the designers' objective | **[read at source]** 2019/458 §4 |
| *"This raises r_F = 6 to r_F = 8"* | **[read at source]** 2026/967 §2.1 |
| Ashur et al.: 35 partial rounds required where the designers' equation gives 22 | **[read at source]** 2023/537 §3.2 |
| Poseidon initiative *raised* external rounds after disclosure | **[read at source]** 2026/306 §6 |
| Poseidon2 margin stated as 7.5% (§3.2) and 12.5% (§7.3) | **[read at source]** 2023/323, 2024-02-08 copy |
| Poseidon2 §7.1 *"this is a pessimistic estimate"* (statistical leg) | **[read at source]** 2023/323 |
| τ=1→2, τ=2→24, τ=4→≥42 at base ~2^64 | ⚑ **[measured]** `integral_char_p_settling.sage`, guarded against 1/13/20 — ⚠ its fourth guard row is UNSOURCED, see §8 |
| integral dies at r≈5 under the degree heuristic | **[measured, prior lane]** `ring-hash-cryptanalysis.md` |
| `dim Krylov(M_I,e₀)` full on our deployed constants; the pincer | **[measured, SIBLING LANE]** `gsr-poseidon-2026-1692.md` §1c |
| our Poseidon2 repair `R_P 13→15`, +1.4% | **[computed, SIBLING LANE]** same note |
| the kink `R_P = t−2k` and its value function | ⚑ **[derived here]** from GSR's closed form; reconciles the two lanes |
| the 48:1 allocation ratio | ⚑ **[computed here, UNVERIFIED against A4]** — open item 2 |
| the DoF round ceiling `1+(t−k)` | ⚠ **[PUBLISHED — GKR 2025/954 §5.1]**, corrected in §8 C3; only the *k-round headroom against GSR* is ours |
| skip family absorbs ≤1 round of the gadget-Feistel | ⚑ **[derived here + measured]** `computed_line.py` §8, 1019/2000 |
| "the sign of the error is predicted by the instrument" | ⚑ **[inferred here]** from the five instances + the two verbatim direction-words |
| Perrin's elimination-step rule + *"sometimes litteraly non-existent"* | **[read at source]** 2024/605 abstract |
| Perrin's replacement bound rests on *"a reasonable conjecture"* | ⚑ **[read at source]** 2024/605 abstract — the brief carried the first half of this sentence, not the second |

**One item not chased**: CheapLunch's exact statement of the Poseidon ideal-degree bound
(`α^(k·R_F+R_P)`) is carried in §2 from the brief and marked *partial* in the held column. A
second citation lane was running against it; fold its result in before §2 is quoted
outward. Nothing else in this note rests on a claim I did not open.

---

## 8. Corrections — three, and one of them narrows the thesis

A second citation lane swept the seven attack families against `~/paperbin` and the full
IACR mirror. It returned three corrections **to this note and to the repo**, and they are
worth more than the additions.

### ⚑⚑ C1. "21–22 at degree 8" is not in Beyne–Verbauwhede, and it is inside a falsification guard

`eprint 2025/932` uses **exactly three fields**: `2^64−2^32+1` (e=1), `(2^31−2^24+1)²`
(e=2), `(2^17−1)⁴` (e=4). **There is no degree-8 extension anywhere in the paper and no
published "21".** The 21/22 that the number was taken from are **column headers in the
divisibility-by-`p` block** of Table 3 — a *different quantity*, whose last rounds are
24/24/26.

The claim is currently load-bearing in four places:

| file | what it says |
|---|---|
| `ring-hash-cryptanalysis.md:186` | *"20 at degree 4, 21–22 at degree 8"* |
| `ring-hash-design.md:618` | table row `degree-8 extension \| 21–22` |
| `ring-hash-tau-verdict.md:43` | *"reproduces the paper's 1/13/20/21 exactly"* |
| `ring-hash-scripts/integral_char_p_settling.sage:183` | ⚑ **the guard itself** |

⚑ **The last one is the serious one.** Line 183 was
`report("deg-8 (2^8+1)^8 e=8 t=8", 2**8+1, 8, 8, 21)` — a row of the **falsification
guard** asserting an expected value the paper does not contain. **That row cannot go red
against the paper, because the paper says nothing about it.** It is a self-comparison
wearing a guard's clothes, and it reported `OK`, which is how "reproduces the paper's
1/13/20/21 **exactly**" got written. This is `minted-a-falsifier-that-stopped-falsifying`
and `feedback-a-documented-wound-is-not-a-detected-one` in one line of code.

**Fixed here, minimally and without deleting evidence**: the row is relabelled
`[UNSOURCED]`, the file header carries the correction, and Phase A's banner no longer says
"must be 1 / 13 / 20 / 21". **Rows 1–3 are genuine, are verified against the paper, and
pass — so the τ verdict and the τ=2 → 24 measurement stand.** Only the degree-8 figure
must stop being quoted. The other three files are other lanes' and are flagged, not edited.

### ⚑⚑ C2. "Nobody in the AO-hash space is pressing this" is REFUTED — they are, and they say so

This was in the brief and I repeated it. It is wrong. Perrin, EC'26/SPRING 2026 slides
(`~/paperbin/spring2026-perrin-slides.pdf`, slide 31, *"Potential directions for
hardening"*):

> *"**Ideal Degree** — The 'boring/fastest' step of PoSSo is the only with a reliable
> complexity. ⟹ **security arguments based on D_I are the future!**"*

That is our thesis, stated by the field, as a direction. And FreeLunch, CheapLunch and the
resultant line are all *executions* of it — every one of them relocates the security
argument onto the one quantity that can be bounded.

⚑ **The unifying fact the sweep found, which is better than the claim it refutes: the
elimination / root-finding leg is the ONLY step anybody can bound tightly, in every paper
in the family.** FreeLunch: *"we are able to tightly estimate the complexity of polyDet"*
but *"we do not have a clear estimate for matGen"*. Perrin: *"while the complexity of
GröbFind can only be upperbounded (while we would need a lower bound anyway), that of FGLM
is tight."* Everything upstream — GB computation, system generation, multiplication-matrix
construction — is heuristic or open, everywhere.

**So the honest positioning is narrower and still defensible.** Not *"nobody computes the
line"* — they do, and they have converged on which quantity to compute. What is absent is:

1. **the feasibility-region formulation** — the field computes a *quantity* (`D_I`) and
   turns it into a *round count*; nobody treats the result as a region over the whole
   parameter vector, which is why GSR's `R_f0` constraint has no home in anyone's
   provisioning rule (§3);
2. **regime labels that travel** — A4 is *"we conjecture that this bound is achieved"*,
   GKR's ideal degree is an explicit `Conjecture 1` with *"We leave the problem to prove it
   open for future work"*, Perrin's own bound is a conjecture, and all three get quoted
   downstream as if they were bounds;
3. **machine checking** — nobody does it, and §5 says we should do it in exactly one place.

**Rewrite the pitch accordingly. "Nobody is doing this" is false and a reviewer will say
so in one sentence.**

### ⚑ C3. The DoF round ceiling is NOT ours — Grassi–Koschatko–Rechberger published it

§0 and `computed_line.py` §9 present the DoF-counting ceiling as our derivation. **It is
published.** GKR, eprint **2025/954** (*Poseidon and Neptune: Gröbner Basis Cryptanalysis
Exploiting Subspace Trails*, ToSC 2025(2)), §5.1:

> *"an attacker can cover at most `0 ≤ t − (c + d) ≤ t − 2` rounds without exhausting the
> degrees of freedom necessary to solve the CICO problem."*

Same argument, different parameterization. **Our `1 + (t−k)` is the GSR-specific instance of
GKR's bound, not a new result, and the note must say so.** What remains genuinely ours is
narrow: the observation that GSR attains `1 + (t−2k)` against that ceiling, so **the residual
headroom for the family is exactly `k` rounds**, and that closing it requires satisfying the
CICO input constraints without spending DoF.

⚑ And GKR's subspace-trail construction is the same Krylov object the sibling lane
computed: `S^(ℓ) = ⟨e₀, e₀M, …, e₀M^{ℓ−1}⟩^⊥`, with *"the choice of the matrix M in
Poseidon, Poseidon2, and Neptune guarantees that dim(S^(ℓ)) = t − ℓ"*. **The pincer in §3
is visible in GKR's own algebra**; what the sibling lane added was computing it on our
deployed constants and naming the consequence.

---

## 9. Instance 6, and the additions that change marks in §2

**⚑ Instance 6 — resultants, eprint 2025/259** (Bariant, Boeuf, Briaud, Hostettler,
Øygarden, Raddum, *Improved Resultant Attack against Arithmetization-Oriented Primitives*):

> *"We show that most variants of Griffin, Arion and Anemoi **fail to reach the claimed
> security level.** For the first time, we successfully break a parameter set of Rescue,
> namely its 512-bit security variant."*

**Sixth instance, same direction.** And it is the *best-founded* bound in the whole family —
*"an efficient reduction procedure that we propose and **rigorously analyze**"*, with the one
assumption discharged per primitive (`c = 1` for Arion/Griffin/even-char Anemoi, `c = 2`
otherwise) and tightness **measured**: *"we observe that this upper bound is reached."*

### Mark changes to §2

| row | was | now | source |
|---|---|---|---|
| A6 resultants | EXACT-ATTACK | ⚑ **EXACT-ATTACK, rigorously analyzed** — the strongest-founded bound in the family | 2025/259 §3.1 |
| A4 CheapLunch | EXACT-ATTACK | **closed form, but `"We conjecture that this bound is achieved"`** — CONJECTURED regime; and *loose* for Griffin/ArionHash where assumptions are unverified | 2025/2040 §4.2, abstract |
| T1 invariant subspaces | EXACT-DEFENSE | ⚑ **SPLIT.** *Infinite* subspace trails of a P-SPN **linear layer**: DECIDABLE, iff, `O(t³)`, **measured at 4 ms (t=4) to 30 ms (t=16)** (GRS 2020/500 §5.1). *General* invariant subspaces of a round function: ⚑ **NO decision procedure — a stated open problem** (Leander–Minaud–Rønjom 2015/068 §7). All invariants of an unkeyed permutation: exact but `O(n·2^{2n})`, *"impractical for n = 64"* (Beyne 2018/763) | three papers |
| T2 invariant quotients | EXACT-DEFENSE in principle | ⚑ **AND THERE IS NO LITERATURE.** The sweep found **no paper on invariant quotient attacks** in either corpus. Our gate is our own construct with no external check — which is exactly how it came to be vacuously green | absence, stated with the instrument |
| T3 subspace trails | heuristic-except-Krylov | **EXACT construction**: `S^(ℓ)` is an orthogonal complement of a Krylov span, `O(t³)`, no search; max length `t−1` closed form. ⚠ but the ideal degree built on top is `Conjecture 1`, *"We leave the problem to prove it open"* | GKR 2025/954 §4.2, §5.1 |
| A1/A2 (new) | — | ⚑ **Khovratovich 2026 (informal, UNPUBLISHED)**: `b ≤ 4t/m` ⟹ **MDS kills 4-round skipping**; **3-round skipping OPEN**, *"No 3-round trail found yet"*, open ETH grant. This is why the Initiative moved to Poseidon1/KoalaBear | `spring2026-khovratovich-slides.pdf` sl. 7, 12 |

⚠ **T1's split is the one that matters for us.** We have been carrying "invariant subspaces:
EXACT-DEFENSE" as a single row. It is exact for the *linear layer* and **undecidable in
general** — and the Weft kill lived on the general side. The §2 mark was too generous and
is corrected above.

⚠ **And note the shape of the absence in T2**: no paper found, in a corpus that is
cryptology-only. Per `feedback` doctrine that is *"nothing listed"*, not *"nothing exists"*
— stated with the instrument, as required.
