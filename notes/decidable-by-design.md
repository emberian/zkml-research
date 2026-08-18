# Decidable by design — minimizing the assumed surface, and the two legs that will not collapse

2026-08-18. DESIGN-RESEARCH lane on a criterion nobody uses: **not "prove the hash secure"
(impossible for a compressing function) but MINIMIZE the surface that must be ASSUMED, and
choose structure so that what remains is DECIDABLE rather than ARGUED.** Successor-in-spirit
to `weft-c-spec.md` (Twill, where exactly two of seven legs stay argued),
`hash-ideation.md` (the eight constructions and the proposed regular-sequence gate item),
and `formal-cryptanalysis-pipeline.md` (the attack-family/computability table). Sibling
lanes live — this note references, does not duplicate.

**Substrate, said out loud**: nothing here authors a constraint. The computations are a
Python twin (sympy Gröbner over GF(p)); the two papers whose mechanisms decide the question
are read at source. If any construction sketched here ever becomes a circuit, the AIR is
Lean-authored.

Labels: `[MEASURED]` = script + log in this lane; `[READ]` = paper/file at source;
`[DERIVED]` = pencil derivation shown; `[ASSERTED-BY-<who>]` = carried, not re-derived.
Artifacts: `notes/decidable-scripts/` (this lane's — `dbd_ideal_degree.py`,
`dbd_freelunch_boundary.py`, `dbd_bobbin.py`, `dbd_density.py`); logs under
`/tmp/dbd-*.log`. Read at source: **FreeLunch, eprint 2024/347** §2.3, §3.1, §4.3 (the
`already-a-Gröbner-basis` mechanism and the full-inverse-layer limitation);
**Perrin, eprint 2024/605** abstract + his Spring-2026 slides (the `D_I` conclusion);
**resultants, eprint 2025/259** §5 (the closed-form ideal degrees and the breaks);
**Vaudenay, *Decorrelation: A Theory for Block Cipher Security*, J. Cryptol. 2003** §2–3,
§6 (what decorrelation bounds and what it needs).

---

## 0. VERDICT IN TEN LINES

1. **Neither argued leg collapses to "decidable" wholesale — but the Gröbner leg FACTORS,
   and the factorization is the result.** The decidable part is the **ideal degree `D_I`**;
   the argued part is (a) the exponent turning `D_I` into wall-clock cost and (b) the
   minimization over algebraic models. Perrin's own conclusion slide, verbatim `[READ]`:
   *"Ideal Degree: the 'boring/fastest' step of PoSSo is the only [one] with a reliable
   complexity ⟹ security arguments based on `D_I` are the future!"* This lane's contribution
   is to say *why* only `D_I` is decidable, and what it costs to lean on it. §1.
2. ⭐ **THE `x⁻¹` TENSION IS RESOLVED, AND THE RESOLUTION IS THAT IT WAS NEVER A TENSION.**
   *FreeLunch-modelable*, *Gröbner-decidable*, and *attackable-with-known-cost* are **one
   property**. *Un-modelable*, *non-decidable*, and *conjecturally-secure-but-unproven* are
   its **one** complement. There is no (decidable ∧ secure) corner via this route, because
   **the certificate of decidability is the attacker's input.** `x⁻¹` full-inverse layers
   are chosen precisely because they **refuse** decidability. §1c.
3. **[MEASURED]** A power-map CICO model (`yᵃ = x`) has pairwise-coprime **pure-power**
   leading monomials — it *is* a FreeLunch system, `D_I = ∏αᵢ` known by construction — for
   **both** sparse and full-inverse layers. Confirmed by explicit grevlex GB at t=2,R=2.
   **So "does a regular sequence exist / is `D_I` known by construction" is YES generically,
   and is therefore NOT the discriminator.** §1a.
4. ⭐ **[MEASURED]** The two *cheapest* S-boxes split on this axis. The **inversion** witness
   `x·y = 1` (deg 2, the cheapest cell) has **degree-2 product** leading terms `xᵢyᵢ` that
   **chain-collide across consecutive rounds** — it is **not** a free Gröbner basis and needs
   real Buchberger — while the **power-map** witness `yᵃ=x` is free. The cheap in-circuit
   form and the FreeLunch-modelable form are **different S-boxes**. §1b.
5. **The discriminator that actually moves security is the minimal-model VARIABLE COUNT**,
   set by the layer's sparsity: sparse-1-branch `D_I ≈ αᴿ`, full-inverse `D_I ≈ α^{tR}`
   `[DERIVED]`. Security is `min` over models; finding the minimal model is the
   encoding-discovery problem, and it is **not decidable** — the residual argued core. §1d.
6. ⚑ **Answer to "is regularity decidable at our sizes, or does it move the intractability?"
   BOTH, depending on who is asking.** Verifying regularity of *arbitrary* top-forms is a
   dimension computation = a grevlex Gröbner basis = **no cheaper than solving** (illusory
   collapse). Exhibiting a **constructive FreeLunch certificate** (coprime pure-power leading
   monomials) is **O(n²)** and sufficient — `[MEASURED]` **6–45× cheaper than the GB at
   n=4–6, ratio growing.** The collapse is real for a **designer** who constructs the
   certificate, illusory for an **auditor** who must verify an arbitrary design. §1e.
7. ⚠ **The trail→differential leg does NOT collapse, and decorrelation theory is why not.**
   `[READ]` Vaudenay's decorrelation bias bounds differential/linear distinguisher advantage
   **as an average over a uniformly random SECRET KEY**, via algebraic key injection
   (`NUT-II` is literally `k₁x+k₂`). A hash permutation is **keyless**; its round constants
   are **fixed and public**, not random and secret. **The averaging that makes the bound hold
   is unavailable, so the theory says nothing about a single fixed permutation.** The gap is
   not weak analysis — it is where keyless-ness bites. §2.
8. **The three observed mechanisms generalize into three predictive design rules** —
   saturation ⇒ *pick the maximal-degree extreme so the bounded quantity stops in O(1)
   steps*; finite lattice ⇒ *make the invariant family index over a tower so it is
   enumerable*; duality ⇒ *choose a component with a self-map that folds the search in half*.
   Each rule says which choice **buys decidability** and, per the fence, **what it hands the
   adversary.** §3.
9. **A decidability-primary construction is sketched (`SETT`)** and its costs to the
   adversary are named leg by leg. Its honest position: it makes **five of seven** legs
   decidable and is explicit that the **sixth (Gröbner) is decidable only as a per-model
   UPPER bound, never a floor**, and the **seventh (trail→differential) is irreducibly
   argued** for the keyless reason above. §4.
10. ⭐ **THE CEILING, AS A POSITIVE RESULT.** *"Designed to be information-theoretically
    safe"* has a precise meaning and it is **not** "IT-secure" (false). It is: **the
    assumption surface is exactly one object — an ideal permutation — and of the seven attack
    classes, five are decided by terminating computation, one is decidable only per-model
    (upper bound), and one is irreducibly argued, and here is the structural reason for each.**
    That statement is publishable and nobody has written it. §5.

---

## 1. THE GRÖBNER LEG — it factors; the decidable half is `D_I` and only `D_I`

### 1a. Both sparse and full designs are trivially FreeLunch under a power-map witness — so THAT is not the question

The ideation lane proposed (`hash-ideation.md` §0 claim 3) a **regular-sequence check on the
CICO ideal's top-degree parts**: if the top forms are a regular sequence, the Hilbert series
— and hence the degree of regularity and the F5 cost — is the complete-intersection one,
**known by construction (Macaulay bound), not estimated.** The move is exactly the one this
lane hunts. The first thing to establish is *how much it actually decides.*

A **FreeLunch system** (2024/347 Def 8, `[READ]`) is a sequence `P = {p₀,…,pₙ₋₁}` for which
some monomial order makes `LM≺(pᵢ) = xᵢ^{αᵢ}` — each leading monomial a **pure power of a
distinct variable.** Then (Prop 1 + Prop 4, `[READ]`) the leading monomials are pairwise
coprime, so `P` is **already a Gröbner basis**, the ideal is zero-dimensional, and its ideal
degree is `D_I = ∏αᵢ` **in closed form.** This is a *constructive* regular sequence: the
pure-power leading monomials `{xᵢ^{αᵢ}}` have no common projective zero, hence form a
regular sequence, and FreeLunch *exhibits the order* rather than proving regularity abstractly.

**[MEASURED]** (`dbd_ideal_degree.py`, `dbd_freelunch_boundary.py`) — model an iterated design's
CICO system with one fresh witness per S-box, S-box `= yᵃ` written as the degree-`a` relation
`yᵢᵃ = (previous state)ᵢ`:

| model | vars | S-box eqs | FreeLunch cert (coprime ∧ pure-power)? | grevlex GB (confirm) |
|---|---:|---:|:---:|---|
| **full inverse layer** t=2 R=2 (Rescue/RPO/XHash12/Twill shape) | 6 | 4 | **True** | 11 polys, structure confirmed |
| **sparse 1-branch** t=2 R=2 (Griffin/Arion/XHash8 shape) | 4 | 2 | **True** | 4 polys, structure confirmed |

Both shapes pass. **The existence of a constructive regular sequence / a known `D_I` is
generic for power-map designs and does not distinguish the secure from the broken.** The
naive per-S-box model always gives one, at ideal degree `α^{#S-boxes}`. That number is an
**upper bound on the cost of that one model**, not a security floor.

### 1b. ⭐ The two cheapest S-boxes split on the FreeLunch axis — measured

The above used `yᵃ = x` (a power-map / root witness). The **other** cheapest S-box, lane-wise
inversion, is normally written in-circuit as the degree-2 relation `x·y = 1` — the cheapest
committed cell there is (`hash-ideation.md` §2.3, claim 1). Its algebra is different:

**[MEASURED]** (`dbd_bobbin.py`) the CICO model with `sᵢ·yᵢ = 1` per lane, full MDS:

```
BOBBIN xy=1  t=2 R=2: coprime_LM=False pure_power=False
   sample S-box LMs: [ s0_0*y0_0,  s0_1*y0_1,  y0_0*y1_0,  y0_0*y1_1 ]
```

The leading monomials are **degree-2 products** `xᵢyᵢ`, not pure powers, and the round-2
equations — whose input `s⁽¹⁾ = M·y⁽⁰⁾ + c` is a dense linear form in the previous round's
witnesses — all carry the **same top variable** of that form (`y0_0` above), so they
**collide.** `x·y=1` is therefore **not** a FreeLunch system in Def-8's sense: it is a
Gröbner basis for its *own* generators only where they are coprime, and the chain across
rounds is not. It needs a real Buchberger run.

> ⭐ **The cheapest in-circuit S-box (`x·y=1`, one cell) and the FreeLunch-modelable S-box
> (`yᵃ=x`, pure power) are DIFFERENT S-boxes.** This sharpens `hash-ideation.md`'s claim 1
> (*"every cell you save hands the attacker a lower-degree model"*): the deg-2 inversion cell
> is *cheap* **and** *not directly FreeLunch-modelable* — those pull the same way here, not
> opposite ways. The attackable-because-cheap intuition is right for **power maps** and
> **wrong for inversion under a dense layer.** The variable that decides modelability is not
> the S-box's degree; it is whether its leading term is a **pure power of a fresh variable**
> (dominates, coprime) or a **product** (chains, collides).

⚠ **Scope and an honest correction of my own first pass.** I first proposed "a full MDS
destroys leading-term coprimality" as the clean mechanism. `dbd_density.py` refutes the clean
form: a *sparse* cyclic-shift linear layer still shows collisions (6/36 pairs at t=3,R=3
vs 12/36 for MDS) — because **any** iterated model with intermediate variables chains
consecutive rounds through shared state variables. Density changes the collision *count*, not
its existence. The correct statement is the pure-power one above (§1b), plus the
variable-count one below (§1d); "MDS density" is a contributing factor, not the mechanism.

### 1c. ⭐⭐ The `x⁻¹` tension resolved — modelable = decidable = attackable is ONE property

The brief flagged the sharpest question in the lane: `x⁻¹` is chosen *because* FreeLunch's
authors say they cannot model it — and **being unmodelable is the opposite of being
decidable.** Read at source, the two are not opposite; they are the same statement.

`[READ]` FreeLunch 2024/347 §4.3, verbatim: *"XHash12, RPO and Rescue-Prime all contain a
layer of inversion operations in **all** branches, and hence we cannot directly obtain a
FreeLunch from them."* XHash8 (inversion in **8 of 12** branches) *can* be modeled — *"by
adjusting for this minor difference, [we] directly define a FreeLunch system."* The boundary
is **sparse vs full inverse layer**, at source.

Put the three predicates side by side:

| predicate | sparse / power-map (Griffin, Arion, Anemoi, XHash8) | full inverse layer (RPO, XHash12, Rescue, Twill) |
|---|---|---|
| a cheap FreeLunch model (low `D_I`) exists | **YES** — constructed | **NO** — 2024/347 §4.3, at source |
| `D_I` decidable *and small* | **YES** | no small `D_I` known |
| best-known attack cost | **closed form** (2025/259) | conjectural / brute-force-bounded |
| **outcome** | ⚑ **Griffin, Arion, Anemoi variants, and Rescue-512 all fell in 2025/259** | conjecturally secure, **unproven** |

> ⭐ **The resolution.** *FreeLunch-modelable* ⟺ *a cheap regular-sequence certificate
> exists* ⟺ *`D_I` decidable and small* ⟺ *the design tends to be broken or tight*. Its
> negation — *full inverse layer* ⟺ *no cheap certificate* ⟺ *no decidable `D_I` floor* ⟺
> *conjecturally secure but unproven*. **There is no (decidable ∧ secure) corner via this
> route, because the certificate of decidability IS the attacker's input.** You cannot buy
> decidability of the Gröbner leg without buying the structure that is the attack. The brief's
> fence — *structure bought for analysis is structure an attacker can use* — is not a caution
> here; it is a **theorem-shaped statement about this specific leg.** `x⁻¹` full-inverse
> layers are the designs that **refuse** decidability on purpose, and 2025/259 is the record
> of what happens to the ones that accepted it.

⚠ **And say the un-flattering half.** *Un-modelable* is **not** *secure*; it is *un-analyzed*
(`hash-landscape.md` ADD.4's reframe, and 2024/347's own §5 *"Forcing the Presence of a
FreeLunch for Anemoi"* — a design that resisted the direct model was modeled anyway by
engineering a modified system). **Absence of a cheap certificate today is not proof one
cannot be forced tomorrow.** So the full-inverse side is not "decidably secure"; it is
"decidably **un**-attackable-by-the-current-technique," which is a strictly weaker and honest
claim.

### 1d. What actually moves security: the minimal-model variable count

Both sides have a decidable `D_I` for *some* model. What differs is the **minimal** model:

`[DERIVED, arithmetic]` (`dbd_run3.py`):

| design | minimal-model vars | `D_I` (naive) | log₂ `D_I` (α=3) |
|---|---:|---|---:|
| full inverse layer t=24 R=26 (Twill's parameters) | ≈ `t·R` = 624 | `α^{624}` | 989 |
| sparse 1-branch t=24 R=26 | ≈ `R` = 26 | `α^{26}` | 41 |

The sparse design's state is **algebraically slaved** to one nonlinear branch, so ≈`R`
variables capture it and the attackable `D_I` is small. The full inverse layer makes every
lane **independently** nonlinear, so ≈`t·R` variables survive and `D_I` is astronomical.
**Security is `min` over models**, and the encoding that finds the minimal model (Griffin's
"bypass," 2025/259's reduction) is the art of the attack. **Deciding whether a smaller model
exists is the encoding-discovery problem — no algorithm quantifies over all polynomial
encodings and monomial orders. That is the irreducible argued core, and it is exactly
Perrin's *"literally non-existent."*** `[READ]` 2024/605 abstract.

### 1e. Answer to the coordinator's Q1 — verifying vs. constructing regularity

> *Is regularity decidable at our sizes, or does it just move the intractability?*

**It moves the intractability iff you VERIFY it post-hoc; it is cheap iff you CONSTRUCT it.**
`n` homogeneous forms in `n` variables are a regular sequence ⟺ their only common projective
zero is empty ⟺ the quotient is zero-dimensional — and testing that is a **grevlex Gröbner
basis + a Hilbert-dimension read**, i.e. **the same computation as solving.** So the ideation
lane's gate item *"take the top forms and test regularity"*, read literally, **is a Gröbner
basis in disguise and saves nothing** on an arbitrary design.

What saves you is the **constructive certificate**: exhibit a monomial order under which the
leading monomials are pairwise-coprime pure powers. That is **O(n²)** — compare `n` leading
monomials — and it is a *sufficient* condition (Buchberger Prop 1). `[MEASURED]` the cert
check ran **6–45× faster than the actual GB at n=4–6, with the ratio growing** (0.0003 s vs
0.015 s at n=6). The correct gate item is therefore:

> **Not** *"is the CICO system a regular sequence?"* (a GB) **but** *"exhibit a FreeLunch
> order, or prove none exists."* Exhibiting one is cheap and yields `D_I = ∏αᵢ`; its
> **absence** is the interesting, hard, and security-relevant case — and it is where the
> full-inverse designs live.

For **Bobbin specifically** (`hash-ideation.md` §2.3, blocked-by-design on this gate item):
`[MEASURED]` its `x·y=1` model is **not** directly FreeLunch (§1b), so the gate item returns
*"no direct FreeLunch order under the `xy=1` witness."* That is the correct verdict and it is
**not** a green light — it says Bobbin sits on the un-modelable side with the full-inverse
designs, so its Gröbner security is **argued, not decided**, exactly like Twill's. Bobbin
should not be built as though the deg-2 cell bought it a decidable floor; it did not.

### 1f. `D_I` → cost: the residual exponent, and it is Perrin's open question

Even where `D_I` is decidable, the map from `D_I` to wall-clock cost carries an exponent that
is **not** a settled constant: FGLM is `O(n·D_I³)`; sparse-FGLM / Wiedemann is closer to
`D_I²`; the resultant + fast-multivariate-multiplication route of 2025/259 reaches
`≈ Õ(D_I)`. `[READ]` 2025/259 §5 computes Griffin's and Arion's final univariate degree in
closed form (*"= db·α^{r−b}·(2α+1)^{r−b}, which also corresponds to the ideal degree"*) and
**still** produces new breaks — because the improvement is in the **exponent**, not in `D_I`.
Perrin names this exactly on his last slide, `[READ]`: *"`D_I` vs `D_{2I}`?"* — the open
question of whether the reliable quantity is the ideal degree or a refinement.

> **So the Gröbner leg's decidable half is `D_I`; its argued half is the exponent `ω′` in
> `cost ≈ D_I^{ω′}`, `ω′ ∈ [1,3]`, being driven downward by better algorithms — plus the
> minimization over models (§1d), which is not bounded at all.** The argued part is not
> "literally non-existent" as it is for the raw degree of regularity; on a fixed FreeLunch
> model it is bounded on both sides (`1 ≤ ω′ ≤ 3`). **That is the collapse: from "estimate a
> quantity that sometimes does not exist" to "an exponent in a closed interval, on a system
> of known ideal degree." Partial, real, and it is the most that is available.**

---

## 2. THE TRAIL→DIFFERENTIAL LEG — decorrelation theory, read, and why it does not apply

The brief asked directly: decorrelation theory (Vaudenay) makes IT-flavoured claims about
distinguisher advantage — **does it apply, or why not?** Read at source, the answer is a clean
*no*, and the *why not* is structural and worth stating because it locates the gap.

`[READ]` Vaudenay 2003. The **`d`-wise decorrelation bias** (Def 2) is a distance between the
distribution of `(C(x₁),…,C(x_d))` **taken over a uniformly random secret key** and the ideal
(uniform) distribution. The main results bound attack advantage through it:

* **Theorem 13** (differential) and **Theorem 17** (linear), `[READ]`: for a cipher with
  pairwise (2-wise) decorrelation bias `ε`, no differential/linear distinguisher of complexity
  `< O(1/ε)` succeeds. *"if the pairwise decorrelation bias has the order of `ε`, linear
  distinguishers do not work against [C] unless its complexity reaches the order of magnitude
  of `1/ε`."*
* The **constructions** (`NUT-II`, §3.3) achieve this with **algebraic key injection over a
  random key**: `NUT-II` is literally `C(x) = k₁·x + k₂` with `(k₁,k₂)` uniform. `COCONUT`,
  `PEANUT`, `WALNUT` families build on it. **Theorem 8** is explicitly a key-averaging bound.

Every guarantee is an **average over a uniformly random secret key.** Now our object:

> ⚠ **A hash permutation is KEYLESS.** There is no random secret key to average over; the
> round constants are **fixed and public.** For a single fixed permutation the "random key"
> distribution is a point mass, the decorrelation bias is not the averaged quantity the
> theorems bound, and **Theorems 13/17 say nothing.** A perfectly-2-decorrelated *family*
> still contains weak individual members, and a keyless permutation *is* one fixed member.

**This is not a small-print exclusion; it is where the gap lives.** Decorrelation is, in fact,
the cleanest existing instance of *"count the differential, not the trail"* — the 2-wise bias
bounds the **actual** differential probability (the aggregated object), not one characteristic
— and it achieves that closure **because averaging over the key linearizes the differential
probability** (`k₁x+k₂`'s pairwise distribution is exactly uniform). **The closure is bought
with secret randomness we do not have.** So:

> ⭐ **The trail→differential gap does not collapse for a keyless permutation, and the reason
> is structural: the only IT-flavoured theory that closes it needs a secret random key to
> average over, and a hash has none.** *"No trail above 2⁻¹²⁸" is not "no differential above
> 2⁻¹²⁸"* precisely because the fixed-key differential probability is not the key-averaged one
> — which is the exact object Beyne's quasidifferential theory (eprint 2022/837) was built to
> compute. That theory is **exact but a large finite computation** (an EXACT-ATTACK-flavoured
> instrument, per `formal-cryptanalysis-pipeline.md` §2's marks), not a cheap defense bound.
> There is no decidable defense-side closure of this leg for a keyless design, and
> decorrelation tells us why: the randomness that would make it decidable is absent by
> construction.

⚠ **The one thing decorrelation *does* offer us**, and it is worth a follow-up: its
*construction* discipline (a provable 2-wise-decorrelated **round** as a building block) is
transplantable to the **keyed** parts of our stack that a hash is not — grind/PoW keyed
stages, or a keyed compression in a `WARP`-style MMO mode (`hash-ideation.md` §2.1), where a
random-ish key *is* present. **Named, not pursued here.** For the sponge permutation itself,
decorrelation is inapplicable and the leg stays argued.

---

## 3. THE THREE MECHANISMS, GENERALIZED INTO DESIGN RULES — with the adversary's cut named

The brief's three observed mechanisms — saturation, finite lattice, duality — are each an
instance of a general rule that predicts **which component choice buys decidability.** A rule
that predicts the choice is worth more than any construction, so here they are, each with the
property that makes it available **and the structure it hands the attacker.**

### 3a. SATURATION → *pick the extreme of a monotone bounded quantity, so it stops in O(1) steps*

**Mechanism observed**: `x⁻¹`'s `F₂`-degree is **maximal (31)**, so a degree-based instrument
(CLAASP-MP, division property) saturates in **two steps** and the bound is decided by a
one-line composition `deg(f∘g) ≤ deg f · deg g` rather than by a solver (`weft-c-spec.md`
§4a).

**General rule**: *if an attack is governed by a **monotone** quantity `q` with a known
ceiling `q_max` (degree, correlation order, algebraic immunity), choose the component that
sits at `q_max`. Then `q` reaches its ceiling in `⌈log_{step-gain} q_max⌉` steps — a **decided
constant**, not a searched bound.* The instrument returns "saturated" without solving anything.
Decidability is bought because a monotone sequence that has hit its ceiling **provably cannot
move**, so the search terminates by algebra.

⚠ **What it hands the adversary**: *saturation of the DEFENDER's instrument is also saturation
of the defender's VISIBILITY.* A maximal-degree S-box makes degree-based analysis die
immediately **in both directions** — it certifies nothing beyond "≥ 2 steps," and any attack
that does **not** read that quantity (the entire Gröbner leg, which reads *structure*, not
degree) is unaffected and now runs against a design its designers can no longer instrument.
`weft-c-spec.md` §4a states this: *three instruments reporting "nothing here" is one fact
about our instruments, not three about the primitive.* **Rule: saturation is a decidability
win only for the saturated quantity, and it blinds you to every other.** Buy it, and buy an
independent instrument for each un-saturated leg.

### 3b. FINITE LATTICE → *index the invariant family over a tower, so it is enumerable not searched*

**Mechanism observed**: the tower-indexed subspaces `V_b` give an invariant family that is
**enumerable** (one per tower level), so the structural leg is discharged by exhaustion at
every level rather than by an open subspace-trail search (`formal-cryptanalysis-pipeline.md`
T1/T2; `weft-c-spec.md` §2c, §3g).

**General rule**: *if the potential invariants of a component form a **finite, indexable
lattice** — the subfield tower `GF(2) ⊂ GF(2²) ⊂ … ⊂ GF(2³²)`, the block-constant flags of a
coset-union point split, the isotypic components of a linear layer's `F[M]`-module — then the
"are there invariant subspaces?" question is a **finite enumeration** (`EXACT-DEFENSE`), not an
argued absence.* The tower structure is what makes the family finite; a generic component's
invariant subspaces are an infinite variety.

⚠ **What it hands the adversary**: *the same tower index that enumerates the DEFENDER's check
enumerates the ATTACKER's targets.* A coset-union point split makes the block-constant flag
**enumerable — and present** (`weft-c-spec.md` §6: Mark-32's own MDS carries a `12 ⊃ 6 ⊃ 3`
flag *because* its point split is a coset union, and the coset union is exactly what makes the
fast transform fast). **The lattice you enumerate to check is the lattice the attacker climbs.**
2026/306 turned exactly such a flag into `2¹⁰⁶` on Poseidon2. **Rule: an enumerable invariant
family is a decidability win only if the enumeration comes back EMPTY; if it comes back
non-empty the same finiteness that let you find it lets the attacker use it.** Enumerability
decides the question in both directions — prefer the component whose lattice is enumerable
**and provably empty** (full-field shift, irreducible-charpoly linear layer), not merely
enumerable.

### 3c. DUALITY → *choose a component with a self-map that folds the codeword search in half*

**Mechanism observed**: `branch(M) = branch(M⁻¹)` and the four-pass exhaustion over
`M, M⁻¹, Mᵀ, (Mᵀ)⁻¹` **exhaust** every codeword with min-side ≤ 2, self-certifying the branch
number (`formal-cryptanalysis-pipeline.md` S2; `weft-c-spec.md` §3c).

**General rule**: *if a component admits an **involutive or order-`k` self-map** that acts on
the search space (transpose–inverse duality for a linear layer, Frobenius for a subfield
structure, the differential/linear DDT–LAT transpose relation for a quadratic S-box), the
exhaustive search folds by the order of the map — and a search that was `O(N)` becomes
`O(N/k)` with the folded part **certified by the symmetry**, not re-searched.* Decidability is
bought because the self-map turns "search all codewords" into "search a fundamental domain and
apply the symmetry."

⚠ **What it hands the adversary**: *a self-map that folds the search is a self-map the attacker
composes into a distinguisher.* The transpose–inverse duality is why a **linear** trail and a
**differential** trail are the same object viewed twice — convenient for the defender's
exhaustion, and it is exactly the structure a **subspace-trail** attack rides. The `K*`-
equivariance that a constant-free inverse-`+`-linear round enjoys (`weft-c-spec.md` §1e) is a
self-map (`R₀(λS) = λ⁻¹R₀(S)`) that no branch number sees and that an attacker turns into a
subfield-valued invariant. **Rule: a folding symmetry decides the search it folds, and every
symmetry is a potential distinguisher — so break it in the ROUND (constants, a non-`K`-linear
layer `B`) while keeping it in the COMPONENT you are certifying.** Duality is safe as an
*analysis* tool and dangerous as a *round* property; the design must separate the two, which is
precisely why Twill keeps `B` (`weft-c-spec.md` §1e).

### 3d. The meta-rule the three share

> ⭐ **Every decidability-buying mechanism is a piece of structure, and structure is
> two-faced: the property that makes a question *finite/monotone/folded* — hence decidable —
> is the same property an attacker reads.** Saturation decides one quantity and blinds you to
> the rest; an enumerable lattice decides emptiness and hands you a target if non-empty; a
> folding symmetry decides a search and is a distinguisher if left in the round. **The
> decidability is real and the cost is real, and they are the same object.** A design that
> wants decidability-as-primary must therefore, for each mechanism it uses, (i) name the
> quantity it decides, (ii) name the attack that reads the same structure, and (iii) show the
> second is bounded by something *other* than the mechanism itself. §4 does this leg by leg
> for a concrete sketch.

---

## 4. `SETT` — a construction with decidability as the PRIMARY criterion, and its costs named

Not a proposal to build (the standing verdict holds, §5; `post-weft-hash.md` §7). A **worked
example of what "decidability primary" forces**, so the criterion is concrete and its costs
are visible. Name per house convention (weaving terms taken): **SETT** — the count of picks
between two selvages, i.e. *the number you must fix before the pattern is decided.*

### 4a. The choices, each made FOR a decidability rule and against its cost

| component | choice | decidability rule (from §3) | ⚠ cost to the adversary named |
|---|---|---|---|
| field | `GF(2³²)` Fan–Paar tower | 3b finite lattice: subfield invariants **enumerable** | tower gives coset-union structure ⇒ **watch block-constant flags** (§3b); use a full-field shift so the enumeration is empty |
| S-box | `x⁻¹`, **all** lanes | 3a saturation: `F₂`-degree maximal ⇒ degree legs decided in 2 steps; §1c: full inverse ⇒ **refuses** the FreeLunch model | Gröbner leg becomes **un-decidable** (§1c) — this is a *deliberate* trade of a decidable floor for conjectural resistance, and it must be **said**, not hidden |
| linear layer | companion matrix of an **irreducible** degree-`t` `f`, all coeffs nonzero | 3b: `F[M]`-module **simple** ⇒ invariant subspaces = ∅ **by theorem** (Heddle, `hash-ideation.md` §2.4/§3.3) | irreducible ⇒ **diffusion diameter = `t`** ⇒ a lone difference takes `t` rounds to detonate ⇒ **round count dominated by diffusion latency**, measured 4–5× cells (the reason Heddle is cost-dead) |
| round asym. | a non-`K`-linear `B` layer + full-field constants | 3c: breaks the `K*`-equivariance self-map in the **round** while keeping transpose duality in the **component** | `B` triples the per-lane algebraic degree the attacker faces **and** the in-circuit aux cells (`weft-c-spec.md` §1e) — pay it |
| mode | overwrite sponge, capacity carried, length in capacity | inherits the **proved field-free sponge indifferentiability** (the one unconditional layer) | none new; the assumption stays exactly "ideal permutation" |

### 4b. What SETT decides and what it argues — the honest ledger

| leg | mark | SETT's status | decided by |
|---|---|---|---|
| differential / linear (trail) | EXACT-DEFENSE | **decided** | wide-trail via branch, four-pass exhaustion (3c) |
| invariant subspace / quotient | EXACT-DEFENSE | **decided — and EMPTY by theorem** | irreducible charpoly ⇒ simple module (3b) |
| subfield / twisted-subfield | EXACT-DEFENSE, cost 0 | **decided — empty** | full-field shift + constants (3b) |
| integral / division property | EXACT-ATTACK | **decided (≥ 2 steps)** | `F₂`-degree saturation (3a) |
| S-box skipping / GSR | EXACT-ATTACK | **decided (≤ 1 step)** | no partial rounds (`weft-c-spec.md` §2d) |
| **Gröbner / CICO** | HEURISTIC, no defense bound | ⚑ **decidable only per-model, as an UPPER bound; no floor** | §1 — `D_I` known for a model, `min` over models is not decidable |
| **trail → differential** | — | ⚠ **argued — irreducibly, keyless** | §2 — decorrelation needs a key SETT does not have |

> **Five legs decided, one decidable-only-as-an-upper-bound, one irreducibly argued.** That is
> the shape of the best available object, and the two that do not close are **the same two the
> brief named** — not because SETT is weak but because those two are where decidability ends
> for a keyless AO permutation, and §1c and §2 give the structural reason for each.

### 4c. The cost of decidability, totalled

Decidable structure is **structured**, and Weft died of importing a structure an attacker
could use (`weft2.md`, the triangularity kill). SETT's structural bill:
* **diffusion latency** (irreducible companion, 3b) ⇒ `t`-round diameter ⇒ ~4–5× the cells of
  a dense-MDS design at equal statistical margin — the dominant, measured cost;
* **Gröbner un-decidability** (full inverse, §1c) ⇒ its binding leg is *argued*, so it inherits
  the `×2.1` outward-correction prior and the whole "no defense-side bound" posture — SETT is
  **not more secure** on this leg than Twill, only more explicit that the leg is open;
* **the block-constant flag risk** of any tower field (3b) ⇒ a normative full-field-shift
  condition, or the flag returns.

> ⚑ **The construction that maximizes decidability is NOT the one to deploy** — it is
> cost-dead on diffusion (Heddle's finding, `hash-ideation.md` §2.4) and it moves nothing on
> the one binding leg. **Decidability-primary is a design *lens*, not a design *objective*:**
> it tells you which legs you can stop arguing and forces you to say the remaining ones out
> loud. The deployable object trades some decidability back for cells (a dense mixing layer,
> accepting an *enumerable* rather than *empty* structural lattice) — which is exactly what
> Twill does, and why Twill, not SETT, is the standing candidate.

---

## 5. ⭐⭐ THE CEILING, AS A POSITIVE RESULT

The lane's deliverable is a **positive statement about what is knowable**, and here it is.

> **For an arithmetization-oriented sponge hash, "designed to be information-theoretically
> safe" cannot mean "IT-secure" — collision resistance is impossible for a compressing
> function, unconditionally. It has exactly one honest meaning, and it is a statement about
> the ASSUMPTION SURFACE and the DECIDABILITY of the attack classes:**
>
> 1. **The assumption surface is exactly ONE object: an ideal permutation.** Everything above
>    it is unconditional (the IOP layer) or reduces to it (sponge indifferentiability, held
>    field-free and proved). This is the minimized surface, and it is already minimal — there
>    is no known construction with a smaller one.
> 2. **Of the seven attack classes, FIVE are DECIDED by terminating computation**: differential
>    and linear (wide-trail, four-pass branch exhaustion), invariant subspace and autonomous
>    quotient (module simplicity / closed-set enumeration), subfield (Galois-orbit check),
>    integral/division (degree saturation), and S-box-skipping (partial-round count). Each is
>    `EXACT-DEFENSE` or `EXACT-ATTACK` in `formal-cryptanalysis-pipeline.md` §2's sense, and
>    each is discharged by a computation that **halts with a certificate**, not an argument.
> 3. **ONE class — Gröbner / CICO — is DECIDABLE ONLY PER-MODEL, as an upper bound.** The ideal
>    degree `D_I` of any fixed regular-sequence model is closed-form (Perrin's "the future"),
>    but security is the `min` over models, and no algorithm quantifies over all encodings.
>    **A design can make its best-known model's `D_I` exceed the bar; it cannot certify no
>    better model exists.** Choosing a full inverse layer *refuses* even the per-model
>    decidability in exchange for having no known cheap model at all — a deliberate, statable
>    trade, not a gap.
> 4. **ONE class — trail → differential — is IRREDUCIBLY ARGUED for a keyless design.** The
>    only IT-flavoured theory that closes it (decorrelation) requires a secret random key to
>    average over; a hash permutation has none. The gap is structural and named.
>
> **That is the ceiling: assumption surface = {ideal permutation}; 5 of 7 classes decided by
> computation, 1 decidable per-model as an upper bound, 1 irreducibly argued — with the
> structural reason for each of the last two.** It is not "IT-secure" and anything that says
> so is false. It is the precise, defensible, and — as far as this lane's corpus reaches —
> **unwritten** statement of what "safe by design" can mean for an AO hash.

⚠ **Corpus disclosure.** The "nobody has written it" claim is about **framing**, not
components — every ingredient (Perrin's `D_I` program, Vaudenay's decorrelation, the FreeLunch
boundary, the wide-trail EXACT-DEFENSE marks) is published and cited above. The unwritten thing
is the **assembly into a decidability ledger with the two arguments' structural causes named**,
and that claim rests on the reading in this note, not on an absence search over the eprint
mirror (which is cryptology-only and cannot see the ITP/formal-methods venues where a
decidability framing would live — `swarm/PREFLIGHT.md` corpus-blindness note).

---

## 6. WHAT THIS SAYS TO THE SIBLING LANES

* **To the ideation lane** (`hash-ideation.md`): the regular-sequence gate item is worth
  building, **with one correction** — it must be the **constructive FreeLunch certificate**
  (exhibit a coprime-pure-power order, O(n²)), **not** a post-hoc regularity test (a GB in
  disguise, §1e). And it decides a per-model **upper bound**, never a floor (§1d), so it can
  **block** a candidate (no cheap model ⇒ argued leg) but never **bless** one. For **Bobbin**,
  `[MEASURED]` the `xy=1` model is not directly FreeLunch (§1b), so the item's verdict is *"sits
  with the un-modelable designs — Gröbner leg argued"*, which is the honest block the lane
  already applied.
* **The Jacquard/circ kill and the horizon caution are noted and adopted.** This lane's
  computations are **exact and terminating** (Gröbner bases, leading-monomial comparisons, full
  enumerations), not horizon-limited trail scans, so the 206-false-stall failure class cannot
  bite here — but the discipline (*a decidability instrument that reports a property because it
  stopped looking too early is worse than none*) is the reason every `[MEASURED]` cell above is
  an exhaustive or closed-form computation with its scope stated, not a bounded search.

## 7. REPRODUCE

```bash
cd ~/dev/zkml-research/notes/decidable-scripts
python3 dbd_ideal_degree.py       # both-shapes-are-FreeLunch + cert-vs-GB timing (small)
python3 dbd_freelunch_boundary.py # leading-monomial structure, sparse vs full
python3 dbd_bobbin.py             # Bobbin xy=1 witness: not directly FreeLunch (chain collisions)
python3 dbd_density.py            # density changes collision COUNT, not existence (self-correction)
# reads at source:
#   ~/paperbin/eprint-2024-347.pdf         FreeLunch  (Def 8, Prop 4, sec 4.3)
#   ~/paperbin/xhash-security-perrin-2024-605.txt   Perrin abstract
#   ~/paperbin/spring2026-perrin-slides.pdf         "D_I are the future" / "D_I vs D_2I?"
#   ~/paperbin/eprint-2025-259.pdf         resultants (sec 5, closed-form ideal degrees)
#   (Vaudenay decorrelation, J.Cryptol 2003, fetched to scratchpad this lane)
```

**Provenance.** `[MEASURED]` here: both power-map CICO models FreeLunch (coprime pure-power
leading monomials), confirmed by explicit grevlex GB at t=2,R=2; the `xy=1` inversion model
NOT directly FreeLunch (degree-2 product leading terms chain-collide, sample collisions shown);
the FreeLunch-certificate check 6–45× cheaper than the GB at n=4–6; linear-layer density
changes the collision count (MDS 12/36, perm 6/36 at t=3,R=3) but not its existence.
`[READ]` at source: FreeLunch §4.3 (full-inverse-layer limitation, verbatim), Perrin abstract
and slides (`D_I` conclusion, verbatim), 2025/259 §5 (closed-form ideal degrees + the breaks),
Vaudenay §2–3/§6 (decorrelation bias is a key-average; Theorems 13/17; `NUT-II = k₁x+k₂`).
`[DERIVED]` here, labelled: the minimal-model variable-count divergence (`α^{tR}` vs `α^R`);
the modelable=decidable=attackable identity; the three design rules and their adversary cuts;
the SETT ledger. **No claim above is `[LEAN]`** — this lane authored no constraint.
