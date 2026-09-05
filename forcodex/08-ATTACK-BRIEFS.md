# Attack briefs — for codex

2026-08-17. **These are our own constructions, and we want them broken here
rather than in public.** Ember's division of labour: we design and defensively
analyze; **codex runs the offensive cryptanalysis**, being better at it.

Everything below is a candidate, none deployed, all greenfield. **A break, a
distinguisher, or a tightened bound are all wins. So is "your parameters are
fine but your ARGUMENT is wrong" — several of ours are cost tables wearing
security clothes.**

---

## The standing rule these briefs exist to satisfy

> **Novelty is acceptable iff we attack it ourselves first.** Dregg is young;
> nothing is deployed; the cost of a break found here is a rewrite, and the
> cost of one found later is a reputation. **Every custom primitive below is
> unshipped precisely until this file has answers.**

## What we already checked, so you do not redo it

| construction | done | result |
|---|---|---|
| Weft (mixing = our additive-NTT transform, `x⁻¹` S-box) | branch number, **exact** | **6** at t=24 (MDS 25; Poseidon2's own layer 8) — *and the real problem was a **4-deep invariant subspace flag**, which branch number does not see* |
| σ-Poseidon / gadget-Feistel (ring hash) | branch numbers, schedule cost table, τ trilemma | τ=1 dead (challenge space 2⁶⁴), τ=4 punished by integral cryptanalysis, **τ=2 chosen** |
| Poseidon2 (deployed) | four independent confirmations incl. **CheapLunch 2025/2040 at source** | *"no attacks on full Poseidon with its security margin, 80 ≤ λ ≤ 256"* |

---

## BRIEF 1 — the ring hash (highest value; zero external analysis)

**What**: an RO-like hash over **R_q = Z_q[X]/(X^d+1)** that is *compactly
arithmetizable over the ring* — Zama's open problem (eprint 2026/1127 §D).
Two candidates, both ours:
- **σ-Poseidon**: Poseidon2-shaped, linear layers `x + c·σ(x)` where σ are
  **Galois automorphisms already present as native terms in Zama's own
  constraint system**. Bar: 363,513 R_q constraints at τ=2.
- **gadget-Feistel**: 192 rows/perm, **27.4 rows per absorbed ring element**
  — 26× cheaper than Poseidon-over-Z_q. **92,257 constraints**, taking FS from
  52% → 4% of the circuit.

**Parameters**: **τ = 2**, **q = 2⁶⁴ − 257** (ord₃₂ = 2, α = 7 legal,
γ = 257), d = 16, B = 2¹⁶, K = 4, NR = 16.

**⚑ THE FOUR THINGS WE NAMED AND NEVER RAN** — **ALL FOUR NOW RUN (2026-08-18).**
Full record: `notes/ring-hash-attacks-2-3-4.md`; scripts `notes/ring-attack-scripts/`.
⚠ **Nothing below is a break, and NR=16 is still not derived.** What changed is that
three of the four now have *numbers* and the fourth has a *forgery*.

1. ✅ **RUN 2026-08-18 — REACHED at 2 rounds, still OPEN.** ~~MITM / boomerang~~ —
   ⚑ **the framing was retargeted and that mattered more than the result.** The
   MILP/MITM route was the wrong door: **2025/2213 is AES-SPN only** (*"beyond
   AES-based primitives"* is its own future work) and the Feistel papers are
   **2022/189** and **2023/1359** (*"Automated MITM Attack Goes to Feistel"*, which
   was in nobody's sweep). ⚑ **And the sibling lane's "no published MITM model can
   be instantiated" does NOT survive at source**: 2022/189 §3.1/§4.3 handles
   expanding *and* contracting cells — *"This is the only required change"* — and
   explicitly does not require bijective round functions.
   - **A model WAS instantiated** at ring-element granularity (legitimate because
     `F_r(R)_i = Σ_{i'} f(R_{i'})` — the nonlinearity never couples two input
     elements, **measured 12/12**). Raw reach **3 rounds**. ⚑ **But calibrated
     against the two published 2-branch-Feistel targets it underestimates by up to
     4×, so the number to carry is 12 rounds vs NR=16 — a 1.33× margin, NOT 4×.**
   - ⚑ **The leg that actually defends us is the CAPACITY, not the round count**: a
     MITM needs **50–75%** relative gain to move the 128-bit claim; the largest ever
     published against a 2-branch Feistel is **~12%**. **4–6× the state of the art.**
   - ⚑ **THE RETARGET, and the real result.** The one technique that *reaches* a
     decomposition layer is hand-built: **eprint 2024/1900** ("Opening the Blackbox",
     Liu et al.). ⚠ **Two corrections to how it was described to me.** (a) *"Independent
     of the S-box"* is **§3, the baseline the paper BEATS** — §4's carry-DDT exists to
     **open** the S-box and is **maximally S-box-dependent**; what it does not need is
     the *high-degree polynomial over F_p*. (b) ⚑ **It runs at FULL parameters and is
     CHEAP** — Goldilocks and 2^31−1, 10^6 queries, **15–32 lookups each**. **So the
     "this family only runs at toy primes" pattern does NOT retire this instrument**,
     which makes its verdict a statement about the primitive, not about our budget.
     Its published reach: **3/5 Tip5, 2/6 Monolith-64, 4/5 SFS Tip4.**
   - ⚑ **AND IT CANNOT BE STATED AGAINST US — three independent breaks**, since its
     axiom is `z_i = S_i(w_i)`: (1) `Z_j = Y_j·Y_{j+1}` couples **adjacent limbs**
     (patching costs `4B² = 2^34` states, a `2^66` table); (2) the product is a
     **negacyclic convolution**, so **no limb order gives a bounded-width state**;
     (3) ⚑ **fatal alone — the dense `g`/`h` mixing destroys the limb structure before
     recomposition, so `DDT_{i,j}` has no definition on our primitive.**
   - **What WAS run**: its carry half (which *is* our step 1, validated against 40k
     samples at deployment parameters) plus an **exact** substitute for the other half.
     **Reaches 2 rounds, then stalls.**
   - ⚠ **THE NEAR-MISS — a standing design refusal.** Their §7.1 *is* a working recipe
     for a **coupled** nonlinearity (Monolith's `x_i + x_{i-1}²`), keeping their
     Algorithm 2 as a subroutine under outer backtracking. **It would apply to us if our
     product were `R_i·R_{i+1}` (element-coupled) instead of `Y_j·Y_{j+1}` (limb-coupled).
     Never move the product to element granularity for cost** — that one change hands an
     attacker a published, full-size, measured recipe.
   - ⚠ **Two parameter facts, logged because they cut both ways.** Their Thm 1 (§4.5)
     needs *"the `l_{h−1}` most significant bits of `p` all 1"* — **`q = 2^64−257 =
     0xFFFF_FFFF_FFFF_FEFF` satisfies it exactly, as Goldilocks does** (verified), i.e.
     shared with every prime this paper broke; harmless under break 3, live again in any
     variant that restores limb-locality. And the precompute is `16h·2^{2l}`: **2^38
     (~1.25 TB) at `B=2^16` vs 2^23 (~42 MB) at `B=2^8`** — ⚑ **`B=2^16` is a 65536× tax
     and `B=2^8` would put us inside the attacked regime. An argument FOR the current base.**
   - ⚑ **NEW STRUCTURAL FINDING: `P=2` never multiplies the top plane.** `Z_0=Y_0Y_1`,
     `Z_1=Y_1Y_2`, so `Y_3` enters only linearly ⇒ **`F_r` is exactly affine in the top
     plane with a state-independent slope, probability 1, on a set of size 2^1024.**
     **25% of the state crosses every round on a purely linear path.** `P=3` closes it
     at 12→16 rows/round (+33%). This is an *order-1* relation — strictly stronger than
     the order-2 one the note flagged.
   - ⚑ **AND THE STANDING REFUSAL IT PRODUCES: the reach is bounded by the DENSITY of
     `g_3`, not by NR.** With `g_3 = B^3` the characteristic **chains without limit**
     (that is the live falsifier). **A sparse/structured/scalar top-plane coefficient —
     exactly what a cost pass reaches for — reopens an unbounded deterministic
     characteristic.** Chaghri's lesson through a different door. **`g` must stay dense.**
   - ⚠ **The order-2 claim, scoped correctly at last**: constant 40/40 for **one round
     function** (reproduced), and the **permutation kills it at 2 rounds** (0/20). The
     note's sentence is true; its scope is one round function, not the permutation.
   - ⚑ **STILL OPEN.** Four instruments have now been pointed at this primitive and
     only one *reached* it, for 2 rounds. **That is one fact about our instruments, not
     four about the primitive. NR=16 remains precedent.**
2. ✅ **CLOSED 2026-08-17 — RAN, guard passed, result below.** ~~The τ=2 settling experiment~~: Beyne–Verbauwhede's own notebook
   (eprint 2025/932, `SPN.ipynb`) **at our parameters**. Their result — integral
   properties survive **round 1 at prime, 13 at degree 2, 20 at degree 4** — is
   what drove us off τ=4. ~~We chose τ=2 without running it at τ=2.~~ **RESULT: τ=1 dies at round 2,
   τ=2 at round 24, τ=4 at ≥42. The ordering holds by execution; τ=4 is
   INTEGRAL-INFEASIBLE. ⚑ But at identical (e,t) the paper's base 2³¹ gives 13
   and our 2⁶⁴ gives 24 — we had chosen against a number understating us 1.85×
   — and 24 is a FLOOR (the deployed σ-layer mixes weaker than the model),
   leaving ~6 rounds against the borrowed budget. The round-count derivation
   is now binding.**
3. ✅ **RUN 2026-08-18 — CLOSED, clears by hundreds of bits.** ~~Gröbner/CICO on
   σ-Poseidon~~.
   - ⚠ **PERRIN'S RULE WAS MIS-PARAPHRASED IN THIS BRIEF, and the correction
     matters.** The antecedent of *"the latter"* is **THE COMPLEXITY**, not the
     basis. Every ideal has a Gröbner basis; what can be non-existent is its
     **cost**, because a weighted order can make the modelling *already be* a
     Gröbner basis (the FreeLunch phenomenon). **The rule is stronger than the
     paraphrase: never price security on an F4/F5 estimate, because it can
     evaporate to zero.** ⚠ Perrin gives **no** elimination cost formula; the
     formulas are CheapLunch's.
   - CheapLunch Eq.(10) implemented and **reproduced on 4/4 rows of its own Table 2
     to <0.1 bit** before being pointed at us; guards live by injection, and it
     does not report a break on instances published as safe.
   - ⚑ **The answer is entirely granularity-dependent, and only the WRONG reading is
     scary.** Ring-element (t=9, k=1) gives **2^106.7 — a false break**; it is
     invalid because `R_q` is not a field and `x^7` over `R_q` is **8** degree-7
     maps over `F_{q²}`, not one. At the legitimate granularities: **2^1286 / 2^1645.**
   - ⚑ **THE COMPARISON ASKED FOR: Gröbner reaches ~4 rounds; the char-p integral
     floor is 24. Gröbner does NOT reach further. The integral property remains the
     binding algebraic constraint and the ~6-round margin is unchanged.**
     **σ-Poseidon is not in the trouble this brief flagged as possible.**
   - ⚠ **Live residual not priced by any of it**: CheapLunch's model assumes `p` is
     too large to guess a coordinate. **Ours is q ≈ 2^64** — FreeLunch *abandoned*
     its XHash8 attack for exactly this. Any future attack reducing to guessing a few
     `F_q` coordinates is cheap for us in a way it is not for a 256-bit design.
4. ⚑ **RUN 2026-08-18 — PARTIAL, and it is now THE item that should gate shipping.**
   ~~The free-norm-check assumption~~.
   - **LAW, measured exhaustively (it is a counting identity, exact at 3 toys × 3
     slacks): a norm bound loose by `s` bits admits `K·s` bits of forgery per
     coefficient ⇒ `64s` bits per RING ELEMENT ⇒ `448s` per permutation call.**
   - ⚑ **The design credits itself with a 2^52 grinding COST. One bit of slack hands
     the prover 2^64 free CHOICES per absorbed element. That is not a degraded
     margin — it is the inversion of it: the prover stops paying and starts choosing.**
   - **Forgery exhibited at deployment parameters**: two plane vectors recomposing to
     the same ring element, one passing a 1-bit-slack check and failing an exact one,
     **round-function outputs differing in 16/16 coefficients.**
   - ⚑ **THE FINDING: obligation O5 is filed as a COST row** (*"bounds the ×1–2 factor
     in §4b"*) **but the same schedule determines the enforced ∞-norm bound, and
     therefore whether the hash is a function at all. O5 is a soundness obligation
     wearing a cost obligation's clothes.** Binding mode is structurally safe (`Op` is
     a short-plane subtype); **hash mode has no such protection** — in-circuit FS runs
     the sponge on *witnessed* planes.
   - ⚠ **I did NOT verify that slack exists** — that needs 2026/1127's decomposition
     schedule, which is not in our tree. Verified: *if* it exists it is priced by the
     law above, and the obligation that would settle it is open and mis-filed.
   - Minor correction: the credited figure is **2^52** at the deployed `2^64−257`
     (γ=257), not the 2^54 in the design note (computed at `2^64−59`, γ=59).

⚠ **Known-adjacent breaks to aim with**: **Grassi et al. 2023/822 broke full
Rubato**. ✅ **CHECKED 2026-08-18 — prime q genuinely saves us, and the framing was
wrong.** Their Assumption 1 (*"there exists m with m|q"*, `m ≤ ⌊2^{λ/n}⌋`) is
**unsatisfiable identically** at prime q — dead hypothesis, not a preference. ⚑ **But
that attack's expensive, composite-dependent stages exist only to STRIP RUBATO'S
GAUSSIAN NOISE** (their §7.3: the linearization *"is negligibly small compared to
doing steps 1 and 2"*). **We have no noise, so prime q defends a flank we never had,
and the cheap leg — linearization — is modulus-agnostic.** Corroboration: HERA is
prime-field and noiseless and was broken by linearization anyway (2023/1800).
⚑ **The genuinely in-scope paper is 2025/932** (Beyne–Verbauwhede), whose stated
domain is *"finite rings of prime characteristic isomorphic to a product of fields"* —
`R_q ≅ (F_{q²})^8` **by name** — and which found HADES-family degree estimates
*"overly optimistic"*. **That is the paper our own 24-round integral floor came from,
so both routes land on the same place: integral in char p is the binding constraint.**
And **2021/1010** independently proposed our de-linearization idea in one sentence.

⚑ **FOUND EN ROUTE — a new σ-Poseidon schedule defect, zero-cost to fix.** The prime-q
check ("do the σ exponents generate a *transitive* subgroup of the 8 CRT slots?")
passes **overall** — C3 is satisfied and the cipher does **not** split into 8
independent `F_{q²}` ciphers. ⚠ **But per round it fails badly**: `31 = 2d−1` is exactly
`q mod 32`, so `σ_31 ∈ ⟨q⟩` and is the **identity on the slot index**; and the schedule
cycles `5→25→17→1` with `5^8 ≡ 1`, so **one block in four uses the identity outright**.
**14/30 rounds (47%) mix no slots, and rounds 8–11 are four consecutive slot-diagonal
rounds** — S-box slot-wise, `R_q`-MDS slot-wise, σ trivial. **For four rounds the
permutation decomposes into 8 independent `F_{q²}` maps** — the very 2026/1127 §D
structure σ exists to destroy, handed to an algebraic attacker free.
**Recommend: strengthen C3 from a whole-schedule condition to a PER-ROUND one and
re-pick the exponents.** C3 as written cannot see this.

**Tooling, now versioned**: `~/src/ring-ro-hash/` (25 files, `git init`'d
2026-08-16) — `branch.py`, `design_branch_frontier.py`, `sbox_law.py`,
`avalanche.py`, `design_subfield_invariance.py`, `galois_span.py`,
`design_gadget_feistel.py`, `sigma_poseidon.py`, `msis_correction.py`,
`run_all.sh`. Design record: `notes/ring-hash-design.md`,
`notes/ring-hash-tau-verdict.md`, `notes/ring-hash-cryptanalysis.md`
(⚠ **that last file has ZERO external citations** — its "not executed:
a direct Gröbner/CICO attack" line is an invitation).
- ⚑ **09-04, from the delta lanes.** eprint **2026/1760** (Jo) collided the
  Initiative's full-round KoalaBear Poseidon1 (16,3,8,20) by choosing the MDS
  *after* the constants, under the challenge's arbitrary-MDS rule — a rules
  artefact for them, **a design rule here**: a Cauchy-programmed layer with
  borrowed constants must derive its constants after/from the matrix (1760 §6
  says exactly this). And **2026/1792**'s nonlinear subspace trails (2·E_c
  partial rounds) are the model to run against the gadget-Feistel's partial
  layer. `notes/hash-delta-2026-09-04.md` §7, `notes/eprint-delta-2026-09-04.md` §1.

---

## BRIEF 2 — Weft / Weft-2 (a live re-opening)

**Weft-1 is dead as specified** (subspace flag). **Weft-2 is under evaluation
right now** and may reach you: `novelPack` in **internal** rounds only, dense
in external (Poseidon2's own architecture), plus a **free lane rotation** —
because the flag subspaces are contiguous *suffixes* and a rotation maps a
suffix to a wrapped set. **We verified the rotation kills THAT flag; killing
one flag is not the absence of flags.**

**Your job if it survives our lane**: the **subspace-trail search on
`r ∘ novelPack`** — Grassi-style, the 2026/306 shape, and Poseidon2b's own
subspace analysis (2025/1893, in paperbin) as the template. ⚠ Note the
structure is *tower-triangular by construction* — that is exactly what made
Weft-1's flag, so a second flag is the expected finding, not a surprise.

**Also worth your eye**: our differential accounting says branch 6 + `x⁻¹`
clears 128 bits in two rounds. **We did not do the linear/correlation side.**

---

## BRIEF 3 — the dual-mode commitment

**One artifact, two modes**: the **linear mode is the P=0, round-0 projection
of the gadget-Feistel** — an Ajtai/MSIS gadget commitment `C = A·G⁻¹(v+a₀)` —
with the de-linearizer strictly *after* the read-out, so **linear-mode openings
never cross it.** Full mode is the FS hash. Same parameters as Brief 1.

**Attack surfaces we named**:
- ⚑ **The modes share arithmetic, parameters, and a one-way implication — NOT
  one assumption.** A linear-core collision breaks both. **Is there an attack
  that uses one mode against the other?** That crossing is the novel part and
  therefore the likely defect.
- The **γ-ambiguity** (γ = 257): we argue it is a grinding channel in hash mode
  that *cannot* break binding (both representatives recompose to the same v).
  **Verify or break that asymmetry.**
- The invariant that keeps **KRS25 hash-delegation unreachable** is *"π appears
  in no proven relation."* **Find a configuration where it does.**
- **`AccRbrFold`**: binding proved safe through **T = 2⁴⁷−2**, lost
  unconditionally at 2⁴⁷−1 (tight both ways). ⚠ `MsisHardEx` is *nonexistence*
  — proved at a toy, **expected false at production sizes by pigeonhole**; the
  computational reading is a named residual, **and that gap is where a real
  attack would live.**
- ⚑ **09-04, standing gate — the ideal-quotient test, BEFORE indifferentiability.**
  Any full-mode round built only from ring-polynomial operations respects every
  CRT-slot congruence and is a perfect distinguisher target. Ran on the real modulus
  (`notes/ring-hash-scripts/ideal_quotient_gate.py`): both candidates escape as whole
  permutations; σ₃₁ is the Frobenius, so 14/30 σ-Poseidon rounds are slot-respecting
  and the τ=2 cost row is mis-counted. Re-run this script on ANY change to a σ-layer
  exponent, the gadget, or the modulus. `notes/dual-mode-ideal-quotient-gate.md`.
- ⚑ **09-04**: the generalized-birthday / k-tree regime (eprint **2026/1835**) is
  absent from this brief and from `ring-hash-{cryptanalysis,dual-mode,design}.md`
  (grep: only MDS-birthday hits). Add it beside the MSIS short-opening obligation
  before anything custom ships. `notes/eprint-delta-2026-09-04.md` §1.

---

## BRIEF 4 — Z_Q product-ring sumcheck

Sumcheck over **Z_Q = F_q0 × F_q1 × F_q2** with a sampling set `A`
(pairwise-invertible differences), soundness `v·d/|A|`, **|A| ≤ min qᵢ ≈ 2³⁶**
(a theorem, attained by the diagonal). Amplification: **shared Ext4 (2¹⁴⁴)
clears our ~124-bit bar; shared Ext2 (2⁷²) does NOT.**

**Attack it here**: field-wide Schwartz–Zippel is **FALSE over Z_Q** — we
proved it by exhibit and repaired to `A`-relative counting. **Is the repair
tight?** And the **one-handle PCS obligation**: if the opening is per-limb,
*per-limb selection reappears at the opening index* — **that is a live hole if
anyone instantiates carelessly.**

---

## What a result looks like, from our side

Anything that moves a number, kills a candidate, or **shows an argument is a
cost table wearing security clothes**. Our own history says the last is the
most likely: this week we found *a bound over an empty event*, *a model too
weak to express the attack it ruled out*, and *an anti-vacuity tooth that was
itself vacuous.* **Assume the same standard of error applies to everything
above.**
