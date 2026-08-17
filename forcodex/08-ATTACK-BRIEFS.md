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

**⚑ THE FOUR THINGS WE NAMED AND NEVER RAN** (in priority order):
1. **MITM / boomerang on the gadget-Feistel.** Our own note says *"the order-2
   differential does NOT die in one round"* and files this as the **first
   attack-me item**. It has never been run.
2. **The τ=2 settling experiment**: Beyne–Verbauwhede's own notebook
   (eprint 2025/932, `SPN.ipynb`) **at our parameters**. Their result — integral
   properties survive **round 1 at prime, 13 at degree 2, 20 at degree 4** — is
   what drove us off τ=4. **We chose τ=2 without running it at τ=2.**
3. **Gröbner/CICO on σ-Poseidon**, with **Perrin's methodological rule**
   (2024/605, in paperbin): *base the argument on the **elimination step**, not
   on computing the Gröbner basis — the latter is "sometimes literally
   non-existent."* ⚠ And CheapLunch (2025/2040) now extends FreeLunch past
   CICO-1 to **multiple outputs** — the natural first thing to point at us.
4. **The free-norm-check assumption** — the Feistel's named risk. Our binding
   layer made an unchecked norm *unrepresentable* (a subtype), **but the hash
   mode's security argument still leans on it.**

⚠ **Known-adjacent breaks to aim with**: **Grassi et al. 2023/822 broke full
Rubato** — *"symmetric primitives over rings Z_q for composite q… a setting
where security is much less studied."* **Our q is prime, which is that paper's
own countermeasure** — verify that actually saves us. And **2021/1010**
independently proposed our de-linearization idea in one sentence.

**Tooling, now versioned**: `~/src/ring-ro-hash/` (25 files, `git init`'d
2026-08-16) — `branch.py`, `design_branch_frontier.py`, `sbox_law.py`,
`avalanche.py`, `design_subfield_invariance.py`, `galois_span.py`,
`design_gadget_feistel.py`, `sigma_poseidon.py`, `msis_correction.py`,
`run_all.sh`. Design record: `notes/ring-hash-design.md`,
`notes/ring-hash-tau-verdict.md`, `notes/ring-hash-cryptanalysis.md`
(⚠ **that last file has ZERO external citations** — its "not executed:
a direct Gröbner/CICO attack" line is an invitation).

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
