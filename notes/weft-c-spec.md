# TWILL — the coset-transform char-2 hash, specified, and its round count derived

2026-08-18. DESIGN + ANALYSIS lane, successor to `notes/weft-coset-repair.md` (the Lean
landing), `notes/weft2.md` (the coset repair) and `notes/post-weft-hash.md` (the gate and
the adopt-Mark-32 recommendation).

**Substrate, said out loud: nothing in this lane authors a constraint anywhere** — not in
Lean, not in Rust. The Lean this rests on (`Selvage/CosetNovelTransform.lean`,
`Selvage/HashRelationInverse.lean`) states theorems about proved objects; the Python is a
computational twin. **If Twill ever becomes a circuit, the AIR is Lean-authored.**

Every claim is `[LEAN]` (named theorem, green build, axiom-pinned), `[MEASURED]` (script +
log named), `[READ]` (file/paper + line), `[DERIVED]` (labeled), or `[ASSERTED-BY-<who>]`
(someone else's number, carried, not recomputed).

**Artifacts**: `notes/weft-c-scripts/weftc_legs.py` and `notes/weft-c-scripts/
weftc_trails3.py` (this lane's; both import `~/src/ring-ro-hash`'s `weft_branch.py`,
`weft2_structure.py`, `weft_coset_repair.py` **unmodified**), logs
`/tmp/weftc-legs-full.log`, `/tmp/weftc-trails3.log`. Read at source this lane: **eprint
2024/633 (Vision Mark-32)** §2.1, §3.1–3.5, §4.2 and its Sage listings, and **eprint
2019/426 (the Marvellous design strategy)** §4.5, §5 and Figure 1 — `~/paperbin/
vision-mark-32-binary-tower-hash-2024-633.txt`,
`~/dev/gh/forks/IACR-eprint-mirror/2019/426.pdf`.

---

## 0. VERDICT IN NINE LINES

1. **The primitive is named and specified**: **Twill** — Vision Mark-32's round, field,
   geometry and S-box, with its MDS replaced by the one-transform coset novel transform.
   One component swapped, on the one axis we computed. §1.
2. ⚑⚑ **`[M32-flag]` IS CLOSED, AT SOURCE AND AGAINST THE MATRIX.** Mark-32's own Sage
   listing fixes its point split to ω₀..ω₂₃ / ω₂₄..ω₄₇; **both halves are unions of cosets
   of U₁, U₂ and U₃**, so the deployed Mark-32 MDS carries the 3-deep block-constant
   invariant flag **dim 12 ⊃ 6 ⊃ 3**, has **`deg(minpoly) = 6`**, and its **entries lie in
   GF(2⁸)** — a 2¹⁹² set closed under the mixing layer. `[MEASURED]`, with a random-split
   control that shows none of the three. **The adoption target reaches our own flag.** §6.
3. ⚑⚑ **AND THE REPO HAS BEEN COUNTING MARK-32'S ROUNDS WRONG BY 2×.** `[READ at source]`
   Algorithm 1 and §4.2: *"Single round … consists of 48 round constant additions, 48
   tower-field inversions, 48 affine linearized polynomial evaluations and **2 MDS matrix
   multiplications**"* at t = 24. **Mark-32's "8 rounds" is 16 S-box layers and 384
   inversions**, not 192. `weft2.md` §6c's cells/bit table is wrong by a factor of two on
   its Mark-32 row, and the ~3.2× cells/bit headline inherits it. §5, §8.
4. ⭐ **THE ROUND-COUNT RESULT, and it is the deliverable**: **branch 8 versus branch 25
   does not move the round count at all.** Every statistical leg is satisfied at 8 S-box
   layers even against the full-state 768-bit bar, while the binding legs are algebraic and
   demand more. The 3× branch difference is worth **1.68× native mixing throughput in
   software** and **zero rounds**. §2.
5. **Recommended: R = 26 S-box layers (13 Vision-rounds).** Computable legs floor at 8;
   the binding leg is Gröbner/CICO at Mark-32's asserted 6, **corrected outward ×2.1** (the
   measured base rate of outward corrections in this literature, six instances — an
   empirical prior, **not** a bound); then Marvellous' own `N = 2ℓ` rule. Each leg is
   stated separately in §2 with its instrument named. ⚑ **Fed Mark-32's own uncorrected
   legs, the same derivation returns exactly Mark-32's 16 steps** — the check that this is
   a derivation and not a number we wanted.
6. ⚑⚑ **AND MARK-32 SHIPS BELOW ITS OWN DESIGN STRATEGY'S FLOOR.** `[READ at source]`
   Marvellous, eprint 2019/426 §5, verbatim: *"we recommend `2⌈n/5.5m⌉` rounds, **with a
   minimum of 10 rounds**"*. At Mark-32's own parameters (`m = 24`, `n = 128`) that is
   **10 rounds**. **Mark-32 ships 8.** Its abstract says so obliquely — *"fewer rounds than
   the original Vision design … the security arguments … have been reworked"* — and the
   rework is Table 1's five underived numbers. ⚑ At `t = 24` the Vision formula itself is
   vacuous (`5.5·m·N = 1056` bits at `N = 8` against a 128-bit target), **so the floor of
   10 was carrying the entire round count, and the floor is exactly the designers' stated
   distrust of their own toy extrapolation. Mark-32 dropped the distrust and kept the
   extrapolation.** §2h.
7. **The computable legs ran with live guards, and TWO guards fired on this lane's own
   instruments** — a search that pruned on genericity and so missed the constructive
   witness (reporting a clean, wrong **0**), and a mutation aimed at a column no witness
   reads (reporting a dead `8 vs 8`). ⭐ **New result: the 4-step minimum active S-box count
   is ≥ 17, strictly above the generic `⌊R/2⌋·B_d = 16`** — exactly eight weight-4
   codewords exist, they have a closed form, and they do not chain. And the Lean pins were
   **proved live by injection**: one `sorry` turns three of them red. §3.
8. **The uncomputable legs are named — and the sibling CLAASP-MP lane's answer arrived and
   refuted half of my expectation.** `[READ at source, by that lane]` CLAASP's ground field is
   `F₂`, so **Twill's mixing layer and both `B` layers are ONE `linear_layer` component each**
   and Twill is *cheaper* to express than the gadget-Feistel by orders of magnitude. It still
   buys nothing, for the other lane's own reason: `x⁻¹` has maximal `F₂`-degree, so the
   quantity the tool bounds is saturated in two steps and the leg returns `NR ≥ 2`. §4a.
   ⚑ **A tool's reach is decided by whether its ground field matches AND whether the quantity
   it bounds is still moving — not by whether the design "feels" classical.**
9. ⚠ **THE STANDING VERDICT IS UNCHANGED AND RESTATED: the char-2 hash slot does not
   exist.** No char-2 AIR, no constraint evaluator, no witness-gen (`post-weft-hash.md` §1,
   the routability grep). **This lane makes the object ready and defensible, not deployed.**
   The code-side half survives regardless. §7.

---

## 1. ⭐ THE SPECIFICATION — Twill

> **Why "Twill".** A twill weave is what you get when the weft is **offset** on each pass
> instead of returning to the same column. That is the entire design move: the evaluation
> domain is offset off the interpolation window. The lineage name in the brief is
> `Weft-C`; **Twill is the name on the wire**, and it is the only one used below.

### 1a. What Twill is, in one sentence

**Twill = Vision Mark-32 with its MDS replaced by the one-transform coset novel transform,
and with the round count re-derived rather than inherited.**

Everything else — the field, the tower, the state size, the rate/capacity split, the `x⁻¹`
S-box, the linearized affine layer `B`/`B⁻¹`, the two-step round — is Mark-32's, kept
deliberately, because **the only thing we have that Mark-32 does not is a computed reason
to change one component, and changing anything else is a deviation with no analysis behind
it.** The design's whole claim is the swap and the derivation.

### 1b. Field and state

| parameter | value | provenance |
|---|---|---|
| field `K` | **GF(2³²)**, the Fan–Paar / Wiedemann binary tower `T₅`: `T_{k+1} = T_k[x_k]/(x_k² + x_{k−1}x_k + 1)`, `x₀² = x₀ + 1` | `Theory/BinaryTowerFanPaar.lean` `[LEAN]`; the deployed additive-BaseFold line's own tower |
| element encoding | packed 32-bit; basis bit `j` = the `j`-th multilinear monomial (`towerPack`) | `[LEAN]` |
| lanes `t` | **24** | Mark-32's geometry; also the Weft geometry |
| state | `S ∈ K²⁴`, **768 bits** | |
| rate `r` | **16 lanes = 512 bits** | Mark-32 |
| capacity `c` | **8 lanes = 256 bits** | Mark-32 |
| security claim | **128-bit** collision / preimage, from `c/2` | Mark-32; generic, mode-conditional (§1g) |

### 1c. The mixing layer — `cosetPack`, the one component that is ours

Fix the ordered GF(2)-basis `β = (β₀,…,β₅)` of a 6-dimensional subspace `V₅ ⊂ K`, and
**a shift `x* ∈ K`**. Write `V_b = ⟨β₀,…,β_{b−1}⟩`, `s_b(X) = ∏_{v ∈ V_b}(X − v)` (the
monic subspace vanishing polynomial, `F₂`-linear), and the LCH novel basis
`X̂_i = ∏_{b : bit_b(i)=1} s_b`, `deg X̂_i = i`.

```
M[j][i] = X̂_i( x* + v_j )        i, j ∈ [0, 24),   v_j = the j-th point of V₅
                                   in binary-expansion order
```

**The state vector is novel-basis COEFFICIENTS**, not values — that is what separates Twill
from the systematic-RS form, and it is the whole of §6's finding
(`weft-coset-repair.md` §1a).

**Concrete instantiation (this is the spec, not an example):**

| | value |
|---|---|
| `β_j` | the `j`-th packed `F₂`-basis element, i.e. the integer `2^j`, `j = 0..5` |
| `x*` | **must be a full-field element**, `x* ∉ GF(2⁸)` and `x* ∉ V₅`. Measured instance: `x* = 0xA3C17E59` |
| ops | **the identical LCH butterfly network with shifted twiddles** — `cosetPack_succ` `[LEAN]`; 80 multiplications per application at `t = 24`; **zero operations over the encoder** |

**The four free conditions** (all cheap, none of them a branch number; three banked in
`weft2.md` §8, the fourth in `weft-coset-repair.md` §4a) — Twill carries all four as
**normative spec conditions**, not as advice:

1. **Coset domain.** `x* ∉ V₅`. (At `x* = 0` the layer is Weft-1 and has a fixed lane:
   `cosetPack_shift_zero` + `weftRound_autonomous_shift_zero` `[LEAN]`.)
2. **Full-field shift.** `x*` must not lie in any proper subfield. (At `x* = 32` every
   branch number and flag count is identical and the GF(2⁸) 2¹⁹² set survives — `[MEASURED]`,
   `weft2.md` §4.)
3. **Full-field round constants.** Every `C_{r,k}[i]` must be a full-field element. ⚑ **A
   transcript-separation tag that is a small integer IS an element of GF(2⁸)** and voids
   condition 2 (`weft2.md` §2c). Constants are therefore specified as §1f, not as tags.
4. **`M·1` must not be block-constant.** `[MEASURED]`: 24 distinct values for Twill, 14 for
   Weft-1. (Column 0 of *any* evaluation matrix is `X̂₀ = 1`, so `span(e₀) → span(1)` in one
   round for every point set; this is the condition that kills the trail at `r = 2`.)

### 1d. The S-box — lane-wise `x⁻¹`

`π(x) = x⁻¹` for `x ≠ 0`, `π(0) = 0`. Applied to all 24 lanes; **there are no partial
rounds** — §2d turns that absence into a security property.

| property | value | provenance |
|---|---|---|
| differential uniformity | `δ = 4` ⇒ `DP_max = 2⁻³⁰` at n = 32 | Nyberg; `[MEASURED]` exhaustively at n = 8, `weft2.md` §1a |
| Walsh max | `\|W\| = 2^{n/2+1}` ⇒ `corr ≤ 2⁻¹⁵`, `LP_max = 2⁻³⁰` | Lachaud–Wolfmann; `[MEASURED]` exhaustively at n = 8 |
| `F₂`-degree | **31**, maximal | standard |
| verification relation | `invWitnessed` (degree 2, one witness) or `invSystem` (witness-free, degree 3) — **graph-sound over any field** | `[LEAN]` `HashRelationInverse.lean` |
| the zero branch | **load-bearing**: `x·y = 1` without it fails completeness at 0 | `[LEAN]` `bareInv_not_complete` |
| native cost | inversion = **1.58×** a tower multiplication | `[READ]` 2024/633 §3.1, their own measurement |

⚑ **`x⁻¹` is DP/LP-symmetric at 30 bits.** One active S-box is worth exactly 30 bits on the
differential side *and* 30 on the linear side. Every branch figure below multiplies that
number, on both sides — the half `k16-proof-and-weft.md` never filled in.

### 1e. The round — Vision's two-step shape, kept

```
for r = 1 .. R_rounds:
    step A:   S[i] ← B⁻¹( S[i]⁻¹ )   for all i        S ← M·S + C_{r,1}
    step B:   S[i] ← B ( S[i]⁻¹ )    for all i        S ← M·S + C_{r,2}
```

with `B(x) = β₀x + β₁x² + β₂x⁴ + β₃` a linearized affine polynomial over `K` and `B⁻¹` its
compositional inverse (dense, all 32 Frobenius terms).

**Units, and this is where the repo's record was wrong (§0.3).** One *round* = **two S-box
layers**. Below, **`R` always counts S-box layers ("steps")**, and Vision-rounds are
reported as `R/2`. Mark-32 is `R = 16`.

⚑ **Why `B` is kept, and it is a real decision with a computed reason, not deference.**

* Without any non-`K`-linear layer, the constant-free round map is **`K*`-equivariant**:
  lane-wise inversion is homogeneous of degree −1 and `M` is `K`-linear, so
  `R₀(λS) = λ⁻¹ R₀(S)` for every `λ ∈ K*`, and over `R` steps `π₀(λS) = λ^{(−1)^R} π₀(S)`.
  `[DERIVED, one line]` The twisted-subfield test `weft2.md` §5 runs is the *subfield-valued
  slice* of exactly this family; the equivariance itself is a property of the **round map**,
  which no branch number, no subfield test and no minimal polynomial can see. Round
  constants break it — in the same "invariant subspace" sense, i.e. by masking, which is
  why condition 3 above is normative. `B` destroys it outright.
* `B` raises the attacker's **`K`-algebraic system** from all-degree-2 (`x·y = 1`, one
  equation per S-box) to three degree-2 equations per S-box (`x·y = 1`, `u = y²`, `v = u²`,
  then a linear combination), tripling the Bézout ideal degree per step from `2^{24}` to
  `2^{72}`. That is the design target of `SLVG_THOUGHT` §II.5 — *cheap in the proof
  system's operations, expensive in the adversary's algebra*.
* In-circuit `B⁻¹` costs **the same as `B`**, because the verifier constrains the **sparse**
  direction `B(w) = y` rather than evaluating the dense one. Natively both are a
  `GL₃₂(2)` matrix-vector product (`[READ]` 2024/633 Algorithm 2), which is an XOR tree:
  `[READ]` their Table 3 prices the two `B` layers at **0.6 k of 50.0 k LUT — 1.2% of a
  round.**
* And the negative case is the decisive one: **removing `B` is a deviation from the only
  reference design at this rung, with no analysis attached.** The brief's own reframe is
  that our differentiator is *checking*, not deviating. Dropping the component that carries
  what analysis exists, to save cells in an AIR nobody has emitted, is the substitution the
  house doctrine forbids.

**The coefficients `β₀..β₃`, fixed by a procedure rather than left open** — a spec with a
hole in it cannot be implemented and therefore cannot be attacked, which is the failure mode
this note exists to avoid:

```
for j = 0,1,2,3:
    beta_j = cSHAKE256("TWILL-B-v1", "TWILL-v1" || LE32(t) || LE8(j)) truncated to 32 bits
    redraw while  beta_j == 0  or  beta_j lies in a proper subfield of GF(2^32)
redraw the whole quadruple while the GL_32(2) matrix of B (2024/633 Algorithm 2) is
    SINGULAR -- B must be a bijection, and that is a rank check, not a guess
```

⚠ **`[TWILL-B]` is an obligation ON these coefficients, not a hole in place of them**: the
coefficient-grouping recurrence (Liu–Sarkar–Meier–Isobe) must be computed for the exact `B`
this procedure produces, and if it comes back badly the procedure gains a third rejection
condition. That is a spec change with a stated trigger, which is what an obligation should
look like. It inherits `[M32-coeffgroup]` — Mark-32's `B` has **three** Frobenius terms (the
Chaghri-repair density) at **adjacent** exponents `{0,1,2}` where the repair that fixed
Chaghri used spread `{0,2,8}`, and **nobody has computed the recurrence for either.**

⚠ **The cost of keeping it, stated**: `B` triples the S-box layer's auxiliary cells
in-circuit (3 aux + 3 degree-2 constraints per lane per step, versus 1 + 1). ⚑ **Unless
`F₂`-linear maps are free in the eventual char-2 AIR** — squaring over GF(2³²) *is*
`F₂`-linear, so in a Binius-shaped tower AIR the `u = y²`, `v = u²` cells may cost nothing.
**Nobody has emitted that AIR, so the cells figure for any char-2 design is contingent on
two unmeasured things** — the round count and the AIR's treatment of `F₂`-linear maps.
Named, not estimated.

### 1f. Round constants

`C_{r,1}, C_{r,2} ∈ K²⁴` for `r = 1..R/2`, i.e. `24·R` field elements. Specified as:

```
C[r][k][i] = Twill_XOF( "TWILL-v1" ‖ LE32(t) ‖ LE32(R) ‖ LE32(r) ‖ LE8(k) ‖ LE32(i) )
             re-drawn until the value is a FULL-FIELD element (condition 3)
```

where `Twill_XOF` is **cSHAKE256** with customization string `"TWILL-RC-v1"` — the hash the
deployed binary line already pins (`Compiler/Tower256AdditiveFriController.lean`,
`[READ]`), used here only to derive constants, so no circularity. The rejection loop is
the normative part: **a constant in GF(2⁸) voids condition 2 and the branch numbers cannot
see it.**

⚠ Not "the transcript-separation tags we already use" (`aligned-hash-space.md:272`). That
sentence is the recorded defect; this line replaces it.

### 1g. Mode — a standard overwrite sponge, and a flag on Mark-32's

**Twill's mode**, normative:

* State `S = (S_rate ∈ K¹⁶, S_cap ∈ K⁸)`, initialised `S_rate = 0`,
  `S_cap = (LE64(byte-length of the message) as two lanes, then a 6-lane domain-separation
  tag)`.
* **Absorb**: overwrite `S_rate` with the message block, **carry `S_cap` forward
  unchanged**, permute. Pad the message with the fewest zero field elements to a multiple
  of the rate; the length in the capacity is what makes the padding injective.
* **Squeeze**: read the first 8 lanes of `S_rate` (256-bit digest).
* **Domain separation**: 6 capacity lanes (192 bits) carry a purpose tag. This is a *use*
  requirement of ours, not Mark-32's.

⚠ **`[M32-mode]` — NEW OBLIGATION, and this lane could not settle it.** Mark-32's §3.4
prose, verbatim `[READ]`: *"The remaining blocks are absorbed by overwriting 16 input rate
elements with a message block and **overwriting the 8 input capacity elements with the
first 8 output rate elements of the preceding permutation**."* Read literally, the
permutation's **capacity output is discarded** and the chaining value is re-derived from
the rate output — which makes the construction a chop-MD with a 256-bit chaining value,
**not a sponge**, and the sponge indifferentiability argument does not transfer verbatim.
**This lane read the text only; Figure 2 is not machine-readable from the PDF, and the
reading is NOT asserted.** It is filed so it is findable, next to `[M32-indiff]`. Twill's
mode above avoids the question by carrying the capacity, which is the well-understood
object.

⚠ **`[TWILL-indiff]`** inherits the open upstream `SpongeIndiffGame` exactly as the
deployed hash does. Stated, not discharged.

### 1h. Everything a second implementer needs, in one place

```
Twill-v1
  field        GF(2^32), Fan-Paar tower T5, packed 32-bit, add = XOR
  t = 24 lanes (768 bits)     rate 16 (512b)     capacity 8 (256b)
  beta_j       = 2^j, j = 0..5                       (the F2 basis of V5)
  x*           full-field, not in V5 and not in GF(2^8); v1 fixes 0xA3C17E59
  M[j][i]      = Xhat_i(x* + v_j),  i,j in [0,24)    (one LCH pass, shifted twiddles)
  S-box        x^-1 with 0 -> 0, ALL 24 lanes, every step
  B(x)         = b0 x + b1 x^2 + b2 x^4 + b3         (linearized affine; B^-1 dense)
               [TWILL-B] the four coefficients are NOT fixed by this spec -- see sec.4
  round        [x^-1, B^-1, M, +C_{r,1}] then [x^-1, B, M, +C_{r,2}]
  R            = 26 S-box layers = 13 rounds          (derived, sec.2)
  constants    cSHAKE256("TWILL-RC-v1", ...), rejection-sampled to full-field
  mode         overwrite sponge, capacity CARRIED (not re-derived), length in capacity,
               6 capacity lanes of domain separation, squeeze 8 rate lanes
```

---

## 2. ⭐⭐ THE ROUND COUNT, LEG BY LEG — each with its instrument named

Units: **`R` counts S-box layers (steps)**; Vision-rounds are `R/2`. Two bars are carried
throughout, because the choice between them is a real one and hiding it inside a single
number is how a flattering figure gets quoted:

* **bar A = 128 bits** — the claimed security level (`c/2`).
* **bar B = 768 bits** — the state size, i.e. *no useful characteristic exists at all*.
  This is the conservative statistical convention and it is the one used below unless
  stated.

### 2a. The legs

| # | leg | mark (`formal-cryptanalysis-pipeline.md` §2) | requires (steps) | instrument |
|---|---|---|---:|---|
| 1 | **differential** | **EXACT-DEFENSE** (wide trail via `B_d`) | **8** (bar B) / 2 (bar A) | `B_d = 8` EXACT `[MEASURED]`, `DP_max = 2⁻³⁰` |
| 2 | **linear** | **EXACT-DEFENSE** (wide trail via `B_l`) | **8** (bar B) / 2 (bar A) | `B_l ≥ 8` PROVEN `[MEASURED]`, `LP_max = 2⁻³⁰` |
| 3 | **structural** — invariant subspaces, autonomous quotients, subfield/twisted-subfield, observability | **EXACT-DEFENSE** (T1/T2/T4) | **1** | `[LEAN]` at every level + `[MEASURED]` exhaustively |
| 4 | **S-box skipping / GSR-shaped** | **EXACT-ATTACK** (A2/A3) | **2** | `[DERIVED]`, §2d |
| 5 | **higher-order differential / integral** | **HEURISTIC** here; `[WEFT-integral]` open | **4** | `[ASSERTED-BY-MARK-32]` Table 1 (2 rounds) |
| 6 | **interpolation** | **HEURISTIC** | **8** | `[ASSERTED-BY-MARK-32]` Table 1 (4 rounds) |
| 7 | **Gröbner / CICO** | ⚑ **HEURISTIC, no defense-side bound in either direction** | **6 asserted → 13 corrected** | `[ASSERTED-BY-MARK-32]` Table 1 (3 rounds) × the outward-correction prior |
| — | **unknown attacks** | **NOT COMPUTABLE BY CONSTRUCTION** | — | this is what the margin is for |

```
max over computable + inherited legs (uncorrected)      =  8 steps  ( 4 rounds)
max after the outward correction on leg 7               = 13 steps  (6.5 rounds)
N = 2 * l   (Marvellous, eprint 2019/426 sec.4.5)       = 26 steps  (13  rounds)
Marvellous' hard floor at m=24, n=128                   = 20 steps  (10  rounds)
max of the two                                          = 26 steps  (13  rounds)
```

> ### **R = 26 S-box layers = 13 Vision-rounds.**

**And two checks that the derivation is a derivation:**

* ⚑ **Fed Mark-32's own uncorrected legs (`ℓ = 4` rounds, its Table 1's max), the rule
  returns `N = 2ℓ = 8` rounds = 16 steps — Mark-32's shipped count, exactly.** The
  derivation reproduces the reference design's provisioning when given the reference
  design's assumptions. The 10-step difference is *entirely* the outward correction on the
  one leg with no defense-side bound.
* ⚑ **And it clears the floor that Mark-32 does not** (§2h).

### 2b. ⭐ Legs 1 and 2 — the statistical legs, both sides, and the result that matters

Wide-trail accounting for a lane-wise S-box and a single global mixing matrix: any two
consecutive steps carry at least `B_d` active S-boxes, so `R` steps carry at least
`⌊R/2⌋·B_d`, and the best characteristic probability is at most `2^{−30·B_d·⌊R/2⌋}`.

| `B_d` | bits per 2 steps | steps for bar A (128) | steps for bar B (768) |
|---:|---:|---:|---:|
| 25 (MDS / Mark-32) | 750 | 2 | **4** |
| **8 (Twill)** | **240** | **2** | **8** |
| 6 (Weft-1, killed) | 180 | 2 | 10 |
| 2 (Poseidon2's internal layer, deployed) | 60 | 6 | 26 |

**Read the last column against the binding leg, which is 13 steps.**

> ⭐⭐ **Branch 8 versus branch 25 does not move the round count.** Both clear every
> statistical requirement well inside the algebraic legs' demand. Quantified two ways so
> the flattering one is not the only one quoted:
>
> * **over the full `R = 26`**, the full-state bar needs only `B_d ≥ 768/(30·13) = 1.97`,
>   i.e. `B_d ≥ 2`;
> * **over any 8-step segment** — the stricter reading, and the one that matters if an
>   attacker splits the permutation for an inbound/outbound phase — it needs
>   `B_d ≥ 768/(30·4) = 6.4`, i.e. `B_d ≥ 7`.
>
> **Twill has 8, exact and attained, and clears both.** ⚠ Branch 6 (Weft-1's value) clears
> the first and **fails the second** — so the segment reading is the one that distinguishes
> them, and it is the one to use. **The 3× branch gap the systematic-RS form buys is worth
> zero rounds and 1.68× native mixing throughput in software.**

**And the threshold is located rather than asserted.** On the full-`R` reading at
`R = 16` (Mark-32's own count) the statistical leg binds only below `B_d = 768/(30·8) =
3.2` — **branch 6 would still have cleared it.** ⚑ So the original Weft kill's headline —
*"branch 6 versus MDS 25"* — was **never a statistical objection at all**, which is what
`weft2.md` §1 argued and this is its quantitative form: **the thing that killed Weft-1 was
structural (leg 3, and specifically the `b = 0` fixed lane), and leg 3 is the leg on which
Mark-32 now fails.**

**Margin owed against legs 1, 2 and 3: ZERO.** They are EXACT-DEFENSE, and the pipeline's
own corollary is that a margin against an exact-defense family is not insurance, it is
cost (`formal-cryptanalysis-pipeline.md` §3).

⚠ **Scope of the row, stated:** these are bounds on *characteristics*. A keyless permutation
also admits rebound and truncated-differential routes that beat a characteristic bound. At
30 bits per active S-box in a 768-bit state this is not close, but the row is a bound and
not a proof of resistance. **`[TWILL-rebound]`, open, named.**

### 2c. Leg 3 — structural, where Twill's whole case lives

| property | Twill | Mark-32's MDS | Weft-1 (killed) |
|---|---|---|---|
| invariant lane subspaces, **every level incl. b = 0**, both sides | **0** `[LEAN]` | 0 | **5** |
| autonomous quotients, any `R`, any S-box, any constants | **0** `[LEAN]` | 0 | **5**, smallest `{0}` |
| block-constant (2026/306-shaped) invariant flag | **none** `[MEASURED]` | ⚑ **12 ⊃ 6 ⊃ 3** `[MEASURED]`, §6 | — |
| stalled block-constant trails, `\|S\| ≤ 2` + regular blocks (370) | **0 / 370** | **117 / 370** | 370 / 370 |
| stalled block-constant trails, all `\|S\| = 3` (2 024) — **new, §3g** | **0** | 0 | **2 024** |
| stalled on random irregular partitions (500) — **new, §3g** | **0** | ⚑ **20, all at dim 12** | **500** |
| stalled on the contiguous-pair family (12) — **new, §3g** | **0** | ⚑ **12 / 12, dim 12** | — |
| entries / twisted-subfield class | **GF(2³²) / none** | ⚑ **GF(2⁸) / GF(2⁸)** | GF(2⁸) |
| `deg(minpoly)` | **24** | **6** | 24 |
| per-lane observability | **24 / 24** | 0 / 24 (worst defect 18 lanes) | 8 / 24 |
| diffusion depth | **1** `[LEAN]` | 1 | **∞** |

**This is the swap, and it is the only swap.** Twill wins the structural leg outright, and
it is the leg on which the amended gate (`weft2.md` §9) puts branch number *fifth*.

### 2d. Leg 4 — why an all-full-round design has nothing to feed the skip family

GSR (eprint 2026/1692) absorbs `1 + (t − 2k)` rounds by fixing one S-box input per partial
round so the output is a constant and the state stays **affine in the free variables**;
[GSR] §5.2's own sentence — *"Because the mapping is affine, every state `S^(r)` with
`1 ≤ r ≤ t−2k` remains an affine combination of the variables in `X₁`"* — is the whole
attack. It ate **23 of Poseidon-t=24's 31 rounds** and **100% of our deployed Poseidon2's
partial budget at both widths** (`formal-cryptanalysis-pipeline.md` §0(C)).

`[DERIVED]` **Twill has no partial rounds.** To linearize one step you must fix all `t = 24`
S-box inputs, which consumes 24 degrees of freedom — the entire state. The CICO problem
offers `c = 8` capacity lanes plus whatever the rate contributes; **no budget reaches a
second step.** So the family absorbs **at most 1 step**, and leg 4 asks for 2.

> ⚑ **The transferable statement, and it is the same shape as the gadget-Feistel's:
> the skip family eats PARTIAL rounds, and a design with none has nothing to give it.**
> Vision, Rescue, RPO and XHash12 are all in this class; it is not a Twill property, it is
> an all-full-round property, and it is a real reason to prefer all-full at this S-box —
> reinforcing `weft2.md` §6c, which killed the internal/external split on cost.

### 2e. Leg 7 — the binding leg, and it is not computable in either direction

Mark-32 asserts **3 rounds = 6 steps** (Table 1). Its own §3.5.1 says why that number is
soft, verbatim `[READ]`: *"the extrapolation of solving degree is a heuristic approach and
**its correctness has not been proven**"*, and then replaces it with a Bézout ideal-degree
route whose formula it states without a derivation.

Our position on this leg, stated at the right resolution:

1. **There is no defense-side bound.** Perrin (2024/605) abstract: *"the latter complexity
   is hard to estimate—and is sometimes **litteraly non-existent**."* His repaired route is
   explicitly **conjectural** (*"under a reasonable conjecture about the behaviour of the
   degree of polynomial ideals of dimension 0"*).
2. **The strongest attack framework does not reach this shape.** FreeLunch (2024/347)
   builds systems for XHash8 but names **full-inverse-layer designs (XHash12, RPO, Rescue)
   as the ones it cannot model** — and Twill is a full inverse layer at every step. ⚑ Per
   `hash-landscape.md` ADD.4's reframe, **"unmodelable" is absence-of-analysis wearing a
   security costume**, not immunity, and it is the wrong way round from what a designer
   wants.
3. **So the leg is inherited and corrected, not computed.** The pipeline's organizing fact:
   *on families with no defense-side bound, the heuristic errs OPTIMISTIC and has been
   corrected outward every time it has been checked* — six instances, none opposed:
   2.1×/2.5×/2.9× (GSR at three targets), 4.8× (integral), 1.15× (our own Poseidon2), 1.6×
   (Ashur et al. 2023/537). **Median ≈ 2.1×.**

> **Leg 7 = 6 × 2.1 = 12.6 → 13 steps.**
> ⚠ **The 2.1 is an empirical base rate over six heterogeneous instances. It is a PRIOR,
> not a bound, and it is the softest number in this note.** It is stated as a multiplier so
> that it can be argued with, which is more than the literature's `+7.5%` offers.

### 2f. The margin, and what it is FOR

Per `formal-cryptanalysis-pipeline.md` §3: a heuristic designer's margin does two jobs —
known-attack slack and unknown-attack risk — and is honest about neither.

* **Job 1 (known-attack slack) is already spent**, explicitly, in leg 7's ×2.1. It is not
  in the margin.
* **Job 2 (unknown-attack risk) is the margin, and it is ×2**, which is Marvellous'
  own rule (`N = 2·max(legs)`) applied to our corrected max instead of an uncorrected one.
* ⚑ **The allocation question has no answer here, and that is a design virtue.** Poseidon's
  margin is misallocated because its two round types have different value functions and a
  multiplicative rule cannot see the kink at `R_P = t − 2k`. **Twill has one round type**,
  so the margin has exactly one place to go, there is no kink to be blind to, and the
  region-versus-max distinction (§3 of the pipeline) collapses to a max **because the
  design has one shape variable**. That is worth saying: the pipeline's sharpest finding is
  *inapplicable to Twill*, and the reason is a design property.

### 2g. What the number is sensitive to

| move | effect on `R` |
|---|---|
| bar A (128) instead of bar B (768) | none — legs 1/2 fall to 2 steps and were never binding |
| `B_d` falls from 8 to 6 | none at `R = 26`; binds only below `B_d ≈ 2` |
| a computed algebraic bound for full-inverse-layer designs appears | **this is the only thing that moves it**, and it would move leg 7 in either direction |
| `[WEFT-integral]` runs and disagrees with Mark-32's asserted 2 rounds | leg 5 moves; it is 4 steps against a binding 13, so it would have to move 3× to bind |
| the outward-correction prior is rejected | `R` falls to 16 = Mark-32's own count |

⚑ **Note the last row.** If you decline the ×2.1 prior, Twill's derivation returns
**exactly Mark-32's 16 steps** — from the same legs, by the same rule. **The derivation
reproduces the reference design's provisioning when it is given the reference design's
assumptions.** That is the check that the derivation is not merely a way to write down a
number we already wanted.

### 2h. ⚑⚑ The provisioning rule at source — and Mark-32 ships below its own floor

The rule Twill uses is **not ours**. `[READ at source: eprint 2019/426, the Marvellous
design strategy, §4.5]`, verbatim:

> *"To set the number of rounds for each primitive we consider `ℓ`, the maximal number of
> rounds that can be attacked by any of the attacks above. … Having determined `ℓ`, we set
> the number of rounds to be **2ℓ with a minimum of 10 rounds**."*

and §5, specialised to Vision:

> *"Experiments on reduced parameters show that the base-2 logarithm of the complexity of
> such an attack is lower-bounded by **5.5mN**. Accounting for a factor 2 security margin,
> we recommend `2⌈n/5.5m⌉` rounds, **with a minimum of 10 rounds**, for ciphers operating
> on a state of `m` elements and targeting an `n`-bit security level."*

`[READ]` The same paper's Figure 1 caption settles the units for good: ***"A single round
(two steps) of Vision."***

**Evaluate the formula at Mark-32's own parameters** (`m = 24`, `n = 128`):

```
2 * ceil( n / (5.5 m) )  =  2 * ceil( 128 / 132 )  =  2 * 1  =  2 rounds
                                            floored at        10 rounds
Mark-32 ships                                                  8 rounds
```

> ⚑⚑ **Vision Mark-32 ships 8 rounds where the design strategy it cites floors at 10.**
> Its abstract says so obliquely — *"The permutation used in Vision Mark-32 has **fewer
> rounds than the original Vision design**, which makes it perform better. The security
> arguments of Vision have been **reworked** for Vision Mark-32"* — and the rework is
> §3.5's Table 1: five numbers (1, 1, 2, 4, 3) with **no derivation shown for any of
> them**, plus a Bézout ideal-degree re-evaluation whose formula is stated without one.

⚑ **And read what the floor was FOR.** At `m = 24` the Vision formula is vacuous:
`5.5·m·N = 5.5·24·8 = 1056` bits of claimed Gröbner complexity against a **128-bit**
target, so the formula clears at `N = 1`. **The minimum-10 floor was carrying the entire
round count at this width**, and the floor exists because the designers did not trust an
extrapolation fitted on toy parameters — their own §4.5 words: *"we implement the cipher
and an attack and observe the degree of regularity experimentally for **small round
numbers** … we **assume** a constant relation …"*.

> **Mark-32 kept the extrapolation and dropped the distrust.** That is the same substitution
> `formal-cryptanalysis-pipeline.md` §0 measures six times in the other direction: on
> families with no defense-side bound, every checked heuristic moved **outward**. Mark-32 is
> the only instance on our books of one being moved **inward**, and it was moved inward past
> a floor rather than past an estimate.

⚠ **Stated as a defect of a round count, not as an attack.** Nobody has attacked Mark-32 at
8 rounds or at 10. **`[M32-floor]`, new obligation**, and it is the cheapest one on the
adoption list to act on: *adopting Mark-32 at 10 rounds instead of 8 costs 25% and restores
compliance with its own strategy.*

---

## 3. THE COMPUTABLE LEGS, RUN — with live guards, and one of them fired

Script `notes/weft-c-scripts/weftc_legs.py`, log `/tmp/weftc-legs-full.log`. Every row
carries a value it must **refuse**; a row that accepts its wrong value is reported as
**DEAD** and fails the run. This exists because the repo has shipped a dead guard row
before (a row asserting a number its source paper does not contain,
`formal-cryptanalysis-pipeline.md` §8 C1) and because a mutation that became a no-op has
killed an adversary while leaving the gate green (`minted-a-falsifier-that-stopped-falsifying`).

### 3a. ⚑ THE GUARD FIRED ON THIS LANE'S OWN SEARCH

The first version of the 4-step search enumerated singular `4×4` minors and read off a
1-dimensional kernel, skipping "degenerate" minors of rank ≤ 2. It reported
**0 weight-4 codewords** — clean, fast, and **wrong**, because the constructive witness
`f = (s₄+a)(s₂+c)` lives in exactly the skipped case: on the first 8 domain points,
`s₄(x* + v) = s₄(x*)` is **constant** (those points lie in `x* + V₃ ⊂ x* + V₄ = ker s₄`),
so columns `16` and `20` are `a·`(columns `0` and `4`) and every `4×4` minor there has
**rank 2**. The search was replaced with an exact branch-and-bound over which rows are the
(at most 4) nonzero ones, which needs no rank assumption at all.

> ⚑ **The lesson, and it generalizes past this script**: *a search that prunes on a
> genericity assumption prunes hardest exactly where the design's own structure lives.* The
> witness was constructed FROM the subspace structure, so of course it sits in the
> degenerate stratum. **The guard that caught it was "recover the known witness" — a row
> that costs one line and was the only thing standing between this note and a confident 0.**

### 3b. `[M32-flag]` — closed. See §6 for what it means.

### 3c. The exact 2-step transition profile, both sides

`f_M(w) = min{ wt(Mb) : wt(b) = w }`, exact at `w = 1,2,3` by the same certified exhaustion
that produces the branch numbers (the passes return `w + f(w)`).

| layer | side | `f(1)` | `f(2)` | `f(3)` |
|---|---|---:|---:|---:|
| **Twill** | differential (`M`) | **24** | **8** | **8** |
| **Twill** | linear (`Mᵀ`) | **24** | **12** | **12** |
| Weft-1 (killed) | differential (`M`) | 8 | 4 | 4 |
| Weft-1 (killed) | linear (`Mᵀ`) | ⚑ **1** | **1** | **1** |

**Reading:**

* `f_M(1) = f_{Mᵀ}(1) = 24` for Twill — a single active lane reaches **every** output lane
  on both sides (the `[LEAN]` general form is `weftMix_single_full_support`). **Narrow
  trails explode immediately**: a 1-active step forces a 24-active successor, so the
  minimum-active trails cannot live below weight 4.
* ⚑ **The guard row is the killed form's linear profile: `f_{Mᵀ}(1) = 1`.** That is the
  fixed lane — `e₀` is a fixed point of `Mᵀ`, giving a linear trail with exactly one active
  S-box per round for any number of rounds, which is the defect that actually killed
  Weft-1. **A profile instrument that cannot see a fixed lane is not an instrument**, and
  this row proves ours can.
* **Both floors re-run here rather than quoted**, on both sides of both quantities
  (`M`, `M⁻¹`, `Mᵀ`, `(Mᵀ)⁻¹`): the min-side ≤ 3 exhaustion reads **10** on the
  differential side and **11** on the linear side. `[MEASURED]` Min-side ≤ 3 exhausted at
  `m` means any codeword of sum ≤ 7 would have been found, so **`B_d ≥ 8` and `B_l ≥ 8`
  are both PROVEN.** `B_d = 8` is additionally **EXACT and attained**, by the min-side-4
  witness the passes provably cannot reach (§3e gives the whole family). `B_l ∈ [8,10]`
  remains open at the top. ⚑ **The open end costs nothing**: the defense uses the *lower*
  bound, so closing `[8,10]` could only improve leg 2, which is not binding.
* ⚑ **The linear side is the half the original kill never computed**, and on the killed
  form it read `B_l = 2` — worse than its differential 6, with an iterable one-active-S-box
  trail. On Twill both sides read ≥ 8. **Computing only one side of a wide-trail argument
  is how a design with an iterable linear trail passes a branch-number gate.**

### 3d. `[WEFT-multiround]`, trail half — the 4-step minimum active count

The generic bound is `⌊R/2⌋·B_d = 16` at `R = 4`, and 16 is **attained only if a chain of
weight-4 supports `(4,4,4,4)` exists** — because `w₁+w₂ ≥ 8` and `w₃+w₄ ≥ 8` force the sum
to 16 or more, and the profile above kills every other split that sums to 16 (`w = 1`
forces 24; `w = 2` forces 8; `w = 3` forces 8).

**The enumeration is exact, and the completeness argument is a theorem, not a sample:**
`p = Σ_{i∈A} b_i X̂_i` has degree exactly `max(A)` and a `(4,4)` codeword has **20 roots
among the 24 domain points**, so `max(A) ≥ 20`. That prunes `C(24,4) = 10 626` supports to
**5 781** with no loss. Within each, the branch-and-bound over which `≤ 4` rows are nonzero
is exhaustive over `K⁴` up to scalars.

### 3e. ⭐ THE RESULT — there are exactly EIGHT weight-4 codewords, and they do not chain

`[MEASURED]` 5 781 candidate supports, **8 codewords, 4 distinct in-supports, 2 distinct
out-supports, and `in ∩ out = ∅`:**

```
in {0,4,16,20} -> out {16,17,18,19}      in {2,6,18,22} -> out {16,17,18,19}
in {0,4,16,20} -> out {20,21,22,23}      in {2,6,18,22} -> out {20,21,22,23}
in {1,5,17,21} -> out {16,17,18,19}      in {3,7,19,23} -> out {16,17,18,19}
in {1,5,17,21} -> out {20,21,22,23}      in {3,7,19,23} -> out {20,21,22,23}
```

⭐ **And the enumeration turns out to have a closed form, which is worth more than the
count.** The four in-supports are `j ⊕ {0,4,16,20}` for `j ∈ {0,1,2,3}` — i.e. the four
cosets of the XOR-subgroup `⟨4,16⟩` inside `⟨1,2,4,16⟩` — so the eight codewords are
exactly

```
p  =  Xhat_j  ·  (s_4 + a)(s_2 + c) ,     j in {0,1,2,3},  c in the two s_2-cosets
```

with `a = s₄(x*)`. The mechanism is forced: `(s₄ + a)` vanishes on **all of `x* + V₄`**,
which is domain points `0..15`; the remaining 8 points `16..23` are `x* + β₄ + V₃`, on
which `s₂` takes exactly **two** values, so `(s₂ + c)` kills one block of 4 and leaves the
other. That is why the out-supports can only be `{16,17,18,19}` or `{20,21,22,23}`, and why
there are exactly `4 × 2 = 8` of them. **The constructive witness of `weft2.md` §4 is the
`j = 0` member of this family**, and the family is now complete.

**And the third step is expensive, measured.** From either out-support, the exhaustive
search to `wt_out ≤ 12` returns **nothing**: `[MEASURED]`

```
supp {16,17,18,19}  ->  min wt_out >= 13
supp {20,21,22,23}  ->  min wt_out >= 13
```

against a generic 3-step bound of `⌊3/2⌋·8 = 8`. **A trail that takes the cheapest possible
two steps pays at least 13 on the third.**

> ### ⭐⭐ **CONSEQUENCE 1: the 4-step minimum active S-box count is ≥ 17, strictly above
> the generic `⌊R/2⌋·B_d = 16`.**
>
> A 4-step trail with exactly 16 active S-boxes needs `w₁+w₂ = 8` **and** `w₃+w₄ = 8`. The
> exact profile of §3c kills every 4-step pattern with those sums except four, and the
> enumeration and the onward measurement kill those four:
>
> | pattern | killed by |
> |---|---|
> | `(1,7,·,·)`, `(2,6,·,·)`, `(3,5,·,·)` | `f(1)=24`, `f(2)=8`, `f(3)=8` — `w₂` cannot be 7, 6 or 5 |
> | `(5,3,·,·)`, `(6,2,·,·)`, `(7,1,·,·)` | `w₂ ∈ {3,2,1}` forces `w₃ ≥ f(w₂) ∈ {8,8,24}`, but `w₃ ≤ 7` |
> | `(4,4,4,4)` | ⭐ **the weight-4 digraph has no 2-edge path**: no out-support is an in-support |
> | `(4,4,5,3)`, `(4,4,6,2)`, `(4,4,7,1)` | ⭐ **onward min from a `(4,4)` out-support is ≥ 13**, so `w₃ ≥ 13 > 7` |
>
> ### ⭐ **CONSEQUENCE 2, sharper on the cheapest route: any 4-step trail that uses the
> cheapest 2-step pair costs ≥ 22.** `4 + 4 + 13 + 1`, from the same measurement.

⚑ **`[WEFT-multiround]`'s trail half is discharged on this family**, with a closed-form
description rather than a table, and the answer is a *strict improvement* on the generic
bound — the first time in this cone that a multi-round count came out better than
`⌊R/2⌋·B` rather than merely equal to it.

⚠ **Scope, stated:** the enumeration is exhaustive over `(4,4)` codewords and the pattern
elimination is exact given `f(1), f(2), f(3)`. It does **not** establish the exact 4-step
minimum — only that 16 is not attained, hence `≥ 17`. Closing it to an exact value needs
the analogous enumeration at the `(5,3)`, `(6,2)` and sum-17 patterns, which this lane did
not run.

**GUARD, and it was DEAD on the first attempt — recorded, because this is the second
distinct guard failure in one lane.** The falsification row is *"perturb one coefficient
and the count must move"*. The first version flipped `M[7][11]`; **column 11 appears in
none of the eight supports**, so the mutation was a **no-op for this measurement** and the
row read `8 vs 8` — an adversary that stopped adversarialising, exactly
`minted-a-falsifier-that-stopped-falsifying`. Flipping a coefficient a witness actually
reads moves the count to **6** `[MEASURED]`, and the script now **asserts the mutated
column is one a witness reads** before it reads the verdict.

> ⚑ **Both failures are the same shape and neither was in the code under test.** The first
> was a search that pruned exactly where the structure lived; the second was a mutation
> aimed exactly where the structure was not. **An instrument built around a design's
> generic case will be blind to its structured case in both directions** — and the only
> thing that caught either was a row whose expected value came from *outside* the
> instrument (the constructive witness).

### 3f. ⭐ THE LEAN PINS, MUTATION-TESTED — proved live by injection, not asserted

House law: *axiom pins mutation-tested*. `Selvage/CosetNovelTransform.lean` builds green
(**2 187 jobs**, warnings only, no `sorry`). To show its 23 `#guard_msgs … #print axioms`
pins are not decoration, a **single `sorry`** was injected into the proof of
`weftMix_no_invariantSet` **on a copy** (`lake env lean` on `/tmp/`, the shared worktree
never touched — verified clean afterwards):

```
warning: declaration uses `sorry`
'…weftMix_no_invariantSet'       depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
error: Docstring on `#guard_msgs` does not match generated message      <-- 1
'…weft_one_object'               depends on axioms: [propext, sorryAx, …]
error: Docstring on `#guard_msgs` does not match generated message      <-- 2
'…weft_one_object_satisfiable'   depends on axioms: [propext, sorryAx, …]
error: Docstring on `#guard_msgs` does not match generated message      <-- 3
```

⭐ **One `sorry` in the structural theorem turns THREE pins red — including the marquee
`weft_one_object`**, the "one function inhabits both the mixing and the encoding
interface" claim. The pins do not merely watch their own declaration; **`sorryAx`
propagates to everything that consumes it, so the apex claim cannot go green over a hole
underneath it.** That is the property `minted-behavioural-evidence-cannot-see-a-proof-hole`
says nothing else in this stack has: a differential test, a solver and a table are all
blind to an unproved lemma, and this is not.

### 3g. Block-constant trails at `|S| = 3` and at irregular partitions

`[MEASURED]` `notes/weft-c-scripts/weftc_trails3.py`, log `/tmp/weftc-trails3.log`. This is
the family the parent lane listed as **NARROWED, not closed** (`weft-coset-repair.md` §3d
item 3), extended from `|S| ≤ 2` to `|S| = 3` exhaustively plus 500 random irregular
partitions:

| start family | **Twill** | Weft-1 (killed) | ⚑ **Mark-32's OWN matrix** |
|---|---:|---:|---:|
| all `|S| = 3`, exhaustive (2 024) | **0 stalled** | **2 024 / 2 024** | 0 |
| random irregular partitions (500) | **0 stalled** | **500 / 500** | ⚑ **20 / 500, all at dim 12** |
| contiguous pairs `(0,1)(2,3)…(22,23)` (12) | **0 stalled** | — | ⚑ **12 / 12, all at dim 12** |

* **The instrument is live in both directions**: the killed form stalls on *every* start
  (its fixed lane), and **Mark-32's matrix stalls 20/500 on random irregular partitions and
  12/12 on the pair family** — so a clean 0 for Twill is a measurement, not a blind spot.
* ⚠ **And the arms are not interchangeable**: Mark-32 reads a clean **0/2024 at `|S| = 3`**,
  because a 3-subset start has block-constant hull of dimension 1 and explodes on the next
  step for any dense matrix. **Reading that 0 as "Mark-32 has no structure" would have been
  exactly the wrong conclusion** — its flag lives on the *pair* family, where it stalls
  12/12. The scan arm has to be aimed at the family the structure lives in.
* **Scope, stated:** `|S| = 3` is exhaustive; the 500 irregular partitions are a **sample**
  of a Bell(24)-sized space and are labelled so. `|S| ≥ 4` outside these families is
  **still open** (§4, U7).

---

## 4. THE LEGS WE CANNOT COMPUTE — named, with what would decide each

| # | leg | why it is not computable | what would decide it |
|---|---|---|---|
| U1 | **Gröbner / CICO solving degree** (leg 7) | no defense-side bound exists (Perrin); FreeLunch/CheapLunch explicitly do not model full-inverse layers | a solving-degree result for full-inverse-layer AO designs. **Nobody has one.** A CICO-`k` experiment at toy `t` and `R` extrapolated is what Mark-32 did and it is what its own §3.5.1 calls unproven |
| U2 | **`[TWILL-B]` — the `B` coefficients** | the spec **fixes** `β₀..β₃` by a derivation procedure (§1e), but the coefficient-grouping recurrence (Liu–Sarkar–Meier–Isobe) has **not been computed for the `B` it produces**, and this lane did not implement the recurrence | `O(n)` seconds of computation per candidate `B`, once implemented; a bad answer adds a third rejection condition to the procedure. Inherits `[M32-coeffgroup]`: Mark-32's `B` has **three** Frobenius terms (Chaghri-repair density) but at **adjacent** exponents `{0,1,2}` where the repair used spread `{0,2,8}`, and **nobody has computed it for that one either** |
| U3 | **integral / division property** `[WEFT-integral]` | the Beyne–Verbauwhede propagation is a large finite search; char-2 towers are the extreme point of their monotonicity axis and `x⁻¹` has maximal `F₂`-degree | their notebook at `t = 24`, GF(2³²), `R = 26`. Feasible, minutes-to-hours, **not run here** |
| U4 | **rebound / truncated differential** `[TWILL-rebound]` | no statement yet; the wide-trail bound does not cover it | an inbound/outbound analysis at this branch number |
| U5 | **`[TWILL-indiff]` / `[M32-mode]`** | inherits the open upstream `SpongeIndiffGame`; and Mark-32's own mode reading is unresolved (§1g) | the Lean sponge game, plus reading 2024/633 Figure 2 |
| U8 | **integral / monomial-prediction, via CLAASP-MP** | ⚑ **NOT a reach problem — Twill is cheap to express (§4a). The quantity the tool bounds is `F₂` degree, and `x⁻¹`'s is MAXIMAL, so it saturates in 2 steps and the bound is vacuous by construction** | nothing the tool can say; but the sibling lane's direct cube-sum measurement (`fct6`, with its `r=1` positive control) at 1/2/3 steps would confirm the derivation by measurement. **Cheapest open item in this note** |
| U6 | **general `K`-subspace trails** outside the coordinate and block-constant families | unbounded search space | a subspace-trail search framework for `K`-linear layers; not attempted, **not waived** |
| U7 | **block-constant trails at `\|S\| ≥ 4` outside the scanned families** | Bell(24)-sized family | §3g closes `\|S\| = 3` **exhaustively** (0/2 024) and samples 500 irregular partitions (0/500) with both controls firing; `\|S\| ≥ 4` outside those is **evidence, not exhaustion** |

### 4a. ⭐ The sibling CLAASP-MP lane's answer IS in — and it refutes half of my expectation

`notes/feistel-classical-tooling.md` landed while this note was being written (`e2764ef`).
Its subject is the gadget-Feistel, not Twill, but it read **CLAASP-MP's component vocabulary
at source** (eprint 2026/735 §3.3, Alg. 4, plus the installed tree), and that reading decides
our question too.

**What it found, `[READ at source]` and `[MEASURED]`:**

* CLAASP-MP's vocabulary is **bit-level over F₂**: XOR, AND, NOT, OR, COPY, ROTATE, SHIFT,
  **S-box (via its ANF)**, **linear layer (an F₂ matrix)**, MODADD, MODSUB, FSR, and a
  `(x·y) mod 2ⁿ` model.
* The gadget-Feistel **is** expressible — exactly, verified against its spec — but its dense
  public-constant combination over `Z_q` with `q` a **64-bit prime** has no primitive in any
  classical tool and costs **14.5 M components and 943 M wire bits per round**. ChaCha, the
  paper's headline target, is 512 bits of state.
* ⚑ And the scale wall did not decide it. **The quantity CLAASP-MP bounds — the F₂ algebraic
  degree — is already saturated after one round**, measured directly by cube sums on the real
  primitive: the only integral property that exists is the trivial 1-round Feistel branch copy
  (`1024/1024` against a chance baseline of `2.0` — the harness's own positive control), and
  at `r = 2, 3` nothing survives above chance. **So the tool would return "no distinguisher"
  after a 10⁹-variable solve that 2¹⁶ evaluations settle in 18 seconds.**

### ⚑ MY EXPECTATION WAS WRONG ON EXPRESSIBILITY AND RIGHT ON USEFULNESS — for a different reason

The brief carried, and an earlier draft of this section repeated, that *"`x⁻¹` over a tower is
closer to Vision than to a Feistel — so classical bit-level tooling may NOT reach this one."*
**Read against CLAASP's actual vocabulary, that is backwards.**

| Twill layer | in CLAASP | cost |
|---|---|---|
| the mixing layer `M` | it is `K`-linear, hence **`F₂`-linear on the 768-bit state** | ⭐ **ONE `linear_layer` component**, a 768×768 `F₂` matrix |
| `B` and `B⁻¹` | linearized affine ⇒ **`F₂`-linear**, and 2024/633 Algorithm 2 *already gives the `GL₃₂(2)` matrix* | ⭐ **ONE component each**, 32×32 |
| `x⁻¹` over GF(2³²) | not a table (2³² entries), but the tower inversion is a bounded recursive AND/XOR circuit | hundreds of components per lane |
| round constants | XOR of a constant | free |

> ⭐⭐ **Twill is CHEAPER to express in CLAASP than the gadget-Feistel by orders of magnitude,
> and the reason is structural: CLAASP's ground field is `F₂`, and so is Twill's.** The thing
> that cost the gadget-Feistel 14.5 M components — a dense combination over a **prime**-order
> ring — **does not exist in Twill.** Two entire layers that would be the expensive part of an
> AO hash collapse to one component each, because *linearized* is exactly what CLAASP's
> `linear_layer` primitive means.
>
> ⚑ And the sibling lane's measured tool defect — **CLAASP's `modulus` field never reaches any
> constraint model**, with `check_anf_correctness` missing the divergence at `p = 0.54` — is
> **irrelevant to us**, because a char-2 primitive never sets a modulus.

**And it still buys nothing, for the sibling lane's own reason, harder.** `x⁻¹` has `F₂`-degree
**31 — maximal** — so one S-box layer takes every lane's degree to the top, and the mixing layer
(full support from any single lane, `f(1) = 24`, §3c) spreads it across the state in one more.
`deg(f∘g) ≤ deg f · deg g` gives `31² = 961 > 767` after **two steps**. CLAASP-MP computes an
**upper** bound on that degree, and an upper bound is never below the exact value — so wherever
the exact degree already equals the cube dimension, **the tool cannot certify an integral
distinguisher no matter how well the MILP is solved.** The leg would return **`NR ≥ 2`**: the
same "sets nothing" the sibling lane got, reached without the scale wall.

> ⚑ **The transferable law, and it is sharper than "classical tools reach classical designs":**
> **a classical automated tool's reach is decided by two things, and neither of them is whether
> the design "feels" classical — (i) is the tool's ground field the primitive's ground field,
> and (ii) is the quantity the tool bounds still MOVING at the round counts you care about?**
> The gadget-Feistel fails (i) and (ii). **Twill passes (i) perfectly and fails (ii) on
> arrival** — and failing (ii) is the *design's* doing, not the tool's: a maximal-`F₂`-degree
> S-box is chosen precisely so that degree-based analysis dies immediately.
> ⚠ **Which is a security property and an analysability cost at the same time**, and the second
> half is the one nobody says out loud. Per `feedback-every-instrument-is-blind-to-the-next-wound`:
> **three instruments reporting "nothing here" is one fact about our instruments, not three
> about the primitive.**

**What would still be worth running, and it is the cheapest open item in this note:** the
sibling lane's `fct6` method — direct cube sums by Möbius, with its own `r = 1` positive
control — pointed at Twill at 1, 2 and 3 steps. It needs no MILP, no CLAASP install and no
solver; it is `2^m` evaluations of the permutation. **It would confirm the two-step derivation
above by measurement instead of by a degree-composition bound, and it would say so in an
afternoon.** It is not run here.

---

## 5. THE COMPARISON TABLE — and the last column is the whole argument

### 5a. The four objects

| | **Twill** | **Vision Mark-32** | **Poseidon2 (deployed)** | **gadget-Feistel** |
|---|---|---|---|---|
| field | GF(2³²) tower | GF(2³²) tower | BabyBear (31-bit prime) | `Z_q[X]/(X¹⁶+1)`, `q ≈ 2⁶⁴` |
| rung | char-2 | char-2 | prime | ring |
| `t` / rate / cap | 24 / 16 / 8 | 24 / 16 / 8 | 16 / 8 / 8 | `(L,R) ∈ R_q⁴ × R_q⁴` |
| S-box | `x⁻¹`, all lanes | `x⁻¹`, all lanes | `x⁷`, full + partial | base-`B` digit products |
| mixing | ⭐ **1-pass coset novel transform** | 2-pass systematic-RS `V₂V₁⁻¹` | `M_E` / `M_I` | dense-in-planes `F_r` |
| branch `B_d` | **8** EXACT, attained | **25** by RS theorem | 8 EXACT (`M_E`) / **2** (`M_I`) | n/a — no MDS |
| structural flag | **none** | ⚑ **12 ⊃ 6 ⊃ 3** block-constant | none | n/a |
| subfield set | **none** (full-field `x*`) | ⚑ **GF(2⁸)**, a 2¹⁹² set | none | n/a |
| `deg(minpoly)` | **24** | **6** | — | n/a |
| min active S-boxes over 4 steps | **≥ 17** `[MEASURED]`, ≥ 22 on the cheap route | **≥ 50** (generic, from `B_d = 25`) | — | measured full diffusion in 2 rounds |
| skip-family absorption | **≤ 1 step** `[DERIVED]` | ≤ 1 step | ⚑ **100% of `R_P`** `[MEASURED]` | 1 round `[MEASURED]` |
| **S-box layers** | **26** | **16** | 21 (`R_F=8`, `R_P=13`) | 16 rounds |
| **S-boxes / perm** | **624** | **384** | 141 | — |
| native mixing, software mult-count | **80 mults/step** | 160 mults/step | — | — |
| native, Mark-32's own FPGA split | — | S-box **80.4%**, MDS **18.4%**, `B` **1.2%** | — | — |
| in-circuit | ⚠ **unmeasurable — no char-2 AIR exists** | ⚠ same | **300 cells/perm, 1.21 cells/bit** `[repo figure]` | **92 257 constraints, 4.0% of circuit** |

### 5b. ⭐⭐ WHERE EACH ROUND COUNT COMES FROM — the column nobody else fills in

| design | rounds | **DERIVED FROM** |
|---|---:|---|
| **Twill** | **26 steps** | ⭐ **COMPUTED, leg by leg, §2**: three EXACT-DEFENSE legs measured and exhausted (`B_d` certified, `B_l` floor proven, zero invariant subspaces/quotients at every level in Lean); one EXACT-ATTACK leg derived (no partial rounds ⇒ the skip family absorbs ≤ 1 step); three legs inherited from Mark-32 and **labelled as inherited**; the binding one **corrected outward by a stated empirical prior**; ×2 unknown-attack margin. **Every leg's requirement stated separately and its instrument named.** |
| Vision Mark-32 | 16 steps<br>(**20 by its own strategy's floor**) | **DESIGNER ASSERTION, BELOW ITS OWN FLOOR**: Table 1 lists five attacks against "required number of rounds" **1, 1, 2, 4, 3** with **no derivation shown for any of them**, then applies `N = 2·max = 8 rounds`. ⚑ But the strategy it cites (Marvellous, 2019/426 §4.5/§5) says *"`2⌈n/5.5m⌉` rounds, **with a minimum of 10 rounds**"*, and at `m=24, n=128` the formula is vacuous so **the floor of 10 is the whole number** — a floor the designers put there because their own Gröbner extrapolation was fitted on *"small round numbers"*. **Mark-32 ships 8.** §2h. ⚠ Zero attack papers, and nobody has looked (`hash-landscape.md:619`). |
| Poseidon2 (deployed) | 21 | **PRECEDENT + AN ARBITRARY MARGIN, self-described**: 2019/458 §5.4 verbatim — *"we **arbitrarily** decided to add … two more rounds with full S-box layers, and 7.5% more rounds with partial S-box layers."* ⚑ And measured against GSR, **all 13 of our partial rounds buy zero** (`R_P = 13` sits **below** the kink `t − 2k = 14`). ⚠ The stated margin is **7.5% in §3.2 and 12.5% in §7.3 of the same document**, with the flattering figure used in the argument that a known attack is absorbed. |
| gadget-Feistel | 16 | **PRECEDENT, and our own note says so**: the HKT 14-round indifferentiability result for 2-branch Feistel **with ideal round functions**, plus margin — and nothing about `F` is an ideal round function. ⚑ The pipeline computed every leg it can and **they are all satisfied at NR ≈ 2–3**; the binding leg (order-2 / MITM / boomerang) is **OPEN**, so *"the computed line does not justify NR=16 and does not refute it — it says nothing."* |

> ⚑ **That column is the entire argument for building anything ourselves.** Three of the
> four numbers are precedent or assertion; one is a derivation with every leg labelled. It
> does not make Twill *safer* than Mark-32 — it makes Twill **arguable**, and Mark-32 is
> not, because there is nothing published to argue with except a five-row table.

### 5c. The cost comparison, honestly, in two currencies that disagree

⚑ **Our own record contains two contradictory native-cost models and both are in the
repo.** They must not be quoted interchangeably.

| model | says | why |
|---|---|---|
| **software multiplication count** (`weft2.md` §6c) | **mixing dominates**: at 8 rounds, 640 mixing mults vs 303 S-box mult-equivalents — 68% mixing | on a CPU/GPU, multiplication by a **constant** in GF(2³²) costs about the same as a general multiplication |
| **Mark-32's own FPGA LUT count** `[READ]` Table 3 | ⚑ **the S-box dominates**: inversion **40.2 k**, MDS **9.2 k**, both `B` layers **0.6 k**, of **50.0 k LUT per round** — 80.4% S-box | in hardware a **constant** multiplication is an XOR tree; their 24×24 MDS costs ≈ 8.8 general-multiplier-equivalents, not 576 |

**Consequence for Twill's headline saving.** The one-transform coset form halves the mixing
work relative to the two-transform RS form:

* **software**: `1.68×` per permutation at equal round count (`weft2.md` §6c) — this is the
  figure that matters for **Merkle-tree building in STARK proving**, which is where native
  hashing throughput actually binds.
* **hardware**: the mixing is 18.4% of a round, so halving it saves **≈ 9% of a round** —
  the `1.68×` becomes about `1.10×` at the permutation level.

⚑ **And then the round counts must be composed with it, which nobody has done:**

```
Twill  at 26 steps, 1 pass  :  26 x 80  = 2080 mixing mults + 624 x 1.58 =  986  ->  3066
M32    at 16 steps, 2 pass  :  16 x 160 = 2560 mixing mults + 384 x 1.58 =  607  ->  3167
M32    at 20 steps, 2 pass  :  20 x 160 = 3200 mixing mults + 480 x 1.58 =  758  ->  3958
       (= its own strategy's 10-round floor, sec.2h)
                       ratio Twill : M32-as-shipped  =  0.97x
                       ratio Twill : M32-at-its-floor =  0.77x
```

⚑ **The 160 mults/step for Mark-32 is the reading most favourable to it**, and it is the
one used above: it prices `A = V₂V₁⁻¹` as **two LCH passes**, which is only available
because Mark-32's point split is coset-structured. Implemented as the dense 24×24 matmul it
literally is, the same layer costs **576 mults/step** and Mark-32 lands at 9 216 + 607 =
9 823, i.e. **Twill would read 0.31×**. ⭐ **And that is the same fact as §6, from the cost
side: Mark-32's MDS is fast *because* its point split is a coset union, and a coset union is
*exactly* what creates the flag. The speed and the structure are one property.**

> ⭐ **Twill at its own derived 26 steps costs slightly LESS natively than Mark-32 at its
> asserted 16, and 23% less than Mark-32 at its own strategy's floor of 20** — on the
> software mult-count model — while carrying 1.63× the S-boxes, a repaired mixing layer,
> and a stated derivation. `[DERIVED]`, from two measured inputs (80/160 mults per pass;
> inversion = 1.58× a multiplication).
> ⚠ **On the hardware model the same composition reads ≈ 1.5× against us** (≈ 1.2× against
> Mark-32-at-its-floor), because there the S-box is 80% of the cost and we buy 63% more of
> them. **Say the unflattering one out loud: on FPGA, Twill's derived round count is the
> expensive choice, and the mixing saving that motivates the whole design is worth ~9% of a
> round.** The software figure is the one that matters for STARK proving (Merkle-tree
> building on CPU/GPU); the hardware figure is the one that matters for Mark-32's own
> stated target, which is an Alveo card.

### 5d. Cells: the number that cannot be quoted

⚠ `post-weft-hash.md` §4 item `[M32-cells]` carries *"≈ 200–400 cells at R = 8"* as
`[DERIVED, shape-level]`. **That figure is wrong on two counts**: it uses 8 S-box layers
where Mark-32 has 16, and it prices the `x⁻¹` relation without the `B` layer's auxiliary
cells. A corrected shape-level figure is `t · R · (aux per S-box)` = `24 · 16 · 3 = 1152`
for Mark-32 and `24 · 26 · 3 = 1872` for Twill — **but only if `F₂`-linear maps cost cells
in the eventual AIR, and nobody has emitted it.** If squaring is free in a Binius-shaped
tower AIR the figures are `384` and `624`.

> ⚑ **A range of 384–1872 is not a measurement, and the `~3.2× cells/bit` headline
> (`weft2.md` §8) rests on the low end of it plus a round count nobody had computed.**
> **The honest state: cells/bit for any char-2 design is unmeasurable today.** It becomes
> measurable on the day scenario C opens and a Lean-authored AIR is emitted — not before.

---

## 6. ⚑⚑ `[M32-flag]` CLOSED — the adoption target reaches our own flag

`weft-coset-repair.md` §5 handed forward a cheap obligation: *read Mark-32's actual Sage
point split and test whether both point sets are unions of cosets of a common subspace.*
**Done, at source, and then verified against the matrix.**

### 6a. The split, from the paper's own listing `[READ: 2024/633 §3.3]`

Code Listing 3 builds `W_i` as **subset sums** of `U[i]` and truncates
`W.append(W_i[: 2*self.m])`; Code Listing 4 builds `X[j]` for `j in range(2*m)`. So the
generator's columns are `ω₀ … ω_{2m−1}` **in the standard binary-expansion order**, with
`ω_j = Σ_i j_i β_i` and `β_j = mds_field.from_integer(2^j)`. RREF then makes the **first
`m`** columns systematic. Therefore:

> **Mark-32's point split is the NATURAL one: message points `ω₀..ω₂₃`, parity points
> `ω₂₄..ω₄₇` — i.e. the integers `0..23` and `24..47`.** No assumption; it is what the
> listing computes.

**And the paper says it in prose too**, `[READ]` §3.3, verbatim — so this does not rest on
reading Sage:

> *"The result of RREF has the identity as its left-hand half and our desired MDS matrix on
> the right. … it's the extrapolation matrix, which takes the values of some polynomial of
> degree less than `m` on the set `ω₀, …, ω_{m−1}`, and returns the evaluations of the same
> polynomial on `ω_m, …, ω_{2m−1}`."*

⚑ **`post-weft-hash.md` §3 flagged the split as `[ASSUMED here: 0..23 / 24..47 — re-read
Mark-32's Sage listing before adopting verbatim]`. The assumption was right, and it is now
`[READ]`.** ⚠ Which is the uncomfortable half: **the sibling lane's flagged assumption
turned out to be the load-bearing one, and holding it as an assumption for a day is how a
2¹⁹² subfield set and a 3-deep invariant flag sat unnoticed in a candidate we had already
ranked first.**

### 6b. The consequence, measured on the matrix

`[MEASURED]` `weftc_legs.py` L1:

| | `U₁` (\|W\|=2) | `U₂` (\|W\|=4) | `U₃` (\|W\|=8) | `U₄` (\|W\|=16) |
|---|---|---|---|---|
| `P₁ = 0..23` a union of `W`-cosets | **yes** | **yes** | **yes** | no |
| `P₂ = 24..47` a union of `W`-cosets | **yes** | **yes** | **yes** | no |
| predicted invariant dim `t/\|W\|` | **12** | **6** | **3** | — |
| `A = V₂V₁⁻¹` preserves it, verified | ⭐ **yes** | ⭐ **yes** | ⭐ **yes** | — |

and alongside it:

* `[MEASURED]` **`A`'s entries lie in GF(2⁸)** (subfield level 3) — every one of the 48
  points is an integer `< 64`, hence in `T₃ = GF(2⁸)`, so `(GF(2⁸))²⁴`, **a 2¹⁹² set, is
  closed under Mark-32's mixing layer**. `x⁻¹` maps every subfield into itself, so the only
  escape is the round constants and the `B` coefficients — **which the paper does not
  publish in this document, so the escape is an accident of instantiation that we cannot
  even check.**
* `[MEASURED]` **`deg(minpoly)(A) = 6`**: the Krylov space from any single lane is
  6-dimensional, so *every* choice of S-box lane leaves an 18-lane subspace on which a
  partial round would be linear. ⚠ Not a break of Mark-32, which has no partial rounds —
  but it is decisive for architecture, and Twill reads **24**.
* **CONTROL, and it is what makes the row live**: a **random** (non-coset) 24-point parity
  set gives **no flag, full-field GF(2³²) entries, and `deg(minpoly) = 24`** — MDS with
  none of the structure. `[MEASURED]` And it is an `O(t²)` matmul, which deletes the entire
  alignment thesis. **The structure is the price of the fast transform.**

### 6c. What it is and what it is not

* **Not a break.** It is an invariant **subspace**, so a round constant outside it breaks
  it — unlike an invariant *quotient*, which constants merely re-parameterise. **This note
  does not claim a break of Vision Mark-32.**
* **It is the attacked shape.** 2026/306 turned the analogous structure into **2¹⁰⁶** on
  Poseidon2 *despite* round constants, via round-skipping degrees of freedom.
* ⚑ **And it is present by construction, in the object our own gate blessed at branch 25.**
  `post-weft-hash.md` §7's closing law was *"the passes are a floor instrument, not an
  identity instrument."* Its sharper form, now confirmed against the deployed matrix:
  **the passes are not a STRUCTURE instrument either, and MDS is not a structure
  certificate.**

### 6d. What it does to the standing recommendation

`post-weft-hash.md` §7 ranks **adopt Vision Mark-32** first, on an epistemic-flywheel
argument: *an unanalyzed published design accumulates analysis and an unanalyzed private
one does not.* **That argument survives and this note does not overturn it.** What changes:

1. The adoption is **no longer free of obligations we already know about**. `[M32-flag]` is
   now a **measured defect of the deployed matrix**, not a question. It joins
   `[M32-coeffgroup]`, `[M32-integral]`, `[M32-groebner]`, `[M32-indiff]`, `[M32-age]`,
   `[M32-cells]` — and this note adds three: **`[M32-subfield]`** (GF(2⁸) entries,
   measured), **`[M32-mode]`** (§1g), and **`[M32-floor]`** (ships 8 rounds where its own
   strategy floors at 10, §2h).
2. ⚑ **The free repair exists and is one line of the spec**: shift one point set by a
   full-field element. The points stay distinct, so the RS/MDS theorem is untouched, and
   the entries go to GF(2³²). ⚠ **It repairs the subfield and NOT the flag** — the
   translate split still carries `12 ⊃ 6 ⊃ 3`, and worse, `A² = I` with
   `rank(A + I) = 12`: **half the state fixed POINTWISE by an MDS layer**
   (`weft-coset-repair.md` §1c). **There is no free repair for the flag that keeps the fast
   transform.**
3. ⭐ **The cheapest action on the adoption path is not a cryptanalysis, it is a round
   count.** `[M32-floor]` costs 25% and restores compliance with the design strategy
   Mark-32 cites. **Adopt-Mark-32-at-10-rounds is a strictly better object than
   adopt-Mark-32, at a price we can state**, and it does not need a single new result.
4. **So the fork is now real and it is ember's** (CLAUDE.md category 4, taste):
   *adopt a published design with a measured structural defect, a round count below its own
   strategy's floor, and an empty analysis record — or build one with the defect repaired, a
   computed round count, and no record at all.*
   **This lane's job was to make that fork visible with both sides priced, and it is.**
   ⚠ **And the honest weighting has not changed**: an unanalyzed *published* design
   accumulates analysis and an unanalyzed *private* one does not. **Nothing measured here
   beats that, and this note does not claim to.**

---

## 7. ⚠ THE STANDING VERDICT, RESTATED — unchanged, and not this lane's to overturn

> `post-weft-hash.md` §1 and §7, `[READ]` — ***"Now: build nothing."***

**The char-2 hash slot does not currently exist.** Scenario C — a char-2 circuit verifying
char-2 proofs — is the only home a Weft successor could have, and it lacks its entire
substrate: **no char-2 AIR, no constraint evaluator, no witness-gen**
(`post-weft-hash.md` §1's routability grep: `minidregg/prover/src/` holds fold/NTT/sumcheck/
tower kernels and no circuit; breadstuffs' GF(2) hits are all FHE-side). Scenario A
(terminal binary proofs) keeps cSHAKE256; scenario B (recursion in the deployed BabyBear
wrap) takes the deployed Poseidon2 plus a ~1.03–1.94× packing codec, and its real open cost
— fold emulation, 1–30% of a wrap — is **hash-independent**.

**This lane makes the object ready and defensible, not deployed.** Twill is specified to
the point where a second implementer can build it and an attacker can attack it, its round
count is derived rather than asserted, and its computable legs are run. **None of that is a
reason to build it, and this note is not one.**

⚑ **And the code-side half survives regardless of whether the slot ever opens**
(`weft-coset-repair.md` §5): `cosetPack` **is** the additive-code encoder on a shifted
domain — evaluating a BaseFold/FRI codeword on a coset rather than on the interpolation
window is ordinary practice, and `cosetPack_succ` `[LEAN]` prices it at **the same butterfly
network, precomputed shifted twiddles, no extra operation**. The window bijection
(`cosetPack_injective_of_natDegree_lt`, `_surjective_on_window`,
`exists_unique_table_cosetPack`) carries the property the additive BaseFold descent runs on
to the shifted domain. **That half is not conditional on anything in this note.**

---

## 8. OBLIGATION-TABLE UPDATES

* ⚑ **`post-weft-hash.md` §4 `[M32-flag]`: CLOSED — and it closes as a CONFIRMED DEFECT**
  (§6). Read at source, verified on the matrix, with a random-split control.
* ⚑ **NEW `[M32-subfield]`**: Mark-32's MDS entries lie in **GF(2⁸)**; `(GF(2⁸))²⁴` = 2¹⁹²
  is closed under the mixing layer and the S-box layer. Escape depends entirely on the `B`
  coefficients and round constants, **which 2024/633 does not publish**. `[MEASURED]`
* ⚑ **NEW `[M32-mode]`**: the §3.4 prose describes a construction that, read literally, is
  a chop-MD with a 256-bit chaining value rather than a sponge. **Text-only reading, NOT
  asserted** — needs Figure 2 or the reference implementation (§1g).
* ⚑⚑ **CORRECTION to `weft2.md` §6c and `post-weft-hash.md` §4 `[M32-cells]`: Mark-32's
  "8 rounds" is 16 S-box layers / 384 inversions**, `[READ at source]` Algorithm 1 and
  §4.2's own op count. The `192 S-boxes` row is wrong by 2×, and the `~200–400 cells` and
  `~3.2× cells/bit` figures inherit the error (§5c–5d).
* ⚑ **CORRECTION to `weft2.md` §6c's cost conclusion**: *"the mixing layer dominates the
  native cost, not the S-box"* is true of the **software multiplication-count** model and
  **false on Mark-32's own FPGA numbers**, where the S-box is 80.4% and the whole MDS is
  18.4%. Both models are now in the record with their instruments named (§5c).
* ⭐ **`[WEFT-multiround]` trail half — the 4-step active count is now a NUMBER, and it is
  better than the generic bound**: **≥ 17** (16 not attained), and **≥ 22** along the
  cheapest 2-step route (§3d–3e), by an exact enumeration of all eight weight-4 codewords
  whose completeness argument (`deg p = max(A) ≥ 20`) is a theorem. The exact value is
  still open.
* ⭐ **`|S| = 3` block-constant partitions: CLOSED exhaustively** (0/2 024), plus 500 random
  irregular partitions (0/500), both with controls that fire (§3g). `|S| ≥ 4` outside those
  families and general `K`-subspaces remain **NARROWED, not closed**.
* ⚑ **NEW `[M32-floor]`**: Mark-32 ships **8 rounds** where the Marvellous strategy it cites
  floors at **10** (`2⌈n/5.5m⌉` with a stated minimum of 10, eprint 2019/426 §5). At
  `m = 24` the formula is vacuous, so the floor was the whole number. **Adopting Mark-32 at
  10 rounds costs 25% and restores compliance with its own strategy** (§2h).
* **NEW `[TWILL-B]`**: the linearized affine coefficients are **fixed by a derivation
  procedure** (§1e), but the coefficient-grouping recurrence has not been computed for the
  `B` it produces; a bad answer adds a rejection condition (§4, U2).
* **NEW `[TWILL-rebound]`**: the wide-trail rows are characteristic bounds and do not cover
  rebound/truncated routes (§2b).
* **NEW `[TWILL-indiff]`**: inherits the open `SpongeIndiffGame` (§1g).
* **`weft2.md` §8's free conditions are now NORMATIVE SPEC CONDITIONS**, all four (§1c).

---

## 9. REPRODUCE

```bash
cd ~/dev/zkml-research/notes/weft-c-scripts && python3 -u weftc_legs.py       # ~12 min
cd ~/dev/zkml-research/notes/weft-c-scripts && python3 -u weftc_legs.py --fast   # skips wt-3
cd ~/dev/zkml-research/notes/weft-c-scripts && python3 -u weftc_trails3.py    # ~1 min
cd ~/dev/minidregg && lake build Selvage.CosetNovelTransform && lake build    # the Lean
cd ~/src/ring-ro-hash && python3 weft_coset_repair.py                         # the parent lane
```

⚠ **Two operational notes paid for in this lane.** (1) `pgrep -f weftc_legs` **matches the
waiting shell that contains the string**, so an `until ! pgrep …` loop never exits — the
recorded self-match class (`minted-the-wrapper-answers-for-the-work`), hit again. Match on
`weftc_legs\.py` and count. (2) Python buffers stdout when redirected; without `-u` a log
file stays at **0 bytes** for the whole run and a live job looks dead.

**Provenance.** Read at source this lane: eprint **2024/633** (Vision Mark-32) §2.1 (the
round), §3.1 (inversion, 1.58×), §3.2 + Algorithm 2 (`B` as a `GL₃₂(2)` matrix), §3.3 +
Code Listings 2–4 (the point split), §3.4 (the mode), §3.5 + Table 1 (the round-count
table), §4.1 Table 2 and §4.2 Table 3 (the FPGA costs, and the 48-inversions-per-round
line); and eprint **2019/426** (Marvellous) §4.5 (the `2ℓ`, minimum-10 rule and the
"small round numbers" extrapolation), §5 (the Vision formula) and Figure 1 (*"A single
round (two steps) of Vision"*).

**Quoted from prior lanes, not re-measured here**: the `B_d = 8` attaining witness's
construction, `B_l ≤ 10`, the 0/370 vs 117/370 block-constant trail scan at `|S| ≤ 2`, the
Lean theorem list, the `1.68×` / 80-vs-160 software mixing figures and the `1.58×`
inversion cost, the deployed Poseidon2 and gadget-Feistel figures, the pipeline's six
outward-correction instances.

**Measured here**: `[M32-flag]`, `[M32-subfield]` and `deg(minpoly) = 6` on the actual
Mark-32 matrix, with a random-split control that shows none of the three; the exact 2-step
transition profile `f(1), f(2), f(3)` on **both** sides for Twill and for the killed form;
the `B_d ≥ 8` and `B_l ≥ 8` floors re-run on all four matrices; the complete weight-4
codeword enumeration (8 codewords, closed form, no 2-edge chain), the onward minimum
`≥ 13`, and the perturbation guard (8 → 6); the `|S| = 3` and irregular-partition trail
scans with both controls firing.

**Derived here, labelled**: the leg-by-leg round count and the `×2.1` outward-correction
prior; the `K*`-equivariance argument for keeping `B`; the skip-family absorption bound for
an all-full-round design; the two native-cost compositions; the CLAASP-MP instrument-fit
expectation.

**Corpus disclosure**: no absence claim in this note rests on the eprint mirror. The two
"nobody has computed X" statements (`[M32-coeffgroup]`, `[M32-floor]`'s justification) are
statements about **the cited papers' own contents**, read at source, not about the
literature at large.
