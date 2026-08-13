# fold_add as an opening, not a circuit — spec, build, and the honest ratio

**Lane**: design + build. Started 2026-08-13. Written incrementally.
**Claim under test** (from `notes/prover-floor.md` §"Correction to my own brief"):
`fold_add` is linear, MLE is linear, therefore `c_out = Σₖ aₖcₖ ⟹ ĉ_out = Σₖ aₖĉₖ`
**as polynomials**, so one common-point opening certifies the whole fold — zero
sumcheck rounds. AIR cost Θ(B·N·L), linear route Θ(N·L), **ratio = B**.

**Verdict**: the *algebra* holds and is now demonstrated on real deployed-shape
ciphertexts. Everything else in the source claim needs revising.

- **Three of the four headline numbers are wrong or mis-attributed** (§0).
- ⚑ **The brief's premise is FALSE.** "Nobody has applied this to FHE ciphertext folding"
  — Zama **2024/451** proves exactly `ĉ = Σ wᵢcᵢ` with fixed public weights *the circuit
  way*, and Zama **2026/027** proves linear maps on GLWE ciphertexts *the MLE way*. **Both
  PDFs are in `~/paperbin`.** And the Layer-A fact is stated almost verbatim in the
  Binius64 Blueprint, also in `~/paperbin` (§5).
- ⚑ **The ratio claim has a hole I did not price**: it is prover-side only, and the
  verifier moves the *opposite* way — `O(B)` openings against `O(polylog)` for the AIR
  route — in direct tension with binding condition (c) (§4.4).
- ⚑ **The stub is a shipped-bug class**, not a toy caveat: consuming claimed evaluations
  without checking them against commitments is the OtterSec/Dusk PLONK defect, ~$60M
  (§3).

**What survives is narrow, real, and worth having**: a batch fold is *aligned-pointwise,
not a contraction*, so even the sumcheck the state of the art runs is unnecessary (§5.3).

---

## 0. Corrections to the brief, stated first

| brief said | measured / read | where |
|---|---|---|
| "690× at B=512" | **B=512 is not a deployed shape.** The node's fold batch is **B=4** (`ORDER_COUNT : Nat := 4`, `metatheory/Market/DarkBazaarPrivateDescriptor.lean:44`), pinned by the session roster and the fixed-arity proving family. Deployed ratio is **4.2×**; 715× at B=512 is confirmed but is a batch we do not run. | §4 |
| "h2 measured lazy accumulation at 0.88×" | **Wrong cell** (0.88× is *single-prime-109-bit lazy ÷ RNS-3-limb lazy*), and then **measured in-tree**: lazy is 0.84× at B=256 but **break-even at the deployed B=4**. The direction holds on two instruments; the free-speedup argument does not hold at the batch we run. | §6 |
| "zero carries, zero range checks" | Zero *in the fold relation*. The Θ(N·L) term in "the linear route is Θ(N·L)" **is** the one-time canonicalisation range-check on the result. The reduction is not eliminated; it is performed **once instead of B times**. That is the whole mechanism and it should be said that way. | §2.5 |
| "one common-point opening certifies the whole fold" | True, but only under an accounting where the **inputs are already committed**. Under total-system accounting both routes are Θ(B·N·L) and the ratio is the per-add column count, not B. Both accountings are legitimate; they answer different questions. | §4.2 |

---

## 1. What is actually deployed (read, not assumed)

Read from the tree at `08f0df18b`.

**The operation.** `fhegg-core/src/bfv_lean.rs:539` `fold_add(a, b, t)` — RNS
coefficient-wise modular add of two 2-polynomial BFV ciphertexts, with a wrap gate
that *refuses* when `a.plain_bound + b.plain_bound ≥ t`. `fold(cts, t)` (line 558)
left-folds it. `add_row` (line 497) is `s = a+b; if s >= q { s - q }` — **it reduces at
every step.** Lazy accumulation is therefore a *change* to this function, not a
description of it.

**The shape.** `FOLD_DEGREE = 4096`, `FOLD_MODULI = [0xffff_ee001, 0xffff_c4001,
0x1_ffff_e0001]` — L=3 RNS primes of 36/36/37 bits, P=2 polynomials.
So one ciphertext = **P·L·N = 2·3·4096 = 24,576 residues** = 98,304 bytes at u32-per-
residue, matching the `h2-verdict.md` "ciphertext in RAM 98,304 B" row.

**The coefficients `aₖ`.** In the deployed path they are **0/1 side selectors**, not
general weights. `additive.rs:210` partitions `rows` by `row.side` into `demand_rows`
and `supply_rows`, then folds each side. So the two folds are

```
c_demand = Σₖ [sideₖ = Bid]·cₖ        c_supply = Σₖ [sideₖ = Ask]·cₖ
```

with `aₖ ∈ {0,1}` and `a^demand + a^supply = 1` componentwise. **`side` is a plaintext
field of the signed order envelope** — so the coefficient vector is public and is
already bound by the trader's Ed25519 signature. That is a *gift* for binding
condition (a) in §2, and it means the deployed instance is strictly easier than the
general weighted-fold statement.

**The batch size B.** `node/src/dark_clearing_service.rs:135` takes `FAMILY_ORDERS`
from `dregg_circuit_prove::dark_bazaar_private::ORDER_COUNT`, which the Lean descriptor
`metatheory/Market/DarkBazaarPrivateDescriptor.lean:44` fixes at **4**. The emitted
descriptor is `circuit/descriptors/by-name/dark-bazaar-private-n4k4.json`, trace width
181, 12 public inputs.

⚠ Precision about the enforcement, because my first draft over-stated it: line 383
(`family_counts_agree`) is a **drift check** — it refuses when the descriptor *name*'s
`n{N}k{K}` disagrees with the compiled constants, which is what stops the constants
sliding away from the emission. What pins B=4 per session is the roster
(`OpenSessionRequest.traders` is "exactly `FAMILY_ORDERS` hex Ed25519 verifying keys")
together with the fixed-arity proving family. Both are real; neither is a runtime
`if orders != 4` on submission, and it is worth saying which is which.

⚠ So **the deployed B is 4, and it is enforced, not incidental.** The B=512..10⁵
numbers that circulate come from `fhegg-fhe/src/bin/gpu_resident_bench.rs`, which sweeps
N = 10³..10⁵ as a *GPU arena capacity* study. That is a harness bound, not a batch the
node ever folds. Any "690×" statement must name which of these two it prices.

---

## 2. The statement, in the shape a Lean theorem would take

### 2.1 Objects

Let `F` be the proof field (BabyBear, `p = 2^31 − 2^27 + 1`) and `E = F⁴` the degree-4
extension (`|E| ≈ 2^124`).

A ciphertext `c` is a vector of `M = P·L·N` residues, the `(π, j, i)` entry lying in
`Z_{q_j}`. Since `q_2 ≈ 2^37 > p`, a residue **does not fit in `F`**. Fix a limb radix
`2^w` and a limb count `λ = ⌈log₂ q_max / w⌉`; the deployed choice is `w = 19, λ = 2`.
Define

```
limbs : Π_j Z_{q_j} → F^λ ,  limbs(v) = (v mod 2^w, ⌊v / 2^w⌋)
flat  : Ciphertext → F^{M·λ}     -- fixed, public, injective-on-canonical index order
```

Let `μ = ⌈log₂(M·λ)⌉`. Deployed: `M·λ = 49,152`, `μ = 16`, padded length `2^16 = 65,536`.
For `x ∈ F^{2^μ}` let `x̂ : E^μ → E` be its multilinear extension.

### 2.2 The relation

```
FoldOpen(B) :
  public   : commitments C₀..C_{B−1}, C_out ; coefficients a₀..a_{B−1} ∈ F ; bound Bnd
  witness  : ciphertexts c₀..c_{B−1}, c_out
  asserts  : (1) Cₖ = Commit(flat(cₖ)) for all k, and C_out = Commit(flat(c_out))
             (2) flat(c_out) = Σₖ aₖ · flat(cₖ)             -- over F, componentwise
             (3) every entry of flat(c_out) is < Bnd, with Bnd ≤ p     -- ⚑ the range leg
```

and the FHE-side meaning is recovered by (2)+(3) together, never by (2) alone.

### 2.3 The protocol

```
1. prover  → commits C₀..C_{B−1}  (in practice: already committed, at ingress)
2. prover  → commits C_out
3. verifier: r ← E^μ  drawn from the transcript AFTER (1) and (2) and after a₀..a_{B−1}
4. prover  → opens ĉₖ(r) for k ∈ [B] and ĉ_out(r)   -- ONE common point, batched
5. verifier: ĉ_out(r) =? Σₖ aₖ · ĉₖ(r)
             + the range leg (3), discharged separately
```

**No sumcheck round occurs.** Step 5 is a single field equation.

### 2.4 Soundness of the linearity leg

`d := flat(c_out) − Σₖ aₖ·flat(cₖ)`. If `d ≠ 0` then `d̂` is a nonzero multilinear
polynomial in `μ` variables of individual degree 1, so `Pr_r[d̂(r) = 0] ≤ μ/|E|` by
Schwartz–Zippel. At `μ = 16`:

- over `F` alone: `16/2^31 ≈ 2^{−27}` — **not enough**;
- over `E = F⁴`: `16/2^124 ≈ 2^{−120}` — fine.

⚑ **The challenge must be drawn from the extension field.** A base-field challenge
gives a 2^−27 forgery probability on the *whole fold*, well under the repo's ~124-bit
bar. This is the one place the construction can silently fall below bar and it is
cheap to get right.

### 2.5 What the range leg is for, and why it is not free

Step 5 proves equality **in `F`**, i.e. mod `p`. FHE semantics is equality **in `Z`**
(under lazy accumulation) and thence mod `q_j`. Mod-`p` equality implies integer
equality only if both sides are `< p`. So:

- the honest accumulator entry is `Σₖ aₖ·limbₖ`, bounded by `(Σₖ|aₖ|)·2^w`;
- with 0/1 coefficients that is `B·2^w`;
- **field-wrap-free requires `B·2^w < p`**, i.e. at `w = 19`, `B < 2^{12} = 4096`.

A prover that reduces mid-fold produces a `c_out` that differs from `Σₖ aₖcₖ` over `Z`,
so step 5 **fails** — the no-reduction side condition is *fail-closed for the honest
prover*, not a soundness hole. The soundness hole is the other direction: an adversarial
`c_out` equal to the true sum **plus a multiple of `p`**. That is exactly what leg (3)
forbids, and leg (3) costs `Θ(M·λ) = Θ(N·L)` range checks. **This is the Θ(N·L) in
"the linear route is Θ(N·L)".** It is the same reduction the AIR route performs `B`
times; here it is performed once.

So the correct one-line statement is:

> **The linear route does not delete the reduction. It amortises it: one canonicalisation
> of the result instead of B canonicalisations of the partial sums.**

### 2.6 The three binding conditions, as the brief names them

**(a) The coefficients must be bound to the transcript that produced `r`.**
If `aₖ` may be chosen after seeing `r`, the prover faces *one* equation
`ĉ_out(r) = Σₖ aₖ ĉₖ(r)` in `B` unknowns over `E` and solves it in closed form for any
`c_out` it likes (set `a₀ = (ĉ_out(r) − Σ_{k>0} aₖĉₖ(r))/ĉ₀(r)`). **This is a total
break, not a degradation.** In the Lean statement it appears as: `r` is a function of a
transcript state that already absorbed `(C₀..C_{B−1}, C_out, a₀..a_{B−1})`.
Deployed mitigation: `aₖ` is the `side` bit of a *signed* envelope, fixed before the node
ever folds — so the deployed instance satisfies (a) structurally. The general weighted
statement does not get that for free.
This is demonstrated as a live forgery in the build (§3, `forges_when_coefficients_are_chosen_after_the_challenge`).

**(b) "No modular reduction" must be enforced, not assumed.**
Enforced by leg (3) of §2.2 — a range check on the *output* limbs against
`Bnd = B·2^w`. Two distinct wrap hazards, both covered:
`q_j`-wrap (FHE side) and `p`-wrap (field side). Note leg (3) is a check on the
*result only*, `Θ(N·L)`, never `Θ(B·N·L)`.

**(c) What binds `cₖ` to the ciphertexts the FHE engine held.**
⚑ **This is the real seam and it is currently unmet.** Read at source:
`fhegg-fhe/src/attestation.rs:185`, `InputDigest::ciphertext` binds
`ciphertext.to_fhe_bytes()` — a *byte digest of the wire encoding*. The MLE commitment
is a Merkle root over a Reed–Solomon codeword of `flat(cₖ)`. Two different functions of
the same ciphertext. There are exactly two ways to close it (and see §4.3 for what the
first one costs):

  - **(i) make the ingress commitment BE the MLE commitment** — the trader computes
    `Commit(flat(cₖ))` and signs *that*; the attestation's `ordered_inputs` digest is
    replaced. Cost: a `Θ(N·L)` RS-encode + Merkle per order, paid **by the trader, once**,
    at ingress. This is a wire-format change and a descriptor re-emit. **Greenfield: do it.**
  - **(ii) prove digest ↔ MLE agreement in-circuit** — a hash over all 98,304 bytes of
    every input ciphertext, inside the proof. That is `Θ(B·N·L)` in-circuit hashing:
    it *reintroduces exactly the term the whole result deletes*. **Not an option.**

There is no third way, and (ii) is not a fallback — it is a way to spend the entire win.
Naming it here so it does not get picked later as "the compatible option".

### 2.7 ⚑ Half of this is already in Lean, and it is the ℤ half

I went looking for where to put the Lean statement and found the FHE-semantics half
already there. **Read, not relayed:**

`metatheory/Bfv/Ring.lean:354` —

```lean
def matVecRCt {P : Params} {N n : ℕ} (S : Fin n → Fin n → ℤ) (x : Fin n → RCt P N) :
    Fin n → RCt P N :=
  fun i => ⟨fun k => ∑ j, S i j * (x j).phase k⟩
```

That is `c_out = Σⱼ aⱼcⱼ` at the ring level with **public integer coefficients**, and
`matVecR_noiseAtInt` (line 364) proves the output noise is the same linear map applied to
the input noises — "exact coefficient algebra". `stepR_noise_le` then bounds it with **no
factor of `N`**, precisely because the multipliers are public integer scalars acting
coefficientwise rather than ring elements.

Three consequences, and the third is the interesting one:

1. **The Lean work item is smaller than §4bis first suggested.** The FHE-semantics leg of
   `FoldOpen` — "the linear combination of ciphertexts is the linear combination of
   phases, and its noise is the linear combination of noises" — is proved. What is *not*
   proved, and is the genuinely new Lean work, is the **argument** leg: that a
   common-point opening of committed MLEs certifies the claimed output. That is a
   statement about the proof system, not about BFV.
2. **The carrier is `Rn N = Fin N → ℤ` — integer coefficients, no modular reduction.**
   So the Lean model of the fold *has always been the lazy-accumulation model.* My §2.5
   side condition is not an extra hypothesis to bolt on; it is the hypothesis the existing
   Lean development already works under.
3. ⚑ **Which means the divergence is on the Rust side.** `Bfv.Ring` folds in ℤ;
   `bfv_lean::add_row` reduces mod `q_j` at every step. They are reconciled only through
   the separate per-coefficient wrap argument (`Bfv.Noise.decryptPhase_add_q`). So
   "switch the deployed fold to lazy accumulation" is not a change *away* from the
   verified model — **it is a change *toward* it.** The reducing implementation is the
   one that does not match the Lean.

⚠ The composition is not free, and the remaining gap is worth naming exactly: `RCt` is a
**phase-only** model — one `Rn N` per ciphertext, the decryption phase. The object `flat`
commits is the **`(c₀, c₁)` RNS residue pair**, which is not the phase; the phase is
`c₀ + c₁·s` and depends on the secret key. So `FoldOpen` certifies linearity of the
*wire* representation, and `Bfv.Ring` certifies that linearity of the wire representation
implies linearity of the phase and hence of the message. Chaining them needs the step
"phase is ℤ-linear in `(c₀, c₁)` for fixed `s`", which is true and easy but is **not
written down**. That is the seam, and it is one lemma, not a campaign.

### 2.8 What this relation does NOT say

- It does not say the committed `cₖ` are well-formed BFV ciphertexts (canonical
  residues, honest encryption, declared `plain_bound` truthful). That is the *pre-existing*
  gap already named at `dark_clearing_service.rs:56` — "the 4-bit quantity bound is a
  DECLARATION, not a range proof". `FoldOpen` is sound **relative to** the committed
  inputs and inherits that gap unchanged; it neither widens nor narrows it.
- It does not certify the *plaintext* semantics of the fold (that the summed slots mean
  a demand curve). That is the descriptor's job.
- It says nothing about noise growth. The wrap gate on `plain_bound` is a separate,
  already-deployed refusal.

---

## 3. The build

`~/dev/breadstuffs/fold-opening/` — a workspace member, **not** a default-member,
following the `sumcheck-toy` precedent (M0 of this same ladder; this is M1).
**17/17 tests green.**

**Substrate, said out loud: no AIR, constraint, gadget or `air_accepts` is authored,
here or anywhere in this lane.** The relation is §2 above, in the shape a Lean theorem
takes. The Rust is the limb map, the transcript, the range leg as a *value* check, a
measurement harness, and the adversaries.

### What is built

| piece | file | what it is |
|---|---|---|
| the limb map `flat` | `src/lib.rs` `flatten` | 37-bit RNS residue → 2× 19-bit BabyBear limbs, layout pinned by a test |
| the lazy accumulator | `lazy_fold` / `LimbAccumulator` | componentwise limb sums, **no carry, no mod-q reduction** |
| the FHE-side lazy fold | `lazy_fold_residues` | `bfv_lean::add_row` minus the conditional subtract, no limb map — so §6 can be measured without contamination |
| the transcript | `draw_point` | Poseidon2 `DuplexChallenger` on deployed constants; absorbs shape, all `Cₖ`, `C_out`, **all `aₖ`**, the bound; then samples `r ∈ EF^16` |
| the commitment | `commit` | Poseidon2 sponge over the limb vector — binding, **not openable** |
| the protocol | `prove` / `verify` | `B+1` MLE evaluations at one point, one field equation |
| the range leg | `RangeLeg` | binding condition (b), enforced; refuses a bound ≥ `p` as vacuous |
| the cost model | `CostModel` / `account` | derived, named columns, both accountings |
| the adversaries | `adversary::draw_point_without_coefficients` | one binding condition removed so it can be **refuted** |

### The adversarial tests, and what each one buys

- **`forges_when_coefficients_are_chosen_after_the_challenge`** — removes binding
  condition (a) and forges. Given `r` first, the prover computes
  `a₀ = (target − Σ_{k>0} aₖvₖ)/v₀` in closed form and certifies an **arbitrary,
  unrelated ciphertext** as the fold. The test then shows the correct transcript order
  defeats the same forgery. ⚑ *This is the natural mistake*: the coefficients feel like
  witness data ("how the prover folded"), so absorbing only commitments looks complete.
- **`a_field_wrap_forgery_passes_linearity_and_is_caught_by_the_range_leg`** — adds `p`
  to one limb. The `F`-images are **identical**, so linearity accepts both. Only the
  range leg separates them. This is what makes leg (3) load-bearing rather than hygiene.
- **`a_bound_at_or_above_the_field_order_is_refused_as_vacuous`** — a range leg with
  bound ≥ `p` excludes nothing; it must *refuse*, not pass. (Prove-the-floor-false.)
- **`the_deployed_reducing_fold_breaks_the_identity`** — ⚑ **the load-bearing negative
  result.** `bfv_lean::fold` as deployed *reduces at every step*, so its output is not
  `Σcₖ` over `Z` and it **fails** the linearity check. The linear route requires
  *changing* the deployed fold; it is not a proof about the function as it stands.
  Fail-closed, which is the right direction, but it is a build item, not a freebie.
- **`a_mutated_result_is_caught`**, **`a_swapped_coefficient_vector_is_caught`** —
  constructive mutations, asserted to have actually mutated before the verdict is read.
- **`input_binding_is_a_commitment_not_a_wire_digest`** — asserts the MLE commitment and
  the proto3 wire digest of the *same ciphertext* differ, so binding condition (c) cannot
  be quietly assumed closed.
- **`the_challenge_point_lives_in_the_EXTENSION_field`** — the regression guard for §2.4.
  A drop to base-field challenges would typecheck, pass every other test in the file, and
  cost 93 bits. The test also **builds the base-field point it exists to reject** and
  asserts the same predicate scores it zero, so the gate is refutable rather than argued.

### ⚑ What is stubbed, named — **and it is a shipped-bug class, not a hypothetical**

**There is no polynomial commitment.** `FoldOpening::values` are numbers the prover
asserts; nothing ties them to `FoldOpening::commitments`. This is the same caveat
`sumcheck-toy` carries and it is the *whole* remaining gap in the protocol.

⚑ **Say the severity at the right resolution.** This exact shape is a live audit finding
with money behind it. `~/paperbin/audit-blog-ottersec-dusk-plonk-unverified-evals.txt`
(OtterSec, Apr 2026):

> *"the prover slipped four public selector evaluations into the proof struct, and the
> verifier consumed them in its final equation **without ever validating them against the
> trusted commitments** in the verifier key. The prover can set them to whatever values
> make the equation pass."* — ~$60M at risk.

That is a one-for-one description of `verify` as it stands: it consumes `values` in its
final equation and never validates them against `commitments`. So the stub is not "a
missing optimisation" or "an unbacked claim in a toy" — **it is the precise defect class
that has already shipped to production elsewhere.** Every one of the `B+1` evaluations
must be bound by a verified opening against a commitment fixed *before* `r`. Nothing less
counts, and the writeup must say so in these words rather than in the softer ones I first
used.

It is made visible in the type rather than in a comment: `verify` returns
`VerifiedAt { point }` — the outstanding obligation, as a field, so it cannot be read as
discharged. A real deployment proves `values[k] = ĉₖ(point)` against `commitments[k]`
with a multilinear PCS.

**Do not read a passing `verify` as "the prover knew ciphertexts summing to `c_out`".**
Read it as: *given honestly-opened evaluations*, the linear relation holds with soundness
error `μ/|EF| ≈ 2^−120`, and each binding condition is demonstrated load-bearing by a test
that removes it and forges.

The candidate for closing it exists at the pinned Plonky3 revision: `p3-sumcheck`'s
`commit_base` (a WHIR base-field commitment) plus its `layout` module, which stacks many
tables into one commitment and natively supports multiple opening claims. That is the
seam `notes/multilinear-pcs-landscape.md` is separately costing; this lane did not build
it and does not claim it.

---

## 4. The honest ratio

`cargo run --release -p fold-opening --bin fold_opening_bench`. M-series laptop,
min-of-N, three runs stable.

### 4.1 Committed field elements — **[DERIVED]**

⚠ There is **no AIR for `fold_add` in the tree to measure** (`prover-floor.md`:
"fold_add, ct×pt and ct×ct have no AIR at all"), so this prices the AIR that *would* be
written. Columns per modular-add site: **2 base + 4 lookup felts + 1 inter-limb carry =
7**. That is deliberately conservative to the AIR — the repo measures **34** elements per
site at real circuit sites, so every ratio below is a floor.

| B | AIR marginal | linear marginal | **marginal ratio** | total ratio |
|---|---|---|---|---|
| **4 (DEPLOYED)** | 1.03e6 | 2.46e5 | **4.2×** | 2.78× |
| 16 | 5.16e6 | 2.46e5 | 21.0× | 5.76× |
| 64 | 2.17e7 | 2.46e5 | 88.2× | 7.32× |
| 512 | 1.76e8 | 2.46e5 | **715.4×** | 7.91× |
| 3840 (ceiling) | 1.32e9 | 2.46e5 | 5374.6× | 7.99× |

The linear-route marginal column is **constant in B** — 245,760 elements, always. That
is the result, in one column.

**The two accountings, and why both are honest:**

- **Marginal** (inputs already committed): exactly `7(B−1)/5`. Linear in `B`. ⚑ *This
  is the accounting in which "ratio = B" is true*, and the inputs genuinely are already
  committed — the attested clearing receipt already binds every ordered input ciphertext
  (`dark_clearing_service.rs` §6). At B=512 it gives **715×**, confirming the briefed
  "690×" as the right order of magnitude for the right reason.
- **Total-system** (charge every input commitment): `(8B−7)/(B+5)` → **saturates at 8×**.
  Under this accounting the win is the per-add column constant, **not** `B`.

Neither is wrong; they answer different questions. **A claim of "690×" must say which.**
And note the total-system ratio is *already* within 1% of its asymptote at B=512 — past
B≈64 the marginal number is the only one still moving.

### 4.2 Wall-clock — **[MEASURED]**

| B | limb map | MLE evals (B+1) | commit out | TOTAL | vs the FHE fold |
|---|---|---|---|---|---|
| **4 (DEPLOYED)** | 0.11 ms | 0.49 ms | **5.02 ms** | 5.63 ms | **258×** |
| 16 | 0.46 ms | 1.76 ms | 5.01 ms | 7.24 ms | 71× |
| 64 | 1.81 ms | 6.22 ms | 5.05 ms | 13.08 ms | 33× |
| 256 | 7.48 ms | 27.03 ms | 4.99 ms | 39.50 ms | 23× |

⚑ **The commitment dominates at the deployed batch — 89% of the linear route at B=4 —
and it is `B`-independent.** This is `prover-floor.md`'s central finding arriving again
from a completely different direction: *even the route that deletes the sumcheck entirely
is hash-bound.* The Θ(B)-shaped win is real and it lands on a term that is not the
bottleneck at B=4.

⚠ Two named inadequacies in this table. (i) `commit` is a Poseidon2 sponge in the
**scalar challenger path**, not the packed Merkle path a real PCS uses — so 5.02 ms is
an over-estimate of the commit term, probably by several ×. (ii) The total is **missing
the PCS opening**, so every "vs the FHE fold" figure is a **lower bound** on the linear
route's real cost. The right reading of 258× is "the linear route is at least 258× the
FHE fold at deployed B", against the AIR route's ≥618× (packed) / 1639× (scalar) from
`h2-verdict.md` — the same order, and the comparison will only get worse once the
opening lands.

### 4.3 ⚑ A correction to my own marginal accounting

The marginal column above charges the input commitments to nobody, on the grounds that
*"the attestation already binds every ordered input ciphertext"*. **Read at source, that
is true but not sufficient.** `fhegg-fhe/src/attestation.rs:185`:

```rust
pub fn ciphertext(ciphertext: &LeanCiphertext) -> Self {
    Self::ciphertext_bytes(&ciphertext.to_fhe_bytes())   // a digest of the WIRE BYTES
}
```

So the inputs are already bound — **by the wrong function**, which is binding condition
(c) restated as an accounting fact. Closing (c) does not merely *re-point* an existing
commitment; it **replaces a SHA-class digest over 98,304 bytes with an RS-encode +
Merkle commitment over 49,152 field elements.** Measured here, the sponge over the limb
vector alone is **~5 ms**, against roughly ~0.1 ms for a byte digest of the same
ciphertext — call it one to two orders of magnitude dearer *per input*.

That does not overturn the marginal frame, and here is precisely why it does not:

- the cost is **per-trader, at ingress, once**, and it is off the folding node's
  critical path — which is what "marginal to the fold prover" means;
- it is paid **anyway** by any design that proves anything about these ciphertexts with
  a hash-based PCS. It is not a cost of *this* result.

But "already committed" was doing more work in that sentence than it had earned, so:
**the honest marginal claim is "the input commitment is not the fold prover's cost", not
"the input commitment is free".** ⚑ The system-wide bill for closing (c) is a
one-to-two-order-of-magnitude increase in per-order ingress commitment cost, and that
belongs in the decision, not in a footnote.

### 4.4 ⚑ The verifier goes the other way — a hole in the ratio claim, found in review

Everything above prices the **prover**. The prior-art sweep surfaced the objection I had
not priced, and it is correct:

> *The zero-round claim is really "the verifier does O(k) work". Your claim is sound only
> when the fold arity k is small enough that the verifier can compute `Σ aₖ ĉₖ(r)` itself,
> or when the `aₖ` MLE is verifier-evaluable. If k is large or the `aₖ` are committed,
> you are back to a sumcheck.*

Worked through:

- The **arithmetic** is fine — `B` multiply-adds in `EF`, trivial at any `B` we would run.
- The **openings** are the problem. The verifier must check `B+1` evaluations against
  `B+1` commitments. With a hash-based PCS that is `B+1` Merkle-path sets — `O(B·λ·log M)`
  hashes. **The linear route's verifier is linear in `B`; the AIR route's verifier is
  polylogarithmic in the trace.** So the two routes trade in *opposite directions* and my
  §4.1 table prices only one side of that trade.
- The standard fix is to commit all `B+1` polynomials as columns of **one** Merkle tree, so
  one opening yields all `B+1` values per query — verifier back to `O(λ·log M)` hashes plus
  `O(B)` cheap field ops.

⚑ **But that fix collides head-on with binding condition (c).** Closing (c) means *each
trader commits its own ciphertext independently at ingress* — `B` separate roots, by
construction, produced at different times by different parties. You cannot also have them
be columns of one tree. So:

| | one shared tree | B independent per-trader roots (what (c) needs) |
|---|---|---|
| verifier | `O(λ log M)` hashes + `O(B)` field ops | **`O(B·λ log M)` hashes** |
| binding (c) | ✗ — needs a single committer holding all inputs | ✓ |

**This tension is unresolved and it is the most interesting thing the review turned up.**
It does not touch the deployed answer (`B=4`: four Merkle openings, nothing), but it means
the `715×`-at-`B=512` figure is a **prover-side** number whose verifier-side counterpart
moves the wrong way, and any push toward large `B` (§4.5's "raise `ORDER_COUNT`") has to
answer it first. Do not quote the marginal ratio without this sentence attached.

### 4.5 The deployed answer, in one line

> At the batch the node actually folds (**B=4**), the opening route commits **4.2×**
> fewer field elements than the AIR that would have to be written — not 690×. The 690×
> regime begins around **B≈500** and the node is three orders of magnitude away from it.

The Θ(B) result is correct and worth having. It is a result about a *batch size we do
not run*. Two honest uses of it: (a) it is a reason to **raise** `ORDER_COUNT` — the
economics of the linear route improve linearly with the auction's batch, which is an
argument for a bigger auction rather than a faster prover; (b) it applies unchanged to
any other ciphertext fold in the system with a large `B` — the GPU arena sweeps N=10³–10⁵
and *those* are the shapes where 715×–5000× is live, if anything ever needs them proved.

---

## 5. Prior art — **the brief's premise is false: we are not first at Layer B either**

> **Headline.** The brief said "we are almost certainly not first at the FACT — the
> question is whether anyone has applied it to FHE ciphertext folding, which is our
> actual claim." **Someone has.** Tremblay Thibault, Walter & Zhang (Zama + USC),
> *Practical SNARGs for Matrix Multiplications over Encrypted Data*, eprint **2026/027**,
> with an open-source implementation — **and the PDF is in `~/paperbin`**
> (`practical-snargs-matvec-over-encrypted-data-zama-2026-027.pdf`). Read at source. The
> surviving delta is real but much narrower than "our actual claim", and it is stated in
> §5.3.

⚠ **Instrument disclosure, per house law.** Two independent instruments, both named.
(i) Web/arXiv search plus full text of three papers I pulled and `pdftotext`-extracted
myself (VERITAS, the Zama matvec SNARG, and the reference lists of both). (ii) A full
sweep of `~/paperbin` — 1,205 PDFs + 561 `.txt` siblings including the `joshibot/`,
`attestable/` and `uweave/` subdirs — by ripgrep over every extraction **plus four
`pdftotext` sweeps over all 810 PDFs lacking one**, plus ~25 targeted reads (§5.7).
paperbin is **not blind here**: it carries Rinocchio (`2021-322`), both Zama vFHE papers
(`2024-451`, `2026-027`), Atapoor (`2024-032`), Laminate (`2025-2285`), ring-R1CS vFHE
(`2024-1764`), blind-PCS vFHE (`2026-487`), Phalanx (`2025-302`), Heliopolis (`2023-1949`),
HasteBoots (`2025-261`), the packed-sumcheck TFHE SNARK (`2025-719`), and Zama's
verifiable bootstrapping (`2026-1127`). Everything below is a *presence* finding;
**no absence is claimed anywhere in this section**, and §5.7 says which shelf is missing.
Two instrument failures, named: the ACM Computing Surveys systematic review of verifiable
FHE (`10.1145/3797902`) **returned 403 and was not read**, and eprint 2024/032 **429'd**
(though the PDF is in paperbin and was not read either). Both remain unconsulted, and the
survey is the single best instrument for any absence question.

### Layer A — **written down almost verbatim, in our own corpus**

Not merely folklore-adjacent. The single closest statement is the **Binius64 Blueprint**,
§4.4 "The Zero Reduction" (`~/paperbin/binius64-blueprint-spec.pdf`, `.txt` ll. 1072–1080):

> *"Alone among the four constraint reductions it costs nothing: **it adds no prover
> message and no sumcheck round**, and it draws no challenges of its own… **Its whole
> content is the observation that a Zero constraint is linear**, so that the polynomial
> whose vanishing is at stake is d̂ itself rather than a product of witness multilinears.
> A multilinear that vanishes on the cube is the zero polynomial; **a single evaluation at
> a point the prover could not predict therefore certifies the constraint outright, with
> no sumcheck needed to get there.**"*

That is this note's §2.3 and §2.4, as a general reduction, with the reason. Supporting
sightings, each an independent statement of the same fact:

- **Binius** (`binius1-towers-binary-fields-2023-1784.pdf`, Ex. 4.9) generalises it and
  gives it the name **"virtual polynomial"**: the verifier "may query each of the handles
  at `r`, evaluate `g` itself on the results, and finally compare". The term has a citation
  lineage (Jolt Atlas, Powdr, DeepProve all restate it).
- **GKR-HND transformers** (`gkr-hnd-transformer.pdf`, arXiv 2607.21162): *"**addition is
  checked by MLE linearity**"* — one sentence, no proof, i.e. treated as known — used for
  the residual stream.
- **Laminate** (`laminate-succinct-simd-verifiable-fhe-2025-2285.pdf`, §4.4.2), inside a
  *verifiable-FHE* paper: *"reduces to a single opening query against the committed scalar
  coefficient MLE… **with no additional sumcheck rounds**"*, for affine gates that are
  exactly "CT-CT additions, PT-CT additions, scalar-CT multiplications".
- **Thaler's book** §16.1 for the batch-opening converse; **Bünz et al.**
  (`accumulation-without-homomorphism-bunz-2024-474.pdf`) names the folding premise
  explicitly *in order to remove it*.

**Claiming novelty at Layer A would be plainly wrong.** It is citable, named, and sitting
in `~/paperbin` in a production spec document.

### 5.0 ⚑ Our exact statement is in paperbin — solved the AIR way, by the authors of 5.1

`~/paperbin/vfhe-zama-plonky2-tfhe-bootstrap-20min-2024-451.pdf` — Tremblay Thibault &
Walter, *Towards Verifiable FHE in Practice*, §"Weighted sum":

> *"the weights `w_i` are in cleartext… **The weights are assumed to be constants known in
> advance and built in the arithmetic circuit.** … the circuit now multiplies each element
> `a_{c_i}` with its respective weight `w_i` before summing them together, resulting in a
> combined element `â = Σ_{i=1}^n w_i·a_{c_i}` … equivalent to the `j`-th element of the
> ciphertext `ĉ = Σ_{i=1}^n w_i·c_i`."*

**That is `FoldOpen`, verbatim** — fixed public weights, RLWE ciphertext coefficient
vectors — **solved by building the interior into a plonky2 circuit.** So the "AIR route"
this note prices against is not a straw man I invented for the comparison; it is the
published baseline, by the same group that later wrote 5.1. Two things follow:

1. The §4.1 cost model is pricing a **real** design, which strengthens it.
2. They pay exactly what the model predicts: *"the circuit now computes **one hash chain
   per input ciphertext**… input and output of the step circuit increase in size linearly
   with the number of input ciphertexts `n`."* — and that hash chain is **their answer to
   our binding condition (c)**, paid in-circuit. §2.6 called route (ii) "not an option
   because it spends the entire win"; here is someone spending it.

### 5.1 ⚑ Layer B — **published**: Zama eprint 2026/027, and it is in our own corpus

*Practical SNARGs for Matrix Multiplications over Encrypted Data* proves exactly the
statement `Mx = y` for a **public matrix `M` and an encrypted vector `x`** — a linear map
on RLWE ciphertexts, of which our fold is the special case where `M` is one 0/1 selector
row. Its method, in its own §1.1:

> *"the main challenge here is the mathematical gap between polynomial rings
> `R_q = Z_q[X]/(X^N+1)` and finite fields… we adopt the **ring-switching** idea…
> **Ring embedding**: an appropriate extension field `F_q` of `Z_q` is chosen… we embed
> the statement `Mx = y` over `R_q` into a statement over `F_q[X]`. **Ring reduction**:
> reduce the statement, via a **polynomial commitment scheme** over the extension field,
> from `F_q[X]` to `F_q`… each `R_q` element is compressed into an `F_q` element."*

That is "commit the ciphertext coefficients as polynomials, move to an extension field,
reduce the ring statement to field evaluations" — **the shape this note proposed, already
built, benchmarked and open-sourced.** The brief's framing ("the question is whether
anyone has applied it to FHE ciphertext folding") is answered *yes*, by a paper sitting in
`~/paperbin`. Recording that plainly, because the alternative is discovering it after
building on the assumption.

Note also *what they had to give up to avoid limbs*: `q` is a **64-bit prime** with
extension degree 2. They match the proof field to the FHE modulus — the "shared
cryptographic parameters" constraint VERITAS criticises in Fiore et al. We take the other
branch (31-bit BabyBear + a 19-bit limb map + an explicit range leg), which is a real
design fork and not obviously the worse one, given `prover-floor.md`'s field-choice result.

### 5.2 Layer B's wider neighbourhood

The literature has a name and a taxonomy for this (Chatel–Knabenhans–Pyrgelis–Troncoso–
Hubaux, *Verifiable Encodings for Secure Homomorphic Analytics* / **VERITAS**,
arXiv:2207.14071v4, §related work). Read at source:

1. ⚑ **Bois, Cascudo, Fiore, Kim — "Flexible and efficient verifiable computation on
   encrypted data" (PKC 2021).** VERITAS's own summary: *"the resulting approach still
   limits the admissible HE pipelines (since it **does not support modular reduction**)."*
   **Our "no modular reduction during accumulation" side condition is a KNOWN limitation
   of a known line of work.** We did not discover the constraint; we are proposing to
   *live inside it deliberately* (lazy accumulation) and to *enforce it* with an explicit
   range leg (§2.5), which is the part I have not found stated anywhere.
2. **Fiore, Gennaro, Pastro — "Efficiently verifiable computation on encrypted data"
   (CCS 2014).** Built from two blocks, the second of which is *"a commit-and-prove SNARK
   for **multiple polynomial evaluations**"*. That is structurally our shape — commit
   ciphertext polynomials, prove evaluations — a decade early, in the pairing/QAP setting.
3. **Rinocchio** (Ganesh–Nitulescu–Soria-Vazquez), SNARKs for ring arithmetic; and
   **Fiore–Gennaro–Pastro-style homomorphic MACs** (Catalano et al. authenticate *linear
   ciphertext operations* specifically).

### 5.3 ⚑ The surviving delta: a fold is not a contraction

Zama's scheme **runs the sumcheck protocol twice** (§: *"prover and verifier run the
sumcheck protocol twice"*). Ours runs it zero times. That is not an oversight on their
part — it is a consequence of proving a strictly harder statement, and the distinction is
the one genuinely load-bearing technical point left in this note:

- **Matrix–vector, `y_i = Σ_j M_ij x_j`.** The output index `i` and the summed index `j`
  are **different**. This is a *contraction*, and a contraction needs a sumcheck over `j`.
  Zama proves this and pays for it.
- **A fold, `c_out[t] = Σ_k a_k c_k[t]`.** `k` is a **batch** index, not a contracted
  coordinate: every term is aligned at the *same* coordinate `t`, and there are only `B`
  of them. So it is `B+1` separate multilinears related by a pointwise identity, and
  `B+1` evaluations at one common point settle it. **Zero rounds.**

**So the delta is: for the aligned-pointwise case, even the sumcheck the state of the art
runs is unnecessary.** That is a real observation and it is worth the build. It is also
*much* smaller than "nobody has applied this to FHE ciphertext folding", and it should be
written up as a corner of Zama-style ring-switching vFHE, not as a new result.

⚠ Honesty bound on §5.3: I read the Zama paper's abstract, §1, §1.1 and grepped its body
for the sumcheck usage. **I did not read their protocol section in full**, so "they could
not have specialised the aligned case" is *not* claimed — only that their headline
statement is a contraction and their protocol runs sumchecks.

### 5.4 The nearest neighbour on the authenticator branch, and how it differs

**VERITAS** carries a homomorphic *authenticator* alongside the ciphertext and applies the
same linear map to it. Its own words (§VI-B): *"both authenticators trivially support the
BFV linear operations… These operations are simply executed on all components of the
authentication σ"* and *"do not expand the size of the authentication."*

So VERITAS **does** exploit linearity — and the difference from our claim is exactly the
thing the claim is about:

| | VERITAS (REP / PE) | this note |
|---|---|---|
| mechanism | homomorphic authenticator carried *through* the computation | commit + one common-point opening *after* it |
| cost of the additive part | **Θ(additions)**, constant-factor: measured **53×** (REP) / **4.5×** (PE) per add vs bare BFV | **Θ(result)** — the additions cost *nothing*, `B+1` evaluations at one point |
| verifiability | **designated-verifier** (secret authenticator key) | publicly verifiable (hash-based PCS) |
| generality | any BFV circuit incl. rotation, relinearisation, bootstrapping | **linear folds only** |

### 5.5 ⚑ Four things that refute or complicate the claim

**(a) "Free additions ⟺ no modular reduction" was written down in 2021, in this setting.**
Rinocchio (`~/paperbin/ring-rinocchio-snarks-for-ring-arithmetic-2021-322.pdf`, discussion,
p.39):

> *"When using a QAP to emulate ring arithmetic, **addition gates are no longer for free;
> in contrast to QRPs with free ring additions. This is due to the fact that, in the
> QAP-based approach, a modular reduction might be necessary after adding two numbers.**"*

That is §2.5's mechanism — the thing I wrote up as "the whole mechanism and it should be
said that way" — stated five years ago, in the ring-SNARK-for-FHE literature. **Any
framing of "we noticed that reduction is what breaks freeness" as new is dead.**

**(b) ⚑ The field-alignment escape hatch makes our side condition look optional.**
Both Zama papers simply *choose the FHE modulus to be the proof field*: 2024/451 takes
`q = 2⁶⁴−2³²+1` (Goldilocks), and the TFHE SNARK `2025/719` takes `q = 2³¹−2²⁷+1`
(**BabyBear — our field**). With `q_FHE = p`, mod-`q` reduction is native field arithmetic:
**no limb map, no range leg, no lazy-accumulation discipline, and the identity holds
without any side condition at all.** The first question any reviewer asks is why we do not
do that, and the honest answer is narrow: *we do not control the modulus* — the deployed
carrier is `fhe.rs` BFV at HE-standard 36/36/37-bit RNS primes, and changing them is an FHE
security-parameter decision, not a proof-system one. That answer needs to be in the writeup,
because without it the entire §2.5 apparatus reads as self-inflicted.

**(c) The general method is "witness the quotient"; ours is a restriction.**
Limber (`~/paperbin/eprint-2026-1635.pdf`, Chen–Xia–Nguyen–Bünz, Aug 2026) proves
integer/mod-`p` R1CS with committed quotient witnesses — *"if the relation holds over the
integers, then the relation holds over the random prime `p` unconditionally"* — and
2026/027 does the ring analogue with an explicit committed `r` in `Mx = y + (X^N+1)·r`.
**Forbidding reduction is strictly weaker than accounting for it.** Position §2.5 as a
cheap specialisation for the aligned case, never as the better general answer.

**(d) The FHE side couples the two conditions we stated separately.**
Heliopolis (`~/paperbin/heliopolis-fri-over-ciphertexts-iop-2023-1949.pdf`, §1.2):
*"**the size of the coefficients in the linear combination and the additive depth …
constitutes a significant obstacle for noise management in practice**"*. Small `aₖ` and
bounded depth are what keep both the RLWE noise *and* the integer magnitude in range — so
§2.5's field-wrap bound and the existing `plain_bound` wrap gate are **one coupled
condition**, not two independent ones. The note currently presents them separately.

### 5.6 ⚑ The prior-art verdict, in the form it should be quoted

| layer | verdict |
|---|---|
| "MLE is linear, so linear maps need no rounds / one common-point opening certifies them" | **written down almost verbatim** — Binius64 Blueprint §4.4 "Zero Reduction", in `~/paperbin`. Named ("virtual polynomial") in Binius. Not ours, not close. |
| "apply it to an FHE ciphertext fold `c_out = Σ wᵢcᵢ` with fixed public weights" | **published, in `~/paperbin`, twice.** Zama **2024/451** does exactly this statement *the circuit way*; Zama **2026/027** does linear maps on GLWE ciphertexts *the MLE way* (with sumchecks). The brief's premise that this was open is **false**. |
| "free additions ⟺ no modular reduction" | **Rinocchio (2021), p.39**, in this exact setting. Not a discovery. |
| enforcing the condition with a **range leg on the result** rather than restricting the pipeline | **not found stated** — but the general method (witness the quotient: Limber, 2026/027) is *stronger*, so this is a specialisation, not an advance. |
| **a fold is aligned-pointwise, not a contraction, so even Zama 2026/027's two sumchecks are unnecessary** | the real delta (§5.3). Narrow, technical, worth the build — **and partially spent by §4.4**, since the verifier cost it saves in rounds it pays back in `B` openings. |

**What this means for how the result gets described.** Not "one common-point opening
certifies the whole fold — nobody has done this for FHE." Rather:

> *Ring-switching vFHE (Zama 2026/027) proves linear maps on RLWE ciphertexts by
> committing coefficients and reducing to an extension field, at the cost of a sumcheck
> because a matrix–vector product is a contraction. **A batch fold is not a contraction**
> — the batch index is not summed against the output index — so for that case the
> sumcheck is unnecessary and `B+1` openings at one common point suffice, with the
> no-reduction condition enforced by an `Θ(N·L)` range leg on the result rather than by
> restricting the pipeline.*

⚑ And the honest sequencing consequence: **before any more is built here, read Zama
2024/451 §"Weighted sum" and 2026/027's protocol section in full.** Both are in
`~/paperbin`, they are the direct predecessors on the two opposite routes, and §7's build
order should be re-derived against them rather than against this note's original assumption
that the ground was empty.

### 5.7 What was searched, and the gap that remains

The paperbin sweep was: ripgrep over all 561 `.txt` extractions, plus **four full
`pdftotext` sweeps over all 810 PDFs lacking a `.txt` sibling** (Layer-A phrases, Layer-B
phrases, ciphertext-linear-combination phrases, linear-map-commitment phrases), plus
targeted reads of ~25 high-value PDFs. Every vFHE paper in the corpus was checked for what
it does with the additive part; the table of results is in the sweep record.

⚠ **The most likely place for a further prior hit was not searched, because it is not in
the corpus.** The classic "verifiable HE for linear/additive computation only" line —
**Fiore–Gennaro–Pastro (CCS'14), Fiore–Nitulescu–Pointcheval (PKC'20),
Bois–Cascudo–Fiore–Kim (PKC'21), Chatel et al. (arXiv 2207.14071), Madi et al.
(RDAAPS'21)**, and **Boneh–Drake–Fisch–Gabizon** "linear combination schemes" — is
**absent from `~/paperbin` entirely**. HasteBoots's related-work section characterises the
first four as "supporting only basic FHE operations such as LWE additions", which is
precisely our fragment. **Fetch those before any novelty is claimed anywhere.** Nothing in
this section is an absence claim, and this paragraph is why.

---

## 6. Lazy accumulation — the correction

`notes/h2-verdict.md:27` reads:

| op | RNS 3-limb | single 109-bit | ratio |
|---|---|---|---|
| ct+ct add, reduced (our deployed fold path) | 2.34 µs | 5.09 µs | 2.18× |
| ct+ct add, lazy (available to both) | 1.71 µs | 1.51 µs | 0.88× |

The **0.88×** in that table is the *column* ratio — single-prime-109-bit lazy ÷
RNS-3-limb lazy. It is a statement about the H2 field question, **not** about lazy
accumulation.

The number the fold-as-opening claim needs is the *row* ratio on our own deployed
carrier: **RNS lazy ÷ RNS reduced = 1.71 / 2.34 = 0.731×**.

### ⚑ And then I measured it in-tree, and it is neither number

`lazy_fold_residues` is `bfv_lean::add_row` with the conditional subtract deleted and
nothing else changed — the narrowest possible instrument for this exact question. Against
`bfv_lean::fold` on the same fixtures, min-of-400 (B≤64) / min-of-40, three stable runs:

| B | `bfv_lean::fold` (reduced) | lazy residues | ratio |
|---|---|---|---|
| **4 (DEPLOYED)** | 0.018–0.022 ms | 0.021 ms | **0.97–1.16× — break-even** |
| 16 | 0.080–0.082 ms | 0.084–0.085 ms | 1.04× |
| 64 | 0.340 ms | 0.336 ms | 0.98× |
| 256 | 1.59–1.62 ms | 1.34–1.36 ms | **0.84×** |

So, three instruments and three answers, and the honest summary is:

- **the direction is confirmed** — lazy accumulation is cheaper, in both h2's artifact
  and in-tree, and it grows cheaper with `B` as the branch-elimination outruns the
  wider accumulator;
- **the magnitude at large B is ~0.84× in-tree**, between h2's 0.73× and the misquoted
  0.88×;
- ⚑ **at the deployed B=4 there is no measurable win at all.** Three adds is too few for
  branch elimination to pay for a wider accumulator, and the loop-shape noise is the same
  size as the effect.

An earlier draft of this measurement read 3.7× *slower*, then 1.11× slower, before
landing here — both were artefacts of my accumulator, not of laziness: the first paid a
multiply per element for a coefficient that is always 1 in the deployed shape, the second
did `B` passes where `fold` does `B−1` (zero-init-then-add rather than seed-from-first).
Recording that because the first draft would have been reported as a refutation of h2,
and it was a bug in the instrument.

**So "the side condition is met free, and is even a speedup" is right at B≥256 and is
NOT established at the batch we run.** It is not an obstacle either — break-even is
fine — but it is not the supporting argument the brief made it.

⚠ Further caveat, unresolved: the deployed fold path is a GPU-resident arena kernel
(`fhegg-fhe/src/gpu_arena.rs`) whose conditional subtract is one instruction in a lane.
Every figure above is CPU-scalar. Nothing here is measured for the shipped GPU kernel,
where the branch is cheapest and lazy accumulation has the least to win.

---

## 7. What is left to build, in order

Not a wishlist — the ordered remainder, with the one that is actually blocking first.

1. **Close binding condition (c) by replacing the ingress commitment.** The trader
   computes `Commit(flat(cₖ))` and signs *that*; `order_ingress`'s wire-byte digest and
   the attestation's `ordered_inputs` are re-pointed at it. This is a wire-format change,
   a descriptor re-emit and a re-genesis — i.e. ordinary work here. **Until this lands the
   protocol proves a statement about committed vectors that nothing ties to the
   ciphertexts the FHE engine held**, which is the difference between a result and a
   result you can use.
2. **The multilinear PCS.** The stub. `p3-sumcheck`'s `commit_base` + `layout` (WHIR) at
   the pinned revision is the candidate and it natively supports several opening claims
   on one stacked commitment — which is exactly the `B+1`-polys-one-point shape. Costed
   separately in `notes/multilinear-pcs-landscape.md`; do not duplicate that lane.
3. **The relation in Lean**, per §2.2, with the range leg as a lookup. Smaller than it
   looks: §2.7 found the FHE-semantics half already proved (`Bfv.Ring.matVecRCt` /
   `matVecR_noiseAtInt`). What is new is the *argument* leg plus one connecting lemma
   ("the phase is ℤ-linear in `(c₀, c₁)` for fixed `s`").
4. **Switch the deployed fold to lazy accumulation.** Required (§3, the load-bearing
   negative result), and measured break-even at B=4 — so it is a correctness
   prerequisite, not a speedup. Do not sell it as one. ⚑ And per §2.7 it moves the Rust
   *toward* the Lean model, not away from it — `Bfv.Ring` already folds in ℤ.

⚑ **Do not do (2) before (1).** A PCS opening against a commitment that is not the
ingress commitment is a beautifully-proved statement about the wrong object.
