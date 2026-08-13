# fold_add as an opening, not a circuit — spec, build, and the honest ratio

**Lane**: design + build. Started 2026-08-13. Written incrementally.
**Claim under test** (from `notes/prover-floor.md` §"Correction to my own brief"):
`fold_add` is linear, MLE is linear, therefore `c_out = Σₖ aₖcₖ ⟹ ĉ_out = Σₖ aₖĉₖ`
**as polynomials**, so one common-point opening certifies the whole fold — zero
sumcheck rounds. AIR cost Θ(B·N·L), linear route Θ(N·L), **ratio = B**.

**Verdict so far**: the *algebra* holds and is now demonstrated on real deployed-shape
ciphertexts. **Three of the four headline numbers in the source claim are wrong or
mis-attributed**, and the correction makes the result *narrower but sharper*. Details
in §4, §5 and §6.

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
| the FHE-side lazy fold | `lazy_fold_residues` | `bfv_lean::add_row` minus the conditional subtract, no limb map — so §5 can be measured without contamination |
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

### ⚑ What is stubbed, named

**There is no polynomial commitment.** `FoldOpening::values` are numbers the prover
asserts; nothing ties them to `FoldOpening::commitments`. This is the same caveat
`sumcheck-toy` carries and it is the *whole* remaining gap in the protocol.

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

### 4.4 The deployed answer, in one line

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

## 5. Prior art — **we are not first at the fact, and the nearest neighbour is sharper than expected**

⚠ **Instrument disclosure, per house law.** This section is built from **web/arXiv search
plus full-text of one paper I pulled and extracted myself**. `~/paperbin` (1,091 PDFs,
507 with `.txt`) was swept separately. Neither instrument alone supports an absence
claim, and this section makes none: everything below is a *presence* finding.
One instrument failed outright and is named: the ACM Computing Surveys systematic review
of verifiable FHE (`10.1145/3797902`) **returned 403 and was not read** — it is the single
best instrument for the absence question and it remains unconsulted.

### Layer A — "linear maps are free in the multilinear world": **KNOWN, and we are not close to first**

This is folklore and it is the operating assumption of several whole literatures:
GKR/sumcheck zkML checks linear layers with sumchecks over MLEs; batch-opening arguments
are random-linear-combination arguments; folding schemes (Nova and descendants) exist
*because* a linear combination of committed instances is cheap under commitment
homomorphism. **Claiming novelty at Layer A would be wrong.** Our note should never have
been going to.

### Layer B — FHE ciphertext folding: **the neighbourhood is populated, and two neighbours are very close**

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

### The nearest neighbour, and exactly how it differs

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

⚑ **The honest position, then.** The *fact* is known (Layer A). The *setting* is populated
(vFHE, and the no-reduction restriction is already documented as a limitation). What I have
not found stated is the specific combination: **cost proportional to the RESULT rather than
to the ADDITIONS, for an FHE ciphertext fold, publicly verifiable, with the no-reduction
condition promoted from a restriction into an enforced range leg.** VERITAS is the closest
and it is Θ(work) with a 4.5–53× constant; we are Θ(result) with zero per-addition cost —
but only for the linear fragment, which VERITAS covers as a special case of far more.

**Trading generality for asymptotics is the actual claim.** That is a much narrower and
more defensible sentence than "one common-point opening certifies the whole fold", and it
is the one to use.

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
