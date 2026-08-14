# Ligerito — exploratory formalization

**Lane framing.** A prior lane concluded "Ligerito-family soundness cannot compose from what we
hold." That is a statement about *our current machinery*, not about whether Ligerito is worth
understanding. Ligerito is BinarySpartan's PCS, so we need to know it either way. **This lane's job
is to state it in Lean, not to decide whether to build it.**

Sources read at first hand:
- `~/paperbin/ligerito.pdf` — Novakovic & Angeris, "Ligerito", May 2025.
- `~/dev/gh/forks/IACR-eprint-mirror/2025/1187.pdf` — the eprint version.
- `~/dev/gh/forks/IACR-eprint-mirror/2024/1399.pdf` — Angeris–Evans–Roh, "A Note on Ligero and
  Logarithmic Randomness" (Sept 2024). **This is the source of the bound Ligerito misprints.**
- `~/paperbin/proximity-gaps-interleaved-codes-diamond-gruen-2024-1351.pdf` — Diamond–Gruen.

---

## 0. Provenance: there is exactly one version, and the errata are not fixed in it

[MEASURED] `pdftotext -raw` on the paperbin copy and on eprint 2025/1187, whitespace-normalised
and `diff`ed: **textually identical**. eprint history is a single version (received 2025-06-24,
approved 2025-06-27). The `angeris.github.io` copy is the same file (212 KB, same May 2025 date).

So: **the two errata below are still live in the only published version.** There is no published
errata note; the corrections are derived here from the paper's own cited source (AER24) and
confirmed against the paper's own parameter selection.

⚠ The paper has **no `Theorem` environment anywhere** — its error analysis is running prose that
delegates the load-bearing proximity step to [AER24] and [DG24].

---

## 1. The soundness statement, as a Lean statement would read it

### 1.1 What Ligerito actually is

Not FRI-shaped. **Ligero-shaped**: an *interleaved* linear code, committed row-wise under a Merkle
tree, opened at *whole rows*, merged with a *partial sumcheck*, applied *recursively* for ℓ rounds.
The recursion is the new part: instead of sending `y_r = X̃r` (which is √N-sized), the prover
**commits `Mat(y_r)` as the next round's matrix** and proves the needed inner products about it.

The one requirement on the code is unusually weak: *any linear code whose generator-matrix rows can
be efficiently evaluated*. Reed–Solomon, Reed–Muller, RAA all qualify.

### 1.2 The base guarantee (§3), which everything else is bookkeeping over

Given a committed (opaque) matrix `X ∈ F^{m×n'}` and a challenge `r`, if the verifier's check
`X_S r = G_S y_r` passes on a uniformly sampled `S ⊆ {1..m}` of fixed size, then:

1. **∃! `X̃` with `‖X − G X̃‖ < d/2`** — where `‖·‖` counts **nonzero ROWS of a matrix**, `d` is the
   code distance, and `d/2` is the **unique decoding radius** (not Johnson, not capacity);
2. **`y_r = X̃ r`** — the received vector is the partial evaluation of that unique `X̃`.

Both hold except with the error probability in §1.3.

### 1.3 ⚑ The corrected bound, with the errata arithmetic

**The source.** AER24 §3.2 eq (18) is the theorem Ligerito is quoting. Read at
`~/dev/gh/forks/IACR-eprint-mirror/2024/1399.pdf`, verbatim:

```
p + p' + p''  ≤  (1 − (q+1)/m)^{|S|}  +  k(q+1)/|F|  +  (1 − (d−q)/m)^{|S'|}      (AER24-18)
```

for proximity parameter `q`. **Every base is of the form `1 − (something)/m`.** That single fact
settles both errata.

#### Erratum 1 — Reed–Solomon case: eqs (4), (15), (17) and the §6.3 proof

In the unique-decoding regime `q + 1 = d/2`, AER24-18's first base is `1 − d/(2m)`. For RS,
`d = m − n + 1`, so

```
1 − d/(2m) = 1 − (m−n+1)/(2m) = (2m − m + n − 1)/(2m) = (m + n − 1)/(2m)
```

The paper prints **`(m − n − 1)/(2m)`**. The sign on `n` is flipped.

| | base | bits/query at ρ=1/4 | at \|S\|=148 |
|---|---|---|---|
| printed `(m−n−1)/(2m)` → `(1−ρ)/2` | 0.375 | −1.4150 | **2^−209.43** |
| correct `(m+n−1)/(2m)` → `(1+ρ)/2` | 0.625 | −0.6781 | **2^−100.35** |

The printed bound overstates security-per-query by **2.087×**.

⚑ **Decisive internal cross-check — the paper's own parameters use the CORRECTED base.** §6.4 sets
`|S_i| = ⌈−(λ + log ℓ)/log((1+ρ)/2)⌉`, whose base is `(1+ρ)/2` — the *correct* one. And §7 reports
`|S_i| = 148` at `λ = 100, ρ = 1/4`:

```
⌈−100 / log₂(0.625)⌉ = ⌈100/0.678072⌉ = ⌈147.48⌉ = 148      ✓ exactly the paper's number
⌈−100 / log₂(0.375)⌉ = ⌈100/1.415⌉    = ⌈ 70.67⌉ =  71      ✗ what it would have said
```

**So the erratum is confined to the displayed equations. The reported security level and the
reported proof sizes/benchmarks are unaffected** — §6.4 and §7 were computed correctly. This is a
transcription defect in the statement, not a defect in the instantiation. That distinction matters:
it means *formalizing eqs (4)/(15)/(17) verbatim would prove a bound the protocol does not have*,
while the concrete scheme as benchmarked is fine.

#### Erratum 2 — general linear code case: the summand of eq (18)

AER24 sets `q = d/3 − 1` for the general (non-RS) case, so `q + 1 = d/3` and the first base is
`1 − d/(3m)`. Ligerito's **eq (5)** and **eq (16)** print this correctly. Ligerito's **eq (18)
summand** prints `(d_i/(3m_i))^{|S_i|}` — the `1 −` is dropped. Note eq (18)'s own *tail* term
keeps the `1 −`, so **eq (18) is internally inconsistent with itself**, as well as with (5)/(16)
and with AER24.

| | base | bits/query at ρ=1/4 (d/m = 3/4) | at \|S\|=148 |
|---|---|---|---|
| printed `d/(3m)` | 0.25 | −2.000 | 2^−296.0 |
| correct `1 − d/(3m)` | 0.75 | −0.4150 | **2^−61.43** |

⚑ **This one has a real design consequence the paper never states:** at the *same* 148 queries a
general linear code buys only **61 bits**, not 100. Reaching λ=100 with a general code needs

```
⌈100 / 0.41504⌉ = 241 queries      vs. 148 for Reed–Solomon
```

— a **1.63× query blowup**, i.e. 1.63× the Merkle openings, which §6.4 identifies as the *dominant*
communication cost. The "works over essentially any linear code" flexibility is real but is **not
free**, and the note's headline proof sizes are RS-only. The gap is structural: RS gets the
unique-decoding radius `d/2` from Diamond–Gruen; a general code only gets `d/3` from AER24.

#### ⚠ Third observation (mine, not an erratum): the 1/|F| terms are not safely negligible

§6.4 drops every `1/|F|` term on the ground that "`|F| ≫ 2^λ`". At the paper's own experimental
parameters (`|F| = 2^128`, `λ = 100`, `N = 2^24`, `ρ = 1/4`) the headroom is only `2^28`, while the
first-round term `m₁k₁` is around `2^26`–`2^30` depending on the round split:

| k'₁ | k₁ | m₁ | `m₁k₁/|F|` |
|---|---|---|---|
| 2 | 22 | 2^24 | 2^−99.54 |
| 3 | 21 | 2^23 | 2^−100.61 |
| 4 | 20 | 2^22 | 2^−101.68 |
| 6 | 18 | 2^20 | 2^−103.83 |

For the tighter splits this term **equals or exceeds the query term** (2^−100.35). So `λ = 100` is
approached from both sides and the field terms are load-bearing. **A formalization must carry them;
it may not drop them.**

### 1.4 The statement as Lean would read it

Quantifier structure of the §6.3 guarantee, made explicit (the paper leaves all of this in prose):

```
∀ (F : Type) [Field F] [Fintype F]                    -- ⚠ NO characteristic hypothesis anywhere
  (ℓ : ℕ) (hℓ : 2 ≤ ℓ)                                 -- number of rounds
  (k k' : Fin ℓ → ℕ)                                   -- per-round dimensions, k_{i+1} + k'_{i+1} = k_i
  (m : Fin ℓ → ℕ) (d : Fin ℓ → ℕ)                      -- per-round block length and distance
  (G : ∀ i, Matrix (Fin (m i)) (Fin (2^(k i))) F)      -- per-round generator, distance d i > 0
  (X : ∀ i, committed matrix)                          -- the opaque committed matrices
  (S : ∀ i, Finset (Fin (m i)))                        -- query sets, |S i| fixed
  (w : F^(2^(k 0 + k' 0))) (α : F),
  VerifierAccepts … →
    Pr[ (∀ i, ∃! X̃ i, ‖X i − G i * X̃ i‖ < d i / 2)     -- (1) unique decoding, per round
        ∧ wᵀ vec(X̃ 0) = α                              -- (2) the claimed inner product
        ∧ y_ℓ = Mat(X̃ 0) (r_0 ⊗ … ⊗ r_{ℓ-1}) ]         -- (3) the tensor-fold consistency
    ≥ 1 − ligeritoError …
```

Three things a Lean reading makes visible that the prose hides:

1. **`‖·‖` is the row-count norm on matrices, not a Hamming weight on vectors.** `‖X‖ = #{rows of X
   that are nonzero}`. This is *the* type-level obstruction: it is a metric on `Matrix` (equivalently
   on `Fin ℓ → ι → F`), not on `ι → F`.
2. **The uniqueness `∃!` is doing real work** and is where the `< d/2` unique-decoding radius is
   consumed. Above `d/2` there is no `∃!` and the whole statement shape changes (list decoding).
3. **There is no hypothesis on `char F`.** Diamond–Gruen Thm 3.1 and AER24 Thm 3.6 are both stated
   over an arbitrary field and an arbitrary `[n,k,d]` code. Only the *base case* (BCIKS Thm 4.1, for
   RS) is code-specific. **Ligerito is char-2-clean by construction** — which is exactly why
   BinarySpartan pairs it with a binary field.

### 1.5 The corrected total bound

Reed–Solomon (eq (17), corrected):

```
∑_{i=1}^{ℓ-1} [ 2k_{i-1}/|F| + (|S_i|+1)/|F| + ((m_i + 2^{k_i} − 1)/(2m_i))^{|S_i|} + m_i k_i/|F| ]
  + 2k_{ℓ-1}/|F| + ((m_ℓ + 2^{k_ℓ} − 1)/(2m_ℓ))^{|S_ℓ|} + m_ℓ k_ℓ/|F|
```

General linear code (eq (18), corrected):

```
∑_{i=1}^{ℓ-1} [ d_i k_{i-1}/(3|F|) + (|S_i|+1)/|F| + (1 − d_i/(3m_i))^{|S_i|} + d_i k_i/(3|F|) ]
  + 2k_{ℓ-1}/|F| + (1 − d_ℓ/(3m_ℓ))^{|S_ℓ|} + d_ℓ k_ℓ/(3|F|)
```

(Two further indexing slips, noted but not load-bearing since these are all `O(1/|F|)`: the `2k_{i-1}`
in the first summand should be `2k'_i` to match the §6.3 tally, and the tail terms are indexed at `ℓ`
where the protocol only defines codes `G_1 … G_{ℓ-1}`.)

---

## 2. Design-space placement — our analogues, tested rather than assumed

### 2.0 ⚠ A notation trap that must be cleared first

Three sources use three transposes of the same matrix, and conflating them silently inverts the
metric:

| source | matrix | the sampled axis | what "distance" counts |
|---|---|---|---|
| Ligerito §2.1/§3 | `X ∈ F^{m×n'}`, `m` = **block length** | **rows** (`S ⊆ {1..m}`) | `‖·‖` = "number of nonzero **rows**" |
| Diamond–Gruen §2 | `F^{m×n}`, `m` = **interleaving factor**, `n` = block length | columns | differing **columns** |
| this file's Lean | `ι → Fin m → F`, `ι` = block length | `ι` | differing `ι`-positions |

[VERIFIED at source] Ligerito's "nonzero **rows**" and DG24's "differing **columns**" are **the same
set** — the code positions — because Ligerito writes the interleaving factor on the *column* axis
and DG24 writes it on the *row* axis. A reader who takes both at face value concludes the two
papers use different metrics. They do not.

### 2.1 What an interleaved-code opening does differently from a FRI fold

| | FRI/WHIR fold (our cone) | Ligero/Ligerito interleaved opening |
|---|---|---|
| committed object | one word `f : ι → F` | `m` words at once, one Merkle leaf per **position**, leaf = the whole column `Fin m → F` |
| the query | one coordinate of one word | one position, **all `m` rows at it** |
| the reduction | fold `ι → κ`, halving the domain, `ℓ = 2` affine line | no domain change; a **random linear combination of the `m` rows**, checked against the claimed combined word |
| what recursion is | apply the fold again to a **smaller word** | commit `Mat(y_r)` — the *result* — as the next round's **matrix** |
| where the error comes from | proximity gap for the affine line `f₀ + α·f₁` | (i) proximity gap over the interleaving `Cᵐ`, (ii) the `|S|`-query miss `(1 − d/(2m))^{|S|}`, (iii) sumcheck `2k/|F|`, (iv) batching `1/|F|` |

The load-bearing difference is **(i)**: FRI needs a gap for `ℓ = 2`; Ligerito needs it for `ℓ = m`,
over the interleaving, with a *tensor-structured* coefficient vector rather than a free one.

### 2.2 The six requirements, retested

The prior lane's table is in `binaryspartan-position.md` §7.4. Retested against the tree, and
against a Lean file that now typechecks:

| requirement | prior verdict | **retested** |
|---|---|---|
| interleaved code `Cᵐ` | Absent | ⚠ **Overstated.** It is 12 lines: `interleavedCode m C : Submodule F (ι → Fin m → F)`, now in the tree and proved a genuine submodule. Nothing had to be invented. |
| **column distance** | "Absent — `relDist`/`close` **cannot express it**; a different metric" | ❌ **REFUTED.** DG24's column distance *is* Hamming distance at the alphabet `Fᵐ`. `relDistV_eq_relDist` proves our `relDist` is that function **by `rfl`**. The obstruction was the binder `[Field F]` on the *alphabet*, and `Selvage/CorrelatedAgreement.lean`'s own `omit [Field F]` annotations are its own evidence that the mathematics never used it. |
| proximity gap at `ℓ = m` | Absent, "the UD root-counting proof does not generalize" | ✅ **Confirmed absent, and this is the real work.** DG24 Thm 3.1 is unproved here. But see §2.3 — it is *stated* now, and its hypothesis is one we partly hold. |
| tensor coefficients `⊗ᵢ(1−rᵢ,rᵢ)` | Absent, "shape admitted, nothing proved" | ⚠ **Half.** The evaluated form exists (`eqMle`, `chiEval`) with the factorization law (`chiEval_split`, `mle_outerTable`). The **coefficient vector** did not exist; `tensorCoeff` now does. Nothing is *proved* about it — that part of the verdict stands. |
| column openings | Absent | ✅ **Confirmed.** `OpeningScheme.verifyOpen : Root → ι → F → Op → Prop` opens one coordinate of one word. Column leaves need the value type generalized `F → V` — **the same binder class as `relDist`**, so mechanical, but genuinely not done. |
| generic linear codes with distance `d` | Absent | ⚠ **Overstated.** `CorrelatedAgreement`, `codeword_eq_of_close_of_close`, `HalfThresholdRegime` and the Johnson list bound are all stated for an arbitrary `Submodule F (ι → F)` with distance entering as the hypothesis `hdC`. What is missing is a *bundled* `LinearCode` structure, which is convenience, not content. |

**Net: two of six "absent" verdicts do not survive contact, one is half-right, three stand.** The
strongest of the three — the `ℓ = m` proximity gap — is the one that matters, so the prior lane's
*conclusion* about cost was directionally right while two of its *reasons* were not.

### 2.3 ⚑ The finding that changes the cost: Ligerito's general-code bound sits at **our** radius

Ligerito has two bounds. They sit at different proximity radii, and this is not incidental:

* the **Reed–Solomon** bound uses `q + 1 = d/2` — the **unique-decoding** radius, imported from
  Diamond–Gruen Cor 3.7 on top of **BCIKS Thm 4.1**;
* the **general linear code** bound uses `q = d/3 − 1` — the **`d/3`** radius, from AER24 alone.

Our tree proves `rs_proximityGap_UD` **unconditionally** at `δ < (1−ρ)/3`, and for a Reed–Solomon
code `d/m ≈ 1 − ρ`, so

```
d/(3m)  ≈  (1 − ρ)/3          ← Ligerito's general-code radius
                              ← IS our proved radius, exactly
```

and `Selvage/HalfThresholdRegime.lean` reaches a comparable regime **char-agnostically, for every
linear code**. Meanwhile the `d/2` radius Ligerito's *headline* RS bound needs is precisely the one
our `Selvage/ProximityGapUDTight.lean` leaves open behind the named hypothesis
`PolishchukSpielman`.

**So the cheaper of Ligerito's two bounds is the one our floor already reaches, and the expensive
one fails on a leg we have already independently identified as open.** A formalization that
targets the general-linear-code bound inherits *no new* undischarged floor. One that targets the
RS bound inherits the BCIKS leg we already owe. That is a real sequencing result, and it inverts
the intuition that "RS is the easy case".

⚠ Priced honestly: the general-code bound costs **241 queries instead of 148** at `λ = 100`,
`ρ = 1/4` (§1.3, erratum 2). It is not a free substitution — it is a 1.63× proof-size penalty
bought in exchange for standing entirely on proved ground.

---

## 3. The exploratory Lean — landed and green

**`/Users/ember/dev/minidregg/Selvage/LigeritoInterleaved.lean`**, 567 lines, registered in
`Selvage.lean`. Committed as `0c08c93`.

[MEASURED] `lake build Selvage.LigeritoInterleaved`: **0 errors, 0 warnings**.
`lake build Selvage` (whole library, 3089 jobs): **green**.
`scripts/check-import-boundary.sh`: PASS. `scripts/check-proof-hygiene.sh`: PASS (469 files,
216 guarded axiom footprints). **No `sorry`, no `axiom`** — house law respected; unproved parts
are named obligation `Prop`s. Four `#guard_msgs … #print axioms` pins.

### What is proved

* **The alphabet-general layer** — `relDistV`, `closeV`, `AgreesOnV`, `combV`,
  `CorrelatedAgreementV`, `IsProximityGeneratorV` over any `F`-module alphabet `V`, with the
  metric lemmas (`relDistV_comm`, `hammingDist_add_card_le_of_agreesOnV`,
  `relDistV_le_of_agreesOnV`) reproved verbatim — they go through unchanged, which is the point.
* **The bridges, all by `rfl`** — `relDistV_eq_relDist`, `agreesOnV_eq_agreesOn`, `closeV_eq_close`,
  `correlatedAgreementV_eq_correlatedAgreement`, `isProximityGeneratorV_eq`, plus `combV_eq_comb`
  (`*` → `•`). The existing WHIR cone **is** the `V = F` instance.
* **`agreeSet_card_ge_of_relDistV_le`** — the converse of `relDist_le_of_agreesOn`, which
  `Selvage/CorrelatedAgreement.lean` does not have and the bridge needs.
* **`interleavedCode`** as a genuine `Submodule`, with `mem_interleavedCode`,
  `interleavedCode_top`, `swap_mem_interleavedCode`.
* ⚑ **`correlatedAgreement_iff_closeV_interleaved`** — the first real lemma:

  ```lean
  theorem correlatedAgreement_iff_closeV_interleaved [Nonempty ι]
      {C : Submodule F (ι → F)} {δ : ℝ} {f : Fin m → ι → F} :
      CorrelatedAgreement C δ f ↔ closeV δ (interleavedCode m C) (Function.swap f)
  ```

  An `↔`, over an arbitrary linear code, with **no characteristic hypothesis**.
* **The errata as theorems, not comments** — `rs_correctedBase_eq_one_sub_ud` (the corrected base
  *is* `1 − d/(2m)`), `correctedBase_sub_printedBase`, `printed_rs_bound_is_optimistic`,
  `printed_generic_bound_is_optimistic` (both errata understate the error at **every** query
  count), `ligeritoErrRS_nonneg`.
* **A characteristic-two keystone** — `correlatedAgreement_interleaved_charTwo` instantiates the
  bridge over `ZMod 2`, where `FoldingData` (which carries `two_ne : (2:F) ≠ 0` as a *structure
  field*) cannot go. Nothing in the file touches `FoldingData`.

### What is stated but not proved (named obligation `Prop`s, tag `[LIGERITO-interleaved]`)

`InterleavingPreservesProximityGap` (DG24 Thm 3.1) · `TensorStyleProximityGap` (DG24 Def 2.3,
stated with the counting measure over `Fin ϑ → F` and the materialized `tensorCoeff`) ·
`MatVecProductSound` (Ligerito §3) · `LigeritoSound` (Ligerito §6.3).

**Honest scope limit.** `LigeritoSound` is deliberately abstract in its acceptance predicate: this
file has no transcript object, and minting one here would be a twin of `Selvage/AccRbrBcs.lean`'s.
It carries the quantifier structure and the *corrected* error, nothing more.

---

## 4. Cost of a full formalization, in named missing lemmas

Not vibes. Each row is a statement someone would write.

### Tier A — to reach Ligerito §3 (the matrix-vector guarantee)

| # | missing lemma | note |
|---|---|---|
| A1 | `interleavedCode_minDist : (∀ u v ∈ C, u ≠ v → dC ≤ relDist u v) → ∀ U V ∈ interleavedCode m C, U ≠ V → dC ≤ relDistV U V` | **Cheap.** If two interleaved codewords differ, some row differs, so they differ in ≥ `d` positions. Days, not weeks. |
| A2 | `interleavedCode_uniqueDecoding` | Immediate from A1 + the *existing* `codeword_eq_of_close_of_close`. This is Ligerito §3's `∃!`. |
| A3 | `interleavingPreservesProximityGap` — **DG24 Thm 3.1** | ⚑ **The real work.** ~1.5 pages at source; uses only unique decoding (`e ≤ ⌊(d−1)/2⌋`), a pigeonhole on false witnesses, and row-wise application of `C`'s own gap. We hold the UD step. |
| A4 | `tensorCoeff_succ` — the Kronecker vector's recursion | Prerequisite for A5. Nothing is currently proved about `tensorCoeff`. |
| A5 | `tensorStyleProximityGap_of_affineLineGap` — **DG24 Thm 3.6 / AER24** | Induction on `ϑ`, folding two rows per step. |
| A6 | `openingSchemeV` — `OpeningScheme` with its value type generalized `F → V` | **Same binder class as `relDist`** — mechanical, but wide: every consumer of `verifyOpen` re-types. |
| A7 | `positionBinding_columns` — `BinaryMerkle` binding at column leaves | The survey notes `positionBinding_of_collisionFree` gives this "directly if you commit column-wise". Verify, do not assume. |
| A8 | `matVecProductSound_of_*` — a realizer discharging `MatVecProductSound` | Assembly of A1–A7. |

### Tier B — to reach Ligerito §6 (the recursion)

| # | missing lemma | note |
|---|---|---|
| B1 | `partialSumcheck_sound` — reduce `k → k'` variables, not `k → 0` | We have `sumcheck_soundness` at `v·d/|F|`; the *partial* variant is a generalization, not a new proof. |
| B2 | `batchedSumcheck_sound` — the `+1/|F|` batching term | Ligerito §4.3. |
| B3 | `gluedSumcheck_sound` — §4.3's "gluing" observation | Needed for the round-to-round hand-off. |
| B4 | `ligeritoSound_induction` — induction on `ℓ`, tallying the corrected `ligeritoErrRS` | The paper's §6.3 proof, which is genuinely an induction and genuinely short. |

### Tier C — the wall

| | |
|---|---|
| **Knowledge soundness** | Ligero-family extraction needs **expected-PPT rewinding extractors**. This is not a lemma; it is a framework we do not have, and the prior lane's "harder in Lean than anything else in this document" is not overstated. Ligerito's own note proves *soundness*, not knowledge-soundness, so this is inherited from the family, not owed to the note. |
| **BCIKS Thm 4.1 at `d/2`** | Only needed for the **RS** bound. `Selvage/ProximityGapUDTight.lean` already carries it behind `PolishchukSpielman`. **Avoidable** by targeting the general-linear-code bound (§2.3) at a 1.63× proof-size cost. |

### The honest summary

**8 + 4 = 12 named lemmas to a formalized Ligerito §3 and §6 soundness statement**, of which
**one (A3) is the substantial mathematics** and two (A6, A7) are wide-but-mechanical retypings of
the same binder class this lane already demonstrated is cosmetic. Tier C is not on that path for
*soundness*; it is on the path for *knowledge* soundness, which Ligerito itself does not prove.

**The negative result, stated plainly and earned:** the `ℓ = m` interleaved proximity gap
(A3) genuinely does not exist in our tree, and our `ℓ = 2` unique-decoding root-counting proof does
not generalize to it — that part of the prior lane's verdict survives testing. **What does not
survive is the claim that the metric and the code object are absent or inexpressible.** They cost
one binder and twelve lines respectively, and both are now in the tree and green.
