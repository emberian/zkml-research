# Ring-switching connectors: the Diamond–Posen read, the `Basis`, and the handoff

2026-08-14. Lane: LEAN BUILD — build the named gap between our machinery and the
compiler that would consume it.

**Landed in `~/dev/minidregg`:**

- `Theory/ExtensionBasis.lean` (commit `eb1c6bf`) — the subfield/extension
  `Basis` connector.
- `Selvage/RingSwitching.lean` (commit `f5b604f`) — Definition 2.2 and its
  reversal, the direction fix for `liftWord`, the tensor algebra, Remark 3.4's
  char-2 identity, Theorem 3.5's Schwartz–Zippel leg proved, the compiler's
  interface, and §7's handoff list.

Both axiom-pinned, no `sorry`. Substrate stated at the top of each file: neither
touches `Selvage/Proximity.lean`'s `FoldingData`, whose `two_ne : (2:F) ≠ 0` is
uninhabitable in characteristic two.

---

## 1. The paper, read — eprint 2024/504, *Polylogarithmic Proofs for Multilinears over Binary Towers* (Diamond, Posen)

Read from `~/paperbin/binius2-ring-switching-binary-towers-2024-504.txt`,
theorem statements and proofs, not the abstract.

### What ring-switching actually is

A **compiler**, and it is stated as one. Construction 3.1 takes as *input* a
multilinear polynomial commitment scheme `Π′ = (Setup′, Commit′, P′, V′)` over a
large field `L`, and *outputs* a small-field scheme `Π = (Setup, Commit, P, V)`
over a subfield `K` with `deg(L / K) = 2^κ`. It is agnostic to `Π′` — the paper
says so explicitly, naming Blaze and WHIR and "even large-field schemes that
haven't been created yet."

The compilation is:

- `Setup(1^λ, ℓ, K)` runs `Setup′(1^λ, ℓ′)` where **`ℓ′ = ℓ − κ`**. ⚑ Note the
  fixpoint: `L` is *returned by* `Setup′`, and `κ` is determined by `L`, so the
  caller must solve `ℓ′ = ℓ − κ(L(ℓ′))`. The compiler does not choose `κ`.
- `Commit(t)` for a `K`-multilinear `t(X₀,…,X_{ℓ−1})` **packs** it into an
  `L`-multilinear `t′(X₀,…,X_{ℓ′−1})` (Definition 2.2) and calls `Commit′(t′)`.
- The evaluation IOP: the prover sends one element `ŝ` of the *tensor algebra*
  `A = L ⊗_K L`; the verifier checks a column identity, samples `κ` batching
  scalars, and the two run an `ℓ′`-round **degree-2** sumcheck on
  `h = A · t′`; the whole thing terminates in one call to `Π′`'s evaluation
  protocol at `(s′, r′)`.

**Definition 2.2 (packing).** For an extension `L/K` with `K`-basis
`(β_v)_{v∈B_κ}` and a `K`-multilinear `t(X₀,…,X_{ℓ−1})`, with `ℓ′ := ℓ − κ`,

> `t′(X₀,…,X_{ℓ′−1}) := Σ_{v∈B_κ} t(v₀,…,v_{κ−1}, X₀,…,X_{ℓ′−1}) · β_v`

In Lagrange-coefficient terms: replace each `2^κ`-element chunk of `t`'s
coefficient vector with the single `L`-element obtained by basis-combining that
chunk. The paper emphasises: **"Definition 2.2's packing procedure is
reversible."**

### Theorem 3.5, stated properly

> **Theorem 3.5.** If `Π′ = (Setup′, Commit′, P′, V′)` is secure, then
> `Π = (Setup, Commit, P, V)` also is.

"Secure" is Definition 2.9, and the *shape of that definition is the reason the
theorem is provable by construction*:

> **Definition 2.9.** For a PPT adversary `A` and PPT emulator `E`: the
> experimenter samples `params ← Setup(1^λ, ℓ)`; `A` interacts with the vector
> oracle and outputs a handle `[f]`; **`E`, on `A`'s record of interactions,
> outputs `t(X₀,…,X_{ℓ−1})` — before seeing `r`**; the verifier samples `r`,
> `A` claims `s`, the evaluation IOP runs to a bit `b`.
> `Real := s if b=1 else ⊥`; `Ideal := t(r) if t ≠ ⊥ and b=1 else ⊥`. `Π` is
> secure if for every `A` there is an `E` with
> `Pr[Real ≠ Ideal] ≤ negl(λ)`.

⚑ The extraction is **straight-line**: `E` commits to `t` *immediately after the
commitment*, with no rewinding. The paper says it adopts this stricter form
"owing essentially to their use of Reed–Solomon codes, which are efficiently
decodable," and that it is what makes composability easy.

**The proof of 3.5 is an emulator construction, in three lines:**

1. `E` runs `Π′`'s emulator internally: `t′ ← E′`.
2. If `t′ = ⊥`, output `⊥`.
3. **"By reversing Definition 2.2, `E` obtains `t(X₀,…,X_{ℓ−1}) ∈ K[X]^{⪯1}`,
   which it outputs."**

Then four bad events are excluded, in order: `E′` fails (negligible, by `Π′`);
`t′(r′) ≠ s′` while `b′ = 1` (negligible, by `Π′`); the batching scalars miss a
wrong first message — Schwartz–Zippel on
`S(X) := Σ_{u∈B_κ} (ŝ_u − s_u)·eq~(u, X)`, bad set `≤ κ/|L|`; and the sumcheck
launders the resulting false claim, `≤ 2ℓ′/|L|`.

**Added soundness error: `(2ℓ′ + κ)/|L|`.**

### What it requires of the small ring and the large one

| requirement | where it bites |
|---|---|
| `L / K` a field extension of degree `2^κ` | the index set `B_κ` and the arity `ℓ′ = ℓ − κ` |
| a fixed `K`-**basis** `(β_v)_{v∈B_κ}` of `L` | Definition 2.2 (packing) and Theorem 3.5 step 3 (unpacking) |
| `L` large enough that `(2ℓ′+κ)/|L|` is negligible | §3.2 assumes `deg(L/K) = λ`, giving `|L| ≥ 2^λ` |
| `K` arbitrary, `L` of any characteristic including 2 | stated in §1.2 |
| the tensor algebra `A = L ⊗_K L` and its column/row views | the prover's first message `ŝ` |

⚑ **What it does NOT require:** nothing about `Π′`'s internals — no code, no
domain, no characteristic, no smooth subgroup. The interface is `Setup′`,
`Commit′` on an `L`-multilinear, and an evaluation protocol at an arbitrary
point of `L^{ℓ′}`, plus completeness and Definition-2.9 security.

### The interface it needs from the PCS it compiles

Exactly three call sites, and two hypotheses:

1. `Setup′(1^λ, ℓ′) → (params, L)`.
2. `Commit′(params, t′)` for `t′ ∈ L[X₀,…,X_{ℓ′−1}]^{⪯1}`.
3. `⟨P′([f], s′, r′; t′), V′([f], s′, r′)⟩` — evaluation at an **arbitrary**
   `r′ ∈ L^{ℓ′}` (the sumcheck's challenge point, off any evaluation domain).
4. Hypothesis: `Π′` complete (Theorem 3.2).
5. Hypothesis: `Π′` secure in the Definition 2.9 straight-line sense
   (Theorem 3.5).

That is the whole surface. `Selvage/RingSwitching.lean`'s
`LargeFieldMlePcs` + `Complete` + `Extractable` is it, in Lean.

### The paper's own instantiation (§4), for reference

Construction 4.12 is "a characteristic-2 adaptation of BaseFold": commit by
Reed–Solomon-encoding over an `F₂`-affine domain chain `S^(0) ⊃ S^(1) ⊃ …`
built from an *ordered* `F₂`-basis `(β_0,…,β_{ℓ+R−1})`, then run a sumcheck on
`h = eq~(r, X)·t(X)` interleaved with FRI folds
`fold(f^(i), r) ` (Definition 4.6, the **additive** fold — Remark 4.10 notes its
matrix is the inverse additive-NTT butterfly). Theorem 4.13: complete.
Theorem 4.17: secure. Corollary 4.5 is the fact that
`Ŵ_i(β_{ℓ+R−1})` is an `F₂`-basis of `S^(i)` — the domains fold *with their
bases*.

---

## 2. The `Basis` connector — `Theory/ExtensionBasis.lean`

**Mathlib was checked first and hard, and Mathlib had almost all of it.** The
connector is assembly, not construction:

| needed | Mathlib gives |
|---|---|
| a basis of a finite extension | `Module.finBasisOfFinrankEq` (`Module.Free` + `Module.Finite` are automatic over a field / for a finite type) |
| cube indexing `B_κ` instead of `Fin (2^κ)` | `Basis.reindex` along `Fintype.equivOfCardEq` |
| the coordinate map | `Basis.equivFun : L ≃ₗ[K] (B_κ → K)` |
| degree from cardinality | `Module.natCard_eq_pow_finrank` |
| dimension transport | `LinearEquiv.finrank_eq`, `Module.finrank_fintype_fun_eq_card` |
| the tensor algebra and its array basis | `Algebra.TensorProduct.includeLeft/includeRight`, `Basis.tensorProduct`, `Module.finrank_tensorProduct` |

The one thing nobody had written was the *reindexing to the cube* and the
packing map built on it.

### What landed

- `cubeBasis (hdeg : finrank K L = 2^κ) : Basis (Fin κ → Bool) K L`.
- `packOf β l` — Definition 2.2 for an **arbitrary** family (so failure modes
  are expressible); `packEquiv b l` — the same at a `Basis`, as a `K`-linear
  **equivalence**; `packCube b l` — the `ℓ = κ + ℓ′` form.
  **`.symm` is Theorem 3.5's step 3.**
- `finrank_packed_eq` — **zero embedding overhead as a dimension identity**,
  derived *from* the equivalence: the packed target
  `(B_{ℓ′} → L)` carries exactly `2^(κ+ℓ′)` `K`-coordinates, the count the
  unpacked `K`-multilinear carries.
- `lift_overhead_factor` — and an element-wise lift's target carries `2^κ`
  times as many.
- `towerExt_finrank : finrank (T_j) (T_{j+d}) = 2^d`.

⚑ **The tower fact is nicer than expected and is worth stating on its own:**
`|T_k| = 2^(2^k)`, so `[T_{j+d} : T_j] = 2^d` — **every sub-level extension of
the binary tower has degree an exact power of two, and `κ = d` exactly.**
Crossing `d` tower levels consumes `d` multilinear variables. That is *why*
`B_κ` and not `Fin (2^κ)` is the right index type, and it is why the binary
tower is the natural home for ring-switching rather than a convenient one.
Deployed Binius shape `T₀ ⊂ T₇`: `κ = 7`, degree 128, built as
`biniusCubeBasis`.

### Teeth (instantiations that must be refused)

- `no_cubeBasis_of_finrank_ne` — a wrong `κ` admits **no** cube-indexed basis.
- `packOf_not_injective_of_repeat` — a coordinate family with a repeat packs two
  distinct `K`-witnesses onto one `L`-object. Extraction dies; the type does not
  notice.
- `algebraMap_not_surjective` / `liftFun_not_surjective` — the element-wise lift
  is not surjective once `[L:K] > 1`.

### Honest residual

`cubeBasis` produces `Classical.choice`'s basis, not the Fan–Paar tower basis
the deployed arithmetic uses. Every statement quantifies over `b`, so pinning it
to `Theory/BinaryTowerFanPaarCodec`'s coordinates is a separate constructive
job. **It changes the prover's cost, not the compiler's soundness.**

---

## 3. `liftWord` — why it points the wrong way, and both directions

`Selvage/SmallField.lean:225`:

```lean
def liftWord (f : ι → Fq) : ι → K := fun i => algebraMap Fq K (f i)
```

It maps a `K`-word to an `L`-word **of the same length**. Ring-switching's
packing maps a `K`-word to an `L`-word **`2^κ` times shorter**. Diamond–Posen
open §1 by rejecting exactly this construction:

> "One might trivially attempt to commit to a tiny-field multilinear simply by
> embedding its coefficients into an extension… it would impose an artificial
> penalty proportional to the ratio between its input's original coefficient
> bitwidth and the scheme's native field's bitwidth."

That ratio is `lift_overhead_factor`'s `2^κ`.

**The relationship, proved** (`liftWord_eq_packOf_zero`): `liftWord` **is**
ring-switching's packing map at `κ = 0`. It is not a different construction; it
is the degenerate instance, at the one arity that contracts nothing.

**The refusal, proved** (`liftWord_not_packing`): at `[L:K] > 1` the lift is not
surjective, so no reindexing and no choice of basis makes it Definition 2.2's
map. `packOf` at a basis is bijective; the lift is not.

**The missing direction, supplied**: `unpackWord b l = (packEquiv b l).symm`,
with `unpackWord_bijective`. This is the map the tree did not have and the one
the emulator needs.

---

## 4. Extra connectors found en route

### The tensor algebra is Mathlib's, and Remark 3.3 is a theorem

`A = L ⊗[K] L`; `φ₀ = Algebra.TensorProduct.includeLeft`,
`φ₁ = includeRight`; Figure 9's `2^κ × 2^κ` `K`-array is
`Basis.tensorProduct b b`. The paper observes (crediting Raju Krishnamoorthy)
that `t(r_κ,…,r_{ℓ−1})` relates to the message `ŝ` by the multiplication map
`h : L ⊗_K L → L`, "which is of course not injective", so `ŝ` cannot be
replaced by a single field element.

`tensorMul_not_injective` proves it by dimension count: `(2^κ)² > 2^κ`.
**Consequence, worth saying plainly: a ring-switching verifier handed one
`L`-element in place of `ŝ` is unsound, not merely lossier.**

### Remark 3.4's identity, and it is characteristic-2-only

`eqMle_charTwo`: in characteristic 2,
`eq~(z,x) = ∏ᵢ (1 − zᵢ − xᵢ)`. This is what makes the verifier's `e` computable
in `2·ℓ′·2^κ` `L`-multiplications by the paper's three-line loop.
`eqMle_charTwo_fails_at_five` shows the cheap form computes the **wrong** `e`
over `F₅` — so it is a genuine char-2 dividend, not a restatement.

### ⚑ Theorem 3.5's Schwartz–Zippel leg was already in the tree

`Selvage/MultilinearZeroTest.lean`'s `eqMle_zero_test` states exactly
`Pr_{z}[Σ_b eq~(z, b)·D(b) = 0] ≤ m/|F|` for `D ≠ 0`. That is Theorem 3.5's
batching bound verbatim. `ringSwitch_batching_bound` is it, re-stated in
ring-switching's vocabulary — **one of the two probabilistic legs the compiler
contributes is discharged at the paper's own constant.**

---

## 5. What a characteristic-2 BaseFold must provide — the handoff

`Selvage/AdditiveBaseFold.lean` (sibling lane, uncommitted at time of writing)
is building the other end. This is the list, and it is in the tree as
`Selvage/RingSwitching.lean`'s `RingSwitchTarget` plus its docstring.

**The two formal obligations** (`RingSwitchTarget`'s fields):

1. **`Complete`** — an honest commitment plus a true evaluation claim is
   accepted. This is Theorem 3.2's hypothesis and nothing else.
2. **`Extractable`** — Definition 2.9's straight-line extraction: a table `t`
   determined by the *commitment alone*, before the evaluation point, whose MLE
   agrees with every accepted claim. This is Theorem 3.5's hypothesis.

**The five shape requirements** — these are what actually break compositions:

3. **Arity: `ℓ′ = ℓ − κ`, never `ℓ`.** The compiler hands `Π′` a *shorter*
   multilinear over a *bigger* field. At the deployed Binius shape
   (`K = T₀`, `L = T₇`, `κ = 7`) a `2^20`-coefficient bit-multilinear becomes a
   `2^13`-coefficient `GF(2^128)` one. And note the fixpoint (§1): `Setup′`
   chooses `L`, hence `κ`, hence `ℓ′` — the compiler does not.

4. **Table form, not codeword form.** `commit` takes the Lagrange coefficient
   table `(Fin ℓ′ → Bool) → L`. `AdditiveBaseFold`'s `lchLevelWord` is an
   *evaluation word* on the level-`n` additive domain. The bridge is its
   Boolean-Möbius layer (`booleanMobiusPolynomial` / `tableOfPoly`), which that
   file already documents as porting verbatim because it is a change of basis on
   coefficient vectors with no characteristic in it.

5. **Evaluation at an arbitrary `r′ ∈ L^{ℓ′}`, off the domain.** The sumcheck
   hands `Π′` a point sampled from `L`, not a domain point.
   `lchLevelWord_terminal` terminating at `mle (tableOfPoly m p) r` is the right
   shape.

6. ⚑ **BLOCKING: the transcript must bind the ORDERED basis `β`, not just its
   span.** `AdditiveBaseFold`'s own `keystone_basis_ambiguity` exhibits one
   codeword, on one four-point domain over `GF(16)`, that is an honest
   commitment to **two different tables** under two orderings of the same
   `GF(2)`-basis (`β = (1, x₁)` vs `β′ = (x₁, 1)`). **Ring-switching's
   `Extractable` is FALSE for a scheme with that ambiguity** — the emulator
   cannot produce *the* table. This is not a hygiene note; it is a prerequisite,
   and it is a good thing that lane found it before the seam was built. The
   paper's Corollary 4.5 is the same fact from the other side: the domains fold
   *with their ordered bases*.

7. **No `FoldingData` anywhere on the path.** The compiler is
   characteristic-agnostic, but any `Π′` reached through `Selvage/Proximity`'s
   `FoldingData` is vacuous at `CharP L 2`
   (`Selvage/CharTwoWall.lean`'s `foldingData_charTwo_False`). `Π′` must come
   through the additive cone.

**And one thing the additive lane does *not* have to build.** Definition 2.9's
straight-line extraction wants a decoder within the unique-decoding radius.
`Selvage/SubUdSeam.lean`'s `subUdRecover (dom : ι ↪ F) (d : ℕ) (δ : ℝ)` is
stated over `[Field F]` with **no characteristic hypothesis and an abstract
`dom : ι ↪ F`** (checked: section variables at `SubUdSeam.lean:143–144`), so it
instantiates at an additive domain unchanged. `subUdRecover_sound`
(`SubUdSeam.lean:221`) pins the recovered codeword uniquely on
`δ < (1 − (d−1)/n)/2` — half the relative distance. And
`Selvage/AdditiveProximity.lean:286`'s `additiveFold_distance_UD` carries
`[CharP F 2]` and lives on `δ < 1 − (2 + d/|R|)/3`, which is `(1−ρ)/3` — inside
that radius. **The extractor and its radius are already code-agnostic and the
char-2 distance bound is already proved; what is missing is the wiring, not the
mathematics.**

---

## 6. What is NOT done, stated as work rather than as a boundary

`RingSwitchSecure` in `Selvage/RingSwitching.lean` is a **named obligation**:
the assembly step of Theorem 3.5, given the two legs. Discharging it needs

- the product-uniform marginalization and union bound over
  `(r″, r′) ← L^κ × L^{ℓ′}` (the tree has `uniformProb` and, per
  `Selvage/Depth.lean`, a pushforward bound — this is plumbing, not new
  mathematics); and
- the `ℓ′`-round **degree-2** sumcheck transfer over `h = A · t′`, connected to
  the tensor-algebra identity (30). `Selvage/Sumcheck.lean`'s
  `sumcheck_soundness` has the right shape (`v·d/|F|` at `d = 2`) and
  `Selvage/QuadraticSumcheck.lean` exists; **nothing in the tree connects either
  to `A`'s row and column decompositions.** That connection is the next piece of
  work.

The obligation is deliberately *not* of the `∃ err, err ≤ bound` shape a reader
could discharge by inspection — its hypotheses constrain a supplied accepting
set and a wrong constant refutes it — and
`ringSwitchSecure_hypotheses_inhabited` shows its antecedent is satisfiable, so
it is not true-because-empty.

Also not done, and both are cheap-but-real: pinning `cubeBasis` to the Fan–Paar
coordinates (a prover-cost matter), and instantiating `subUdRecover` at the
additive domain (a wiring matter).
