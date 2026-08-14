# BinarySpartan — analysis and position

Date: 2026-08-14. Status: **in progress, written incrementally.**

Provenance legend used throughout:
- **[READ]** — I read the primary source myself, at the cited file/line.
- **[CLAIM]** — asserted by a tweet/slide/brief; not verified at source.
- **[MEASURED]** — I ran the command and this is its output.

---

## 0. The claim under analysis

BinarySpartan (Setty, MSR; in the eprint review queue, draft not public) = **Spartan over a binary
field, with Ligerito as the PCS and Diamond–Posen ring-switching.** [CLAIM]

The framing that matters, from the abstract as relayed: *"All but the last optimization were
developed in the context of prime fields... BinarySpartan is not a new proof system but rather a
natural instantiation of Spartan over binary fields."* [CLAIM]

**If that framing is true, it is the whole opportunity.** An instantiation has no machine-checked
compilation layer. The question is not whether we can match 410k hashes/sec — we cannot and should
not try. The question is whether *our* compilation layer transfers to the binary instantiation.

---

## 1. What Ligerito actually is, and what its soundness rests on [READ]

Source: `/Users/ember/paperbin/ligerito.pdf` — Novakovic & Angeris (Bain Capital Crypto), **May
2025**. Extracted with `pdftotext`; 1594 lines.

⚠ **First correction to the brief's mental model.** Ligerito is **not** FRI-shaped. It is
**Ligero-shaped**: an interleaved linear code with **column/row openings**, merged with a **partial
sumcheck**, applied **recursively** over ℓ rounds. From §1:

> "Ligerito, a new polynomial commitment scheme and inner product argument, which works over
> essentially any code that has the following property: any row of the code's generator matrix can
> be efficiently evaluated."

Benchmarked over a **32-bit binary field**: 2^24 coefficients, M1 MacBook Pro, Julia prover, **1.3 s
proving, 255 KiB proof**. Proof size ~log(N)²/log log(N).

⚠ **The paper has no `Theorem` environment anywhere.** [MEASURED — `grep -n "Theorem"` returns no
theorem statements, only section text.] It gives "a simple proof of its error bounds" as running
prose, and it **delegates the load-bearing proximity step to two cited papers**. From §2:

> "we refer readers to [AER24] and [DG24] for proofs which we will rely on throughout."

### The actual soundness dependency chain [READ]

Ligerito §3's "matrix-vector product protocol" guarantee is the black box everything else uses:

> 1. There exists some unique matrix X̃ such that ‖X − G·X̃‖ < d/2, where d is the distance of the
>    Reed–Solomon code G
> 2. The vector y_r satisfies y_r = X̃·r

with error probability, for Reed–Solomon:  `((m − n − 1)/2m)^|S| + mk/|F|`
and for a **general linear code**:  `(1 − d/(3m))^|S| + dk/(3|F|)`

Note **‖·‖ < d/2 — this is the UNIQUE DECODING radius**, not Johnson, not capacity. Ligerito's
recursive composition (§6.3) tallies UD-regime terms only.

The chain, resolved to primary sources:

```
Ben-Sasson–Carmon–Ishai–Kopparty–Saraf (BCIKS), JACM 2023, Thm 4.1
    RS codes exhibit proximity gaps for affine lines up to the UD radius, ε = n
        ↓
Diamond–Gruen, eprint 2024/1351, "Proximity Gaps in Interleaved Codes", Thm 3.1
    lifts proximity gaps from a code C to its INTERLEAVING C^m
        ↓
Angeris–Evans–Roh, eprint 2024/1399, reproduced as DG24 Thm 3.6
    lifts affine-line gaps for all C^m to TENSOR-STYLE proximity gaps
        ↓
DG24 Corollary 3.7 — RS features tensor-style proximity gaps for e ≤ (d−1)/2, ε := n
        ↓
Ligerito §3 matrix-vector product guarantee
        ↓
Ligerito §6 recursive composition (+ partial sumcheck, + Merkle openings)
```

### ⚑ The single most important sentence in this note

**Diamond–Gruen 2024/1351 Theorem 3.1, read at source**
(`~/dev/gh/forks/IACR-eprint-mirror/2024/1351.pdf`):

> "We fix a field F_q and an arbitrary [n, k, d]-code C ⊂ F_q^n.
> **Theorem 3.1.** If C features proximity gaps for affine lines with respect to the proximity
> parameter e ∈ {0, …, ⌊(d−1)/2⌋} and the false witness bound ε ≥ e + 1, then, for each m > 1,
> C's interleaving C^m also does."

**This is stated over an arbitrary field F_q and an arbitrary linear code. There is no
characteristic hypothesis, no multiplicative subgroup, no root of unity, no smoothness.** It holds
in GF(2^k) exactly as written. Same for Thm 3.6 (AER24), which is also code-generic.

**The only RS-specific, and therefore the only possibly field-sensitive, step in the whole chain is
the base case — BCIKS Thm 4.1.** Everything above it is a generic lift. And Ligerito supplies a
general-linear-code fallback bound that does not need RS at all.

That makes the Ligerito soundness foundation an unusually well-shaped formalization target: two
generic lifting theorems over an abstract field, sitting on one imported base case, composed by
exactly the kind of round-by-round bookkeeping our compilation layer already does.

---

## 2. The binder census — is our substrate prime-pinned? [MEASURED]

Run over `/Users/ember/dev/minidregg/Selvage/*.lean` (125 files):

| binder | count |
|---|---|
| `variable {F : Type*} [Field F]` | 40 |
| `variable {F : Type} [Field F]` | 25 |
| `variable {F : Type*} [CommRing F]` | 4 |
| `[Field F]` (total) | 169 |
| `[Fintype F]` | 251 |
| `[DecidableEq F]` | 303 |
| `[CharP F 2]` | 13 |
| **`[CharP F p]` for odd/prime p** | **0** |

**There is no prime-field pin in the binders.** The substrate is `[Field F] [Fintype F]
[DecidableEq F]` — a finite field, which GF(2^k) is.

Char-2 hazard sweep [MEASURED]: every `/ 2` hit in `AccRbrBcs.lean`, `AccSound.lean`,
`AccRbrInstance.lean`, `AuditSampling.lean`, `CollisionResistanceROM.lean` is **ℝ-valued** —
distance ratios (`δ < dC / 2`) and probabilities (`q * (q−1) / 2`). None divides by `(2 : F)`.

⚠ **And we already have a char-2 branch.** These carry `[CharP F 2] [Algebra (ZMod 2) F]` today:
- `Selvage/AdditiveProximity.lean` — `foldedCloseToDeg_iff_close`, `additiveProximityGap_of_isProximityGenerator`, `additiveProximityGap_UD`, `additiveFold_distance_UD`
- `Selvage/AdditiveFriQuery.lean` (`structure AdditiveFriTower`, L74), `Selvage/AdditiveFriTower.lean` (L28)
- `Theory/AdditiveNTT.lean`, `Theory/AdditiveNTTTransform.lean`, `Theory/BinaryTower.lean`
  (`binaryTower_char_two`, L82), `Theory/BinaryTowerCodec.lean`, `Theory/BinaryTowerFanPaarCodec.lean`

⚠ **Correction to the brief: the binary cone is not "unwired to anything."**
`/Users/ember/dev/minidregg/docs/SELVAGE-COMPLETE.md` [READ] describes a landed **Tower256 additive
FRI Lean-owned controller** (decodes proof bytes in Lean, derives roots-before-challenges, checks
Merkle openings and fold equations, reaches `AdditiveFriAdaptiveCoherentAccepts`), a **Tower256
indexed LogUp** clause-404 dispatcher, and a **deployed native work `9101` "Tower256 dot product"**
in base V1. Under adjudication by a lane; recorded here as a live contradiction with the brief.

### Where the prime pins actually live [MEASURED]

`ZMod` occurrences across `Selvage/` + `Assurance/`:

| field | count |
|---|---|
| `ZMod 5` | 1127 |
| **`ZMod 2`** | **202** |
| `ZMod 7` | 47 |
| `ZMod 11` | 14 |
| `ZMod 13` | 2 |

These are **witnesses, teeth and counterexamples**, not theorem binders — the general results are
stated over `[Field F]` and these instantiate them at a small concrete field to fire a `decide`.
`ZMod 5` is the house toy field. Note **202 `ZMod 2` occurrences**: a binary-field instance layer
already exists.

The **BabyBear** pins are concentrated in exactly the modules you would expect — the *deployed
instantiation* layer, not the theory: `Selvage/BaseFoldBcs{ByteCodec,FiatShamir,Padding,QuerySamplingJoint}.lean`,
`Selvage/BaseFoldPoseidon2{,Rom}.lean`, `Selvage/ExtensionChallengeBridge.lean`,
`Selvage/SmallField.lean`, `Selvage/Rank1GradientCheck.lean`, `Selvage/ZkmlPoseidon2Data.lean`.

**That is the whole shape of the answer to Question 1, in one line: the theory is field-generic, the
instantiation is BabyBear, and the char-2 instantiation is already partly built.**

### The structural fact that decides most of the FRI cone

A **multiplicative** FRI/RS line needs a smooth multiplicative subgroup of order 2^k. In GF(2^k) the
multiplicative group has order 2^k − 1, which is **odd** — no such subgroup exists, at any k. That
is why Binius/BinarySpartan use *additive* NTT over affine subspaces. So for every proximity keystone
the question is: is the evaluation domain a *multiplicative subgroup* (`IsPrimitiveRoot`, `orderOf`,
`ω`) or an *abstract `Finset F` / affine subspace*? The former does not transfer; the latter does.

**Ligerito sidesteps this entirely** — it needs "any linear code whose generator rows are efficiently
evaluable", not a smooth domain. That is a large part of why it is the PCS BinarySpartan picked.

---

## 3. What ring-switching actually is [READ]

Source: `/Users/ember/paperbin/binius2-ring-switching-binary-towers-2024-504.txt` — Diamond & Posen
(Irreducible), *"Polylogarithmic Proofs for Multilinears over Binary Towers"* = eprint **2024/504**.
Confirmed: this **is** the Diamond–Posen ring-switching paper named in BinarySpartan's abstract.

⚠ **Do not confuse it with the other Diamond–Posen paper.** Ligerito's *logarithmic randomness*
comes from Diamond–Posen, *"Proximity Testing with Logarithmic Randomness"* (Commun. Cryptol. 2024)
— a **different** paper. Both are load-bearing in BinarySpartan, for different reasons.

### Ring-switching is a compiler with a security-preserving reduction

From the abstract:

> "We introduce a sumcheck-based **compiler** — called 'ring-switching' — which, upon being fed a
> multilinear polynomial commitment scheme over some large extension field, yields a further scheme
> over that field's ground field. The resulting scheme **lacks embedding overhead**, in that its
> commitment cost, on each input, equals that of the large-field scheme on each input of identical
> size (in bits)."

The two load-bearing results are **preservation theorems**:

> **Theorem 3.2.** If Π′ = (Setup′, Commit′, P′, V′) is complete, then Π = (Setup, Commit, P, V)
> also is.
>
> **Theorem 3.5.** If Π′ = (Setup′, Commit′, P′, V′) is secure, then Π = (Setup, Commit, P, V)
> also is.

Theorem 3.5 is proved by **constructing an emulator E for Π out of the emulator E′ for Π′** (§3, proof
step 1–3: run `t′ ← E′`; abort on ⊥; otherwise invert Definition 2.2 to recover `t ∈ K[X]⪯1`).

**⚑ This is the single best-matched formalization target in the entire BinarySpartan stack, and the
reason is structural, not lucky.** Ring-switching is not a new hardness assumption or a new code — it
is a *compiler between proof systems, with a straight-line emulator-based extraction argument*.
Machine-checking compilers with security-preserving reductions is precisely and exclusively what the
Selvage layer is: RBR→Fiat–Shamir over an inhabited oracle, BCS at the deployed alphabet,
accumulation-depth composition, and straight-line extraction are all theorems of that same shape.

Supporting structure that is also clean to formalize:
- **Definition 2.10, small-field IOPCS** — a tuple `(Setup, Commit, P, V)` where `Setup(1^λ, ℓ, K)`
  emits `params` including an extension `L/K`; `Commit` takes `t ∈ K[X_0..X_{ℓ−1}]⪯1`; the IOP runs
  over `L`; security as Def 2.9 except the emulator must output a polynomial **over K**. A crisp
  interface, and the K-vs-L split is exactly the subfield/extension bookkeeping our
  `ExtensionChallengeBridge` / `SmallField` modules exist for.
- **Definition 2.2, the ring-switch equality indicator**, parameterized by a K-basis `(β_v)_{v∈B_κ}`
  of `L/K` — and we have Fan–Paar basis and trace facts proved in
  `/Users/ember/dev/minidregg/Theory/BinaryTowerFanPaar.lean` (578 lines) and
  `Theory/BinaryTowerTrace.lean` (351 lines).

### Two further confirmations that our char-2 cone is on the right line

1. Ring-switching needs a **large-field target scheme to compile from**, and the paper says (§1.2)
   that to get one it "develop[s] a **characteristic-2 adaptation** of [BaseFold] at length." We hold
   a BaseFold cone (`Selvage/BaseFold*.lean`, ~20 files, completeness + an RBR soundness instance)
   *and* a char-2 additive-proximity cone (`Selvage/AdditiveProximity.lean`, `AdditiveFriTower.lean`).
2. That char-2 BaseFold adaptation rests on **Lin–Chung–Han's additive NTT** ("the key result is
   Theorem 4.13"). We hold `Theory/AdditiveNTT.lean` and `Theory/AdditiveNTTTransform.lean`, both
   under `[CharP F 2]`, with `additiveFold_distance`, `additiveFold_distance_exact`,
   `close_of_correlatedAgreement`, `foldMap_injOn_transversal`.

### And the same proximity result carries both legs

Ring-switching's §2 cites **Theorem 2.4 (Diamond–Gruen [DG25, Cor. 1])** — the *same* interleaved /
tensor-style proximity gap corollary that Ligerito's matrix-vector guarantee rests on (§1 above).

So **one theorem — Diamond–Gruen's UD-regime interleaved-code proximity lift, stated over an
arbitrary field and an arbitrary linear code — sits under both the PCS and the ring-switching leg of
BinarySpartan.** If a single formalization target had to be picked, that is it.

---

## 4. The crux, measured: how far is `CorrelatedAgreement.lean` from Diamond–Gruen? [READ]

`/Users/ember/dev/minidregg/Selvage/CorrelatedAgreement.lean` (533 lines). Binders, L67–69:

```lean
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]
variable {ℓ : ℕ}
```

**No characteristic, no cardinality, no prime.** The code carrier is `C : Submodule F (ι → F)` —
an arbitrary linear code over an arbitrary field on an arbitrary finite index type. This is
*literally* Diamond–Gruen's "we fix a field F_q and an arbitrary [n,k,d]-code C ⊂ F_q^n".

The load-bearing theorem, L325 (WHIR Lemma 4.10), proved with a real proof body:

```lean
theorem hasMutualCorrelatedAgreement_of_isProximityGenerator [Nonempty ι]
    (G : ProximityGenerator F ℓ) (C : Submodule F (ι → F)) {B : ℝ}
    {err : ℝ → ℝ} {dC : ℝ}
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hPG : IsProximityGenerator G C B err)
    (herr_mono : …) (herr_nonneg : …) :
    HasMutualCorrelatedAgreement G C (max (1 - dC / 2) B) err
```

Its own docstring: *"correlated agreement gives mutual correlated agreement for free in the
**unique-decoding regime**, for **EVERY linear code**."* The regime is `δ ∈ (0, min {dC/2, 1−B})`,
and the proof turns on unique decoding (`codeword_eq_of_close_of_close`, L165).

**So we already work in exactly Diamond–Gruen's setting: arbitrary field, arbitrary linear code,
unique-decoding radius, correlated-agreement conclusion.** The supporting idiom is all there —
`relDist` (L75, on Mathlib `hammingDist`), `close` (L112), `AgreesOn` (L119), `comb` (L179),
`ProximityGenerator` (L202), `CorrelatedAgreement` (L253), `IsProximityGenerator` (L264).

### The one object that is missing, named exactly [MEASURED]

**The interleaved code `C^m` and its block distance `d^m` do not exist in the repo.**

- `grep -i "interleav"` across `Selvage/` and `Theory/` returns **only polynomial parity
  interleaving** — `parityInterleave` in `BaseFoldCompleteness.lean` and
  `MultiplicativeMleTerminal.lean`, which is BaseFold's even/odd coefficient split. Unrelated.
- `grep -i "tensor"` returns nothing relevant — there is no tensor-style proximity gap definition.
- Code carriers in `Selvage/`: `Submodule F (ι → F)` ×169, `Submodule F (Fin m → F)` ×49. Always a
  **single-word** code. Never a matrix/interleaved one.

**But the gap is a definition, not a wall.** Diamond–Gruen's `d^m(U,V) = |{j : column j of U ≠
column j of V}|` is *already* what `relDist` computes if the word's value type is `Fin m → F`
instead of `F` — Mathlib's `hammingDist` is generic in the codomain, so `relDist` needs its codomain
generalized, not rewritten. And `C^m` is `{U : ι → (Fin m → F) | ∀ i, (U · i) ∈ C}`, a `Submodule`.

So the shortest real path from what we hold to Ligerito's foundation is:

1. generalize `relDist` / `AgreesOn` / `close` in the codomain (mechanical);
2. define the interleaved code `C^m` and `d^m` (a definition);
3. prove **Diamond–Gruen Thm 3.1** — the lift `C` has proximity gaps ⟹ `C^m` does. Its proof is a
   counting argument over two sets `R*`, `R**` (DG Lemmas 3.2/3.3/3.4: `d^m(U_r,V_r) ≤ e`,
   `|R**| ≤ |R*|·(n−|D|)+|D|`, `|R**| ≥ (n−e)·|R*|`) plus the unique-decoding step we already have as
   `codeword_eq_of_close_of_close`;
4. prove **AER Thm 3.6** (affine-line gaps for all `C^m` ⟹ tensor-style gaps) — an induction on the
   list-size parameter ϑ;
5. **Corollary 3.7** then follows by composition, given the BCIKS base case.

### ⚑ And the base case is not a premise — we prove it [READ]

I expected the BCIKS base case to be threaded as an unproved hypothesis, the way `HaboeckTheorem2`
is in `Selvage/JohnsonMcaBridge.lean` (L270: `def HaboeckTheorem2 … : Prop`, consumed as `hHab` at
L283/301/333). It is **not**. `Selvage/ProximityGapUD.lean` L477:

```lean
/-- **The hPG DISCHARGE — the standing proximity-gap hypothesis PROVED at the
one-third-UD radius.** … realized here, hypothesis-free, on that interval. -/
theorem reedSolomonCode_isProximityGenerator_UD [Nonempty ι] [Fintype F]
    (dom : ι ↪ F) (d : ℕ) :
    IsProximityGenerator (affineGenerator F) (reedSolomonCode dom d)
      ((2 + (d : ℝ) / (Fintype.card ι : ℝ)) / 3)
      (fun _ => (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))
```

resting on the dichotomy theorem at L409, which is the Ben-Sasson-et-al. Thm 4.1 *shape*:

```lean
theorem rs_proximityGap_UD [Nonempty ι] [Fintype F] (dom : ι ↪ F) {d : ℕ}
    {δ : ℝ} (hδ0 : 0 < δ) (hδ3 : (d : ℝ) < (1 - 3 * δ) * (Fintype.card ι : ℝ))
    (f : Fin 2 → ι → F) :
    (affineGenerator F).pr (fun r => close δ (reedSolomonCode dom d) (comb r f))
      ≤ (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)
    ∨ CorrelatedAgreement (reedSolomonCode dom d) δ f
```

**Binders: `[Nonempty ι] [Fintype F]` and an embedding `dom : ι ↪ F`. No characteristic. No prime.
No smooth subgroup. No root of unity.** It holds over GF(2^k) as written — the evaluation domain is
an arbitrary injection `ι ↪ F`, i.e. an abstract point set, not a multiplicative subgroup.

Proof hygiene [MEASURED]: **zero real `sorry`s** in `ProximityGapUD.lean`,
`ProximityGapUDTight.lean`, `ProximityGapUDSharp.lean`, `CorrelatedAgreement.lean` — the `grep`
hits are docstrings *asserting* their absence (L39 "The proof (all of it, no sorry)", L862
"`propext`, `Classical.choice`, `Quot.sound` — no `sorryAx` anywhere in the file"). **Zero `axiom`
declarations** anywhere in `Selvage/` or `Theory/`.

⚠ **The price, stated honestly.** Our radius is `δ ∈ (0, (1−ρ)/3)` — **one-third** unique decoding.
BCIKS Thm 4.1, which Ligerito and Diamond–Gruen both invoke, holds to `e ≤ ⌊(d−1)/2⌋` — **one-half**.
So composing DG Thm 3.1 on *our* base case yields a real theorem with a **concretely worse radius**
than the paper chain, hence more queries `|S|` for the same error. That is a quantitative gap, not a
structural one: the statement is the same shape, the constant is weaker.

The bounded-exposure fallback still stands regardless: Ligerito supplies a **general-linear-code**
error bound `(1 − d/(3m))^|S| + dk/(3|F|)` that needs no RS base case at all — and note that its own
constant is *also* a one-third, which suggests the one-third radius is the natural home for a
field-generic argument.

---

## 5. The Spartan spine: sum-check and the zerocheck [READ]

`/Users/ember/dev/minidregg/Selvage/Sumcheck.lean` L61:
`variable {F : Type} [Field F] [Fintype F] [DecidableEq F]` — **field-generic, no characteristic.**

The soundness theorem is **degree-generic**, not pinned to a rung:

```lean
theorem sumcheck_soundness {v d : ℕ} {prover honest : ℕ → Polynomial F} {H S : F}
    (hProverDeg : ∀ i, i < v → (prover i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hHonestDeg : ∀ i, i < v → (honest i).degree < ((d + 1 : ℕ) : WithBot ℕ))
```

built on field-wide Schwartz–Zippel (`card_agreeFinset_lt`, L77) and a per-round union bound
(`unionBound_fixed`, L306). Spartan's degree-3 zerocheck is `d := 3` in this engine.

Three concrete rungs are built, all `variable {F : Type} [Field F] [Fintype F] [DecidableEq F]`:

| rung | file | form |
|---|---|---|
| degree 1 | `Selvage/MultilinearExtension.lean` | a single MLE's hypercube sum |
| **degree 2** | `Assurance/AirSumcheckQuadratic.lean` L110 | **`Â·B̂ − Ĉ`** — the R1CS/Spartan form, terminal check factored |
| degree 3 | `Assurance/AirSumcheckCubic.lean` L88 | `cubicForm E A B C D x = Ê(x)·(Â(x)·B̂(x) + Ĉ(x)·D̂(x))` — the `eq`-headed cubic |

`cubicForm` with the `eq` head *is* Spartan's zerocheck shape, and it is discharged into two named
consumer theorems (`cubicForm_fraction_layer` for a GKR fraction-tree layer via
`Selvage/EqPolynomial.lean`'s `eqMle_eq_mle`, and `cubicForm_hadamard` for `Â·B̂ − Ĉ`).

### The gap the repo already names, in its own words

`Assurance/AirSumcheckQuadratic.lean` L94–100 is explicit about what is missing, and it is exactly
the Spartan-shaped hole:

> "the missing lemma is exactly this table-evaluation-to-wire-word linearization (**Spartan's second
> phase**). … the multilinear zero-test `Pr_{z ← F^m}[mle D z = 0] ≤ m/|F|` for `D ≠ 0` —
> **multivariate Schwartz–Zippel for multi-affine functions, not yet vocabulary**."

So: **the sum-check engine and the zerocheck algebra are present and field-generic; Spartan's second
phase (the sparse-MLE / table-to-wire linearization, i.e. the SPARK offline-memory-checking step)
is absent and is correctly labelled absent.** Multivariate Schwartz–Zippel over the boolean
hypercube is named as missing vocabulary.

⚠ One caveat on `|F|`: every sum-check error term here is `d/|F|` or `m/|F|`. Over a *small* binary
field (GF(2), GF(2^8)) those are vacuous — which is precisely why BinarySpartan needs
**ring-switching** to run the sum-check in a large extension `L` while committing over the ground
field `K`. The bound is field-generic; the *usefulness* of the bound is not. That is a parameter
fact, not a proof obstruction, and it is the reason ring-switching is load-bearing rather than an
optimization.

---

*(sections 6–8: keystone classification table, have/partial/absent table, binary-cone contents,
external formalization landscape, and the position statement — pending lane returns)*
