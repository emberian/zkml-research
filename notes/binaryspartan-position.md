# BinarySpartan — analysis and position

Date: 2026-08-14. Status: **complete.** Read §0.5 first — it changes how to read everything else.
The deliverable is §6 (keystone transfer classification); the position is §12.

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

## 0.5 ⚠⚠ FIRST: I could not verify that BinarySpartan exists

**Read this before acting on anything below.** The brief presents BinarySpartan as a fact. Three
independent instruments failed to find it, and one found the phrase being used *against* the idea.

**Instrument 1 — a prior note in this very repo, written TODAY.**
`/Users/ember/dev/zkml-research/notes/neo-superneo-read.md` §2 (dated 2026-08-14) already ran this
question and recorded: IACR full-text search for "BinarySpartan" → **∅**; Setty's 2026 eprints =
**{2026/242} only**; a grep of all **810 papers numbered ≥ 242** in
`/Users/ember/dev/gh/forks/IACR-eprint-mirror/2026/` for "BinarySpartan"/"Binary Spartan" → **∅**.

**Instrument 2 — my own sweep.** `/Users/ember/paperbin` (1626 papers, full-text `.txt` extracts):
no BinarySpartan file, no BinarySpartan hit.

**Instrument 3 — and this is the interesting one.** The phrase's *only* home in either corpus is
`/Users/ember/paperbin/binius64-blueprint-spec.txt:163`, in a section titled verbatim
**"§1.2 Why Not Binary Spartan?"** — **Irreducible arguing against the construction.** Their
objection: over `n` witness bits, `A, B, C` have `O(n)` nonzeros and partial evaluation costs
`O(λn)` bit ops — "a second factor of λ" for the sparse-matrix openings — *"the large field infects
what ought to be a bit-level computation."*

### How to hold this

- **The tweet/slide claims remain [CLAIM], not [READ].** No abstract was recovered. The 410k/219k/163k
  h/s figures, the 6.2 ms SHA-256, and the Flock/Vega/Binius64 comparison set are **unverified**.
  ⚠ Note the tell: the brief itself says the paper is *in the review queue*, which explains an eprint
  absence — but it does not explain the *positive* evidence in instrument 3.
- **The described system is nevertheless a real near-neighbour of things in print**, so the ingredient
  list is coherent even if the paper is not confirmed: Binius64 already ships **IronSpartan** (§6 —
  commit-and-prove Spartan over binary fields, used as its ZK outer argument), plus §4.8
  ring-switching and §5.2 BaseFold. And `/Users/ember/paperbin/sumcheck-speedup-2026-587.txt:96`
  states that Binius64 *"applies SuperSpartan … over binary fields using (FRI-)Binius as the PCS."*
- **Irreducible's objection is exactly what ring-switching is supposed to answer**, which is why a
  system pairing Spartan-over-binary with ring-switching is a sensible thing for someone to build.

**Bottom line: everything below about *our* transfer story stands on its own merits and does not
depend on BinarySpartan being real.** The binary-field question is live regardless — Binius64 and
IronSpartan are shipped artifacts. But do not repeat the benchmark numbers as fact, and do not tell
anyone we verified the paper. We did not.

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

⚠⚠ **Do not quote those two expressions as the true bounds — the paper misprints them, both times in
the flattering direction.** A prior survey in this repo,
`/Users/ember/dev/zkml-research/notes/multilinear-pcs-landscape.md` §9.5/§11.2/§12, recorded **two
transcription defects, both favourable**:

- eqs (4)/(15)/(17) print `(m − n − 1)/(2m)` where the correct factor is **`(m + n − 1)/(2m)`**;
- eq (18) prints `(dᵢ/3mᵢ)^{|Sᵢ|}` where the correct factor is **`(1 − dᵢ/3mᵢ)^{|Sᵢ|}`**.

(Note the §3 form I quoted above, `(1 − d/(3m))^|S|`, is the *correct* shape — it is eq (18) later in
the paper that drops the `1 −`. So the paper is internally inconsistent, not uniformly wrong.)

**Consequence, and it is a real one: formalizing Ligerito verbatim would prove a bound the protocol
does not have.** This is exactly the class of thing a machine-checked treatment exists to catch —
and it is an argument *for* the work, not against it. But it means Ligerito is an unrefereed note
whose printed error analysis is already known-defective, which is a materially different object from
a refereed theorem.

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

⚠ **CORRECTION to my own first draft of this section.** I initially wrote "the gap is a definition,
not a wall." That is too optimistic and a lane refuted it. Split the claim in two:

- **Steps 1–2 below really are definitional.** Diamond–Gruen's `d^m(U,V) = |{j : column j of U ≠
  column j of V}|` is already what `relDist` computes if the word's value type is `Fin m → F`
  instead of `F` — Mathlib's `hammingDist` is generic in the codomain. And `C^m` is
  `{U : ι → (Fin m → F) | ∀ i, (U · i) ∈ C}`, a `Submodule`.
- **Steps 3–4 are genuinely new mathematics.** Our UD proof (`correlatedAgreement_of_close_card`) is
  a *root-counting* argument. Diamond–Gruen's interleaved lift is a *rank / row-space* argument over
  the sets `R*`, `R**`. Different proof, not a generalization of ours. Do not price it as a port.

One thing that *does* line up better than the lane's summary suggests: **DG Thm 3.1 takes affine-line
proximity gaps as input and produces affine-line proximity gaps for `C^m` as output** — i.e. it is an
ℓ = 2 → ℓ = 2 statement. Our only proved realizer, `affineGenerator F : ProximityGenerator F 2`
(coefficients `![1, r]`, "literally WHIR's `Gen(ℓ; α)` at `ℓ = 2`"), is **exactly the input shape DG
Thm 3.1 wants.** The jump to tensor-structured coefficients happens one level up, in AER Thm 3.6.
So the ℓ = 2 restriction is not the obstacle here; the interleaved object and the DG proof are.

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

## 6. ⚑ THE DELIVERABLE — keystone-by-keystone transfer classification

### 6.0 The census that decides most of it [MEASURED]

Across `Selvage/`, `Theory/`, `Assurance/`, `Compiler/`:

| symbol | occurrences |
|---|---|
| `IsPrimitiveRoot` | **0** |
| `rootsOfUnity` | **0** |
| `primitiveRoot` | **0** |
| `orderOf` / `Subgroup` | 1 file, `Theory/CyclotomicInertia.lean`, **orphaned** (nothing imports it) |

**There is no multiplicative evaluation domain in this repository.** Every Reed–Solomon code is over
an abstract injective embedding of an abstract index type — `Selvage/ReedSolomon.lean` L87:

```lean
noncomputable def reedSolomonCode (dom : ι ↪ F) (d : ℕ) : Submodule F (ι → F) :=
  (Polynomial.degreeLT F d).map (evalOnDomain dom)
```

`ι` an arbitrary `Fintype`, `dom` an arbitrary `Function.Embedding`, minimum distance by pure root
counting. Nothing is a subgroup, an `ω`-orbit, or a coset. And
`AdditiveProximity.additiveImageDomain [CharP F 2] (R : Finset F) (beta : F)` — the additive/affine
LCH image — **plugs into exactly that slot, and the repo already proves it does** (`finsetDomain`,
`closeToDeg_iff_close`).

This is the single most important measurement in the note. The usual reason a proof system is
prime-pinned — a smooth multiplicative subgroup of order 2^k, which cannot exist in GF(2^k) — **does
not apply to us, because we never assumed one.**

### 6.1 The classification table

| # | Keystone | Files (under `/Users/ember/dev/minidregg/`) | Verdict |
|---|---|---|---|
| 1 | RBR → Fiat–Shamir over an inhabited oracle | `Selvage/Rbr.lean`, `FiatShamir.lean`, `Depth.lean` | **FIELD-FREE** |
| 1b | Sumcheck / BaseFold RBR instances | `Selvage/SumcheckRbr.lean`, `BaseFoldRbr.lean` | **FIELD-GENERIC** |
| 2a | BCS at the abstract alphabet | `Selvage/AccRbrBcs{,Raw,Shifted}.lean` | **FIELD-GENERIC** |
| 2b | BCS at the **deployed** alphabet | `Selvage/BaseFoldBcsQuerySampling.lean`, `BaseFoldBcsByteCodec.lean` | ⚠ **STRUCTURALLY-PRIME-ONLY** |
| 3 | State restoration | `Selvage/Rbr.lean`, `Depth.lean` | **FIELD-FREE** |
| 4 | Accumulation-depth composition | `Selvage/Depth.lean`, `AccExtractChain.lean`, `Accumulator.lean`, `AccSound*.lean` | **FIELD-GENERIC** |
| 5 | Sponge indifferentiability (~22 files) | `Selvage/SpongeIndiff*.lean` | **FIELD-FREE** (`[AddCommGroup Rate]`) |
| 6 | Two-regime calculator (core) | `Selvage/JohnsonRegime.lean`, `HalfThresholdRegime.lean`, `JohnsonMcaBridge.lean` | **FIELD-GENERIC** |
| 6b | …its selector wrapper | `Selvage/RateRegimeSelector.lean` | **STRUCTURALLY-CHAR≠2** (keyed on `FoldingTower`) |
| 7 | BaseFold completeness | `Selvage/BaseFoldCompleteness.lean`, `BaseFoldIor.lean` | **STRUCTURALLY-CHAR≠2** |
| 7b | BaseFold RBR soundness instance | `Selvage/BaseFoldRbr.lean` | **FIELD-GENERIC** |
| 8 | Degree-3 sumcheck rung | `Assurance/AirSumcheckCubic.lean` | **FIELD-GENERIC** — *explicitly char-2-designed* |
| 9 | Multilinear Schwartz–Zippel | `Selvage/MultilinearZeroTest.lean`, `EqPolynomial.lean` | **FIELD-GENERIC** |
| 10 | Matmul contraction face | `Assurance/ZkmlMatmulSumcheck.lean`, `Selvage/Rank1GradientCheck.lean` | **FIELD-GENERIC** |
| 11a | RS / correlated agreement / proximity gaps | `Selvage/ReedSolomon.lean`, `CorrelatedAgreement.lean`, `ProximityGapUD*.lean` | **FIELD-GENERIC** |
| 11b | Multiplicative FRI fold | `Selvage/Proximity.lean`, `HalfThresholdFri*.lean` | ⚠ **STRUCTURALLY-CHAR≠2** |
| 12a | `Selvage/SmallField.lean` | | **FIELD-GENERIC** core; prime *numerals* only |
| 12b | `Selvage/ExtensionChallengeBridge.lean` | | **FIELD-GENERIC** — brief's suspicion was wrong |
| 12c | `Selvage/BabyBearExt4.lean` | | **STRUCTURALLY-PRIME-ONLY** by construction |

**Score: 13 of 18 transfer with no new mathematics.** Three need re-keying onto the additive tower
that already exists; one needs deleting-and-simplifying; one is a deployed artifact, not a keystone.

### 6.2 The one genuine wall, named exactly

`Selvage/Proximity.lean` L178:

```lean
structure FoldingData (F : Type*) [Field F] {ι κ : Type*}
    (dom : ι ↪ F) (domSq : κ ↪ F) where
  neg : ι → ι
  dom_neg : ∀ i, dom (neg i) = - dom i
  sq : ι → κ
  domSq_sq : ∀ i, domSq (sq i) = dom i ^ 2
  sec : κ → ι
  sq_sec : ∀ k, sq (sec k) = k
  dom_ne_zero : ∀ i, dom i ≠ 0
  two_ne : (2 : F) ≠ 0          -- ⚠ char ≠ 2 as a STRUCTURE FIELD
```

**`FoldingData` is uninhabitable under `[CharP F 2]`, two independent ways:**
1. `two_ne : (2 : F) ≠ 0` is directly false.
2. `card_eq_two_mul_card` (L908): `Fintype.card ι = 2 * Fintype.card κ`. In char 2, `x ↦ x²` is the
   Frobenius **automorphism** — injective — so fibres are singletons and `|ι| = |κ|`. The 2-to-1
   structure the entire multiplicative fold rests on does not exist.

The F-valued char-2 hazards (distinct from the ℝ-valued `/ 2` I cleared in §2):
- `Proximity.lean:237` `foldEven … := (f (D.sec k) + f (D.neg (D.sec k))) / 2`
- `Proximity.lean:241` `foldOdd … := (f (D.sec k) - f (D.neg (D.sec k))) / (2 * dom (D.sec k))`
- `HalfThresholdFriTranscript.lean:77-78` the verifier's opened-fibre check, same shape
- `Proximity.lean:200` `neg_ne`'s `(2 : F) * dom i = 0` argument

### ⚠⚠ The vacuity hazard this creates — flag it before anyone "ports" anything

**Because `FoldingData` is uninhabitable in char 2, every theorem quantified over `(D : FoldingData …)`
becomes VACUOUSLY TRUE, with zero content, the instant you instantiate `F := GF(2^k)`.** That covers
`proximity_sound` (L689), `proximity_sound_prob` (L706), `proximity_complete` (L445),
`close_of_correlatedAgreement` (L1059), `fold_notMem_of_notMem` (L816), and everything in the 11
downstream files.

This is exactly this repo's own documented failure class — an apex theorem true because its premise
is empty. Anyone who "instantiates the multiplicative cone at a binary field" will get a **green
build and a meaningless theorem**, and no axiom check or `#assert_axioms` will notice, because a
vacuous theorem is honestly proved. The correct move is the one the repo already made: **do not
instantiate `FoldingData` at char 2 — use the additive tower instead.**

`Selvage/AdditiveFriTower.lean` L28 says so in its own header:

> "The multiplicative `FoldingTower` in `Selvage.Proximity` cannot be instantiated in characteristic
> two: its fibres are `{x,−x}` and its structure contains the field axiom `2 != 0`. This file
> therefore records the additive tower directly. … No multiplicative squaring/negation structure is
> used or assumed."

### 6.3 Two keystones worth calling out as unusually good news

**Sponge indifferentiability is field-FREE and *additively* typed.** `Selvage/SpongeIndiff.lean`
L192: `variable {Rate Cap : Type} [AddCommGroup Rate]`. `grep -c Field` returns **0 in 21 of 22
files**. Over GF(2^k) lanes `[AddCommGroup Rate]` is literally **XOR** — which is what a real binary
sponge (Keccak) does. This ~22-file cone is the best-transferring asset we hold, and it transfers
*toward* the hash-based direction the EF is moving in.

**The degree-3 rung was already built for char 2 on purpose.** `Assurance/AirSumcheckCubic.lean`
header:

> "This form needs **no division and no characteristic hypothesis** — it works over any commutative
> ring, which matters because the char-2 (binary-tower) instantiation **cannot use `{0,1,2,3}`
> interpolation nodes at all**."

`cubicForm_line` (L161) is coefficient-form, closed by one `ring`; `cubic_sumcheck_soundness` (L366)
gives `≤ m·3/|F|`. Someone on this project already thought about binary towers at the sumcheck layer.

### 6.4 The deployed sampler — the one place "port" is the wrong verb

`Selvage/BaseFoldBcsQuerySampling.lean` L47:

```lean
theorem babyBear_nonzero_factorization {ell : Nat} (hell : ell ≤ 28) :
    modulus - 1 = querySlackSize ell * queryIndexSize ell
```
with `acceptedScalarEquiv : {x : F // x ≠ 0} ≃ Fin (querySlackSize ell) × PowerTwoFriLevels ell 1`.

This needs `2^(ell−1) ∣ |F| − 1`. In GF(2^k), `|F| − 1 = 2^k − 1` is **odd**, so this is
unconstructible for any `ell > 1`. ⚑ **But note where the smooth-order dependency actually sits: in
the CHALLENGE SAMPLER, not the evaluation domain** — and it becomes *unnecessary*, because
`|GF(2^k)| = 2^k` is already a power of two, so an unbiased query coordinate is "take the low
`ell−1` bits" with **no rejection event at all**. Same for `BaseFoldBcsByteCodec.lean`: over
GF(2^128) every 16-byte string is a valid element, so the `value.val < modulus` canonicity
obligation becomes `True`. **Both modules get strictly simpler, not harder.**

### 6.5 Proof hygiene behind every verdict above [MEASURED]

Across `Selvage/`, `Assurance/`, `Theory/`, `Compiler/`, `Kernel/`, `Effects/`, `Pred/`:
- **`axiom` declarations: 0**
- **bare `sorry` terms: 0** (all grep hits are docstrings asserting their absence)
- `native_decide`: 2 files only (`SmallField.lean` ×1, `ZkmlSuiteRegistry.lean` ×5)

Two honest exceptions, both **`Prop`-valued named hypotheses that are never asserted**:
`IsProximityGenerator` (WHIR Thm 4.8 / BCIKS) and `WHIRConjecture412` + `HaboeckTheorem2`. Both are
field-generic `Prop`s over an abstract `ι ↪ F` carrying **no characteristic assumption** — so a
binary instantiation inherits exactly the same open premise, **no worse**. (And per §4, the
one-third-UD case is discharged outright by `reedSolomonCode_isProximityGenerator_UD`.)

---

## 7. What the binary cone actually proves [READ, lane-verified]

### 7.1 Three corrections to the brief

1. **"~9,750 lines / ~311 theorems and UNWIRED to anything" is false.** Every file is in the build
   graph (`Minidregg.lean` → `Theory`/`Selvage`/`Compiler`/`Assurance`), and the additive-FRI
   soundness theorem is consumed by 4 `Compiler/` and 3 `Assurance/` modules. A concrete tower is
   constructed at `Compiler/Tower256AdditiveFriRawDeployment.lean:93`.
2. **`AdditiveFriTower.lean` is not the proximity result** — it is domain geometry (quotient maps,
   transversals, pair domains, injectivity). The soundness bound lives in
   **`Selvage/AdditiveFriQuery.lean` (836 lines)**, not the 432-line file the brief pointed at.
3. **`HalfThresholdFriTower.lean` is not in the binary cone at all** — `grep -c CharP` = **0**. It is
   over the *multiplicative* `FoldingTower`. The brief listed it as a binary-tower proximity result;
   it is not one. Its results are real but belong to the multiplicative stack.

### 7.2 The actual theorem

`Selvage/AdditiveFriQuery.lean` — a real, proved, multi-round, adaptive additive-FRI soundness bound:

```lean
theorem additiveFriAdaptive_coherent_sampled_sound_UD
    (deg : ℕ → ℕ) (st : FriAdaptiveTranscript S) (radius : ℕ → ℝ) (qCount : ℕ) {tau : ℝ}
    (htau : tau ≤ 1) (hfinal : 0 ≤ radius m)
    (hshrink : ∀ j : Fin m, radius (j+1) + tau ≤ radius j)
    (hdeg : ∀ j : Fin m, deg j = 2 * deg (j+1)) …
    (hband : ∀ j : Fin m, radius j < 1 - (2 + (deg (j+1):ℝ)/((T.transversal j j.isLt).card:ℝ))/3)
    (hfar0 : ¬ close (radius 0) (reedSolomonCode (T.dom 0) (deg 0)) (st.word 0 …)) :
    uniformProb … (fun x => AdditiveFriAdaptiveCoherentAccepts T S deg st qCount x.1 x.2) ≤
      (m:ℝ) * (2^(ell-1) : ℕ) / (Fintype.card F : ℝ) + (1 - tau)^qCount
```

**Bound: `m·2^(ℓ−1)/|F| + (1−τ)^q`.** `#print axioms` pins `[propext, Classical.choice, Quot.sound]`.

**It proves, it does not assume.** `AdditiveProximityGap` *is* a `def … : Prop` threaded as `(hPG : …)`
— the `HaboeckTheorem2` pattern the brief worried about — **but it is discharged**, by
`Selvage/AdditiveProximity.lean`'s `additiveProximityGap_UD`, which takes **no proximity-gap
argument** and bottoms out in `reedSolomonCode_isProximityGenerator_UD` → `rs_proximityGap_UD` →
`correlatedAgreement_of_close_card`. The additive chain **does not import** `JohnsonMcaBridge` or
`ProximityGapUDTight`, so neither `HaboeckTheorem2` nor `PolishchukSpielman` is in its dependency
path. Band: `δ < (1−ρ)/3`, error `|R|/|F|`.

Cone census: **`sorry` = 0, `axiom` = 0, `native_decide` = 0.** All 38 `#guard` hits are
`#guard_msgs … in #print axioms X` — build-time axiom accounting, **not** the `#guard e`
unit-test-in-Lean-clothes pattern. Zero bare `#guard`.

It fires concretely at one round: `keystone_additiveFold_distance_fires` exhibits a word over
**GF(16) = `binaryTower 2`** at `δ = 1/8`, `d = 1`, whose fold stays 1/8-far outside ≤ 2 challenges —
positive distance, not the trivial exact regime.

Four explicit premises, none hidden: an **ideal** `BindingCommitment` (carrying `binding :
PositionBinding` as a structure field); **no Fiat–Shamir** (interactive, stated in the docstring);
the `(1−ρ)/3` band; and a radius schedule `radius(j+1) + τ ≤ radius(j)`.

### 7.3 ⚠⚠ A vacuity finding that outranks the rest of this note

`Assurance/Tower256MerkleBindingCardinality.lean`:

```lean
theorem merklePcs_empty_of_positive {ell : Nat} (positive : 0 < ell) : ¬Nonempty (MerklePcs ell)
theorem jointGameFamily_impossible (joint : BoundJoint) : False
```

Pigeonhole: `2^256` roots cannot injectively receive `(2^256)^(2^ell)` words, so a **universally
position-binding cSHAKE Merkle PCS over Tower256 does not exist at any positive FRI height.**
`Assurance/Tower256AdditiveFriControllerAdmission.lean:41` and
`Assurance/Tower256AdditiveFriActualReduction.lean:46` both declare `variable {pcs : MerklePcs ell}`
— **every theorem in those two files is vacuous at positive height.**

The repo *does* know (`scripts/CarrierCensus.lean:145-160` flags all four carriers as
`auditedNonTargets`, and the live replacement is the inhabited collision-retaining `RawMerklePcs`).
But `docs/SELVAGE-COMPLETE.md:155-159` still claims `SemanticHistoryTower256CheckpointGame` "closes
the former structural two-ledgers residual" — **`jointGameFamily_impossible` refutes that**, and
conversely `:106-107` lists the raw non-binding PCS as *open* when it has landed. **Two doc defects
worth fixing regardless of what happens with BinarySpartan.**

Also still dangling on the live path: `FarWordSoundnessCertificate` is **never constructed** — only
ever threaded as a hypothesis — and it *cannot* be constructed at the deployed carrier, because
`Tower256AdditiveFriRawDeployment.zeroTranscript` has every word `= 0` and the zero word **is** in
the RS code, so `initialFar` is false there by construction. The deployed instance is
`ell = 1, m = 1, degree = 1` — a statement-inhabitation carrier, not a firing of the bound.

Stale docstrings that would mislead an auditor: `AdditiveNTTTransform.lean:419` still labels
`AdditiveProximityGap` **"(RESIDUAL HYPOTHESIS)"** and `:508` calls `additiveFold_distance`
"REDUCED … modulo the named proximity-gap floor" — both superseded by `additiveProximityGap_UD`.
`AdditiveFriTower.lean:402-411` claims no honest type exists to instantiate, which
`AdditiveFriQuery.lean` refuted. **A reader auditing by docstring would conclude this cone assumes a
gap. It does not.**

### 7.4 Could Ligerito-family soundness compose from this? — **No.**

**What we have is FRI-shaped. Ligerito needs the Ligero-shaped theorem.** Decisive measurement: the
only **proved** `IsProximityGenerator` realizers in the entire repo are all at **ℓ = 2**
(`affineGenerator F`, coefficients `![1, r]`) plus one trivial `⊤`-submodule case. There is no proved
proximity generator at ℓ > 2.

| Ligerito requirement | present? |
|---|---|
| Interleaved code object `C^m` / matrix-of-rows | **Absent** — codes are `Submodule F (ι → F)`, single words |
| **Interleaved distance** (fraction of bad *columns*) | **Absent** — `relDist`/`close` cannot express it; a different metric |
| Proximity gap at ℓ = m rows (interleaved-RS CA) | **Absent** — and the UD root-counting proof does not generalize to it |
| Tensor-structured coefficients `⊗ᵢ(1−rᵢ, rᵢ)` | **Absent** — `ProximityGenerator.weight` admits the *shape*, nothing proved |
| **Column openings** (all m rows at one position) | **Absent** — `OpeningScheme.openAt` opens one position of one word |
| Recursion via sumcheck/tensor glue | **Absent from this cone** — grep for `mle`/`sumcheck` across the four additive files returns **nothing**; the additive stack is a pure LDT/proximity stack |

What *would* carry over, and it is not nothing: the vocabulary is **already ℓ-general**
(`CorrelatedAgreement (C) (δ) (f : Fin ℓ → ι → F)`, `IsProximityGenerator`,
`HasMutualCorrelatedAgreement` are all stated at arbitrary ℓ), so instantiating at ℓ = m is *proving
a new realizer*, not restating the theory. Plus the entire binary-field substrate (`binaryTower`,
discharged Fan–Paar fast multiplication, the `Tower256` 32-byte codec, the additive NTT / novel-basis
bijection, subspace-vanishing linearity), a code-agnostic `BinaryMerkle` whose
`positionBinding_of_collisionFree` gives **column** binding directly if you commit column-wise, and
the query-miss probability toolkit.

### ⚑ 7.5 The strategic alternative the lane surfaced

**If the goal is *a machine-checked multilinear PCS over binary towers* rather than *Ligerito
specifically*, there is a materially shorter path.** The repo already has a FRI-family multilinear
PCS — the `Selvage/BaseFold*` cone, 17 files, with sumcheck, BCS Fiat–Shamir, and Poseidon2/ROM
ledgers — but built over the **multiplicative** `FoldingTower`. **Porting BaseFold onto the proved
additive tower composes two things that both already exist and both already sit at ℓ = 2.**

And this is not a detour from BinarySpartan: **ring-switching's own target is "a characteristic-2
adaptation of BaseFold, developed at length"** (§3). So BaseFold-on-the-additive-tower is
simultaneously the cheapest binary PCS we can reach *and* the exact object Diamond–Posen's compiler
consumes. That is the strongest single lead in this note.

---

## 8. ⚠ The Poseidon claim, corrected at source [READ]

**The brief says: "the Ethereum Foundation is publicly abandoning Poseidon for L1." The corpus does
not support that sentence as written.** What it supports is narrower and more interesting.

Instrument: `/Users/ember/paperbin`, files `grey-poseidon-initiative-state-of-art-2026.txt` (fetched
2026-08-13, from poseidon-initiative.info + Khovratovich's SPRING2026 Rome slides, 10 May 2026),
`grey-ethresearch-poseidon-not-secure.txt`, `poseidon2-round-skipping-skipping-class-2026-306.pdf`,
`poseidon-bounty2026-khovratovich.pdf`, `poseidon-fiat-shamir-cryptanalysis.pdf`.

**What actually happened — a pivot *within* the Poseidon family, not an abandonment:**

> Khovratovich slide 6, titled verbatim: **"Why We Moved from Poseidon2: Round Skipping Attack"**
> … Response, stated on the slide: **"Poseidon Initiative pivots to Poseidon1 (KoalaBear, MDS
> matrix) for Bounty 2026."**

The attack is real: *"Skipping Class: Algebraic Attacks exploiting weak matrices and operation modes
of Poseidon2(b)"*, Merz & Rodriguez Garcia (ETH Zurich), **eprint 2026/306**, Feb 2026. It exploits
Poseidon2's **non-MDS internal matrix** (chosen for circuit efficiency, linear branch number
`b < t+1`); spending 4 degrees of freedom per round skips ≈ `t/4` full rounds; it yields an algebraic
preimage attack easier than the corresponding CICO problem and the first algebraic collision attack
outperforming its preimage counterpart.

**Khovratovich's own characterisation is the calibrated one:** *"Does not break recommended
parameters outright, but substantially erodes the security margin."*

And there is a real theorem behind the retreat to MDS (Khovratovich 2026, slide 7, informal): a trail
skipping `m` rounds of an SPN with `t` state elements and branch number `b` needs `b ≤ 4t/m` (m even)
/ `b ≤ (4t−2)/(m−1)` (m odd). MDS gives `b = t+1`, so **no 4-round skipping trail exists for any
MDS-based SPN**. `m = 3` is open (ETH Zurich short-term grant topic, 2026).

**The other cited artefact is a forum argument, not a position.**
`https://ethresear.ch/t/poseidon-hash-for-ethereum-is-not-secure/25637` (created 2026-08-06) is a
community thread in which users actively dispute each other about capacity elements and round counts.
It is not an EF statement and must not be relayed as one.

### The honest version of the claim

- ✅ **Supported:** the Poseidon Initiative moved off **Poseidon2** to **Poseidon1 (KoalaBear, MDS)**
  for Bounty 2026, driven by a published attack that eroded the margin without breaking parameters.
- ✅ **Supported:** there is live, unsettled community debate about Poseidon's security for Ethereum.
- ❌ **Not supported by this corpus:** "the EF is abandoning Poseidon for L1." That is a stronger and
  differently-shaped claim. (Drake's *"hash-friendly SNARKs"* advocacy is a separate matter — web
  instrument, under lane adjudication; note that advocacy by an EF researcher is not an EF position.)

⚠ **Why this matters for our position and not just for accuracy:** if the argument for pivoting to
binary fields is "Poseidon is dead," that argument is **overstated and will not survive contact with
Khovratovich**. The durable argument is the *structural* one — hash-based SNARKs over binary fields
remove the algebraic-hash cryptanalysis surface **entirely**, so they are not exposed to the next
round-skipping result at all. Argue the structure, not the obituary.

⚠ **And one nuance that keeps the structural argument honest.** "Binary fields remove the
algebraic-hash surface" is true only if you then use a **traditional** hash (BLAKE3 / SHA-256 /
Keccak), which is exactly the BinarySpartan pitch. Binary-tower land also has its *own*
arithmetization-oriented hash — `vision-mark-32-binary-tower-hash-2024-633.pdf`, **Vision Mark-32**
(Ashur, Mahzoun, **Posen**, Šijačić; Irreducible), a Vision instance over binary tower fields with an
optimized round count and an efficient MDS matrix. Vision Mark-32 is an algebraic hash and therefore
**carries the same class of cryptanalytic exposure Poseidon2 just took a hit from.** So the escape is
"traditional hashes proved natively", not "binary fields" per se. Say it that way.

---

## 9. What BinarySpartan is made of vs. what we hold — have / partial / absent

Corpus 3 = `/Users/ember/dev/minidregg`: **400 Lean files, 179,470 lines, 0 `sorry`.**

| Ingredient | Verdict | Path | What is there / what is missing |
|---|---|---|---|
| **Sum-check protocol** | **HAVE** | `Selvage/Sumcheck.lean`, `SumcheckReduction.lean`, `SumcheckRbr.lean` | `sumcheck_soundness` + `adaptive_sumcheck_soundness` bound false-claim acceptance by `v·d/\|F\|`, **parametric in `d`**. Prefix-measurable (adaptive) prover, discharged union bound. Nothing missing at the protocol layer. |
| **Degree-3 rung** | **HAVE** | `Assurance/AirSumcheckCubic.lean` (629 ln) | Realizers at d=1/2/3; `cubicForm_subsumes_prodDiff` makes d=2 a special case, not a twin. Landed 2026-08-13. **Spartan's outer sumcheck is exactly this shape.** |
| **MLE + `eq` polynomial** | **HAVE** | `Selvage/MultilinearExtension.lean` (750), `EqPolynomial.lean` (155) | `mle_injective`, `multiAffine_eq_mle` (uniqueness), round-chain skeleton for arbitrary `g`; `eqMle_fold : Σ_b eq(z,b)·f(b) = f̂(z)` — the zerocheck→sumcheck bridge. |
| **Binary tower field substrate** | **HAVE** | `Theory/BinaryTower.lean`, `BinaryTowerFanPaar.lean`, `BinaryTowerTrace.lean` | `binaryTower k = GaloisField 2 (2^k)` (real mathlib construction). Fan–Paar generators **built, not assumed**; `towerMul_eq_mul` unconditional for all `k`. ⚠ Rust `prover/src/binary_tower_256.rs` is an **unverified seam**, and the repo says so: `[BTOWER256-RUST-UNVERIFIED]`. |
| **The PCS we do have** | **HAVE** | `Selvage/BaseFold*.lean` (~15 files), `Commitment.lean`, `MultilinearCommitment.lean` | BaseFold at RS in the unconditional `(1−ρ)/3` band; Merkle/BCS `OpeningScheme` + `PositionBinding`; full IOR verifier + soundness + Poseidon2/FS alphabet. ⭐ **plus a characteristic-2 BaseFold** — see the ⭐ row below. |
| ⭐ **char-2 BaseFold = ring-switching's own target** | **HAVE** | `Selvage/AdditiveProximity.lean`, `AdditiveFriTower.lean`, `AdditiveFriQuery.lean`, `BaseFoldBinaryMerkle.lean`, `Assurance/Tower256AdditiveFri*.lean` | `additiveProximityGap_UD`, `additiveFold_distance_UD`, `additiveFriAdaptive_coherent_sampled_sound_UD` — all proved. **This is precisely the object Diamond–Posen build to feed their compiler.** |
| **Spartan: R1CS zero-check face** | **PARTIAL** | `Assurance/AirSumcheck.lean`, `AirSumcheckQuadratic.lean`, `Compiler/AirFlatten.lean` | Present: flattened degree-≤2 gate system by catamorphism, `flatten_constraint_iff`, gates in `{0,1}^m`, `gateTableA/B/C`, defect `D = A·B − C`, `airGateSystem_sound`. **Missing: the whole Spartan cost structure** — tables are dense, one entry per gate; no `Ã(r_x,r_y)`, no inner sumcheck, no `Σ_y (r_A Ã + r_B B̃ + r_C C̃)(r_x,y)·z̃(y)`. |
| **Spartan: sparse-MLE / SPARK / offline memory checking** | **ABSENT** | — | Zero hits for `sparse`, `SPARK`, `offline memory`, `memory check`, `Lasso`, `Twist`. No timestamp vectors, no multiset/permutation check, no computation commitment. **This is what makes Spartan's verifier sublinear, and it is not started.** |
| **SuperSpartan `next` MLE / shift operator** | **ABSENT** | — | Zero `nextMle`/`shiftMle`/`cyclicShift`. ⚠ **`Selvage/AccRbrBcsShifted.lean` is a FALSE FRIEND** — its "shift" is round-schedule re-attribution, not an index shift. `Compiler/Air.lean` has **no trace, no rows, no transition relation** — a `Term (AirSig F Idx)` over one flat assignment. Uniform/repeating constraint structure does not exist as a concept here. (Source read: CCS §5.1 Thm 2, `IACR-eprint-mirror/2023/552.pdf`, `ñext = h+g`, O(log D) closed form.) |
| **Ring-switching** | **ABSENT** | — | Zero `ringSwitch`. **No `Basis` of an extension over a subfield anywhere in 400 files.** ⚠ The one base↔extension bridge runs the **opposite way**: `SmallField.lean`'s `liftWord : (ι → Fq) → (ι → K)` and `ExtensionChallengeBridge.lean`'s `liftConstraint` are **pointwise embedding with the index set unchanged** — i.e. exactly the embedding overhead ring-switching exists to delete. |
| **Ligerito / Ligero / Brakedown / interleaved PCS** | **ABSENT — deliberately** | — | Rejection is **on the record with reasons** (`notes/multilinear-pcs-landscape.md` §9.5/§11.2/§12): unrefereed note, two favourable-direction errata (see §1), commitment is interleaved with **whole-row leaves** so `OpeningScheme` re-instantiates at a row-valued type, and it needs Diamond–Gruen 2024/1351 which we do not hold. Ligero/Brakedown knowledge-soundness needs **expected-PPT rewinding extractors** — "harder in Lean than anything else in this document." |
| **Binius64 byte lookup tables** | **ABSENT** | — | ⚠ **This ingredient is not a lookup argument.** `grep -ci logup` on the Binius64 spec = **0**. It is §4.3.3's prover-side `Extrap : F₂⁶⁴ → F_{2⁸}⁶⁴` extrapolation as 8 chunks × 256-entry tables + 7 bytewise XORs, **128 KiB total**. A **field-arithmetic implementation technique** — its Lean analogue is a `native`/kernel conformance object, not a theorem. |
| **LogUp / lookup argument** | **PARTIAL** | `Selvage/LogupStar.lean` (378), `LogupIndexLink.lean`, `Compiler/Tower256Logup*.lean` | `logup_wrong_rational_accept_prob_le`, `logup_wrong_or_pole_prob_le` — poles counted separately, not silently excluded. The file states its own scope: *"a committed-pushforward integrity kernel, not a complete lookup-soundness theorem."* Two obligations open and named. |
| **Binary one-hot lookup** | **PARTIAL** | `Selvage/BinaryLookup.lean` (165) | ⭐ The teeth are the point: `boolean_sum_one_not_oneHot_charTwo` — over `ZMod 2`, `![1,1,1,0]` is Boolean, sums to 1, and **is not one-hot**. A genuine char-2 hazard, proved. But 165 lines: no Shout/Lasso, no soundness. |
| **Phalanx SIMD R1CS** | **ABSENT** | — | Zero `SIMD` in the tree. ⚠ **Corpus trap, resolved** — see below. |
| **Gruen / Dao–Thaler / Bagad–Domb–Thaler sumcheck opts** | **ABSENT, correctly out of scope** | — | All are **prover-cost** optimizations that do not change the `v·d/\|F\|` soundness statement. They belong in `prover/src/sumcheck.rs`, not Selvage. |

### ⚠ Corpus traps resolved (fix these in any future brief)

- **The Phalanx in `paperbin` is the WRONG paper.** `phalanx-fhe-friendly-snark-2025-302.pdf` (=
  `vfhe-phalanx-…ccs25-…`) is Zhang/Wang/Liu/Xiang/Deng/Fisch, *"An FHE-Friendly SNARK"*, whose
  "SIMD" is **BFV ciphertext slot packing**. I confirmed this independently: its SIMD hits are all
  "FHE SIMD … enabling batched homomorphic evaluations", and it is the corpus's **only** Phalanx
  citation. It is a plausible decoy (it *is* Spartan-based over a Ligero/Brakedown commitment).
  **The right one is Tzialla–Kothapalli–Parno–Setty, NDSS 2022 = eprint 2021/1263** — in the mirror,
  absent from paperbin. SIMD R1CS there = one `A,B,C` over **β witness columns** with I/O
  consistency `x_i.in = x_{i−1}.out`. CCS §5.3 notes SuperSpartan does that check in `O(log βℓ)` via
  `ñext` vs Phalanx's `O(βℓ)` — *"an exponential improvement."*
- `fri-binius-2024-504.pdf` and `binius2-ring-switching-binary-towers-2024-504.*` are **one paper**,
  double-filed.
- `ring-switching-sublinear-proofs-polynomial-rings-2025-199.pdf` is Huang–Mao–Zhang, a
  **lattice/Galois-ring** paper — shared phrase, unrelated mechanism. Not Diamond–Posen.
- `smallfield-turn-sok-…-2026-1371.txt` and `small-field-turn-systematization-2026-1371.txt` are
  **byte-identical**. Greyhound is absent from both corpora.
- Binius64 §4.2 attributes shift-indicator polynomials to *"Diamond and Posen [DG25, §4.3]"* while
  its own bibliography resolves `[DG25]` to **Diamond and Gruen** — an internal citation defect in
  the spec.

### ⚑ The single largest structural gap: ring-switching

**It is the largest precisely because we hold both of its endpoints and neither of its connectors.**

Diamond–Posen's reduction needs three objects: (i) a large-field multilinear PCS over `L`; (ii) a
**`K`-basis `(β_v)_{v∈B_κ}` of `L`**; (iii) the **packed multilinear**
`t'(X_0..X_{ℓ'−1}) := Σ_{v∈B_κ} t(v,X)·β_v` with **`ℓ' = ℓ − κ`**, plus a sumcheck converting an
`L`-point evaluation claim on `t` into one on `t'` by basis-decomposing *both* the prover's `ŝ_v` and
the `eq` weights down to `K`. ⚠ The naive `β_v`-recombination is **insecure**, because `(β_v)` is
independent over `K` but **not** over `L`. That subtlety is exactly the kind of thing a
machine-checked treatment is for.

We have (i) — twice, including the char-2 BaseFold that is Diamond–Posen's *own* instantiation
target. We have `L` and `K` as real objects (`binaryTower k`, `binaryTowerEmbed`,
`binaryTowerEmbedChain`, `towerMul_eq_mul`). We have the head polynomial the reduction runs on
(`eqMle`, `eqMle_fold`). We have 179K sorry-free lines on top.

**We do not have (ii) or (iii), and our one base↔extension bridge points the wrong way.** Ring-switching
is the only ingredient whose absence is a missing **object at the foundation** rather than a missing
protocol on top of held objects — because `ℓ → ℓ−κ` **re-types the index of every downstream claim**,
so it cannot be bolted on late.

Runners-up, for calibration:
- **2nd: the sparse structure-matrix commitment (SPARK / offline memory checking).** Also zero, and
  it is precisely what Binius64 §1.2 says a binary Spartan founders on. But we are *not* at zero on
  its ingredients (`LogupStar` pushforward kernel, `BinaryLookup`'s one-hot χ-vector, and
  `notes/lookup-ram-verdicts.md`'s finding that binary-tower bits are one of exactly three
  commitment families where sparse/boolean data is structurally cheap).
- **3rd: Ligerito.** Also zero — but a *priced, argued* zero, not an oversight.

---

## 10. The claims, adjudicated against primary sources

### 10.1 BinarySpartan has no primary source of any kind

| Instrument | Result |
|---|---|
| eprint title search "Spartan binary fields" | no results |
| eprint **author search "Setty"** | only **2026/242** *Neo and SuperNeo: Post-quantum folding with pay-per-bit costs over small fields* (Nguyen & Setty), updated 2026-08-14 — **small PRIME fields, not binary** |
| eprint 2026 listing browsed to **2026/1644** (Aug 9) | nothing matching |
| MSR homepage `microsoft.com/…/people/srinath/` | 41 publications, most recent **MicroNova, IEEE S&P 2025**. No 2026 entries |
| `srinathsetty.net` | ⚠ **dead domain — now a Thai lottery site. Do not cite it.** |
| GitHub code search `"BinarySpartan"` | **0** cryptography hits |
| `microsoft/Spartan2` | renamed **`vega-prover`** 2026-06-27; sources `bn254.rs`, `pasta.rs`, `pt256.rs`, `hyrax_pc.rs`, `ipa.rs` — **prime field, discrete-log PCS, zero binary-field code** |
| X/Twitter thread | HTTP 402; mirror CAPTCHA'd. **The thread was never read directly by anyone in this analysis.** |

Combined with §0.5 (paperbin ∅, mirror-2026 grep of 810 papers ∅, and the phrase appearing only in
Binius64's *"Why Not Binary Spartan?"*): **treat BinarySpartan as an unpublished claim.**

### 10.2 ⚑ The benchmark numbers do not survive contact with the primary sources

The EF benchmark is real: `privacy-ethereum/csp-benchmarks` (PSE), rendered at
ethproofs.org/csp-benchmarks. ⚠ **Its hardware is Apple M1, 8 cores, 16 GB (AWS `mac2.metal`)** —
*not* an M4 Max. Raw result JSON, SHA-256 @ 2048 B, latest committed run 2026-06-26:

| System | **Measured** | Claimed | Field / PCS per the repo's own metadata |
|---|---|---|---|
| Flock | **33.93 ms** | 26.0 ms | `F2^128`, BaseFold, sec=100 |
| Binius64 | **67.29 ms** | 62.0 ms | `F2^128`, iop="Binius64 + Spartan", BaseFold, sec=96 |
| spartan2 | **541.72 ms** | "Vega 44.2" | **`P256`, Spartan, Hyrax, sec=128** |

1. ⚠ **"Vega" does not appear in the EF benchmark at all.** The closest entry is `spartan2` — the
   same crate, before its 2026-06-27 rename to `vega-prover` — measured at **541.72 ms, i.e. 12×
   the claimed 44.2 ms.**
2. ⚠ **Vega is not a binary-field or post-quantum system.** P-256 + Hyrax is discrete-log. Putting it
   in a post-quantum binary-field comparison is a category error.
3. ⚠ **Hardware mismatch, unresolved and load-bearing.** M4 Max/12P vs M1/8-core plausibly accounts
   for 3–5× by itself — **enough to consume most or all of the claimed 4.2× margin over Flock.**
   Whether the 26.0/44.2/62.0 figures were re-run on an M4 Max or lifted from the M1 harness is
   undetermined, and **that single question decides whether the headline survives.**

**And the cross-check is worse.** Flock's own paper (Bünz–Rothblum–Wang, arXiv 2607.27491 / eprint
2026/1329, 2026-07-29), abstract verified verbatim:

> "On a **single core of an M4 Max** processor, Flock proves **82k** evaluations of the BLAKE3
> compression function, **42k** SHA-256 compressions, and **30k** Keccak permutations per second…
> On ten cores, throughput exceeds **660k** BLAKE3 compressions per second."

Same chip, so directly comparable:

| | BinarySpartan (12 P-cores) | per core | **Flock (1 core)** |
|---|---|---|---|
| BLAKE3 | 410,000 | 34.2k | **82k** |
| SHA-256 | 219,000 | 18.3k | **42k** |
| Keccak | 163,000 | 13.6k | **30k** |

**Flock is ~2.2–2.4× faster per core, and beats BinarySpartan outright in aggregate** (>660k BLAKE3
on ten cores vs 410k on twelve). Caveat, stated fairly: BinarySpartan's figures say "including
witness generation"; Flock's abstract does not say. If Flock's exclude witness-gen the gap narrows.

**Internal tension in the claim itself.** 2 KiB + SHA-256 padding = 33 compressions. At 219,000 h/s
that is **0.151 ms** of throughput-equivalent work against **6.2 ms** claimed latency — a **41×
fixed-cost gap**. Both can be true (latency vs batch throughput), but **the two headline numbers do
not corroborate each other**, and "4× faster than Flock" is metric-selective: Flock is explicitly a
*batch* prover, so a single 2 KiB instance is its worst case.

### 10.3 The Poseidon claim: the quote is real, the institution is not behind it

Drake's X post (2026-08-13), as surfaced in search snippets and four secondary outlets — **X could
not be fetched directly**:

> *"Goodbye, Poseidon! … The Ethereum Foundation is abandoning Poseidon for L1, pivoting to SHA or
> BLAKE."* and *"In hindsight the key was not SNARK-friendly hashes, but hash-friendly SNARKs."*

✅ The quotes are accurate. ~1M hash calls/sec on a laptop, ~100× overhead vs native, leanVM 2027 /
deployments 2028 — all as briefed.

❌ **But there is no official EF publication.** blog.ethereum.org's Jul–Aug 2026 posts are WEBCAT
grants, a Board Update, Devcon 8 tickets, and AI triage — nothing on Poseidon or hashes. **The
Poseidon Cryptanalysis Initiative is still scheduled through December 2026 with live bounties.** So
the evidence supports *"a senior EF researcher publicly stating an EF position, echoed by press,
with no institutional artifact behind it."*

**And say this part out loud: Poseidon was not broken.** "Reaches its dream conclusion" means it
*survived*; the pivot is performance-and-conservatism driven. This corroborates §8 exactly.

⚠ **The tension nobody in the coverage names:** the actual leanVM (`leanEthereum/leanVM`, pushed
2026-08-07) is **KoalaBear — a 31-bit PRIME field** — with degree-5 extension, WHIR + SuperSpartan +
Logup, ~124 bits provable security. **It is not a binary-field system today.** "The EF's PQ team is
building binary-field infrastructure as part of leanVM" is aspirational relative to what is in the repo.

---

## 11. Is anyone else machine-checking a binary-field proof system?

**Yes — exactly one group, it is Lean 4, it is EF-funded, and it shipped this week.** "Every
formalization is prime-field" is false, but only barely.

| Project | What it holds today | Field | Active |
|---|---|---|---|
| **ArkLib** (Verified-zkEVM; Quang Dao/CMU + EF), 323★ | IOR framework, Fiat–Shamir, `ProofSystem/{Binius,Stir,Fri,BatchedFri,Spartan}`, its own `Data/CodingTheory` (Reed–Solomon, Berlekamp–Welch, Johnson, proximity gaps) | **BINARY + prime** | **2026-08-14** |
| **CompPoly** (split out of ArkLib), 47★ | `Fields/Binary/` — 31 files, 813 KB: Wiedemann tower, additive NTT, GF(2^128)/GHASH | **BINARY** | 2026-08-14 |
| **Clean** (zkSecurity, Mitscha-Baude), 175★ | circuit eDSL, `Channel`/`Ensemble` for multi-AIR zkVMs, soundness+completeness per gadget | ⚠ **prime only, structurally**: `abbrev F p := ZMod p` with `[Fact p.Prime]` | 2026-08-14 |
| **soundcalc-lean** (symbolicsoft) | every soundcalc report cell re-derived as a theorem over exact ℚ | **all prime** | current |
| **Binius64** (`binius-zk/binius64`), 168★ | **632 Rust files. Zero `.lean`/`.v`/`.thy`.** | binary, **unverified** | 2026-08-14 |
| **Flock** (`succinctlabs/flock`), 72★ | zero proof-assistant files | binary, **unverified** | 2026-08-14 |
| AFP `Sumcheck_Protocol` (Garvía/Sprenger/Bootle) | Isabelle/HOL, completeness **and** soundness | field-agnostic by axiomatization; **never instantiated at a binary field** | static |
| infotheo (Rocq) | `ecc_classic/{reed_solomon,bch}`, `lib/f2.v` — **binary BCH machine-checked** | GF(2) | 2026-07-29 |
| `IrreducibleOSS/binius` | ⚠ **ARCHIVED** 2025-09-09, superseded by `binius-zk` | — | dead |
| `lean-fri` | ❌ does not exist | — | — |

I confirmed the **soundcalc-lean** row independently against the local checkout at
`/Users/ember/dev/soundcalc-lean` (55 Lean files). It is **structurally prime-pinned by
construction** — `Soundcalc/Field/Core.lean:45`:

```lean
structure FieldParams where
  base : PrimeField
  e    : ℕ
  epos : 0 < e
abbrev FieldParams.twoAdicity (F : FieldParams) : ℕ := F.base.twoAdicity   -- v₂(p − 1)
abbrev FieldParams.prime (F : FieldParams) : F.p.Prime := F.base.prime
```

`Soundcalc/Field/` contains BabyBear, Goldilocks, KoalaBear, Mersenne31 and **no binary tower**. The
type carries a **primality proof** and a **2-adicity** field — i.e. the smooth multiplicative
subgroup that GF(2^k) cannot have. It could not represent a binary field without redesigning its
core type.

### 11.1 ⚑ ArkLib's binary cone — read the leaves, not the top file

ArkLib's field discipline is a typeclass constraint the theorems cannot escape
(`ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean`):

```lean
variable {L : Type} [Field L] [Fintype L] [CharP L 2] …
variable (𝔽q : Type) [Field 𝔽q] … [hF₂ : Fact (Fintype.card 𝔽q = 2)]
```

But the umbrella is greener than the leaves — **exactly this repo's own "per-file green hides a red
umbrella" class**:

- `BinaryBasefold/General.lean` — **0 `sorry`**; has both `fullOracleReduction_perfectCompleteness`
  **and** `fullOracleVerifier_rbrKnowledgeSoundness` (round-by-round, explicit error term), composed
  via `append_rbrKnowledgeSoundness`. **This is a real result and it is ahead of us on composition.**
- `FRIBinius/General.lean` — 0 `sorry`, **completeness only**, and the file ends
  `-- TODO: state RBR KS`. ⚠ **For FRI-Binius the soundness property is not even stated.**
- The leaves those theorems rest on are **not** sorry-free: `Steps.lean` 13,
  `FRIBinius/CoreInteractionPhase.lean` 9, `BatchingPhase.lean` 5, `QueryPhase.lean` 4, `Basic.lean`
  2, `CoreInteractionPhase.lean` 2 — **33 `sorry`s across the Binius directory.**

**CompPoly's arithmetic layer, by contrast, is genuinely clean**: ~10,354 lines, 363 theorems,
**0 `sorry`, 0 `axiom`, 0 `native_decide`, 0 `#guard`.** Tower irreducibility *proved* via the
trace-map property; the abstract tower proved isomorphic to the computable `BitVec` representation
(`Equiv.lean`, 0 sorry — the step that makes it non-vacuous); additive NTT proved correct;
GF(2^128)/GHASH irreducibility discharged by explicit gcd/mod **certificates** rather than
`native_decide`. **They arrived at this repo's `#guard`/`native_decide` position independently.**

### 11.2 Three things worth flagging

1. ⚠ **There is no ArkLib ↔ Binius64 connection of any kind.** ArkLib formalizes the Diamond–Posen
   *paper*; `binius64` is 632 Rust files with no extraction, no spec link, **not even a differential
   test**. The deployed binary-field prover carries **zero formal content**. Same for Flock.
2. **Quang Dao is the hinge.** He is first author of eprint **2026/587** *Speeding Up Sum-Check
   Proving* (Dao, DeStefano, Domb, Bagad, Thaler, 2026-03-24) — the optimization BinarySpartan
   reportedly cites — **and** ArkLib's lead. VCVio (Tuma, Dao, Waters, Hicks/EF, Hopper) is the same
   cluster.
3. **`clean`'s `abbrev F p := ZMod p` with `[Fact p.Prime]` is the single cleanest artifact of the
   prime-field monoculture**: the EF-funded Lean circuit DSL for the ecosystem **cannot represent a
   binary field at all.**

### 11.3 Scope of the absence — naming the instruments

Negative results came from: AFP topic browse + targeted queries (**no AFP entry for FRI, proximity
testing, IOPs, or PCPs**; no coding-theory topic exists); a **Mathlib full-tree grep** for
`GaloisField|BinaryTower|ReedSolomon|CodingTheory|Hamming` → **2 files**, and `GaloisField.lean` is
`noncomputable` with no tower and no `BitVec` bridge — **unusable as a substrate, which is precisely
why ArkLib built its own coding theory**; `gh search code "binary tower field" --language coq` → 0;
org listings for IrreducibleOSS, binius-zk, o1-labs, Veridise, reilabs, runtimeverification,
NethermindEth.

⚠ Not covered: **GitLab** (Binius originally lived at `gitlab.com/IrreducibleOSS/binius`), private
work, F*/EasyCrypt/Jasmin beyond the KZG paper, non-English venues. And GitHub code search indexes
incompletely — `gh search code "Binius" --language lean` returned 2 hits though
`ArkLib/ProofSystem/Binius/` demonstrably exists — so **negative code-search results are weaker
evidence than tree listings**, which were used wherever the repo was known.

### 11.4 One asset the brief did not know we had

`/Users/ember/dev/breadstuffs/GOAL-ARKLIB-VACUITY.md` (53 lines) records that **we already found and
repaired a vacuity in ArkLib itself**: its KZG evaluation-binding was vacuous (`tSdhAssumption` is
`Classical.choice`-false at every parameter). The repair landed, and on top of it
`tSdh_ggm_sound` — a bound over ArkLib's **real** `tSdhExperiment` — was proved in **both** standard
generic-group models (Maurer and Shoup), sorry-free and axiom-clean, with a 16-commit PR package
assembled against ArkLib's contribution guidelines (**not filed**).

**That is a working relationship with the exact group that owns the only other binary-field
formalization, and a demonstrated ability to find vacuity in their tree.** It is the strongest
non-technical asset in this analysis.

---

## 12. ⚑ THE HONEST POSITION

### 12.1 Answer to the question that was actually asked

**Our formal layer is field-agnostic, and this is a genuine opportunity — with one wall that is
already breached and one gap that is real.** Not "prime-pinned and this is a problem."

The evidence, in one paragraph: there is **no multiplicative evaluation domain anywhere in the repo**
(0 `IsPrimitiveRoot`, 0 `rootsOfUnity`, 0 `primitiveRoot`); every Reed–Solomon code is over an
abstract `dom : ι ↪ F`; **13 of 18 compilation keystones transfer with no new mathematics**; the
prime pins are `ZMod 5`/`ZMod 7` *teeth* and a BabyBear *deployment* layer, never theorem binders;
the one structural wall (`FoldingData`, carrying `two_ne : (2 : F) ≠ 0` as a **structure field**)
**already has its char-2 replacement built and proved** (`AdditiveFriTower`/`AdditiveFriQuery`,
reaching a real multi-round UD soundness bound `m·2^(ℓ−1)/|F| + (1−τ)^q`); and the binary cone is
**wired, not orphaned**, with 0 `sorry`, 0 `axiom`, 0 `native_decide`.

### 12.2 What is genuinely missing, in priority order

1. **Ring-switching** — the largest structural gap, because we hold **both endpoints and neither
   connector**. No `Basis` of an extension over a subfield exists in 400 files, and our only
   base↔extension bridge (`liftWord`) points the **wrong way** — it *is* the embedding overhead
   ring-switching deletes. `ℓ → ℓ−κ` re-types every downstream claim, so it cannot be bolted on late.
2. **Spartan's sparse-MLE / SPARK / offline memory checking** — at zero, and it is exactly what
   Binius64 §1.2 says a binary Spartan founders on. But we are not at zero on its *ingredients*.
3. **Interleaved-code proximity (Diamond–Gruen 2024/1351 Thm 3.1 + AER Thm 3.6)** — needed only if
   we chase Ligerito specifically. New mathematics (rank/row-space), not a port of our root-counting.

### 12.3 The three things I would say out loud

**(a) Do not lead with the benchmark story, and do not repeat the numbers.** BinarySpartan has no
primary source; Flock beats its per-core figures ~2.2–2.4× *on the same chip, from a verified
abstract*; the EF harness that produced the comparison set runs on an **M1**, not an M4 Max; and
"Vega 44.2 ms" corresponds to a system measured at **541.72 ms** that is **discrete-log, not
post-quantum**. Anyone who leads with these numbers will be corrected in public.

**(b) The durable argument is structural, not the obituary.** "Poseidon is dead" is overstated —
Poseidon was **not broken**, the Initiative pivoted Poseidon2→Poseidon1 (MDS) and still runs through
December 2026, and there is **no institutional EF artifact**, only one researcher's tweet. The real
argument is that hash-based SNARKs over binary fields **remove the algebraic-hash cryptanalysis
surface entirely** — and even that needs the honest caveat that it holds only when you then use a
*traditional* hash, because binary-tower land has its own algebraic hash (**Vision Mark-32**,
co-authored by Posen) carrying the same exposure class.

**(c) We are not alone, we are not first, and we are ahead on the axis that matters.** ArkLib +
CompPoly are real, EF-funded, active this week, and **ahead of us on ring-switching and on
composition** (their Binary BaseFold has a *composed* RBR-knowledge-soundness theorem). But their
FRI-Binius **has no soundness statement at all** (`-- TODO: state RBR KS`) and there are **33
`sorry`s in the Binius leaves**, while our comparable cone is **0/0/0** and our additive-FRI bound is
proved, not stated. Meanwhile the two *shipped* binary provers — Binius64 (632 Rust files) and Flock
— carry **zero formal content, not even a differential test**.

### 12.4 What a machine-checked binary-field proof system looks like from here

**The short path is not Ligerito. It is BaseFold-on-the-additive-tower, then ring-switching.**

1. **Re-key `BaseFoldCompleteness`/`BaseFoldIor`/`RateRegimeSelector` from `FoldingTower` onto the
   proved `AdditiveFriTower`.** Composes two things that both already exist and both already sit at
   ℓ = 2. ⚠ **Do not instantiate `FoldingData` at char 2** — it is uninhabitable, so every theorem
   over it goes **vacuously true** with a green build and no axiom-check will notice.
2. **Delete-and-simplify `BaseFoldBcsQuerySampling` and `BaseFoldBcsByteCodec`.** Over GF(2^k) the
   rejection sampler and the canonicity obligation both *evaporate*. This is the one place "port" is
   the wrong verb.
3. **Then ring-switching** — and this is the strongest single lead in the note, for a structural
   reason: ring-switching is a **compiler with security-preserving reductions** (Thm 3.2 completeness,
   Thm 3.5 security, the latter by **constructing an emulator E from E′**). That is *exactly and only*
   what the Selvage layer is. And Diamond–Posen's own compilation target is "a **characteristic-2
   adaptation of BaseFold**, developed at length" — i.e. **step 1 produces precisely the object step 3
   consumes.**

**The one-breath version:** *we hold a field-agnostic, sorry-free, axiom-free compilation layer and a
proved characteristic-2 BaseFold, which is the exact object Diamond–Posen's ring-switching compiler
consumes; the missing piece is the compiler itself, and a security-preserving compiler between proof
systems is the only thing this layer has ever been for.*

### 12.5 Immediate repo actions this analysis surfaced, independent of any of the above

- ⚠ **`Assurance/Tower256AdditiveFriControllerAdmission.lean` and
  `Tower256AdditiveFriActualReduction.lean` are VACUOUS at positive FRI height** — both bind
  `variable {pcs : MerklePcs ell}`, and `merklePcs_empty_of_positive` **proves that type empty**.
  `scripts/CarrierCensus.lean:145-160` knows; the modules still read as results.
- **`docs/SELVAGE-COMPLETE.md:155-159` is refuted by `jointGameFamily_impossible`** (it claims the
  "two-ledgers residual" is closed), and **`:106-107` lists the raw non-binding PCS as open when it
  has landed.** Two doc defects.
- **Stale docstrings that would mislead an auditor into thinking the additive cone assumes a
  proximity gap when it proves one**: `Theory/AdditiveNTTTransform.lean:419` ("RESIDUAL HYPOTHESIS")
  and `:508`; `Selvage/AdditiveFriTower.lean:402-411` (claims no honest type exists to instantiate,
  refuted by `AdditiveFriQuery.lean`).
- **`FarWordSoundnessCertificate` is never constructed** and *cannot* be at the deployed carrier —
  `Tower256AdditiveFriRawDeployment.zeroTranscript` has every word `= 0`, and the zero word **is** in
  the RS code, so `initialFar` is false by construction. The deployed instance is `ell=1, m=1,
  degree=1`: a statement-inhabitation carrier, not a firing of the bound.

