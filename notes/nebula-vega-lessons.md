# Nebula & Vega — lessons, the DL dividend priced, and the PQ-Vega path

2026-08-17. DEEP-READ + CHARTING lane. Both papers read end-to-end at source this session:
**Nebula** = Arun–Setty, *"Nebula: Efficient read-write memory and switchboard circuits for
folding schemes"* (`~/paperbin/nebula-folding-machine-executions.pdf`, S&P 2026; eprint 2024/1605
by adjacency with NeutronNova 2024/1606, also read in part from the mirror). **Vega** =
Kaviani–Setty, *"Vega: Low-Latency Zero-Knowledge Proofs over Existing Credentials"*
(**eprint 2025/2094**, mirror copy `~/dev/gh/forks/IACR-eprint-mirror/2025/2094.pdf`, S&P 2026).
Read against: `docs/LEAF-VS-RECURSION.md`, `notes/ring-hash-dual-mode.md`,
`notes/neo-superneo-read.md`, `minidregg/Selvage/{HeteroComposition,Depth,AccRbrBcs*}.lean`,
`minidregg/Kernel/SparseAuthenticatedState.lean` + `Compiler/SparseAuthenticatedStateLogupBridge.lean`.
Tags: `[READ]` verbatim at a named source · `[DERIVED]` arithmetic on stated counts, labeled ·
`[MEASURED]` only where a prior lane's instrument is cited. Their numbers carry THEIR conditions;
ours are counts, not clocks.

---

## 0. One-breath verdict

**The recursion-seam gap is real, it is ~three orders of magnitude, and it is bought with one
assumption: commitments that ADD.** Everything else in these two papers — the memory argument, the
switchboard, even most of the ZK trick — is *transferable in shape* to a linear-commitment PQ stack,
and the dual-mode note's own cost table prices a Nova-shaped fold over our MSIS commitment at
**~4–7×10³ R_q rows per step ≈ 4–8% of the FS bill it rides beside** — the PQ Vega nobody has
priced, priced (§1c). Their memory soundness statement is exactly the theorem our `TwistContinuity`
residual has been waiting for, and it is **not DL-bound** (§3). Their formal content is zero —
verified at repo and corpus with instruments named (§6). Where they win, it is measured latency on
a DL substrate and mechanism maturity for memory; where we win, it is the assumption, the
machine-checked statements, and a refutation of a published theorem their proof style cannot even
express (§2).

---

## 1. Q1 — the DL dividend, quantified at source

### 1a. Their verifier costs, verbatim

| object | cost | source `[READ]` |
|---|---|---|
| Nova folding verifier circuit | **≈10,000 R1CS multiplication gates** — "a random linear combination of homomorphic commitments and performs some hashing" | Nebula §1, citing microsoft/Nova |
| HyperNova folding verifier | "slightly higher hashing" than Nova; k−1 group scalar mults + O(d·log m) hashes | Nebula §1; NeutronNova §comparison |
| NeutronNova (ZeroFold) verifier | **k+1 group scalar mults + O(d) hashes/field ops**; "improvement atop Nova in verifier circuit sizes (by about **10–13%**)"; folding n instances = 1+log n rounds | NeutronNova 2024/1606 |
| CC-NIVC overhead over NIVC | instance: +1 commitment; proof: +2 commitments +1 hash; per-step circuit: **+1 hash + 1 group scalar mult** (independent of \|ω\|) | Nebula Lemma 1 |
| Nebula layer-2 fold circuit | **≈40,000 gates to fold four instances** | Nebula §4.4(3) |
| memory op (Nebula) | **4 constraints** + range check rc_m + amortized scans <4·\|M\|/m; vs Spice ≈1,100, Merkle 3,750–8,000 | Nebula Table 2 |
| Bünz–Chen 2024/325 memory (their comparison) | (c+1)·log T scalar mults ≈ **100,000 constraints** in-circuit, degree 4–7 | Nebula §1.2 |
| Vega's ZK circuit (Succinct NovaBlindFold) | verifier-checks SCR1CS = **"a few hundred constraints even when the original constraint system has a million or more"** | Vega §6.1.2 |

Commitment assumptions, confirmed at source: Nebula rides Pedersen/MSM-based homomorphic
commitments ("committing to 0s is free in MSM-based commitment schemes" is load-bearing for
pay-per-use, §5.3's cached-`Cz₁` trick is Pedersen homomorphism); Vega is **P-256/T-256 + Hyrax
PCS** — a curve chain, DL through and through (§4.3, §7; prior lane's Spartan2→vega-prover
finding corroborated). Nova additionally needs a **curve cycle** for the non-native group
arithmetic — a cost their headline gate counts already absorb but their assumption column pays.

### 1b. The seam gap in one currency `[DERIVED]`

Ours, measured (`docs/LEAF-VS-RECURSION.md`, commit `1ba443bdd`): the wrap's in-circuit FRI
verifier = **38,168 Poseidon2 permutations** — identical to the child's native verify, row for
row — 94.1% of hashing width-driven; wrap 40.55M → **28.97M cells** at the landed packing;
**K = wrap/leaf = 26.9**.

Nebula's own conversion constant ("a hash invocation costs about ≈250 constraints", §Challenge 1)
puts our wrap's *hashing alone* at 38,168 × 250 ≈ **9.5×10⁶ constraint-equivalents** against
Nova's **10⁴**: **the recursion seam is ~10³× wider over Merkle than over Pedersen.** The
mechanism is exactly the one the leaf-vs-recursion note isolated: Pedersen commitments add, so a
fold verifier checks `C' = C₁ + ρ·T + ρ²·C₂` and never opens anything; a Merkle root supports no
linear recombination, so every combination is an OPENING — query paths, leaf sponges, transcript
absorption — and that is the whole 38,168.

Honesty about what each side buys: Nova's 10⁴ buys a *fold* — succinctness deferred to a final
SNARK (Vega's proofs are 108 kB and verify in 23 ms because Spartan+Hyrax compresses at the end);
our 38,168 buys a *full verify* at every layer, i.e. succinctness at every step. And the
`neo-superneo-read.md` calibration stands: replacing hashing *inside* our existing wrap caps at
×1.6–2.2 (hashing is 36.45–53.98% of cells, a plurality not a supermajority). The 10³ dividend is
only reachable by **not verifying in-circuit at all until the end** — folding is a different
recursion *shape*, not a cheaper hash.

### 1c. ⚑ THE PQ-VEGA PRICING — Nova-shaped folding over the dual-mode linear commitment `[DERIVED]`

`notes/ring-hash-dual-mode.md` already holds the currency: R_q = Z_q[X]/(X¹⁶+1), q = 2⁶⁴−257,
τ=2, B=2¹⁶, K=4 planes, κ=24; Feistel absorb **27.4 rows/ring element**; per-step FS bill
**92,396 rows** (gadget-Feistel) / 363,513 (σ-Poseidon τ=2); 1 row = 1 ring mult. A committed
relaxed-R1CS-shaped fold step over `C = A·Y` prices as:

| component | R_q rows |
|---|---:|
| absorb fresh instance: witness commitment κ=24 + cross-term commitment κ=24 → 48 × 27.4 | 1,315 |
| fold arithmetic `C' = C₁ + ρ·T + ρ²·C₂` (+ value/instance folds): ~2–3 κ-length scalar ops | ~50–80 |
| norm control per fold (Π_DEC-shape, k=K=4): absorb 4 fresh plane commitments = 96 elts | 2,630 |
| recomposition check Σ_k B^k·C_k = C: k·κ ring mults | ~100 |
| **total per fold step (Feistel FS)** | **≈4.1×10³**, ×1–2 O5 schedule factor → **4–7×10³** |

**≈4–8% of the per-step FS bill the artifact already pays** — the fold seam is nearly free *in
its own world*, exactly as the dual-mode note found for the evaluation opening (which is paid
once at the end, 1.5–2.9×10⁴ rows, not per fold). Cross-substrate, with §4c's stated conversion
range (100–1024 base-mult-equiv/row): a PQ fold step ≈ 0.4–5×10⁶ equiv — **roughly 4–50× a DL
fold (10⁴ constraints on a 256-bit field), and ~10²–10³× below the Merkle wrap.** The ordering,
with all unit caveats owned:

```
  DL fold (Nova)  ~10⁴ gates   <   PQ fold (dual-mode)  ~4–7×10³ R_q rows   <<   Merkle wrap  38,168 perms
        1×                              ~4–50× DL [DERIVED]                        ~10³× DL [their constant]
```

**The dividend survives post-quantum at an order-of-magnitude discount, not a collapse.** The
prices assume: the host pays its norm checks (the §5c fail-open hazard — under folding this
becomes *per-round and structural*, which is the right place for it: the folding schedule IS the
norm machinery), and the substrate migration itself — the R_q prover/IVC infrastructure that does
not exist in the tree. `PROVEN-IN-LEAN ≠ ROUTABLE`'s grep test fails maximally here; this is a
BUILD, and the dual-mode note's §7 already gated it on the substrate decision above any note's
pay grade.

**γ-grinding under folding — settled, negligible `[DERIVED]`.** Each absorbed commitment's plane
representative is prover-chosen; at γ/q = 2⁻⁵⁶ the expected ambiguous coefficients are ~2⁻⁵²/ring
element, so per fold step (~100 absorbed elements) ~2⁻⁴⁵ — the prover almost never even *has* a
choice. Folding multiplies the channel linearly in volume, never exponentially; the term stays
~Q·2⁻⁵²·(elements) in the ROM ledger, unchanged in class from the design note's accounting. The
term that IS new under folding is **Q·ε_MSIS** (FS over a committed transcript binds only
computationally — hazard §5b), one per absorbed commitment; linear in Q, carried not hand-waved.

**Where Neo's 16× lands.** The corrected figure (`neo-superneo-read.md` §0a: 512 B/ring element
vs 32 B/field element) is a data-volume fact about a *field-native hash eating ring elements* —
the LatticeFold configuration. The dual-mode kills that configuration twice: the hash is
ring-native (27.4 rows/element — no per-element decomposition into 16 field absorbs), and §4d's
commit-instead-of-absorb caps any committed vector's transcript footprint at **κ = 24 elements**
regardless of length (break-even n_r > 24 amortized). Neo dissolves the 16× by embedding the
transcript into the field; the dual-mode neutralizes it by making the hash live where the data
lives and compressing volume through its own commitment mode. Substitutes, as the Neo note said —
but only the dual-mode ALSO supplies the evaluation-binding commitment the fold endpoint needs.
No honest single number compares the two (different currencies); the refusal is §4c's.

---

## 2. Q2 — commitment-carrying IVC mapped onto AccRbrBcs / Depth / VerifierEmbedding

**Their object** (Nebula §3, Construction 2): proof Πᵢ = ((Uᵢ,Wᵢ),(uᵢ,wᵢ),pcᵢ,Cᵢ₋₁); carried
commitment Cᵢ = H(Cᵢ₋₁, C_ωᵢ₋₁) reusing the witness commitment the folding scheme already
computes; the step circuit F′ hashes (vk,i,z₀,zᵢ,Uᵢ,pcᵢ,Cᵢ₋₁) into the public IO, folds via
NIFS.V, and increments C. Knowledge soundness (Thm 1, App B.1): the classic **sequential
extractor recursion** — Eᵢ₋₁ built from Eᵢ plus the folding scheme's extractor, ε − negl(λ) per
level, **n a global constant**. Their depth story is the constant-depth heuristic, unpriced per
round.

**The mapping, both directions:**

- **CC-IVC ↔ `accReductionBcs`.** Both accumulate committed advice and extract it back through
  the chain. Ours is at the BCS/root alphabet with the verifier CHECKING every opening,
  `extract_sound` PROVED at the **(t+k)·accRbrError** price (RBR, quantitative), and backward
  composition returning the committed words exactly (`bcs_extract_is_seam`). Theirs extracts by
  hash/commitment binding through a paper induction with no per-round price.
- **⚑ Their fold schedule IS our open residual.** In Construction 2 the folded output's
  commitment exists only *after* the challenge that folded it — the exact **lagged-root
  schedule** of `AccRbrBcsShifted` (`h_{i+1}` committed only after ρᵢ), whose residual (a) — the
  adaptive-increment round bound, "the scored increment's challenge is one round old, so the
  fixed-pair event cannot price it" — is precisely the step Nebula's proof *does not attempt to
  price round-by-round*; sequential extraction never sees it. Our residual is the honest name for
  a gap their proof style walks past.
- **The corner check, asked for by the brief.** `Depth.lean` proves the published [OB-2]
  composition (WARP 2025/753 Thm B.4 shape) **FALSE** at `Z = ∅` — ε_rbr constrained only ON the
  statement set, so `ε := −1` satisfies a vacuous hypothesis while the conclusion demands
  `0 ≤ (t+k)·(−1)` (`OB2_depth_composition_false`; repaired with a nonnegativity guard and then
  PROVED, `OB2_depth_composition_nonneg_proved`). **Does Nebula's accumulation hit that corner?
  No — and for a revealing reason:** their Definition 5(ii) quantifies negl(λ) directly against
  an adversary-chosen instance, with no ε-function-over-a-statement-set to degenerate. The corner
  is unexpressible in their formalism *because no concrete bound is expressible in it at all*.
  They cannot state the theorem we refuted, and cannot state the repaired one either.

**What they can state that we currently cannot:**
1. **Folding at the commitment alphabet.** `Rbr.Reduction`/`AccRbrBcs` live at Merkle roots +
   opened columns; "recombine two ROOTS linearly, unopened" is untypeable there — roots do not
   add. The dual-mode linear commitment is exactly what would make an **`AccRbrFold`** instance
   statable (additive root type, fold as the round message). Named as the Lean follow-up (§7).
2. **NIVC** — per-step function selection (pcᵢ = φ(zᵢ,ωᵢ), ℓ step functions, pay-per-use).
   Selvage has no analog of a step-indexed relation family; our tower is uniform per layer.
3. **Memory-coupled accumulation** — layer-2's F_final checks 2–7 (C-continuity across finalized
   proofs, γ-derivation pinning, the multiset equality) couple the accumulator to a memory claim.

**What we state that they cannot:** the machine-checked refutation + repaired quantitative bound
(above); `widened_relation_refuses_embedding` — the **IsEmpty tooth** that a verifier gadget
accepting strictly more than its verifier admits NO embedding (directly relevant to their
switchboard, §5); and `ivc_tower_sound`'s type-level fact that **unbounded depth needs a
SELF-embedding** — their F′ containing NIFS.V *is* a self-embedding, but nothing in their
formalism marks the closure requirement; our `ComposeFixedPoint` names it, and `ComposeErrorBound`
honestly remains named-not-proved on our side too.

---

## 3. Q3 — their read-write memory vs our `TwistContinuity` residual

**Their memory soundness statement, exactly `[READ]`:**

- **Lemma 2** (offline checking, exact direction, citing Spice extended [eprint 2018/907,
  Lemma C.1]): with the timestamp discipline (reads/writes bump ts; assert t < ts), *if every
  read returns the tuple last written, then ∃ FS with `IS ∪ WS = RS ∪ FS` (multisets), FS = final
  memory; conversely if any read violates last-write, NO such FS exists.*
- **Corollary 1** (fingerprinted): the γ-product equality
  `∏(i+γ₁vᵢ+γ₁²tᵢ−γ₂)·∏(wa+γ₁wv+γ₁²wt−γ₂) = ∏(ra+γ₁rv+γ₁²rt−γ₂)·∏(i+γ₁v′+γ₁²t′−γ₂)` holds w.p.
  1 if consistent, and w.p. **≤ O(M+N)/|F|** for ANY FS if not — over γ₁,γ₂ sampled *after* the
  prover commits; requires N < char F, timestamps in F.
- **Theorem 2**: the two-layer IVC (ΠF carries the advice commitment; F_ops/F_scan recompute the
  four multiset hashes under it; γ's derived by hashing C_n; layer 2 folds finalized proofs) is
  an IVC scheme with **sequential consistency** and prover space O(|F|+M). Soundness = CC-NIVC
  extraction + commitment binding + Corollary 1.

**Is this the answer to `TwistContinuity`? Yes — in shape, and the shape is not DL-bound.**
`TwistContinuity` (Compiler/SparseAuthenticatedStateLogupBridge.lean:90) is the row-only
sequential-consistency relation, stated inductively; today it is PROVED only in the honest
direction (`of_busRelation`: an accepted *semantic* execution's bus satisfies it), and the
adversarial direction — a *committed* bus forced into continuity by a cryptographic argument — is
the named residual ("the semantic statement a Twist-style argument must prove"). Nebula's Lemma 2
is **precisely the missing combinatorial keystone**: it reduces the inductive threading to
(multiset equality + timestamp order + range checks), i.e. to objects our tree already has
machinery for — LogUp/`logupDot` for the fingerprint, `AcceptedLogupRun`'s roots-before-challenge
schedule for the commit-then-γ discipline, and the `uniformProb` toolkit for the Schwartz–Zippel
bound. **The DL content of Nebula's memory is nil**: the incremental commitment needs only
binding + incrementality (their own Construction 1 is a hash chain), and the fingerprint is field
arithmetic. Only the *carrier* (reusing the folding scheme's Pedersen witness commitment for
free) is DL; a Merkle root or Ajtai commitment carries identically.

Deltas to respect before transplanting:
- Their memory is ONE flat address space with prover-supplied timestamps; our `Layout` is typed
  namespaces with **ROM/RAM/appendOnly disciplines** — strictly richer. Their storage
  "insert" (write-without-read for uninitialized keys, double-insert-protected per Spice) is our
  `appendAllocate`. **Their model has no `free`** — our `ramFree` (deallocation, `some → none`)
  has no Nebula analog, and offline checking with reallocation needs its own argument (a freed
  cell's timestamp history must not let a stale tuple re-enter RS). Flag, don't assume.
- Their "non-recursive cost profile" claim is real and conditional: 4 constraints/op **plus**
  rc_m **plus** two linear scans amortized over ≥2¹⁵ ops per structure (Table 2's own caveat for
  persistent storage: scan cost ∝ initialized keys, "a few thousands to tens of millions").

---

## 4. Q4 — NovaBlindFold vs our VEIL-class ~3%

**The trick, at source** (Vega §2.1.2, §6; HyperNova [27] Lemma 9 for HVZK): run the *non-ZK*
PIOP; commit each round message with hiding Pedersen commitments; write the PIOP **verifier's**
checks as a split-committed R1CS — O(log m), "a few hundred constraints" after moving the witness
evaluation out to the PCS's ZK evaluation argument; fold that tiny instance with a **randomly
sampled relaxed instance** (one Nova fold = one hiding commitment sent); reveal (or
Spartan-prove) the folded witness. ZK because the random instance masks; exponential improvement
over folding the *original* instance with a random one.

**Anatomy of the dependence:** the fold is a linear recombination of commitments (homomorphism),
the mask is a hiding commitment (Pedersen), and the endgame needs a ZK evaluation argument
(Hyrax). **On Merkle, step (b) does not exist** — there is no fold of two roots, so Succinct
NovaBlindFold in its own form is another DL dividend. **On the dual-mode linear commitment it
transfers in shape**: A·Y is additively homomorphic, so "fold the tiny verifier-check instance
with a random instance" is statable — but the *hiding* half costs what lattices always charge:
the random witness must be short (for binding) yet mask a short witness statistically, i.e. a
smudging/flooding factor on the norm bound B (or rejection sampling), which inflates κ.
**Unpriced — named as the follow-up obligation (§7), not assumed cheap.**

**Against our recorded number:** `speedup-ledger.md` line 20: **VEIL ZK wrapper, 3% prover
overhead for the ZK property, eprint 2026/683** — hash-stack ZK is already nearly free by
masking techniques. So NovaBlindFold is *not a class gap in ZK cost*: both stacks land at
"ZK ≈ free"; theirs by homomorphic masking of a logarithmic verifier circuit, ours by VEIL-class
masking. The genuinely transferable *idea* is architectural: **make ZK an operation on the
verifier-check object, sized by the verifier, not the witness** — in our accumulation language,
mask at the accumulator (the `ConstrainedMask` / seam-hiding coexistence point in `AccRbrBcs` at
t = d = 2 is the analogous object already in the tree).

---

## 5. Q5 — the switchboard, precisely (reference account for the sibling decompilation lane)

**Mechanism** (Construction 3, Fig. 1): block-diagonal stitching of ℓ R1CS circuits into
A*,B*,C* with m = Σmᵢ + 1 + ℓ(1+|x|) rows, n = 1 + |x| + Σnᵢ columns. Each block's **first
column z[sᵢ] is its switch, doubling as the block-local constant-1 wire**. Three added
constraint families, one row each in A*,B*,C*:
1. single-switch: Σᵢ z[sᵢ] = 1;
2. binarity: z[sᵢ]·(1−z[sᵢ]) = 0;
3. input consistency: local input copy = switch × global input, per block, per input coordinate.
   ⚠ *As printed* (p. 23) the formula reads `z[j] = z[sᵢ]·z[sᵢ+j]`, which for an inactive block
   would zero the GLOBAL input — the worked example witness `[1, x, 0, s₂, x, w, 0…0]` and the
   Lemma 3 proof show the intended direction is `z[sᵢ+j] = z[sᵢ]·z[j]`. A printed-formula bug;
   semantics unambiguous from the proof. The sibling lane should implement the proof's version.

**Soundness argument** (Lemma 3, App B.2) and *why turned-off constraints stay sound*: the
sum + binarity rows force **exactly one** active block k; input consistency forces its local
input = x; its rows then bind normally, and ω parses out as a Ck-witness. Every inactive block's
variables can be (and by input-consistency partly must be) all zeros, and **all its rows are
satisfied by zero because they are homogeneous in block-local variables**: a block row's support
lies entirely within its own column span, and the block has *no access to the global constant-1
column* — its only "1" is its switch, which is 0 when off. "Off" is sound because an off block
asserts nothing and the IVC statement claims nothing for it.

**What prevents a prover from turning off a constraint that should bind — three interlocking
refusals:** (i) granularity — you can only power down a whole block, never a row; the single live
block's constraints all bind because its constant wire is real; (ii) **which** block must be live
is itself in-circuit: Theorem 3 requires each Cⱼ to *embed φ and check that φ selects j*, so
activating the wrong instruction is unsatisfiable, not merely unattested; (iii) zero or two live
blocks violate rows 1–2. Knowledge soundness then composes Nova's extractor with Lemma 3 per step.

⚑ **The Lean-statable invariant the construction silently relies on** — and the one worth more
than the construction to the decompilation lane: **block-support discipline.** A subcircuit row
that touches ANY global column (the constant 1, or x directly instead of its switched local copy)
is a constraint that *stays live when its block is off* — the exact widened-gadget wound
`widened_relation_refuses_embedding` exists to refuse. Lemma 3 is true *of circuits satisfying
the support discipline*; a compiler emitting switchboards must enforce that discipline
structurally (a support-check per row), not by convention. That is the theorem to state: support
discipline ⇒ (C* satisfiable at x ⟺ ∃! k, Ck satisfiable at x).

**Pay-per-use, and its substrate dependence:** witness sparsity per step is
n_active + 1 + ℓ(1+|x|); the prover dividend requires **committing zeros to be free** — true of
MSM/Pedersen (their observation), **true of Ajtai/linear commitments** (A·Y over a sparse Y is a
sum over nonzero columns — Neo's pay-per-bit is the same fact one level down), **false of
Merkle/FRI** (LDE + hashing pay full width regardless). Nova's cross-term is handled by their
`T = (Az₁∘Bz₂)+(Az₂∘Bz₁)−u₁Cz₂−Cz₁` sparsity analysis + cached `Cz₁ ← Cz₁ + r·Cz₂` — pure
linearity, transfers to any homomorphic commitment. **So the switchboard rides the PQ-Vega path
(§1c) intact, and does not ride the deployed Merkle stack at all.**

**Their measured effect, conditions named `[READ Table 1]`:** proto-EVM (100 of 141 opcodes,
SHA3 replaced by a cheaper custom hash, laptop i9, best batch size per row): constraint system
3,640K (Spice memory) → **115–116K (Nebula memory) = the ~31× "30×"**; ERC-20 (635 steps) proving
1,300 s → **5 s = the 260×** from adding the switchboard, 2,400 → 5 = 480× from both vs
Spice+switchboard; baseline without either OOMs. The 30× is the *memory* technique; the 260× is
the *switchboard* (pay-per-use commitments at equal constraint count) — the two headline numbers
belong to different mechanisms.

---

## 6. Q6 — surpass axes, honest

| axis | them | us | verdict, with the why |
|---|---|---|---|
| **PQ** | ✗ — Vega: P-256/T-256 + Hyrax (DL); Nebula/Nova: Pedersen + curve cycles | ✓ — hash-based deployed; dual-mode = MSIS | **We win on assumption.** Their entire seam dividend (§1) and ZK trick (§4) sit on homomorphisms a quantum adversary deletes. |
| **Formal content** | **Zero.** Corpus: both papers grep-clean for lean/coq/mechaniz/formally-verified (full-text, this session). Instrument: GitHub tree of `microsoft/Spartan2` (= **vega-prover**) fetched this session — no proof files of any kind, a Python "reference implementation… optimized for clarity"; microsoft/Nova is the same org's Rust. Their proofs are paper proofs; Nebula's Lemma 3 is half a page. | The position: machine-checked RBR accumulation at the deployed alphabet, a **refutation of a published composition theorem** + its repaired proof, IsEmpty teeth, axiom audits | **We win, and it is the whole position.** Their formalism cannot state a concrete depth bound at all (§2). |
| **Transparency** | ✓ both (Vega's pitch vs Crescent's Groth16) | ✓ | Tie — say so plainly. |
| **ZK cost** | Succinct NovaBlindFold: overhead ∝ few-hundred-constraint verifier circuit; elegant | VEIL-class **~3%** prover overhead recorded (2026/683) | **Parity by different mechanisms.** Theirs is another DL dividend in its current form; transfers to our lattice side only with an unpriced hiding-mask tax (§4). |
| **Verifier cost / recursion seam** | Nova fold ≈10⁴ gates; NeutronNova −10–13%; Vega verify **23 ms / 108 kB** (1920-B MSO, 16 vCPU Azure F16as v7) | wrap = 38,168 perms, 28.97M cells; counts not clocks — no honest clock comparison exists | **They win today, by ~10³ at the seam, and the why is the assumption** (commitments that add) **plus one idea** (fold now, verify once at the end). §1c: a PQ analog keeps ~10²–10³ of that gap at 4–50× their fold cost. |
| **Memory** | 4 constraints/op + rc + amortized scans; sequential-consistency theorem with both directions proved (on paper); conditions: ≥2¹⁵ ops to amortize, no `free`, flat address space | `TwistContinuity`: richer typed disciplines (ROM/RAM/appendOnly), honest-direction proved, adversarial direction OPEN | **They win on mechanism maturity; the mechanism is assumption-free and is our missing keystone** (§3). Adopting Lemma 2 as the Lean target converts their win into ours. |
| **Performance, conditions named** | 30× constraints (memory), 260× ERC-20 (switchboard), 92 ms mDL prove — each under the conditions in §5/§1a | counts: K=26.9, ×2.011 packing landed, etc. | **They win on measured latency for their workloads.** Engineering + assumption. We do not clock-race; the surpass path is §1c + §3, not benchmark envy. |

---

## 7. What to do — the transfer list, ranked

1. **⚑ Formalize Lemma 2 ↔ `TwistContinuity`** (finite combinatorics, no crypto): multiset
   equality `IS ∪ WS = RS ∪ FS` + timestamp discipline ⟺ the inductive threading relation —
   then the fingerprint direction is LogUp machinery + `uniformProb` Schwartz–Zippel, and the
   commit-then-γ schedule is already `AcceptedLogupRun`'s. Closes the named residual's semantic
   half; extends their statement with `free`/realloc, which they do not cover. Highest value per
   effort in this whole read.
2. **State `AccRbrFold`**: the fold-shaped accumulation instance over an additive root type
   (the dual-mode linear commitment) — the object §2 shows is untypeable at the BCS alphabet and
   the PQ-Vega path needs. The `AccRbrBcsShifted` lagged-root residual is the round bound it
   will inherit; solving it there pays twice.
3. **Price the lattice hiding mask** for a PQ NovaBlindFold (smudging factor on B → κ; or
   rejection sampling) — the one unpriced cell in §1c/§4.
4. **Block-support discipline lemma** for the switchboard (sibling decompilation lane owns the
   implementation; §5 is the reference; the printed input-consistency formula bug is flagged
   there).
5. Already queued elsewhere, reinforced here: the **B.6 lattice-estimator run at BabyBear**
   (`neo-superneo-read.md`'s highest-value item) — the PQ-Vega pricing above is at q = 2⁶⁴−257;
   whether a 31-bit-native variant exists is the same open question Neo left.

## 8. Sources & instruments

- Nebula: `~/paperbin/nebula-folding-machine-executions.pdf` — full text read (§1–§6, App A–C);
  quotes at point of use. NeutronNova: mirror `2024/1606.pdf`, extracted, verifier-cost sections.
- Vega: mirror `~/dev/gh/forks/IACR-eprint-mirror/2025/2094.pdf` — full text read (§1–§9,
  App A–C incl. the S&P meta-review).
- Ours: `docs/LEAF-VS-RECURSION.md`, `notes/ring-hash-dual-mode.md` (cost table §4, hazards §5),
  `notes/neo-superneo-read.md` (16× correction, LR calibration), `notes/speedup-ledger.md`
  (VEIL row), `minidregg/Selvage/{HeteroComposition.lean, Depth.lean}` (read in full / header +
  teeth), `Selvage.lean:57-59` (AccRbrBcs* summaries), `minidregg/Kernel/SparseAuthenticatedState.lean`
  + `Compiler/SparseAuthenticatedStateLogupBridge.lean` (read in full).
- Absence claims: "zero formal content" = grep of both extracted paper texts (this session's
  scratchpad copies) + WebFetch of the vega-prover GitHub tree (this session). Corpus and
  instrument named per the corpus-blindness rule; no literature-wide absence claimed.
- Extractions live in this session's scratchpad (`nv-nebula.txt`, `nv-vega.txt`,
  `nv-neutronnova.txt`); the paperbin/mirror PDFs are the durable copies.
