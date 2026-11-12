# LOOM — recomposing the frontier into minidregg's own proof system (v2)

*v1: 2026-08-07 architecture-level design. v2: same day, revised against full
construction-level reads of WARP (2025/753), Arc (2024/1731), Holography
Accumulation (2026/538), ZK-PCD (2026/289), and Rotem–Tessaro (2024/1724) —
appendices included. One deep-read lane (Basefold/WHIR/DeepBrake claim formats)
still out; §6 notes where it lands. v2 changes are marked ⟲.*

**Stance.** Every step below is (a) a cited theorem, (b) our obligation **[OB-n]**,
or (c) a design choice. The ledger is the deliverable. Working name **Selvage**
(weaves the blocklace's strands into one fabric); ember may rename.

## 1. The link layer — ⟲ OB-1 resolved: the composition dissolves

v1 asked whether a WARP/Arc accumulator can ingest Basefold-style claims at
successively halved lengths. Construction-level answer: **neither scheme folds
mixed lengths — and Selvage never needs it.** WARP's accumulated object
`acc.𝕩 = (rt, α, μ, β, η)` — one Merkle root, one multilinear evaluation
constraint `û(α) = μ`, one bundled circuit constraint `P̂(β, C⁻¹(u)) = η` — **is
already a constrained-codeword claim at full length** (WARP Def 5.6/5.7,
Constr. 10.4). The accumulator does not consume a PCS's outputs; it **replaces
the PCS opening at every chain link**, at per-step cost `(1+ℓ₂)·t` Merkle
openings + two sumchecks — what one opening would have cost anyway. The folding
PCS appears exactly **once**, compressing the final accumulator for the light
client (Arc's own suggestion: outsource the decider to a one-shot argument).

Link-layer facts now pinned (from the reads):
- **Any linear code works** (n a power of two); no decoder is ever needed by the
  scheme — extraction uses erasure correction only (every linear code has it,
  O(n³) generic; Õ(n) for RS). Systematic codes avoid a dec_C term.
- **Mutual correlated agreement is THE load-bearing property** (plain proximity
  gaps do not relate input agreement sets to the output's — WARP fn. 6).
  Unconditional today: every linear code at δ(C)/3 (unique regime); RS at the
  Johnson radius via 2025/2051 + 2025/2110. ⟲ **The Nov 2025 results upgrade
  WARP-over-RS at Johnson from conjectured to unconditional — an observation no
  paper states; Selvage's parameter section should state and use it.** [OB-6′]
- In-domain queries re-read as boolean multilinear claims make batching
  linear-time; imported claims at non-boolean points cost O(n) each — keep them
  O(1) per step (design rule for the receipt encoding).
- Arc's per-instance *degree* heterogeneity (geometric degree correction in
  Combine) means rates fold natively at one domain — the accommodation we keep
  in pocket for heterogeneous receipt sizes.
- Accumulator inputs in Selvage are always chain-internal, so Arc's first OOD
  binding round is skippable (Arc Rem. 7.15) — cheaper links, and the design
  should never accept externally-supplied accumulators without re-binding.
- **The strict/relaxed (promise) relation split is the formal interface for
  "what a chain link certifies"** (honest decider checks exact codeword
  membership; δ-slack lives only in extraction). Selvage's Lean statements fix
  this interface on day one. [OB-3 restated below]

## 2. The transcript layer — ⟲ corrected: RBR + BCS, no R–T in front

v1 cited Rotem–Tessaro (2024/1724) as the extraction reference for the sumcheck
front. **Withdrawn on concrete pricing**: both R–T transforms are controlled by
the special-soundness tree size N = Π nᵢ = (d+1)^{log n}; for n = 2²⁰, d = 3
that is N ≈ 2⁴⁰, needing t ≈ λ·N committed transcript trees (transform 2) or
c^s·N ≥ 2¹⁵⁰ prover work (transform 1, whose round cap is Θ(log λ/log log λ) —
single digits). R–T exists to rescue protocols whose only handle is special
soundness; **where round-by-round knowledge soundness holds, Fiat–Shamir of RBR
in the ROM already yields straightline extraction from a single transcript**
(the CY24/BMNW25 route; what WARP and holography both use). Selvage's law:

> **Every component enters the stack with an RBR knowledge-soundness proof;
> the transcript layer is one BCS/FS compilation of the whole protocol; R–T is
> reserved for a hypothetical future constant-round non-RBR component** (where
> its Merkle-instantiated transform 2 also uniquely offers QROM soundness with
> only polynomial loss — the one thing to remember it for).

The extraction skeleton for the apex is WARP's: relaxed RBR knowledge
(backwards extraction — each round extractor consumes the *next* round's
witness), erasure correction only, and loss-free depth composition
`ε_sr ≤ (t+k)·ε_rbr` proved by a union bound (WARP Thm B.4). This is exactly
the proof shape mechanization likes. [OB-2 restated below]

## 3. ⟲ The structure layer — adopt the holography split (2026/538)

Verdict from the full read: **genuinely hash-compatible.** Lincheck-family
SNARKs terminate in two check kinds: witness-dependent evaluations and
*holographic* checks (evaluations of public structure polynomials — dominating
recursive cost). Holography accumulation batches the structure claims to a
fresh point by **commitment-free sumcheck** (Π_GBF2: for R1CS, 7ν + 3(K+1)
field elements, zero cryptographic operations), RBR-proved, straightline after
FS. It is *complementary* to the WARP-shape witness accumulator, and it makes
the prover **stateless on the structure side** while removing per-step
structure-polynomial costs.

Selvage adopts the split: **witness claims → WARP-shape accumulation; structure
claims → GBF-style commitment-free sumcheck batching.** Hash-based carve-out,
accepted: no homomorphic decider — the final decide pays the merged structure
evaluations directly (or one closing argument; the final compression step
absorbs it). [OB-7] Our receipts' structure side is unusually favorable: the
body descriptors are *derived* from the fold-algebra IR, so the "circuit
structure" being holographically evaluated is one uniform family, not per-app
matrices — the ℓ·t_M term stays small by construction. **[OB-3′]**: state the
receipt/seam encoding so that Q-chain seam claims land in the GBF (public,
commitment-free) side wherever possible, and in the witness accumulator only
where they must.

## 4. ⟲ The disclosure layer — OB-4 is a contribution slot, confirmed

From the reads: **neither WARP nor Arc has any ZK** (salt-zero Merkle, t
codeword symbols leaked per step, no sketch); 2026/289's concrete zk machinery
is Pedersen-homomorphic with rewinding extraction (4m-transcript trees,
expected-PPT) — disqualified twice over for our stack. **ZK for hash-based
straightline accumulation does not exist. That is Selvage's open problem to
solve.** What ports from 2026/289:
- the **architecture** (their Thm 1, fully generic): split compliance from
  accumulation-verification; zk confines to a small compliance proof plus zk of
  the accumulation scheme in the strengthened sense (simulate accumulator AND
  accumulation proof) — killing the O(2^d) masking blowup;
- two ideas to re-prove RBR-style on our substrate: (a) fold in one uniformly
  random satisfying pair to randomize the output accumulator (cheap here — the
  folded word is recommitted every step anyway); (b) CFS17/XZZ+19 zk-sumcheck
  masking with the KS24 point-update to keep claim-state constant.
The genuinely new work: **hiding for the spot-check opening leakage** (masked
openings / zk-code machinery) with a straightline RBR proof. Dial default
remains off at v0; the research lane runs beside deployment, not in front.

## 5. Small fields, parameters — ⟲ and the staging flip

**v0 is WHIR-shaped-at-unique-decoding, not Basefold.** The survey's original
staging ("Basefold first, WHIR later") is withdrawn: Basefold's knowledge
soundness is forking-based and its soundness plain-not-RBR (§6) — ineligible
under the straightline law — while WHIR at UD parameters is unconditional
end-to-end (CA ⇒ mutual CA free, Lemma 4.10/Cor. 4.11) *with* RBR knowledge
soundness. The parameter ladder is now regime-tagged on one architecture:
**UD (unconditional, v0) → Johnson (unconditional for RS since 2025/2051 +
2025/2110 — the fold rule at √ρ needs no conjecture) → beyond-Johnson (pull
eprint 2026/1432, "MCA beyond the Johnson radius," before pricing)**. Each
rung only changes δ, t, and the ledger's regime tag.

Witness data over the deployed base field; challenges/accumulator sampling over
the extension (WHIR's OOD errors already demand the cubic/quadratic extension
at Goldilocks). WARP App. D transfers the soundness analysis exactly
(|Λ(C_F,δ)| = |Λ(C_𝔹^e,δ)|) but **loses prover linearity by O(λ) — a stated
open problem** and a contribution slot [OB-8]. Field-size inequalities (WARP
Eq. 12–13; Arc Thm 6.2) enter the repo as checked constants. t = λ/(−log(1−δ))
openings per input oracle is the whole verifier story.

## 6. ⟲ The claim interface, confirmed (third lane landed)

**The accumulated object is a multi-constrained CRS claim over one fixed code,
frozen at the outermost level — descent is the decider's job.** WHIR's own
machinery proves the closure Selvage needs: CRS-claim × CRS-claim → CRS-claim
under γ-folding (same-word constraints: Constr. 5.5, RBR error (t−1)ℓ/|F|;
cross-word: Constr. 7.4 via mutual CA, err★ + (s−1)ℓ/|F|), with the proximity
test — all queries, all Merkle paths — deferred entirely to the decider, which
runs ONE WHIR descent ending in a transparent constant-size f̂_M. This is the
same shape as WARP's `(rt, α, μ, β, η)` (convergent from two papers). The four
carried data per link: **word commitment** (one root; all links share the
outermost code — the alignment law, since rate-shifting breaks cross-depth
folding), **constraint channel** (points + targets, γ-linear in both), the
**proximity ledger** (δ, its regime tag, and the additive RBR error budget —
a scalar the accumulator carries), and **uniqueness pins** (one OOD constraint
per word before its first fold beyond unique decoding; a pin is itself a CRS
constraint and folds along).

Design rules banked from the reads:
- **σ before γ** (DeepBrake's message-order lesson): fix every link's claimed
  targets before sampling the fold challenge — then the fold challenge does
  double duty and no separate evaluation-binding obligation accrues.
- **Basefold's native claims are NOT accumulable** (per-level code chain,
  coupled query paths) — and its extractor is *predicate-forking* (2^d
  reruns) with plain-not-RBR soundness: excluded from the stack by the
  straightline law, kept as the fold=bind invariant's origin.
- The BrakeWHIR **virtual-oracle trick** (outer authenticated columns feed the
  inner PCS's initial oracle on a shared query set — no recommitment of folds)
  is reusable wherever a fold of committed words must itself be opened.
- Concrete decider costs at λ=128 (Goldilocks³, (24,½)): 621 KiB / 4.8 ms /
  10k hashes at UD, 299 KiB / 2.5 ms at Johnson — the one-time price the
  light client pays after the accumulator.

## 7. The obligation ledger (v2)

| id | obligation | status / risk | first move |
|---|---|---|---|
| OB-1 | fold ∘ accumulate mixed-length compatibility | ⟲ **RESOLVED — dissolved.** Accumulator replaces the PCS at links; folding PCS only at final compression | write the link-layer relation in Lean against WARP Constr. 10.4's shape |
| OB-2 | whole-stack straightline KS apex | ⟲ **depth-composition (Thm B.4) TOWER PROVED** (`Selvage/Depth.lean`): backwards extractor (Constr. B.5), Claim B.6 chain-descent, the fresh-slot bound, and a from-scratch `uniformProb` union-bound toolkit — all no-sorry. Two findings: (a) the as-first-stated `OB2_depth_composition` is **machine-checked FALSE** (`OB2_depth_composition_false` — the `Z=∅` sign corner: a vacuous empty-`Z` hypothesis admits `εrbr:=-1`; specialization-7's "arbitrary uniform bound" opened it); (b) the repair `OB2_depth_composition_nonneg` (one added `0 ≤ εrbr` guard, free for nonempty `Z`) is proved modulo **one named seam [OB-2a]**. The whole-stack apex (3 arrows: sumcheck → link accumulation → final compression) still sits above this depth lemma. | close [OB-2a]; then compose the 3 arrows onto the repaired depth lemma |
| OB-2a | the `t` game-move slots of the union bound: `Pr[HitBad j] ≤ εrbr δ` | ⟲ **named seam under OB-2**, precisely diagnosed (not hand-waved): bounding an arbitrary game move's slot needs a lazy-`rnd` resolver over *every* salted `(stmt, prefix)` pair — the eager-total-function `rnd` gives it free, the lazy rendering (specialization 5) does not; fixing all coins but `c_j` does not hold `srOut` fixed. Trace-prefix scaffolding banked (`srTrace_take_agree`: move `j` depends on `c_{<j}` alone). | build the general lazy-rnd resolver; its uniformity closes the game-slot bound |
| OB-3 | seam/receipt claims native to the accumulator | ⟲ refined: route seam claims to the GBF (public) side where possible [OB-3′]; strict/relaxed promise interface fixed day-one | prototype Q/seam encoding against `(rt,α,μ,β,η)` + GBF claim shapes |
| OB-4 | ZK accumulation, hash-based, straightline | ⟲ **confirmed open in the literature — contribution slot.** Architecture ported (2026/289 Thm 1); opening-leakage hiding is the new mathematics | after OB-2 statements; design masked-opening experiment |
| OB-5 | stateless accumulator variant | ⟲ subsumed: holography split adopted for the structure side (§3); witness side stays WARP-stateful (acceptable: one node, not distributed provers) | — |
| OB-6 | unique-decoding mutual-CA realizer (v0 floor) | low; unconditional for every linear code at δ(C)/3 | early — it inhabits the carrier |
| OB-6′ | ⟲ Johnson-regime WARP-over-RS upgrade (2025/2051+2110 applied to WARP's conjectured-MCA remark) | medium — `JohnsonMcaBridge` now pins 2110's exact reduced-rate constants and Selvage interface; the GS/BCIKS/Hensel algebraic core remains to formalize | `Selvage/JohnsonMcaBridge.lean` |
| OB-7 | ⟲ GBF structure-claim batching integrated with derived descriptors | medium-low | after the IR fold-algebra lands |
| OB-8 | ⟲ small-field accumulation without the O(λ) linearity loss (WARP App. D's open problem) | open research — second contribution slot | after v0 ships at extension-field sampling |

Statement-first discipline throughout: every OB enters the Lean tree as a
`Prop` with ATLAS keystone fields (satisfiable/teeth/premise-inhabitation)
before proof work starts.

## 8. Next actions

1. Third lane lands → finalize §5/§6, close the claim-format question.
2. Scaffold the Lean project: `Theory/` (import-boundary-enforced) + `Selvage/`
   skeletons; state OB-2 and OB-6 statement-first.
3. Field + sponge decisions (survey §7) bind at OB-6's instantiation.
4. The two contribution slots (OB-4 ZK, OB-8 small-field linearity) get
   research notes of their own once v0 statements are green.
