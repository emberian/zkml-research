# What Selvage is, what it wants, and what it still needs

2026-08-13, written after the design phase. Supersedes the vaguer parts of
`SYSTEM.md`.

## 1. What it IS, stated narrowly

**Selvage is the compilation layer of a proof system, machine-checked** — the
part between *"an interactive protocol is round-by-round sound"* and *"a
deployed non-interactive verifier accepts only true things."* ~48K lines of
Lean in `minidregg/Selvage/`, zero `sorry`.

Concretely it holds, proved: FRI/RS proximity with **attained** error bounds
and regime interfaces that track the 2025–26 literature *including the
refutations*; correlated agreement (WHIR Lemma 4.10, domain-general — ✅
**verified at source 2026-08-13, and our version is *better than the paper's***:
the printed `min{1−δ_C/2, B}` must be `max`, Def 4.9's `1−B` must be `1−B*`,
ours is stated for an **arbitrary** generator rather than the power curve, and
our `herr_mono` supplies a monotonicity side condition the paper's proof uses
**silently**); the
**RBR→Fiat–Shamir compiler theorem** over an *inhabited* lazy-sampling oracle;
**BCS-style transform soundness at the deployed alphabet**; **state-restoration
soundness**; **accumulation depth composition** — including a machine-checked
proof that the published theorem is **false at a corner**, with the repair;
**sponge indifferentiability**; the **commit-then-audit theorem**; a
**two-regime security calculator with the regime in the type**; and the LogUp*
pushforward kernel.

**Why that set is unusual**: every other effort has legs *or* composition, not
both. ArkLib's composition theorems are `sorry`. Hirai has base-protocol FRI
only. StarkWare stops at the AIR. Isabelle/STARK has no proximity leg.

**And the honest half**: Selvage is **theory about an object that does not run
yet.** The engine is a 433-line degree-1 sumcheck. There is no multilinear
commitment. The accumulation architecture it proves is not what any deployed
prover here runs.

## 2. The idea that unifies the three workloads

The design phase produced one sentence that reorganizes everything:

> **An AIR commits the INTERIOR of a relation; a sumcheck commits its
> BOUNDARY.**

⚠ **TERMINOLOGY AND PRIOR ART (2026-08-13):** this is standard and named —
**`polynomial virtualization`** (Thaler, *"Sum-check Is All You Need"*, eprint
2025/2041 §5.2, whose whole thesis is this sentence), with the upper-bound
half a **published theorem from 2013** (Thaler CRYPTO'13 Thm 3) and a
complexity lineage (Kalai–Raz → RRR16 → Ron-Zewi–Rothblum) whose Remark 1.2
restates it exactly: *an AIR commits the Cook–Levin witness; a virtualizing
sumcheck commits the original NP witness.* **Retire "boundary"** — it collides
with *border rank*. Say **"shallow and wide"** for the qualifying class, and
**materialize-vs-virtualize** for the fork (not AIR-vs-sumcheck: R1CS/Plonkish/
AIR are interconvertible). ⚠ **The monotone reading is wrong** — the same
survey says *"not zero, there's a sweet spot."* **What is ours: the measured
EXCHANGE RATE** (one committed felt ≈ 3,120 field mults at lb=4 / 12,331 at
lb=6, vs ~40 to virtualize one per layer — 78×–308×), which locates that sweet
spot as a threshold rule; **and the lower-bound half, which does not exist
anywhere.**

The interior of a bilinear form is n³; its boundary is n². That is 5,461× at
n=4096, and it is Θ(n). It generalizes:

- **zkML**: a matmul's boundary is (A, B, C); its interior is every
  multiply-accumulate. ⚠ And Thaler's famous 0.18–0.33% overhead is the
  **B≈n** case — overhead is `1/B + 1/n`, so **at B=1 it is 100.02%, and
  autoregressive decode is B=1.**
- **vFHE**: `fold_add` is a **linear** map, so MLE linearity gives
  `ĉ_out = Σaₖĉₖ` as polynomials — **one common-point opening, zero sumcheck
  rounds, zero carries, zero range checks.** Ratio = B — ⚠ **prover-side
  only**; the verifier moves the opposite way to O(B). ⚠ And the deployed batch
  is **B=4** (ratio **4.2×**); 690–715× prices B=512, a shape the node does not
  fold (`notes/fold-as-opening.md` §0/§4). We
  have the proof; nobody has built it.
- **Kernel turns**: a typed semantic transition's boundary is the *state
  delta*; its interior is an execution trace. **The kernel's statements are
  boundary statements by construction** — which is why they are cheap, and it
  is the same fact as "we don't emulate a VM."

**So the thesis is: prove boundaries, not interiors — and choose statements
whose boundaries are small.** Everything else (field, hash, PCS) is a constant
factor on top of that choice.

## 3. Ambitions, honestly scoped

1. **A proof system whose compilation layer is machine-checked end to end.**
   Nobody has this. We hold most of the pieces and no PCS binding.
2. **Deployable speed via statement choice, not prover heroics.** Measured
   levers: sampling (~20×), boundary-vs-interior (Θ(n)), read-only/write-once
   memory (~80×), accumulate-vs-verify-per-link. The prover-level literature
   trades in 2–4× on terms that are 2–17% of the total.
3. **Three workloads on one substrate** — kernel turns, ML inference, FHE ops
   — because they are all boundary statements over committed data.
4. **Everything open.** Not a moat; the point is that more correct artifacts
   exist in the world.

## 4. Open questions, ranked by what they block

**Blocking the architecture:**
1. ⚑ **Hash-bound or arithmetic-bound?** Two lanes disagree (derived 94% hash;
   measured 19–40%). Decides whether the field/hash migration is worth ~3.4×
   or much less. **One profiling run.**
2. ⚑ **The multilinear PCS seam.** Selvage is univariate RS/FRI throughout.
   ⚠ **CORRECTED 2026-08-13** (`notes/multilinear-pcs-landscape.md`): the
   *positional* framing was **wrong, and correcting it shrinks the job**.
   `openAt : … → (Fin m → F) → Op` is the **KZG/homomorphic** shape; **no
   hash-based multilinear PCS has it.** In BaseFold, WHIR, Ligerito and every
   Ligero/Brakedown descendant the commitment **is** a Merkle vector commitment
   to a codeword — exactly our `OpeningScheme`, reusable **unchanged** (verified
   verbatim: ZCF23 p.20, Haböck p.8, WHIR Construction 5.1) — and the opening is
   an **interactive reduction** compiled by the BCS transform we already hold.
   The deliverable is therefore one object: an `RbrKnowledgeSoundness` instance
   for the braided protocol, after which `Depth.lean:1982` + `FiatShamir` +
   `AccRbrBcs` carry it to a non-interactive verifier **for free**.
   **Recommendation: BaseFold @ RS in our own unconditional `(1−ρ)/3` band**
   (`ProximityGapUD.foldDistancePreserving_UD` — which is *also* ZCF23's own
   published regime), then WHIR-UD. Five new items, no conjecture, **no new
   proximity result**. Not a campaign. See §11 of the landscape note.
3. ⚑ **Value-ring polymorphism.** The base→extension boundary is a measured
   ~3× cliff. ⚠ **"Must be designed in from day one" is NOT supported** —
   Hierarchy Builder exists to evolve algebraic hierarchies *"without breaking
   user code"* and MathComp completed that retrofit. **True narrower
   statement: cheap iff constraints consume the ring through an interface,
   ruinous iff `Felt` leaks everywhere — a check, not a deadline.** And the
   semiring-provenance literature *prescribes the shape*: transport commutes
   with a ring change **iff the map is a homomorphism**, and semantics in any
   K **factors through the free object** — so the emitted AIR should be a
   syntactic expression over ℤ-coefficients with each ring a valuation, not a
   `BabyBear → BabyBear` function (Kovach–Kjolstad, PLDI'23: exactly this,
   proved in Lean 4, ~540 lines).
4. **Degree.** The engine is degree-1; GKR fraction trees and zkML matmul both
   want degree 3. The protocol layer is already degree-generic and
   `AirSumcheckQuadratic` already did degree 2 — so this is a port, plus
   multilinear Schwartz–Zippel (~100 lines).
5. **GKR/layered circuits exist nowhere in our Lean.**

**Blocking specific pillars:**
6. **H1** — does the 61-bit joint-representation point survive a 2.4-bit
   margin? H2 collapsed *into* H1, so this is now the whole question.
7. ⚑ **Cross-limb binding — EXHIBITED 2026-08-14, and it was TWO holes.**
   `notes/cross-limb-binding.md`; `breadstuffs` `5b653ba5d`. **A** = provenance
   (`∀i∃source` vs `∃source∀i`; the accepted output is a value no honest pair
   produces). **B** = expressibility (`⌊t·x/Q⌉` reads the CRT reconstruction, so
   there is no per-limb equation to bind). ⚑ The first-named fix, a CRT-consistency
   relation, is a **tautology** — the CRT map is a bijection. **ct×pt narrower than
   recorded**: B absent, A alive at `K^L` not `(K²)^L`, and a singleton pool closes
   it. **The fix is a layout choice and costs +0 felts / +0 perms**; the bill is the
   2-felt BabyBear bridge it forces. Remaining: no closure for B, and no ct×ct
   arithmetization exists to fix — single-prime (gated on H1) dissolves both.
8. **ε_chk instantiation** — the audit theorem's checker is abstract. Tier 2
   and 3 soundness are parameters until it is instantiated, with two named
   transport obligations.
9. **ε_beacon** — we hold the grinding *mechanism*, not a beacon model. The
   G=1 threshold VUF is an assembly of parts we own (`pqvrf` + fhegg's
   threshold ceremonies) that nobody has checked.
10. **Router binding must be ZK** — expert selections leak 91% of tokens, and
    our spec assumed a public opening.
11. **τ=2 for the ring hash** — one named experiment (the Beyne–Verbauwhede
    artifact at our parameters).
12. Named seams: `[ACC-extract]`, `[LOGUP-ADDRESS-LINK]`, `TwistContinuity`.

## 5. The innovations we are actually in want of

Not "papers to read" — **things that do not exist and that we are positioned to
build:**

1. **A multilinear PCS with a machine-checked soundness story over a small
   prime field with a hash.** BaseFold/WHIR exist as constructions; the Lean
   does not, anywhere. **Our FRI/proximity cone is the hard half of it.**
2. **Jagged PCS, in Lean.** One commitment for arbitrarily many tables of
   different heights, no extra oracles, verifier cost depending only on total
   log-area — which kills the recursion-circuit explosion. It reduces to a
   degree-2 sumcheck (which our engine already proves) plus a **width-4,
   two-bit-state read-once branching program** — decidable per layer, with an
   induction on top. ⚠ **QUALIFIED 2026-08-13**: the machinery description is
   **correct in every clause** (Lemma 2.3 degree-2; Claim 3.2.2 *"width-4"* with
   a literal two-bit state; Claim 4.2.1 per layer; Lemma 4.2's reverse
   induction), and it *is* the most Lean-tractable object in the corpus — **but
   that is because it has NO cryptographic content.** Instrument: grep over
   2025/917 for `extract|binding|knowledge.sound|round-by-round|Fiat` → **0 hits
   each**. It is an information-theoretic claim transformer `p̂(z)=v ⟼ q̂(z′)=v′`
   whose output claim needs a dense multilinear PCS underneath — batch-BaseFold,
   per its own §7 *and* Rothblum's Simons talk. **Proved first and alone it is a
   green theorem that commits to nothing.** Do it *after* the base PCS, and
   formalize Lemma 5.1's `(2m+1)/|𝔽|`, not Theorem 1.5's `2m/|𝔽|`.
3. **A boundary-statement compiler.** ⚠ **CONTRADICTED 2026-08-13: it
   exists.** Distiller (eprint 2022/1557, S&P 2023) compiles *"not the
   original computation but an abstracted specification of it,"* provably
   safely, at 1.3–50× — via a refinement chain over transition systems, with
   the mechanization explicitly a free choice. **What survives as ours: the
   COST THEORY (which abstraction is cheapest and why) and the Lean
   instantiation.** It has zero follow-ups in 25,765 eprint texts. And the
   near-term move is smaller than a compiler: **Dumas–Kaltofen–Villard's
   certificate catalogue (rank, determinant, char/min poly, Frobenius, PSD)
   already meets our boundary criterion — they named it "essentially optimal"
   in 2014 — and is compiled with Fiat–Shamir as a HEURISTIC. Selvage holds
   exactly the RBR→FS leg they lack. Joining them is a port.**
4. **Value-ring-polymorphic constraint authoring in Lean**, with the *emitted*
   object polymorphic too. Every fast system encodes this in its type system;
   nobody has done it in a proof-carrying authoring language.
5. **A proof-native weight commitment**, with a documented byte→field encoding
   for MX formats — where the natural encoding is *not* "reinterpret the
   bytes," because E2M1 values are multiples of ½ and a k=32 block dot is an
   exact ≤13-bit integer.
6. **The ring-native RO-like hash at τ=2.** Genuinely open (2026/1127 poses
   it), and now with a real cost case: **52% → 4% of the circuit.** The
   enabling observation — that the needed slot-mixers are automorphisms
   already present as native constraint terms — is ours.
7. **`fold_add` as a single opening.** We have the proof; the build is
   unclaimed, and it is the vFHE M1 thesis in its cheapest form.
8. **Sampling × ZK router binding.** The audit game and the MoE spec both
   exist; their composition is unexamined, and the honest-on-sampled attack
   lands exactly on the corrupt-round predicate.

## 6. What Selvage is NOT

Not a zkVM. Not a faster FRI. Not a moat. **Not, yet, a running system** — and
the honest one-line status is: *the compilation layer is proved, the engine is
one rung up from a toy, and the commitment seam is unbuilt.* The next window's
job is to move the engine and the seam, not to prove more things about them.
