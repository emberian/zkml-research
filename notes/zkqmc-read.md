# zkQMC (eprint 2022/1007) — read in full, composed against the audit game

2026-09-04. Deep-read lane. Source: `/Users/ember/dev/gh/forks/IACR-eprint-mirror/2022/1007.pdf`
(a copy also sits in `~/paperbin/zkqmc-probabilistic-computation-quasirandomness-2022-1007.pdf`,
collected in-campaign and never read). This is the first recorded content on the
item that `forcodex/01b-STEERS-RECOVERED.md` §16 and `swarm/OPEN-QUEUE.md` §E carry
by name only ("the mine's genuine surprise, a direct answer to 'prove the sampling
was honest'"). Corpus grep before writing: `zkqmc|quasi-monte|low-discrepancy|2022/1007`
over `notes/ docs/ forcodex/ swarm/` → only the three name-only mentions above. Nothing
here was known to us beyond the title.

**Verdict up front.** The paper is real and modest: a worst-case error bound for
*integral estimation* with prover-chosen randomness, obtained by making the bound
uniform over the prover's choice. It does **not** compose with the audit game's
`ε_beacon` (it is the prover-controlled-beacon case the Lean file already refutes,
and worse: one observed audit reveals the whole schedule) and does not touch
`ε_chk`. It does not change `E[Λ] ≤ b/q`; it removes the bound. Generality label:
**trap** for the use the campaign had in mind, **real but off-axis** for what the
paper actually claims. Details in §3–§6.

---

## 0. What the paper is, structurally [READ]

- **Title/authors/venue.** "zkQMC: Zero-Knowledge Proofs For (Some) Probabilistic
  Computations Using Quasi-Randomness." Zachary DeStefano, Dani Barrack, Michael
  Dixon, Los Alamos National Laboratory (LA-UR-22-28108; funded under LANL ISTI
  project 20210529CR and NWCAL, p.12). PDF created 2022-08-05 (pdfinfo). **ePrint
  only**: dblp lists it solely as `IACR Cryptol. ePrint Arch. 2022: 1007`; no
  conference or journal version found (kagi, dblp — see §5). DeStefano has since
  moved to NYU (Walfish group; kagi hit on his NYU page).
- **Length/shape.** 18 pages, two-column. Sections: 1 Intro · 2 Background (MC,
  QMC, discrepancy, ZK/zkSNARKs) · 3 Approach · 4 Implementation · 5 Benchmarks
  (Table 1, p.11) · 6 Multi-Prover Systems · 7 Discussion · 8 Future Work · App. A
  (BPP/RP/ZPP/Las Vegas) · App. B (DSL grammar + operational semantics) · App. C
  (Interval Algorithm Correctness Proof).
- **Theorem environments.** One theorem and two corollaries, all in Appendix C
  (p.18), all about the *interval-propagation* algorithm of §6. The main claim
  ("the prover can search infinitely over sequences and will never find one that
  breaks soundness", p.6) is **prose** on top of Koksma–Hlawka [Nie92]: no
  soundness or zero-knowledge theorem, no game, no adversary, no reduction.
- **Artifact.** A libsnark/Groth16 implementation with a custom DSL and compiler
  (`Compile(f) → C_f`, `Expand(C_f, N) → C_qmc,f,N`, p.6–7), benchmarked on LANL's
  Darwin cluster. **No repository URL in the paper.** Public-artifact search in §5.

## 1. The construction, precisely [READ, page-cited]

**Problem (p.1, p.4).** A prover wants to convince a verifier, in NIZK, of the value
of something "that can be efficiently probabilistically approximated using the
Monte Carlo method" (p.4) — an integral `∫_{[0,1]^d} f(u) du` — where the
randomness is *prover-generated*. The paper's framing sentence: "the process of
designing adversarially resistant non-interactive zero-knowledge protocols
(e.g. zkSNARKs) for computations which involve prover-generated randomness and
uncertainty is not well understood, and current approaches require additional
statistical and cryptographic assumptions or machinery" (p.1).

**The failed alternatives, as the paper ranks them (p.5, "Limitations of the
Monte Carlo Method").** This taxonomy is the part most relevant to us:

1. Prover picks the points freely → "soundness is clearly violated".
2. Prover picks a seed, points come from an ideal PRNG → "soundness is again
   threatened by the ability of a malicious prover to search over seed values."
   They price it: if the prover searches `M` seeds and keeps the worst, the
   sample count to hold confidence `α` at width `ε` goes from
   `N = (Φ⁻¹((1+α)/2)·σ/ε)²` to `N = (Φ⁻¹((1+α^M)/2)·σ/ε)²` by union bound
   (as printed; [INFERRED] the exponent should read `α^{1/M}` for the count to
   *grow* with `M` — a typo in a non-load-bearing formula). This is the
   multiplicative try-count factor, the same mechanism `Selvage/LightClientGrinding.lean`
   machine-checks on the challenge oracle.
3. Seed from a random oracle → sound, but "breaking the zero-knowledge requirement
   (x₁⋯x_N becomes fully known to the verifier) and the introduction of a
   cryptographic assumption about random oracles."
4. **A randomness beacon** → "introduces both a cryptographic assumption and the
   potential for an adversarial prover to search over time to acquire a sequence
   of points which misleads the verifier." (p.5) — i.e. they name beacon grinding
   as a reason to *avoid* beacons, and never price it.

**The construction (p.2–3, p.6–7, p.9).**

- Replace the `N` i.i.d. uniform points with a **Kronecker (Weyl) sequence**
  `x_k = ({γ₁k + c₁}, …, {γ_d k + c_d})`, `k = 1..N`, with `γ_i` irrational and
  "badly approximated by the rationals" (linearly independent over ℚ; the paper
  cites [Bec94] for discrepancy) and `c_i` arbitrary (p.3). Three stated reasons
  for this family (p.3): fewer non-uniformity artefacts in high dimension than
  other constructions; **"the discrepancy is preserved when we consider these
  points on a torus … so we can effectively arbitrarily pick c₁,…,c_d without
  changing the discrepancy"**; each term costs `d` additions, multiplications and
  moduli.
- **Seed binding / secrecy split (p.6):** "we use a Kronecker sequence with
  **public irrational coefficients** γ₁,…,γ_d and **private seed variables**
  c₁,…,c_d; however, this approach generalizes to any other low-discrepancy
  sequence which preserves discrepancy when shifted. This provides the prover P
  with sufficient freedom to hide the discrete evaluations of f(x_i) from the
  verifier V." The shift `c` is the prover's private witness; the verifier never
  learns it. ZK is asserted "up to pathological cases" (p.6); no theorem.
- **What the circuit checks (p.7, p.9):** `d·N` new field elements
  `x_{1,1}…x_{d,N}`; `x₀` constrained to unsigned fixed-point in `[0,1)`; each
  `x_{i+1}` produced by a gadget `C_qmc(x_i) → x_{i+1}` computing
  `x_{i,k+1} = {γ_i + x_{i,k}}` by keeping the bottom `ℓ` fractional bits
  (p.9) — applied `N−1` times; `C_f(x_i) → r_i` evaluates `f`; the output is
  `Σ r_i / N`. So the verifier's check is: *the points are a γ-Kronecker
  sequence for SOME shift, and the average was computed correctly.* Fixed-point
  precision loss is acknowledged and set aside: "we ignore those limitations for
  now (they are properly addressed by Niederreiter [Nie92], and ultimately do not
  change the primary result)" (p.7).
- **The error statement (p.2, prose; Koksma–Hlawka):**
  `|1/N Σ f(x_i) − ∫ f| ≤ C·(log N)^d / N · Var_HK(f)`, `Var_HK` the
  Hardy–Krause variation, under Niederreiter's *conjecture* that
  `B_d (log N)^d / N` is the minimal star discrepancy (p.3, p.12 "Assuming the
  conjecture"). What the SNARK attests (p.6): an interval `I` with `∫ f ∈ I` and
  `λ_d(I) ∈ O((log N)^d / N)`. The soundness sentence (p.6): "This automatically
  satisfies the soundness requirement on the output without any additional
  computational, cryptographic, or statistical assumptions. … Unlike in the failed
  pure Monte Carlo cases, the prover can search infinitely over sequences and
  will never find one that breaks soundness. This result can be tight, so
  additional information about f is required to achieve faster convergence."
  [INFERRED] The mechanism, stated the way the paper does not: the bound is a
  *supremum over all point sets of the given discrepancy*, and shift-invariance
  makes every choice of `c` such a set, so the prover's degree of freedom is
  inside the quantifier of the bound rather than a random variable the verifier
  must trust.
- **Who bounds `Var_HK`?** The verifier needs it to know `Δ`. When `f` is
  private (particle example, p.8): "it is not possible for the verifier to
  directly compute Var_HK, it is still possible obtain a reasonable upper-bound on
  Var_HK which can be used to calculate worst-case error bounds." No procedure is
  given. This is the load-bearing side condition for §3.
- **Multi-prover composition, the one theorem (p.11, App. C p.18).** Theorem 1:
  for `I` a closed `d`-hyperbox, `f` Lipschitz on `I`, and ANY `N` points
  `X ⊂ I`: `u ∈ I ⟹ f(u) ∈ [min_i f(x_i) − Δ, max_j f(x_j) + Δ]` with
  `Δ = ½·d·(D_N(X)·λ_d(I))^{1/d}·max|∂^d f/∂v₁⋯∂v_d|`. Corollary 1: with a
  low-discrepancy set, `Δ ∈ O(d·log N / N^{1/d})`. Corollary 2: piecewise over
  finitely many Lipschitz convex regions. This is interval propagation through an
  uncertain input using the sample set as a net; note the `N^{1/d}` — the curse
  of dimension is fully present.
- **Appendix A [READ].** BPP: rephrase the acceptance function `A_x(r)` as an
  integral and use QMC to separate `≥2/3` from `≤1/3`; this works only when
  `Var_HK(A_x) < N / (6·B_d·(log N)^d)` (p.15). RP/co-RP: `< N/(2·B_d·(log N)^d)`
  (p.16). Las Vegas/ZPP: **no QMC at all** — since a Las Vegas output is always
  correct, the prover may pick `r` freely; the paper encodes a trace of length
  `< c·E[t_X(R)]` and bounds the expected number of retries by
  `N_c ≤ c/(c−1)` via Markov (p.16). That Las Vegas needs no derandomization is
  itself the tell: prover-chosen randomness is harmless exactly when the
  *statement* does not depend on which randomness was chosen.
- **Benchmarks (Table 1, p.11) [READ].** libsnark + Groth16 + PCD, Xeon E5-2698
  @2.30 GHz, 64 threads. Overhead of quasi-random vs. plain random points: time
  0.069 %–5.136 %, memory 0.024 %–1.814 % across π estimation, cluster integral,
  particle exposure at 10⁰–10³ iterations; largest run 127.8 s / 55.5 GB
  (particle exposure, 10³). "Verifier time is approx. 50 ms and is independent of
  circuit size." Pessimistic number: the QR overhead is small only because the
  baseline is a Groth16 circuit already paying for `N` copies of `C_f`; the
  Kronecker step is `d` fixed-point additions per iteration and cannot be
  otherwise.

## 2. What it is NOT

Stated by the paper [READ]:

- No average-case convergence, no confidence intervals: "the QMC method … does not
  provide a nice measure of average-case convergence" (p.3); the CLT does not
  apply to structured sequences (p.3). Hybrid QMC with a random shift has fast
  average-case convergence empirically but "heavily depends on the behavior of
  the function being integrated" (p.3).
- Curse of dimension: the bound is `(log N)^d / N` (integration) and
  `d·log N / N^{1/d}` (interval propagation); the BPP/RP embeddings need
  `Var_HK` polynomially bounded (p.15–16), and §8 names "those where Var_HK is
  exponential in d" as open (p.12).
- The verifier cannot compute `Var_HK` for private `f` (p.8); the bound is only
  as good as an externally supplied variation bound.
- Minimal discrepancy is a conjecture (p.3, p.12); star discrepancy of an
  arbitrary point set is NP-hard to compute when `N ≈ d` (p.3, [GSW09]).
- "Distribution" (several provers sharing one environment) leaks and "does not
  work in this multi-prover distributed case without additional modifications"
  (p.12).
- Fixed-point precision is ignored (p.7).

Inferred [INFERRED]:

- "Without additional cryptographic assumptions" means *beyond the NIZK's* —
  the implementation is Groth16 (knowledge assumption, trusted setup); the QMC
  layer adds none.
- No ZK proof: the claim that `c` and `f` stay hidden "up to pathological cases"
  is unargued. In particular the *interval endpoints* leak `Σ f(x_i)` exactly.
- The worst-case guarantee is over the prover's choice of **points**, for a
  **fixed** `f` of bounded variation. Nothing is said, and nothing can be said,
  when the adversary chooses `f` after seeing the points — `Var_HK` is then
  adversarial. This is the hinge for §3.
- The paper's own p.5 taxonomy contains our `ε_beacon` concern (beacon grinding
  over time) and our try-count mechanism (item 2), in a 2022 paper that meets a
  proof of computation. It does not compose them; it steps around them. This is
  a citation for `notes/audit-sampling-prior-art.md`'s "the legs exist separately"
  line, not a change to it.

## 3. Composition with the audit game

**Ground truth composed against** (`/Users/ember/dev/minidregg/Selvage/AuditSampling.lean`,
quoted) [OURS]:

```lean
def q (A : AuditParams) : ℝ := A.p * (1 - A.εchk) - A.εbind - A.εbeacon          -- l.167
def BeaconLeg (A : AuditParams) (R : Round Ω) : Prop :=
  ∀ h : List Ω, A.p - A.εbeacon ≤ uniformProb Ω (fun ω => R.fires h ω)           -- l.236
def ChkLeg (A : AuditParams) (R : Round Ω) : Prop :=
  ∀ h : List Ω, R.corrupt h = true →
    uniformProb Ω (fun ω => R.fires h ω ∧ R.chkErr h ω)
      ≤ uniformProb Ω (fun ω => R.fires h ω) * A.εchk                            -- l.244
theorem detect [Nonempty Ω] (hL : DetectionLegs A R) {h : List Ω}
    (hc : R.corrupt h = true) : A.q ≤ uniformProb Ω (fun ω => R.alarms h ω)      -- l.315
theorem sequential_bound_of_legs [Nonempty Ω] {A : AuditParams} {R : Round Ω}
    (hL : DetectionLegs A R) (hq : 0 < A.q) (n : ℕ) :
    expOver Ω n (fun h => (R.count h : ℝ)) [] ≤ 1 / A.q                          -- l.623
```

and the two residuals that decide the matter (l.1087–1099 of the file's §8): "`ε_beacon` —
`BeaconLeg` is a named hypothesis … the file does NOT derive `ε_beacon ≤ p · Pr[G ≥ 2]`
from a beacon model" and "**Fresh coins across rounds.** `expOver` averages over
INDEPENDENT uniform draws, one per round. … A beacon whose draws are correlated across
rounds is outside the sequential theorem."

**The role mismatch, stated once.** zkQMC's guarantee is: *for a fixed integrand `f` of
bounded Hardy–Krause variation, the estimate is within `Δ` of the truth for EVERY choice
of the prover's randomness `c`.* The prover's freedom sits inside the quantifier of the
bound. The audit game's guarantee is: *for EVERY adversarial choice of the corrupt
indicator (an arbitrary function of the history, chosen after every past coin), the
alarm probability over THIS round's fresh coin is `≥ q`.* The adversary's freedom is over
the integrand, and the coin must be fresh. The two quantifier orders are opposite. Under
Koksma–Hlawka the price of letting the adversary pick `f` after the points is
`Var_HK(f)`, which for an indicator that alternates with the point set is `Θ(N)` — the
bound is vacuous exactly when the adversary is adaptive. [INFERRED]

Three placements, checked:

**(A) The audit schedule as a QMC sequence with the shift held by the prover** — the
literal transport of the paper. `fires h ω := [{γ·|h| + c} < p]`, independent of `ω`.
This is expressible in `Round` today and it is the case the file already refutes.
Candidate statement (NOT proved here):

```lean
/-- A selection rule that does not read the round's coin. -/
def Round.Deterministic (R : Round Ω) : Prop := ∀ h ω ω', R.fires h ω = R.fires h ω'

/-- A deterministic schedule with at least one unaudited history is a beacon with
`ε_beacon ≥ p`, so the composed rate is non-positive. -/
theorem deterministic_schedule_q_nonpos [Nonempty Ω] {A : AuditParams} {R : Round Ω}
    (hdet : R.Deterministic) (hB : Round.BeaconLeg A R)
    (hgap : ∃ h ω, R.fires h ω = false) : A.q ≤ 0
```

Proof shape: at the gap history all coins give `fires = false` (by `hdet`), so
`uniformProb … = 0` and `BeaconLeg` reads `p − ε_beacon ≤ 0`; then
`q = p(1−ε_chk) − ε_bind − ε_beacon ≤ p − ε_beacon ≤ 0` using `εchk_nonneg`,
`εbind_nonneg`. ATLAS fields:

- *satisfiable*: `BeaconRefutation.round` (`fires _ _ := false`, l.764–766) is `Deterministic`
  with a gap at `[]`; `BeaconRefutation.honest` has `εbeacon = p = 1/2` and
  `honest_leg_holds` + `grind_honest_q_eq_zero` already exhibit the conclusion with
  equality. The statement is inhabited by an instance already in the file.
- *teeth*: `hgap` is load-bearing — the all-fire schedule (`fires _ _ := true`) is
  `Deterministic`, satisfies `BeaconLeg` at `p = 1, ε_beacon = 0`, and has
  `q = 1 − ε_chk − ε_bind`, which is positive for a good checker (audit-everything is
  fine, it is just not sampling). And `AuditWitness.round` (l.675–677) is NOT `Deterministic`
  (`fires _ ω := sel ω`), so the theorem correctly declines to fire on the instance
  where `q = 1/2` is attained.
- *premise-inhabitation*: `∃ R, R.Deterministic ∧ ∃ h ω, R.fires h ω = false` — by
  `BeaconRefutation.round`.

What this says in words: **a QMC audit schedule is a prover-controlled beacon, and the
theorem is honestly silent about it.** Nothing new is proved by adding it; its value
would be as a named refusal of the sentence "make the audit selection quasi-random so
the prover cannot grind it" — which is the sentence the campaign's lost steer was
apparently reaching for.

**(B) The schedule as a QMC sequence with the shift secret to the warden, `γ` public**
— Rinberg's "private and non-manipulable sampling" implemented with a Kronecker
sequence. Two findings:

- *Not expressible in `Round` as it stands* [OURS, by reading]: `expOver` draws a fresh
  `ω : Ω` from one fixed coin space every round. A one-time secret shift is a round-0
  draw followed by no fresh entropy; expressing it needs per-round coin spaces
  (`Ω₀ = shift space`, `Ω_t = Unit` for `t ≥ 1`) and a rewrite of `expOver`, `stopped`,
  `count`, `mart_step`. Premise-inhabitation fails at the type level, which is the
  residual "Fresh coins across rounds" saying the same thing from the other side.
- *If it were expressible it would be worse than a beacon* [DERIVED]: the adversary is
  the audited party and sees each audit fire (in every design we hold — Rinberg,
  2026/541, our own light client — the prover must open the trace on challenge). A fire
  at round `t` is the linear constraint `c ∈ [−γt, −γt + p) mod 1`, an interval of width
  `p`; `k` fires intersect to width `p^k`. An `ℓ`-bit fixed-point shift (the paper's own
  representation, p.9) is therefore pinned exactly after `k = ℓ / log₂(1/p)` fires:
  `p = 1 %`, `ℓ = 64` → `k ≈ 9.6` fires ≈ `960` rounds in expectation (the entropy-rate
  count agrees: `H(0.01) ≈ 0.0808` bit/round → `≈ 790` rounds). After that,
  `ε_beacon = p` and `q ≤ 0` for every later round. The property that makes a sequence
  low-discrepancy — rigid linear structure, no clumps — is the property that makes it
  recoverable from a handful of observations. A PRF-seeded schedule with the same
  `ℓ` is not recoverable this way (that is what PRF security says); a beacon has fresh
  entropy every round. QMC is the *most* predictable of the three by construction.

**(C) `ε_chk` — the per-sample checker.** The checker is not estimating an integral; it
is testing membership of a committed trace in a relation. Under a 2026/541-style
statistical checker (sampled positions in a Merkle trace) the positions are
Fiat–Shamir-derived after commitment and are already the checker's coins `K` in
`chkLeg_of_product` (l.1002). Replacing them with a deterministic low-discrepancy set is
`K = Unit`, and `hbound` there becomes `err h () = true → 1 ≤ ε_chk`: the adversary who
knows the positions corrupts elsewhere and `ε_chk = 1`. Keeping them FS-derived, QMC has
nothing to add — Koksma–Hlawka applied to the corrupt-position indicator has an
adversarial `Var_HK`. Does not compose. [INFERRED]

**Where the paper's theorem could honestly touch the vocabulary** [INFERRED]: only a
*numerical estimate with a fixed, non-adversarial integrand and a verifier-known
variation bound*. None exists on the soundness path; on the completeness side the
false-positive rate `α_fp` over honest traces is one, and a QMC estimate of it would
carry a worst-case rather than a confidence bound. Nothing we have asked for.

## 4. Composition with zkML: does a QMC sequence change `E[Λ] ≤ b/q`? [DERIVED]

The bound is `leakage_bound` (l.611): hypotheses `0 < q`, `0 ≤ b`, and
`hdet : ∀ h, ¬stopped h → corrupt h → q ≤ Pr[alarm | h]`; conclusion
`E[b · C_{n∧τ}] ≤ b/q` at every horizon `n`. "Sampling randomness" has two readings in an
inference/training audit; both are derived.

**(i) The audit-selection randomness** (which rounds get checked). Replace the beacon by a
density-`p` QMC schedule.

- Public or prover-held shift: the rule `corrupt h := ¬sched(|h|)` is a legal
  `List Ω → Bool`. At every corrupt history `Pr[alarm | h] ≤ Pr[fire | h] = 0`, so `hdet`
  forces `q ≤ 0`, contradicting `hq`. The premise is uninhabitable: the bound is not
  loosened, it is *removed*. Realized leakage is `b` per unaudited round with no alarm
  ever: `E[Λ_n] = b·(1−p)·n`, unbounded in `n`. With the campaign's numbers
  (`notes/audit-sampling-prior-art.md`: `p = 1 %`, `b ≈ 8.7 KB` per 4096-token response)
  the beacon gives `E[Λ] ≈ 870 KB` before first alarm; the QMC schedule gives
  `≈ 8.6 KB/round` forever — `8.6 MB` by round 10³, `8.6 GB` by round 10⁶.
- Secret shift (`ℓ` bits): by §3(B) the bound `b/q` holds only while `c` is unknown,
  i.e. for `≈ ℓ / log₂(1/p)` fired audits; after that the public-shift case applies.
  For `ℓ = 64, p = 1 %`: the same `870 KB` prefix bound as the beacon for ~10³ rounds,
  then `8.6 KB/round` unbounded. Strictly dominated by a beacon at every horizon.

Conclusion for (i): QMC does not change `b/q`; it deletes the theorem's premise.

**(ii) The generation randomness** — the seed `s_t` in `y_t = F(W, x_t, s_t)`, the LLM's
token sampling. This is the reading closest to "prove the sampling was honest" and to
the paper's own motivation ("computations which involve prover-generated randomness",
p.1). Transport: let the per-token uniforms be `u_t = {γt + c}` with `c` the prover's
private shift, and let the circuit check the Kronecker structure (exactly the paper's
`C_qmc` gadget, p.7/p.9). What the worst-case bound then says, for EVERY `c`: the
empirical distribution of `(u_t)_{t≤N}` has star discrepancy `≤ B₁ log N / N`, so the
fraction of tokens drawn from any quantile band `[a, b)` of the committed softmax is
within `O(log N / N)` of `b − a`. That is a genuine, seed-independent, worst-case
"aggregate distributional honesty" statement — the prover cannot, e.g., pick `c` so that
every token is the argmax. [READ, p.2–3 transported; INFERRED as a statement]

What it does NOT do, and this is the leakage question: the exfiltration channel is the
prover's *choice among valid continuations*, i.e. the choice of `c`. Capacity per
response is `≤ ℓ` bits (the bits of `c`) — identical to an `ℓ`-bit PRNG seed. The
discrepancy bound constrains the marginal histogram of the uniforms, not which of the
`2^ℓ` circuit-valid token sequences is emitted; every one of them is "honest in
aggregate". So `b` is unchanged, `q` is unchanged, and `E[Λ] ≤ b/q` is unchanged. The
audit theorem's existing remedy — `s_t` fixed *before* generation and registry-bound
(`notes/audit-theorem-statement.md` "Setting") — takes the seed channel to zero, which
strictly dominates a worst-case histogram bound. The paper's own Las Vegas observation
(p.16: prover-chosen randomness needs no derandomization when the output is always
correct) is the general principle: prover-chosen randomness is harmless iff the
statement does not depend on which randomness was chosen. Token sampling's statement is
the choice.

**(iii) Training-side minibatch sampling** has the same structure: a Kronecker index
sequence over a committed dataset order bounds only interval-visit frequencies; an
adversary choosing `c` and the order jointly places poison wherever the sequence
lands. No change to any bound we hold.

## 5. Citation trail (instruments named)

- **Google Scholar, via kagi result snippet** (query
  `zkQMC zero-knowledge proofs probabilistic computations quasi-randomness DeStefano`,
  2026-09-04): "Cited by 2". The Scholar page itself was not fetched.
- **Citer 1, identified [READ]:** eprint **2025/2152**, Bitan–DeStefano–Goldwasser–Ishai–
  Kalai–Thaler, "Sum-check protocol for approximate computations" (local mirror,
  pdftotext). zkQMC is `[DBD22]`, cited once, in the related-work list "verifiable
  computation protocols for approximate numerical computations [CCKP22, GJJZ22, EZC+25,
  ABIW22, DBD22]". A bibliography mention; the QMC technique is not used. (2025/2152 is
  itself relevant to the zkML pillar's float question and is DeStefano's own successor
  direction: approximate sum-check over ℂ. Not this lane's charge.)
- **Citer 2: not identified.** Instruments and their answers:
  - scry `openalex.works` `hasAllTokens(search_text_lc, ['zkqmc'])` → 0 rows; title
    tokens `['zero','knowledge','probabilistic','computations','quasi','randomness']`
    → 0 rows (coverage extent 1900-01-01..2026-09-04, no known holes). `api.openalex.org`
    `search=zkQMC quasi-randomness` → count 0. ePrint-only reports are not reliably in
    OpenAlex; `openalex.cited_by` therefore could not be run.
  - scry `academic.papers` `hasToken(text, 'zkQMC')` → 0 rows (corpus loaded
    2026-07-05..2026-09-04).
  - scry free-text `"zkQMC"` over `internet.text` → only base64 noise and Michael
    Dixon's homepage (mdxn.org).
  - Semantic Scholar: the record exists (paperId
    `6eda27ada73dc2350c9a950621c1e7601f60960c`, surfaced by kagi) but the public API
    returned HTTP 429 on all three attempts and the MCP server failed to connect, so
    its citation list was not read. Google Scholar author profiles for DeStefano and
    Dixon (kagi snippets) show the same "2" against this paper.
  - dblp (via kagi): ePrint entry only, no venue.
  - kagi `"zkQMC" cited OR citing … 2023 2024 2025 2026` and
    `"quasi-Monte Carlo" "zero-knowledge" proof low-discrepancy …` → no follow-up work
    combining QMC with proof systems; nearest hits are quantum-QMC and unrelated.
- **Artifact:** `gh search repos zkqmc` → nothing; `gh search code "zkQMC"` → only
  base64/domain-list noise; scry `github.documents` → not run to completion (query
  error on my side, not retried). The paper gives no URL. **No public artifact found.**
- **Follow-up work that already does what §3 proposes:** none found (corpus and
  instruments as above). The nearest neighbours we already hold are 2026/541's
  statistical trace test and Campanelli–Datta 2024/1645, neither of which is QMC.

## 6. Generality label

- **For the use the campaign named** ("prove the sampling was honest"; audit-selection
  or generation randomness): **trap.** The guarantee is uniform over the prover's
  randomness for a *fixed* bounded-variation integrand; the audit game's adversary picks
  the integrand adaptively after the points, and the Hardy–Krause term is exactly the
  adaptivity tax. Worse, the structure that yields low discrepancy yields recoverability:
  a secret-shift Kronecker schedule is learned from `≈ ℓ / log₂(1/p)` observed audits.
  In our vocabulary it is `BeaconRefutation` (`ε_beacon = p`, `q = 0`), expressible today
  as the one Prop in §3(A). It does not touch `ε_chk`.
- **For what the paper actually claims** (worst-case error on a prover-computed
  integral with prover-chosen points, verifier-known variation bound): **real, off-axis.**
  A composable ingredient for "a prover reports a UQ number about its own private
  simulation"; no pillar of ours has that shape today.
- **Prior-art value:** p.5 is a 2022 citation for beacon grinding and seed grinding
  (with the try-count union bound) named in a proof-of-computation paper — they are
  stepped around, not priced or composed. Add to `notes/audit-sampling-prior-art.md`'s
  trail; it does not change the "legs exist separately, nobody composes" narrowing.

**Verdict changes:** none. `docs/VERDICTS.md` §7 item 6 stands as written — zkQMC
supplies neither a beacon model for `ε_beacon` nor a checker instantiation for `ε_chk`.
`swarm/OPEN-QUEUE.md` §E's zkQMC line can be retired: the item now has content, and the
content is a refusal with its reason.
