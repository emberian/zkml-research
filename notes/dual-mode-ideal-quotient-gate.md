# Dual-mode ideal-quotient gate: does either full-mode round respect a CRT ideal?

2026-09-04. Adversarial-analysis lane on our OWN construction (`ring-hash-dual-mode.md`,
`ring-hash-design.md` §3/§5, `ring-hash-scripts/`). An external reviewer named the elementary
hazard below as belonging *before* any indifferentiability proof. Script:
`notes/ring-hash-scripts/ideal_quotient_gate.py` (82 s on a laptop, at the REAL modulus).
Every rate below is `[OURS, measured this session]` and quoted from that run.

## 0. One breath

**Both full-mode candidates escape; the escaping component is named in each.** σ-Poseidon escapes
*only* through the σ-layer, and only in rounds whose exponent is outside ⟨q⟩ = {1, 31} mod 32 —
**14 of 30 rounds of the versioned schedule are slot-respecting** (rate 1), reproducing the attack
lane's §3b defect by a different statistic. The gadget-Feistel escapes through `G⁻¹` alone, already
at P = 0. The linear mode is slot-respecting **in the planes** (rate 1 — the feature) and not in the
payload; no cross-mode leak. ⚑ One cost sentence is at risk for a *second* slot-structure reason:
the τ=2 "107.8/elt" row prices full slot-support with a τ=1 law that counts σ_{−5^j} as a new
slot — at τ=2, σ₋₁ = σ_q is the in-slot Frobenius and buys nothing (§5).

## 1. The hazard, and where the corpus already had it

`[DERIVED]` R finite commutative ring, I a nonzero proper ideal, π: R → R/I a ring hom. Any
F: R^w → R^w built from ring +, ring × (constants or variables), R-linear mixing, x^α satisfies
x ≡ y (mod I) ⇒ F(x) ≡ F(y) (mod I) componentwise. For an ideal permutation that event has
probability |R/I|^{−w}; so one query pair distinguishes, and over R ≅ ∏ R/I_i, F is |R/I|-many
independent maps. Here R_q = Z_q[X]/(X¹⁶+1), q = 2⁶⁴−257 prime, q ≡ 31 (mod 32), so X¹⁶+1 =
∏_{k∈{1,3,…,15}} f_k with f_k = X² − c_k X + 1, c_k = ζ^k + ζ^{−k} ∈ F_q, ζ a primitive 32nd root of
unity in F_{q²} = F_q[i]; R_q ≅ (F_{q²})⁸, I_k = (f_k). Baseline per element: q^{−2} = 2^{−128}.

Present in the corpus before this lane (so: not new, and named): 2026/1127 §D's slot-locality
observation, quoted in `sigma_poseidon.py`'s docstring as the design's reason to exist;
`ring-hash-cryptanalysis.md` PA1 ("the honest transfer … a state map built only from slot-wise
power maps and slot-permuting automorphisms decomposes into independent per-slot maps");
`ring-hash-attacks-2-3-4.md` §3b / `docs/VERDICTS.md` §5l (14/30 slot-trivial rounds, run 8–11,
found via the group action on slot *indices*). **Not present**: a direct measurement of
Pr[F(x) ≡ F(y) mod I_k] at the real parameters, per layer and per round — that is this note.
(Instrument: `grep -rn -i 'ideal.quotient\|mod I_\|slot-respect\|Ideal.Quotient' notes/ docs/
forcodex/` → ∅ before this file.)

## 2. The instrument

`ideal_quotient_gate.py` (reproduce: `cd notes/ring-hash-scripts && python3 ideal_quotient_gate.py`,
82 s): builds F_{q²} = F_q[i] (q ≡ 3 mod 4 checked), finds ζ, the eight c_k
(first three printed: 6929386219744803138, 220911891461223498, 13444931089333412157), checks each
disc c_k²−4 is a non-residue (irreducibility) and **multiplies the eight quadratics out in Z_q[X]
without reduction to X¹⁶+1** (the splitting witness). x ≡ y (mod I_k) is tested two ways — evaluation
at ζ^k in F_{q²}, and long division by f_k — and both are asserted on every sampled pair. Pairs:
x uniform in R_q^w, y_j = x_j + f_k·r_j with r_j uniform (y uniform in x's coset). The round
functions are the **ground-truth objects**: `sigma_poseidon.frog_like(q=2⁶⁴−257)` (imported; τ=2,
ℓ=8, C1/C3/C4 PASS) with a round-slice whose 30-round composition is asserted equal to
`SP.permutation`; `design_gadget_feistel.Feistel(q=2⁶⁴−257)` loaded by exec-ing the file's
definitions above its first experiment banner (verbatim, no re-typing). N = 3 pairs per (test, slot)
(N = 2 for the 30 single-round sweeps); with a 2^{−128w} baseline, one agreement is the hazard.

## 3. Results (whole-state agreement rate per slot k = 1,3,…,15; per-elt = mean element agreement)

### 3a. σ-Poseidon (t = 9, RF = 8, RP = 22, α = 7, σ in every round)
```
  round constants s+rc / S-box x^7 / R_q-MDS          1.00 ×8   per-elt 1.000   HAZARD  (ring-polynomial)
  σ-layer x + c·σ_1(x)   [identity]                     1.00 ×8   per-elt 1.000   HAZARD
  σ-layer x + c·σ_31(x)  [= σ_q: in-slot Frobenius]     1.00 ×8   per-elt 1.000   HAZARD
  σ-layer x + c·σ_5(x)   [8-cycle on slots]             0.00 ×8   per-elt 0.000   escape
  σ-layer x + c·σ_25(x)  [two 4-cycles]                 0.00 ×8   per-elt 0.000   escape
  σ-layer x + c·σ_17(x)  [four 2-cycles]                0.00 ×8   per-elt 0.000   escape
  single rounds: HAZARD exactly at r ∈ {2,5,8,9,10,11,14,17,20,21,22,23,26,29} = 14/30
                 (exp ∈ {1,31}); every other round: escape at all eight slots
  rounds 0–1 (1 and 2 rounds)                           0.00 ×8                   escape
  rounds 8–11 (the slot-diagonal window, 4 rounds)      1.00 ×8   per-elt 1.000   HAZARD
  full permutation, 30 rounds                           0.00 ×8                   escape
  CONTROL σ OFF, 30 rounds (= 2026/1127 §D's object)    1.00 ×8   per-elt 1.000   HAZARD
  σ_5 every round, 30 rounds                            0.00 ×8                   escape
```
**Reading.** The escaping component is the σ-layer, and only when k ∉ ⟨q⟩. At τ=2, ⟨q⟩ = {1,31}
and **σ₃₁ = σ_q is literally the power map x ↦ x^q on R_q** (asserted in the script: `pow(x,q) ==
sigma(x,31)`, `pow(x,q²) == x`) — a ring-polynomial map, slot-respecting by §1's theorem, and the
gate cannot tell it from the identity. The `frog_like` schedule's `r%3==2 → 31` rounds (10) and
its `5^8 ≡ 1` block (rounds 9,10,21,22) are therefore eight independent F_{q²} maps, and rounds
8–11 compose to a slot-diagonal 4-round permutation. **The whole 30-round permutation escapes** —
the σ₅/σ₂₅/σ₁₇ rounds do the work — so σ-Poseidon is NOT "eight independent hashes" as shipped;
its *cost* includes 14 σ-layers (1 row/elt each) that mix nothing. Fix is the attack lane's:
per-round `exps[r] ∉ ⟨q⟩ (mod 2d)`; `sigma_poseidon.py`'s C3 checks the group generated across the
schedule and passes this instance.

### 3b. Gadget-Feistel (state 2w = 8, B = 2¹⁶, K = 4, P = 2, NR = 16, γ = 257)
```
  G⁻¹ alone (all four planes Y_j)                       0.00 ×8   per-elt 0.000   escape
  the dense plane-linear map on UNdecomposed x (ctl)    1.00 ×8   per-elt 1.000   HAZARD
  F_0 at P=0 (G⁻¹ then linear)                          0.00 ×8                   escape
  F_0 at P=2 (G⁻¹, adjacent-plane products, linear)     0.00 ×8                   escape
  1 round  (Feistel: R passes through)                  0.00 ×8   per-elt 0.500   escape
  2 rounds / 16 rounds                                  0.00 ×8   per-elt 0.000   escape
```
**Reading.** The escaping component is `G⁻¹` itself: a slot congruence is not a coefficient
congruence, so the base-2¹⁶ digit planes of x and of x + f_k·r share no slot. The plane-products
(P) are irrelevant to *this* gate (they are load-bearing for the differential gate of
`ring-hash-design.md` §3, a different hazard). The 0.500 at one round is the Feistel pass-through
of the untouched branch; it is gone at two rounds.

### 3c. Linear mode C = A·G⁻¹(v + a₀) (κ = 2 rows for the test, A uniform)
```
  as a map of the payload v (G⁻¹ inside)                0.00 ×8                   escape
  as a map of the planes Y  (R_q-linear)                1.00 ×8   per-elt 1.000   HAZARD = the feature
```

## 4. The Lean-shaped gate (stated, not proved)

`RingSponge.lean`'s carrier `Rq q d := Fin d → ZMod q` is additive-only ("the ring structure lives
entirely inside the permutation P"), so the gate lives on the permutation parameter, over a carrier
with the ring structure, e.g. `AdjoinRoot (X^16 + 1 : (ZMod q)[X])`:

```lean
def StateCongr {R} [CommRing R] {w} (I : Ideal R) (x y : Fin w → R) : Prop := ∀ j, x j - y j ∈ I
/-- THE GATE: no CRT ideal is respected by F. -/
def IdealQuotientEscape {R} [CommRing R] {w ℓ} (I : Fin ℓ → Ideal R)
    (F : (Fin w → R) → (Fin w → R)) : Prop :=
  ∀ i, ∃ x y, StateCongr (I i) x y ∧ ¬ StateCongr (I i) (F x) (F y)
/-- the per-round strengthening the attack lane asked for (per-round C3): -/
def PerRoundEscape (I : Fin ℓ → Ideal R) (round : Fin NR → (Fin w → R) → (Fin w → R)) : Prop :=
  ∀ r, IdealQuotientEscape I (round r)
/-- the negation is a THEOREM for every ring-polynomial F, via `Ideal.Quotient.mk` being a RingHom: -/
theorem mvPolynomial_respects (I : Ideal R) (F : Fin w → MvPolynomial (Fin w) R) :
    ∀ x y, StateCongr I x y → StateCongr I (fun j => (F j).eval x) (fun j => (F j).eval y) := sorry
```
ATLAS fields. *Satisfiable*: the script's witnesses — for every i, (x, y = x + f_i·r) with round 0
(σ₅) of σ-Poseidon and with F₀ of the Feistel; agreement 0/3, baseline 2^{−128·w}. *Teeth*: the
negation is inhabited, by measurement (rate 1 at all eight i) and by the theorem: the affine layer
(rc + R_q-MDS), x⁷, x + c·σ_{±1}(x), rounds {2,5,8,…} above, the σ-off 30-round permutation, the
Feistel's plane-linear map on undecomposed input, and Y ↦ A·Y. So the gate distinguishes real
rounds from real rounds; it is not a tautology. *Premise-inhabitation*: the ideals exist — ∏ f_k =
X¹⁶+1 verified in Z_q[X] with no reduction, each f_k irreducible by Euler's criterion on its
discriminant; `I k := Ideal.span {AdjoinRoot.mk (f k)}`. The Mathlib route to the product identity
is a `norm_num`/`ring_nf` check at eight 64-bit constants; left as the obligation it is.

## 5. Sentences at risk, and why

**(R1) ⚑ The τ=2 "107.8/elt (6.7×)" row — the σ cost law was derived at τ=1.** `design_branch_
frontier.py` §(2) / `ring-hash-design.md` §2.0: one Def.-9 row carries both σ = σ₅ and σ̃ = σ₋₁, so
c chain rows + one fused combine reach {5⁰..5^c} ∪ {−5⁰..−5^{c−1}} = "support 2c+1", i.e.
**support s costs ⌈(s−1)/2⌉**. At τ=1 those are 2c+1 distinct slots. **At τ=2 the slot class of
−5^j is the slot class of 5^j** (σ₋₁ = σ_q; §3a measured it slot-respecting), so the σ̃ channel adds
no class. `design_tau_tradeoff.py` prices τ=2 full slot-support 8 as ⌈7/2⌉ = 4 rows. The script's
§(D) enumerates the design note's own row model (one new witness per row; combine reaches
classes(E ∪ 5E ∪ σ̃E) with independent coefficients): `[DERIVED]`
```
  σ̃ = σ_31 (the "natural pick, what 2026/1127 uses", design §2.0)  → 6 chain rows for support 8
  σ̃ = σ_25 / σ_17 / σ_9 / σ_3                                        → 3 chain rows
```
Under the note's cost law rows/perm = 376 + (s_f·8 + s_p·22)·9: **s_f = 6 → 1006 rows = 125.8/elt
(5.7×); s_f = 3 → 790 rows = 98.8/elt (7.3×); the recorded 862 = 107.8 (6.7×) corresponds to
neither.** The direction of the trilemma is unchanged (τ=4 still cheapest, τ=1 still eliminated on
challenge space); the number is. Sentences carrying it: `ring-hash-design.md` l.55 ("**107.8
(6.7×)** τ=2") and l.654 (§4.5 table, "**107.8/elt (6.7×)**"); `ring-hash-dual-mode.md` l.52
("**363,513** (= 3,372.1 ring elements/step × 107.8)"), l.220, l.333 (trilemma row "σ-Poseidon
slot-MDS cost … **107.8**"); `dual_mode_costs.py` ("sigma-Poseidon tau=2 107.8"). ⚠ l.307 of the
design note also reads 862/107.8 but is the τ=1 "support-9 in full" row — same arithmetic, not at
risk. **This is a re-pricing for the design lane, with pp = (σ₅, σ₂₅) as the obvious repair; I did
not re-read Def. 9 at the PDF to confirm pp may be chosen freely per index — design §2.0 says so.**

**(R2) The schedule.** `sigma_poseidon.py` C3's docstring "sigma_-1 is REQUIRED" (true at τ=1,
where ⟨5⟩ is half of (Z/32)^*) and `frog_like`'s "butterfly schedule, closed under the FULL group":
at τ=2, σ₋₁ is slot-trivial and 5⁸ ≡ 1 makes one block in four the identity. Already recorded as
a defect (`ring-hash-attacks-2-3-4.md` §3b, VERDICTS §5l); §3a is its congruence-rate form.

**Not at risk, checked.** `ring-hash-cryptanalysis.md` "What held" bullet 1 (σ kills the §D
distinguisher) — confirmed by an independent statistic (σ off: rate 1 through 30 rounds; σ on: 0).
The 24-round integral floor (`integral_char_p_settling.sage`) is a SHARK/x⁷ model with a slot-MDS,
i.e. it already assumes cross-slot mixing, and the script itself notes weaker mixing "can only be
≥ 24" — the slot-diagonal window lengthens survival, it does not invalidate the floor. The
Gröbner/CICO item-3 verdict: the attack lane already saw the window and said it stands.

## 6. Linear mode, and cross-mode leakage (the "one parameter set" premise)

Slot-respecting **in the planes** is the feature: the evaluation opening (`ring-hash-dual-mode.md`
§4) is R_q-linear algebra, the strong sampling set is the diagonal F_{q²}, and folding works
slot-wise. As a map of v it is not slot-respecting (G⁻¹), which is harmless (binding is to v via
the planes, §2d). A slot-congruent plane pair Y ≡ Y′ (mod I_k) yields C ≡ C′ (mod I_k) — agreement
in ONE of eight commitment slots; binding needs all eight, which is MSIS. `[DERIVED]` such short
pairs exist (I_k has index q² in Z¹⁶, so λ₁ ≲ 4·q^{1/8} = 2¹⁰ < B) — the ordinary CRT structure of
MSIS over a splitting ring, priced by the MSIS reduction, not by the hash; not exhibited (no LLL run).

**No leak into full mode.** The shared object is G⁻¹ ∘ (dense R_q-linear map) (§2c: linear mode is
the P = 0, round-0 projection). In both modes G⁻¹ precedes the linear map, so the only
slot-respecting sub-map, Y ↦ A·Y, is reachable only by whoever chooses planes directly: the
linear-mode prover (MSIS-bounded), and in full mode only through plane freedom — the γ-ambiguity
(~2^{−52}/elt) or norm slack (attacks item 2: 64·s bits/elt). `[DERIVED, counting]` steering a
plane difference D = Y′ − Y into I_k^K needs each of K = 4 plane-differences to vanish at slot k:
2 F_q conditions per plane ≈ 512 bits, against 64·s bits of freedom — unreachable for s ≤ 7. This
is conditional on O5 (the enforced ∞-norm bound), which the attack lane already says gates
shipping. A ≠ F₀ (§2a) and mode domain separation (§5e) are the other two walls; both are spec lines.

## 7. Absence/presence claims, and what I could not verify

- Presence: the hazard in the corpus at three places (§1), by `grep -rn 'Sec\. D\|slot-local'
  notes/` and reading. Absence of the direct congruence statistic: §1's grep → ∅. No web
  instrument (Kagi/scry) was used: this is a check on our construction; no external absence claimed.
- Not verified: 2026/1127 Def. 9 at the PDF for free choice of (σ, σ̃) per index (R1 rests on
  design §2.0's reading); the 24-round floor re-run with the actual 14/30 schedule (sage not
  rerun); C6 on `frog_like`'s uniformly drawn coefficients (holds w.p. 1 − q^{−16}, not checked per
  coefficient; the escape needs only k ∉ ⟨q⟩ and c ≠ 0 in every slot); §6's short-plane bound.
