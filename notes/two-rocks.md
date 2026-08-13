# The two rocks: what was under them

2026-08-13. Both frontier lanes returned. Headline candidate spot-checked
here (prime, family form, 2-adicity, inertia, fold identity — all verify).

## Rock 1 — the joint representation. Candidate: p = 2⁶¹ − 2⁵⁴ + 1

**It is KoalaBear one machine word up**: 127·2⁵⁴+1 to KoalaBear's 127·2²⁴+1.
Same Solinas shape, same cofactor. Properties (lane-computed, spot-verified):
2-adicity **54** (FRI instance ceiling 2^53 — **2^22× Goldilocks'**),
negacyclic NTT to N=2^53, Goldilocks-class reduction with 3 bits of lazy-
reduction headroom Goldilocks lacks, and **Φ_{3^k} irreducible — maximal
inertia — which Goldilocks and BabyBear both FAIL** (ord₉=3). The LTE witness
is present, so `CyclotomicInertia.lean`'s existing proof route applies.

**And there is a family law, provable once for both primes**: for
p = 127·2^n + 1, maximal inertia at every 3^k ⟺ n ≡ 0 or 2 (mod 6).
KoalaBear (n=24) and the candidate (n=54) are instances of one theorem.

**The honest scoreboard on my thesis** (the lane falsified half of it):
- "Nobody posed the joint problem" — FALSE: HELIOPOLIS §6.2 derives a real
  two-sided feasibility region; 2025/286 states our exact tension and takes
  the other branch (weaken the PCS). Six papers adopt proof primes.
- What survives, sharper: **nobody runs a SEARCH** — every paper picks from
  the menu {Goldilocks, BabyBear, 2^16+1, generic RNS} — and **2-adicity has
  never crossed the community boundary** (39 files corpus-wide, none FHE).
- And the constraint is LIVE: Zama 2026/027 hard-stops at D·t·n ≤ 2^31
  because Goldilocks' 2-adicity is exactly 32 — `Domain::new(2^32)` panics,
  **verified by execution**. Their flagship has one doubling of headroom
  left, imposed by a modulus chosen without checking the proof-side domain.

**Other results worth keeping:**
- **Goldilocks is the UNIQUE barrel-shift prime in 65–160 bits** (it is
  Φ₆(2³²) = Φ₁₂(2¹⁶) = Φ₂₄(2⁸) — unique three times over). Shift twiddles
  are take-Goldilocks-or-nothing; a theorem, not a scan.
- Crandall primes structurally excluded (max 2-adicity 12 over all c<4096).
- **The security-model reconciliation**: deployed fhegg "128-bit" = 127.9
  under the HE-standard model and **95.5 core-SVP** — the ~32-bit gap is the
  MODEL, not the parameters (estimator validated against Kyber-768/1024).
  Zama's "~100 bits" = 104.6/74.2, and their code samples BINARY secrets
  while the paper never states the distribution.
- 31-bit is structurally excluded as a ciphertext modulus (floor ~37 bits) —
  the vFHE lane is its own proof domain, and the least-bad second domain is
  the SAME PRIME FAMILY as the first.
- Cross-limb motivation weakened honestly: single-prime removes RNS basis
  extension, not the t/q rounding — and pt-ct has no basis extension anyway.
  The real saving is the ~25–50× emulation term.
- ⚠ Deployed limb q0 has 2-adicity 13: **the deployed tower cannot support
  N=8192 at all**. Any depth-2 move is a full limb re-choice.
- **NEGATIVE, do not build**: the NTT-domain-inside-FRI-domain idea. Novel
  (absent from 25,765 papers) but worthless: NTT is **0.27%** of 719's
  proving (73% is gadget decomposition — fix this attribution wherever our
  notes imply otherwise), matvecmul proves the reduction as a one-line
  committed-quotient identity, and coset-separation ZK is forfeited.

**First experiment (one line, falsifiable)**: swap matvecmul's
`#[modulus]` to 2287828610704211969, recompute the F2 constants; prediction:
the panic at ν=32 disappears and the ceiling moves 2^31 → 2^53, for ~3 bits
of noise margin, with lattice security IMPROVING.

## Rock 2 — the ring-native hash. The gap is real and the operators exist

The survey (exhaustive, greps enumerated): **no ring-native RO-like hash
exists anywhere; nobody has ever tried automorphisms as slot-mixing** (the
only "automorphism near hash" hits in 25,765 papers are unrelated). The
measured bill: Poseidon-over-Z_q costs **>2²² constraints and dominates
Zama's whole 2²²–2²³ IVC circuit** (32–64× the blind rotation it
authenticates) while the ring-native-but-linear MSIS hash costs **126** —
"essentially the entire Fiat–Shamir bill is the price of RO-ness."
LatticeFold's famous 50K recursion estimate is priced against a hash that
does not exist (Anemoi-over-R_q by fiat) and its FS analysis is verbatim
"left as future work."

**The finding**: 2026/1127's own constraint system (Definition 9) carries
σ₅ and σ₋₁ as native terms — used only for constant-checks — and those two
generate the full slot-permutation group of their own ring. The enabling
theorem (construction lane, verified at full rank): **End(R_q) ≅ R_q ⋊ G**
— every Z_q-linear map is an R_q-combination of Galois automorphisms. §D
conflates "algebraic" with "R_q-algebra map"; the missing slot-mixers sit
exactly in that gap, inside their own arithmetization.

**Candidate construction**: Poseidon2-shaped with linear layers
`x + c·σ(x)` (bare σ fails the finite-order criterion — measured ord 2/4 —
the ring coefficient lifts it to 1024, MDS∘(I+cσ) past 3000). Honest price:
**~3.9–4.8×** a field Poseidon per element — against the ~700×-per-element
status quo of decompose-and-hash. Chaghri's break analyzed and
distinguished (its premise fails in an R1CS cost model). Second candidate:
a gadget-decomposition Feistel (non-algebraic, measured to mix all slots,
free where folding already proves norms). **SWIFFT unification**: its ring
splits completely, so SWIFFT is the zero-S-box case of exactly this design
— the two known failures are one failure.

**The Lean transfer is free**: `RingSponge.lean` elaborates clean —
minidregg's sponge mode instantiates at R_q with ZERO new hypotheses.

~~**Open, stated plainly**: no cryptanalysis yet; the |K|+1 branch number is
a real weakness needing a degree analysis; extension-field slots (τ>1) are
a second front the Poseidon2b designers themselves decline to argue.~~
**SUPERSEDED 2026-08-13** — all three clauses moved:
- *"no cryptanalysis yet"* → done, `ring-hash-cryptanalysis.md` (direction
  SURVIVES, six priced weaknesses), now with prior art.
- *"the |K|+1 branch number is a real weakness needing a degree analysis"* →
  **the branch weakness is CLOSED at τ=4** (2 rows/elt/round reach slot-MDS),
  and the composite law is **t+|K|**, not t·|K|+1. `ring-hash-design.md` §1.
  What still needs a degree analysis is **coefficient grouping over F_{q^4}** —
  a different question from the branch number, and the one real open item.
- *"extension-field slots (τ>1) are a second front"* → **still the live question,
  and it is now THE question.** τ=1 is eliminated (2026/1127's own rationale: the
  strong sampling set has size q^τ, so τ=1 collapses the challenge space to
  2^64). But Beyne–Verbauwhede (eprint 2025/932, ASIACRYPT 2025) show integral
  properties in characteristic p survive **monotonically longer with extension
  degree** — round 1 at a prime field, 13 at degree 2, **20 at degree 4** — which
  withdrew an earlier τ=4 verdict. **τ=2 leads provisionally; one named
  experiment settles it.** `ring-hash-design.md` §4.4b–4.5.
This remains a candidate with a clear attack surface, not a construction — but
the surface is now mapped and priced.

## GATE RESULTS (2026-08-13, red-team + experiment + Lean — all three landed)

**Red team: the architecture survives; four headline corrections MANDATORY
before quoting:**
1. **Prior-art restated**: the prime appears in a 2014 Lisp NTT
   candidate-moduli table (stylewarning/lisp-random, comment-only, never
   deployed) — the honest frame is "never deployed; once listed as a
   candidate in 2014," which is arguably more charming anyway.
2. **Noise floor is 55–59 bits, not 51** — the 51 used weight bit-width as
   magnitude (16× understates ℓ1); with fhe.rs's ACTUAL distributions the
   floor is 59 — **only 2.4 bits under the candidate at 8-bit weights**.
   Tight. (4-bit weights keep comfortable margin.) And the clean floor
   depends on fhe.rs's exact-division encoding — p mod t ≈ 0.95t is
   near-worst for textbook-Δ BFV; the paper must state the encoding.
3. **Candidate core-SVP is 213.7, not 205** (stale draft number — even
   better, but the printed number was wrong). And the deployed fhegg secret
   is **CBD(20)** (σ=√10, support ±20) — mislabeled as ternary AND as
   CBD(10) by earlier lanes; actual-distribution security 98.1/130.5.
4. **Barrel-shift uniqueness restated**: the literal claim was false
   (Goldilocks is 64 bits — outside its own claimed window; 37 Φ_m(2^b)
   primes exist in 65–160 bits). The true theorem: among that form with
   **2-adicity ≥ 9**, Goldilocks is unique — and it is the form SIX ways.
   Form ≠ capability (factors of Φ_d(2) qualify too; the F7 73-bit factor
   is a live example), and the scan scripts had real bugs (factorint with
   a limit silently drops composite cofactors). Also: **p61 has NO
   barrel-shift capability** (ord₂ ≈ 2^57) — never imply it inherits that.

**Experiment: CONFIRMED on mechanism, REFUTED on "one line" — and the scar
strengthens the thesis.** Ceiling 2^32 → 2^54 by execution; p61 is
**10–40% FASTER than Goldilocks** (61 bits leaves spare-bit headroom that
64-exactly cannot); proof sizes equal. But e2e broke first: the artifact's
RLWE encode/decode was **Goldilocks-structural in two hidden ways**
(bit-shift decode relying on 2^64 mod q being tiny; wrapping_add through
u64) — **12/12 unit tests passed while decryption was garbage** — repaired
with ~20 lines of textbook exact Regev, field-generic by measurement
(13/13 on BOTH fields). This is more evidence for the paper's actual
thesis: representation choices propagate into deployed systems unexamined,
twice over in one artifact.

**Lean: everything proved, zero obligations.** The family law verbatim
(`familyP_maximalInertia_iff`), three independent derivations of the KB
headline, p61 fully certified with kernel-checked Lucas primality, the
n=214 counterexample proved (67-digit prime, ord₉=2, three quadratic
factors — the ⟺ has real teeth now), Goldilocks proved prime, and the
domain-availability lemma whose Goldilocks negative instance is the
matvecmul panic stated as mathematics. Commit 641ceeb, whole tree green,
HEAD-verified, codex untouched.

(Integrated 2026-08-13: paper/DRAFT.md, CLAIM-LEDGER.md and SUBMISSION-GATES.md now carry all of the above — four corrections applied, G1–G3 closed, new gates G13–G15.)
