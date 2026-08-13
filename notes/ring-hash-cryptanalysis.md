# Ring-hash candidate: cryptanalysis verdict

2026-08-13. The leg that was explicitly missing. **Verdict: the direction
SURVIVES — no feasible break on the reference instance — with priced
weaknesses the design lane must address before this is more than a candidate.**

## What held (proceed)

- **The σ-layer genuinely kills the 2026/1127 §D distinguisher.** Measured:
  integral over one input element stays balanced FOREVER with σ off
  (= §D's object) and saturates with σ on. The slot-mixing claim is real,
  by execution.
- **No Chaghri-style degree stall** at τ=1 or τ=2 — degree grows
  multiplicatively because x^α (α=7) is not a q-power map. ⚑ And the lane
  **retracted its own initial false positive** (a "persistent τ=2 integral"
  that was q=7 statistical noise, checked across seeds).
- No invariant slot-support subspace, no round-function subspace trail on the
  reference instance.

## The priced weaknesses (all must be addressed)

1. **Branch number is O(t) — ~7.2× weaker than a true MDS at frog width**
   (≤9 vs 65), and *independent of d*: one active input cell → 2t active
   output cells, rigorously. Slot-diffusion to full takes ~log₂d rounds
   (measured 7 at d=16). This is the design's own flagged weakness, now
   quantified.
2. **A real top-degree deficit, but data-bounded.** The full-element integral
   persists ~2.7× longer than a same-width real-MDS Poseidon (dies at r≈13 vs
   r=5 at d=4, robust across seeds). Costs q^d data ⇒ **infeasible at real
   parameters** (2^1024 at frog d=16), and lower-order integrals do NOT lag.
   So: not a break, but the quantitative signature that **the round budget
   assumed an MDS the design does not have.**
3. **C5 is a mislabeled gate** — it checks multiplicative order while claiming
   the Poseidon2/Out-of-Oddity criterion, which is minimal-polynomial
   irreducibility. The composite L badly fails irreducibility (char poly
   splits, e.g. degrees [1,1,1,1,4]). The property C5 names is actually
   delivered by C3 + the MDS. Replace with a real subspace-trail/min-poly
   check.
4. **Two unstated load-bearing requirements**: mixing coefficients must be
   generic ring elements — **a scalar/real MDS (a tempting optimization)
   REVIVES a t-cell invariant subspace with trivial distinguisher and
   preimages on it**; and per-round σ-support is 2, not 3 (support-3 is only
   achieved across rounds).
5. **The round count is borrowed, not derived** — RF=8/RP=22 is a width-~12
   Poseidon set, but the object is a width-144 SPN with an O(t)-branch layer,
   and Poseidon's derivation assumes MDS. **Deriving it for the actual width
   and the measured degree curve is the design lane's first job.**
6. Minor: one splitting toy fails C4 (capacity 2^208 < 2^256); and security
   still rests on the same ideal-permutation heuristic as Poseidon, now with
   a weaker linear layer and thinner margin.

Not executed: a direct Gröbner/CICO attack (no Sage; sympy timed out at n=4)
— priced via the degree data instead, and said so.

**Handoff**: ~~keep τ=1 (load-bearing)~~ — **adjudicated, and the answer is
neither: τ=1 is ELIMINATED** (the strong sampling set has size q^τ, so τ=1
collapses 2026/1127's challenge space to 2^64 — its own stated reason for raising
τ), **while τ=4 is the most exposed to integral cryptanalysis in characteristic p**
(§PA2b). **τ=2 leads provisionally.** See `ring-hash-design.md` §4.4b–4.5; derive the round count; fix the two validator gates; carry the degree deficit as
a known margin cost.

---

## Prior art (added 2026-08-13 — this file previously had NO external citations)

The verdict above was reached with zero external cryptanalysis cited, which is
its own defect. Three items, each verified at source; **two of the three came
back partly refuted, and the refutations are the useful part.**

### PA1. Rubato is broken at full rounds — but the analogy needs restating

**Grassi, Manterola Ayala, Norberg Hovd, Øygarden, Raddum, Wang, "Cryptanalysis
of Symmetric Primitives over Rings and a Key Recovery Attack on Rubato", CRYPTO
2023 (LNCS 14083, 305–339), eprint 2023/822.** Abstract, verbatim:

> "Symmetric primitives are a cornerstone of cryptography, and have traditionally
> been defined over fields, where cryptanalysis is now well understood. **However,
> a few symmetric primitives defined over rings Z_q for a composite number q have
> recently been proposed, a setting where security is much less studied.**"

and §1.2, sharper for our purposes: *"the cryptanalysis used to argue for their
security is developed for primitives over fields… knowledge of cryptanalysis
specific to the ring setting is limited."*

**What breaks:** full-round key recovery on **five of the six** Rubato variants
(Rubato-128L survives), e.g. Rubato-80M at 2^57.06 time / 2^17.91 data when
12 | q; 25–58% of admissible q are vulnerable depending on variant. Verified
experimentally by the authors.

**The mechanism, which is what transfers.** Lemma 1: for u | q and any
*polynomial* F over Z_q, F(x) mod u ≡ F(x mod u) mod u. So a polynomial round
function over Z_q **descends to a complete, independently attackable cipher over
every quotient Z_m** — the attacker gets a small faithful projection of the whole
primitive, the Gaussian noise stays non-uniform mod m, and once projected the
degree-2^r map falls to linearization.

⚑ **Do not call this a warning shot at our construction — that is overstated,
and a referee will say so.** The attack needs a *divisor of q*. Our q is prime,
so Lemma 1 has no nontrivial u and the first two attack stages have no analogue.
The paper's own §8.1 opens: *"Restricting q to Prime Numbers. The easiest way to
prevent our attack is to simply restrict q to be prime."* And **Rubato's
designers already patched the spec** — the current 2022/537 says *"in this
version, we explicitly assume that q is prime."* The paper's scope is Z_q, the
integers mod a composite; it never analyses R_q = Z_q[X]/(X^d+1).

**The honest transfer, which has real teeth.** The R_q analogue of Lemma 1 is not
the factorization of q but **the factorization of X^16+1 mod q into τ ideals**,
giving R_q ≅ ∏ F_{q^{16/τ}} — on which x^7 acts slot-wise and each σ_k **permutes
slots without mixing them**. That is the *same* wound in ideal-theoretic
clothing: a state map built only from slot-wise power maps and slot-permuting
automorphisms decomposes into independent per-slot maps. **This is precisely the
burden §1's branch analysis and `ring-hash-design.md` §1 discharge** — and it is
*our* analysis, framed by their lemma, not a result of theirs. Cite it for the
class ("the one deployed ring-native symmetric design was broken at full rounds
within a year, and the field's cryptanalytic toolkit is field-calibrated"), and
say plainly which ingredient we do not share.

### PA2. eprint 2021/1010 — the direction was noted; the number is wrong

**Endre Abraham, "Circuit friendly, post-quantum dynamic accumulators from
RingSIS with logarithmic prover time", eprint 2021/1010.** ⚠ **Unrefereed and
never published** (DBLP: "Informal and Other Publications"; no venue, no DOI;
8 pages, single author).

**(a) The de-linearization remark exists — but it is a different idea.**
§4, its last substantive line: *"…could be mitigated by **using small, chained
RSIS instances and breaking linearity in-between similar to SWIFFTX**."*
It is offered as a fix for **fixed-input-size**, i.e. domain extension — not
pseudorandomness; the paper never mentions random oracles, indifferentiability,
or Fiat–Shamir. And it is *opposed to its own construction*, which needs the
linearity (`acc = Σ L(x_i)`, and its circuit-friendliness pitch is literally
"even linear"). **Cite as "the direction was noted in passing as future work,
without a construction, and for domain extension rather than RO behaviour."**
Not as an independent proposal of our idea.

**(b) The "3,971 AIR constraints" figure is REFUTED — do not quote it.** Verbatim:
*"Our circuit complexity with relation to ZkStarks, expressed as an AIR is 3971
(1024 constants, 1024 multiplication and 1023 addition) for a single R-SIS hash."*
Three defects:
- **1024 + 1024 + 1023 = 3071, not 3971.** The paper contradicts its own breakdown.
- **It is an arithmetic-operation count, not an AIR constraint count** — the op
  count of one length-1024 inner product. **No AIR is exhibited anywhere**: no
  trace width, row count, transition constraints, constraint degree, or proof
  system. AIR reference [9] is cited once, for the word.
- ⚑ **The paper misstates the ring.** §2 justifies the quotient as "the
  irreducible x^n + 1"; but its own q = 59393 is prime with q−1 = 2^11·29, so
  2048 | q−1 and **X^1024+1 splits into 1024 linear factors** — R_q ≅ F_q^1024,
  fully split. (Computed, not recalled.) x^n+1 is irreducible over ℚ, never over
  an NTT-friendly Z_q. A reader following this citation lands on a paper that has
  the slot structure of R_q backwards.

**Consequence for us: there is no usable external datum for "R-SIS hash in an
AIR".** Our constraint counts must come from our own emitted object and cannot be
compared to this figure.

### PA2b. The extension-field S-box: three sources, and one citation of ours is wrong

Added after the τ adjudication (`ring-hash-design.md` §4.4b) turned this from a
side question into the deciding one.

⚠ **Our "2026/1127 fn.11" citation is WRONG — fix it wherever it appears**
(`sigma_poseidon.py:70`, `design_branch_frontier.py:368`). **Footnote 11 is a
bare URL**, `https://www.poseidon-initiative.info/`. The substance is in the
*sentence carrying the marker*:

> "good cryptanalysis of Poseidon only exists for fields of the form Z_q… **The
> study of Poseidon over extension fields is left for now as an open problem.**"

Cite the sentence, not the footnote.

**Poseidon2b is a real paper by the Poseidon designers** — eprint **2025/1893**
(held locally, misnamed, at `~/paperbin/eprint-2025-1893.pdf`). Its **Remark 4**
is the caveat the brief referred to, and it is blunter than a paraphrase:

> "**we cannot convincingly argue the security of Poseidon2b against such
> attacks.**"

⚑ **Beyne & Verbauwhede, "Integral cryptanalysis in characteristic p", ASIACRYPT
2025, eprint 2025/932** — the load-bearing new result, and it is why our τ
verdict moved. In large prime characteristic, **integral/divisibility properties
survive far past the round where algebraic degree saturates**, so prior degree
estimates for the MiMC/Poseidon family are *"overly optimistic."* Verified at
the authors' own artifact (`KULeuven-COSIC/integral-cryptanalysis-characteristic-p`,
executed `SPN.ipynb` outputs), the last round carrying a mod-p² property is
**monotone in extension degree**: **1** at a prime field, **13** at degree 2,
**20** at degree 4, 21–22 at degree 8. Their stated scope — *"finite rings of
prime characteristic p that are isomorphic to a product of fields"* — is
literally R_q.

**This supersedes §"What held" bullet 2 as a clearance.** That bullet records
"no Chaghri-style degree stall at τ=1 or τ=2, degree grows multiplicatively" —
still true, and now known to be **the wrong invariant**: degree growth does not
bound the integral property. ⚠ Their base primes are 2^17–2^31 against our 2^64,
so **round counts do not transfer**; the direction is solid, the magnitude at our
parameters is unmeasured. `ring-hash-design.md` §4.5 names the experiment.

**And the invariant-subfield condition (C6) is a named published class, not our
invention** — Marvellous, eprint **2019/426**, verbatim:

> "We require that the affine polynomial has **coefficients which do not lie in
> any subfield** of F_{2^{n/m}} thus frustrating this attack."

Our sharpened form: every σ-layer coefficient and round constant c ∈ R_q must
satisfy **σ₉(c) ≠ c**. Integer coefficients fail; X passes. **Cost zero.**

⚠ Two things **not** verified at source (eprint.iacr.org rate-limited throughout):
2025/932's abstract and §6.2 prose (confirmed via artifact README, not the PDF),
and the Chaghri §5.2.1 subfield quote (both local copies are v1 and lack the
string; the quote is from the CCS 2022 version). **Nothing above depends on the
Chaghri quote** — Marvellous says the same thing and is verified locally.

### PA3. SWIFFTX — the precedent, and the precedent for the wrong answer

**Arbitman, Dogon, Lyubashevsky, Micciancio, Peikert, Rosen, "SWIFFTX: A Proposal
for the SHA-3 Standard" (NIST SHA-3 submission, 2008)**, over SWIFFT (LMPR,
FSE 2008). SWIFFT is R = Z_257[α]/(α^64+1), f(x) = Σ a_i·x_i with binary-coefficient
inputs — and FSE 2008 §4 states the problem flatly: *"**Our family of functions is
not pseudorandom (at least as currently defined), due to linearity.**"* This is
**exactly our problem, posed in 2008.**

**The de-linearizer is two operations, and both leave the ring** (§2.3: *"The
linearity … is broken by the change of base performed by ConvertToBytes, as well
as by an S-box"*):
- **ConvertToBytes** — a base-257→base-256 radix conversion on *integer
  representatives*, coupling groups of 8 coefficients with a carry bit, mapping
  64 elements of Z_257 to **65 bytes**. Not coefficient-wise, not endomorphic:
  it changes the object.
- **A 256-entry byte permutation** applied to those bytes — i.e. to the binary
  representation, not to Z_257 and *a fortiori* not to Z_257[α]/(α^64+1).

(SWIFFTX's FinalTransform then computes over **Z_256**[α]/(α^64+1) — a third
algebraic setting, with a non-field coefficient ring. It de-linearizes by moving
between three incompatible domains.)

**"…which is precisely why it cannot be arithmetized" — sound, but label it as
OUR inference.** SWIFFTX predates arithmetization-oriented design by a decade and
never mentions circuits or constraints. What the paper *does* say is the strongest
support available (§1): the de-linearizing layer's *"primary goal … is to
significantly increase the degree of the entire SWIFFTX function, viewed as a
polynomial over either GF(2) or **GF(257)**."* **A layer whose stated design goal
is to have no low-degree expression over GF(257) is, by construction, a layer with
no cheap R_q-arithmetic expression** — and a carry-propagating radix conversion
plus a random-permutation lookup are precisely bit-decomposition, range-check and
lookup work in a circuit. Attribute the arithmetization consequence to us.

**Fate**: a first-round SHA-3 candidate, not advanced to round 2. ⚠ NISTIR 7620
gives **no per-candidate rationale** — its speed (320 cycles/byte in plain C) is
far off SHA-2 and that is the plausible reason, but **NIST does not say so and we
must not assert it**. No published break of SWIFFTX itself was found (searched;
"none found", not "none exists"). Known figures are against bare SWIFFT
(~2^106 collisions).

**This is the sharpest statement of our contribution.** SWIFFTX proved a linear
ring-SIS hash *can* be de-linearized while preserving the lattice reduction — but
bought it with a byte-domain excursion designed for high degree over GF(257).
**Our constraint is the one SWIFFTX had no reason to respect: de-linearize
WITHOUT leaving R_q**, via a power map that is a ring-native permutation, so the
nonlinearity lives in the arithmetic the proof system already speaks.
