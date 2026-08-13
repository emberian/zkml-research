# Convergence: what the wave settled, and the one build everything points at

2026-08-13, written in main context after ~10 lanes returned. Three lanes died
on credits mid-work (resumable, §5). This note is the consolidation — the
individual reports are in the transcript; what follows is what CHANGED.

## 1. The one build everything now points at

Four independent lanes converged on the same missing artifact:

- **Lookup constants lane**: logUp-GKR, Celer, logup*, and Twist/Shout-via-
  logup* all require a **multilinear/GKR substrate over a hash PCS** — and it
  is **absent everywhere** (zero `gkr` hits across Plonky3-at-pin, breadstuffs,
  minidregg). "Price the substrate once; the four contenders become cheap A/Bs
  on top of it."
- **Powdr's logup\* route** (the second rescue for one-hot on hash stacks,
  which our earlier three-member law did not know about) *uses* logup-GKR as a
  subroutine — so it needs the same thing.
- **catgrad/zkML lane**: matmul-as-vector-relation is the whole arithmetization
  (158,800 MACs in one 784-contraction on MNIST; 98.7% of the trace).
- **vFHE M1**: the 98,304-equation BFV family is a vector-relation problem
  arithmetized as AIR rows — the reason coverage sat at 1.

**The asset we actually hold**: `Selvage/LogupStar.lean` +
`LogupIndexLink.lean` — the **Lean half of the pushforward kernel**, with
`[LOGUP-ADDRESS-LINK]` named as the open seam, and `canonicalIndexColumn`
+ its boolean proof already there. That is the half worth having, because it
is the half that is *ours and proved*.

⚠ **CORRECTION TO MY OWN FRAMING (ember, and he is right): the existence of
p3-whir at our pin is NOT an asset and should never again be cited as one.**
The direction is **abandoning Plonky3 as fast as possible** — we do not want
their code in the trust path, we want our own Lean-authored, formally verified
substrate. Every "X already exists upstream, unwired" observation in this
repo's notes is a *temptation*, not an opportunity: wiring it grows exactly
the dependency Selvage exists to replace, and puts an unverified Rust engine
where a Lean-derived one belongs. **The substrate gets BUILT, in Lean, in
Selvage.** Upstream code may be read for API shapes and used as a throwaway
differential oracle in tests; it never enters the trust path, and "it's
already there" is not a reason for anything.

**The next real decision is what the Lean-authored multilinear/GKR substrate
looks like — not which upstream crate to wire.**

## 2. Three closures that shrink the board (all decisive, all negative)

- **Celer spike: NO-GO.** The 4.3× was mis-attributed (43m is Papini–Haböck's
  Eq. 5/6, not Celer §4.4) and **overpriced ~2× by its own author's cost
  model**; real ratio 2.3–2.6×, measured 2.35× at m=2^28. Worse: **at our
  n=2^16 tables Celer is in its weakest regime** (it degrades 2.7× with table
  size where logUp-GKR degrades 9%). And the named baseline **does not exist in
  our tree** — building it is most of building the contender.
- **Transciphering: dead, and the recorded obstruction was the wrong one.**
  x^5 IS a permutation at our t (gcd(t−1,5)=1) — the gcd wall was never the
  wall. The real wall: **Pasta-3's homomorphic decryption consumes 269 bits of
  noise budget at a 17-bit prime; our entire modulus is 109 bits.** Break-even
  needs a **170 kbit/s uplink**, plus 8.2 GB of key transfer and a permanent
  4× cost stranding at N≥16384. Our parameters are precisely why the published
  enthusiasm doesn't transfer.
- **Bootstrapping: dead in all four cells.** Crossover sits at **depth 13–17**
  against our depth 1–3; bootstrapping's own noise consumption (147–224 bits)
  exceeds our whole modulus; every NTRU parameter set in print is past the
  concrete fatigue point (2^1 to 2^73 over), and NTRU's `Ω(λ log²q)` dimension
  growth makes precision its structurally worst axis. Actionable residue: **if
  GBFV bootstrapping is ever wanted, t must change and no 20-bit option
  exists** — nearest cyclotomic primes are 22-bit (2768897, 3686401).

**Net: the FHE design space collapsed to something buildable** — depth-1–3
leveled BFV, coefficient encoding, MPC/PBS boundary for nonlinearities. That
is a narrower and clearer target than we had this morning.

## 3. The formal item that is days away and needs nothing contested

**Three-tree FRI-RBR: assemblable with class-(a) adapters only.** No open
mathematics, and — the surprise — **no ArkLib dependency on the critical
path**: our own trees hold BOTH missing legs (Selvage's
`hasMutualCorrelatedAgreement_of_isProximityGenerator` = WHIR Lemma 4.10
proved domain-general; breadstuffs' `curveUDParam_of_classical` = powers CA at
UD radius, general arity). The feared "MCA for all m" collapses because Hirai's
hypothesis is consumed **only at the folding arity** — set `errorstar m δ := 1`
elsewhere (PMF mass ≤ 1). Plan: a fourth thin repo at OUR pin vendoring Hirai's
six files (Apache-2.0), then a ~50-line theorem.

**v1 = the first unconditional machine-checked FRI RBR soundness anywhere.**
And it matches SP1's own `unique_decoding_queries` pricing formula at exactly
(1+ρ)/2 — their regime claim, our theorem.

## 4. Two soundness pins found in passing

- **Ext4 is under the bar, from three independent sources**: 2026/587 App. F
  (FS sumcheck challenges need |F| ≥ 2^128, and repetition cannot rescue it
  under grinding), logup* §5 (picks the **5th** extension of a 31-bit field for
  128-bit security), and our own recorded 2^123.6 ceiling. **This is a
  sumcheck-side pin, not only FRI-side** — and it must be made before the
  Selvage engine's FS rung closes around the wrong field. Ext5, not Ext6
  (Ext6 buys zero bits by Fenzi–Sanso Lemma 3.5 while costing every round).
- **The audit theorem's own negative, and it is load-bearing**: instantiating
  `AuditSampling` at inference forces `ε_chk ≥ 1 − 1/N` on width-N layers, so
  `q ≤ p/N`. **Sampling cannot amortize WITHIN a wide inference** — it
  amortizes which turns get proven, never which ops within a turn. An argument
  from our own theorem for why the zkML pillar needs a real prover. (The
  spatial floor is *named but underived* in our file — that is the work.)

## 5. Landed artifacts, and the three lanes to resume

**Landed**: Selvage sumcheck engine (`fa2df24`, resurrected from a deleted
audited artifact, vector-bound to Lean, fail-closed verifier, detached-clone
gated); paper integration (`2dc508d`, all four red-team corrections applied,
G1–G3 closed, G13–G15 opened, and it caught one over-claim of mine — the fold
congruence did NOT land as a named theorem); catgrad architecture memo + cards
Z1–Z4 + a running spike (`~/src/catgrad-spike`, 26 ops traced, **the swap was
two lines, not ten**).

**Died on credits, resumable from transcript**: KPZ encryption fix (was at a
num-bigint dev-dep question); S-two carrier census (was mid-build, one
namespace fix from running); ring-hash design refinement (was developing the
gadget-Feistel second candidate at full parameters).

## 6. Corrections to standing notes (apply before quoting)

- `lookup-ram-verdicts.md`: "the only named rescue is GF(2^128) packing" is
  true of 2025/105 and **false of the literature** — powdr's logup* route is a
  second rescue needing neither towers nor curves nor lattices (claim-only,
  soundness-free, and it deletes a sub-protocol its own source conditions a
  theorem on — but real).
- `fhe-scout-verdicts.md`: the transciphering gcd note is the wrong
  obstruction; replace with the 269-bit noise-budget wall.
- The Celer "43m vs 10m" row: both numbers are from one paper's Table 1, the
  43 is a re-quote of a 2×-overcounting model, and the ratio is 2.3–2.6×.
