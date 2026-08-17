# Ring hash: build it, and τ=2 — with the reframe that τ is the challenge space

2026-08-13. `notes/ring-hash-design.md` (1077 lines, written incrementally),
scripts versioned into `notes/ring-hash-scripts/` because **`~/src/ring-ro-hash`
is not a git repo — precisely how the predecessor's work nearly vanished.**

## Both of the lane's own verdicts reversed in place

**Delegation → BUILD IT**, reached independently and matching the peer
analysis: delegation pays only when the hash is expensive *in-circuit*, and
Poseidon-over-R_q is 856 constraints/permutation — **1127's bill is transcript
VOLUME; delegation attacks UNIT COST.** At the benchmarked config the Feistel
takes FS from **52.0% → 4.0%** of the circuit, and at 4% there is nothing left
to remove.

⚑ Instructive self-catch: its ProtoGaLattice write-up *"flagged that RO calls ≠
sponge permutations, said reconciling was required before multiplying, then
published the multiplicative claim anyway."* Naming a caveat is not the same
as applying it — a failure mode worth watching in our own writing.

## ⚑ THE REFRAME: τ is the exponent of the folding challenge space

**‖strong sampling set‖ = q^τ — and this is 2026/1127's OWN stated rationale,
not our inference.** It is absent from our entire corpus, and it is what makes
the τ fork a real trilemma rather than a cost question:

- **Challenge space eliminates τ=1** (q^1 = 2^64 is too small).
- **Integral cryptanalysis punishes τ=4**: Beyne–Verbauwhede (2025/932,
  verified at the authors' artifact) show integral properties in characteristic
  p survive **monotonically longer with extension degree** — round **1** at
  prime, **13** at degree 2, **20** at degree 4. **That falsified the premise
  the earlier τ=4 verdict rested on.**
- **Cost favours τ=4.**

**τ=2 is the only point acceptable on all three.** Confidence deliberately
lowered; the settling experiment is named (the authors' own `SPN.ipynb` at our
parameters). The cryptanalysis lane's "keep τ=1" and the design lane's "τ=4"
were **both** wrong, for different reasons.

> ✅ **SETTLING EXPERIMENT EXECUTED (2026-08-17).** The authors' `SPN.ipynb`
> machinery, run verbatim at our base ~2^64 (Frog *and* 2^64−257, identical),
> holding e·t = 16: **τ=1 → round 2, τ=2 → round 24, τ=4 → ≥42** (guard: it
> reproduces the paper's 1/13/20/21 exactly). The reframe's monotonicity holds by
> execution, **but the magnitudes at our modulus are ~2× the paper's** — the τ=2
> integral property survives to **24, not 13** (same e=2,t=8; pure base-prime
> effect). Verdict unchanged (τ=2), but its round-count margin over the borrowed
> 30-round budget is only ~6 rounds and 24 is a *lower* bound for the real
> slot-MDS-in-full-rounds schedule. **Deriving the round count is now the binding
> open item, not a formality.** Full record: `ring-hash-design.md` §4.5a; script
> `notes/ring-hash-scripts/integral_char_p_settling.sage`.

## The two candidates, resolved

- **σ-Poseidon is bounded by its own S-box, not by τ.** The S-box floor is
  **15.3×** — essentially the 16× packing ceiling — and τ only decides 8.0× vs
  5.0×. So the τ question is not what limits it.
- ⚑ **The Feistel's 92,257 is NOT a modelling slip** — the check I asked for.
  It wins **4.67× on permutation AND 5.60× on rate because it has no S-box.**
  The risk is the **free-norm-check assumption**, not the arithmetic.
- **C1 is twice as constraining at τ=4**, so the two candidates want
  incompatible moduli — resolved by a joint modulus at **2^64 − 279**, found in
  seconds rather than filed as an obstruction.
- The **t + |K| branch law** extended past t=2 (13/30 configs certified both
  halves, zero disagreements).

## Prior art added — and two of three came back partly refuted

The cryptanalysis file had **zero external citations**; it now has them, with
corrections:
- **The Rubato "warning shot" framing is overstated** — that attack needs
  **composite q**; ours is prime, **and that is the paper's own
  countermeasure.**
- ⚠ **2021/1010's "3,971 AIR constraints" MUST NOT be quoted** — its own
  breakdown sums to 3,071, it is an **op count with no AIR**, and it
  **misstates its own ring.**
- ⚠ **Our "2026/1127 fn.11" citation is wrong** — footnote 11 is a bare URL.

## Still open, named

**τ itself** (one named experiment), **the round-count derivation owed in every
τ regime**, and the **Feistel's two structural assumptions**.

## Process note

Sibling lanes' commits absorbed this lane's in-progress file **twice**
(`05a06b1`, `edd474f`, `10e0104`). Nothing lost — verified in HEAD each time —
authorship misattributed, not rewritten, per doctrine. **This is the
`--only`-is-path-granular hazard firing in a hot shared file, as documented.**


---

## ADDENDUM (2026-08-16): the dual-mode composition — one artifact, both modes, one modulus

`notes/ring-hash-dual-mode.md` (`297a389`). **The linear mode is the P=0,
round-0 PROJECTION of the gadget-Feistel** — a standard Ajtai/MSIS gadget
commitment `C = A·G⁻¹(v+a₀)` — with the de-linearizer sitting strictly *after*
the commitment read-out, so **linear-mode openings never cross it, and the
same invariant keeps the KRS25 hash-delegation attack unreachable.**

- ⚑ **Parameter compatibility POSITIVE, with a better modulus found**:
  **q = 2⁶⁴−257** at τ=2 (ord₃₂=2, α=7 legal, γ=257 — *strictly better
  grinding margin than the τ=4 point 2⁶⁴−279*). One set serves both modes;
  **the γ-ambiguity is asymmetric in our favor** — a grinding channel in hash
  mode that *cannot* break binding.
- **The verdict splits by world, both halves earned**: as a wrap transplant
  **dead by arithmetic** (×0.7–×13 vs the post-split Horner chains, and the
  Galois packing already banked ×2.011 of the ×2.13 target). **In the R_q
  world: coherent and cheap** — 16–33% of the Feistel FS bill, and
  commit-instead-of-absorb attacks the **VOLUME half of the bill that
  delegation provably could not**, amortizing past κ=24 ring elements.
- **Opening cost 1.5–3.0×10⁴ R_q rows, ~95% of it transcript hashing** — the
  full mode prices its own commitment's openings. *Self-referential in the
  right direction.*
- ⚠ **Security-sharing stated honestly**: shared arithmetic, parameters, cost
  table, and a one-way implication (a linear-core collision breaks both) —
  **NOT one assumption.** MSIS provable; RO-likeness stays heuristic.
  Corrected en route: the 302,141 bar was τ=4; **the standing τ=2 figure is
  363,513.**
- **Lean form**: `OpeningScheme` reused unchanged; **`Op` is a short-plane
  SUBTYPE so an unchecked norm is unrepresentable** — the free-norm-check
  hazard excluded structurally, where forgetting it makes binding vanish
  fail-open. Eight obligations tabled; **O2 (sponge indifferentiability) the
  only wall, and it predates the question.**
- ⚠ Premise check: "absorb is R-SIS-linear" is true of the **Feistel candidate
  specifically** — if its three caveats kill it, **the linear mode stands
  alone as the multilinear-PCS-over-lattices answer.**
