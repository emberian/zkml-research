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
