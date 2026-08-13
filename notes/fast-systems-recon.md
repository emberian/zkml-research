# What makes the fast systems fast — and a contradiction with the floor lane

2026-08-13. Six systems read at source, with measurements run on this machine.
**Read the contradiction first; it changes which lever matters.**

## ⚑⚑ OPEN CONTRADICTION — is the prover hash-bound?

- **Floor lane (derived)**: *"hash-bound at every blowup ≥ 2"*, 94% hash at
  our deployed lb=6.
- **This lane (MEASURED on this laptop, matched Plonky3 FRI-vs-WHIR bench)**:
  *"FRI proving is **~19% hashing with Blake3, ~40% with Poseidon2**. The
  prover is NOT hash-bound — the LDE and folding arithmetic are the larger
  half. FRI **verification** is ~100% hashing."*

Raw numbers behind the measurement: Merkle commit of 2^15×135 BabyBear —
Blake3 **36.3 ms (8.2 ns/elt)**, Poseidon2 **100.9 ms (22.8 ns/elt)**; coset
LDE at blowup 2 is **8.0–12.5 ns/elt**.

**This is not reconcilable by hand-waving and it decides a lever.** If
hash-bound, the field/hash choice dominates and the KoalaBear migration is
worth ~3.4×. If arithmetic-bound, the LDE and folding dominate and the
migration is worth much less. Note the measurement is at **ρ=1/2** while our
deployed point is **ρ=1/64**, and the floor model's hash term scales with
blowup while its encode term also does — **so the disagreement may be about
where the folding rounds are booked.** ⚑ **Resolve by instrumenting one real
IR-v2 proof at lb=6 and lb=4 with a profiler. Until then, do not quote either
figure as settled.**

## The measured ~3× cliff that forces a design decision NOW

Plonky3's own sumcheck bench, run here at 2^22: **`base_ext` 11.99 ms vs
`ext_ext_packed` 35.40 ms — 2.95×.** Round 0 is half the sumcheck work, so
keeping it in the base field is ~1.5× on the whole sumcheck by itself. **This
single fact explains SVO, the univariate skip, SP1's fused first-two-rounds,
and Expander's four-type field stratification — they are all "stay in the base
field longer."**

⚑ **The commitment: the emitted AIR object must be POLYMORPHIC IN THE VALUE
RING FROM DAY ONE.** Every system encodes the boundary in its type system
(SP1's `Air<..F,F,EF>` *and* `Air<..F,EF,EF>`; Expander's four field types;
Plonky3's `A: Algebra<B>`). **Retrofitting means rewriting every constraint,
and until you do you pay 3–4× on the hottest round forever.**

## Jagged PCS — the highest-value idea, and we already have its primitive

One commitment, one codeword, one query set, for arbitrarily many tables of
arbitrarily different heights. Prover: **≤ 5·2^m + 2^n + 2^k multiplications**
(the "5 per trace element", decomposed: 4·2^m for the sumcheck + the rest
generating the indicator). **No extra oracles** — the proof is the dense PCS
proof + two sumcheck proofs + row/col counts. Verifier depends only on total
log-area `m`, **which kills the one-recursion-circuit-per-proof-shape
explosion.** Soundness error `2m/|F|`.

It reduces to a degree-2 product-of-two-multilinears sumcheck plus a **width-4,
two-bit-state read-once branching program** (`MemoryState { carry,
comparison_so_far }`) — a finite, decidable-per-layer Lean object with an
induction on top. **`sumcheck-toy` already proves exactly that sumcheck shape
over BabyBear with Ext4 challenges.** Ceno independently made Jagged its
default PCS.

⚠ **Two teeth not to drop** (without them a prover re-slices the dense vector
at will): prefix-sum **monotonicity** (`full_geq`) and the
**dimension-binding hash** `compress(commit, H(len ‖ rows ‖ cols))`.
⚠ **Ceiling: 2^30 total committed cells** — a consequence of our field size,
not their design. That is why SP1 shards.
⚠ The "~16× better verification" figure is **asymptotic in the paper**
(λ·2^k → m·2^k); the 16 is unverified. Do not quote it.

## ⚑ Our soundness posture is the outlier, and fixing it is cheap AT OUR RATE

| system | regime | conjecture? | queries |
|---|---|---|---|
| SP1 Hypercube | UniqueDecoding | **no** | 124 / 94 |
| OpenVM/SWIRL | UD + proven Guruswami–Sudan | **no** — *"We use only proven error bounds"* | 443 app |
| Binius64 | UniqueDecoding | **no** | ~232, zero PoW |
| leanVM | **Johnson** (a theorem); capacity behind a Cargo feature | no by default | — |
| Ceno | `enum SecurityLevel { Conjecture100bits }` | **yes** | 100 |
| **dregg IR-v2** | — | **yes** | **19** |

Our IR-v2 reads **128.7 conjectured / 71.7 Johnson / 34.6 unique-decoding** —
independently reproducing our own recorded "conjectured 130 / proven 51–73",
which cross-checks both.

**To reach 100 genuinely-UD bits: 86 queries instead of 19 — and `log_blowup`
does NOT change.** We already run ρ=1/64, so each query is worth *more*
(0.98 UD bits/query vs SP1's 0.68 at ρ=1/4). **We have already bought the
expensive half.** The delta is **4.5× on the query phase and ZERO on the
commit phase.** For comparison, 100 UD bits costs 203 queries at ρ=1/2, 124 at
1/4, **86 at 1/64** — we are on the cheap end of that curve already.

**And leanVM publishes the price of the conjecture, measured, side by side:**
proven **1426 XMSS/s, 327 KiB** vs conjectured **1481 XMSS/s, 171 KiB** —
**~2× proof size, ~4% time.** Copy their shape: default proven, conjecture
behind a compile-time flag, **publish both columns.**

## Free algebraic wins — take all of them, they are ring identities

`{0,1,∞}` (send h(0),h(∞); h(1) free from the claim) · `{0,2,4}` chosen so
extrapolation is **pure adds and doublings** · SP1's zerocheck stacks **four**
free-point tricks in one function (degree-4 needs 5 points, they compute 3, and
2 in round 1) · fold as `α(y−x)+x` not `αy+(1−α)x`, halving extension mults on
the hottest loop. **In Lean these are EASIER to prove than the naive forms.**

Also already-in-our-tree-and-unused: **SVO** (`p3-sumcheck/src/svo/`,
eprint 2025/1117 Alg. 5 — never materializes the 2^l eq table, O(3^l) not
O(6^l)); and **`p3-security`**, a mechanized SecurityAssumption with BCSS25
Thm 1.5 encoded — **an independent implementation to cross-check `FriLedger`
against.** ⚠ One tension to resolve: theirs says d=5 reaches 128 with
KoalaBear; our `PROVEN-120-CONFIG.md` says d=5 cannot reach 120. Probably
scope (RS proximity leg vs whole apex composite) — **check, don't assume.**

## ⚑ Constraint degree is a SPACE knob, not a time knob

Ceno reverted a *correct* degree-3 lowering, verbatim: *"a side effect is
performance regressed due to the new resident column bring more overhead to
GPU vram which reduce the multi-tower concurrency scheduling."* Degree `d`
costs `d+1` evaluations per round — **linear, paid in time**. Lowering `d`
costs committed columns — **paid in space.** On any memory-scheduled device
the columns win. OpenVM can afford degree 3 only *because* its univariate skip
shrinks the extension buffer **16×** (26.05 GiB → 1.63 GiB at production
l_skip=4). **Price both sides before setting a degree bound.**

## In a GKR arrangement the PCS stops being the bottleneck

Ceno's committed measurements (real block, self-hosted GPU): `pcs_opening`
**15.2 s** and `commit_traces` **6.9 s** — *invariant across every
configuration* — while the sumcheck tower ran **176 s → 24.9 s** and remained
the largest line. **If you choose a substrate assuming the hash PCS dominates,
that assumption inverts under GKR.**

## Binius64's retreat, recorded as a deletion not an essay

The field crate went **27,028 → 16,838 lines (−38%)**. The team that invented
bit-granular tower commitments **kept only the two endpoints of their tower**
— GF(2) for witness bits, GF(2^128) for challenges — and moved to GHASH, *the
field the CPU has an instruction for*. `BinaryField{2b,4b,16b,32b,64b}` and
`TowerLevel` now have **zero references**.

**And the cost relocated rather than vanishing**: "XOR is free" is paid for by
a 4,163-line shift-reduction prover, and **~90% of XMSS verification is
`shift::check_eval`** — re-deriving the circuit's wiring. **The transferable
rule: any encoding trick that makes a class of gate vanish must be priced by
what the WIRING argument then costs.**

## Corrections to our record

- ⚠ **The "160×RTX4090 → 16×RTX5090 in six months from software alone" claim
  is NOT substantiated anywhere in the SP1 repo** — every `perf(gpu)` commit
  body is just its title. I have quoted it. The *mechanism* is real and
  documented (VRAM tier sets shard size; ≤30 GB cards get ~29% smaller
  shards), but the factor is not.
- **SP1's only Hypercube audit lists "precise claims about the bits of
  security" under NON-GOALS** and calls the code *"prototype state"* (3
  critical / 7 high). Cite their 100 bits as a target constant, not a result.
- ⚠ `~/src/leanMultisig` is a **dead 8-commit personal fork** — re-clone
  `leanEthereum/leanMultisig`.
- **leanVM's KoalaBear⁵ has a reason and a hidden cost**: an assertion
  `field_size_bits > security_level` with SECURITY_BITS=124 (4×31=124 fails).
  And **5 ∤ (p−1), so no binomial quintic extension of KoalaBear exists** —
  the trinomial costs 25 base mults vs ~16 for a binomial quartic, **≈1.5–1.6×
  per extension multiply.** *Check your prime's factorization before
  committing to an extension degree.*
- **Plonky3 has no GKR** (zero hits) and `p3-lookup` materializes permutation
  columns. Every system here either left Plonky3 or built the GKR layer
  itself. **That is the size of the LogUp-GKR move: build, not adopt.**

## The lesson worth stealing, in their words

Binius64, after a gate that could not go red for weeks (fix: **−15 lines**):
> **"The filler stops judging. It reads the transcript and fills wires; the
> circuit decides."**

In a Lean-authored setting the analogue is: **any emitter or witness generator
that validates its own output is a gate that cannot go red. The emitted object
must be the only thing that can reject.**
