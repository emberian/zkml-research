# The prover floor, derived — and the wall and the floor are the same object

2026-08-13. `paper/scripts/prover_floor.py`. **The design artifact the
verification phase was crowding out.**

## The one-sentence result

**The prover is hash-bound at every blowup ≥ 2, and the floor is hashing too.
The sumcheck is 2–17% of prover time — so a 2× on the sumcheck is a
1.02–1.17× on the prover.** That re-prices most of the speedup literature,
including several things we spent days evaluating.

## The cost function (per committed base felt, blowup 2^b, width w, height h)

- **hash** = `2^b·(1/8 + 2/w)` permutations — **dominant, ∝ blowup**
- **encode** = `(2^b+1)·log₂h/2` mults
- **sumcheck** = `(d−1)·k·10` mults — **independent of b**
- **opening** — negligible, because FRI batches all `w` columns into **one**
  codeword before folding. (That derives DeepProve's otherwise-odd
  56.85%-commit / 1.04%-open split.)

At w=48, h=2²⁰: b=1 → 84% hash; **b=6 (deployed) → 94% hash, and 28.4× the
b=1 cost.** Cross-check: derived native BabyBear/KoalaBear permutation ratio
1.69× vs the in-circuit measurement 1.82× — two instruments, 4% apart.

## ⚑ Matmul vs trace: 5,461× at n=4096, and the general statement

**The AIR commits the interior of the relation; the sumcheck commits its
boundary.** The interior of a bilinear form is n³, its boundary n². An AIR
must *contain every multiply-accumulate it constrains* (n³ rows); the sumcheck
commits only A, B, C (3n²). **Ratio = 4n/3, i.e. Θ(n).**

## ⚑ Thaler's 0.18–0.33% is the B≈n case, and it does not apply to decode

Overhead = `1/B + 1/n`. At B=512 that is **0.220%** — reproducing the cited
band exactly. **At B=1 it is 100.02%.** **Autoregressive decode IS B=1.** The
most-cited number in sumcheck-for-ML does not apply to the workload everyone
wants to prove, and we have been quoting it.

## ⚑ Correction to my own brief, and a proof instead of a ratio

**The 98,304-equation family does NOT cover fold_add** — it proves a fresh
*encryption* (`ct₀ = u·pk₀ + e₀ + Δm`). **fold_add, ct×pt and ct×ct have no
AIR at all.** And **pk is public**, so that whole 1,032,192-row butterfly
family commits **the interior of a public linear map**. By sumcheck: **86× at
matched blowup, 103× with a proof-field-matched limb, 406× against the
deployed lb=6 point** (10.5× butterfly network × 2.0× 36-bit limbs in a
31-bit field × 2.0× the carries/ranges emulation forces).

**For fold_add there is a PROOF, not a ratio.** MLE is a *linear* map, so
`c_out = Σaₖcₖ ⟹ ĉ_out = Σaₖĉₖ` as polynomials — **one common-point opening
certifies it. Zero sumcheck rounds, zero carries, zero range checks.** The
side condition (no reduction) is met by lazy accumulation, **which h2 already
measured at 0.88× — faster on the FHE side too.** AIR cost is Θ(B·N·L)
(proportional to the *additions*); the linear route is Θ(N·L) (proportional
to the *result*). **Ratio = B — 690× at B=512, ⚠ PROVER-SIDE ONLY** (2026-08-13: the verifier moves the *opposite* way — B+1 openings against B+1 commitments is O(B) Merkle work vs a polylogarithmic AIR verifier, and the one-shared-tree fix collides with the per-trader-root binding condition).

And ct×ct's entire cost is the range checks on key-switch digits, which in
RNS-BV *are* the limbs — so a matched limb deletes a third by construction.

## The commitment floor, and what it does to the field choice

Proved two ways (Ω(|w|) reads; Ω(H(w)) bits through the oracle). **Irreducible
AND dominant**, so exactly three levers: fewer committed values, smaller ones,
more bits per unit ALU.

⚑ **It changes the field choice for a stronger reason than the field memo
gave**: the only figure of merit a hash has is bits/op — **Poseidon2-KoalaBear
0.301 vs BabyBear 0.227** — *and* **α=3 makes lb=2 legal** (measured: 38 of 91
goldens refuse lb=2 today because the α=7 S-box needs a degree-6 quotient).
**So the migration is ~3.4× on the dominant term, not ~1.5×.**

## Small values: the literature pushes on the smaller half

34 committed elements per site = 10 base columns + 6 lookups × 4 base felts —
**71% of every committed element in a zkML proof is a LogUp extension-field
aux column.** Against an 8-bit activation the blow-up is 132× = **3.88× field
embedding × 34× protocol.** The protocol half is 34× and the packing half is
3.9×; **the small-value literature attacks the 3.9×.**

## ⚑ Three things to act on

1. **`lb=6` is 2.9× off the measured optimum and buys a WITHDRAWN regime.**
   Measured: **20 ms at lb=4 vs 58 ms at lb=6.** lb=6 yields 34 proven UDR
   bits; the 130 it was chosen for is the **CBR column `ethereum/soundcalc`
   deleted.** *This is a config constant.*
2. **In-circuit Merkle authentication is 15.2× in our own tree** (`map_write_chip`
   227 ms vs `umem_write_read_nochip` 14.9 ms) **and the cheaper path is
   already built.** It re-derives, inside an argument that already carries a
   vector commitment, a fact the PCS could establish as an opening.
3. **Lookup batching is a trap: 0.62×, a net loss.** 34→14 elements/site
   (2.43×) but degree 7 forces lb≥6 (3.95× dearer). *Aux columns ↔ constraint
   degree ↔ blowup ↔ hash work is the whole cost structure in one chain.*

## The honest gap

Floor → best-known: **~1,200× (ML forward pass), ~86–103× (BFV), ~10,000×
(turn).** **Almost none of it is the sumcheck and almost none is asymptotic**
— it is *committing derivable values, in a field 4× wider than they are, under
a code 64× longer than it needs to be.* Compounded substrate levers: **8–15×**
honestly, since blowup/field/hash act on the same term and do not multiply
cleanly.

## Named inadequacies

The per-element model over-predicts below lb=4 (query work dominates there);
ext-mult priced at 9 base mults; the Blake3 ratio is 6–10× depending on
modular-add cost; **the BFV sumcheck route is a cost derivation, not a built
system** — the domain-change sumcheck and the multilinear-commitment seam are
both unbuilt, and the seam is a campaign; the turn's ~733-felt witness is a
shape estimate.
