# Field-operation counts for the IR-v2 prover — the missing half of the instrument

**Status: COMPLETE (2026-08-14).** Every section below is `[MEASURED]` or `[COUNTED KERNEL /
DERIVED MULTIPLICITY]`, labelled where it matters. One instrument (§G5) failed on this box and
says so in §6 rather than being quietly dropped.

**Why this exists.** `docs/COST-MODEL.md`'s retraction states the problem exactly: we have
*exact* Poseidon2 permutation counts and *zero* field-operation counts, so the claim "the prover
is hash-bound at every feasible blowup" compares an exact count against a contended clock. That
comparison is not sound, and it is not sound in the specific direction that matters: hash work is
a large-buffer traversal (memory-bound) and field arithmetic is cache-resident (compute-bound), so
under load they degrade at *different rates*. `hash/arith` is the single quantity a busy box
corrupts most.

Harness: `breadstuffs/circuit/tests/ir2_field_op_counts.rs` (§G1–§G5 below are its test names).
Companion to `circuit/tests/ir2_phase_profile.rs` §A–§F.

---

## 0. ⚑ The approach, and why the obvious one does not work

**The obvious instrument fails on a bound, and the bound is real.** Mirroring §D — wrap `BabyBear`
in a counting newtype, prove under a config over it — cannot reach this prover:

```rust
pub fn prove_vm_descriptor2_for_config<SC>(..., base_trace: &[Vec<BabyBear>], ...) -> ...
where
    SC: StarkGenericConfig,
    Domain<SC>: PolynomialSpace<Val = P3BabyBear>,      // ← Val is PINNED
```

`Val` is pinned to `P3BabyBear`, and the trace argument is concrete `Vec<Vec<BabyBear>>` produced
by monomorphic witness generation (`generate_effect_vm_trace`, the Poseidon2 chip lanes, the
heap-root and mem-boundary builders). Note that the **AIR itself is field-generic** —
`impl<AB> Air<AB> for Ir2Air where AB::F: PrimeField32` — so the obstruction is the *witness*, not
the constraint system. Making witness generation generic is a real refactor of deployed code, and
this lane does not move deployed types, for the same reason §D did not.

**What is substitutable at zero cost is one seam over: the `Dft` type parameter.**

```rust
pub struct TwoAdicFriPcs<Val, Dft, InputMmcs, FriMmcs, Fold = CpuTwoAdicFriFold> { .. }
//                            ^^^  free parameter over TwoAdicSubgroupDft<Val>
```

Exactly as the Poseidon2 permutation was a free parameter of the hash/compress types. And this is
worth more than it sounds, because of *where* the arithmetic is. From `ir2_phase_profile.rs` §A at
b=6:

| arith phase | ms | share of arith |
|---|---:|---:|
| LDE quotient-eval | 12.925 | 50% |
| LDE commit | 7.710 | 30% |
| open arith (quotient reduce) | 3.545 | 14% |
| quotient eval | 1.283 | 5% |
| lookup perm | 0.246 | 1% |
| FRI fold | 0.072 | 0.3% |

**80% of the prover's arithmetic is DFT at b=6** — but only **46% at b=3**, which is precisely
where the crossover sits. So the DFT count is the bulk of the answer at the deployed point and
only half of it at the interesting one. Both facts are load-bearing below.

### The three parts

1. **Record.** `RecordingDft` implements `TwoAdicSubgroupDft<P3BabyBear>` by delegating every
   method to a real `Radix2DitParallel<P3BabyBear>` and logging `(method, height, width,
   added_bits, shift)`. The proof is bit-identical to the deployed one; the added work is a
   `Vec::push` per DFT call, and calls number in the dozens.
2. **Replay.** The recorded sequence is replayed *in order* against
   `Radix2DitParallel<CountedBabyBear>`, a `repr(transparent)` newtype whose
   `Add`/`Sub`/`Mul`/`Neg`/`try_inverse` bump global counters. In order, and against a *single*
   instance, because the DFT memoises twiddle tables — replaying out of order or with a fresh
   instance per call would charge twiddle construction repeatedly and over-count.
3. **Derive** the non-DFT arithmetic from the (vendored, readable) source, checked in shape
   against counted DFT cases.

### Why replay on synthetic data is exact

Replay uses matrices of the *recorded dimensions* filled with an arbitrary pattern. That is exact
because `Radix2DitParallel`'s op count is a function of `(h, w, added_bits)` alone: every branch in
`first_half` / `second_half` / `coset_dft` is on a layer index or a twiddle *position*
(`dit_layer_twiddle_free` fires at layer 0 and at the first row-pair of each block — structural,
never a value test). The only value-dependent path in the file is `try_inverse`'s zero check, which
the DFT reaches with `shift.inverse()` and `F::from_int(h).try_inverse()` — non-zero constants that
replay reproduces exactly, because the shift is recorded as its canonical `u32`.

---

## 1. ⚑⚑ SCALAR-EQUIVALENT, NOT INSTRUCTIONS — the choice and its consequence

**Every count here is a scalar-equivalent operation count: how many BabyBear
multiplications/additions the ALGORITHM performs, independent of how many the machine issues per
instruction.**

It is scalar-equivalent *by construction*, not by convention. `CountedBabyBear::Packing = Self`
(plonky3's blanket `unsafe impl<T: Packable> PackedValue for T`, `WIDTH = 1`), so `p3-dft`'s packed
butterflies — `F::Packing::pack_slice_with_suffix_mut(row)` — degrade to width-1 packs and every
lane is counted individually. **This does not change the algorithm**: a butterfly is applied to
every element of every row-pair either way, so the width-1 replay and the deployed NEON width-4 run
perform the same scalar-equivalent work.

**Why this unit and not instructions:** §D already reports permutations in exactly this unit ("a
packed `permute_mut` adds `Packing::WIDTH`"). The two instruments therefore compose in one unit,
which is the entire point of building this one.

**The consequence, stated because it is the whole reason wall clock and op count diverge:**

- A scalar-equivalent count measures **work**, not instructions and not latency.
- On this box `<BabyBear as Field>::Packing` is `PackedMontyField31Neon`, **WIDTH = 4**. The
  deployed prover issues roughly one instruction per 4 counted multiplies wherever the path
  vectorises.
- **The hash side vectorises too** (§D: the Merkle build and the PoW grind are both packed; only
  the challenger's ordinary duplexing is scalar, ~4,830 permutations in the whole proof). So the
  SIMD factor does *not* cancel out of the comparison automatically — it has to be handled on both
  sides, and it is: §G3 measures the conversion rate as a **packed-path lane rate on both sides**.
- **A count in this file may not be converted to milliseconds by multiplying by a scalar-latency
  rate.** Doing so would inflate the arithmetic side by the SIMD factor (~4× here) and is exactly
  the error that would manufacture a "hash-bound" verdict.

The instruction-count question is a *different* question with a different answer: divide each
phase's scalar-equivalent count by the SIMD width of the path that executes it. The work count is
hardware-free and reproducible by anyone; the instruction count is a property of this box.

---

## 2. Per-phase field-op counts `[MEASURED]`

`§G1`, `field_op_counts_per_phase`. Workload: the same real transfer effect §D counted
permutations on (`transferVmDescriptor2`, `CellState::new(100_000, 0)`, one `Transfer`), at
`q = 19`, `pow = 0`. Configuration recorded with every number, per the cost model's rule 1.

### Scalar-equivalent field operations, DFT phases, exact

Six DFT calls land outside the `compute quotient` span and twelve inside it, at every blowup.

| b | LDE commit (6 calls) | LDE quotient-eval (12 calls) | **DFT total** | DFT MUL only |
|---:|---:|---:|---:|---:|
| 3 | 1,725,147 | 62,255 | **1,787,402** | 594,362 |
| 4 | 3,266,179 | 118,502 | **3,384,681** | 1,131,161 |
| 5 | 6,348,387 | 231,284 | **6,579,671** | 2,205,191 |
| 6 | 12,513,091 | 457,424 | **12,970,515** | 4,354,115 |
| 7 | 24,843,075 | 910,856 | **25,753,931** | 8,653,691 |

Every phase is `Θ(2^b)`: the DFT total goes 1.89× · 1.94× · 1.97× · 1.99× per rung, converging on
2 exactly as the LDE's closed form predicts. **The quotient-eval share is a flat 3.5% at every
blowup** (3.48 / 3.50 / 3.52 / 3.53 / 3.54%).

### ⚑ FINDING 1 — the profile's "LDE quotient-eval" is not what its own note says it is

The recorder logs the **enclosing span path** at each DFT call, so the phase split here is computed
by `ir2_phase_profile.rs`'s own predicate rather than by a re-derivation of it. At b=6, in call
order:

```
  #     h      w   +b          MUL          ADD          SUB   span path
  0    64    236    6      2955163      2945280      2945280   prove_batch
  1     8    386    6       301724       301080       301080   prove_batch
  2    16      2    6         6468         4160         4160   prove_batch
  3    64     72    6       897416       898560       898560   prove_batch
  4     8     12    6         9916         9360         9360   prove_batch
  5    16      4    6         8884         8320         8320   prove_batch
  6    64      4    6        65256        49920        49920   prove_batch>compute quotient
  7    64      4    6        57832        49920        49920   prove_batch>compute quotient
  8..15  8     4    6      ~3800 ea      3120 ea      3120 ea   prove_batch>compute quotient
 16,17  16     4    6       ~10000 ea     8320 ea      8320 ea   prove_batch>compute quotient
```

**Zero `coset_idft_batch` calls. Zero `coset_dft_batch` calls. At every blowup.** So:

> `phase-profile.md` §2: *"`LDE quotient-eval` is consistently ~1.7× `LDE commit`. That is
> `get_evaluations_on_domain` taking its slow path (iDFT the committed LDE back to coefficients,
> then coset-DFT onto the quotient domain) rather than truncating. It is the largest single
> arithmetic term at every blowup and looks like a live optimisation target."*

**Refuted on both counts.** `get_evaluations_on_domain`'s slow path is *never taken* — the fast
truncation branch (`domain.shift() == Val::GENERATOR && lde.height() >= domain.size()`) fires every
time, and produces no DFT call at all. What the profile labels "LDE quotient-eval" is the **twelve
width-4 quotient-CHUNK LDE commits** from `get_quotient_ldes`, which sit under the `compute
quotient` span because `p3-batch-stark` enters that span as an RAII guard for the whole per-AIR
loop body.

And it is **not the largest arithmetic term**: it is **3.5%** of the LDE's arithmetic
(457,424 of 12,970,515 ops), against the 96.5% carried by the six trace/preprocessed/permutation
commits.

### ⚑⚑ FINDING 2 — the phase carrying 3.5% of the arithmetic is measured at 63% of the time

| at b=6 | counted ops | §A measured ms | ms per Mop |
|---|---:|---:|---:|
| LDE commit (6 calls) | 12,513,091 | 7.710 | **0.62** |
| LDE quotient-eval (12 calls) | 457,424 | 12.925 | **28.3** |

**A factor of 46 between two phases doing the same kind of work.** Both cannot be statements about
arithmetic. Either the LDE's time is overwhelmingly *not* field operations, or that harness
mis-attributes — and §G5 settles which without a whole-prover clock. See §6.

This is exactly the class the cost model's rule 5 names: *"When a new measurement contradicts a
share, that is a finding, not a discrepancy to average away."*

### The non-DFT arithmetic `[COUNTED KERNELS, DERIVED MULTIPLICITY]`

`§G4`. The DFT is 80% of the arithmetic at b=6 but only ~46% at b=3, so the remainder is
load-bearing at the interesting end. It is reached through `p3-fri::open`, which is behind no
substitutable type parameter — so instead each **kernel** that phase is built from is *called* over
the counting field at the geometry the recorder observed. Extension primitives, counted not
assumed:

| kernel | MUL | ADD | SUB | INV |
|---|---:|---:|---:|---:|
| ext × ext | **19** | 12 | 0 | 0 |
| ext × base | 4 | 0 | 0 | 0 |
| ext + ext | 0 | 4 | 0 | 0 |
| ext − ext | 0 | 0 | 4 | 0 |
| ext inverse | 23 | 11 | 0 | 1 |

⚠ **One stated fidelity gap.** `MontyField31` overrides `binomial_mul` with `quartic_mul_packed`
(4 multiplies by W + a 4×4 packed dot product = **20**); the counting field has no such override
and takes the generic `quartic_mul`, which shares subterms down to **19**. The counting extension
is therefore ~5% *cheaper* per extension multiply than the deployed one — it **under-states**
arithmetic, which is the conservative direction for a hash-bound claim.

FRI fold, counted directly through the public generic `CpuTwoAdicFriFold`: **28.0 multiplies per
folded row** at arity 2, stable across heights (28.4 / 28.1 / 28.0 at 512 / 2048 / 8192 input rows).

Open phase, kernels counted and multiplicities derived **upward** (P = 2 opening points assumed for
every committed matrix, an over-count — quotient chunks are opened at zeta only):

| b | mats | open MUL | open ADD+SUB | **open total** |
|---:|---:|---:|---:|---:|
| 3 | 18 | 1,973,660 | 1,755,662 | **3,729,332** |
| 4 | 18 | 3,039,644 | 2,753,038 | **5,792,692** |
| 5 | 18 | 5,171,612 | 4,747,790 | **9,919,412** |
| 6 | 18 | 9,435,548 | 8,737,294 | **18,172,852** |
| 7 | 18 | 17,963,420 | 16,716,302 | **34,679,732** |

**This bound is validated, not merely asserted.** At b=6 it predicts
`9,435,548 × 0.1805 ns + 8,737,294 × 0.1450 ns = 2.97 ms` against §A's measured **3.545 ms** for
"open arith" — **84% of the phase's time explained by its counted operations.** That agreement is
what licenses using the bound in the verdict.

---

## 3. The derivation check — and why the count had to be taken, not derived `[MEASURED]`

`§G2`, `dft_derivation_check`. Textbook radix-2 DIT is `(h/2)·w·log₂h` butterflies, each one
multiply + one add + one sub. Counted against that on a plain `dft_batch`:

| h | w | MUL counted | MUL textbook | ratio | ADD counted | ADD ratio |
|---:|---:|---:|---:|---:|---:|---:|
| 64 | 8 | 1,203 | 1,536 | **0.783** | 1,536 | **1.000** |
| 256 | 8 | 6,496 | 8,192 | **0.793** | 8,192 | **1.000** |
| 1024 | 8 | 33,635 | 40,960 | **0.821** | 40,960 | **1.000** |
| 4096 | 8 | 166,502 | 196,608 | **0.847** | 196,608 | **1.000** |
| 1024 | 64 | 264,192 | 327,680 | **0.806** | 327,680 | **1.000** |

**The ADD ratio is exactly 1.000 at every size. That is the instrument validating itself** — the
counting field reproduces the textbook additive structure to the unit, so the counter is not
dropping or double-charging operations.

**The MUL ratio is 0.78–0.85, and the gap is real code, not error.**
`dit_layer_twiddle_free` and `dit_layer_first_one` skip the multiply wherever the twiddle equals
one — all of layer 0, and the first row-pair of every block in every later layer. So:

⚑ **A hand-derived butterfly count over-charges the multiplies by 18–22% and gets the adds exactly
right.** That asymmetry is invisible to anyone deriving from the algorithm's shape, and it is the
argument for counting rather than deriving. (It also rises with `h`: 0.783 at h=64 to 0.847 at
h=4096, because the twiddle-free savings are a per-block constant that the block count dilutes.)

Coset LDE at the shape the prover actually calls, same instrument:

| h | w | +b | MUL | ADD | SUB |
|---:|---:|---:|---:|---:|---:|
| 64 | 8 | 3 | 15,647 | 13,824 | 13,824 |
| 64 | 8 | 6 | 113,224 | 99,840 | 99,840 |
| 256 | 8 | 3 | 78,148 | 73,728 | 73,728 |
| 256 | 8 | 6 | 567,456 | 532,480 | 532,480 |

An `h → h·2^b` coset LDE is one iDFT of size `h` plus `2^b` coset DFTs of size `h`, so the multiply
term is `Θ(2^b · h · log h)` — **linear in the blowup**, which is why the LDE phases double per rung
in the §A timing table. The ratio 113,224 / 15,647 = 7.24 for a 8× blowup increase confirms it
(sub-linear only because the shared iDFT is amortised).

---

## 4. The conversion rate `[MEASURED]`

`§G3`, `conversion_rate_microbenchmark`. Estimator: **min over N = 4,000 windows of 4,096 packed
operations each**, one thread. Short windows, many of them — a window is ~3 µs, so a clean sample
needs only one un-preempted window out of four thousand. An 80 ms whole-prover timing has no such
escape, which is the whole reason this is the only timing in the lane.

**Both sides measured in the same unit: packed-path, throughput-bound, per-lane (scalar-equivalent).**

| quantity | value |
|---|---:|
| packed multiply | 0.722 ns/call = **0.1805 ns per scalar-equivalent multiply** |
| scalar multiply | 0.661 ns (**SIMD factor 3.66×** — near the theoretical 4) |
| packed add | 0.580 ns/call = **0.1450 ns per scalar-equivalent add** |
| packed Poseidon2 | 648.19 ns/call = **162.05 ns per scalar-equivalent permutation** |
| scalar inverse | 103.5 ns = **573 multiplies' worth** |

### ⚑ **Y = 897.6** — one Poseidon2 permutation costs ~898 BabyBear multiplies

Independent sanity check on Y: a Poseidon2-16 permutation over BabyBear is 8 external rounds
(16 S-boxes each, `x⁷` = 4 multiplies) plus 13 internal rounds (1 S-box each) ≈ **564 multiplies**
of arithmetic, plus the MDS/diffusion additions. A *time* ratio of 898 against a *count* ratio of
564 is exactly the right shape — the excess is the additions and the round-constant adds. **The
exchange rate is not a free parameter; it is pinned by what the permutation computes.**

Note also what the SIMD factor does here: comparing a packed permutation against a **scalar**
multiply would have given Y ≈ 245 instead of 898. Getting the unit wrong on one side is a 3.7×
error in the quantity the whole verdict turns on.

### Y across working sets — the one place the retraction's premise could have bitten

`§G3b`. The retraction's reasoning was that hash work is memory-bound and arithmetic is
cache-resident, so a rate measured in cache would not transfer. That is a real hazard: the
committed LDE buffer is 6.3 MB at b=6. Measured across working sets (min of 200 windows each):

| buffer | ns / multiply (lane) | ns / permutation (lane) | **Y** |
|---:|---:|---:|---:|
| 32 KB | 0.1373 | 159.42 | 1160.9 |
| 512 KB | 0.1481 | 162.32 | 1095.7 |
| 4 MB | 0.1620 | 162.81 | 1005.2 |
| 16 MB | 0.1852 | 164.75 | **889.8** |

**Y moves by only 1.3× across a 512× change in working set**, because a Poseidon2 permutation does
~560 multiplies per 64-byte state (compute-bound at every size) while a bare multiply is one
operation per element (bandwidth-exposed once it leaves cache). So the hazard is real but small,
and it is bounded: **Y ≥ 890 anywhere in the range the prover operates.** The verdict below uses
that floor, not the flattering 1161.

---

## 5. ⚑ THE HASH-BOUND VERDICT — as a conditional on a measured ratio

### The statement

Let `P` be scalar-equivalent Poseidon2 permutations, `M` scalar-equivalent multiplies, `A`
scalar-equivalent adds+subs, and `r = t_add/t_mul = 0.803` (measured).

> **The prover is hash-bound iff `Y > X`, where `X ≡ (M + r·A) / P` and `Y ≡ t_perm / t_mul`.**

`X` is exact and hardware-free — it is a property of the algorithm at a configuration and nothing
else. `Y` is the single measured constant, and it is the *only* place a clock enters.

### X, computed from the counts (arithmetic = counted DFT + §G4's upward-bounded open phase)

| b | P (perms, §D) | M | A | **X** | Y/X margin at Y=890 |
|---:|---:|---:|---:|---:|---:|
| 3 | 27,778 | 2,568,022 | 2,948,702 | **177.7** | **5.01×** |
| 4 | 54,826 | 4,170,805 | 5,006,558 | **149.4** | **5.96×** |
| 5 | 108,922 | 7,376,803 | 9,122,270 | **135.0** | **6.59×** |
| 6 | 217,114 | 13,789,663 | 17,353,694 | **127.7** | **6.97×** |
| 7 | 433,498 | 26,617,111 | 33,816,542 | **124.0** | **7.18×** |

### ⚑ THE VERDICT

> **Hash-bound iff the conversion rate exceeds X = 178 (worst case, b=3) — and the measured rate
> is Y = 890 at the largest working set, 898 at the primary estimator, 1161 in cache.**
>
> **The prover is hash-bound at every feasible blowup, by a factor of 5.0× to 7.2×, and there is
> no crossover anywhere in `b ∈ {3,…,7}`.** The margin *narrows* as `b` falls, but at the b=3 floor
> it is still 5×: reaching parity would need the hash work cut by 5× or the arithmetic raised by 5×.

This is now a **count-vs-count** comparison with one measured constant, not a count-vs-clock
comparison. `COST-MODEL.md`'s demotion of "hash-bound at every feasible blowup" to *unproven* can
be lifted — **for the work claim.** It cannot be lifted for the time claim, and §6 is why.

### Every approximation in X points the same way

Each one makes X *larger*, i.e. makes hash-bound *harder* to conclude:

- The open phase assumes **P = 2 opening points for every committed matrix**; quotient chunks are
  opened at zeta only.
- The counting extension's `quartic_mul` is **19 multiplies where the deployed
  `quartic_mul_packed` is 20** — so extension arithmetic is under-priced by ~5%.
- `P` **excludes the PoW grind** (47,917 more scalar-equivalent permutations at the deployed
  pow=16, blowup-independent). Including it at b=6 takes X from 127.7 to 104.6 and the margin from
  7.0× to 8.5×.
- Not counted at all: `quotient eval` and `lookup perm` (§A: 1.283 + 0.246 ms at b=6, both flat in
  b). Even charging them at the *whole* arith rate would move X by well under the 5× margin.

⚠ **What is NOT bounded this way:** an inverse is charged as one event, not decomposed. §G3
measures one scalar inverse at 103.5 ns = **573 multiplies' worth**, and the counted `INV` totals
are 3 per proof in the DFT and one per batch inversion in the open phase — call it O(10). Ten
inverses is ~5,700 multiply-equivalents against 13.8 million. Negligible, and now on the record.

---

## 6. ⚑⚑ WHAT THE COUNTS EXPOSE THAT NO CLOCK COULD — and a premise that was backwards

With both sides exact, the two instruments can be asked a question neither could answer alone:
**how much of each phase's measured time is accounted for by its counted operations?**

At b=6, q=19, pow=0, using §A's per-phase minima and §G3's rates:

| phase | counted work | predicted ms | §A measured ms | **explained** |
|---|---|---:|---:|---:|
| Merkle-commit + FRI-fold Merkle | 216,378 perms | 35.06 | 43.71 | **80%** |
| open arith | 9.44 M mul + 8.74 M add | 2.97 | 3.55 | **84%** |
| **LDE commit (6 calls)** | 4.18 M mul + 8.33 M add | **1.96** | **7.71** | **25%** |
| **LDE quotient-eval (12 calls)** | 0.17 M mul + 0.28 M add | **0.073** | **12.93** | **0.6%** |

### The premise in `COST-MODEL.md`'s retraction is inverted at this geometry

> *"hash work (large-buffer traversal, memory-bound) and field arithmetic (cache-resident,
> compute-bound) degrade at different rates under contention"*

Measured, it is the **hash** side whose time is accounted for by its operation count (80%), and the
**arithmetic** side whose time is mostly *not* operations (19% overall, 0.6% in the phase that
carries the most measured time). The hash phase is compute-bound and behaves like its count; the
LDE phase does not.

The retraction's *conclusion* — that operation counts are the primary instrument on this box — is
right, and this is a second, independent reason for it: **counts are the only way to see that a
phase's time is not its work.** A clock cannot distinguish "expensive arithmetic" from "cheap
arithmetic wrapped in expensive movement", and that distinction decides whether an arithmetic
optimisation is worth anything.

### ⚑ FINDING 3 — a live optimisation target, correctly diagnosed for the first time

`phase-profile.md` flagged "LDE quotient-eval" as *"the largest single arithmetic term at every
blowup"* and *"a live optimisation target"*, diagnosing it as `get_evaluations_on_domain` taking a
slow iDFT+DFT path. **The diagnosis is wrong** (that path is never taken — zero such calls at every
blowup) **but the target is real, for a different reason:**

- It is **twelve separate `coset_lde_batch` calls on width-4 matrices** — the quotient chunks, one
  per chunk, each committed independently.
- It carries **3.5% of the LDE's arithmetic** and, per §A, **63% of the LDE's time**.
- Per call, the two LDE phases cost almost the same: **7.710/6 = 1.285 ms** and
  **12.925/12 = 1.077 ms** — within 19% of each other, while their per-call *work* differs by 27×.

**The cost is per-CALL and per-narrow-matrix, not per-operation.** A width-4 BabyBear matrix is
exactly one NEON vector per row, so every per-row cost — twiddle load, bit-reversed index, bounds
check, and the `1..2^b` coset loop's per-coset twiddle-map lookup — is paid against 4 lanes instead
of amortised across a 236-wide row. The chunks group by height (2 at h=64, 2 at h=16, 8 at h=8), so
**batching them into three matrices of width 8/8/32 instead of twelve of width 4** is the shape of
the fix. That is a data-layout change, not an arithmetic one — which is why an arithmetic
optimisation aimed at this phase would have bought nothing, and why the previous diagnosis would
have sent someone to fix a branch that never executes.

### ⚠ An instrument that did NOT work, reported as such

`§G5` tried to settle the per-call question directly: replay each recorded geometry as a standalone
`Radix2DitParallel<P3BabyBear>` kernel, min-of-25, no prover. **It failed on this box.** Every
geometry hit the same ~2.7–6.0 ms floor — a **14,788-op** call measured 3,773 µs and a **903,884-op**
call measured 3,625 µs, i.e. 61× the work in *less* time. A floor that flat and that far above the
work is a scheduling artifact (rayon dispatch against load average 50–80), not a measurement.
**The `ns/op` column §G5 prints is not evidence and is not used above.**

What settles Finding 3 instead is arithmetic on numbers already in hand: §A's own per-phase ms
divided by this lane's exact call counts and op counts. No new clock.

**What would settle the per-call constant properly:** the same §G5 kernel sweep on a quiet machine,
or with `RAYON_NUM_THREADS=1` to remove dispatch, sweeping width at fixed total element count
(w ∈ {4, 8, 16, 64, 256} at constant h·w) — which isolates the width effect from the size effect.
That is the next measurement, and it is cheap.

---

## 7. What is now reusable

`circuit/tests/ir2_field_op_counts.rs` is the arithmetic half of the instrument §D was the hash
half of. **No deployed constant, config or type moves** — the only Cargo change is a `num-bigint`
dev-dependency (already in the lock via `p3-field`; `Field::order()`'s required signature has to
name `BigUint`).

| section | test | what it gives |
|---|---|---|
| §G1 | `field_op_counts_per_phase` | exact per-phase, per-blowup field-op counts + the ordered DFT call log with span paths |
| §G2 | `dft_derivation_check` | closed form vs counted; validates the counter (ADD ratio 1.000) |
| §G3 | `conversion_rate_microbenchmark` | Y, both sides in scalar-equivalent packed-lane units, + the working-set sweep |
| §G4 | `open_phase_and_extension_primitives` | counted extension primitives, counted FRI fold, bounded open phase |
| §G5 | `lde_time_per_counted_operation` | ⚠ does not work on a loaded box; keep for a quiet one |

**Reach and limits.** The counting field cannot be instantiated as the prover's `Val` — `Domain<SC>:
PolynomialSpace<Val = P3BabyBear>` and monomorphic witness generation forbid it. It reaches the DFT
through the `Dft` type parameter and the extension/FRI kernels by direct call. The two phases it
does **not** reach are `quotient eval` and `lookup perm` (§A: 1.28 + 0.25 ms at b=6, both flat in
`b`, together ~6% of arith time). Reaching them means either evaluating `Ir2Air` through a counting
`AirBuilder` — the AIR *is* generic (`AB::F: PrimeField32`), so this is possible and is the obvious
next extension — or making witness generation field-generic, which is a real refactor.
