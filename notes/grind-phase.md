# The PoW grind — what 16 bits buy, what they cost, and what to do about the variance

**Measured 2026-08-13/14.** Companion to `notes/phase-profile.md` §4, which named the phase:
`query_proof_of_work_bits = 16` is **47,917 Poseidon2 permutations, ~25% of a deployed IR-v2
prove**, depends on **neither blowup nor trace size**, and drew `0.04 / 8.2 / 10.1 / 31.9 / 40.0 /
40.8 ms` across one parity ladder — a spread that manufactured a false optimum.

Instruments:
* `breadstuffs/circuit/tests/grind_phase_measure.rs` (§G1–§G5), new.
* `minidregg/Assurance/TwoRegimeQueryBudget.lean` §7, new — the exchange rate as named two-sided
  theorems over exact ℚ, kernel-checked.
* Code reading of `vendor/plonky3-challenger-82cfad73/src/grinding_challenger.rs` and
  `vendor/plonky3-fri-82cfad73/src/prover.rs`.

---

## 0. Where the grind is, and what it is grinding — read, not inferred

`vendor/plonky3-fri-82cfad73/src/prover.rs:97-98`:

```rust
// Produce a proof of work witness before receiving any query challenges.
// This helps to prevent grinding attacks.
let pow_witness = challenger.grind(params.query_proof_of_work_bits);
```

It sits **after** `commit_phase` (all fold rounds committed and observed) and **after** the fold
arities are absorbed, and **before** the first `challenger.sample_bits(...)` that draws a query
index. That position is the whole point: the witness binds the transcript that *determines* the
query indices, so re-rolling the indices costs `2^pow` work per attempt.

### ⚑ This refutes the "move it off the critical path" option by construction

Its input is the completed FRI commit-phase transcript, which does not exist until the trace is
committed and folded. There is no earlier point at which the same object can be ground. Grinding
*something else* earlier (say, right after the main trace commit) is a **different, weaker
protocol** — it would not bind the fold commitments, so a prover could still re-roll them. So
"grind the commit transcript before the trace is ready" is not an optimisation of this phase; it
is a soundness change, and the lane's own rule forbids it.

The other two options — fixed-work and parallelism — survive, and §3/§4 measure them.

## 0b. The deployed values, confirmed at source

| config | file | `query_pow` | `commit_pow` |
|---|---|---:|---:|
| IR-v2 descriptor batch | `circuit/src/descriptor_ir2.rs:7248, :7265` | **16** | **0** |
| v1 production uni-STARK | `circuit/src/plonky3_prover.rs:112, :118` | 16 | 0 |
| ZK lane | `circuit/src/stark_zk.rs:66, :71` | 16 | 0 |
| BN254 outer shrink | `circuit-prove/src/dregg_outer_config.rs:138, :158` | 16 | 0 |
| Mina wrap | `circuit-prove/src/dregg_mina_config.rs:155, :174` | 16 | 0 |
| recursion default | `recursion-verify/src/config.rs:58, :66` | **14** | 0 |
| IR-v2 inner (wrap) | `recursion-verify/src/config.rs:96, :94` | 16 | 0 |

**Every `commit_proof_of_work_bits` in the tree is `0`** — seven config families, no exceptions.
`circuit/tests/commit_pow_cost_measure.rs` already prices that knob and is not re-derived here.

⚑ **The grind is per-FRI-proof, not per-pipeline.** A recursion tower with `n` proofs pays `n`
independent draws. The variance argument in §5 compounds accordingly: the *tower's* latency is a
sum of `n` exponentials, which concentrates — but a single leaf mint, which is what a light client
waits on, is one draw.

### The one place the `2^pow` in the Lean column is not exact — checked, and it is 4.7×10⁻⁵ bits

`check_witness` uses `CanSampleBits::sample_bits`, which is the low `bits` of a **canonical** field
element (`duplex_challenger.rs:264-270`), and `2^16 ∤ p`. So the success probability is not exactly
`2^−16`. Exactly: `p = 2³¹ − 2²⁷ + 1 ≡ 1 (mod 2¹⁶)`, so `30721` of the `p` residues have low 16 bits
zero against `30720` for every other pattern, giving

`P(success) = 30721 / 2013265921 = 2^−15.999953`.

**The deployed grind delivers 15.999953 bits, not 16** — a deficit of `4.7 × 10⁻⁵` bits, i.e. the
honest prover's expected work is 0.0033% below `2^16`. The tree *has* the exact alternative
(`UniformGrindingChallenger::grind_uniform` / `check_witness_uniform`, with rejection sampling) and
does not use it; at this magnitude that is the right call, and the point of writing it down is that
"exactly `powBits` bits" is now a checked approximation rather than an unexamined one.

⚑ **The BN254 outer grind is a different implementation.** `MultiField32Challenger::grind`
(`grinding_challenger.rs:335-356`) is **neither SIMD-packed nor batched**: it is
`(0..F::ORDER_U32).into_par_iter().find_first(|w| self.clone().check_witness(bits, *w))`, one full
BN254 Poseidon2 duplex per candidate, at `OUTER_FRI_QUERY_POW_BITS = 16`. Everything measured below
is the BabyBear `DuplexChallenger` path (the IR-v2 leaf); the outer path's per-candidate cost is
one BN254 permutation, not one BabyBear permutation ÷ 4 lanes.

---

## 1. ⚑ What the grind buys, in bits, in OUR regime — and what it displaces

`Assurance.TwoRegimeQueryBudget` prices the query column as
`err = (1 − θ_r)^q / 2^pow`, so in bits:

> **`column_bits = q · (−log₂(1 − θ_r)) + pow`**

`pow` enters **additively and identically at every regime** (new theorems
`powBits_add_divides`, `powBits_add_shifts_bits`, `grind_moves_every_regime_identically`): `k` more
grind bits is exactly `k` more column bits, two-sided, unconditionally. A query enters
**multiplicatively and regime-boundly** — one more query multiplies the squared error by
`survivalSq r ρ`, which is `(65/128)²` at UDR against `1/64` at JBR
(`the_query_lever_is_regime_dependent`). This is the exact dual of §6's `logup_carries_no_regime`:
the *other* wall carries no regime; here it is the *grind* that carries none, and the query that does.

At the deployed `lb = 6` (`ρ = 1/64`):

| regime | status | bits per query | queries per grind bit | deployed column | **pow's share** |
|---|---|---:|---:|---:|---:|
| **UDR** | proven | **0.9776** | **1.0229** | 34.58 → `Bits 34` | **46.3%** |
| JBR | idealised | 3 | 0.3333 | 73 → `Bits 73` | 21.9% |
| CBR | withdrawn | 6 | 0.1667 | 130 → `Bits 130` | 12.3% |

**⚑ At UDR — the only regime that is still standing — 16 of the deployed column's 34.58 bits are
grind. Nearly half of the proven query-phase soundness of the shipped IR-v2 batch is proof-of-work,
not queries.** That is not a criticism of the design; it is the fact any cost argument has to start
from, and it was not written down anywhere before this note.

### The exchange rate, two-sided and machine-checked

`sixteen_grind_bits_cost_seventeen_queries_at_UDR` and
`sixteen_grind_bits_cost_six_queries_at_JBR` (new, kernel `norm_num` over ℚ, no `native_decide`):

| regime | queries that buy back `pow = 16` | and one fewer does **not** |
|---|---:|---|
| UDR | `q: 19 → 36` (**+17**) | `q = 35` is strictly less sound than deployed |
| JBR | `q: 19 → 25` (**+6**) | `q = 24` is strictly less sound than deployed |
| CBR | `q: 19 → 22` (**+3**) | `q = 21` is strictly less sound than deployed |

Both halves are stated, because "17 queries suffice" is also true of 170. The pair pins the rate.

⚑ **A cost argument that says "the grind replaces N queries" without naming its regime has quoted
one of 17 / 6 / 3.** The three differ by 5.7×, and the flattering one (3) is the withdrawn regime.

### And the prices of the two levers, measured, are three orders of magnitude apart

| lever | prover | verifier | wire |
|---|---|---|---|
| **+16 grind bits** | **+12.4 ms expected** (2^16/4 lanes × 758 ns), 8.2 ms at the deployed draw | +1 permutation (`check_witness`) | **+1 field element** |
| **+17 queries** (same bits, UDR) | +~0.05 ms (`open_batch` copies stored digests, hashes nothing — all 19 queries cost 0.05–0.07 ms) | +17 Merkle paths ≈ **+2.3 ms** (from the parity ladder's `dverify/dq ≈ 0.137 ms/query`) | +17 query proofs (§4 measures the bytes) |

**On the prover, the grind is the expensive way to buy those bits by ~250×.** What it buys back is
verifier time and proof bytes. So the deployed `pow = 16` is not a mistake — it is a *deliberate
transfer of cost from the verifier to the prover*, which is the correct direction for a light-client
system. The question §5 settles is whether 16 is the right amount of that transfer.

### The shape of the trade, before any number: one lever is linear and the other doubles

* A **query bit** costs a *constant*: ~0.003 ms of prover, ~0.2 ms of verifier, ~5.5 KiB of wire,
  per 0.9776 bits, at every point on the curve.
* A **grind bit** costs *nothing* on the verifier (`verifier.rs:254` is a single `check_witness` =
  one `observe` + one `sample_bits` = **one Poseidon2 permutation, ~1 µs, for all 16 bits**) and
  *nothing* on the wire (one field element), but its prover cost **doubles with every bit**: the
  `p`-th bit costs `2^(p−1)/lanes × 758 ns`.

⚑ **That asymmetry is the whole answer, and it has a robustness property worth stating.** Because
the marginal grind cost is exponential and the marginal query cost is flat, there is a **unique**
crossover `p*` for any weighting of prover-ms against verifier-ms and wire-bytes — and `p*` moves
only **logarithmically** in that weighting. Changing how much you value verifier time relative to
prover time by 1000× moves the optimal `pow` by 10 bits. So "what is the right `pow`" is a
well-posed question with a stable answer, which is not obvious a priori.

---

## 2. The distribution of the grind's work — exact, no clock involved

**The instrument, and why it is immune to this box.** The dregg `find_map_first` delta makes `grind`
return the **globally minimal** valid witness `w`. So candidates `0..=w` were all evaluated and
**the returned field element *is* the exact trial count** — the cost of a grind is readable off the
proof, with no timer, no sampling profiler, and nothing that a load average of 135 can touch. (This
is a second, unadvertised consequence of the determinism delta, and it is the only reason a useful
number came out of this box tonight.)

**MEASURED** (§G2, N = 256 independent transcripts at `pow=16`, N = 1024 at `pow=12`; exact counts,
load average 79–120 and it does not matter):

| | mean | p50 | p90 | p99 | max over N |
|---|---:|---:|---:|---:|---:|
| **trials, `pow=16`** | **67,486** | 53,173 | 149,417 | 277,677 | 398,257 |
| × theory `2^16` | 1.030 | | | | |
| packed perms | 16,872 | 13,294 | 37,355 | 69,420 | 99,565 |
| **ms at 758 ns/call** | **12.79** | 10.08 | 28.32 | 52.62 | **75.47** |

and the tail is exponential to two decimal places — the model is **checked**, not assumed:

| | P(>1× mean) | P(>2×) | P(>3×) |
|---|---:|---:|---:|
| observed (`pow=16`, N=256) | 0.402 | 0.133 | 0.039 |
| observed (`pow=12`, N=1024) | 0.334 | 0.125 | 0.046 |
| `e^−k` | 0.368 | 0.135 | 0.050 |

⚑ **Independent confirmation of `phase-profile.md` §4 from a different direction:** §G5 proves an
honest transfer proof at the deployed knobs and reads its witness — `w = 47,912`, i.e. 11,979 packed
permutations, against the counting-config's **11,979 SIMD calls**. Two harnesses, two mechanisms,
the same integer.

The analytic form (`trials ~ Geometric(2^−pow)`), which the measurement above matches:

| quantile | trials | × the mean | packed perms | **ms (1 thread)** |
|---|---:|---:|---:|---:|
| p10 | 6,905 | 0.105 | 1,726 | 1.31 |
| p50 | 45,426 | 0.693 | 11,357 | 8.61 |
| **mean** | **65,536** | **1.000** | **16,384** | **12.42** |
| p90 | 150,902 | 2.303 | 37,726 | 28.60 |
| p99 | 301,804 | 4.605 | 75,451 | 57.19 |
| p99.9 | 452,706 | 6.908 | 113,177 | 85.79 |

⚑ **The deployed grind's p99 is 53 ms measured (57 ms modelled) — 4.2× its mean.** Anything with a
latency budget must carry that number, and `phase-profile.md` §4's largest observed draw (40.8 ms)
is only the p96: the ladder was not unlucky, it was ordinary. The worst of 256 draws was **75 ms**,
against a whole-prove budget of 69 ms.

Two properties of this variance that matter for how you fix it:

* **It is per-PROOF, not per-run.** For a fixed transcript the witness is fixed — that is exactly
  what the determinism delta buys — so re-running one proof reproduces its own draw exactly. Every
  *new* proof draws again. You cannot retry your way out of a bad draw, and you cannot benchmark
  your way past one either: a single-number prove time at `pow=16` is one sample of this table.
* **A tower concentrates; a leaf does not.** A recursion tower with `n` proofs pays a sum of `n`
  independent exponentials, whose relative spread falls as `1/√n`. The object a light client waits
  on is **one leaf mint = one draw**, which is the worst case for variance.

*(§G2 re-measures this empirically — 256 independent transcripts at `pow=16`, 1024 at `pow=12` —
and checks the tail masses against `e^−k` rather than assuming the model. The numbers above are the
model; the empirical check is what makes them evidence.)*

---

## 3. ⚑ The grind is NOT parallel any more, and a cost verdict in the tree still says it is

`circuit/tests/commit_pow_cost_measure.rs:75-83` (landed **2026-07-28**, `5c18754ed`) states:

> ⚑ `grind` is ALREADY both SIMD-packed … and rayon-parallel
> (`(0..num_batches).into_par_iter().find_map_any`, `challenger/src/grinding_challenger.rs:166`).
> The rate above is therefore a **WHOLE-MACHINE rate, not a per-core one: there is no further thread
> multiplier to apply**, and a column that applied one would be counting the same parallelism twice.

**That premise left the tree five days later.** Commit `90680ee7d` (2026-08-02, *"the prover picked
a RACING PoW witness, and sixteen teeth were red for refusing correctly"*) is the dregg determinism
delta: it replaced `find_map_any` with **`find_map_first`** in the vendored challenger, because
`find_any` returns whichever valid witness a worker thread happened to reach first, the witness is
absorbed into the transcript *before* the query indices are drawn, and three rayon runs of one
binary produced three distinct proof lengths. The delta is correct and the byte-parity gates
depend on it.

But `find_any` and `find_first` are **different parallel problems**, and this is derivable from
rayon's own code, not a guess:

* `find_any` (`MatchPosition::Anywhere`) sets `full()` as soon as *any* worker matches. `T` workers
  scan `T` disjoint subranges; each hits a match after `Geom(2^−pow)` batches; the first to finish
  ends the search. Latency `≈ 2^pow / (lanes · T)` — a genuine `T×`.
* `find_first` (`MatchPosition::Leftmost`) must prove **no lower candidate exists**, so `full()`
  only fires for a worker whose *lower bound* already exceeds the best index found. The answer lives
  at candidate `w ≈ 2^pow`, i.e. in the first `0.003%` of a `2^31/4`-batch range. Rayon's splitter
  is **thief-driven**: the low chunk is subdivided only when another worker goes idle and steals —
  and the other workers are *not* idle, because they are each grinding their own multi-million-batch
  subrange and will not abort until a lower match is published. The worker that owns index 0
  therefore walks `0 → w` essentially **alone**.

### MEASURED (§G3), and the derivation was right

Fixed transcript (`w = 83,061`, a 1.27× draw), min of 5, box parallelism 12, load ~90. `crit` = the
maximum batches any **one** worker scanned = the permutations on the critical path — a
**contention-free** instrument, because every batch is exactly one Poseidon2 permutation, so the
scaling conclusion does not depend on this box's load at all.

| threads | **A `find_map_first` (deployed)** | | **B `find_map_any` (upstream)** | | **C windowed min (proposed)** | |
|---|---:|---:|---:|---:|---:|---:|
| | crit | scale | crit | scale | crit | scale |
| 1 | 20,766 | 1.00 | 20,766 | 1.00 | 65,536 | 1.00 |
| 2 | 20,766 | **1.00** | 20,766 | 1.00 | 32,768 | 2.00 |
| 4 | 21,956 | **0.95** | 6,613 | 3.14 | 18,098 | 3.62 |
| 8 | 20,766 | **1.00** | 4,319 | 4.81 | 12,096 | 5.42 |
| **12** | **20,766** | **1.00** | 5,214 | 3.98 | **8,745** | **7.49** |

⚑ **The deployed grind's critical path is EXACTLY CONSTANT — 20,766 batches at 1 thread and 20,766
at 12. Scale 1.00. It has no parallelism at all.** Wall clock agrees and then some: `24.4 ms` at one
thread, `28.9 ms` at twelve — it gets *slower*, because the eleven other workers contend for cache
and memory bandwidth while contributing nothing.

And the energy bill is the sharpest number in the table:

| total batches scanned | T=1 | T=4 | T=12 |
|---|---:|---:|---:|
| A `find_first` (deployed) | 20,766 | 80,655 | **123,517** |
| B `find_any` | 20,766 | 19,630 | 36,313 |
| C windowed (`c=4`) | 65,536 | 65,536 | 65,536 |

**The deployed grind burns 5.9× the work at 12 threads to deliver 1.00× the latency.** Eleven
workers scan candidates above the answer, publish matches that lose the `min`, and are discarded.

Strategy B does scale — and over 8 runs on 12 threads it returned **4 distinct witnesses**
(`754998892, 1069549211, 1258302293, 1887436913`), which is precisely the byte-nondeterminism
`90680ee7d` was landed to kill. Strategy C returned **the same witness as A** (`83061`) at every
thread count, in one window.

So the consequence is not conditional: the 2026-07-28 warning *"there
is no further thread multiplier to apply"* is now **backwards**. It was written to stop a reader
double-counting parallelism; today it makes a reader count parallelism that is no longer there. This
is the `a-cost-verdict-outlives-its-premise` class, in our own tree, with the premise's departure
recorded in the very commit that made the code correct — a hardening commit that quietly disarmed a
cost model.

⚠ It is **not** a soundness regression. `90680ee7d` changed *which* valid witness is returned and
nothing else; the work an honest prover performs and the predicate the verifier checks are
identical. What it changed is the *schedule*, and nobody re-priced the schedule.

---

## 4. pow vs queries at a fixed soundness column

**The ladder.** At `lb = 6`, hold the UDR column at or above the deployed `34.575` bits and move
where the bits come from. The `q` per rung, and the fact that each rung really is at least as sound
as deployed *and* tight (one query fewer drops below), are **theorems**, not floats in a test —
`the_cost_ladder_is_at_or_above_the_deployed_column` and `the_cost_ladder_is_tight`:

| `pow` | `q` | UDR bits | JBR bits |
|---:|---:|---:|---:|
| 0 | 36 | 35.195 | 108 |
| 8 | 28 | 35.374 | 92 |
| 12 | 24 | 35.463 | 84 |
| **16 (deployed)** | **19** | **34.575** | **73** |
| 20 | 15 | 34.665 | 65 |

**MEASURED** (§G4, real IR-v2 transfer proofs, `RAYON_NUM_THREADS=1`, min of 5, load ~90–120).
Arm 1 holds `pow = 0` at every `q`, so the query slope is free of the grind's draw:

| `pow` it stands for | `q` | **verify ms** | **proof bytes** |
|---:|---:|---:|---:|
| 0 | 36 | 11.38 | 237,262 |
| 8 | 28 | 9.26 | 190,654 |
| 12 | 24 | 8.90 | 167,350 |
| **16 (deployed)** | **19** | **6.87** | **138,220** |
| 20 | 15 | 5.82 | 114,914 |

⇒ **`dB/dq` = 5,826 B per query** (intercept 27.5 KB) and **`dV/dq` = 0.265 ms per query**
(intercept 1.83 ms). The byte slope is within 8% of `FRI-PARAM-FRONTIER` §1b's independent fit
(`3971 + 239·lb = 5,405` B/query) — the offset is `rmp-serde` against postcard, the same offset
`phase-profile.md` §5 reports. The verify slope is an *upper* bound: this box was at load ~100.

⚠ **The prove-ms column of §G4 is unusable and is not quoted.** Arm 1 read
`401 / 602 / 414 / 469 / 383 ms` across `q = 36 → 15` — non-monotone, with ±100 ms of contention
noise against a real signal of ~0.05 ms. `dP/dq` therefore comes from `phase-profile.md` §2's clean
instrument (**the entire query/open phase is 0.05–0.07 ms for all 19 queries**, because
`MerkleTreeMmcs::open_batch` copies stored digests and hashes nothing) ⇒ **`dP/dq` ≈ 0.003 ms**.
Naming which column of my own run is garbage is the point of running two arms.

⚑ **And `pow` is free on the wire, measured:** across the whole ladder the two arms' proof sizes
differ by **at most 2 bytes** (190,654 vs 190,652) — the witness is one field element under a
varint codec. Against 5,826 B per query, that is the entire wire cost of 16 soundness bits.

Putting it together, all relative to the deployed point (`E[grind] = 2^pow/4 × 758 ns`; this
session's contended rate measured 914 ns, and the quieter 758 ns from `phase-profile` is used —
using 914 makes the grind column 21% worse, not better):

| `pow` | `q` | prover−grind | **E[grind]** | **E[prove]** | verify | proof bytes |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 36 | +0.05 ms | 0.00 ms | **+0.05** | +4.5 ms | **+99.0 KB** |
| 8 | 28 | +0.03 ms | 0.05 ms | **+0.08** | +2.4 ms | +52.4 KB |
| 12 | 24 | +0.02 ms | 0.78 ms | **+0.80** | +1.3 ms | +29.1 KB |
| **16** | **19** | **0** | **12.42 ms** | **+12.42** | **0** | **0** |
| 20 | 15 | −0.01 ms | 198.7 ms | **+198.7** | −1.1 ms | −23.3 KB |

⚑ **Read the last two columns together.** Going from `pow=16` to `pow=12` buys back **11.6 ms of
prover for 29 KB of wire and 1.3 ms of verify.** Going the other way, `pow=20` costs **186 ms of
prover to save 23 KB.** The exponential does all the work: the interesting region is narrow, and it
contains 16.

---

## 5. VERDICT on the deployed point

### The decision rule, in closed form

Because the marginal grind bit doubles and the marginal query bit is flat, the optimum is where they
meet, and it can be written down:

> `p* = 1 + log₂[ (dP/dq + w·dV/dq + β·dB/dq) · (1/r) / (t_perm / lanes) ]`

with `r = 0.9776` bits per query at UDR/lb=6, `t_perm = 758 ns` (packed Poseidon2), `lanes = 4`,
`w` = how many prover-ms one verifier-ms is worth, and `β` = how many prover-ms one KiB of proof is
worth. Substituting §4's **measured** slopes (`dP/dq = 0.003 ms`, `dV/dq = 0.265 ms`,
`dB/dq = 5.69 KiB`):

| what you are optimising | `w` | `β` (ms/KiB) | `p*` |
|---|---:|---:|---:|
| prover latency only (a devnet mint) | 0 | 0 | **5.0** |
| prover + verifier equally, wire free | 1 | 0 | **11.5** |
| **prover + verifier + wire at 1 ms/KiB (a chain that posts proofs)** | **1** | **1** | **15.97** |
| a light client verifying many proofs | 10 | 1 | **16.5** |

⚑ **`p* = 15.97` at the weighting dregg actually uses. The deployed `pow = 16` is the optimum, to
two significant figures, and nobody computed it.** `FRI-PARAM-FRONTIER` §1b already says the
`(6, 19)` blowup point was chosen because *"the axis this system optimizes [is] wire bytes and verify
ms for light clients and on-chain verifiers"* — pricing a KiB of proof at about a millisecond of
prover time is exactly that axis. So the answer to "is 16 the right point" is **yes, and for the same
reason the blowup was already chosen**, which is a consistency nobody had checked.

Note how flat it is: `p*` moves by only ~11 bits across a weighting range spanning four orders of
magnitude. That is the `log₂` in the formula, and it is why this is a robust answer and not a knife
edge — which also means **the answer would survive my verify slope being 30% off from contention**.

### But the schedule, not the parameter, is what should change

`p*` is computed against the **measured, single-threaded** grind cost. §3 shows that cost is
single-threaded *by accident* — `find_map_first` does not divide the search. Restoring parallelism
(§6) divides `t_perm/lanes` by `T`, which moves `p*` **up** by `log₂ T ≈ 3.6` bits on this box.

So the two findings compose:

* **Do not lower `pow`.** 16 is optimal at today's schedule and *more* than justified at a fixed one.
  Lowering it would be a security parameter traded for a performance problem that has a free fix.
* **Fix the schedule.** It is worth ~7.6× on the grind's mean and ~11× on its p99, changes no wire
  byte, and needs no VK rotation.
* **Do not raise `pow` yet either.** `p* ≈ 19.5` after the fix is inside the noise of the weighting,
  and raising it *is* a ledger move (`Bits 34 → 37` at UDR) that should be argued on soundness, not
  smuggled in as an optimisation.

---

## 6. THE PROPOSAL — a windowed parallel min-witness grind

**One sentence: scan a bounded window of the candidate space completely and in parallel, reduce
with `min`, and advance a window if it was empty.**

```rust
// replaces `(0..num_batches).into_par_iter().find_map_first(scan_batch)`
let mut lo = 0;
loop {
    let hi = (lo + window).min(num_batches);
    if let Some(w) = (lo..hi).into_par_iter()
            .filter_map(scan_batch)
            .min_by_key(|w| w.as_canonical_u64()) {
        return w;                       // the FIRST non-empty window's min IS the global min
    }
    lo = hi;                            // P(empty) = e^(−c) per window
}
```

### It returns byte-for-byte the same witness

Windows are contiguous and ascending, so the first window containing any match contains the
*smallest* match, and `min` over that window is the global minimum — which is exactly what
`find_map_first` computes. Same predicate, same witness, same query indices, same proof bytes, same
VK. **This is a scheduling change and nothing else**, and `§G3` asserts the equality rather than
arguing it (`assert_eq!(grind_windowed(..), grind_first(..))`).

### Why it fixes both problems at once

| | deployed `find_map_first` | proposed windowed min |
|---|---|---|
| parallel efficiency | ~1× (the low chunk is walked by one worker; thieves land above the answer) | **~T×** — every window is a complete scan with no early exit, perfectly splittable `window = T·k` |
| work distribution | geometric in *candidates*: `P(> k·mean) = e^(−k)`, unbounded tail | geometric in **whole windows**: `P(> n windows) = e^(−c·n)`, a small integer × a fixed unit |
| determinism | yes (that is why the delta exists) | **yes, identically** |
| extra work | none | `E[windows]·c/1 ≈ c/(1 − e^(−c))` × the mean draw — the tunable price |

### MEASURED: the window count, over 64 independent transcripts

The window count is another exact, clock-free observable, so this table is not affected by the box
either. Theory is `E[windows] = 1/(1 − e^{−c})`:

| `c` | windows needed, over 64 draws | mean | theory |
|---:|---|---:|---:|
| 1 | `{1: 37, 2: 18, 3: 6, 4: 2, 6: 1}` | 1.64 | 1.582 |
| 2 | `{1: 55, 2: 8, 3: 1}` | 1.16 | 1.157 |
| 4 | `{1: 63, 2: 1}` | 1.016 | 1.018 |
| **8** | **`{1: 64}`** | **1.000** | 1.0003 |

⚑ **At `c = 8` the grind becomes literally fixed-work**: one window, every time, over 64 draws
(`P(> 1 window) = e^{−8} = 3.4×10⁻⁴`). That is the "fixed-work alternative" the brief asked about —
and it turns out not to need a VDF or a new predicate, just a window. Constant 131,072 packed
permutations, ~8.3 ms at 12 threads, **variance essentially zero**, same witness, same bytes.

`c = 1` is the low-mean option (~1.6 ms mean, ~5.2 ms p99); `c = 8` is the low-variance option
(8.3 ms, always). Both are large improvements on the deployed 12.4 ms mean / 53 ms p99 / 75 ms
worst-of-256, and the choice between them is a scheduling preference, not a soundness one.

⚠ The wall-clock column of the `c` sweep (`38.9 / 35.5 / 80.4 / 152.2 ms` at one thread) is
contention noise at load ~100 and is not quoted; the window counts and the `crit` column of §3 are
the figures that do not need a quiet box.

### Choosing the window, and the limit

`c` is the window measured in expected draws. Its two effects pull the same way down to the barrier
cost, so this is not a real trade-off in the interesting range:

| `c` | window latency (T=12) | `E[windows]` | **E[latency]** | **p99 latency** | wasted work |
|---:|---:|---:|---:|---:|---:|
| deployed (`find_first`) | — | — | 12.4 ms | 57.2 ms | 0 |
| 4 | 4.1 ms | 1.018 | 4.2 ms | 8.3 ms | 4.07× |
| 2 | 2.1 ms | 1.157 | 2.4 ms | 6.2 ms | 2.31× |
| **1** | **1.03 ms** | **1.582** | **1.63 ms** | **5.2 ms** | 1.58× |
| 0.5 | 0.52 ms | 2.542 | 1.32 ms | 5.2 ms | 1.27× |
| `→ 0` | → 0 | → ∞ | **→ 1.03 ms** = mean/T | → mean/T | **→ 1.00×** |

⚑ **The limit is the point.** As the window shrinks, the scheme degenerates to *"scan in parallel,
synchronise every `k` candidates"* — latency tends to `mean/T`, which is the information-theoretic
floor for a deterministic minimum-witness search, and the wasted work tends to **zero**. The only
thing stopping `c → 0` is the per-window rayon join (~µs). So: **pick the window so one window takes
~0.5–1 ms**, i.e. `window ≈ 2^pow / lanes` batches at the deployed knobs (`c = 1`). Nothing about
this is delicate.

At `c = 1`, `E[windows] = 1.58`: total work rises 1.58× while latency falls ~7.6× on the mean and
~11× on the p99, on a 12-core box.

### The same pathology, two more sites

`find_first` is also used by **`MultiField32Challenger::grind`** (`grinding_challenger.rs:352` — the
BN254 outer/shrink challenger, where a candidate costs a *BN254* Poseidon2 duplex, not a BabyBear
permutation ÷ 4 lanes) and by **`grind_generic`** (`:316`, behind `grind_uniform`). Both take the
same fix. The outer one is where the absolute milliseconds are largest.

### What it is not

* Not a *fixed-work* / VDF scheme. A VDF is sequential by construction, so it makes latency worse,
  and verifying it needs a proof. Refuted, not deferred.
* Not a change to `pow`. **No security parameter moves.** The bits stay at 16.
* Not a way to move the grind off the critical path — §0 shows that is impossible without
  weakening what the witness binds.

---

## 7. Reproduce

```bash
cd ~/dev/breadstuffs
# ⚠ never pipe cargo into head/grep -m: head exits, SIGPIPE kills the build, and the pipeline
# still reports success. Redirect and grep the file. (PREFLIGHT, 2026-08-14.)
cargo test -p dregg-circuit --release --test grind_phase_measure --no-run > /tmp/b.log 2>&1
B=$(ls target/release/deps/grind_phase_measure-* | grep -v '\.d$')

$B g1_exchange_rate_and_the_lean_cells      --nocapture --exact --test-threads=1   # §G1
$B g5_the_grind_gate_bites_on_a_bad_witness --nocapture --exact --test-threads=1   # §G5
DREGG_GRIND_SAMPLES=256 \
  $B g2_grind_work_distribution             --nocapture --exact --test-threads=1   # §G2
DREGG_GRIND_REPS=7 \
  $B g3_grind_thread_scaling      --ignored --nocapture --exact --test-threads=1   # §G3
RAYON_NUM_THREADS=1 DREGG_PROFILE_REPS=5 \
  $B sweep::g4_pow_vs_queries_at_fixed_soundness --ignored --nocapture --exact --test-threads=1
```

Lean side (kernel-checked, no `native_decide`):

```bash
cd ~/dev/minidregg && lake env lean Assurance/TwoRegimeQueryBudget.lean
```

Release only. **Report the load average with any wall-clock number taken from this box** — §G2's
trial counts and §G3's `crit` column are the two figures that do not need one.
