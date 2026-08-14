# VERDICTS — the single current-truth file

2026-08-13. **This file states what we believe NOW. No history, no superseded
claims, no ⚠ markers.** If a question is settled it is here in its final form;
if it is open it is in §7. Evidence lives in `notes/`; where a note and this
file disagree, **this file wins** and the note is history.

---

## 1. Fields and hashes

**Deployed, both trees: BabyBear** (2013265921 = 15·2²⁷+1), challenge **Ext4**,
hash **Poseidon2 width-16**. KoalaBear (2130706433 = 127·2²⁴+1) is a
**recommended, unexecuted** migration target.

- **Ext4's realized soundness is 100 bits**, not the field-size 2^123.6.
- **Ext5 fixes the LogUp wall (100→136) and does nothing for the query wall.**
  There are two independent 100-bit walls; extension degree moves only one.
- **Poseidon2 round-skipping (2026/306): no action.** Our margin is +286 bits
  and the attack cannot reach our bar even if every skippable round were free.
  **α=7 is why**; α=3 (KoalaBear) roughly halves the margin — still safe, but
  the migration makes this worth re-deriving.
- **The prime family is 127·2ⁿ+1** — KoalaBear is n=24, p61 = 2⁶¹−2⁵⁴+1 is
  n=54. Prime members {2,12,18,24,54,72,114}; first bad-class prime n=214.
  **The row is Riesel 1994, Table 5, h=127.** Maximal 3-adic inertia iff
  n ≡ 0 or 2 (mod 6).

## 2. Soundness accounting

**Our deployed IR-v2 (lb=6, q=19, pow=16) reads: UDR 34 / JBR 73 / CBR 130.**

- **"Conjectured 130" is CBR-shaped — the capacity regime `ethereum/soundcalc`
  deleted in Nov 2025.** 57 of the 130-vs-73 headroom is a withdrawal, not a
  knob. **Never quote 130.**
- **100 proven-UD bits costs 86 queries instead of 19, with `log_blowup`
  unchanged** — 4.5× on the query phase, **zero on the commit phase**, because
  ρ=1/64 already bought the expensive half. Four of five production systems
  refuse the capacity conjecture; we are the outlier. Measured price of the
  proven regime elsewhere: ~2× proof size, ~4% time.
- ⚑ **"`lb=6` is 2.9× off the optimum" is REFUTED — it was a grind draw.**
  `query_proof_of_work_bits=16` is **~25% of a deployed prove** (47,917
  permutations / 8.2 ms), depends on **neither blowup nor trace**, and is
  **exponentially distributed** — it drew 0.04 / 8.2 / 10.1 / 31.9 / 40.0 /
  40.8 ms across one ladder. At **pow=0** the curve is strictly monotone
  (14.9 / 20.3 / 34.9 / 67.9 / 120.6 / 243.3 ms) with **lb=3 fastest by
  1.4×**. The published lb=3 point paid 40.8 ms of grind against lb=4's 10.1 —
  **that 30 ms of coin flip *was* the reported optimum.** (The published
  `prove` column also included a full self-verify.)
- **`num_queries` is unpinned in the recursion verifier** — read from the
  inner proof, never checked against a configured count. A child minting one
  query drops the column to 19 bits (JBR) / 16 (UDR). *The field wall is
  compiled into the verifier; the query wall is carried in the proof.*

## 3. FHE

- **Deployed depth is 2** (measured, 40/40). The secret is **CBD(20)**
  (variance 10, support ±20) — not ternary, not CBD(10).
- **The KPZ encoding fix is a NO-OP** — fhe.rs already uses exact-division
  encoding; r_t(Q) is structurally absent from our noise path.
- **Dead, with reasons**: transciphering (269 bits of homomorphic-decryption
  noise against our 109-bit modulus); bootstrapping (depth 13–17 crossover
  against our 1–3); scheme-switching (**hazardous** — working CPA-D PoC).
- **t = 2²⁰ binds any BFV polynomial nonlinearity to degree ≤ 2 regardless of
  levels.** Nonlinearities go through the MPC/PBS boundary. Encrypted
  attention at depth ≤3 is refuted.
- **Coefficient-encoded matmul is built and measured**: 12 bits/matmul with
  **split-sign** (`W = W⁺ − W⁻`; direct coefficient lift gives **zero**
  advantage over SIMD because negative weights lift to ~t), depth 2 after,
  466 µs at 512×31. **Inner dim ≤ 31 at int8×int8, ≤504 at 4×8** — the
  binding constraint is t, not the technique.
- **H2: a 109-bit joint prime is a net loss; a 61-bit one wins on both sides
  but costs 48 bits of noise budget = exactly one depth level.** The deciding
  variable is the machine word, not the number of primes. **H2 collapsed into
  H1 — they are not independent gates.**
- The deployed noise expansion is the **proven δ_R = N**, not the heuristic
  2√N (measured to 0.02 bits).

## 4. Proof-system design

- **The principle is `polynomial virtualization`** (Thaler 2025/2041), not
  "boundary" — that term collides with *border rank*. The fork is
  **materialize-vs-virtualize**, not AIR-vs-sumcheck. Restated:
  *an AIR commits the Cook–Levin witness; a virtualizing sumcheck commits the
  original NP witness.* **The monotone reading is wrong — there is a sweet
  spot, not zero.**
- ⚑ **The exchange rate was in the WRONG UNIT.** 78–308× is *counted field
  multiplications*; the conversion to wall-clock had never been taken.
  **Measured: 54.7 ns per marginal committed felt vs 10.97 ns per value per
  sumcheck layer — a ~5× wall-clock rate at lb=3**, because hashing
  SIMD-vectorizes harder than folding does. **Consequence: a degree-(α+1) fold
  costs 77–132 ns against 55 ns to commit, so GKR LOSES at α=7 by 1.4–2.4×
  and wins only at α ≤ 3.** The layer budget is **0.42–0.71 layers at α=7**,
  1.49–1.66 at α=3. ⚠ Every plan priced against 78–308× (C2, C5, C7) needs
  re-pricing.
- **The multilinear seam is ONE `RbrKnowledgeSoundness` instance, not a new
  abstraction.** No hash-based multilinear PCS is indexed by an evaluation
  point; the commitment is a Merkle vector commitment to a codeword — our
  existing `OpeningScheme`, unchanged. Route: **BaseFold at RS in our own
  unconditional (1−ρ)/3 band.** Five new items, no conjecture, no new
  proximity result.
- **Jagged PCS has no cryptographic content** — which is why it is tractable.
  A large convenience on top of a PCS that does the security work.
- **`fold_add` as one opening: ratio = B, PROVER-SIDE ONLY — and B is 4 in
  deployment, so the real figure is 4.2×, not 690×.** ("Lazy accumulation is
  free" is also dead: 0.88× is a *column* ratio and it breaks even at B=4.) The verifier
  moves the opposite way (O(B) Merkle work vs a polylogarithmic AIR verifier),
  and the shared-tree fix collides with per-party root binding.
- **The base→extension boundary is a measured ~3× cliff.** The emitted
  constraint object should be a **syntactic expression over ℤ-coefficients
  with each concrete ring a valuation** (semiring provenance: transport
  commutes iff the map is a homomorphism). This is a *check*, not a deadline —
  cheap iff constraints consume the ring through an interface.
- ⚑ **Poseidon2 virtualization: direction CONFIRMED, mechanism REFUTED.** The
  sumcheck route loses (see the exchange-rate correction). **The win is
  in-AIR virtualization of the degree-1 lanes**: 211 of the deployed 352
  committed felts (59.9%) carry no nonlinearity, so carrying them as
  expressions gives **352 → 157 felts, 352 → 141 constraints, 2.11× prove,
  2.34× committed cells, at identical `max_constraint_degree = 7`** —
  strictly Pareto, no trade to price. **And the ratio GROWS as α falls**
  (2.24× BabyBear → 2.83× KoalaBear w16), so the field question gets a second
  answer pointing the same way. ⚠ The `map_write_chip` 227 ms "corroboration"
  **was not one** — it is a chip-table present-vs-absent comparison.
- **The degree-3 rung is LANDED** (`Assurance/AirSumcheckCubic.lean`):
  `cubicForm E A B C D = Ê·(Â·B̂ + Ĉ·D̂)`, soundness `≤ m·3/|F|`. **Both
  consumers are theorems, not prose** — `cubicForm_fraction_layer` (GKR) and
  `cubicForm_matmul` (zkML) discharge "one rung serves both", and
  `cubicForm_subsumes_prodDiff` proves the degree-2 engine is a *special
  case*, so the two files denote one object. **Multilinear Schwartz–Zippel
  landed** with it. Table folding is wired: **m=16 runs instantly**; the
  remaining ceiling is memory (~40 MB at m=20), not time.
- **Sumcheck is 2–17% of prover time.** Prover-level optimizations trade in
  2–4× on a term that small; statement- and protocol-level levers are 10–100×.
- **We are abandoning Plonky3.** Upstream code may be read for API shapes and
  used as a throwaway differential oracle; it never enters the trust path.

## 4b. Tensor units and the GEMM route

- ⚑ **The Amdahl ceiling for tensor silicon is 1.26× at the deployed point.**
  GEMM-shaped work is only the two LDE rows — **20.8% of prove** (21–32%
  across the range) — and **MLE folding is under 0.1%.** Trace height does not
  rescue it: swept 2^6→2^12, `hash/arith` is flat-to-rising, because the
  Merkle leaf is a sponge over the whole row and scales like the LDE.
- **The field-mapping question is SOLVED and free**: CROSS's **BAT** (Basis
  Aligned Transformation) precomputes `a·2^{8i} mod q` offline for a
  **preknown** operand, turning one modular multiply into a K×K byte-matrix
  product. **BabyBear at 31 bits ⇒ K=4, exactly CROSS's K — it transfers with
  zero modification**, and our implementation is bit-exact four independent
  ways. Measured: **BAT beats three-limb Montgomery by 3.05×** on hardware
  with *no INT8 unit*.
- ⚠ **BUT BAT needs one operand PREKNOWN.** Free for an NTT (twiddles);
  **not free for an MLE fold or a sumcheck round** (two runtime witness
  tensors). Grouping them as "also GEMM-shaped" is true and a *different
  claim*; porting by analogy would be the expensive mistake.
- **Four-step does not survive to LDE sizes**: the extra-multiply factor grows
  as √N/log N — 341× at N=2^12, **3277× at N=2^20**. Four-step and radix-2 are
  the m=2 and m=log N members of one family costing `m·N^{1+1/m}`.
- ⚠ **MoMA does not use tensor cores at all** (scalar 2^64-limb Barrett), and
  **MORPH's mapping is different** (its GEMM is base *conversion*, for
  256–753-bit moduli). Drop both from the tensor thread.
- ✅ **The fusion thesis HOLDS at toy scale and compounds**: 1.30–4.92× single
  hand-off; **2.7–7.1× at 2^20–2^22 on memory traffic alone** discounting the
  1.3–2.5 ms device sync; and across K=1→16 batched hand-offs fused per-stage
  falls **3.8–5.3× and is still falling** while unfused plateaus. ⚠ Two
  caveats that must travel with it: **unified memory makes every number a
  lower bound**, and the sync floor is wgpu's, not physics. **Structural
  finding: two wgpu devices cannot share a buffer, so fusion was unreachable
  by construction** — `bfv_ntt_gpu`, `tfhe_*_wgpu` and `private_book_bfv_wgpu`
  each still stand up their own device.

## 5. zkML

- **MXFP4 within-block exactness holds; NVFP4 preserves it but destroys the
  power-of-two-scale shift argument** — our arithmetization is MXFP4-specific.
- **Router binding must be ZERO-KNOWLEDGE** — expert selections recover 91% of
  tokens. DeepSeek-V4's early-block **hash routing** makes selection a public
  function of the token id, so binding is free there.
- **Ties are a property of the scoring function**: sigmoid-scored routers are
  *structurally* tied (only 26 distinct bf16 values in [0.9,1.0) for 256
  experts); raw-logit ~4%; V4's Sqrt(Softplus) never saturates.
- **"Append-dominant KV" is true of the computation, false of serving.** Fold
  over the **accepted token sequence**, never over cache writes.
- ⚑ **CSE does not rescue matmul.** The 2,696,666→220 figure is a
  Poseidon2/Merkle shape that re-reads subterms; a contraction's `m·k·n`
  products are pairwise **distinct**, so CSE leaves **318,040 gates at
  318,040** — **no gate-level emit of any kind gets below `m·k·n`.** At ~52
  bytes/gate that is a ~17 MB descriptor. (The conclusion "matmul needs a
  vector relation" stands; the reason was wrong.)
- **The registry commitment as shipped is a checksum no prover can open.** The
  real object is Poseidon2 over the field-element encoding, at a leaf
  granularity the circuit opens, in the layout the prover reads.

## 6. Method

- **No absence claim without**: grep `~/paperbin` first (now full-text
  extracted for all 1,218 PDFs); the **corpus AND the instrument** named in
  the claim; at least one non-eprint corpus; and an explicit flag if the
  evidence is metadata-only (arXiv's `all:` field is).
- **Write the note first and incrementally.** Every high-value loss was a lane
  that finished with no note.
- **Verification is a gate on claims, not a source of them.**
- **We build in the open. "What is ours" is not a question we ask** — the
  question is what produces the best system, and our advantage is that
  holding every layer lets us *join* things built apart.

## 7. Genuinely open

1. ~~Is the prover hash-bound?~~ **SETTLED — HASH-BOUND AT EVERY FEASIBLE
   BLOWUP.** Measured per-phase on a real IR-v2 proof: `hash/arith` = 1.01 at
   b=3 → 1.86 at b=8, **no crossover in range** (extrapolates to b≈2.9, and
   **b=2 does not exist for this circuit** — a degree-7 S-box needs
   `log_blowup ≥ 3`). The blowup knob moves the mixture 1.8× across its whole
   range and never flips it. ⇒ **the field/hash migration is worth its ~3.4×
   on the dominant term**, and the KoalaBear case strengthens.
2. **H1** — does the 61-bit design point survive a 2.4-bit margin? Now carries
   the whole joint-representation question.
3. **Can we choose the FHE modulus?** Both Zama predecessors set q_FHE = the
   proof field; 2025/719 uses BabyBear. *Our "we don't control it" was never
   verified, and checking it is cheaper than building what depends on it.*
4. **τ for the ring hash** — τ=2 leads (challenge space kills τ=1, integral
   cryptanalysis punishes τ=4); one named experiment settles it.
5. **Cross-limb binding** for ct×ct.
6. **ε_chk instantiation** and **ε_beacon** — the audit theorem's checker is
   abstract, and we hold the grinding mechanism but no beacon model.
7. **Does the virtualization threshold beat committing on Poseidon2?**
   Predicted 4–15×; a measurement, and the cheapest large number available.
8. **Is our FHE parameter point post-quantum at all?** (N=4096, log q=109,
   t=2²⁰) is a **classical**-line set nobody ships — Apple ships N=4096 with
   **83 bits** for `.quantum128`, and **N=8192 / 148 bits** when it wants
   log t ≈ 20. **If we claim PQ-128 there, that is a gap.** Not refuted
   anywhere.
9. **d=5 at KoalaBear: 128 or not?** Plonky3's `p3-security` says it reaches
   128; our `PROVEN-120-CONFIG.md` says d=5 cannot reach 120. **Probably a
   scope difference** (RS proximity leg vs whole apex composite) — **check,
   do not guess.**
