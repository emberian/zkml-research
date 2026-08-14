# VERDICTS — the single current-truth file

2026-08-13. **This file states what we believe NOW. No history, no superseded
claims, no ⚠ markers.** If a question is settled it is here in its final form;
if it is open it is in §7. Evidence lives in `notes/`; where a note and this
file disagree, **this file wins** and the note is history.

---

## 1. Fields and hashes

### 1b. ⚑ The KoalaBear case is REFUTED on this evidence (2026-08-13)

**Measured ≈1.05× on the leaf prover, not 3.36×.** All three factors fail, and
each fails differently:
- **Hash rate 1.33× is counted multiplications**; in wall clock it is **~1.02×**.
- **Blowup 2× was already inside the floor lane's 3.4×** — in its own sentence.
  And it belongs to the descriptor degree budget plus the §7.0 bug, not to the
  field.
- ⚑ **The narrowing ratio INVERTS.** Both published figures reproduce exactly
  from `R_P = 13 → 20`: `16·(1+8+R_P)` gives 352/464 and `16+128+R_P` gives
  157/164 — **so 2.24→2.83 grew because the BASELINE grew. Absolute committed
  felts go 157 → 164: 4.5% WORSE.** (Chip share of committed width is 13.35%,
  which also re-scopes the "2.11× prove" figure to **1.08× on the deployed
  batch.**)

**Other findings that change the record:**
- ⚑ **The soundness sign is backwards in our notes: LOWERING blowup BUYS
  soundness** (ε_C ∝ ρ^−3/2·|D⁰|²) — composite λ rises **+2 (leaf) to +13.5
  (wrap)**. At UDR-100, proof size varies 1.13× and verify 1.29× across
  lb=2…8 while **prove varies 39×**. Measured: `(6,19)→(2,57)` is **13.13×
  faster at 4096 rows**, 1.74× at 64 — **the lever scales with trace height,
  and zkML is 2^16–2^20.**
- **KoalaBear MANDATES lb ≤ 3** (two-adicity 24 against a 2^21 wrap), so with
  the floor at 3 it pins lb=3 exactly.
- ⚑ **Our commit bound is five years stale — worth +17–21 real bits.** The d=5
  tension resolves: both `d`s are the *extension* degree, there is no
  `p3-security` crate (it is `uni-stark/src/security.rs`), and their
  KoalaBear/128 line is **WHIR's quintic at ρ=1/4 on a 2025 bound** while ours
  is **FRI on BCIKS20 (2020)**. Both true. **That staleness is worth more than
  the extension-degree flag day PROVEN-120 was buying.** ⚠ Citation-strength
  caveat: BCSS25 states no FRI theorem and its Thm 4.3 plugs into a personal
  communication.
- **Flag day: two items are a REDESIGN, not a swap.** 450 files / 4,216
  literals / **50 independent modulus declarations** in metatheory (minidregg
  has 1). ⚑ **Ext6 stops existing** (`3 ∤ p_KB−1`, so no binomial degree-6
  extension — 11 files plus ErrorBudget120's 137-bit target), and ⚑ **`X⁴−11`
  becomes reducible** — leave it and the "quartic field" is **a ring with zero
  divisors, silently.**

**Recommendation: fix the `p3-fri` bug, repair our own gate, drop the blowup
at BabyBear. KoalaBear is NOT recommended on this evidence** until the
recursion engine is profiled and plonky3's own `R_P = 20 vs 85` docblock
discrepancy is settled.

> ✅ **08-14: the first two are DONE (§7.0).** The third is **priced, not
> landed**: in exact permutation counts the drop is **prover ÷15.2 · verifier
> ×2.28 · wire ×~2.4 · UDR +20 bits · row ceiling ×16**, which is a genuine
> two-sided trade rather than a free win, and the per-descriptor knob it really
> wants needs a `num_queries` pin in the recursion verifier first.
> `notes/blowup-drop.md`. ⚠ **The "13.13× at 4096 rows" quoted below is wall
> clock on a contended box** — the same case re-measured today reads 7.78×. Use
> the counts.

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
- ⚑ **The grind is 46.3% of our proven soundness, and `pow=16` is OPTIMAL.**
  `pow` is **additive and regime-free**; a query is **multiplicative and
  regime-bound** (0.9776 bits at UDR, 3 at JBR, 6 at withdrawn CBR at lb=6).
  **At UDR — the only regime still standing — the 16 grind bits are 46.3% of
  the deployed 34.58-bit column.** Exchange rate **17 / 6 / 3 queries**,
  two-sided. ⚠ *A cost argument that says "the grind replaces N queries"
  without naming its regime has quoted one of those three — and the flattering
  one is the withdrawn regime.* The closed-form optimum is **p\* = 15.97** on
  the wire-bytes/verify-ms axis dregg actually optimizes — **`pow=16` is
  optimal for the same reason the blowup was, and nobody had computed it.**
  (Also checked rather than assumed: `sample_bits` delivers **15.999953**
  bits, not 16.)
- ⚑⚑ **OUR OWN HARDENING COMMIT REMOVED THE GRIND'S PARALLELISM.** `90680ee7d`
  swapped upstream's `find_map_any` for **`find_map_first`** so the PoW
  witness would stop racing — correct, every byte-parity gate needs it — but
  `find_first` must prove no *lower* candidate exists. Measured critical path:
  **1 thread 20,766 batches; 12 threads 20,766. Scale 1.00.** Wall clock gets
  *worse* (24.4 → 28.9 ms) and total work rises **5.9×** as eleven workers
  scan above the answer and lose the `min`. **The hardening-commit-disarms-a-
  guard class, in our own tree, found by measuring rather than reading.**
  ✅ **LANDED 2026-08-14** (`11cff8852`, `00b2cf2d5`, `81ddc8566`) — **all five
  grind sites**, and the safety argument is structural rather than tested:
  `windowed_find_map_first` reduces by **lowest unit index**, making it
  *`find_map_first` with the early exit deleted.* **Byte-for-byte verified four
  ways with no clock**, including minimality checked against the *definition*
  exhaustively (476,286 candidates below the returned witnesses, all invalid,
  so the differential oracle cannot drift into agreement) and window invariance
  across nine sizes from 1 to 2^24. **Nothing re-emits: no wire format,
  descriptor, VK, or re-genesis.**
  **Measured, latency and work in separate columns**: critical path **10.6×
  mean / 11.8× p99** at T=12, **total work +12.6%**; BN254 outer **9.49×**
  (28,954 → 3,147 calls, +13% work). Window `c = 1/4` chosen by **minimax over
  the one constant counts cannot see** (a 7.1 µs per-window barrier), not at a
  point estimate — and **`c = 8` is REFUTED** (8.29× work at twice the p99).
  ⚑ **And the honest inversion: this fix RAISES grind's share of prover WORK**
  (23.2% → 25.4% at lb=6). It buys latency, *a share-of-work percentage cannot
  show that*, and the latency share is not computable from anything measured —
  so the lane declined to quote one.
  ⚑ **Two findings beyond the brief**: **rayon leaves `Range<u64>`
  unindexed**, so the first version's window split only on steal and delivered
  **2.47×, not ~10×** — *a parallel primitive whose parallelism is conditional
  on scheduling luck passes every correctness test*, and it was caught only
  because derived and counted numbers were both printed. And
  **`apex_shrink_bn254_tooth` had been RED since 2026-08-08**, `#[ignore]`d as
  `"SLOW"` — its sibling got a mint-split fix and the twin did not; now fixed.
  **Original prototype note — fix:** windowed parallel `min`: scan a bounded window fully in parallel,
  reduce with `min`; the first non-empty window's minimum **is** the global
  minimum, so it returns **byte-for-byte the same witness** (same predicate,
  query indices, proof bytes, VK). **7.49× on the critical path at 12
  threads**, and **at c=8 the work is literally fixed — the "fixed-work
  alternative" without a VDF.** *Do not lower a security parameter to fix a
  scheduling bug that has a free fix* — and the fix moves p\* **up** ~3 bits,
  making 16 comfortably right rather than marginally right.
  ⚠ Refuted by construction: *"move the grind off the critical path"* — its
  input is the completed FRI commit-phase transcript, which does not exist
  earlier; grinding anything earlier binds less and is a weaker protocol.
- **Variance, measured over 256 transcripts**: mean 12.8 ms, **p99 52.6 ms,
  worst-of-256 75.5 ms against a 69 ms whole-prove budget**; tail matches
  `e^−k` to two decimals. The 40.8 ms draw that manufactured a false optimum
  was the **p96**.
- ⚠ **A tooth that did not exist**: the six `InvalidPowWitness` rejections in
  `deployed_refines_verifier_teeth.rs` are all **transcript desyncs** —
  nothing ever mutated the witness. A constructive falsifier now exists
  (`find_map_first` returns the *minimal* valid witness, so `w−1` provably
  fails): tamper in place, refuse, restore, accept.
- ⚑ **"`lb=6` is 2.9× off the optimum" is REFUTED — it was a grind draw.**
  `query_proof_of_work_bits=16` is **~25% of a deployed prove** (47,917
  permutations / 8.2 ms), depends on **neither blowup nor trace**, and is
  **exponentially distributed** — it drew 0.04 / 8.2 / 10.1 / 31.9 / 40.0 /
  40.8 ms across one ladder. At **pow=0** the curve is strictly monotone
  (14.9 / 20.3 / 34.9 / 67.9 / 120.6 / 243.3 ms) with **lb=3 fastest by
  1.4×**. The published lb=3 point paid 40.8 ms of grind against lb=4's 10.1 —
  **that 30 ms of coin flip *was* the reported optimum.** (The published
  `prove` column also included a full self-verify.)
- ✅ **`num_queries` PINNED 2026-08-14** (`52e1fab` in `~/dev/plonky3-recursion`)
  — at the chokepoint, as an **equality** mirroring native (more queries than
  configured is refused too, or Fiat–Shamir diverges), checked before the
  challenger sampling loop so an attacker-chosen count never drives
  `sample_bits`. Both constructors take it positionally, so **all 12 call sites
  were arity errors** — none could silently keep the old behaviour.
  ⚑ **The falsifier proved the hole was REAL**: with the pin disarmed, a
  **one-query proof verified** (`Ok(())` — *that* is the finding, not the
  failed assert). Re-armed, 8/8 green. It also caught a drift the pin creates:
  `test_fri_verifier_rejects_zero_query_proof` would have been short-circuited
  by the new check and **gone on passing while testing something else.**
  **Soundness delta: 16 → 34 bits at UDR** — the only unconditionally proven
  regime. (19→73 is the *idealised* Johnson column, 22→130 the *withdrawn*
  capacity one; the exported ledger carries only those two and **has no UDR
  column at all**.) Query column only; `ε_C` untouched and deliberately not
  composed.
  ⚑⚑ **ACTION FOR EMBER: the pin does NOT reach breadstuffs yet.**
  `breadstuffs/Cargo.toml:370-373` pins `rev = "fc3c6df"`. It needs `52e1fab`
  **pushed** and those four lines bumped — pushing is outward-facing so the
  lane correctly left it. **Until then the hole is still open in breadstuffs.**
  ⚑ **A NEW hole found by the same mechanism, deliberately NOT fixed and NOT
  quantified**: **`max_log_arity` is unpinned.** `FriProofTargets::new` reads
  `log_arities` off the proof; native enforces `1 ≤ log_arity ≤ max`. The
  *sum* is pinned transitively but **the partition is attacker-chosen and
  `log_arity = 0` is unrejected** — a zero-arity phase leaves `cumulative_bits`
  unadvanced, so `folded_height_after` repeats and the roll-in `position()`
  lookup can route to the wrong phase. **The lane states it has not derived
  direction or magnitude and that no number should be quoted.** ⚠ Sequencing
  note it left: `test_fri_verifier_rejects_per_query_schedule_mismatch` tampers
  by `log_arity += 1` under `max_log_arity = 1`, so a native check fires first
  and **that test stops exercising what it names.**
  **Family audit**: `log_blowup`, `log_final_poly_len`, `commit_pow_bits`,
  `query_pow_bits`, MMCS-on — all pinned; `cap_height` derived from the
  commitment exactly as native does.
  ⚠ **And a CI job has been unrunnable for two months**: `recursion/examples/
  common/mod.rs` has 43 `E0004`s since `ccebf66` (2026-06-13), and
  `.github/workflows/ci.yml:106` *runs* `--example recursive_aggregation`.
  **Fail-open gate class.**
- ~~`num_queries` is unpinned in the recursion verifier~~ (original entry) — read from the
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
- ✅ **THE SEAM IS CLOSED (2026-08-14).** S3 (`Selvage/QuadraticSumcheck.lean`)
  and S4 (`SumcheckRbr.lean` + `BaseFoldRbr.lean`, `basefoldSumcheckRbr`) both
  landed, plus four layers past them. **No new commitment abstraction was
  built — `OpeningScheme` is reused**, as the landscape verdict predicted.
  ⚑ **And the `raw_commit_terminal_differs_f5` ambiguity dissolved — it was
  never a value ambiguity.** The raw word is an *honest commitment to a
  DIFFERENT table*: `rawPoly = 1 + 2X` reads the values `[1,2]` as
  *coefficients*, its table is `[1,3]`, and that table's MLE at 3 genuinely
  **is** 2. **Two statements, not two answers to one.** Proved, all axiom-
  pinned, no `sorry`, no obligations needed:
  `basefoldExactClaim_value_unique` (two strict claims over the *same* word
  and point carry the *same* value — **nothing probabilistic**, just
  interpolant uniqueness plus Möbius injectivity) · `raw_commit_not_exact_
  claim_at_honest_f5` (deterministic) · `raw_commit_wrong_value_bound_f5`
  (against an adaptive prover it survives on **at most 2 challenges in 5**,
  where completeness accepted its descent at *every* challenge — **that is the
  boundary crossed**) · `raw_root_ne_honest_root_f5` (**different roots, so
  `value_unique` is never asked to reconcile them** — pinning has two halves,
  root→word and word→value, and **both are theorems**).
  ⚑ **S4 was an ISLAND** — `basefoldSumcheckRbr` had **zero consumers**; the
  ledger path ran through the *operational* `basefoldIor_exact_sound` instead.
  Now wired to Selvage's unconditional FS keystone, giving straightline
  `(t + m)·2/|F|`. *A landed theorem nothing consumes is the
  gating-defaults-to-silence class in Lean.*
  ⚠ **NOT proved, stated in the docstrings and the commit**: the reduction's
  witness type is `Unit`, so this is **straightline soundness with a TRIVIAL
  EXTRACTOR — not extraction of the committed table**, which is the commitment
  layer's job and is composed by no theorem. The RS/proximity leg is still not
  product-composed into the knowledge state. And **there are now two
  accountings of one leg** (operational IOR bound vs RBR instance) agreeing at
  `m·2/|F|`; one should be *derived* from the other — flagged, deliberately
  not collapsed unilaterally.
- ~~The multilinear seam is ONE `RbrKnowledgeSoundness` instance~~ (predicted,
  and it held) No hash-based multilinear PCS is indexed by an evaluation
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
  strictly Pareto, no trade to price. ⚠ The "ratio grows as α falls" reading is **refuted** — see §1b: it grew
  because the *baseline* grew with `R_P`, and absolute committed felts get
  4.5% worse.
  ✅ **LANDED 2026-08-14** (`permEmissionNarrow`, `daa207ae7`): **352 → 141
  gates**, ops/row 2,668 → 2,246, and `max_constraint_degree` **7 on both
  arms — pinned on both EMITTED objects** (`the_degree_is_seven_on_both_arms`),
  since identical degree is the half of a Pareto claim a virtualization gets
  wrong. All 11 deployed table-AIR artifacts re-emitted **byte-identical**;
  nothing deployed moved.
  **The relating theorem, and it is an identity over ℤ rather than a
  congruence** — so nothing hides in a modulus: the `j`-th wide internal gate
  body is `c_j·δ` for the *one* narrow body, `c_j = 1` on fifteen lanes and
  `p−1` on lane 0, with `lane_zero_multiplier_is_a_unit` cancelling `p−1` ⇒
  **the one narrow gate holds iff all sixteen wide ones do.** Then
  `narrow_accepts_exactly_the_wide_witnesses`, stated against an arbitrary
  block — **deliberately not an ∃-over-a-witness.**
  ⚑ **A finding the brief did not have: the sharing node is a PRECONDITION
  here, not an optimization.** The narrow arm has **no tree spelling** — one
  internal round multiplies a tree state ~16×, so thirteen is ~5·10^18 nodes
  — which means **§6b's tree-vs-DAG agreement oracle has no narrow
  counterpart by construction.** An instrument is lost, not just a cost saved.
  ✅ **UNBLOCKED 2026-08-14** (`f1718d513`): `poseidon2_permute_aux_witness_narrow`
  writes the 141, and `poseidon2_wide_aux_from_narrow` is
  **`narrowSat_forces_the_trace` as a program** — rebuilding all 352 from seed
  + 141 **without calling `poseidon2_trace`**. The AIR stayed in Lean (existing
  gate lists wrapped in a `TableAir`; **no gate authored**), and the eleven
  deployed artifacts are untouched because it does not route through
  `EmitTableAirs`.
  ⚑ **Measured in COUNTS, and the counts correct the circulating figure:**
  per-chip **2.3439× committed cells but only 1.9733× prover permutations**
  (flat in height to four figures) — *the widely-quoted "2.11× prove" is a
  wall-clock number*; cells fall 2.34× while hashing falls 1.97×, because the
  quotient and FRI terms do not follow the width. **Per-batch: 1.0763×.**
  ⚑ **And a flattering layer one level ABOVE the per-chip/per-batch split**:
  the prover commits **three rounds**, and narrowing the chip shrinks only the
  first (the bus interface is unchanged so the LogUp trace stays 12 wide;
  degree is unchanged at 7 so the quotient stays 32 wide). **Stopping at main
  traces reports 1.1023×** — a third number, flattering, and reachable by an
  honest-looking choice of denominator.
  ✅ **Cross-validated**: the `main + LogUp` row reproduces the independent
  span-dump census *exactly* (22,992 cells, 2,936 leaf perms, 13.35% chip
  share) — **two instruments, two days, same numbers.** And debug and release
  produced **byte-identical tables**, which is the counts methodology
  demonstrating its own contention-immunity.
  ⚑ **Where this actually pays: 13.35% is the THINNEST chip workload.** The
  recursion tower is ~75% in-circuit Poseidon2, where the factor approaches
  the full **1.97×**. The per-batch 1.08× is a floor, not a ceiling.
  ⚠ Named seam: **no provenance gate binds the two checked-in fixtures to the
  Lean emission** — same shape as `table-airs/` being invisible to
  `verify_provenance`. The shape pin and witness/falsifier pair stand
  meanwhile; that is a check, not a hash.
  ⚠ Honestly undone: that the narrow emission's literal gate list, *resolved
  through `shareVals`*, **is** the equation system the theorems reason about
  — needs a `shareVals` prefix lemma plus a fold invariant (~a day), **and it
  would close the same gap for the WIDE arm, which never had it either.**
  Currently case-checked on six row windows and labelled as case-testing. ⚠ The `map_write_chip` 227 ms "corroboration"
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

## 5a. The matmul contraction (landed)

- **The `foldl → Finset.sum` bridge is built**, in two *named* steps so the
  discard point is a line you can point at (`foldl_add_eq_listSum` →
  `listSum_finRange_eq_sum` → `foldl_finRange_eq_sum` → `denote_matmul_sum`).
- ⚑ **My brief named the wrong property: the load-bearing one is
  ASSOCIATIVITY, not commutativity.** IEEE-754 addition *is* commutative and
  is *not* associative. And step 2 has **no counterexample at all** —
  `Finset.sum` over `Fin k` cannot be *written* without commutativity, so its
  refutation is a **type error, not a number.** A saturating scalar reading
  refutes the bridge on the real denotation (`run … = 5` while its own
  `Finset.sum` is `9`, kernel-decided).
- **Padding needs NO `Theory/` change** — correcting a recorded fork (a `pad`
  op vs non-dyadic MLE machinery): **neither.** Zero-extension is a fact about
  *tables*, so no `TOp` constructor moves and no denotation theorem changes
  shape. The pad becomes a commitment-layer obligation.
- **The contraction face**: `mle₂_contraction` (`Ĉ(x,y) = Σ_p Â(x,p)·B̂(p,y)`
  at **every** `(x,y)`), two-block Schwartz–Zippel, and
  `matmul_sumcheck_soundness ≤ (μ+ν)/|F| + κ·3/|F|`. It needs **no `eq`
  factor** (outer indices bound first) and is **degree 2 on a degree-3 wire**.
  A forged output table is exhibited *surviving* at `x=1`, so the `(μ+ν)/|F|`
  event is nonempty.
- ⚑ **Measured** (`[2,1024]·[1024,128]`, MNIST layer 1 padded): transcript
  **51 field elements = 408 bytes** against the AIR route's **314,000 gates /
  ≈27 MB descriptor**. But: output 6.4 ms · **bind-outer 9.6 ms · sumcheck
  rounds 0.5 ms** — **the sumcheck is 5% of the prover.** *The lever is the
  partial evaluation, not the rounds.* ⚠ And the 408 bytes **omits two
  multilinear openings that do not exist yet**, so it is a ratio for the
  *relation*, not for a system.

## 5b. Verifiable training (first pieces landed)

- ✅ **The rank-1 gradient check is PROVED and BUILT**
  (`Selvage/Rank1GradientCheck.lean`, 545 lines, no `sorry`).
  `mle_outerTable` gives `(δ⊗x)^(r) = δ̂(r_row)·x̂(r_col)` over **any
  `CommRing`**, from three Mathlib facts. `rank1_sound`: a wrong `G` survives
  with probability **≤ (mᵢ+mⱼ)/|F|**, by the defect argument. **The
  two-variable case cost zero extra work** — splitting `r` into halves is a
  fact about the check, not about the measure.
- ⚑ **The sharp tooth is FREE**: `rank1_sound` carries **no rank hypothesis**,
  so *every other rank-1 matrix* is priced at the same bound —
  `rank1_refuses_other_outer_products`. **The "certifies some outer product"
  vacuity is excluded by theorem, not by testing.**
- **`rankK_sound`**: the batch shape costs K verifier multiplications and
  **the bound does not grow with K**.
- **`sgd_step_sound`** (five lines): **the whole SGD step for a linear layer
  is three openings at one common point, zero rounds — and the gradient is
  never committed.**
- **Measured at 4096×4096 (m=24)**: **2.5×10⁴ ops for the check vs 1.7×10⁹
  for the circuit ≈ 7×10⁴×**, `O(2^{m/2})` vs `O(2^m)`.
- ⚠ **THE HONEST HALF, and it is the useful finding**: the check removes the
  n² **proof**, not the n² **commitment**. The step still commits 2^24 felts
  for `W'` (263 ms hash proxy vs 116 µs for δ and x). **Once the gradient
  proof is 10⁴× cheaper, the commitment IS the step** — which is direct
  evidence for the low-rank-update route (`DARK-TRAINING.md` §3), where the
  committed object per step is 2rd instead of d².
- ⚠ **And the bound stated plainly**: `24/2^31 ≈ 2^-26.1` **is not a security
  level.** The fix is the **field** (degree-4 extension ≈ 116 bits), never the
  layer size — the bound is logarithmic in n.
- ⚠ Teeth limit the lane found itself: **the counting teeth cannot see a
  transposed row/column convention** (the wrong gradient's accepting set is
  symmetric). An asymmetric accept/refuse pair is the real index-order
  detector and is carried on both sides.
- **Not covered**: δ is not verified to be the correct backpropagated error
  (that is the chain, and needs a real sumcheck); the nonlinearity's
  derivative; conv (a correlation, unexamined); the data; and exactness over a
  million accumulating steps.

## 5c. Low-rank updates (landed) — and the break-even is not where I expected

`Assurance/ZkmlLowRankUpdate.lean` (758 lines, no `sorry`, 21 clean axiom pins,
`c060efa`) + a counts-only Rust pricer (`3ffa609`, **no clock in the file**).

⚑ **My question — "is rank-`r` literally `rankK_sound`?" — answered as a
CORRECTION: yes, for ONE of two designs, and they are not the same protocol.**
- **`r`-openings design** (`A,B` as `2r` separately-opened vectors): the
  summand **is** `rankK`'s summand *by `rfl`*, giving `(μ+ν)/|F|` with no `κ`.
  **But it does not save the commitment** — which was the entire point.
- **One-commitment design** (the one that saves `2rd` felts): the verifier
  holds one opening of each and **cannot evaluate the inner sum**, so it must
  sumcheck `κ = log₂ r` variables — **`(μ+ν)/|F| + κ·3/|F|`, which DOES grow
  with `r`.**
⚠ **And the honest counter-cut**: that sumcheck is **128 field ops at r=64**.
*The correction is real in the error bound (under 1 bit at every usable rank)
and nothing at all in the cost.*

**Both proofs are instantiations, not twins**: `lowRank_delta_is_the_matmul_
output` shows `W' − W` **is** `matmulTable A B`, so the landed contraction
argument transfers with nothing re-derived, and `matmulTable_rank_one`
collapses `κ=0` to the outer product — **the rank-1 rung is the `r=1`
instance.**

**The inference side, which is the genuinely new part** (`matVec` did not exist
anywhere in the tree): `matVec_matmulTable` proves `(A·B)v = A(Bv)` — *the
cheap order is legal* — and `matVec_chainUpdate` is what makes the **chain**
cheap: **the `d²` term appears ONCE for a list of any length.** (Nicely, *"the
base does not depend on A,B"* is `rfl` and is deliberately **not** dressed up
as a theorem.)

**Pricing — calibrated, not asserted**: the tree law reproduces
`phase-profile.md`'s measured Merkle column to a constant 2 at all five rungs,
**and the binary refuses to print if it stops doing so.** At d=4096: full `W'`
= 16,777,216 felts / 8,404,991 perms; low-rank r=16 = 131,072 / 65,662 —
**128× on both**, blowup-independent.
- ⚑ **Break-even rank is `d/2` = 2048.** Nobody uses a rank near that, so
  **the commitment is never the reason to stop.**
- ⚑ **The break-even that BINDS is in STEPS**: merging deltas back costs one
  recommit, so `T·2rd > d²` gives **T = 128 steps at d=4096, r=16.** *That is
  the real design constraint, and it is not the one I briefed.*
- ⚑ **The natural `d×r` layout of `A` costs 2.0× more PERMUTATIONS than
  transposing it** at r=8, for **identical felts** — only the wide layout
  reaches `d/(2r)`. **Invisible in a felt count**, and the same shape as the
  LDE's per-call/per-narrow-matrix finding.

**Teeth**: the vacuity to fear was *"certifies low rank"* vs *"certifies THIS
delta"* — `lowRank_refuses_another_low_rank_update` refuses a genuinely
different rank-2 delta. **Gauge freedom exhibited nonempty** (`A,B` bound only
up to `GL_r`). 9/25 false accepts against the theorem's 10/25 — nearly
attained.

⚠ **Undone, and the chain theorem makes one of them MORE urgent**: `A,B` is
not verified to be the *correct* projection; the nonlinearity; **accumulated
exactness over many steps** — which matters more now that the chain is cheap;
the positional `OpeningScheme`; Fiat–Shamir; and `r` must be a power of two.

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

0. ✅ **CLOSED 2026-08-14 — the bug is fixed, the gate is repaired, the drop is
   priced. The config flip is NOT landed and the reason is in the note.**
   `notes/blowup-drop.md`; `breadstuffs` `4e6089484` + `26b33a37a`, `minidregg`
   `4889368`. What it was: the "degree-7 S-box needs `log_blowup ≥ 3`" floor was
   **one `.bit_reverse_rows()` too many** in `p3-fri`'s
   `get_evaluations_on_domain` extrapolation path — right values, wrong rows,
   wrong quotient, a well-formed proof the verifier rejects — **and
   `fri_blowup_global_knob_survey.rs:685-690` asserted that the refusal MUST
   happen, so our gate would have gone red when the bug was fixed.**
   - **Fixed** in the `[patch]`ed `vendor/plonky3-fri-82cfad73`. **PR #1982 is
     the same change and is STILL OPEN / CHANGES_REQUESTED** (checked 08-14), so
     we carry it with the provenance recorded.
   - **Gate inverted** to assert the correct behaviour, and **all twelve survey
     descriptors — chip-bearing and chip-free — now prove AND self-verify at
     `(2,57)`.** The per-descriptor "floor" column reads `log_blowup 2` for all.
   - **Verified by construction**, not by outcome: both PCS paths against an
     independent coset DFT (with the buggy answer built constructively and
     asserted to differ), a degree-7 AIR verifying at `lb=2`, **and a corrupted
     trace still rejecting** — `circuit/tests/fri_extrapolation_row_order.rs`.
   - ⚑ **The win, in exact permutation counts** (this box was at load 30–52; wall
     clock here is not evidence): **prover 15.19× fewer**, and the 38 extra
     queries cost it **five permutations**. **Verifier 2.28× MORE** — which
     reproduces the 2026-08-04 "why 6 stays" verdict exactly. The trade is real
     and two-sided; the note's §7 says what the flip needs first (a
     **`num_queries` pin in the recursion verifier**, which is a soundness hole
     on its own).
   - ⚑ **A model calibrated on a censored sample.** §1b's byte predictor was
     fitted only on descriptors that *could be measured* at `(2,57)` — i.e. with
     every chip-bearing one excluded by the bug — and missed them by up to
     **99%**. Refitted with a chip indicator: error **76–99% → 0.0–4.3%**, and
     adding the term moved the other two coefficients by **0.01%**.

1. ~~Is the prover hash-bound?~~ **SETTLED — HASH-BOUND AT EVERY FEASIBLE
   BLOWUP.** Measured per-phase on a real IR-v2 proof: `hash/arith` = 1.01 at
   b=3 → 1.86 at b=8, **no crossover in range** (extrapolates to b≈2.9, and
   **b=2 does not exist for this circuit** — a degree-7 S-box needs
   `log_blowup ≥ 3` — ⚠ **which is the bug in §7.0, not a law**). The blowup
   knob moves the mixture 1.8× across its whole range and never flips it.
   ⚠ **But the "~3.4× migration" does NOT follow — see §1b.**
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

---

## 7a. ⚑ A specimen that justifies the axiom-pin discipline

While a lane worked, **HEAD was red inside a live sibling's file**
(`Selvage/BaseFoldBcsQuerySamplingJoint.lean` at `69a2ecd`): a **parse error**
— `omit`/`set_option … in` placed after a docstring — truncated a declaration,
and **the theorem downstream elaborated with `sorry` IN ITS STATEMENT.** The
printed signature read `… ≤ ↑m * (3 / sorry) + …`.

**It was caught by the `#guard_msgs`-pinned `#print axioms`, on `sorryAx`.**
Nothing else would have: the file compiled, the theorem existed, its name was
right, and a reader skimming would have seen a bound. **A `sorry` in a
STATEMENT is invisible to every check except an axiom pin** — and this is the
first time we have seen one in the wild rather than reasoned about it.
(The sibling fixed it in-session; `lake build Selvage` is green at 2,486 jobs.
⚠ Anyone holding a green claim about `acceptedSeedRawCommittedIor_coherent_
exact_sound` should re-check it at that lane's settled commit.)

## 7b. Two instrument defects worth more than most findings

- ⚑ **A MODEL CALIBRATED ON A SAMPLE THE BUG HAD CENSORED.** A byte predictor
  was fitted on the descriptors that *could be measured* at (2,57) — i.e. with
  **every chip-bearing one excluded by the `p3-fri` bug** — and then missed
  those by up to **99%**, *while reporting a tidy ±63% confidence about a
  population it had never seen.* Refitted with a chip indicator: error
  **76–99% → 0.0–4.3%**, and adding the term moved the other two coefficients
  by **0.01%** — *the tell that it is structure, not curve-fitting.*
  **The general form: a bug that silently filters your sample corrupts every
  model fitted downstream, and the model's own error bars will look fine.**
- ⚑ **Phase counters were process-global and only the HEADER said so.** Five
  tests bracket a `prove` with a shared counter; `--test-threads=1` was
  *documented and never enforced*, so **every default invocation was silently
  corruptible.** Fixed with a file-scoped mutex — and verified the way that
  matters: **all six pass under default parallelism with a count table
  byte-identical to the serial run**, the same contention-immunity
  demonstration the narrow-emission lane made with debug-vs-release.

## 8. The through-line, 2026-08-13/14

**Every measurement lane found that the thing we were optimizing was not the
cost, and the actual cost was somewhere nobody had looked.** Six for six:

| we believed | measured |
|---|---|
| the sumcheck is the prover | **2–17% of it** |
| matmul's cost is the sumcheck | **5%** — the lever is the partial evaluation |
| virtualize Poseidon2 with a sumcheck | **the sumcheck loses**; in-AIR narrowing wins |
| the exchange rate is 78–308× | **~5× in wall clock** — the unit was never converted |
| the blowup floor is mathematics | **a one-line upstream bug we froze as a law** |
| the rank-1 check removes the n² cost | **removes the n² PROOF; the COMMITMENT becomes the step** |
| grinding is a small tax | **25% of prove, 46% of proven soundness, and our own hardening commit un-parallelised it** |

And the *shape* of the error is consistent: **a plausible cost model, never
converted into the unit that bills.** Counted multiplications instead of
nanoseconds. Asymptotics instead of constants at our sizes. A ratio for a
relation quoted as a ratio for a system. A distribution's tail read as a mean.

**The rule that falls out**: *before optimizing a term, measure its share.*
Every lane that measured first found the target somewhere else; every estimate
we carried without a measurement was wrong in the same direction — flattering
the thing we had already decided to work on.
