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
  > ⚑ **09-04: the caveat is STALE, and so is the crate claim.** BCSS25 =
  > eprint 2025/2055; its `[Sta25]` ("StarkWare Team. S-two whitepaper. 2025.
  > Personal communication") is **eprint 2026/532** (Mar 2026; App. A.2 **Thm 28**
  > "CA over given sets", **Thm 29** weighted, Johnson regime, from Thm 25
  > [BCI+20, BCH+25]); `[Hab25]` is **eprint 2025/2110**. Both public, both in the
  > mirror and `~/paperbin`. 532's **Thm 19** is a FRI theorem on the 2025 bounds —
  > for *circle* FRI over M31; classic-FRI [HHM25] is still unpublished by 532's
  > own text. So the +17–21-bit commit-column upgrade rests on a readable chain
  > (a vendor whitepaper, not peer review); re-derivation is a second ε_C column
  > in `FriLedger.lean` beside the old one, whose `:270` "Neither is public" is
  > now stale. And `p3-security` **has been a crate since 2026-07-08**, alongside
  > `uni-stark/src/security.rs`. `notes/proximity-delta-2026-09-04.md` §3.2–3.3.
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
  > ⚑ **09-04: upstream now labels it legacy.** Plonky3 `p3-security` v0.7.0
  > (#2018, merged 2026-09-03) added `legacy_conjectured_error = log_blowup ·
  > num_queries + query_pow` — character-for-character our `capacityBits`. Its
  > non-legacy "conjectured" column is the DG25 random-words heuristic, [DERIVED]
  > **128.40** at (6,19,16) over BabyBear⁴; `SecurityAssumption::CapacityBound`
  > still exists upstream. The rule stands, now citable against upstream's own
  > label. Grinding "additive and regime-free" holds at three sources (2026/532
  > §5, `p3-security/src/grinding.rs`, soundcalc `apply_grinding`) with one
  > refinement: additive *to the round it precedes*; commit-phase PoW (ours = 0)
  > is the one additive lever on ε_C. `notes/proximity-delta-2026-09-04.md` §3.3–3.4.
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
- ⚑ **The coefficient-matmul route's provable noise budget and its freedom from
  the cross-limb expressibility hole are THE SAME PROPERTY** (2026-08-14): a
  public integer scalar acts coefficientwise, which is why `stepR_noise_le`
  carries no `δ_R` factor AND why limb `i`'s output is a function of limb `i`'s
  input (`Bfv.scalarStep_limb_local`). One property, two payoffs. The provenance
  half of the hole survives there anyway — see §7.5.

## 3b. ⚑ ZERO-EMULATION vFHE: the limb primes are OURS, and that dissolves the problem

The ECFFT exploration (2026-08-16, `notes/ecfft.md`) ended in the strongest
shape: **the exotic tool is blocked by its own theorems, and the prize does
not need it.**

- **ECFFT is PQ-neutral, confirmed at source** (eprint 2022/1542 Remark 2:
  QROM-secure compilation; nothing committed in the curve group; an
  adversarially chosen curve is inert — the advice is deterministically
  checkable, setup transparent). *Ember's question answered: no hedge needed.*
- **But it dies on REACH, not price**: Thm 8/9 caps the 2-group at
  `2^k ≤ 2√q`, so our 36-bit primes top out at trace height **2^18 < the 2^19
  the family needs** — and Thm 13's error term **exceeds 1** at our
  blocklengths with base-field challenges. (Constants would have been fine:
  ~4–6× on the prover-relevant transform.)
- ⚠ My premise was wrong twice: the fold set is **degree 4096, not 8192**, and
  the measured limb 2-adicities are **13/14/17**, not "≥14."
- ⚑⚑ **THE DOMINATING MOVE: the limb primes are GREENFIELD — pick better
  ones.** Sieved: **68 candidate 36-bit and 151 candidate 37-bit primes with
  2-adicity 24**; concrete triple `0xfed000001 / 0xfd9000001 / 0x1ff5000001`
  lands **logQ = 108.978 vs deployed 109.000**. Then **classic FRI reaches
  height 2^21 at blowup 8, over each limb's own prime, ZERO emulation** —
  the measured 4.80× committed-element deletion — **at overhead 1.00×.**
  Cost: **a re-genesis flag day + an H1 re-measure + an [UNRUN] fhe.rs smoke
  test.** *The greenfield doctrine, paying exactly as written: the answer to
  "what does it cost" is "a rebuild."*
- ⚠ **Limb-native proving REOPENS the cross-limb provenance hole** that
  row-interleaving closed — the Z_Q-sumcheck lane is the candidate binding.
- **If EC-FRI is ever wanted**: it reduces to plain RS over exotic domains,
  our cone is ready at the definition level (`dom : ι ↪ F` agnostic, UD gap
  proved), and the fold needs **6 named missing lemmas** — only one with real
  AG content.

## 3c. ⚑ THE PQ-VEGA PATH — the surpass architecture, now priced

From the Nebula/Vega read (`notes/nebula-vega-lessons.md`, both papers at
source; Vega = eprint 2025/2094, **P-256+Hyrax/DL re-confirmed independently
at §4.3/§7**):

- **The DL dividend is ~10³× at the seam**: their Nova fold verifier ≈10,000
  R1CS gates vs our wrap's 38,168 perms ≈ **9.5M constraint-equivalents by
  their own conversion.** Mechanism: *Pedersen adds, Merkle opens* — plus the
  shape change (fold now, verify once at the end).
- ⚑ **THE PQ-VEGA PRICING `[DERIVED]`**: a Nova-shaped fold over the
  **dual-mode MSIS commitment** ≈ **4–7×10³ R_q rows/step ≈ 4–8% of the
  92,396-row FS bill it rides beside.** Ordering: **DL fold 1× < PQ fold
  ~4–50× < Merkle wrap ~10³×.** γ-grinding under folding: negligible,
  class-unchanged; the genuinely new term is `Q·ε_MSIS` per absorbed
  commitment. **Neo's configuration is killed twice by the dual-mode**
  (ring-native absorb at 27.4 rows/elt; the κ=24 commit-not-absorb cap).
- ⚑ **The switchboard rides THIS path, not the deployed stack**: pay-per-use
  requires a **free zero-commitment — true of Pedersen AND Ajtai, false of
  Merkle.** (And Nebula's 30× is the *memory* technique; the 260× is the
  *switchboard* — different mechanisms, do not conflate.)
- ⚑ **Nebula's memory lemma IS our `TwistContinuity` keystone and is NOT
  DL-bound** — Lemma 2 (multiset invariant ⟺ sequential consistency, both
  directions) + fingerprint corollary + two-layer IVC. **Top-ranked transfer:
  pure combinatorics, LogUp + roots-before-challenge machinery already on
  shelf.** ⚠ Their model has no `free`; ours does.
- **Their fold schedule IS `AccRbrBcsShifted`'s lagged-root residual** — and
  folding at the commitment alphabet motivates a new `AccRbrFold`. **They
  cannot state any concrete bound** (negl(λ) formalism), so our depth
  refutation + repaired `(t+k)·ε` is expressible only on our side.
- **NovaBlindFold**: dead on Merkle; transfers in shape to the dual-mode with
  an **unpriced smudging tax**; vs our recorded VEIL ~3% it is **parity, not a
  class gap.**
- ⚠ **A printed formula bug found in Nebula** (p.23's input-consistency
  direction would zero the global input; Lemma 3's proof and the worked
  witness give the right one) — and the silent invariant named:
  **block-support discipline**, which is *our widened-gadget wound* in their
  notation.
- **The surpass table, honest**: they win measured latency and memory
  maturity; **we win PQ, formal content (their repos verified zero this
  session, instruments named), and the depth bound**; transparency ties.
  > 09-04 (soft): eprint 2026/1857 gives the smudging tax a lattice-side price — Θ(log n_F) decomposition depth (k=31 vs Θ(1)), interactive-only. `notes/eprint-delta-2026-09-04.md`.

**The composed architecture this yields**: dual-mode MSIS at the base →
Nova-shaped PQ folding (4–8% overhead) → switchboard pay-per-use (Ajtai
zero-commitment) → Nebula-style committed memory (Lemma 2 ⟺ TwistContinuity)
→ **ember's EVM decompilation on top for the per-program prize.** Every layer
either held or priced; follow-ups: ✅ **`TwistContinuity` DISCHARGED (2026-08-17, `820f0cb`)** —
Nebula's Lemma 2 formalized **both directions** over our richer carriers:
- ⚑ **`twistContinuity_iff_grandEquation`**: TC ⟺ frame-outside-dom ∧
  ∃ stamps, `IS + WS = RS + FS` — the Spice-shaped list induction, Mathlib
  multisets, none hand-rolled. (Target corrected: TC lives in
  `Compiler/SparseAuthenticatedStateLogupBridge.lean:90`, not `Kernel/`; the
  multiset side existed **nowhere** in the tree.)
- ⚑ **The `free` gap ABSORBED as a theorem, not an obligation**: with
  `Option`-valued cells, **`free` is a write of `none`** — the soundness
  induction has *no free case split*, and `stale_read_after_free_refused`
  exhibits the flagged hazard closed. *The model difference Nebula's read
  warned about dissolved into the carrier choice.*
- **The fingerprint at the SHARP bound** `max(|A|,|B|)·(k+1)/|F|` (not the
  crude pairwise one), both legs from the one existing SZ lemma via a
  bivariate-coefficient argument; injectivity honestly `Set.InjOn` — **global
  is UNINHABITABLE for Nat-stamped tuples.**
- **Nine teeth**, including the quantifier-order exhibit: **∀γ, a post-γ
  forgery PASSES** — the γ-before-values ordering shown load-bearing, not
  assumed — and a swap-cycle that *satisfies stampless accounting* yet is
  refused with stamps for every prover stamp choice.
- **One obligation remains**: `[TWIST-FP-BIND]`, six named legs (binding,
  roots-before-γ, range→InjOn, row shapes, root-bound audit frame, positional
  write stamps). Consumers wired **across module boundaries**, both poles.
- ⚑ **Bonus: this engine IS the gap `[SPARTAN-sparse]` recorded** — SPARK's
  combinatorial core now exists; its sparse-matrix instantiation does not.

And
✅ **`AccRbrFold` LANDED (2026-08-17, `bc29222`, 1,448 lines, 16 pinned
audits, no `sorryAx`)**:
- **The norm budget is DATA**: `budget b₀ T = b₀ + T·(ρ·B)` — additive, the
  Cyclo flat-fold regime — and the RBR knowledge state through a fold is a
  genuine Def-4.1 instance. The one remaining obligation
  (`[ACC-rbr-fold-resid](a)`) is exactly the per-absorbed-commitment
  `ε_MSIS` home.
- ⚑ **At our dual-mode parameters (q=2⁶⁴−257, B=2¹⁶): safe through
  T = 2⁴⁷−2, binding lost UNCONDITIONALLY at T = 2⁴⁷−1** — tightness both
  ways. *The norm wall exists and sits ~14 orders of magnitude past any
  realistic fold count: the PQ-Vega folding depth is practically unbounded.*
- ⚑ **The Z=∅ depth corner RECURS under additivity** (`foldOB2Unguarded_false`
  re-run at a genuine fold instance) — **because it lives in the ERROR
  algebra, not the message algebra.** Both halves theorems, as asked.
- ⚑ **Bonus: the `AccRbrBcsShifted` lagged-root residual DISSOLVES at the
  additive alphabet** — every fold root is verifier-computable, no inert
  challenge; **the trade is that the norm budget is the new residual, now a
  field of the structure instead of a comment.**
- **Consumer wired three ways** into `VerifierEmbedding`, including the
  fail-open hazard as an `IsEmpty` theorem
  (`dropped_norm_check_refuses_embedding` — infinite kernel coset vs finite
  norm ball).
- Honest label: `MsisHardEx` is *nonexistence* — proved at the toy, expected
  false at production sizes by pigeonhole; the computational reading is the
  named residual `[FOLD-msis]`.

## 3d. EVM DECOMPILATION — real, unclaimed at the right granularity, staged

`notes/evm-decompilation.md`. **The Futamura framing holds with two amendments
that strengthen it**: (1) circuits have no loops, so residualization becomes
**unroll (gas statically bounds every EVM loop) / fold (the IVC seam) /
refuse** — and classical PE's "residual interpreter" **IS a switchboard**, so
the two techniques are *the static/dynamic halves of one mixed computation*,
priced per program point by the virtualization threshold. (2) ⚠ My 30×
attribution was wrong at source: **Nebula's 30× is the MEMORY technique; the
switchboard is the 260× at UNCHANGED structure — the switchboard never shrinks
the machine at all.** Decompilation's case is stronger, not weaker.

**Prior art, instruments named**: pieces exist — Buffet 2014 ("circuits are
not universal"); ⚑ **powdr autoprecompiles = automatic PE of zkVM circuits
per basic block WITH a Lean-4-verified optimizer** (closest neighbor —
instruction-anchored and block-granular, not semantics-anchored);
Singh–McKay PE-of-hardware 1998; **EquiVM is the front half alive in Lean**;
EVMYulLean passes 22,330/22,332 Cancun tests. **The semantics-anchored,
program-granular, no-machine-left version is unclaimed — and the back half
(proved emission) is exactly `EmitByName`/`ZkmlEltwiseAir`.**

**The shape**: a 10-constructor residual vocabulary (ERC20 transfer = **15–20
semantic ops from 635 machine steps**; stack/PC/decode/static-RAM all die);
correctness as `descriptor_means_semantics` **iff** + `encode_injective` =
*"does ONLY that program"*, trusted base enumerated, **the decompiler itself
UNTRUSTED via per-output translation validation**. Hard parts routed: jumps →
refuse (Elipmoc: 99.5% of real contracts feasible); loops → gas-bounded unroll
or `SelfEmbedding` fold; storage → `TwistContinuity` (⚠ **Nebula's memory does
NOT port here** — it needs the free zero-commitment); calls → one
`VerifierEmbedding` rung; gas → **refused with the premise visible.**

**The prize `[derived, their unit]`**: ≈3–4K vs ≈0.25–0.43M active constraints
— **~60–140× beyond the switchboard** — with three honesty clauses: keccak is
a common ~100× elephant; the win **saturates at our proof floor**
(`P(b)=3381·2^b+766` ⇒ batch transfers); and Merkle-root binding would eat
the prize.

✅ **STAGE 0 LANDED (2026-08-17, `8c5a732`)** — five opcodes end to end, and
⚑ **the decompilation theorem is literally `rfl`**: with the program concrete
and calldata symbolic, **the stack, PC, decode, MSTORE and RETURN reduce away
DEFINITIONALLY** — `fragment_faithful : ∀ cd, evmRun … cd = .ok (beBytes
(residual.denote cd))` costs the kernel nothing. *The Futamura claim, realized:
specialize the interpreter at a program and the machine is not proved away —
it reduces away.* Trust lives only in the per-output TV pair; no theorem
quantifies over the decompiler.

The chain: real 15-byte bytecode · **conformance vectors from a real EVM**
(anvil/revm via `eth_call`, five kernel-decided named theorems including
wraparound and past-the-end calldata) · a **refusing** symbolic-stack
decompiler (STOP, data-dependent offsets, foreign opcodes all refused) ·
**256-bit faced**: 16 limbs × 16 bits (⚑ 8×32 is IMPOSSIBLE — p < 2³²), with
**the absent top-carry pin BEING the mod-2²⁵⁶ semantics** · soundness AND
completeness with executable Lean witness-gen · the iff descriptor theorem +
`encodeBoundary_injective` (the "does ONLY that program" half) · teeth
mutation-first · **3,298 gates / 4,131 wires emitted** (231 KB JSON).

⚠ Two flags: the design note's "≈3–4K per transfer" is **Nebula's R1CS unit —
not comparable to these gates** (range checks, 768 wires, are the
lookup-collapsible dominant term; re-derive at Stage 3). And
`Compiler/EvmAddAir.lean` is **committed but unrooted from the committed
umbrella** — `Compiler.lean` carries a sibling's uncommitted import of an
untracked file, so the rooting line waits (said loudly; the
gating-defaults-to-silence shape, declared this time).

> ⚑ **09-04: a new requirement, not a kill — eprint 2026/1838** (Fenzi, 09-01):
> Fiat–Shamir attacks on *program-generated instances*, which is exactly this
> route's shape. The pinned `p3-batch-stark` transcript (`transcript.rs:27-66`,
> rev `82cfad7`) absorbs the instance count, `(log_ext_degree, log_degree, width,
> num_quotient_chunks)`, the main and preprocessed commitments and public values —
> **not the constraint polynomials**. Proposed, conditional on reading 1838's
> mitigation theorem (PDF not yet in the mirror): absorb a descriptor digest
> before the first challenge. Adds a line to `evm-decompilation.md` §6's trusted
> base ("4. Nothing else" is now "4. the descriptor is bound"). `notes/eprint-delta-2026-09-04.md` §1.

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

## 4c. ⚑ THE RECURSION TOWER, MEASURED — and it refutes two of our claims

`notes/recursion-tower-profile.md`, harness `circuit-prove/tests/recursion_tower_profile.rs`.

**⚑ First, the instrument, because I briefed the wrong one.** *A permutation
counter is BLIND to in-circuit Poseidon2 by construction* — an in-circuit
permutation is an **AIR row**, not a `permute_mut` call, so pointing §D at a
tower layer reports that layer's *native* hashing and **zero** for the thing
the 75% claim was about. And it cannot be pointed there anyway: **layers 1–3
are monomorphic** in `DreggRecursionConfig` via three independent welds.
`p3_recursion::prove_next_layer<SC,…>` *is* generic; **the weld is ours.**
The primary instrument is the **circuit op census** instead.

**⚑ THE IDENTITY, measured twice with no shared code path**: the child's
**native verify** permutations = **38,168**. The leaf wrap's **in-circuit**
`poseidon2_perm` ops = **38,168**. Identical to the unit.
> **A wrap's biggest table IS its child's verifier, row for row.**
So *"verifier ×2.28" is a PROVE price, paid one layer up, as trace.* Verifier
cost and prover cost are the same quantity at different layers.

**The four answers, denominators named:**
1. **In-circuit Poseidon2 share: leaf wrap 36.45%** of `cells(main+prep)`
   (48.36% of `cells(main)`, 11.00% of rows); **apex-shrink 53.98%**. ⚠ **NOT
   ~75% at any denominator** — the estimate every "the tower is where this
   pays" claim rested on. The 36.45% is invariant across two unrelated
   children.
2. ⚑ **`permEmissionNarrow`'s tower factor is 1.000×.** The tower's Poseidon2
   is **upstream `p3-poseidon2-circuit-air`, not the Lean
   `CHIP_TABLE_AIR_JSON`** — *a display-name collision inside a cost model.*
   Its only reach is via the child's width: a 1.3–2.1% cut that
   **power-of-two padding absorbs whole.** At the deployed leaf it is
   **1.077×**, independently reproducing `narrow-witness-gen.md`'s 1.076× by a
   different route. **The hypothesis I dispatched this lane on is refuted.**
3. ⚑ **The blowup trade is NET ≈65× WORSE PER TURN.** On the deployed rotated
   child: prover ÷15.23, **verifier ×2.351** — and the wrap grows **×3.268 in
   cells** while costing **26.05× the leaf**. **The leaf's blowup is a TOWER
   knob, and every grid we have priced one layer of five.** (The decision not
   to flip was already right; this is a much stronger reason.)
4. **Hash-bound in the tower too, at Y/X ≈ 3.1–3.3×** (vs the leaf's 5.0–7.2×).
   **The whole difference is `log₂h`.** ⚠ `Y` does **not** transfer to the
   BN254 layer 4 — stated, not assumed.

**Reds found and reported rather than routed around**:
`rotation_batchstark_leaf_smoke.rs` is **RED at HEAD with no `#[ignore]` and no
gate** (width 1896 vs `GRAD_ROT_WIDTH` 1841 vs its own comment 1647);
`apex_shrink_trace_anatomy.rs` uses `LOG_BLOWUP = 6` against a deployed 3, so
**its model is 8× the deployed cost**; two decision docs carry wrong numbers
(`[9,9,15,14,15]` measures `[9,9,16,15,15]`; ~11,000 in-circuit perms hardcodes
`q=19` where measured is **22,626**). **And there is no `2^20` in the tower at
all — height is a property of the child.**

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

## 5d. ⚑ TWO INSTRUMENT DEFECTS FOUND WHILE FOLDING THE HANDOFF (2026-08-17)

1. ⚑⚑ **THREE Lean modules are committed but UNROOTED from the default build
   — 1,593 lines the umbrella `lake build` has never elaborated.**
   `Compiler/EvmAddAir.lean` (722 L), `ZkmlTraceCheck.lean` (580 L),
   `ZkmlEltwiseAir.lean` (291 L) — **two orphaned undetected since 08-13.**
   Each landing commit shipped the callee and not the umbrella. *They were
   built by explicit target, so the theorems exist; but no default build or
   gate has ever walked them.* ⚠ **And the umbrella edit CANNOT be committed
   to fix it** — `Compiler.lean` also imports two *untracked* files
   (`UwueavePreoProjectionV2.lean`, `HashRelationInverse.lean`), so this needs
   their author. **The gating-defaults-to-silence class, three deep, in the
   file that is supposed to root everything.**
2. ⚑ **`~/paperbin` is ~64% grep-invisible** — measured 1,104 PDFs against
   518 extracted `.txt`. PREFLIGHT claimed *"all 1,218 PDFs have full text."*
   **Every absence claim made by grepping paperbin is re-priced**, including
   several I repeated. Corrected in PREFLIGHT.
3. **The `MM` files in breadstuffs are a STALE INDEX, not partial work** —
   worktree byte-identical to HEAD, staged/unstaged diffs exact inverses.
   ⚠ **A bare `git commit` there would RESURRECT a 6-line-shorter measurement
   harness**, not commit half of someone's work.
4. **minidregg has no `#assert_axioms` machinery at all** — it pins with
   `#guard_msgs … in #print axioms` while breadstuffs uses `#assert_all_clean`.
   ⚠ **A cross-repo audit using one repo's grep reports a false zero.**

## 5e. ~~E5 RE-OPENS~~ ⚑⚑ **RE-DERIVED 2026-08-18 — E5 IS STRENGTHENED, AND THIS SECTION HAD THE SIGN BACKWARDS**

`notes/e5-rederived.md`; `notes/hash-landscape-scripts/crossover_rederive.py`
(six committed controls reproduce before any new row prints).

**What this section said, and it is half right:** the verdict *"binary fields do
not rescue in-circuit verifier cost"* was measured at a **36.45%** hashing share;
the reduced-opening split and the packing retune move it, and a *free* hash goes
from ×1.57 to more.

⚑⚑ **What it got wrong: `R*` — the crossover a candidate hash must beat — is
COMPUTED FROM that same share, and it moves the OTHER WAY.**

> `R* = 1 + (1/m_leaf − 1) / f_circ` — the numerator is the **native-side gain**
> (untouched); the denominator is the **in-circuit penalty exposure** (what grew).
> **`R*` is strictly decreasing in `f_circ`.**

| `f_circ` | free hash (R=0) | **`R*`, leaf wrap** |
|---:|---:|---:|
| 0.3645 *(where E5 was decided)* | ×1.57 | 2.49–4.52× |
| **0.5236 — DEPLOYED TODAY** | **×2.10** | **2.04–3.45×** |
| 0.7330 *(proven, not deployed)* | ×3.75 | **1.74–2.75×** |
| 0.8100 *(derived; a NEW AIR that does not exist)* | ×5.26 | 1.67–2.58× |

**Raising the in-circuit hash share raises the payoff of a FREE hash and raises
the penalty of an EXPENSIVE one — a LEVERAGE increase, not a direction.** Char-2
does not offer `R = 0`; it offers `R = 12.7–24.7×`, which was 2.8–9.9× above the
bar and is now **4.6–14.2×** above it. All three premises hold unchanged.

⚠ **Three corrections to the paragraph above:**
1. **"~×5" is the DERIVED row.** Measured-and-proven is ×3.75; **deployed is ×2.10**.
2. **Deployed `f_circ` is 52.36%, not 36.45%** — `834a3f7` is an ancestor of the
   pinned `fc3c6df`, so `LEAF-VS-RECURSION.md:94`'s *"pin deliberately NOT moved"*
   is stale.
3. ⚑ **The optimizations closed the LOOKUP door, not the binary one.**
   Lookup-arithmetized `R = 3.2` was a **0.79× wrap win** at 0.3645 and is a
   **1.15× loss** at 0.733. `hash-landscape.md` §2's *"highest-value open
   measurement"* crossed out of its own band while nobody was looking.

> **E5 stands, with a larger margin. Do not cite this section as a re-opening.**

## 5f. ⚑⚑ WEFT RE-OPENED: the kill was right for the WRONG reason, and the repair is free

`notes/weft2.md`. Ember asked *"why does Weft have to be dead?"* — both of my
challenges held, and the lane found worse *and* better than either verdict.

**Branch 6 was never disqualifying.** `x⁻¹` has δ = 4 and Walsh max
`|W| = 2^(n/2+1)` **exactly** — both theorems in n — so at n=32 one active
S-box is **30 bits on BOTH sides** (my arithmetic needed sharpening: 30 not 32,
and the *linear* side is not better). Branch 6 → **180 bits per 2 rounds**.
Three things kill the "6 < 25" verdict outright:
⚑ **Poseidon2's own internal layer is far below MDS and ships** ⚠ (*the specific figure "branch 2" was a script DOCSTRING I propagated as a measurement into five notes — corrected 08-18; nobody has computed it*);
⚑ **the comparator was CROSS-CHARACTERISTIC** — M_E's {1,2,3} entries collapse
in char 2 (diagonal factor 2 → 0), and the measured char-2 reduction is
**branch ≤ 8 at t=24**; and MDS is the ideal, not the bar.

**⚑⚑ THE REAL BREAK, which the kill missed and which is total, not a trail:**
> **The flag is 5 deep, not 4** — `weft_branch.py:300` loops `range(1,5)`, and
> the skipped `b=0` level is **row 0 of M = e₀: output lane 0 EQUALS input lane
> 0.** An autonomous 32-bit quotient `x₀ ↦ x₀⁻¹ + c₀` **for any round count.**
>
> ***Round constants break invariant subspaces; they do not break invariant
> quotients.***

`B_l = 2` (the linear branch, **never computed**) is its shadow. Second defect:
with `βⱼ = 2ʲ` **every matrix entry lies in GF(2⁸)** → a `2¹⁹²` round-invariant
unless the constants leave GF(2⁸) — *and small-integer transcript tags do not.*

**And the rotation I proposed is verified but is the WRONG repair**: all 23
non-trivial rotations destroy every invariant lane subspace — **but a rotation
cannot move either branch number** (permutations preserve Hamming weight),
*which is the cleanest available proof that branch number cannot see the
property.*

**⭐ THE FREE REPAIR — and it converges with the post-Weft lane independently**:
evaluate on an affine **coset** (same butterflies, shifted twiddles, **zero
ops**): **B_d = 8 EXACT and attained**, B_l ∈ [8,10], dense, **zero invariant
subspaces on either side**, diffusion depth 1, no twisted-subfield structure,
`deg(minpoly) = 24`, **observability at all 24 lanes**. ⚑ **One transform — so
the "ONE proved linear object" prize survives.** (The sibling lane reached the
same axis via a *disjoint point set* ⇒ systematic-RS ⇒ MDS. **Two lanes, one
answer: the point set was the bug.**)

**Weft-2's internal/external split is REFUSED, twice**: the internal-round
condition is **observability, not branch** — Weft-1 fails it at 16/24 lanes —
so the split would put the structured layer *exactly where its defect binds*;
and after the repair all 24 lanes pass, so **there is nothing to split**
(+11% cells, zero benefit, since `x⁻¹` at F₂-degree 31 is already ~8 all-full
rounds with no tail to cheapen).

⚠ **Two conditions the sibling's MDS repair does NOT carry**: `A = V₂V₁⁻¹` at
the natural split is **still a GF(2⁸) matrix** (free fix: shift one point set),
and **`deg(minpoly A) = 6` — repaired, `A² = I`, an involution** — so **no
S-box lane can serve a partial round.** Not a break of Mark-32 (8 full rounds),
but decisive for architecture.

**The trade, stated honestly**: ⚑ **on the binary rung there is no aged hash to
adopt** — Vision/Mark-32 is *"none found, and nobody has looked"* on our own
books; CheapLunch/Perrin/Rijmen are **prime-field assets**. So it is not
*custom vs aged* but **our object vs a published object with the same skeleton,
both unanalyzed** — and adopt still wins, on the **epistemic flywheel**, not on
margin. With the price of zero age now measurable:
> ***The base rate of "our own tooled analysis missed a total break" is 1 for 1
> on this design.***

**The gate is amended by its own subject**: branch number moves to **FIFTH**,
on both sides; **structure / quotient / subfield / minpoly come first.** New
obligation named: **[WEFT-multiround]**.

## 5g. ⚑⚑ THE τ=2 SETTLING EXPERIMENT RAN — and "13" understated us by 1.85×

The item we named in three notes and never executed is executed
(`notes/ring-hash-scripts/integral_char_p_settling.sage`): Beyne–Verbauwhede's
**verbatim** `SPN.ipynb` Newton-polytope machinery (eprint 2025/932) at **our**
parameters. ⚑ **Falsification guard passed** — it reproduces their published
table **exactly (1 / 13 / 20 / 21)** — *and caught a real bug in the first
wrapper, which never advanced the round polytope. That is what the guard is
for.*

**At base ~2^64** (identical for the Frog modulus and the dual-mode 2⁶⁴−257):

| τ | (e,t) | last round with a mod-q² integral property |
|---|---|---|
| 1 | (1,16) | **2** |
| **2** | **(2,8)** | **24** |
| 4 | (4,4) | **≥42**, still climbing when stopped |

⚑ **The load-bearing comparison: at identical (e=2, t=8), the paper's base 2³¹
gives round 13 and ours gives 24.** Same e, same t — **the ~1.85× is purely the
base-prime effect the design note flagged as "unmeasured."** *We chose τ=2
against a number that understated our own case by nearly 2×.*

**Consequences, in order:**
- **The τ ordering now holds BY EXECUTION, not inference. τ=2 remains the
  pick**, and **τ=4 is not merely "worst" but INTEGRAL-INFEASIBLE** with any
  sane round budget.
- ⚠ **But the margin is thin and 24 is a FLOOR**: against the borrowed
  RF=8/RP=22 = 30-round budget that is **~6 rounds** — and the deployed σ-layer
  is only slot-MDS in *full* rounds, i.e. **weaker mixing than the model that
  produced 24.** ⚑ **The §4.4 round-count derivation is now the BINDING open
  item, not a formality.**
- ⚑ **And the margin question is also a COST question**, which nobody had
  connected: σ-Poseidon's 363,513 constraints assume 30 rounds. At 36 / 40 / 48
  rounds it is **436K / 485K / 582K — i.e. 4.7× / 5.3× / 6.3× the
  gadget-Feistel's 92,257**, whose round count this result does not drive.
  ***Every round of repair widens the gap to the candidate that was already
  ahead.***

**This is the intended "costs a redesign now" outcome**: not a break, but a
hopeful borrowed 13 converted into a measured floor of 24 with a named,
priced debt. **Item #1 of `forcodex/08-ATTACK-BRIEFS.md` is closed; three
remain** (the Feistel's order-2 differential / MITM-boomerang, the
free-norm-check assumption, and a direct Gröbner/CICO under Perrin's
elimination-step rule).

⚠ **Operational note for ember**: amd64 emulation in the Docker VM now uses
**qemu** instead of Rosetta (FLINT's matmul hit an unsupported instruction
under Rosetta on this box). Correct but slower; a Docker Desktop restart
restores Rosetta. **The arm64 `claude-sandbox` containers were untouched.**

## 5h. ⚑⚑ GSR (eprint 2026/1692) APPLIES TO OUR POSEIDON2 IN FULL — and R_P sits BELOW its threshold

`notes/gsr-poseidon-2026-1692.md` (`d741c96`) + scripts in `notes/gsr-scripts/`.
The paper never analyzes Poseidon2 (three passing citations), so this was
settled **by computation, not analogy.**

⚑⚑ **THE STRUCTURAL FINDING: Poseidon2's defense IS the vulnerability.** The
gadget's only stated requirement is that the partial layer be an **invertible
linear map** — justified verbatim as *"Because the mapping is affine."* **No
MDS, no branch number, no round-constant property is ever invoked.** Its one
implicit requirement is **full Krylov rank at `e₀`** — and on our deployed
constants that is **16/16 (w16), 24/24 (w24): FULL.** ***Because Poseidon2's own
design criterion is "no nontrivial invariant subspace", which IS full Krylov
rank. The property that defends it against subspace trails is the property that
makes GSR well-conditioned. No matrix choice fixes this.***

**Our numbers** (`t=16, α=7, R_F=8, R_P=13`, read from source, unanimous across
nine transcriptions): ⚑ **`t − 2k = 14 > R_P = 13`** — **GSR absorbs 100% of
our internal layer plus one full round, with a degree of freedom to spare** —
*strictly worse than the paper's own target, which retains one unskipped
partial round.* **CICO-1 on 18 of 21 rounds at 2^27.4 — practical, seconds.**
CICO-2 at 2^61.1 vs 2^62 generic is one bit, not a break. ⚑ **α = 7 is what
saves us, not Poseidon2.** (Their Table 1 reproduced 5/5 before the calculator
was pointed at us.)

**WHAT STANDS, said as loudly as what falls**: the **full 21-round
permutation**, and **the sponge's ~124-bit claim** — which lives at CICO-k for
k at the capacity, where GSR gives **nothing** (no gain by k=3; identically
vacuous at k=8). ***The instances GSR breaks are not the instances carrying our
security claim.***
> ⚑ **09-04: true of GSR — UNESTABLISHED for eprint 2026/1792** (Li–Liu–Wang,
> 08-26, nonlinear subspace trails). Its trail spans **2·E_c** partial rounds with
> **E_c = t − d in compression mode** [READ, 1792 §2.2/§4]. Our Merkle INTERNAL
> node is `TruncatedPermutation<Perm16, 2, 8, 16>` — compression mode, c=0, d=8,
> no feed-forward (`plonky3_prover.rs:71-72`, `stark_zk.rs:79-80`) — so E_c = 8
> and the window is **16 ≥ R_P = 13**: every partial round absorbed with three to
> spare; the residual is the 8 full rounds at α=7. The leaf sponge (c=8) has
> E_c = 0 and is untouched. **No cost exists at our point** — 1792's tables stop
> at p ≥ 2^64, d ≤ 4, r_F = 6. The decisive computation is named (1792 §4.2's cost
> model, calibrated by reproducing its Table C.1 at t=16, then evaluated at
> p≈2^31, R_F=8, R_P∈{13,20}) and is in flight as `notes/nst-1792-at-our-node.md`.
> 1792 is an independent argument for `R_P 13→20` (four rounds past the trail)
> over `13→15` (still inside it). ⚠ `hash-verdict.md` item 6 "our Merkle tree is
> sponge-mode" is true of leaves only. `notes/hash-delta-2026-09-04.md` §1.2, §7;
> `notes/eprint-delta-2026-09-04.md` §1.

**Margin: 3 of 21 rounds — a CEILING** (a lower bound on adversarial reach;
this lineage has only pushed it up). **Filed NEXT TO, never summed with, the
τ=2 integral FLOOR of 24 — opposite species.** The 3 rounds are set entirely by
`R_f0`, not `R_P`.

⚠⚠ **AND THE ONE RUNNABLE COMPUTATION THAT WOULD MOVE THIS FURTHER**:
**CheapLunch §D.1 already flagged, at our EXACT `t=16, k=1`, that Poseidon2's
non-MDS `M_E` lets "two rounds be freely skipped"** — left as an open problem.
**That skip lives in the initial full rounds, which are our ENTIRE margin.**
Composability is unverified and not claimed — **but if it composes, the margin
goes to 1.**

✅ **COMPOSABILITY SETTLED 2026-08-18** (`d7da8d1`, `notes/gsr-cheaplunch-composability.md`):
**the skip REACHES us; it does NOT compose. Margin stays 3.**
- **It reaches us**, verified by construction on our **deployed** constants (a
  2-round chain, CICO-1 input zero, re-checked against the deployed rounds on
  256 random inputs). ⚠ **Their `M_E` is not ours** (paper `M_4=[[5,7,1,3],…]`
  vs deployed Plonky3 `circ(2,3,1,1)`) so their vector is inert — **but the
  phenomenon rests on the outer form alone.** Nothing dodges it: **α=7 is
  irrelevant** (α-independent given α odd and `gcd(α,p−1)=1`, both forced by
  Poseidon2 needing a permutation), nor width, nor `M_4`, nor constants (12/12
  random sets chain). ⚠ And a brief correction: `s = ⌊t/k⌋ − 2 ≤ k` — **the
  `≤ k` binds**, so at t=16,k=1 an *MDS* `M_E` already gives one free round and
  the non-MDS form buys only the **second**.
- ⚑ **Composition does not merely fail to help — it DESTROYS GSR.** GSR's first
  forward-linearisation functional on the verified chain is a **degree-49
  polynomial: 48 coefficients must vanish against 8 spare parameters.**
  Steelmanned past that particular line by a Grassmannian count: **a 2-round
  front-end skip forces D = 1**, and even a 1-round skip caps at **D = 7 —
  still 8 short of the 15 GSR needs.** ***The obstruction is PRIOR to the
  arithmetic: GSR's freedom exists only if rounds 1–3 are DROPPED; the skip's
  saving only if rounds 1–2 are KEPT. Different objects.***
- **The skip alone is 2^111.6** — not an attack. (A perfect composition would
  have been 2^33.0, above the 2^31 generic bound, and would have bought
  20-of-21 i.e. margin 1.)
- ⚑ **NEW AND LOAD-BEARING: `R_P` buys NOTHING against a front-end skip** —
  that lives in `R_F`'s rounds. **So our safety on that half now rests entirely
  on the §4b obstruction**, recorded with its tripwire: ***any affine family of
  dimension ≥ 15 surviving a front-end external round.*** If that ever appears,
  **the answer is `R_F`, not `R_P`** — and **changing `M_E` is NOT an option**
  (the invariant subspace holds for any `A`).
- **Derived, and left open by BOTH papers**: the mechanism is an `M_E`-invariant
  subspace `W = {(0,v,−v,0)}` with `M_E|_W = A`, preserved by the S-box because
  α is odd — **and it explains why exactly TWO**: MDS misses the second round by
  *exactly one* degree of freedom, and `W` is that degree; the third needs 3
  projective conditions with zero free parameters (180 shapes enumerated, none
  satisfy).
- ⚠ **Two traps paid for**: `pdftotext` **without `-layout` interleaves §D.1's
  six column vectors** into an unreadable stream; and `pow(a, p-2, p)` is
  **silently wrong for the composite modulus `p−1`** in the α-th root — ⚑ **the
  symptom was not an exception but the chain failing at round 2, which reads
  exactly like "the skip does not reach us." A wrong inverse rendering as the
  hoped-for verdict** — the refusal-renders-as-the-expected-verdict class,
  again.

**Repairs, priced against 2.13 cells/S-box**: **`R_P` 13→15 kills the practical
CICO-1 outright for +1.4%**; **13→20 buys margin 3→9 for +5.0%.** A different
internal matrix does **not** work; all-full-rounds is +138% for the same
outcome as the +5% fix. ⚑ *The lane named 15 as containment and 20 as fix
explicitly so the phases are not run backwards — per the house doctrine, and I
recommend going straight to 20.*

**Collateral**: **σ-Poseidon is reached but DOMINATED** (GSR linearizes 8 of 30
rounds vs the integral's 24 — **adds no debt**, and its `R_P/t` is far
healthier at 32% absorbed vs our 100%). **The gadget-Feistel is IMMUNE by
construction** — no S-box, no partial layer. *The front-runner is untouched.*

⚠ **Two corrections to me**: the "triple-confirmed" Poseidon2 verdict is a
**COST** verdict — GSR concerns a different quantity and can neither confirm
nor refute it. And **"Poseidon2's internal layer is branch 2" was a script
DOCSTRING I propagated as a measurement into five notes**; nobody has computed
it, and it is irrelevant to GSR regardless. Corrected at source.

## 5i. ⚑ THE "SHIP AT THE LINE" THESIS: naive form REFUTED, better form SURVIVES

`notes/formal-cryptanalysis-pipeline.md` + `notes/ring-hash-scripts/computed_line.py`
(guard reproduces all 5 rows of GSR's Table 1 to ≤0.6 bits).

**"Compute the line → ship fewer rounds" is FALSE for AO hashes.** **Six
independent instances of a computed bound sitting FURTHER OUT than the deployed
parameter, none the other way**: GSR at t=24 (1.6–2.9×), char-p integral at our
base (4.8×), our own Poseidon2 (1.15×), Ashur–Buschman–Mahzoun (35 partial
rounds where the designers' equation gives 22), resultants breaking Rescue-512,
and the Poseidon initiative *already raising* `R_F`. **My stated make-or-break
fear was the correct one.**

⚑⚑ **BUT THE ORGANIZING FACT IS BETTER THAN THE THESIS WAS: the SIGN of the
error is PREDICTED BY THE INSTRUMENT.** Where a family has a *provable
defense-side* bound (statistical, via wide-trail) designers are **conservative
and say so** — Poseidon2 §7.1: *"this is a pessimistic estimate."* Where a
family has only **heuristics** (algebraic), they are **optimistic and have been
corrected outward repeatedly.**
> ***Formal bounds are looser exactly on the families that are NOT binding.***

**WHAT SURVIVES IS A STRONGER, CHEAPER CLAIM — the value function is KINKED at
`R_P = t − 2k`, and a multiplicative margin rule is blind to a kink BY
CONSTRUCTION.** Measured: **every one of our deployed partial rounds — 13 at
w16, 21 at the w24 sponge — sits BELOW the kink and buys ZERO** against this
family. And inside **Poseidon's own objective** (`t·R_F + R_P`), at identical
215 S-boxes: **the "arbitrary" +2 `R_F` costs 48 S-boxes and buys 1 round of
gate margin; the same 48 spent on `R_P` buy 48. Ratio 48:1** — and *all three*
of Poseidon's own corrected Gröbner conditions prefer the reallocation.
⚑ **So the win is not "fewer rounds" but "the SAME rounds allocated
differently" — free, and derived from the designers' own objective function.**
(Their §5.4 concedes the input: *"we **arbitrarily** decided to add… +2 R_F and
+7.5% R_P."*)

⚠ **Three corrections**, one of them mine to amplify: **the τ=2 script's
falsification guard had a DEAD ROW** (`:183` asserted a "21" the paper does not
contain — B–V use exactly three fields), **so it could not go red and reported
OK** — which is how *"reproduces 1/13/20/21 exactly"* entered three notes and
my summary. **Rows 1–3 are genuine and pass; the τ verdict stands; the guard
was 3/4 live.** Also: *"nobody in the AO-hash space is pressing this"* is
**refuted** (Perrin, EC'26 slide 31: *"security arguments based on D_I are the
future!"*) — the narrow true claim is the *feasibility-region formulation,
regime labels, and machine checking*. And the DoF ceiling is **GKR 2025/954
§5.1, not ours.**

⚑ **AND A DESIGN FORK FOR EMBER — the thesis argues AGAINST our front-runner.**
The gadget-Feistel resists the skip family (absorbs **≤1 round** vs 23 for
Poseidon t=24, because base-B decomposition does not commute with affine maps)
— **but the same non-polynomiality makes the algebraic instrument inapplicable
in BOTH directions, so the pipeline CANNOT set its `NR`.** Every computable leg
is satisfied at NR ≈ 2–3; **the binding leg (order-2 / MITM) is OPEN**, and
**NR=16 remains precedent.** *A primitive we cannot analyze is exactly what the
thesis says not to ship.* ⚠ **Cost of being wrong about NR is ~0.5% of the
circuit — so there are no cost grounds for deferring the MITM work.**

## 5j. ⚑ THE CR/RO SPLIT: real as a JOB, FALSE as a REQUIREMENT — and the live knob is leaf RATE

`notes/fastest-oracle.md` (`566bd8c`) + `notes/fastest-oracle-scripts/merkle_geometry.py`.
My organizing idea — *"a Merkle node needs collision resistance only, so stop
paying random-oracle prices for it"* — is **refuted at the requirement, with
three sources read at the load-bearing passage.**

**The JOB split is real and now exact**: one `Poseidon2BabyBear<16>` in four
roles; **CR work is 92.0% of Merkle-commit perms, 81.6% of all prover hashing,
70.8% of wrap in-circuit perms.** ⚠ One wiring correction to my brief: **the
Merkle PATH never enters the FS transcript** — only the root does.

⚑⚑ **But the REQUIREMENT does not split**: BCS (2023/1071) makes **the tree hash
the random oracle itself** — straightline extraction runs off oracle *queries*,
and **a linear map generates none**; 2019/997 constructs a **CR-only tree that
kills FS-Kilian for ANY challenger, including a true RO**; and **Vortex — the
one production SIS-hash system — concedes in print** that its Merkle tree
*"needs to be modeled as a random oracle… to retain extractability."*
(Chiesa–Orrù 2025/536 gives the modern modular form, with the tree's `κ_MT`
term surviving.)
> **So the split licenses GEOMETRY freedom and a separate GRIND oracle — not
> algebraic tree nodes. And it kills "fewer rounds for the tree since it is only
> CR."**

**The arity computation, exact and validated**: the model reproduces the
measured Merkle-commit count **to the unit at all five blowups**
(26,493 / 52,989 / 105,981 / 211,965 / 423,933) with **zero fitted parameters**.
⚑ **Leaf sponges are 92.03% of the tree and nodes only 7.97% — so ARITY IS A
NULL KNOB (×1.003–1.026)**, independently matching a prior lane's untaken 1.0%.
⚑ **The live knob is the LEAF RATE**: a **w24 rate-16 sponge** (the pinned p3's
own `examples/types.rs` shape; *we deployed the test-convention rate-8*) is
**×0.777 native Merkle-commit** — and sequenced **behind** the narrow-AIR
landing it also wins in-circuit (×0.871; ×1.055 *loss* on today's wide chip, so
the order matters).

**Ranked**: (1) narrow Poseidon2 AIR · (2) **rate-16 leaf sponge** · (3) ⚑ **the
GRIND SWAP — the one slot a traditional hash wins, because grinding is verified
ONCE, not per-query: ~8–14% of deployed prove for +9,168 one-time wrap cells**
⚠ *after* settling the prior budget question, *is `pow=16` worth 25% of prove* ·
(4) decompose the wrap's 29.2% RO lump · (5) **SIS nodes closed three ways**
(the extraction wall above; **Vortex Fig 22's ≥2,048-bit digests → paths ×8–33**;
and our own dual-mode's ×0.7–13), **algebraic fingerprints closed by
definition** (challenge-after-commit), **code-based commitments = the blowup knob
with a bigger verifier.**

**Fixed-cost bound applied throughout**: hash wins compound at the **wrap/tower**
layer, **not at small leaves.**

## 5k. ⚑⚑ THE DECOMPOSITION WALL IS THE FAMILY'S, NOT OURS — "writable and unsolvable"

`notes/feistel-classical-tooling.md`. The lane **corrected its own framing**, and
the corrected version is strictly stronger than the one it replaced.

**I had been recording *"no automated tool models base-B decomposition."* False.**
⚑ **All three decomposition-hash designer papers WRITE exactly that constraint**
— one degree-`B` vanishing polynomial per digit plane (**Monolith 2023/1025
§B.3, Reinforced Concrete 2021/1038 §B.4, Skyscraper-v2 Eq. 21**) — ***and
nobody can run it.*** Every solved data point in the literature is a **toy
prime**: RC at p ∈ {41…127}, Monolith at p ∈ {13,29,61,113}, Skyscraper-v2 at
≤16 bits, **Tip5 never run at all.** **Monolith calls full-size instances
*"computationally intractable"* in its own words.**

> ***"The encoding is writable and unsolvable" is strictly stronger than "no
> tool models it."*** **Our crux is not a peculiarity of our design nor a gap in
> our effort — it is the measured wall for this ENTIRE family, confirmed from
> the designers' side with published numbers.**

The MIQCP tool (**2024/2061**) requires *"degree α being a small integer"* and
our layer is **degree 2¹⁶ per plane** — no. And **2026/1104 §3.1 extends the
wall to the STATISTICAL instrument**: non-polynomial S-boxes need brute force,
*"infeasible for large pⁿ."*

⚑ **THE ONE ACTIONABLE ITEM, and it retargets attack-brief #1**: the only
published technique that **does** reach a decomposition layer is **hand-built,
not automated** — **Liu et al., eprint 2024/1900**, a **limb-wise carry-DDT
automaton in C++ that routes around the S-box entirely** (*"Independent of the
S-box"*; *"we do not know the high-degree expression of the S-box over F_p"*),
reaching **3/5-round Tip5 and 2/6-round Monolith-64 collisions.** ***That, not
"order-2 / boomerang", is what item #1 now means*** — the ring-hash lane is
redirected.

⚠ **And the epistemics it closed with, which should govern how we read all
four**: **"NR = 16 remains precedent, not attack-tested. Four instruments now
report nothing — which is ONE fact about our INSTRUMENTS, not four about the
PRIMITIVE."**

**Gate §7d-bis gains two items**: (7) ***"no tool models it" and "the model
exists and nobody can run it" are DIFFERENT verdicts*** — ask who **writes** the
encoding, then who has **run** it at real parameters; (8) **when every automated
instrument refuses, go find the HAND-BUILT attack — the absence of an
automatable model is not the absence of an attack.**

**Final delta from that lane, three items not previously recorded:**
- ⚑ **Expressibility is YES, constructively** — 40/40 against the versioned
  spec with a live guard. **But the cost is 14.5M components/round, and 97% of
  it sits in ONE LINE of the spec** — *so the modeling bottleneck is a single
  component, not the design.* That is a much more actionable shape than "it
  cannot be expressed."
- **The CLAASP-MP guard was proved live** — 6/6 published SIMON-32 rows, **all
  refutable**, in 1.0 s. *Guard-before-target, as the dead-row lesson demands.*
- ⚑ **The F₂ leg produced our FIRST computed lower bound: NR ≥ 2.** The only
  integral property found is the **trivial 1-round Feistel branch copy — which
  the harness DOES find (1024/1024 against a chance rate of 1)**, so the
  instrument demonstrably works; **nothing above chance at r=2 or r=3.**

> ⚑ **The honest framing of NR=16, which is better than "we don't know": every
> measurable leg clears at 2, and we ship 8× that.** *That is a defensible
> position if and only if the margin's purpose is UNKNOWN-attack risk rather
> than known-attack slack — the distinction the formal-cryptanalysis lane made
> and the one nobody states.*

⚠ **Two method traps paid for**: **a single-line grep is not evidence a quote is
absent** (a verification missed a phrase **spanning a line break**); and a
misattribution was killed where a **corrupt title index** paired "Opening the
Blackbox" with **2024/270 — which is actually YPIR, a PIR paper.** Fetch by
number, **verify the title on the first page.**

## 5l. ⚑ THE RING-HASH ATTACK ITEMS RAN — reached at 2 rounds, margin thinner than believed

`notes/ring-hash-attacks-2-3-4.md` (`19f24db`), six scripts each aborting on a
dead guard. **No break. NR=16 is still not derived** — but three items now carry
numbers and the fourth carries a forgery.

**Item 1 — REACHED at 2 rounds, still OPEN.** ⚠ **Two corrections to my
redirect, both verified at source**: *"Independent of the S-box"* is **§3 of
2024/1900 — the BASELINE the paper BEATS**; the §4 carry-DDT **opens** the
S-box and is maximally S-box-*dependent* (what it avoids is the high-degree
polynomial over F_p). And **it runs at FULL parameters, cheaply** (15–32
lookups/query) — ⚑ **so the "this family only runs at toy primes" pattern does
NOT retire this instrument, which makes its verdict a fact about the PRIMITIVE
rather than our budget.**
**It cannot be stated against us, three ways**: adjacent-limb coupling;
negacyclic convolution (no limb order gives a bounded-width state); and fatally,
**the dense g/h mixing destroys the limb structure before recomposition, so
`DDT_{i,j}` has no definition on our primitive.** Its carry half + an exact
substitute **reach 2 rounds and stall.**
⚑ **And the MITM leg stands, against a sibling lane's claim**: *"no published
MITM model can be instantiated"* **does not survive at source** (2022/189
handles expanding *and* contracting cells — *"this is the only required
change"*). A model **was** instantiated: raw reach 3 rounds — but ⚑ **calibrated
against two published 2-branch-Feistel targets it UNDERESTIMATES by 4×, giving
12 rounds against NR=16: a 1.33× margin, not 4×.** ***"I nearly shipped the 4×
and the calibration refuted it."***
⚑ **New structural defect**: `P=2` never multiplies the top plane, so **`F_r` is
exactly AFFINE in it — state-independent slope, probability 1 — meaning 25% of
the state crosses every round on a purely linear path.** And **the reach is
bounded by the density of `g_3`, not by NR**: at `g_3 = B³` the characteristic
**chains without limit.**

**Item 2 — PARTIAL, and it is the one that should GATE SHIPPING.** Exact
counting law: **`s` bits of norm slack ⇒ `K·s` bits of forgery per coefficient
⇒ 64·s per ring element.** Forgery **exhibited at deployment parameters** (two
plane vectors, same ring element, outputs differing 16/16). ⚑ **One bit of slack
turns the credited 2^52 grinding COST into 2^64 free CHOICES per absorbed
element.** ⚠ **`O5` is filed as a COST row but it determines the enforced norm
bound — hence whether the hash is a FUNCTION at all.** (Whether slack exists
needs 2026/1127's schedule, not in our tree.)

**Item 3 — CLOSED, clears by hundreds of bits.** Gröbner/CICO reaches ~4 rounds
against the **24-round integral floor**; **integral remains binding, ~6-round
margin unchanged — σ-Poseidon is NOT in the trouble I flagged.** Model
reproduces CheapLunch Table 2 **4/4 to <0.1 bit** before being pointed at us,
and **only the INVALID granularity produces a break** (2^106.7 — it undercounts
S-boxes 8×). ⚠ **I mis-paraphrased Perrin**: what is *"sometimes literally
non-existent"* is the **complexity of the Gröbner step**, not the basis.

**Two findings en route**: **prime `q` genuinely kills 2023/822** (its
Assumption 1 is unsatisfiable) ⚠ **but my framing was wrong** — its costly
stages only strip Rubato's Gaussian noise, *which we never had*, and its cheap
leg is modulus-agnostic; **the in-scope paper is 2025/932**, our ring class by
name and the source of our own 24-round floor. And ⚑ **a new σ-Poseidon defect:
14/30 rounds mix no CRT slots, including four CONSECUTIVE slot-diagonal rounds
(8–11)** — S-box slot-wise, MDS slot-wise, both σ exponents trivial — **passing
condition C3 only because C3 checks the whole schedule. A per-round condition is
a zero-cost fix.**

⚠ **House law: TWO guards went dead and were caught** (a norm-slack modulus
guard that was a no-op on its test value; a carry-DDT falsifier that did not
chain on the weakened design either). ***The brief warned about exactly this
class and it recurred twice anyway.***

> **The line to defend: four instruments have now been pointed at the
> gadget-Feistel and only ONE reached it, for 2 rounds. That is one fact about
> our instruments, not four about the primitive.**

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
     > ✅ **09-04: MERGED upstream 2026-08-17** (`f67b0ea2`, only
     > `fri/src/two_adic_pcs.rs`), shipped in `p3-fri` **v0.7.0 (2026-09-04)**.
     > `notes/blowup-drop.md`'s condition for dropping the vendored delta is met;
     > the drop is a Cargo pin bump in breadstuffs (ember's — outward-facing
     > pins, same as the `num_queries` push). `notes/systems-delta-2026-09-04.md` §7.
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
5. ⚑ **Cross-limb binding — EXHIBITED 2026-08-14, and it was TWO holes under one
   name.** `notes/cross-limb-binding.md`; `breadstuffs` `5b653ba5d`
   (`metatheory/Bfv/CrossLimb.lean`, `#assert_namespace_axioms Bfv` 90 → **113**).
   - **HOLE A — provenance.** The checked system is `∀ i, ∃ source`; the honest one
     is `∃ source, ∀ i`. A quantifier swap, invisible to every completeness test.
     `perLimb_not_imp_bound` exhibits limbs from different ciphertexts satisfying
     every per-limb equation, and the accepted output reconstructs to a value **no
     honest pair can produce** — a wrong ANSWER, not an unbound proof.
   - **HOLE B — expressibility.** `rescale_not_limb_local`: `⌊t·x/Q⌉` reads the CRT
     reconstruction, so there is no per-limb equation to bind. Independent of A.
   - ⚑ **The candidate fix this file named first is a TAUTOLOGY.** "A
     CRT-consistency relation over the limbs" can never refuse — the CRT map is a
     **bijection**, and the exhibited forgery is itself CRT-consistent. And
     `perLimb_pins_modProd` shows the hole is not in the arithmetic at all: with
     the operands fixed, the per-limb conjunction IS the mod-Q relation.
   - ⚑ **Why nobody had exhibited it:** every Lean BFV carrier in the tree makes
     the attack unrepresentable — `DarkBazaarSameOpeningPoly.lean:45` says so in
     its own residual list. Documented ≠ detected, in our own tree.
   - **ct×pt is NARROWER than this file recorded.** Hole B **absent**
     (`scalarStep_limb_local` — the same public-integer-scalar property
     `stepR_noise_le` runs on); Hole A alive at `K^L` not `(K²)^L` (6-of-8 vs
     60-of-64 forgeries at the deployed tower). A **singleton pool closes it
     outright** — the hole is a function of how many ciphertexts the transcript
     exposes, not of the operation. ⚠ Deployed depth 2 + 132 results/multiply is
     exactly the many-ciphertext regime, so it is live for the deployed workload.
   - **The fix is a LAYOUT decision and the right one is FREE.** Interleave the
     limbs into one row and the row IS the shared opening: **+0 committed felts,
     +0 permutations** (`boundMul_iff_sharedSelector`). The bill is the 2-felt
     BabyBear bridge that sharing a row forces (`mle_gpu.rs:479`, already
     deployed): **+220,201–294,912 perms per ciphertext at lb=6**. The RLC
     alternative (`rlc_binds`, error `(L−1)/|F|`) costs +293,601 more and buys only
     a probabilistic binding; keeping per-limb-native tables costs ~4× that again.
     ⚑ **So the soundness argument and the field-choice lane converge: per-limb-
     native proving is what makes cross-limb binding expensive.**
   - **Still open:** Hole B has an exhibit and no closure; there is **no ct×ct
     arithmetization in the tree** to fix (the hole is in the design); and `ε_chk`
     **cannot be instantiated limb-locally**, which is new information for item 6.
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
   > ⚑ **09-04: Plonky3's side moved.** #1978 (2026-08-13) grades conjectured
   > security per round and at the instance shape; its conjectured LDT-only
   > numbers dropped **128 → 119–125**. The scope-difference hypothesis is
   > unchanged and still unchecked. `notes/proximity-delta-2026-09-04.md` §3.3.

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
