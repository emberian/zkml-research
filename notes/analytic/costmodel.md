# costmodel lane: the cost model as a total Lean function

Lane id aaebb426de60a31e9. Branch `lane/costmodel` in minidregg (pushed to origin when it builds).
Module `Assurance.CostModel`, namespace `Minidregg.Assurance.Cost`, file `Assurance/CostModel.lean`.
Builds on `Assurance/TwoRegimeQueryBudget.lean` (query column, regime in the type) and
`Assurance/ErrorBudget.lean` + `ErrorBudget120.lean` (the field-size wall).

## Interface (published early; consumers: generator, pcdsystem)

Everything is computable over `ℕ` / `ℚ` (no floats, no `ℝ` in the computable path), so `#eval`,
`#guard` and `native_decide` all work on it.

```lean
namespace Minidregg.Assurance.Cost

inductive BaseField | babyBear | koalaBear | m31 | goldilocks | tower256
inductive HashFn    | poseidon2W16 | poseidon2W24 | keccakF1600
inductive NttKind   | multiplicative | additive        -- BaseField.ntt : BaseField → NttKind

/-- The proof-system knobs (one FRI/STARK-style commitment). -/
structure Params where
  field      : BaseField
  extDeg     : ℕ   -- challenge extension degree (BabyBear⁴: 4)
  logBlowup  : ℕ
  numQueries : ℕ
  powBits    : ℕ   -- query-phase grinding
  transcriptPowBits : ℕ  -- ErrorBudget120's transcript PoW (0 at every shipped config)
  hash       : HashFn
  logArity   : ℕ   -- FRI fold arity 2^logArity
  foldLeafLog : ℕ  -- log2 of elements per FRI-layer Merkle leaf (Plonky3: = logArity; Tower256: 0)
  logFinal   : ℕ   -- stop folding at a domain of size 2^logFinal
  deep       : Bool -- STARK (separate DEEP codeword) vs FRI on the trace codeword (Tower256)

/-- The relation being proved (one committed trace matrix). -/
structure Shape where
  logRows   : ℕ   -- trace height
  width     : ℕ   -- base-field columns; this is the Merkle LEAF WIDTH of the trace commit
  logQuot   : ℕ   -- quotient chunks 2^logQuot = log2_ceil(constraint degree − 1) (each `extDeg` base columns)
  constraintMulsPerRow : ℕ  -- ext-field multiplies to evaluate all constraints at one point
  lookups   : ℕ   -- LogUp arguments K
  lookupArity : ℕ -- column-aggregation factor R

/-- Counts. Work and bytes in separate fields; never a duration. -/
structure Counts where
  baseMuls : ℕ   -- base-field multiplications
  extMuls  : ℕ   -- extension-field multiplications
  perms    : ℕ   -- hash permutations (Poseidon2 perms or Keccak-f calls)
  queries  : ℕ
  proofBytes : ℕ
  memBytes : ℕ   -- compulsory memory traffic, bytes

def proverCounts   : ByteModel → Params → Shape → Counts   -- ByteModel.compulsory eb for CPU
def verifierCounts : Params → Shape → Counts     -- native verifier, one proof
/-- One PCD/recursion step that verifies `fanIn` children of shape `child` (native counts;
    multiply by a `CircuitRates` to get in-circuit rows). -/
def recursionStepCounts (fanIn : ℕ) (p : Params) (child : Shape) : Counts
structure CircuitRates where rowsPerPerm rowsPerExtMul rowsPerBaseMul : ℚ
def inCircuitRows (r : CircuitRates) (c : Counts) : ℚ

/-- Security. The regime is in the name and the type: there is no JBR/CBR entry point.
    `udrErr` = ErrorBudget's landed algebraic budget + the UDR query column + the LogUp wall
    (union bound; [BUDGET-compose] is the named residual, as in ErrorBudget). -/
structure Adversary where queries depth scRounds scDegree hashQueries hashBits : ℕ  -- ErrorBudget's; `deployedAdversary`
def udrErr  : Adversary → Params → Shape → ℚ
def udrBits : Adversary → Params → Shape → ℕ    -- two-sided: udrErr ≤ 2^-b ∧ 2^-(b+1) < udrErr

/-- Hardware: rates are calibration constants, never the model. -/
structure Machine where mulRate extMulRate permRate copyBw : ℚ   -- ops/s, bytes/s
def Machine.time : Machine → Counts → ℚ   -- Σ over phases of max(work/rate, bytes/bw), seconds
```

For pcdsystem: per-recursion-step verifier cost is `recursionStepCounts a p child` (fields `perms`,
`extMuls`, `baseMuls`); its `perms` is `a · q · (Σ Merkle path depths + leaf hashes)` plus the transcript.
Leaf prover cost is `proverCounts p s` with `s.logRows` the rows. Both are linear in `numQueries` with
the coefficients exposed as `verifierPerQuery` / `verifierFixed`.

## Landed (minidregg origin `lane/costmodel`: b01fbec35, cdc28cc5)

Built on hbox pool tree t2 against main 279a12ff; whole-tree build: see below.

### What the function says (all on the reference leaf `refLeaf`: 2^16 rows x 386 columns, degree 7, one LogUp at arity 97; deployed adversary t = q = 2^40, k = 2^8)
- **Deployed IR-v2 (lb 6, q 19, pow 16, BabyBear^4, arity 8) reads 34 bits** through the composed UDR
  function (`ir2_reads_34`): query column 34, field wall 53, commit term 96, LogUp 100.
- **The deployed point is Pareto-dominated at its own 34 bits** (`ir2_is_dominated`): lb 2, q 21, pow 20,
  same everything else, is about 10x cheaper to prove (2.7e7 vs 2.7e8 permutation-units on the CPU
  reference), and has fewer verifier operations and a smaller proof (117 KB vs 124 KB).
- **ud100 = BabyBear^6 challenges, lb 2, q 124, pow 16, commit pow 0, fold by 2**: composed UDR error in
  (2^-101, 2^-100] (`ud100_two_sided`); 124 is the least q (`ud100_queries_minimal`); Pareto-minimal over
  the in-tree-proved grid (ext {4,5,6,8} x lb 1..6 x pow {0,8,12,16,20} x commit pow {0,10,20}, arity 2)
  at every q <= 1000 (`ud100_pareto_minimal`, via the kernel theorem `paretoCheck_sound`).
  Cost against the deployed point on the reference: prover 4.0e7 vs 2.7e8 (6.7x cheaper), verifier
  35.5K vs 3.98K perm-units (8.9x dearer), proof 1.08 MB vs 124 KB (8.7x larger).
- **ud120**: same with q 154 and 10 commit-grinding bits, (2^-121, 2^-120].
- **Arity 8 at BabyBear^5 with 20 commit-grinding bits dominates ud100** (`ud100_dominated_once_curves_admitted`):
  37.8M / 21.0K / 649 KB. It needs BCIKS20's UD curve bound, which is not formalized here: that gap is the
  price of formalizing it.
- The front at 100 bits never uses grinding to replace a blowup step; BabyBear^5 + 20 commit-grinding bits
  and BabyBear^6 + 0 trade 3 points of prover cost against nothing else.

### Calibration (Assurance.CostCalibration)
- The general count function reproduces the Tower256 schedule's counts exactly: 14,680,064 encode
  multiplies and 4,194,255 Keccak-f at ell 20.
- **T4 Tower256 prediction**: at the session's rates (multiply 3.2e8/s, Keccak 5.9e8/s, copy 234 GB/s,
  PCIe 6 GB/s) the model gives 14.8 / 65.9 / 290.6 ms per proof against the measured 16.9 / 67.0 / 303.5 ms
  (two streams): ratios 1.14 / 1.02 / 1.04, every one from below (`tower256_t4_session_prediction`). From
  the calibration range alone it brackets ell 20 and 22 and misses ell 18 by 2% (10.0-16.6 vs 16.9). The
  residual at ell 18 is host work: the upload measured 8.2 ms per proof against the model's 1.4.
- The encode is multiply-bound by more than 5x (`tower256_encode_multiply_bound`).
- The production Tower256 shape (lb 2, q 148) reads 100 bits at UDR (`tower256_reads_100`).
- ROTATION: the unfused INT8 route's HBM floor (2,624 B / 234 GB/s = 11.2 ns) is 6x the 1.85 ns table
  multiply, so it was a predictable loss; the fused floor (0.41 ns) is under it.
- STYLE.md's int8 GEMM rule, derived: HBM-bound on v5e iff n < 3 x ridge = 1441.5.

### The num_queries pin: not mine to land; hand-off to ember (flag day)
State on 2026-11-07: the pin exists and is pushed: emberian/plonky3-recursion `lane/num-queries-pin` =
f17051e8 (52e1fab, the q pin, plus the max_log_arity pin). breadstuffs still pins fc3c6df
(Cargo.toml:370-373). The exact change:
1. breadstuffs `Cargo.toml:370-373`: `rev = "fc3c6df"` -> `rev = "f17051e8"` for p3-recursion, p3-circuit,
   p3-circuit-prover, p3-poseidon2-circuit-air.
2. `recursion-verify/src/config.rs` `create_recursion_config_split_fri`: add `verify_max_log_arity: usize,
   verify_num_queries: usize` and pass them to `FriVerifierParams::with_mmcs(verify_log_blowup,
   verify_log_final_poly_len, verify_max_log_arity, verify_num_queries, verify_commit_pow_bits,
   verify_query_pow_bits, ...)` (the f17051e8 signature). Every caller passes the CHILD's mint knobs: an IR-v2
   child is `IR2_FRI_MAX_LOG_ARITY = 3`, `IR2_FRI_NUM_QUERIES = 19`; a recursion child is
   `RECURSION_FRI_MAX_LOG_ARITY = 1`, `RECURSION_FRI_NUM_QUERIES = 38`.
3. Gate (filtered): in the recursion repo `cargo nextest run -p p3-recursion -E 'test(fri_verifier_pins_query_count)'`;
   in breadstuffs `-E 'test(recursion_rejects) | test(num_queries)'` after `--list`.
4. Warning found here: the recursion examples derive `num_queries = (security_level - query_pow_bits) / log_blowup`.
   That is the CAPACITY (withdrawn) formula. At UDR the count for lambda bits is
   ceil((lambda - g) / log2(2 / (1 + rho))) (lb 6: 0.978 bits per query, not 6). No dregg config may take q from it.
5. Moving to ud100 is a second flag day: challenge field BabyBear^4 -> ^6, lb 6 -> 2, q 19 -> 124,
   max_log_arity 3 -> 1, new VK epoch. ud100 is the target that pin should then carry.

## Status
- [x] CostModel.lean written and built
- [x] Pareto front over the finite grid (compiled check + kernel soundness over all q)
- [x] proven 100-bit (and 120-bit) configuration, its cost; pin handed off with the exact change
- [x] calibration constants + Tower256 T4 prediction
- [ ] DeFi lower bound (sub-lane costmodel-swap)
- [ ] static roofline certificate (sub-lane costmodel-roofline)
- [ ] Codex review of the statements; merge to main after the whole-tree build
