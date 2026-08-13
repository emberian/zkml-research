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
- **`lb=6` is 2.9× off the measured optimum** (20 ms at lb=4 vs 58 ms).
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
- **The exchange rate (ours, measured)**: one committed base felt ≈ **3,120
  field mults at lb=4, 12,331 at lb=6**; virtualizing one ≈ **40 per layer**.
  **78×–308×**, which turns the sweet spot into a threshold rule. Swings 28×
  across the blowup knob.
- **The multilinear seam is ONE `RbrKnowledgeSoundness` instance, not a new
  abstraction.** No hash-based multilinear PCS is indexed by an evaluation
  point; the commitment is a Merkle vector commitment to a codeword — our
  existing `OpeningScheme`, unchanged. Route: **BaseFold at RS in our own
  unconditional (1−ρ)/3 band.** Five new items, no conjecture, no new
  proximity result.
- **Jagged PCS has no cryptographic content** — which is why it is tractable.
  A large convenience on top of a PCS that does the security work.
- **`fold_add` as one opening: ratio = B, PROVER-SIDE ONLY.** The verifier
  moves the opposite way (O(B) Merkle work vs a polylogarithmic AIR verifier),
  and the shared-tree fix collides with per-party root binding.
- **The base→extension boundary is a measured ~3× cliff.** The emitted
  constraint object should be a **syntactic expression over ℤ-coefficients
  with each concrete ring a valuation** (semiring provenance: transport
  commutes iff the map is a homomorphism). This is a *check*, not a deadline —
  cheap iff constraints consume the ring through an interface.
- **Sumcheck is 2–17% of prover time.** Prover-level optimizations trade in
  2–4× on a term that small; statement- and protocol-level levers are 10–100×.
- **We are abandoning Plonky3.** Upstream code may be read for API shapes and
  used as a throwaway differential oracle; it never enters the trust path.

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

1. **Is the prover hash-bound?** Derived 94% at lb=6; measured 19–40% at
   ρ=1/2. **Decides whether the field/hash migration is worth 3.4× or much
   less. One profiling run.**
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
