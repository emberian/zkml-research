# HPU × sumcheck seam study — the verdicts

2026-08-13. 162,770 lines of Zama SystemVerilog read at source; Verilator run
performed; fhegg-rtl measured. Full report in the lane output; this note holds
what changes decisions.

## Corrections to our record
- **"They share a butterfly" — half-false.** Same prime, different machine:
  `ntt_core_gf64` has NO multipliers (twiddles are barrel shifts via the
  ord(2)=192 trick). Not portable to BabyBear: three elaboration-time walls
  plus the shift trick itself.
- **The HPU ciphertext ring is ℤ/2⁶⁴**; Goldilocks is only the transform
  field. Proving THIS hardware's execution needs the ℤ/2⁶⁴→F_p binding that
  719 avoided by fiat. If arithmetic-sharing matters, the proof field is
  Goldilocks [lane inference] — a pull against KoalaBear-everywhere, parked
  as "hardware testbed is its own domain."
- ⚠ Silent-wrong trap: `mod_reduct_solinas2` accepts BabyBear's form
  (INT_POW gap = 4), passes its elaboration guard, and **would build wrong**
  (its own header warns; the guard doesn't check). Use Barrett.
- Tap FIFO sizing: **NTT_OP_W = 66, not 64** — 256 bits/beat short at psi64
  if sized from "Goldilocks = 64."

## The load-bearing findings
- **Tap #1 = `ntt_acc_modsw`** (post-INTT CMUX product, coefficient domain,
  pre-accumulation): 128 coefs/cycle × 64 b @ 400 MHz = **409.6 GB/s**, with
  free sol/eol/pbs_id framing for MLE construction. No-backpressure
  discipline mandatory (the SLR crossings have no ready).
- **Audit sampling is a bandwidth NECESSITY, not an optimization**: the tap
  rate is ~16× the entire ciphertext AXI budget and ~half of V80 HBM.
  100%-proving is physically impossible; the only question is q.
- **14,221 PBS/s derived from source** (PSI·R·MOD_Q_W·f and per-PBS 28.80 MB
  of intermediates) — independently reproducing Zama's published figure,
  which appears nowhere in their repo.
- **The audit instruction costs dozens of lines of C, zero RTL**: the ucore
  is a MicroBlaze running C with runtime IOp tables; 43/64 opcodes free;
  `DOPS_WAIT` already implements stall-on-external-agent — a prover is just
  a different flag-writer. Rate-matching needs ~2.76M cores (reproduces the
  rate gap), so the sampled-testbed framing stands.
- **Verilator lints the production NTT clean TODAY** after a 15-line
  mechanical patch (`var [` → `var logic [` — a Verilator parser crash, not
  a design issue). Simulation-first is real; the whole-design sim is blocked
  by uninitialized SSH-fork submodules and source-less stimulus ELFs (11
  README-vs-source discrepancies logged).
- **It was ported FROM a VU47P-class part**: the U55C flag path is still
  live in run.sh — materially de-risking an F2 reverse-port. Exactly one
  Versal primitive in all synthesizable RTL; zero DSP/BRAM instantiations
  (all inference).

## fhegg-rtl distance — measured
Single-bit, combinational, flat, gate-level; missing buses, arithmetic
nodes (forfeits DSP inference — the most consequential gap), registers,
hierarchy, memory, control. Evaluator is ~O(n^2.4): golden vectors break
first (~19 s/vector at 100k gates). Verdict: do NOT grow it gate-wise; add
a word-level layer (semantics over List (BitVec w), proofs via
bv_decide/structural lemmas) — then the evaluator's list handling stops
mattering too.

## The de-risk order (adopted; buy nothing yet)
1. **The rate/area spreadsheet** — hours, no hardware: at what sampling
   rate q does a VU47P-resident engine keep up, and what does that q do to
   the audit theorem? Prices everything else.
2. **Verilate + cosim `ntt_core_gf64`** — days, laptop: Zama's production
   NTT running on the desk, falsifiable claims, and the same harness fills
   fhegg-rtl's `todo!()` cosim stub.
3. **The wgpu fusion toy** — days, laptop: `gpu_arena.rs` already has
   ResidentHandle ciphertexts that never leave the device; fusion = make
   Arena multi-pipeline, add a WGSL sumcheck fold, measure with/without
   the download between BFV-fold and sumcheck-fold. If fusion doesn't win
   at toy scale on a GPU it won't win on an FPGA.
Expected outcome [lane inference, endorsed]: the honest framing is "an
audit-sampled proving testbed riding an FHE machine's memory system," and
at that framing F2 spot ($0.66/hr) beats a $9.5k V80.
