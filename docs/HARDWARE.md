# The hardware pillar — F2, ASICs, and the one measurement that decides the target

2026-08-13. Reconstructed after dropping it from the synthesis. **The design
phase changed what this pillar is about.**

## ⚑ The same open question decides the silicon

Our one unresolved measurement — **is the prover hash-bound or
arithmetic-bound?** (derived 94% hash at lb=6; measured 19–40% at ρ=1/2) —
**is also the hardware spec.**

- **Hash-bound ⇒ build a Poseidon2 engine.** Permutations per second is the
  figure of merit; the field's only relevant property is hash bits/op.
- **Arithmetic-bound ⇒ build an NTT/butterfly and MLE-fold engine.** LDE and
  folding dominate; memory bandwidth and modmul throughput are the spec.

**One profiling run on a real IR-v2 proof at lb=6 and lb=4 unblocks the field
decision AND the hardware target.** Do it before anything is bought or
designed. And note the virtualization exchange rate points the same way: if
virtualizing costs ~40 mults/layer against 3,120–12,331 per committed felt,
a design should optimize **sumcheck rounds** — *unless* hash-bound, when it
should optimize the opposite.

## What the ASIC dream is actually up against — measured, not vibes

- **No ZK-prover ASIC has ever been fabbed and independently measured.**
  NoCap, zkSpeed, UniZK, zkPHIRE, PipeZK, SZKP — **all simulation.**
- **Irreducible shut down 2025-11-12** after 3.5 years, and their stated
  reason was *"FPGAs underperformed GPUs."* They invented bit-granular tower
  commitments; if anyone had an FPGA case it was them.
- **Software beats silicon on this curve right now.** Succinct's card-count
  collapse came from software (⚠ the specific "160×4090 → 16×5090" factor is
  **not substantiated anywhere in their repo** — the *mechanism* is: VRAM tier
  sets shard size, and ≤30 GB cards get ~29% smaller shards).
- **ZKProphet** (the only independent GPU ZK measurement): compute-bound on
  the **int32 pipeline**, per-SM throughput **flat across GPU generations** —
  which is an argument *for* custom silicon and *against* waiting for NVIDIA.
- ⚑ **But NVIDIA already shipped a ZK instruction**: **`clmad`**
  (carryless multiply-accumulate, SM80+, CUDA 13.3) — **sumcheck 4.1–12.9× on
  B200**, explicitly citing Binius. The first mass-produced instruction
  motivated partly by ZK. **And our binary-tower cone (~9,750 lines, ~311
  theorems in minidregg) is unwired** — that is the software half of the same
  bet.

## ⚑ The cheaper version of our own thesis, which we never priced

**CROSS (2026/160, HPCA'26) + MORPH (arXiv 2604.17808, DAC'26)** — one
MIT/Google program, same lead authors — run **both FHE and ZK as INT8 GEMMs on
TPUs**. TPU v6e beats WarpDrive-on-A100 NTT by **1.43×**; **451× perf/W vs
OpenFHE**; MORPH ≈**10× GZKP-on-V100**. Code public. **MoMA** (CGO'25) is one
rewrite system emitting both FHE and ZKP kernels.

**That is our fusion thesis — one substrate, both workloads — executed by
renting existing AI silicon with no RTL at all.** The F2 plan was made without
it on the table. ⚠ And *"When Proofs Meet Hardware"* (2606.16146) reports **no
universal winner between NTT and sumcheck at equal SRAM/bandwidth** — so the
architecture question is genuinely open even at the silicon level.

## What the HPU seam study established (and it survives)

- **The fusion tap exists and is ideal**: `ntt_acc_modsw` — post-INTT CMUX
  product, coefficient domain, pre-accumulation — at **409.6 GB/s** with free
  `sol/eol/pbs_id` framing for MLE construction.
- ⚑ **Audit sampling is a bandwidth NECESSITY, not an optimization**: the tap
  rate is ~16× the entire ciphertext AXI budget. **100%-proving is physically
  impossible at the tap**; the only question was ever the rate.
- **The audit instruction costs dozens of lines of C and zero RTL** — the
  "microcode" is a MicroBlaze running C, 43/64 opcodes free, and `DOPS_WAIT`
  already implements stall-on-external-agent.
- **Verilator lints Zama's production NTT clean today**, after a 15-line
  mechanical patch. Simulation-first is real.
- **The design was ported FROM a VU47P-class part** (the U55C flag path is
  still live), so **F2 reverse-port risk is materially lower than assumed** —
  exactly one Versal primitive in 162 kLOC, zero DSP/BRAM instantiations.
- ⚠ **The shared-butterfly claim was half false**: same prime, no shared
  datapath — Zama's `ntt_gf64` has **no multipliers at all** (barrel-shift
  twiddles via ord(2)=192, structurally Goldilocks-only), and the HPU's
  ciphertext ring is **ℤ/2⁶⁴**, with Goldilocks only the transform field.

## The Lean-authored silicon path, measured

`fhegg-rtl` is 608 lines: **single-bit, combinational, flat, gate-level**, with
an **O(n^2.4) evaluator** — golden-vector generation breaks before proving
does (~19 s/vector at 100k gates). **Verdict: do not grow it gate-wise.** Add
a **word-level `BitVec` semantics** so `RealizesSpec` is over `List (BitVec w)`
and proofs go through `bv_decide` — at which point the evaluator's quadratic
list handling also stops mattering, and DSP inference (which a gate-level
netlist forfeits) becomes possible.

## The order — nothing bought yet, and that is correct

1. **The profiling run.** Decides the field, the hash, and the silicon target
   at once. Hours.
2. **The rate/area spreadsheet.** At what sampling rate `q` does a resident
   engine keep up, and what does that `q` do to the audit theorem? **Prices
   everything else.** (The rate gap is ~2.76M cores to match the tap.)
3. **The wgpu fusion toy** — `gpu_arena.rs` already keeps ciphertexts
   device-resident; fusion is "make `Arena` multi-pipeline, add a WGSL fold,
   measure with and without the download." **If fusion doesn't win at toy
   scale on a GPU it won't win on an FPGA.**
4. **Price CROSS/MORPH against the F2 plan.** Renting TPUs at 451× perf/W with
   no RTL may dominate a $9.5k board, and it does both our workloads.
5. **Only then** the board, and F2 spot ($0.66/hr) over V80 ($9.5k) unless the
   spreadsheet says otherwise.

**The honest framing of the whole pillar**: not "a prover ASIC," but **an
audit-sampled proving testbed riding an FHE machine's memory system** — which
is a demonstration of a dataflow, not a rate-matched product. The ASIC dream
is downstream of a market that has never once fabbed one, and upstream of a
measurement we have not taken.
