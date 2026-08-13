# vFHE: the next rung, and what we already hold

2026-08-12. Prompted by Vitalik Buterin's read of the Attestable launch
(x.com/VitalikButerin/status/2087241620618088674, confirmed): an H100 does
~100–200 tok/s single-thread raw inference on a 30B model, so 53–85 tok/s
proved is **single-digit overhead for LLM proving** — and the ladder he names
is "single-digit FHE next, then ultimately vFHE (aka STARK × FHE)," with the
note that LLM inference being highly structured and almost-linear makes it
closer than present FHE overheads suggest.

His arithmetic agrees with our roofline lane's independent derivation (53
tok/s ≈ 50% of the ~108 tok/s batch-1 memory-bound ceiling — proving costs
about one inference-time). Two estimates, same answer, different routes.

## Why the structural argument is stronger than it sounds

The cost inversion we measured in ZK proving — **linear ops nearly free
(matmul 5.3% via sumcheck), nonlinearities dominant (66–75%)** — has an exact
twin in FHE: SIMD/rotation linear algebra is the cheap part, and
nonlinearities (polynomial approximation, bootstrapping) are the expensive
part. Same shape, same place. A vFHE-for-LLM effort concentrates ALL
difficulty — cryptographic and proof-theoretic — on one narrow class of ops,
and the linear bulk may be provable nearly free by sumcheck over the ring.

Second bridge, from this very week: **CKKS is block floating point** (shared
scale, noise as precision management). The MX/E8M0 exactness analysis we just
finished may transfer to proving CKKS rescaling. Flagged as a real question,
not assumed (survey lane will judge).

Third: the ~60-paper FHE-transformer-inference cluster (THOR, ARION, Nimbus,
SHAFT, MOAI…) that both miners *excluded as off-topic* ("input privacy, not
execution integrity") is, for vFHE, the substrate cluster. The filter was
right then and wrong now — worth remembering as a lesson about filters.

## What we already hold — AUDITED 2026-08-12 (corrects the first-pass claims)

**Real and deployed** (measured, 478/480 tests green today):
- **`fhegg-fhe` (103K LOC)** — working BFV at 128-bit, degree-4096: keygen,
  encrypt, exact fold, **ct×ct with relinearization**, an n-of-n distributed
  relin-key ceremony, threshold decrypt with a **proven smudging bound** that
  repairs a real hole in fhe.rs. Portable **wgpu negacyclic NTT** and a
  portable **wgpu TFHE programmable bootstrap** (blind rotation, CMUX chain,
  918 deployed steps) — no CUDA required. Node-deployed: `dregg-node` depends
  non-optionally and serves five live dark-clearing endpoints.
- **A Lean-authored, emitted, Rust-consumed BFV AIR already exists** — the
  house-blessed pattern: `EmitByName.lean` emits eight descriptors;
  `circuit-prove` proves with HidingFRI over BabyBear. Coverage honest and
  small: **1 of 98,304 equations materialized**.
- **Identical deployed parameters across all three trees, verified by
  conversion** (fhegg FOLD_MODULI = metatheory Bfv/Params = minidregg
  BfvCompressedEquation). And minidregg proves fhegg's q0 fits six radix-64
  limbs in BabyBear (`fheggQ0_scalar24_base64_fits`) — the sizing fact for
  BFV-RNS-in-a-BabyBear-AIR.
- `metatheory/Bfv/` — 102 theorems, 0 sorry, statement-first with real
  failing sides (smudge-too-small proves statistical distance 1).

**Corrections to what the first pass claimed:**
- **`fhegg-rtl` is NOT FHE RTL.** It is a standalone **Lean netlist DSL with
  a Verilog emitter** (608 Lean LOC) plus a fully commented-out SpinalHDL
  skeleton — disconnected by construction. Better aligned with house law
  than "Rust RTL" would be (Lean-authored hardware!), but embryonic, and the
  hardware ambition is a cold start apart from it.
- **`fhegg-solver` contains no FHE** — plaintext convex solvers. ⚠ And it
  holds a **debt flag: `src/air.rs` is a 334-line hand-written Rust
  constraint system** (Cert-F) — the class the house law forbids. Surfaced
  here as debt, not fixed.
- **The Lean BFV ciphertext has no ring in it.** `Bfv/Noise.lean`'s `Ct` is a
  single `ℤ` phase; relinearization is modelled as adding a bounded integer.
  The real ring work (`WgpuBfvNttSpec`'s `Poly q n`, `PrivateBookBfvBindingAir`'s
  deployed-moduli `RnsPoly`) lives in files that do not talk to it, and
  `FhEggRustDenotation.lean` is a self-`rfl` twin (same function body on both
  sides). **Zero `@[export]` on any FHE Lean symbol** — the strongest twin
  predictor in the house book.

**The two missing pieces, named by the audit — ⚠ #1 INVERTED by the FHE
theory lane (2026-08-13, see `fhe-core-theory.md`):** for public-weights ×
encrypted-activations at deployed parameters, the slot/BSGS route does not
even close under the provable noise bound; the **rotation-free
coefficient-encoding matmul** closes with ~49 bits of headroom and needs no
new key material. Rotation is needed only for slot-to-slot nonlinearity
chains (multi-layer wants n=8192 anyway); PackLWEs is the one genuinely
missing primitive for general packed shapes.

Original audit items, kept for the record:
1. **Homomorphic slot rotation.** Not a single Galois/rotation key in the
   tree. Without slot mixing, packed matmul (BSGS/diagonal method) cannot be
   written at all — today's linear step is one ciphertext per coordinate,
   O(d²) scalar ops, which does not reach LLM shapes. fhe.rs exposes the
   `EvaluationKey`/Galois material, so this is **a build, not research** —
   the smallest change with the largest unlock.
2. **Lift the noise model onto the ring.** Land rotation + packed matmul in
   Rust against real fhe.rs objects, and in the same pass lift `Bfv/Noise`'s
   `Ct` from `ℤ` to the already-proved `Poly q n` — otherwise we ship a
   matmul whose depth budget is asserted by a model with no polynomials in
   it (the n-factor expansion is exactly what the scalar model says it does
   not carry).

Also noted: two SIGABRT tests are the known missing-Lean-archive trap, and
`fhegg-fhe/Cargo.toml:129-140` claims a fix that is not effective on this
machine; `convex_engine.rs:83`'s "noise_after_T does not exist in Lean" is
stale — it exists at `Bfv/Noise.lean:433`.

- **70 vFHE-adjacent papers in the mirror** (full-text cache grep), a real
  subfield to survey rather than a void.
- The ring-proof substrate candidates from this week's mine: GKR over rings
  (2019/762), Zinc's composite moduli (2025/316), ring lookups (2026/471,
  2026/494) — exactly what proving RNS tower arithmetic natively wants.

## The survey's verdict (landed 2026-08-13)

**The calibration number for the whole ladder:** eprint 2025/719 proves a full
TFHE bootstrap with packed sumcheck **over BabyBear** in **2.02 s** — against
the 843 µs bootstrap itself, ~**2,400× overhead**. That is today's vFHE state
of the art: real, measured, and exactly the "crazy ambitious" distance Vitalik
named. (Same amortization applies as for LLM proving: sample the audits and
the per-op overhead stops being paid per op.)

**vFHE has already converged on our substrate.** The practical line (Zama's
plonky2 verifier, HasteBoots, 2025/719) is **small-field sumcheck** —
Goldilocks and BabyBear — because FHE's own 28–36-bit RNS limbs embed
natively in the proof field. The vFHE substrate IS the zkML substrate.

**Three legs of an unassembled machine, one group.** The SJTU/Chipltech group
published the FHE-proving protocol (2025/719), the sumcheck ASIC (PipeSC,
2026/691 — the entire 16-multiplier core is **2.3 mm², 1.2 W in 12 nm**), and
the NTT engine (RENTT, 2026/460), citing verifiable FHE as motivation in all
three — and has not assembled them. A vFHE accelerator is **an FHE machine
with a sumcheck coprocessor and hash cores riding its HBM and multiplier
pool** — not a merger of an FHE chip with a SNARK chip. The prover
(~0.016 modmul/byte) rides the FHE machine's memory system (<1 op/byte),
which the prover alone could never economically justify.

**The hardware reality check:** every famous FHE ASIC — F1, CraterLake, BTS,
ARK, SHARP, BASALISC — is *simulation*; none was fabbed. The first real
silicon is Intel HERACLES (ISSCC Feb 2026), shipped with 64 MB SRAM against
the 256–512 MB every simulated design assumed, no commercial plans, PI gone
— a capstone, not a roadmap. DPRIVE is over. Meanwhile **GPUs beat the
silicon roadmaps** (Zama: 1,040 confidential transfers/s on 8×H100 "a year
early, on commodity hardware"; Cheddar's CKKS bootstrap at 22.1 ms on an
RTX 5090 beats most *simulated* FPGA designs). Rule of thumb: an FHE-ASIC
paper's CPU baseline overstates by ~100–200× vs GPU.

**Two facts that make the open-hardware move buildable now:**
- **Zama's HPU is fully open SystemVerilog** (BSD-3-Clause-Clear): a complete
  TFHE processor — NTT cores *including a Goldilocks-64 variant*, PBS/KS
  datapath, scheduler, microcode, Versal V80 block design, prebuilt
  bitstream, measured ~13–14.2k PBS/s, actively developed. CoFHEE is
  silicon-proven open FHE RTL (55 nm, GPLv3). The one hole: **no open RTL
  anywhere for RNS-CKKS key-switching** — the field's largest open-hardware
  gap.
- **AWS F1 retired 2025-12-20** (every ZPrize FPGA artifact now targets dead
  hardware, unported). **F2** = VU47P, 16 GB HBM2 at ~430 GB/s measured,
  **$1.98/hr flat, ~$0.66 spot** (~$480/mo continuous). Verdict: credible
  for TFHE and prototyping; NOT CKKS-bootstrap-class (2× short on bandwidth,
  ~10× on SRAM — which is why every shipping FPGA FHE product is TFHE).

**The buildable move nobody occupies:** connect Zama's open HPU RTL to a
BabyBear packed-sumcheck engine sharing its HBM and multiplier pool, plus a
Poseidon2 island and a scheduler. Protocol published and implemented; FHE
processor open; board is a V80 or an F2 at spot prices; `fhegg-rtl`'s
Lean-golden-model→Verilog shape is the right glue. **Being early costs a
board, not a tapeout.**

**Three sharpenings from the full hardware report (landed after the addendum):**

1. **The vFHE overhead ladder has a protocol rung far below 2,400×.**
   plonky2-verified bootstrap: ~20 min → packed sumcheck (2025/719): 2.02 s
   (~2,400×) → **Laminate (eprint 2025/2285): 5–67× overhead, via GKR run
   *inside* the FHE** — attacking the protocol, not the silicon. Vitalik's
   "single-digit FHE-proving" rung is approachable along the Laminate axis,
   not the accelerator axis. (Argos, arXiv:2412.03550, gets 3–8% from a TEE —
   the trust-model alternative to keep in the comparison table.)

2. **The rate gap decides the architecture.** Zama's HPU emits ~13k PBS/s;
   proving ONE PBS costs ~194 core-seconds (2025/719). Rate-matching one FHE
   FPGA needs ~2.5M CPU cores — or **~26 prover dies per FHE FPGA even
   granting a 1,000× ASIC speedup**. Proving remains 10³–10⁴× the cost of
   evaluating. So the board-level HPU+sumcheck build is a *testbed and
   dataflow proof*, not a rate-matched system; rate-matching comes from
   protocol work (Laminate direction) + sampling amortization. The prover IS
   nearly free in *area* (2.3 mm² vs hundreds) — the binding constraint is
   bandwidth and the rate gap.

3. **Producer-consumer fusion is the real one-die argument — and it is the
   FHE-side answer to the shared-arithmetic question.** Co-located FHE +
   prover *contend* on HBM (both are <1–2.7 and 0.01–0.28 modmul/byte
   streamers) — UNLESS fused at the dataflow level: the prover's MLE tables
   ARE the FHE evaluation's intermediate polynomials, so a fused design
   streams FHE limbs through the sumcheck fold **as they are produced**,
   paying the traffic once. Off-die that data crosses PCIe twice. *"That
   producer-consumer fusion — not shared multipliers — is the real hardware
   argument for one die, and no published design does it yet."* Also on the
   record: Zama's HPU `ntt_gf64` core uses **Plonky2's exact prime** — an FHE
   accelerator and a prover already share a butterfly in shipping open RTL.

Survey's revised ordering: (1) Lean-verified cross-limb binding — the field's
actual soundness hole; (2) the Galois-ring small-value sumcheck port; (3)
HPU + packed-sumcheck on open FPGA; (4) the CKKS adversarial-steering
question; (5) BFV/MXFP4 pricing.

Corrections recorded: HEIR's `--emit-verilog` is a booleanization pass, not a
hardware backend (widely misreported); Fabric's FHE claim is one word in a
compiler-target list with zero published numbers and silence since 2025-03;
Ant's MPU H1 is the only other joint FHE+ZK silicon claim and has zero
verifiable specs.

## In flight

Both lanes have landed (survey above; audit in this note's holdings section).
The commitment stands: **aggressive-and-soon, fully open — including the
hardware.** Next artifact: the PLAN re-cut, drawing on every note in this
repo.
