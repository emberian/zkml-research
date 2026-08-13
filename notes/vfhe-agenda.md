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

**The two missing pieces, named by the audit:**
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

## In flight

- **Survey lane (opus)**: vFHE state of the art, ring-proof substrate
  recommendation, the FHE-LLM bridge, CKKS/block-float verdict, hardware
  landscape incl. joint FHE+prover silicon.
- **Asset audit lane (opus)**: what fhegg actually implements and tests, what
  minidregg's FHE Lean actually proves vs states, whether the two shores
  connect anywhere — ending with "what do we have Monday, and the first two
  missing pieces."

Agenda proper waits for both. The one commitment made now: **this goes on the
main agenda as aggressive-and-soon, fully open — including the hardware.**
