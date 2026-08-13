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

## What we already hold (verified today, depth pending the audit lane)

- **breadstuffs `fhegg-{core,fhe,rtl,solver}`** — ~130K lines of Rust,
  wgpu-accelerated solver, and an **RTL crate** — the FPGA/custom-silicon
  ambition has an existing running start, not a cold start.
- **minidregg Lean FHE surface** — `BfvNativeBufferAdmission`,
  `PrivateComputationDeclaration` (typed ZK/MPC/FHE effect requests),
  `CrossModulus` (the RNS bridge), `Ext6GateProofNonzeroSuiteClosure`,
  `MpcSealedCellExecution`. FORCODEX: BFV wired into the effect system with
  suite pins, correctly non-deployable at zero pins — i.e. the *interface*
  is formalized and the crypto carrier is an explicit named IOU.
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
