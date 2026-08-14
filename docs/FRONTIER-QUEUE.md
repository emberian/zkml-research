# What's next: the cheapest-ZK thesis, the vFHE gates, and the space-age list

2026-08-13. Written after the first two implementation lanes landed. This is
the forward-looking companion to `SYSTEM.md` (what we're building) and
`AGENDA.md` (the pillars).

---

## PART 1 — The cheapest-ZK thesis (the session's biggest synthesis)

Sort every speedup this campaign measured by size, and a pattern falls out
that nobody states in the literature:

**Statement-level and protocol-level levers are worth 10–100×. Prover-level
levers are worth 2–4×. The field spends nearly all its effort on the latter.**

| lever | size | layer |
|---|---|---|
| Sampled audits (24× prover → ~1.24× system at p=1%) | **~20×** | protocol |
| Read-only / write-once memory vs general RAM (6 cells vs ~502, SP1-measured) | **~80×** | statement shape |
| Semantic turn vs emulated VM execution (no instruction fetch to prove) | **large, unmeasured** | statement |
| Accumulate-then-decide vs verify-per-link (t openings vs 1–3k Poseidon2 perms) | **~10–100×** | protocol |
| Native-hash wrap vs emulated field (40.9M → 1.02M R1CS) | **40×** | engineering |
| Exact native format (requantization absent, not optimized) | **~1.3×** (measured; the 4× claim died) | statement |
| Packed sumcheck over BabyBear | 2.78× | prover |
| Celer grand-product vs logUp-GKR | 2.4× (past crossover) | prover |
| GPU sumcheck | 2.6–4.0× | prover |
| KoalaBear vs BabyBear in-circuit hashing | 1.8× | prover |

**So "cheapest ZK" is not a prover. It is a discipline:**

1. **Prove the smallest true statement.** Every layer of generality
   (VM emulation, general RAM, unpinned backends) is paid at proving time
   forever. The kernel's typed semantic turn is the statement-level version
   of this; the exact-native-format work is the numeric version.
2. **Don't prove what you can commit and audit.** The audit theorem (now
   machine-checked) converts any prover into a deployable one at
   `E[leakage] ≤ b/q`. This is the single largest lever and it is
   composable with everything else.
3. **Shape the workload so the cheap memory case dominates.** Read-only
   (preprocessed) and write-once (SSA) are ~80× cheaper than general RAM.
   Inference is weights-read-only + KV-append: almost entirely the cheap case.
4. **Defer and batch.** Accumulate, discharge once per epoch; batch by
   random linear combination (our own Mina trick, uninherited by the zkML side).
5. **Only then optimize the prover.** And there, prefer the levers that
   compound with (1)–(4): small-value handling, packing, the right field.

Corollary worth stating: **the industry's cost curve is shaped by proving a
statement nobody asked for.** That is the opening.

---

## PART 2 — What must be settled before "full vFHE"

Ordered by what unblocks the most. Each is a *question*, with the reason it
gates and the cheapest way to answer it.

### G1. Single-prime vs RNS — and the connection nobody made
**The question:** can our 3-limb RNS tower collapse into ONE ~109-bit
NTT-friendly prime that is simultaneously the FHE ciphertext modulus and the
proof field (the Zama 2026/027 / GBFV convergence)?

**Why it gates everything:** ⚑ **If yes, the cross-limb binding problem —
our #1 named soundness hole, the thing that makes proving BFV multiplication
hard — does not exist.** Cross-limb binding is an artifact of having limbs.

> ⚑ **REFINED 2026-08-14** (`notes/cross-limb-binding.md`, `breadstuffs`
> `5b653ba5d`). The hole is now exhibited in Lean and it is **two** holes:
> **provenance** (a quantifier swap) and **expressibility** (`⌊t·x/Q⌉` reads the
> CRT reconstruction). Single-prime does dissolve **both** — that claim survives.
> But the sequencing changes: **the provenance half closes for +0 felts / +0
> permutations** by interleaving the limbs into one row, so it need not wait on
> H1. What waits on H1 is the expressibility half. And the cost that single-prime
> avoids is now measured: the 2-felt BabyBear bridge that row-sharing forces is
> **+220,201–294,912 perms per ciphertext at lb=6**.
One prime, no limbs, no CRT reconstruction to bind, no
rounding-across-moduli that lives in no single field. It also deletes the
RNS-emulation-in-circuit cost that dominates every published vFHE result.
**Cost:** losing RNS speed on the FHE side (2-limb arithmetic in software).
**Answer it:** one afternoon — swap the modulus constant in `~/src/matvecmul`
to a 109-bit prime, set P=2^20, inner dim 512, run their existing end-to-end
test. Then measure the FHE-side loss in fhegg.

### G2. The parameter fork: N=4096 vs N=8192
The two-ladder composition needs ~2.5 extra levels for proof generation +1
for packing; we have ~3 total. **It does not close at deployed parameters.**
N=8192/log q≈218 closes it with ~2.5 payload levels left.
**Question:** what does the doubling actually cost — prover time, key sizes,
NTT throughput, bandwidth — on our stack? Nobody has priced it for us.
**Answer it:** extend the Fheanor harness (already built at our parameters)
plus `vendor/fhe-dregg/benches/bfv.rs` at both parameter sets.

### G3. The noise model on the ring
`Bfv/Noise.lean` models a ciphertext as a single ℤ phase. Any depth budget
is a *ring* statement. Until this lifts to `Poly q n`, every depth claim is
asserted by a model with no polynomials in it.
**Good news:** `matVecCt`/`RowBound`/`step_noise_le` are already the right
theorems (they ARE the LZ/Bae row-sum bound); only the carrier changes.

### G4. The CPA-D / determinism hinge — a Lean-shaped theorem nobody has
Threshold decryption **is** an IND-CPA-D oracle; leveled schemes provably
cannot be CPA-D secure unconditionally; and Smart–Walter show CPA-D-style
security wants *randomized* evaluation while provability wants *determinism*.
They derandomize in the ROM for TFHE. **The BFV analogue is unclaimed and
sits exactly on our deployment's wound.** This is simultaneously a security
question we must answer and a first-of-kind formalization target.

### G5. What the audit layer actually checks for FHE ops
We now have a machine-checked audit theorem with an abstract checker. Tier 3
needs that checker *instantiated*: what is the ε_chk for "the FHE engine
performed these ciphertext operations faithfully"? The 719-style vector-NTT
+ Hadamard checks are the candidate. Until instantiated, tier 3's soundness
is a parameter, not a claim.

### G6. Does the nonlinearity boundary compose with the audit game?
BFV can't do nonlinearity at our depth (t=2^20 ⇒ degree ≤2 regardless of
levels — proved by elimination). So nonlinearities go through the MPC
boundary or the TFHE PBS. **Does a sampled-audit regime span a
scheme-switching boundary?** Unexamined, and it is where a real system's
soundness argument would break first.

### G7. Rotation-free matmul, measured
The coefficient-encoding route closes under the *provable* bound with ~49
bits of headroom where the diagonal/BSGS route fails by 2.9. Build it
(`Encoding::poly()` exists, unused) and measure — it is the linear layer.

---

## PART 3 — Space-age: what Selvage doesn't do yet, ranked by (value × readiness)

**Tier A — identified, specified, and buildable now**

1. **The vector-relation / sumcheck architecture.** Selvage proves things
   about AIR+FRI; the whole field moved to sumcheck for tensor and ring
   workloads, and our own BFV equation family (98,304 equations) is a
   vector-relation problem *arithmetized as AIR rows*, which is why coverage
   sat at 1. `p3-sumcheck` exists at our pin. **This is the single biggest
   capability gap.**
2. **Accumulation instead of verify-per-link.** `Selvage/Depth.lean` proves
   the accumulation depth theorem (including a machine-checked falsification
   of the published statement's corner case) — and *nothing runs it*.
   breadstuffs re-verifies FRI in-circuit at every link. The migration turns
   a proved theorem into a statement about a deployed object.
3. **Verified table contents.** The worthwhile work item: a theorem that *this
   committed table is exactly the graph of this function*. StarkWare
   explicitly carved this out as an assumption. Cheap, unclaimed, compounds
   with every table-using consumer.
4. **The tuple-compression lemma** (restricted bad sets, linear not
   quadratic) — one small Lean lemma serving three consumers: our LogUp bus,
   a Celer adaptation, and the CommitSurface-injectivity apex route.
5. **Binary towers, wired.** ~9,750 lines / ~311 theorems formalized in
   minidregg, **unwired to breadstuffs**. The one seam the field memo says is
   worth paying for.

**Tier B — real, needs a design pass first**

6. **Streaming proving** ("70B on a 64 GB box"): substrate exists
   (Sparrow/Hobbit, 1.4× native space measured), system exists nowhere.
7. **Layer-fold sumcheck**: fold transformer layer-uniformity into the
   hypercube — primitive known (Thaler '13), application unclaimed.
8. **MoE router binding**: proof cost ∝ *active* params (~18× discount on
   frontier MoEs) + the permutation argument that stops route-to-cheap-expert.
   **Zero papers in 7,090.**
9. **LoRA inference-side proving + registry deltas**: fine-tuning side
   claimed at NDSS'26; the inference side and the provenance registry are open.
10. **Producer-consumer fusion**: the prover's MLE tables *are* the FHE
    evaluation's intermediates. Testable at toy scale on our own wgpu
    (`gpu_arena.rs` already keeps ciphertexts device-resident).

**Tier C — genuine research, high ceiling**

11. **A lattice/SIS commitment over KoalaBear.** As of today we have the
    theorem that this is *arithmetically the best field for one*
    (`Φ_{3^k}` irreducible ⇒ `R_q` is a field, maximal inertia). **No PCS
    exists in that ring family** — every shelf item is negacyclic and dies
    at KoalaBear. Open bills: the module-BKZ speedup at non-power-of-two
    conductors is unpriced anywhere; ZK/hiding is structurally absent from
    the family; the NTT is lost at high inertia. But this is the only route
    to one-hot addressing (Twist/Shout) for a stack like ours, and the
    formalization community is already pointing at lattices.
12. **The ring-native arithmetization-friendly hash** (2026/1127's stated
    open problem: RO-like over power-of-two cyclotomic rings, compactly
    arithmetizable *over the ring*; they show Poseidon-over-rings fails).
    Sits precisely on our Poseidon2 + Lean-hash-metatheory intersection.
13. **Proof-aware QAT** — train the model into the circuit (I-BERT's
    integer-only approximations port to fields directly). In nobody's paper.
14. **The two-regime security calculator** — soundness parameters as
    Lean-computed two-sided bounds with the regime tag *in the type*.

---

## PART 4 — Where attention goes next (dispatch order)

The template that just worked twice: *spec from the notes → brief with the
corrections baked in → statement-first with teeth → detached-clone gate.*

1. **M0: wire `p3-sumcheck`** — days, unblocks Tier-A #1 and the whole
   vFHE M1. The single highest-leverage engineering move on the board.
2. **The registry** — days, no prover, ships something real and closes an
   attack class nobody else has closed.
3. ~~**KPZ encryption fix + depth re-measure**~~ — ⚠ **DONE AND EMPTY: the fix
   is a NO-OP.** fhe.rs already uses exact-division encoding; there is no free
   depth level. Struck from the queue, not pending
   (`notes/kpz-noop-and-the-model-gap.md`, `docs/VERDICTS.md` §3).
4. **G1: the single-prime experiment** — an afternoon that could delete our
   #1 soundness hole.
5. **Verified table contents** — cheap and worth having.
6. **The tuple-compression lemma** — small, three consumers, one of them the
   breadstuffs apex floor.
7. **`num_queries` pinning** — field-independent soundness fix found in
   passing by the field memo (the recursion path reads it from the inner
   proof and never checks it against a configured count).
8. **KoalaBear-vs-Goldilocks recursion benchmark** — days on an
   already-generic harness; gates the flag day, and the study doesn't exist
   anywhere in the literature.

Everything above is either measured, specified, or explicitly marked as a
question. Nothing on this list is waiting on a research breakthrough.
