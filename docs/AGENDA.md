# The Open Verifiable Computation Agenda

2026-08-13. The synthesis of this repo's research run (~40 notes, ~35 commits,
14 research lanes, one full-corpus mine of 25,765 papers). Supersedes
`PLAN.md` as the top-level document; every claim below traces to a note in
`notes/` or `docs/`, and every note to a source or a measurement.

**Tags:** [measured] = a paper's own tables or our own harness · [verified] =
computed/proved here · [stated] = a primary source speaking · [inferred] =
ours, flagged · [awaiting] = an in-flight lane will settle it.

---

## 0. Stance

**Everyone deserves verifiability.** The aim is an open, post-quantum,
machine-checked stack for proving that a specific model, with specific
weights, produced a specific output — and its extension to encrypted
computation. Where we diverge from others' published choices it is because a
different point in the design space looks reachable, not because their
choices were wrong for them. Attestable, DeepProve, StarkWare, Zama, the
academic groups: collaborators in a worldsystem, competitors in no sense that
matters here. The open position is **vacant**: three of the four best-known
"open" zkML projects are not open-source (DeepProve: evaluation-only license
contradicting its own Cargo.toml; JSTprove: "NO USE RIGHTS"; ezkl: no LICENSE
file) [measured].

The one-sentence system: **commit everything · sample audits · prove sampled
work with a folded, fused, small-field sumcheck over the model's native
format · bind weights and architecture in a public registry · verify
artifacts in Lean end to end — and walk the same stack down the vFHE ladder.**

---

## Pillar I — Bit-exact proving of native-format inference

### The soundness core (the part that is finished thinking)

**Bit-exactness is a soundness property, not a fidelity preference.** Every
deployed fidelity-carrying system hands the prover a per-element acceptance
window (ZIP δ=9×10⁻³; zkLLM ε≈10⁻² row-sum; Spain per-op ε) [measured], and
Zamir's Theorem 1 (arXiv 2602.15756) shows a functionally-identical
adversarial network can steer any target output through windows at fp16
rounding scale — trigger weight M≈0.15, amplification 2^18 at depth 20
[measured]. The repair route provably does not exist: no useful approximate
multivariate Schwartz–Zippel lemma (Bitan–DeStefano–Goldwasser–Ishai–Kalai–
Thaler §5, with SVZ25's "no hope" counterexample) [measured]. **Every bit of
tolerance granted the prover is a bit the adversary can steer; a slack-free
spec gives Zamir nothing to hide in.** (`notes/float-in-zk-three-regimes.md`,
`docs/the-position.md`, the approximate-sumcheck verdict.)

### The format (measured to a conclusion)

- Our bf16 cost thesis **failed Phase 0**: 1.4×, not 4× — requantization is
  not absent but per-element-ified, and the 75% figure double-counted fused
  tables [measured, ours]. (`docs/PHASE0-RESULT.md`.)
- The surviving principle: **prove the model's NATIVE serving format.** The
  frontier ships block-native: gpt-oss is MXFP4 (98.1% of weights, 78.9% of
  per-token linear FLOPs, *no bf16 original exists* — the MXFP4 checkpoint is
  the evaluated artifact); ⚠ **DeepSeek-V4 DOES NOT EXIST** (404 with credentials — registry lane verified; V3.1 was substituted and the correction never propagated). DeepSeek-V4 is power-of-two block-scaled
  everywhere; Kimi-K3 likewise [measured, byte-verified census]. Gemma 4 —
  the model Attestable proves via int8 — is plain BF16, Tier 3.
- **MXFP4 block dots are exact ≤13-bit integer computations** (verified over
  20k blocks, two summation orders, zero deviations) [verified], and **the
  E8M0 scale spread in shipped gpt-oss weights is tiny: p50/p90/p99/max =
  2/2/3/8 over 1.38M reduction rows — 100% fit a width-8 alignment window**
  [measured, ours; per the 26-year corpus zeros, the first MX-for-proving
  measurement anywhere]. The cheap alignment path is the *only* path.
- The caveat that is now a design input: **the format pins weights, not
  computation** — one checkpoint, twelve vLLM backends; OCP MX §6.1 leaves
  dot-product order implementation-defined [stated]. The provable statement
  pins a backend — or pins the *math* via order-independent exact
  accumulation, which within-block exactness makes possible.

### The prover (priced, direction chosen, two reads pending)

- **Matmul is 5.3% of prover time; nonlinear work is 66–75%, requantization
  alone 25–34%** — DeepProve's tables, independently reproduced by OpenLLM's
  own appendix (a group that never cites DeepProve) and zkGPT [measured].
  The Ω(m) commitment floor (2026/1390) makes it structural [measured].
- Therefore the levers, ranked: **small-value commitment** (the only attack
  on the floor's constant; Thaler's surveyed program, 2–20× measured in
  Jolt; unclaimed for ML) · **exact 2^16 tables** for nonlinearities (no
  approximation error; domain escape *impossible by construction* — 0 of
  65,536 addresses lack entries, vs zkAgent's measured 4.16%/token aborts)
  [verified] · **layer-fold sumcheck** (transformer uniformity; primitive
  known, application unclaimed) · **streaming** (Sparrow/Hobbit: 1.4× native
  space measured; "70B on a 64 GB box" exists nowhere) [measured] ·
  **co-scheduled fusion** (witness-gen free by identity for exact formats;
  commitment matmul-shaped under linear-code PCS; sumcheck's early
  small-value rounds ride inference's own data stream) [inferred — the
  shared-arithmetic note; unmeasured].
- GKR/sumcheck won the field for structural reasons (no FFT, no trace
  commitment for matmul); small-field + hash PCS is live at Polyhedra and
  measured superior by both DeepProve's A/B and OpenLLM (FRI-M61 3.8–5.7×
  prover, ~1000× verify over KZG) [measured].
- **CLOSED**: Spain rejected as design (ordered-field theorems, false over
  F_p; verifier holds the RSA factorization), adopted as evidence — it
  PROVES a composition lemma whose conclusion is Zamir's δ-consistent set,
  and is exploitable at its own published parameters with ordinary weights
  at GPT-2 depth. Ozaki ratios re-verified and stand. Celer: adapt gated on
  one spike (grand product 10m vs 43m; crossover read off their own figure;
  table count is now a design variable). New read-and-price item: eprint
  2026/347, exact-integer Mod-PCS from any PCS, hash-based. See
  `notes/spain-celer-verdicts.md`.

### Honest baselines

DeepProve: 174/86 TPM (GPT-2/Gemma-3-270M, CPU, BaseFold — the config absent
from its public code) [measured]. Attestable: 53 tok/s on Gemma-4-31B/H100
[stated, unreproduced, no artifact]; **their CEO's own overhead range is
"2×–100×, depending on the configuration"** — the circulating "<10×" is
Vitalik's estimate against the most favorable baseline [stated]. Their
soundness regime (proven vs conjectured — ~30 bits apart in their
co-authored S-two whitepaper) is unpinned [measured/unknown].
(`notes/attestable-calibration.md`.)

---

## Pillar II — The audit game

**Sampling is the economics.** A 24× prover audited at p=1% is a ~1.24×
system [inferred, arithmetic]; Attestable's CEO states the same escape hatch
("it's enough to prove a very small portion") [stated]. The statement is
folklore (six literatures; Rinberg et al. did our exact application in Nov
2025) — the *composition* is not:

```
q = p·(1 − ε_snd) − ε_bind − ε_beacon        E[leakage] ≤ b/q
```

No source composes these terms [measured — narrowed 2026-08-13: 2026/541
has its own two-term composition (ε_tst + ε_sep), so the claim is precisely
"the legs exist separately, nobody composes them, and the two closest works
each assume one away." Full statement: `notes/audit-theorem-statement.md`]. `ε_beacon` is a
function of adversary compute, not a constant (grinding papers; Relect/SSLE
as the transparent-setup selector) [awaiting: concrete ε_beacon table].
Hard limits stated up front: HLvA steganography means ε_snd > 0 always — the
achievable claim is a *rate* bound; the burst adversary wins with prob 1−p,
so per-message entropy caps are load-bearing; and the 2025/358 lower bound
says covert security buys **no asymptotic savings on the ledger** — sampling
amortizes proofs, never the ledger [measured].

**The machine-checked version is ours to take**: nothing in this area has
ever been machine-checked (verified across Lean/Isabelle/EasyCrypt/Coq
ecosystems), and `Loom/LightClientSound.lean` is already structurally the
commit-then-audit theorem — sharp bound, keystones, kernel-clean. A
refactor, not a campaign. **CLOSED 2026-08-13**: 2026/541 read in full. Overlap: they published our
architecture (Merkle trace + sampled paths) with a two-term composed bound
and a 1/N single-path ceiling; ~67,000× faster proving than zkLLM at ~19×
proof size, against a strictly weaker (statistical, ε_sep-based) soundness
object. Survives to us: the full q-composition (their FS transport is their
own named open problem, citing Campanelli–Datta 2024/1645), the machine
checking, the fully adaptive sequential bound (verbatim — three independent
absence confirmations), and the two-dimensional burst hypothesis. The
formal statement, with the supermartingale and the ε_beacon ≤ α·p
instantiation, is written: `notes/audit-theorem-statement.md`.

The non-prover half already exists **verified** in our trees: the inference
ledger is a minidregg Hyperdocument event log with durable WAL and idempotent
retry [verified, home tree].

---

## Pillar III — Binding and the registry

**Hollow-LLM (arXiv 2607.28884) is unclosed by everyone**: a proof binds the
relation over committed weights, not computational effort — ghost weights
serve a small model under a large model's proofs [measured]. And the field
is racing the *wrong way*: two 2026 systems race to make zkML
architecture-*private*, which would make the effort gap undetectable by
construction [measured, mine]. Closing it needs a **publicly checkable
weight-and-architecture registry** — a thing an open project can ship and a
closed one structurally cannot. Composes with: LoRA fine-tunes as registry
deltas (base committed once; adapters are kilobytes; the fine-tuning side
just got claimed at NDSS'26, the inference side is open) and MoE router
binding (~~zero papers in 7,090~~ **⚑ RETRACTED 2026-08-13 — the absence was
FALSE**: ZK-DeepSeek arXiv 2511.19902 and arXiv 2606.05433 OP-10, **both already
in `~/paperbin/` on the day it was declared**; the sweep read first-2-page caches
and both bury MoE in a subsection. Top-k as a **threshold** argument, Θ(N), not a
permutation; proof cost ∝ active params — **18.3× at context 1, decaying to 2.7×
at 128k**, and the router binding costs 0.72% of the sparse proof. The live gaps
are the tie-break, expert-identity binding, and the context decay — see
`notes/moe-router-binding.md`).

---

## Pillar IV — vFHE

**The ladder, calibrated — and split (2026-08-13): it was TWO ladders.**
SNARK-over-FHE (publicly verifiable, proves ciphertext ops): plonzy2 ~20 min
→ packed sumcheck 2.02 s *96-core wall* (~194 core-s; the ~2,400× was not
core-normalized). FHE-over-SNARK (designated-verifier, proves the plaintext
relation, one-bit leakage per observed verdict): **Laminate 5–67×,
core-normalized but entirely estimated — no implementation** [measured →
corrected]. Different security statements; not one ladder. Sampling composes
cleanly with the first class, poorly with Laminate (noise provisioning is
paid on 100% of instances; repeated public verdicts are a leakage oracle).
**Laminate_base nonetheless fits our deployed fhegg parameters today** for a
depth-1 payload, needing no rotation keys — verified at source down to the
irreducible trinomial. Full corrections and the M0/M1/M2 path:
`notes/vfhe-shortest-path.md`. The single-digit rung is approachable along the
*protocol* axis; the accelerator is not the critical path (rate gap: ~26
prover dies per FHE FPGA even granting 1,000× ASIC speedup) [measured,
lane-derived]. vFHE has **already converged on our substrate** — small-field
sumcheck, because ⚠ **FALSE, and contradicted by the file cited three lines earlier** (`vfhe-shortest-path.md:32`: 36 > 31 bits, hence `fheggQ0_scalar24_base64_fits`). They embed natively into THEMSELVES. Original claim: FHE's 28–36-bit RNS limbs embed natively [measured].

**Structural synergies** (`notes/shared-arithmetic.md`): FHE computes in Z_q
already — no float→field gap exists, the ciphertext trace IS the witness;
and the one-die argument is **producer-consumer fusion** (the prover's MLE
tables are the FHE evaluation's own intermediate polynomials, streamed
through the fold as produced — traffic paid once; no published design does
it) [measured, lane-confirmed]. Zama's open HPU already contains Plonky2's
exact prime in its `ntt_gf64` core: the machines share a butterfly in
shipping RTL today [measured].

**Our holdings, audited** (`notes/vfhe-agenda.md`): a working, node-deployed
BFV stack (ct×ct + relin, distributed relin ceremony, threshold decrypt with
a *proven* smudging bound, wgpu NTT + TFHE bootstrap, 478/480 tests green);
a Lean-emitted Rust-consumed BFV AIR over BabyBear (1 of 98,304 equations —
the pattern landed, coverage honest); identical parameters across all three
trees, verified by conversion. Missing pieces, named: **homomorphic slot
rotation** (zero Galois keys in tree; without it packed matmul cannot be
written; fhe.rs exposes the material — a build, not research) and **lifting
the noise model onto the ring** (today's Lean ciphertext is a single ℤ
phase). Debt surfaced: `fhegg-solver/src/air.rs` is a hand-written Rust AIR
— house-law debt. [awaiting: Laminate/719 deep read → the shortest-path vFHE
demo on fhegg.]

**Hardware, de-mystified:** every famous FHE ASIC is simulation; the first
real silicon (Intel HERACLES) is a capstone with 1/4–1/8 the SRAM the
simulated line assumed; GPUs are beating the custom-silicon roadmaps
[measured]. The open move costs **a board, not a tapeout**: Zama's HPU is
full open SystemVerilog on a V80; F2 is TFHE-credible at $0.66/hr spot; the
`fhegg-rtl` Lean-netlist→Verilog shape is the right glue. Framed honestly as
a testbed and dataflow-fusion proof, not a rate-matched system.

---

## Pillar V — Verified artifacts

Post-Avigad reality (`notes/avigad-stwo-verdict.md`): **"we do Lean" is no
longer a differentiator** — StarkWare runs a funded in-house Lean program
(their S-two AIR formalization: kernel-clean, real theorem, deliberate twin
with an unaudited premise and drift documented in-tree); ArkLib and a
Rust→Lean extraction pipeline are attacking the twin problem on Plonky3 and
RISC Zero [measured]. What remains ours:

1. **Verified table contents** — a theorem that *this committed table is
   exactly the graph of GELU under stated semantics*. StarkWare explicitly
   carved this out as an assumption; unclaimed by anyone. Cheap for us.
2. **Emitted-artifact verification** — the house law's whole point; the
   descriptor-emit pattern already runs for the BFV AIR.
3. **The FRI/proximity cone** (40K lines, 1,537 theorems — larger than their
   whole S-two dev) — the layer everyone stops before, where the conjectured
   legs live, now in an active refutation race (2025/2046 et al.) that
   re-prices deployed "100-bit" claims.
4. **The vacuity instruments** — carrier census, premise inhabitation.
   ⚠ NOT a differentiator and not novel (ember, 2026-08-13): checking whether
   your assumptions have inhabitants is what careful people do, vacuity
   detection has existed in model checking since ~2001, and vacuous
   assumptions early in a development are NORMAL — you write the statement
   before you have the witness. The only real difference is that we run the
   check mechanically and by default instead of by remembering to, and that
   we mark what is still open. Shipping unmarked is the error, not having
   them. Their development lacks the mechanical check; "Verification Theatre" (2026/192: four vulns
   *inside* verified proof code) is the external motivation.

Two imports taken from their work: the restricted-bad-set tuple-compression
trick (portable into our LogUp now), and a conditional route past the
breadstuffs `CommitSurface`-injective apex floor (bind through FS-sampled α)
[measured → design].

---

## The unclaimed-claims ledger

Verified absent from the literature (full-corpus mine, 25,765 papers, 26
years, plus targeted sweeps):

| claim | status |
|---|---|
| MX/microscaling/block-float × ZK, any form | **zero papers**; our E8M0 measurement is the field's first number |
| MoE router binding / proof ∝ active params | zero papers |
| LoRA **inference**-side proving + registry | open (fine-tuning side claimed NDSS'26) |
| transformer layer-fold sumcheck | primitive known, application unclaimed |
| streaming LLM prover ("70B on 64 GB") | substrate exists (Sparrow/Hobbit), system doesn't |
| co-scheduled inference+proving fusion | three adjacent works, none fuses with inference; vFHE fusion also unclaimed |
| machine-checked commit-then-audit + q-composition | no formal treatment anywhere [awaiting 2026/541 read] |
| verified table contents | carved out as an assumption by the one group that could have done it |
| proof-aware QAT ("train the model into the circuit") | in nobody's paper |
| float-split-with-exact-limb-products (the numerical half of Ozaki) | ZK has the integer half in production; the numerical half is absent |

## Phasing — first moves, cheapest-decisive first

1. **The audit theorem in Lean** (Pillar II) — refactor `lightClientSound`
   into the commit-then-audit statement with the q-composition. Small,
   first-of-kind, and the load-bearing formal object for the whole system.
   [gated only by the 2026/541 read]
2. **Verified tables** (Pillar V) — the 2^16 exp/GELU/rsqrt tables with
   contents proved against a reference spec, committed once for the
   ecosystem. Cheap, unclaimed, compounds with everything.
3. **The MXFP4 alignment-window prover harness** (Pillar I) — price the
   exact block-dot + width-8 window over BabyBear against DeepProve's
   protocol, using the measured spread. [gated by Spain/Celer reads]
4. **Registry + Hollow-LLM closure design** (Pillar III) — spec first;
   the ledger halves already exist verified in minidregg.
5. **vFHE first artifact** — prove one fhegg BFV operation with sumcheck
   over BabyBear [gated by the Laminate/719 read]; slot rotation lands in
   parallel as the packed-matmul unlock.
6. **The fusion testbed** — HPU + BabyBear sumcheck on a V80/F2, the
   producer-consumer dataflow proof. The board is $9.5k or $0.66/hr.

## Deliberately not doing

IEEE-754 bit-exactness (nobody wins; headline figures are unbenchmarked
strawmen) · error-tolerant proving (Zamir; Spain loses to quantized on its
own Figure 4; no multivariate Remez) · approximate sum-check as accumulation
fallback (wrong field, no PCS, 14× the precision of exact) · MXINT8-as-
conversion (zero shipped models; proves a derivative) · racing anyone on
throughput before the harnesses land · dedicated prover ASICs (the market
already selected against them; GPUs improve 10×/6mo).

## The standing corrections file

This run's method produced its results by killing its own claims quickly:
the bf16 4× (→1.4×), "requantization absent" (→per-element-ified), rank-1
exp for exact designs (→rank 253), "sampling soundness is a first" (→
folklore + Rinberg), "8854 gates" (→unbenchmarked strawman), "Binius = our
unexplored lever" (→Thaler's surveyed program; ML application is the gap),
"Ozaki is the transplant" (→deferred carry is routine; the numerical half is
the gap), "single-digit overhead" (→a baseline choice; CEO says 2–100×),
"~2,400× is vFHE SOTA" (→Laminate 5–67×). Each correction is in a note with
the evidence. **The instrument that found four of these was "try to break
it" briefing; keep briefing lanes that way.**
