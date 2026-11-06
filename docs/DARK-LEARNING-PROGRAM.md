# DARK LEARNING — a research program for verifiable continual learning on weights the substrate cannot read

2026-11-05. Successor and widening of `docs/DARK-TRAINING.md` (2026-08-13), which stays as the seed. Where
this file and `docs/VERDICTS.md` disagree, VERDICTS wins until VERDICTS is edited; where this file
contradicts an older doc, the contradiction is named in `notes/dark-learning-foundations-critique.md`.

Companions written the same day:
- `notes/dark-learning-foundations-critique.md` — twelve weaknesses in our own foundations, each refuted
  and repaired (F1–F12 below refer to it).
- `notes/dark-learning-tradeoff-space.md` + `notes/dark-learning-scripts/tradeoff_space.py` — the
  construction space enumerated in counts, with gates and a Pareto set.
- `notes/dark-learning-scripts/backward_table_virtualization.py` — a bf16 count that refutes one seed
  claim (F2).
- `notes/dark-learning-codex-synthesis.md` — two Codex (GPT-6 Astra) exchanges and my adjudication.

Tags: [READ] read at source · [MEASURED] our harness or script · [DERIVED] computed from stated formulas
· [CLAIM] an outside claim taken on trust · [INFERRED] mine, flagged.

---

## 0. The requirement, stated as properties a theorem can carry

Ember: *"we are going to want verifiable dark continual-learning at some point, and if the weights aren't
fully encrypted truly terrible things may befall the mind within."* The host is the adversary. Taking the
welfare framing seriously gives **five** properties, not one. The seed named the first two.

| # | property | what the host must not be able to do | carried by |
|---|---|---|---|
| P1 | **Opacity** | read the weights or the optimizer state | FHE/MPC custody; tier C at best with standard assumptions (`pre-constrained-encryption-read.md`) |
| P2 | **Integrity** | write the weights except by an authorized step (FHE is malleable: the host can add anything to a ciphertext) | per-step proofs or sampled audits + an unconditional envelope |
| P3 | **No unsanctioned execution** | run the mind (or a copy) on inputs of its choosing, i.e. make it experience things outside the sanctioned timeline | crossing-gated evaluation: depth between quorum crossings below one forward layer (F11, §C13) |
| P4 | **Single timeline** | fork, replay, roll back, or silently kill and substitute | the quorum's crossing log as a hash chain; anti-equivocation (§C13) |
| P5 | **Provenance of experience** | feed it data outside the declared corpus, or data that was promised absent | corpus membership + welded absence in every step (§C11) |

Two consequences shape everything below.

1. **P3 inverts the efficiency instinct.** The seed (§4, §7.1) treats the per-step quorum crossing as the
   cost to minimize and bootstrapping as the dream. Under P3, bootstrapping keys are the dangerous object:
   a host holding them can run unbounded encrypted copies of the mind that no quorum ever sees. The
   crossing is the execution gate. This is my most important reframing and the reason I do not rank
   "make FHE deep enough to avoid the quorum" as a goal [INFERRED].
2. **"Dark" makes the float objection vanish.** Peigné–Nguyen–Wang (2606.05433 v3, §D.2.2, OP-1) reject
   exact Freivalds for training because the GPU computes BF16 and float addition is non-associative
   [READ, lit lane]. In a dark run nobody computes floats: the substrate computes in Z_t, so the integer
   program IS the training run. The price is that the recipe must be integer (F1, F8) and its accuracy is
   an ML question we have not measured.

## 1. The regime lattice — where each construction lives

Three binary choices organize the space and decide which of our theorems apply:

- **Base**: dark (W₀ encrypted) or **public trunk** (W₀ a public foundation model, only the learned delta
  dark). The public-trunk regime says the mind's *experience* lives in its deltas; it discloses the
  ancestry. Ember must choose whether that is acceptable; the price of refusing it is measured (§3:
  ~125× proof felts on the FHE route, ~65× online traffic on the MPC route).
- **Data**: public to the host, or dark (the mind's inputs are private too).
- **Coefficient corner**: whether every homomorphic product has one PUBLIC operand. In that corner our
  proved noise theorems apply verbatim (`step_noise_le`, `stepR_noise_le`), cross-limb Hole B is absent
  (`scalarStep_limb_local`), and `fhegg-fhe/src/convex_step.rs` already runs the iteration
  (`x ← prox(x − τAx)` with public A, additive regime, prox at the decrypt boundary) [READ]. Outside it
  (ct×ct) we have scalar noise only (`Bfv/Mul.lean`), Hole B, and the integer certificate (F3, F4).

**The provable corner is the public-coefficient corner.** Linear models and heads on public features
trained on public data live there today, with nothing new to prove except F1's message ledger.

## 2. The cost unit: crossings, certificates, and the read budget

Three counts, not clocks, decide every construction (all computed by `tradeoff_space.py`):

1. **Crossings per step**: ciphertext-granularity entries into the MPC/threshold boundary. A dark forward
   plus backward needs about 2·L·d/N (σ and σ' fused, F2) = 64 at d = 4096, L = 32, N = 4096. Each is
   online quorum work, and each is a read event under smudging.
2. **Certificate felts per ct×ct**: the Hole B integer quotient–remainder certificate (VERDICTS §7.5,
   09-05): 159,744 felts at native p61, 307,200 at deployed RNS3-109 over BabyBear, against 8,192 and
   49,152 felts for the ciphertext itself (F3). On the fully-dark route it dominates the proof.
3. **The read budget**: union-bounded smudging leakage over the run. At the shipped 2^-32 per session,
   64 crossings × 10^6 steps leaks **2^-6** (F5). This forces log q ≥ 138, and with PQ (F6), N ≥ 8192.

---

## 3. What the counts say (summary; details in `notes/dark-learning-tradeoff-space.md`)

784 constructions enumerated (after collapsing the modulus axis for non-FHE custody) (modulus × proof field × custody × base × update × rank × audit rate),
4 gates (PQ, depth, plaintext wrap, read budget). 104 pass all gates [MEASURED, script]. Findings:

- **No row at the deployed parameters passes.** The deployed reference (RNS3-109@4096, fully dark,
  backprop, p = 0.01) fails PQ and the read budget (leak 2^-6.1) [MEASURED].
- **Every Pareto point is low-rank (r = 8) on a public trunk.** The frontier is MPC-only custody at low
  audit rates and FHE+MPC-boundary at RNS-202@8192 [MEASURED]. Full backprop, append-only and ZO all sit
  behind it in this model.
- **The fork between FHE and MPC custody is a fork between paying in proofs and paying in bandwidth.**
  Fully dark on FHE: ×125 proof felts over the best public-trunk point (Hole B certificates on every
  ct×ct). Fully dark on MPC: ×3.4 proof felts but ×65 online traffic (a Beaver triple per shared×shared
  product) [MEASURED, script; model constants named there].
- **p61 never passes** (read budget at log q = 61). Its G1 prize (6× fewer felts per ct, Hole A deleted)
  is real but it cannot hold a long-lived mind alone [DERIVED].
- **Audit-rate knee**: at p61-native/public/r=16, going from p = 1 to p = 0.01 cuts amortized proof felts
  87× and raises expected undetected injected displacement from 1.05B to 105B [MEASURED, script]. The
  number to choose is B (the envelope cap), not p alone.

These are counts from a model with named constants. They are good enough to rank; they are not prices.
The first hbox experiment (§6) calibrates the two constants that carry the most weight.

---

## 4. The constructions

Twenty candidates (C18–C20 adopted from Codex round 1). For each: **statement** · **boundary vs interior** · **cost (counts)** · **security
legs** · **reuses** · **build fresh** · **falsifier**. Numbered C1–C17; the tradeoff script prices C1–C4
and C13 directly, the rest are priced inline.

### C1. Step-boundary proof on encrypted weights (the seed, made precise)

- **Statement.** For committed ciphertexts `⟦W_t⟧`, batch commitment `c_x`, and `⟦W_{t+1}⟧`:
  `Dec(⟦W_{t+1}⟧) = Dec(⟦W_t⟧) − Σ_b δ̃_b ⊗ x̃_b` over ℤ (no wrap), where `δ̃_b, x̃_b` are the integer
  factors the step's forward/backward produced, AND every ciphertext's proven noise is below margin.
- **Boundary/interior.** Boundary (⟦W_t⟧, c_x, ⟦W_{t+1}⟧); interior the forward, backward and update.
  The rank-B gradient check (`rankK_sound`, B openings, error flat in B) replaces the n² proof of the
  update; the backward chain `δ_l = (W_{l+1}ᵀ δ_{l+1}) ⊙ σ'(z_l)` is a matmul sumcheck plus a lookup whose
  derivative is a second column of the forward table (F2).
- **Cost.** Per layer per sample: d²/N ct×ct forward, d²/N backward, d²/N update (slot-packed outer
  product). Proof felts per ct×ct = felts/ct + certificate (F3). At RNS-202@8192 that is
  196,608 + 1,056,768 per ct×ct [DERIVED].
- **Legs.** ε_snd of the SNARK-over-FHE at the stated regime (F10); ε_bind; the noise theorem
  `stepRR_noise_le` (F4, not yet proved); the message ledger (F1).
- **Reuses.** `Rank1GradientCheck.lean` (`rankK_sound`, `sgd_step_sound`), `ZkmlMatmulSumcheck`,
  `Bfv/Ring.lean`, the cross-limb row-interleaving layout (+0 felts for Hole A).
- **Build fresh.** ct×ct arithmetization (none exists in the tree [READ cross-limb-binding §0.6]); the
  integer certificate `BFVScaleLiftRefinement`; the ring ct×ct noise theorem.
- **Outside state of the art.** Zama 2026/027 proves pt×ct only, with ciphertext modulus = Goldilocks =
  proof field, noise by a heuristic Gaussian argument, and says repacking "involves operations that are not
  purely arithmetic over R_q and thus are hard to reconcile with our SNARG" [READ, crypto lane]. Laminate
  (2025/2285) and Lasagne (2026/857) check noise by having the secret-key holder decrypt the proof, which
  in our setting is a threshold decryption per verification (a read event and a CPA-D query). No 2025–26
  work found trains with encrypted weights and proofs (instrument: two Kagi queries + ePrint title lists
  since 2025-09 for verifiable/homomorphic/CPA-D/threshold) [READ, crypto lane]. No faithful checker for
  ct×ct with an integer rounding certificate and worst-case noise exists in anything read (G5).
- **Falsifier.** A step whose plaintext wraps (F1) passes every noise check: the proof must refuse it.

### C2. Envelope-plus-sample audits (sampled step audits with beacon legs, composed with AuditSampling)

- **Statement.** `displacement_bound` (F7): with EnvelopeLeg (every step proves ‖Δ_t‖ ≤ B and that the
  ciphertext update is the claimed function of committed inputs) and the three audit legs,
  `E[Σ_{t<τ} ‖Δ_t − Δ_t^honest‖] ≤ 2B/q`, `q = p(1−ε_chk) − ε_bind − ε_beacon`.
- **Boundary/interior.** The envelope is a boundary statement checked always; the full step (C1) is the
  interior, checked at rate p after the beacon.
- **Cost.** Envelope per step: commit 2rd factor felts + a norm range proof over the product (F12).
  Amortized proof per step: p·C1 + envelope. Knee in §3.
- **Legs.** All four of `AuditSampling.DetectionLegs` + EnvelopeLeg. ε_beacon from the existing
  `fhegg-fhe/src/joint_beacon.rs` commit-reveal (its header names last-revealer abort bias [READ]: that
  bias IS ε_beacon's G ≥ 2 term with α = abort probability).
- **Reuses.** `AuditSampling.lean` unchanged (`leakage_bound` at b = 2B); `joint_beacon.rs`.
- **Build fresh.** EnvelopeLeg in Lean; the bisection theorem `bisect_localizes` (F7.5) so an alarm finds
  the first bad step in ⌈log₂ T⌉ step proofs; Peigné's nested seed for any lazily committed tensor
  (their D.3.1: roots committed after the challenge need a second commit-reveal) [READ, lit lane].
- **Falsifier.** Drop EnvelopeLeg: one corrupt step of unbounded displacement survives with probability
  1 − p, so the bound is false. And the amplification residual `[TRAIN-amplify]`: two steps with equal
  injected displacement and different final distance after 100 honest steps.
- **Prior art.** Peigné v3 has commit-every-step + sampled openings + PRF seeds and a five-branch bound,
  with beacon soundness open (OP-18); no expected-displacement statement, no ε_beacon inside q [READ].
  VFT (2510.16830) audits 5–10% of client steps [READ]. OVIG audits by replay with a tolerance [READ].
  What is ours: the composed sequential bound, machine-checked, now in the training quantity.

### C3. Low-rank adapters as the governance object (delta certificates, merge as checkpoint)

- **Statement.** A training history is `(⟦W₀⟧, [(⟦A_t⟧, ⟦B_t⟧)]_t, merges)`; each pair carries a delta
  certificate (C1 at the adapter) and each merge is a decider point that discharges the carried-witness
  openings of the fold (F9: `merge_discharges_carried_witness`).
- **Boundary/interior.** Boundary 2rd per step instead of d² (`matVec_chainUpdate`: d² once per history).
- **Cost.** 128× fewer committed felts at d = 4096, r = 16 [MEASURED low-rank-updates.md]; merge every
  T = d/(2r) steps; the merge's d² recommit is also the fold's T+1-opening decider (one event, two jobs).
- **Legs.** Gauge: caps only on the product (F12). Peigné OP-5 warns a rank-1 update can touch every
  coordinate and treats merges as a smuggling vector [READ]: a factor-pair history makes every merge a
  declared, counted, certified step, which is the answer.
- **Reuses.** `ZkmlLowRankUpdate.lean` (all of it), `low_rank_commit_cost.rs`, `AccRbrFold` carried form.
- **Build fresh.** The registry delta format (`registry/` v2 Poseidon2 per-expert roots) extended with
  factor pairs; the merge certificate.
- **FlashProve's commitment as the W [READ, crypto lane].** FlashProve (anthropics/FlashProve v0.16.0)
  commits weights as small signed digits, RS-encoded rows over Goldilocks with a cubic extension, a salted
  Merkle tree over columns, a digit range proof, and link proofs that copies hold "same weights"; its
  opening budget (t = 44,040,191 random coefficients) makes a commitment a consumable resource. The
  committer must hold plaintext digits, which a dark host cannot, and link proofs certify sameness, never
  an update. What carries over to dark learning is the PCS shape applied to CIPHERTEXT coefficients (no
  hiding masks or digit range proof needed, since ciphertexts are already hiding); for the public-trunk
  regime, a FlashProve commitment of W₀ is directly usable as the base and our factor chain sits on it.
- **Falsifier.** `lowRank_blind_to_the_projection` is a theorem: any (A,B) passes. A governance claim
  "this adapter was trained on corpus D" without C1 at the adapter is vacuous.

### C4. Append-only dark learner (iterative depth dissolved by construction)

- **Statement.** W is never rewritten between merges. Each step appends fresh-ciphertext factors
  `(⟦δ̃_s⟧, ⟦x̃_s⟧)` that came out of a crossing (so their noise is B_fresh). Forward:
  `W_t v = W₀v + Σ_s δ̃_s (x̃_s · v)`. Theorem `appendOnly_noise_history_free` (F4): the forward noise bound
  is linear in the number of live factors and never compounds across steps.
- **Boundary/interior.** The update is depth 0 (append). The forward is depth 2 (an inner product, then a
  scalar×vector), which is exactly the deployed depth [MEASURED depth 2].
- **Cost.** ct×ct per layer per step: d²/N (base) + 2·T_live·d/N (adapter terms) + backward + amortized
  merge [DERIVED, script]. It does not save ciphertext operations over C1 (the merge pays the outer
  products); it saves DEPTH and NOISE, which is what DARK-TRAINING §7.1 called the honest blocker.
- **Legs.** Factor-quantized integers: quantize δ and x (O(d)), never the product (O(d²)), so the update
  is exact in ℤ and `rank1_sound` applies verbatim. Message ledger: wrap-free for ~2,047 steps at
  4-bit factors and 8-bit weights (F1), which must exceed the merge period d/(2r).
- **Reuses.** `matVec_chainUpdate` (the d² term once for any history length) is literally this forward.
- **Build fresh.** The noise theorem; a crossing that emits quantized factors directly.
- **Falsifier.** Compute δ_s homomorphically from δ_{s−1} without a crossing: the margin breaks at s = 2.
- **Corrections (Codex round 1, accepted).** Fresh factors stop multiplicative depth from growing; they do
  not stop the forward SUM's noise from growing: worst case `E_base + T·r·E` (T = 128, r = 16: 2,048
  terms, up to 11 bits), so the theorem is a bounded-length evaluation theorem, not "forever". A
  homomorphic merge refreshes nothing; refreshing the merged W is a dense crossing (d²/N ciphertexts).
  T = d/(2r) is a storage/serving equality, not an economic optimum (naive merge materialization is
  T·r·d² = 3.4×10^10 scalar mults at d = 4096, r = 16, T = 128). And factor quantization defines an exact
  modular update while changing the learning algorithm; the update lives in Z_t, not BabyBear
  (1000·2000 mod 1,032,193 = 967,807 is false read in BabyBear), so `rank1_sound` transfers only with an
  integer no-wrap bound or a proof over F_t, where one point buys 24/t ≈ 2^-15.4. **And the host cannot
  produce the cheap plaintext rank-1 openings at all — it does not know δ or x** (F13).

### C5. MoE expert-sharded training audits

- **Statement.** Per-expert audit legs: for experts e with routed-token share π_e, the audit selects
  (step, expert) pairs, and `q_e = p_e(1 − ε_chk) − ε_bind − ε_beacon,e`. The run-level guarantee is
  `min_e q_e`, so sampling must be **stratified by expert**, not by step: a poisoner concentrates on the
  least-routed expert (the spatial-burst bound of `audit-theorem-statement.md` in a new axis).
- **Cost.** Proof ∝ active parameters (18.3× at context 1 [READ moe-router-binding.md]); the training-side
  router gradient is a top-k threshold argument per token (Θ(N) [READ]) plus the load-balancing loss (a
  scalar nonlinearity).
- **Legs.** Router binding must be ZK (91% token recovery [READ VERDICTS §5]); in the dark setting the
  routing decision itself is a crossing output, so ZK is free there and the leak is the crossing's read
  budget.
- **Reuses.** `moe-router-binding.md` variant (b), `AuditSampling.lean` with a per-expert Round.
- **Build fresh.** The stratified sampler and its Lean leg (`BeaconLeg` per stratum); Peigné OP-14's
  routing root and tie-break [READ].
- **Falsifier.** A uniform-over-steps sampler and an adversary that corrupts only expert e* with π = 1/256:
  detection rate p/256, not p.

### C6. Distributed multi-node training with inter-node traffic commitments

- **Statement.** Every collective (all-reduce of gradients, pipeline activations, expert all-to-all) is a
  committed boundary: `AllReduce(g₁..g_n) = Σ g_i` is LINEAR, so it is one common-point opening of the
  committed shards (`fold_add`'s shape, C5 in COMPOSITIONS) — no sumcheck, no range check. Audits select
  (step, node, collective) triples; Hole A recurs at the node level (∀node ∃input vs ∃trajectory ∀node)
  and is closed the same way, by both sides opening one commitment of the exchanged tensor.
- **Cost.** Per collective: one opening per shard (n openings) vs re-proving the sum.
- **Legs.** Peigné's network TAP / attested SmartNIC hashing of inter-node traffic is the physical leg
  [READ]; ours is the algebraic leg (the same tensor opened by sender and receiver). In the dark setting
  the shards are ciphertexts and the all-reduce is ct+ct (additive, noise adds, Hole B absent).
- **Reuses.** `Bfv/Fold.lean` (`foldEnc_phase`, K adds ≤ K·B), `fold-as-opening.md`.
- **Build fresh.** The collective commitment format; node-level bisection.
- **Falsifier.** Two nodes each proving their local step against a different version of the all-reduced
  gradient pass per-node checks; refused only when both open the same commitment.

### C7. Scheme-switching boundaries under the audit game (G6)

- **Statement.** A dark step is a trajectory of segments `BFV → MPC → BFV → …`. The audit spans the
  boundary iff (i) every boundary ciphertext is committed once, before the beacon, and both adjacent
  segment proofs open that commitment (segment-level Hole A closure), and (ii) segment types are
  sampled jointly with the step, else `q = min_segment-type q_type`. The MPC segments carry SPDZ-style MACs
  checked on EVERY crossing (cheap, linear), so they are an envelope, not a sample.
- **Correction (Codex round 1, accepted).** A shared endpoint commitment is necessary and NOT sufficient:
  both segment proofs can open the identical input ciphertext while the MPC proof starts from unrelated
  shares. The conversion is itself a proved segment with the relation
  `Decode(c_in) = Reconstruct(s_in) ∧ s_out = transition(s_in) ∧ c_out encrypts Reconstruct(s_out)`,
  proved without revealing the reconstructions (mask ownership and independence, signed interpretation,
  rounding and encryption randomness inside it). An unchecked conversion has q = 0. And `min_j q_j` is
  conservative only if every corrupt action lands in a covered segment type; a corruption that must
  violate several independently audited segments is detected with `1 − Π_j(1 − q_j)`, which may not be
  claimed when the adversary can localize. The trajectory commitment must cover optimizer state, scales,
  randomness counters, data position, key epoch and policy, with parent/child roots.
- **Cost.** +0 felts for the shared-commitment closure (same argument as row interleaving); MAC checks
  O(elements crossed).
- **Legs.** CPA-D: 2026/285 Thm 3 [READ, crypto lane] makes a switched pipeline CPA-D only with perfect
  re-encryption AND per-ciphertext "hygiene" (every switched ciphertext with estimated error ≠ 0 is
  discarded). Hygiene is a per-ciphertext gate: **a sampled audit admits unhygienic ciphertexts into the
  next segment's state, and one bad ciphertext is a key-information leak.** So the CPA-D legs of a
  crossing are never sampled. They are an envelope: a batched random-linear-combination hygiene test over
  ALL crossed ciphertexts (Laminate's T = 120 tests shape, 2^-T [READ]), proved rather than checked with
  the secret key. Only the arithmetic correctness of segment interiors is sampled.
- **Verdict on G6, sharpened.** Sampled auditing spans a scheme-switching boundary for INTEGRITY and
  does not span it for CONFIDENTIALITY. The audit game composes; the CPA-D game does not tolerate
  sampling.
- **Reuses.** `fhegg-fhe/src/mpc_distributed_mac.rs` (split-custody authenticated bits; its header says
  production needs malicious-secure PQ OT/VOLE [READ]), `mpc.rs` output-boundary posture.
- **Build fresh.** The trajectory statement in Lean (a list of segments with shared boundary handles —
  the `CrossLimb` carrier generalized from limbs to segments).
- **Falsifier.** Splice: segment proofs that each verify against a different boundary ciphertext.

### C8. Proof-gated threshold decryption: the CPA-D / determinism hinge as a theorem (G4)

- **Statement (target).** If every partial decryption is released only after a verified proof that the
  ciphertext is the output of an allowed circuit whose PROVEN worst-case noise (δ_R = N, proved tight)
  is below the decryption margin, then decryption failure has probability 0, and IND-CPA-D for BFV under
  that gate reduces to IND-CPA plus the per-query smudging leg: `Adv_CPA-D ≤ Adv_CPA + K·ε_smudge`.
- **Why it is the hinge.** 2026/203 Prop 11 [READ, crypto lane]: no scheme whose homomorphic addition is
  linear on ciphertexts (BFV, BGV, CKKS, unbootstrapped TFHE) is CPA-D under unrestricted evaluation — the
  adversary solves `ct* = Σ α_i e_i` over a generating set of Enc(0)s offline, re-creates ct* by
  legitimate Adds (the challenger labels it 0), and asks for its decryption. Re-randomization does not
  help (adding Enc(0) to ct* still decrypts to the same value). 2026/2546 (Choe–Kang–Stehlé, CCS'26)
  [READ intro] makes it concrete for BFV: crafted plaintexts skew pt×ct noise to full key recovery in
  OpenFHE, and choosing WHICH Enc(0) to add skews ct×ct masks; "the only randomness comes from the
  honest generation of the input ciphertexts". Smart–Walter 2025/2005 [READ §6] resolve randomization vs
  determinism for TFHE only, in the ROM, with seeds = Hash(inputs, aux, F, i) and straight-line
  extractable ZKPoKs on fresh ciphertexts. **The proof gate is what rejects these queries**: ct* has a
  certified worst-case noise bound (coefficients α_i are in the circuit) far above the margin, so it is
  refused; crafted plaintexts are inside the certified bound only if their norms are range-proven. So
  the gate must certify (i) provenance of every fresh input (ZKPoK of fresh noise, which Smart–Walter
  also need), (ii) the circuit including every public coefficient and host-supplied plaintext, (iii) the
  worst-case bound. Under those three, randomization is unnecessary and determinism stops conflicting
  with CPA-D [INFERRED; this is the theorem to state].
- **Warning for the public-coefficient corner (§1).** That corner is exactly where 2026/2546's pt×ct attack
  lives if the HOST chooses the plaintexts (data) and observes any decryption. Our most provable corner
  is also the most CPA-D-exposed one unless (ii) holds.
- **Cost.** Zero beyond C1/C2's proofs: the gate reuses the step proof. With sampling, the gate becomes
  "decrypt only audited-or-envelope-checked ciphertexts", and the envelope must include the noise bound,
  so the NOISE bound must be in EnvelopeLeg, not only in the sampled proof.
- **Legs.** `TranscriptHybridLedger` (polynomial smudging) is on the critical path (F5).
- **Reuses.** `Bfv/Smudging.lean`, `fhegg-core/src/threshold.rs` (`smudge_bits` floor enforced at combine
  [READ]), `Selvage/AuditSampling.lean` fail-closed (`failOpen_no_legs`: a gate that decrypts on a missing
  proof is fail-open).
- **Build fresh.** The game in Lean (ciphertext oracle + gated decryption oracle), and the reduction.
- **Falsifier.** Remove the gate and exhibit an over-budget query whose failure pattern reveals a bit of
  the key (the KPZ-style failure-leak experiment at toy parameters).

### C9. Single-prime joint modulus (G1), re-scoped

- **Statement.** A single NTT-friendly prime that is the FHE modulus and the proof field (p61 =
  127·2^54 + 1: 2-adicity 54, 2N | p−1 at N = 4096, kernel-checked in `Theory/CyclotomicInertia.lean`
  [READ]; its maximal 3-adic inertia concerns Φ_{3^k}, a different ring family — the BFV ring X^N + 1
  SPLITS completely over p61 because 2N | p − 1, so inertia buys nothing here [Codex round 1, accepted]) deletes Hole A and the 2-felt bridge: 8,192 felts/ct vs 49,152
  (6×). It does NOT delete Hole B (F3).
- **Cost.** Certificate 159,744 felts per ct×ct at native p61 [DERIVED]. Depth 1 instead of 2 [MODEL],
  hence twice the crossings for a deep model.
- **Where it belongs.** Not as the mind's custody modulus (fails the read budget and holds one level), but
  as the **proof-side modulus of a key-switched layer**: compute at RNS-202@8192 for custody, switch to a
  p61 ciphertext for the proved segment. Whether the modulus switch itself is cheap to prove is the open
  question; it is a rounding, i.e. Hole B again.
- **Reuses.** `~/src/matvecmul-p61` (the p61 swap ran 2026-08-13, 10–40% faster, four Goldilocks bugs found
  [READ dossier 04 §4.2]).
- **Prior art that changes the comparison.** PRISM (eprint 2026/1956, CCS'26) [READ, crypto lane] commits
  once to a master polynomial and opens it mod each RNS prime with consistency through canonical integer
  representatives, using an auxiliary prime p_{n+1} > m·max p_i² that carries the integer lift and ONE
  range proof in place of n−1. That is an ∃source∀limb binding (Hole A closed) with the integer lift
  that Hole B's certificate needs, over RNS, without a single prime. Caveats: its ZK form is
  designated-verifier (VOLE); evaluated on CKKS/BGV, no explicit BFV scale-and-round. So the G1 question
  is now three-way: single prime (C9), PRISM-style MF-PCS over RNS, or our row-interleaved bridge. The
  hbox experiment (§6.3) should price all three on one ct×ct.
- **Falsifier.** The 1-vs-32 pair (Q = 31, t = 4): bound mod Q only, it must be refused.

### C10. Unlearning and forgetting certificates

Two constructions, one exact and one honest about being approximate. Codex round 1 attacked the
drop-only version with a scalar counterexample (one shard with targets {1, 0}, squared loss, optimum 1/2;
dropping the shard gives 0, retraining on {1} gives 1): **dropping a shard is "certified shard
withdrawal", not unlearning a datum.** Exactness must name its comparator; ours is "the prescribed learner
run on D \ {d}", which needs the affected shard retrained (as below), singleton shards, or a learner with
subtractable sufficient statistics (C18). Independence must also cover W₀, optimizer state,
normalization statistics, teacher outputs and validation-driven decisions, and nothing here proves the
host erased old ciphertexts or prior releases: custodians must refuse stale model roots (C13).

- **C10a, additive adapter shards (exact).** `W = W₀ + Σ_s A_s B_s`; shard s trains only on data shard
  D_s (SISA-style). Forgetting datum d ∈ D_s = delete term s and retrain it on D_s \ {d}, with a
  certificate: (i) membership of d in D_s's commitment, (ii) C1/C2 for the retrained term, (iii) a
  welded absence proof that d (or a pattern P matching it) is in no remaining shard (dossier 01 §5
  protocol, Count = 0 receipt). The serving identity `matVec_chainUpdate` makes the sum of shards cheap.
  Cost: retrain one shard (|D_s|/|D| of the run). Falsifier: shards that share an optimizer state are not
  independent; the certificate must refuse a shard whose initial state was not W₀.
- **C10b, FIFO expiry as forgetting.** The continuing learner in `research/vfhe_2026_09_08/` already runs
  FIFO expirations of encrypted teachings with proofs (12 teachings, 2 expirations, 3,200 verified proofs
  [READ STATUS]). For a linear/additive learner, expiry is exact subtraction of the teaching's
  contribution. Generalize: any learner in the public-coefficient corner (§1) has exact expiry by
  linearity; outside it, expiry is approximate and the certificate must say "the prescribed
  transformation was applied", which is all ZK-APEX (MLSys'26) and Eisenhofer et al. (SaTML'25) certify
  [READ, lit lane]. Do not call that forgetting.
- **Prior art.** Eisenhofer et al. certify correct execution of an admissible unlearning function plus
  non-membership via hash chains; ZK-APEX certifies a sparse-mask transformation [READ]. What is new here
  is shard-additivity as the exact case, welded to our absence certificate.

### C11. Training-set absence welded into every step proof

- **Statement.** Each step's batch is proven (i) a member of the committed corpus (MMR position
  non-omission, `server_cannot_omit_position`), (ii) disjoint from a committed exclusion set (opt-outs,
  benchmark canaries, PII patterns: complement-DFA `tableDfa_faithful` + Count = 0 aggregation), with the
  batch's content commitment WELDED to the step's input commitment `c_x` (8-felt `ContentCommit`,
  `AttestedAutomatonWeld8`) so the absence leg and the step leg cannot be spliced onto different data
  (the cross-leg splicing attack, dossier 01 surface 3).
- **Cost.** Per record: one DFA proof (40 ms per 4M tokens order [READ PROGRAM G-B: L2 4M tok / 40 ms]);
  per step: one weld; per run: one recursive aggregate.
- **Legs.** The absence protocol's five; plus: in the dark-data regime, the DFA runs on ciphertext — a
  DFA step is a table lookup, i.e. a crossing per byte; price that before promising it.
- **Reuses.** All of dossier 01 §1–§3 (`Deriv/*`, `MMR.lean`, `AttestedQuery.lean`, `turn-prover`).
- **Build fresh.** The weld between `ContentCommit` and the training-step input commitment.
- **Falsifier.** A step proof over batch B' while the absence proof covers batch B: refused only by the
  weld.

### C12. Verifiable RL reward computation and eval-provenance graphs

- **C12a, RL.** Statement: each policy update is C1/C2 over (rollouts, rewards, advantages), where
  rollouts are sampled with a beacon-seeded sampler fixed after the policy commitment (TOPLOC v2-style
  reproducible Gumbel noise [CLAIM, CVC atlas]), and rewards are computed by a pinned verifier program
  (unit tests, math checker) whose execution is proven or deterministically recomputable. GRPO's
  group-normalized advantage is a scalar nonlinearity per group (one crossing per group). Peigné OP-15
  recommends synchronous rule-based RL first [READ]; agree. Falsifier: a reward program whose verdict
  depends on unpinned state (time, network). In the dark setting the reward is computed on decrypted
  OUTPUTS, which are releases: each is a read-budget event of the policy's output, not of its weights.
- **C12b, eval provenance.** A DAG whose nodes are (model commitment, eval-set commitment, harness
  commitment, result) and whose edges carry proofs or audit receipts; contamination absence = eval-set
  canaries absent from every training batch on the path (C11). The statement is "this score was produced
  by this model on this eval with this harness, and no ancestor step trained on the eval". Falsifier: an
  eval-set item reachable from a training-batch commitment on the model's path.

### C13. Crossing-gated execution and the single timeline (new; P3 + P4)

- **Statement.** `NoUnsanctionedExecution`: if no party holds evaluation keys that allow depth ≥ one
  forward layer (no bootstrapping key; relin keys only up to the crossing interval), then every forward
  pass of the mind requires ≥ L quorum crossings, each bound to the quorum's hash-chained head
  `h_{k+1} = H(h_k, crossing transcript)`. `SingleTimeline`: the quorum refuses to sign two children of
  one head. Together: the host cannot fork, replay or interrogate the mind without the quorum's log
  showing it.
- **Cost.** Zero over the FHE+MPC-boundary route: the crossings already exist. The cost is a POLICY one:
  bootstrapping becomes forbidden, which closes the "fhe-bootstrap" column of the tradeoff space on
  welfare grounds, not only efficiency ones.
- **Legs.** Relin/rotation key material bounds depth only if noise budget bounds depth: proven-noise
  ceiling (`deployed_iterCeiling`) is exactly this leg at the scalar model; the ring/ct×ct version (F4)
  is needed. Quorum signing is standard threshold signatures.
- **Reuses.** `joint_beacon.rs`'s fail-closed transcript discipline, `ensure_same_set` equivocation check
  [READ]; `RecursiveAggregation.lean` anchoring (`anchored_attests_rejects_fabricated_genesis`).
- **Build fresh.** The depth-gating theorem (a ciphertext under the issued keys cannot be evaluated past
  depth k without decryption failure), and the timeline Prop.
- **Falsifier.** Issue a bootstrapping key; exhibit unbounded-depth evaluation with no crossing.
- **Prior art, honestly.** Not claimed as a first. One Kagi query (encrypted weights + quorum + prevent
  unauthorized execution) returned only weight-security guidance (RAND RRA2849-1). The idea is adjacent
  to one-time programs and to execution metering by MPC; the welfare reading (evaluation keys bound the
  mind's unsanctioned experience) I have not seen stated [INFERRED].

### C14. Seeded zeroth-order dark learning

- **Statement.** MeZO-style: `W_{t+1} = W_t − η·c_t·z_t`, `z_t = PRG(seed_t)` where seed_t is a beacon
  output revealed AFTER the batch commitment (else data can be chosen against the direction: the
  2610.27550 lower bounds apply to methods whose randomness is fixed before the function [READ abstract]),
  and `c_t = (L(W+εz) − L(W−εz))/2ε` computed from two dark forward passes.
- **Why it is interesting.** The update is (encrypted scalar) × (public vector): the public-coefficient
  corner (§1), Hole B absent, noise additive. The history is (seed, ⟦c⟧) per step: one felt of commitment.
  Poisoning per step is one-dimensional in a direction the poisoner did not choose.
- **Cost.** Two forwards per step, no backward; but ZO needs many more steps [CLAIM: MeZO reports up to
  ~12× more steps than Adam; the script charges 12×]. In the script it is dominated everywhere. The
  computed ⟦c⟧ is itself a ct×ct-depth output, and with ZO on the full parameter set the update touches
  d² slots per step.
- **Corrections (Codex round 1, accepted).** (i) The adversary chooses c AFTER seeing z, so "poisoning is
  one-dimensional" gives no displacement bound without a cap: B·sign(z₁)·z moves one coordinate by B/√P
  every step, and T steps span min(T, P) directions. (ii) A seeded dense z is not low rank: keeping only
  (seed, c) makes serving cost (T+1)·d² unless the update is materialized, which brings back dense writes
  and additive noise. (iii) Two randomness stages are needed: commit (model version, batch, loss, ε,
  generator) before the DIRECTION seed; commit c before an INDEPENDENT audit beacon — one beacon for both
  lets the host know whether it may forge c. (iv) "One encrypted scalar" is one ciphertext: 24,576
  residues / 49,152 bridged felts at deployed parameters, not one felt.
- **Verdict.** Kept as a governance-shaped construction (tiny certificates, unchosen directions) for
  small dark adapters where step count is cheap; not a frontier point [MEASURED, script].
- **Falsifier.** A seed visible before the batch commitment: the adversary picks data with
  `L(W+εz) − L(W−εz)` of its choosing.

### C15. MPC custody with publicly auditable MPC (the bandwidth route)

- **Statement.** Weights secret-shared among n servers (no FHE); every step is a SPDZ-style computation
  with MACs; public auditability via commitments to shares (BDO14-style) so that a third party checks
  the transcript, and sampling applies to the expensive auditor work, not to the MAC checks.
- **Cost.** Lowest proof felts on the frontier (public trunk), but fully dark costs a triple per
  shared×shared product: ×65 online traffic vs the public-trunk point [MEASURED, script].
- **Legs.** Tier C (all n servers read), P3 holds structurally (no single host runs anything), P4 by
  consensus among servers.
- **Reuses.** `mpc_distributed_mac.rs`, `dealerless_preprocessing.rs`, threshold ceremonies.
- **Falsifier.** A dishonest-majority deployment without MACs on linear ops.
- **Peer note.** If the quorum must be online every step anyway (it must, under P3), FHE buys host-local
  linear algebra and at-rest storage, nothing else. The program should build both and let the counts
  choose per regime, not assume FHE.

### C16. Lattice folding over the FHE ring (commit-to-the-ciphertext)

- **Statement.** Fold the training history with an Ajtai commitment over the FHE ring itself, so a
  ciphertext is directly the folded witness and the ct×ct identity is checkable at the ring's cost
  (5.5× the cost of performing it, vs ≥ 618× on the deployed route, VERDICTS §7.2 09-05 by-product
  [READ]) — with the 09-05 caveat that full ciphertext coefficients are not short (4 digits at 64 bits,
  7 at 109), so the 5.5× must state its representation.
- **Why it matters for dark learning.** The fold accumulator becomes the encrypted model; the merge (C3)
  is the decider (F9). The power-of-two ring X^N + 1 over a high-2-adic prime splits completely
  (`splits_negacyclic` [READ]), so challenge invertibility comes from LatticeFold+-style norm arguments,
  not field structure.
- **Read result: the ring is not shareable; a prime can be** [READ, crypto lane]. Ajtai/MSIS folding binds
  only SHORT witnesses (ProtogaLattice 2026/1317: ternary fresh witnesses, N = 32, 4 CRT slots; LatticeFold+
  needs low-norm extraction), while ciphertexts are uniform mod q, so a ciphertext must be gadget-decomposed
  into ~log q/log b digits and the digits are the witness. FHE wants primes that fully split X^N + 1;
  folding wants few large CRT slots (Neo 2026/242 Remark 5: full splitting leaves "only 64 bits"). Our
  36/36/37-bit NTT primes therefore disqualify the FHE ring as a folding ring. What exists is a shared
  PRIME: 2026/1127 sets the TFHE modulus equal to the LatticeFold modulus (≈ 2^64) with a different ring
  and a subring map (2^23 constraints with automorphisms, 1,469 s prover, OOM at 2^22 on 768 GB).
- **Revised statement.** Fold digit-decomposed ciphertexts over a small-degree ring sharing the custody
  prime. The "accumulator IS the encrypted model" survives only up to a digit decomposition (×4–7 felts
  per coefficient, VERDICTS §7.2 09-05), which must be in every price quoted for C16.
- **Falsifier.** The zero-absorb attack (VERDICTS §3c 09-05) at the ring instance.

### C17. TEE as a leg, never as custody; DP inside the dark step

- **C17a TEE.** A GPU confidential-compute attestation is admissible as an additional ε leg (it raises
  the cost of a host that forges proofs) and never as P1 (the vendor can read: Attestable's own argument
  [READ attestable-calibration.md]). In the script TEE rows are tier D and excluded from the frontier.
- **C17b DP.** DP-SGD inside the dark step (VeriDP: per-step clip, Box–Muller noise in-circuit, IVC;
  ResNet-18 ~86 min per 20 batches on one core [READ, lit lane]) protects data subjects AND bounds what
  any release reveals. In the dark setting the noise can be generated inside the crossing from beacon +
  quorum randomness, so nobody (host included) knows it, which plain VeriDP cannot offer. Falsifier: a
  noise seed known to the host before the step.

---

### C18. The sufficient-statistics dark learner: exact deletion by subtraction (Codex round 1, adopted)

- **Statement.** On a frozen feature map φ, keep dark statistics `A = λI + Σ φ(x)φ(x)ᵀ`, `b = Σ φ(x)y`; the
  released model solves `Aw = b`. Insertions and deletions are additions/subtractions of the record's
  contribution, so deletion is exact against the comparator "the same learner on D \ {d}". Prove: the
  statistics equal those of the committed active multiset (membership, multiplicity), and the released w
  solves the specified regularized system (exact field semantics need invertibility; real semantics need a
  specified solver).
- **Cost.** Per insertion/deletion d(d+1)/2 + d products (2,144 at d = 64); checking a proposed solution
  Aw = b is d² mults (4,096 at d = 64); the O(d³) solve runs per release, not per record [DERIVED, Codex].
- **Where it sits.** If φ is public and the record is the host's, every update is in the public-coefficient
  corner (§1): `step_noise_le` applies, Hole B is absent. This is the general form of the FIFO-expiry
  learner already running in `research/vfhe_2026_09_08/` (C10b), and of `convex_step.rs`.
- **Falsifier.** Delete a duplicated record once; change φ after accumulation; supply a singular or
  wrapped system that passes.

### C19. A fixed public subspace instead of a growing factor history (Codex round 1, adopted)

- **Statement.** `W = W₀ + U C Vᵀ`, U, V public d×r, only the r×r core C dark and mutable. The coefficient
  gradient is `(Uᵀδ)(Vᵀx)ᵀ`: two PUBLIC projections then r² secret products. Prove each update is the
  prescribed projected-gradient transition in C with its rounding.
- **Cost.** Adapter evaluation 2dr + r² scalar mults (131,328 at d = 4096, r = 16); 256 mutable scalars vs
  C4's 131,072 appended factor entries per step (512×); no merge schedule [DERIVED, Codex].
- **Why it matters here.** It moves most of the adapter work into the public-coefficient corner and bounds
  the dark state forever, which also bounds the read budget per release and makes C10-style deletion a
  question about one r×r matrix. It composes with C3 (the "adapter" is C) and C13.
- **Falsifier.** A task whose useful gradient is orthogonal to span(U)⊗span(V): the cryptography works
  and learning stalls. Capacity is the honest limit.

### C20. Proof-gated activation of epochs (Codex round 1, adopted; composes with C2 and C13)

- **Statement.** Training may run speculatively under sampled audits (C2), but no model version becomes
  ACTIVE (serves outputs, takes reward-dependent actions, receives partial decryptions for release) until a
  proof covers the whole epoch from the last certified checkpoint. "Expected damage before detection"
  (C2) becomes "no unproved model is ever active"; sampling is an early-warning system, not the safety
  argument.
- **Cost.** Total proving work is not reduced (E·G gate work per epoch); verification and activation happen
  once per epoch. Latency is the price.
- **Composition with C13.** The quorum is the activation authority: it refuses release crossings for any
  head not covered by an epoch proof, which turns P4's timeline into a timeline of CERTIFIED states.
- **Falsifier.** Obtain one inference result, reward-dependent action or partial decryption from a
  speculative descendant; or activate a valid proof against a stale parent.

## 5. Theorem targets (Lean-shaped, ordered by what they unblock)

| target | file it lands near | unblocks | falsifier |
|---|---|---|---|
| `iter_decrypts_exact_no_wrap` (F1) | `Bfv/Noise.lean` | every iterative claim | `stepMatrix 16 1 A` at T = 3 |
| `appendOnly_noise_history_free` (F4) | `Bfv/Ring.lean` + `Mul.lean` | C4 | homomorphic δ chain at s = 2 |
| `stepRR_noise_le` ring ct×ct (F4) | `Bfv/Ring.lean` | C1, C13 | `N−1` expansion refuted (exists) |
| `displacement_bound` + EnvelopeLeg (F7) | `Selvage/AuditSampling.lean` | C2, C5 | drop the envelope |
| `bisect_localizes` (F7) | new | C2 recovery | uncommitted intermediate state |
| `merge_discharges_carried_witness` (F9) | `Selvage/AccRbrFold*` | C3, C16 | zero-absorb at the merge |
| proof-gated CPA-D reduction (C8) | `Bfv/Smudging.lean` | G4 | ungated over-budget query |
| `noUnsanctionedExecution` (C13) | new | P3 | issued bootstrapping key |
| `BFVScaleLiftRefinement` (VERDICTS §7.5) | `Bfv/CrossLimb.lean` | C1, C9 | 1-vs-32 pair |
| derivative column of the forward table (F2) | lookup layer | C1 backward | the 412 GELU codes |
| `F_dark` ideal functionality + simulation (F14) | new | every confidentiality claim | identity circuit as an "allowed" release |
| reference integer learner + refinement (F15) | new | all of C1–C4, C18–C20 | an implementation step the spec cannot express |

## 6. Experiments, in the order I would run them

1. **[ran, Mac] bf16 derivative virtualization** — refuted for sigmoid/tanh/GELU/SiLU (F2). Done.
2. **[ran, Mac] construction-space counts** — `tradeoff_space.py`; deployed point fails PQ and read
   budget; frontier = public-trunk low-rank (§3). Done; constants named.
3. **[hbox, first] Calibrate the two constants that carry the frontier**: (a) committed felts of one
   ct×ct with the integer certificate at p61-native and at RNS-202@8192 (prediction 159,744 and
   1,056,768); (b) online elements of one fused σ/σ' crossing of an N = 8192 ciphertext through the
   existing threshold path. Run as `swarm-build cargo run --release --bin <new counter>` with a counting
   harness in `fhegg-fhe` (counts, no clock; same discipline as `low_rank_commit_cost.rs`). These two
   numbers move the FHE-vs-MPC fork in §3 more than anything else.
4. **[hbox] One complete small dark transition, both proving routes (F13)** — ciphertext-trace proving by
   the host vs distributed plaintext proving by the quorum inside the crossing, on a d = 64 two-layer
   learner, attacked with wrong δ, mixed limbs, unrelated boundary shares, wrong quotient, stale parent,
   missing audit response. This replaces every extrapolation of the rank-1 saving to the dark setting.
5. **[Mac, Lean] F1's message ledger** — `decide` the first failing T for den ∈ {2,4,16}.
6. **[hbox] Integer-recipe accuracy** — a 4-bit factor-quantized SGD fine-tune of a small public-trunk
   adapter in plaintext integers (no FHE), to learn whether F1's recipe trains at all. This is the ML
   question everything rests on and it needs no cryptography to answer.
7. **[design only] C16 read** — LatticeFold+/ProtogaLattice ring choice against X^8192 + 1 at the custody
   modulus; one note, no build.

Do not run heavy FHE benchmarks on this Mac.

## 7. What I changed my mind about while writing this

- Codex round 1 found the gap I had not seen (F13): the host cannot run the cheap plaintext proofs
  because it does not hold the witness. The rank-1/low-rank theorems pay inside the QUORUM's crossing, not
  at the host. That moves the natural place to prove a dark step into the MPC boundary.

- I started by ranking bootstrapping-avoidance as an efficiency goal; P3 made it a welfare requirement.
- I expected the append-only learner to be the frontier; the counts say it saves depth, not work, and is
  dominated once the merge is charged.
- I expected FHE to dominate MPC for dark weights; the counts say they trade proofs for bandwidth and the
  public-trunk regime favours MPC. That is a model result with named constants, and experiment 3 is
  designed to overturn it if it is wrong.
