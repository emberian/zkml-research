# Dark learning: where our foundations are weak or wrong, refute-then-repair

2026-11-05. Companion to `docs/DARK-LEARNING-PROGRAM.md`. Each item names the weakness, gives the
evidence (tagged [READ] / [MEASURED] / [DERIVED] / [CLAIM] / [INFERRED]), and then gives either the
repaired statement or the experiment that settles it. Items are ordered by how much of the dark-learning
program each one blocks. Nothing here is softened. Where an item contradicts one of our own docs, the doc
and line are named so the next reader can fix it.

**Read F13 first.** It was found by Codex in round 1, after F1–F12 were written, and it blocks more than
any of them: the host holding ciphertexts cannot run the cheap plaintext proofs our training theorems
describe. F11 was revised after Codex round 2 refuted my first version of it.

Scripts referenced: `notes/dark-learning-scripts/tradeoff_space.py` (construction-space counts),
`notes/dark-learning-scripts/backward_table_virtualization.py` (bf16 count, run on this Mac, < 2 s).

---

## F1. The plaintext-precision wall: BFV cannot rescale, and training is a long iteration.

⚠ Astra DL31 (accepted): "nobody wrote this down" was wrong — `Bfv/Noise.lean:490` (`iter_decrypts_exact`)
already carries the message bound `m_i < t` for the UNSIGNED decode. What is missing is the SIGNED bridge:
a symmetric range on signed messages does not make the unsigned decode return negatives. The repair below
is therefore a signed-decoding theorem plus the iteration-specific ledger, not a first statement of the wall.

**Weakness.** Every dark-training note prices NOISE depth. None prices PLAINTEXT growth. BFV has no
rescale: a product of two plaintexts lives at the product's scale until a rounding nonlinearity brings it
back, and `Bfv/Mul.lean` already proves the one-multiply version of this wall [READ `Bfv/Mul.lean:1-20`]:
the safe per-operand cap for one multiply at t = 1,032,193 is 1015 (`product_capacity_tight`), and
`NoWrap.lean` gives inner dimension 512 at 4-bit by 8-bit [READ fhe-core-theory.md]. A training run is
millions of iterations. Two consequences [DERIVED]:

1. **A fractional SGD learning rate wraps unless a rounding crossing intervenes.** (Narrowed after Codex
   round 1: in a scale-carrying representation w_k = a_k/den^k only the NUMERATOR can wrap, and a pure
   contraction w ← w/2 keeps a_k = 1 forever; integer-grid optimizers and exactly divisible updates also
   escape. What wraps is SGD with non-divisible updates, where a_{k+1} = den·a_k − num·den^k·g_k grows ×den
   per step. Modular inversion is not fixed-point division: 2^-1 mod t = 516,097, centred −516,096.) `x <- x - (num/den)·g` in
   integers multiplies the state scale by `den` every step. With 8-bit weights and t ≈ 2^20, the state
   wraps after `floor((19 - 8)/log2 den)` steps: 2 steps at den = 16. `Noise.lean`'s
   `iterGrowth tauDen tauNum normA` and `deployed_iterCeiling = 42` track the NOISE of exactly this
   iteration and say nothing about the message, which lives in ℤ (`iterMsg`) and is read mod t. The
   42-step ceiling is a noise statement about an iteration whose plaintext has wrapped long before step 42
   for any `tauDen > 1` [DERIVED; the Lean is correct about what it states, and what it states is not the
   binding constraint].
2. **Integer (factor-quantized) updates move the wall to a count.** If the update is `W -= δ̃ ⊗ x̃` with
   integer factors, the accumulated weight stays below t/2 for `((t−1)/2 − |w₀|)/max|δ̃_i x̃_j|` steps:
   ~2,047 steps with unsigned 4-bit factors (products ≤ 2^8), 10,532 with signed 4-bit (|·| ≤ 7, products
   ≤ 49) [DERIVED, `tradeoff_space.py` v2 prints the signed case]. Every merge/refresh period must sit below
   that, and every dot product must clear the signed window `inner·|w|·|a| ≤ (t−1)/2`
   (`bfv_coeff_matmul.rs:45-108` [READ via Codex]): 504 at signed 4×8-bit, 10,532 at signed 4×4-bit. A
   longer dot product split into safe pieces is NOT wrap-free when the pieces are added in BFV; they must be
   summed outside (a crossing per piece) or the operand ranges reduced (Codex round 2).

**Repair (statement).** One theorem that carries BOTH ledgers, so neither can be quoted alone:

```
iter_decrypts_exact_no_wrap :
  RowBound S G → (noise ledger) G^T·B_fresh·... < margin →
  (message ledger) ‖iterMsg S T m‖_∞ < t/2 →
  decrypt (iterCt S T x) = iterMsg S T m        -- in ℤ, not mod t
```

and its falsifier: the deployed `stepMatrix 16 1 A` at T = 3 (noise margin holds, message wraps, decrypt
returns the wrong integer). **Experiment (Mac, minutes, no FHE):** extend `Noise.lean`'s
`deployed_iterMargin_*` family with the message-side ceiling and `decide` the T at which each fails first,
for den ∈ {2, 4, 16} and weight widths {4, 8}. Expected: the message side binds first at every den ≥ 2.

**Consequence for the program** (stated for SGD-like optimizers with non-divisible updates; the general
claim "every long run needs a crossing per step" is withdrawn). The per-step rounding nonlinearity is not
an optional MPC hop, it is the
requantization that inference already pays 25–34% of its prover cost for [READ AGENDA Pillar I], now
paid once per step on the weights' update path. Training in BFV is "depth 2 between crossings" by
necessity, and the crossing count is the true unit of cost (§2 of the program).

## F2. "The backward table is virtualized off the forward one" is FALSE in the format we prove, for every activation except ReLU.

**Weakness.** `docs/DARK-TRAINING.md` §1 (⚑ bullet 3) claims σ' is a function of σ, so one 2^16 table
serves both directions. Over the reals this fails for GELU and SiLU (non-monotone). Over bf16 it fails for
sigmoid and tanh too, because saturation and rounding merge inputs whose derivatives differ.

**Evidence [MEASURED, `backward_table_virtualization.py`, all 65,280 finite bf16 inputs, exact real
function rounded once to bf16]:**

| activation | output codes | codes with >1 bf16 derivative | inputs affected | max derivative gap |
|---|---:|---:|---:|---:|
| relu | 32,641 | 0 | 0 | 0 |
| sigmoid | 1,069 | 148 | 16,798 | 0.0038 |
| tanh | 32,498 | 190 | 32,930 | 0.0075 |
| gelu | 48,366 | 412 | 17,008 | 0.514 |
| silu | 48,464 | 751 | 17,243 | 0.501 |

Corroboration from outside [READ, lit lane]: Peigné et al. 2606.05433 v3 App. C.1 and VeriLoRA (NDSS'26)
both use a SEPARATE derivative table; neither claims the virtualization.

**Repair.** What survives is weaker and still useful: the backward lookup is keyed on the INPUT code,
which the forward lookup already committed as its address, so the derivative is **one extra column of the
same table**, not a second table and not a second address commitment. Statement:
`lookup (x ↦ (σ x, σ' x))` with one LogUp multiplicity column shared by both reads. Cost: +1 committed
table column (2^16 felts, once), +0 per-element address commitments. In the dark (MPC-boundary)
construction the crossing has x in shares anyway and outputs both values; nothing is lost. Edit
`DARK-TRAINING.md` §1 accordingly.

## F3. FRONTIER-QUEUE G1 says single-prime "dissolves both holes". Our own VERDICTS says otherwise for Hole B. G1 is stale.

**Weakness.** `docs/FRONTIER-QUEUE.md` G1 (and the ⚑ REFINED block under it) says single-prime dissolves
provenance AND expressibility. `docs/VERDICTS.md` §7.5, 09-05 addendum, shows the rescale certificate is
over the INTEGERS: `round(t(z+Q)/Q) = round(tz/Q) + t`, so the scaled product does not factor through
`z mod Q`, and proving `c_raw = a·b` in R_Q proves nothing about the BFV product [READ]. A single prime
removes limbs, so Hole A (provenance) goes; Hole B (expressibility) needs `z` over ℤ whatever the modulus.

**Evidence [DERIVED, `tradeoff_space.py` G1 block]:** the lifted coefficient `|t·z|` is about
2^(log N + 2 log Q + 1 + log t):

| modulus | proof field | |t·z| | integer limbs | certificate felts / ct×ct | felts / ct |
|---|---|---:|---:|---:|---:|
| RNS3-109 @ 4096 (deployed) | BabyBear | 2^251 | 9 | 307,200 | 49,152 |
| p61 @ 4096 | BabyBear | 2^155 | 6 | 196,608 | 24,576 |
| p61 @ 4096 | native p61 | 2^155 | 3 | 159,744 | 8,192 |
| RNS-202 @ 8192 | BabyBear | 2^438 | 15 | 1,056,768 | 196,608 |

Outside corroboration [READ, crypto lane]: Zama 2026/027 and 2026/1127 both run a single ≈2^64 prime as
FHE modulus and proof (or folding) field, and both avoid ct×ct entirely. PRISM (2026/1956) closes the RNS
version of Hole A with an auxiliary prime above m·max p_i² carrying the canonical integer lift — prior art
our `cross-limb-binding.md` does not cite and should.

So G1's real prize is the **6× cut in felts per ciphertext** (native single-prime) and the deletion of
Hole A, not Hole B. The ct×ct certificate dominates the per-ciphertext cost at every row (3–20× the
ciphertext itself). **Repair:** rewrite G1 as "single-prime deletes Hole A and the bridge, and leaves
`BFVScaleLiftRefinement` (VERDICTS §7.5) as a 3-limb non-native certificate over a 61-bit proof field".
**Settling experiment (hbox, swarm-build, a day):** implement the integer quotient–remainder certificate
for one ct×ct at p61 in the matvecmul-p61 tree (`~/src/matvecmul-p61`, the p61 swap already ran
2026-08-13) and count committed felts against the 159,744 predicted; falsifier: the 1-vs-32 pair (Q = 31,
t = 4) bound only mod Q must be refused.

## F4. Our noise model covers the public-coefficient corner and nothing else that training needs.

**Weakness [READ].** `Bfv/Ring.lean` lifted `matVecCt`/`RowBound`/`step_noise_le` to the ring verbatim, and
those are the right theorems for ct×pt with a PUBLIC integer matrix. Training's update coefficients are
themselves encrypted (δ, x come from the dark forward pass), so the iteration is ct×ct, and:
- `Bfv/Mul.lean` is the scalar model; its own header lists the ring lift for ct×ct as missing and says the
  mod-q correspondence does not carry over from addition (centred representatives needed) [READ
  `Mul.lean:20-40`]. Relinearization noise `B_ks` is a hypothesis.
- `B_fresh` is an assumption in `Noise.lean` [READ header], and the Lean `encrypt` is the pre-KPZ
  `Δ·m + e`, which reads a real fresh deployed ciphertext at 20 bits, not 4 [READ
  kpz-noop-and-the-model-gap.md]: harmless for the bound, wrong for pricing.
- Nothing models the TFHE/PBS or MPC crossing as a noise RESET.

**Repair (statement).** The append-only learner (program §C1) needs exactly two new theorems, both small:
1. `stepRR_noise_le` — ct×ct over `RCt` with `negaMul` and a relin term: the ring version of
   `mul_relin_noise_le`, carrying `δ_R = N` (proved tight already, `negaMul_expansion_attained`).
2. `appendOnly_noise_history_free` — for a forward pass `W₀v + Σ_s δ_s (x_s·v)` where every `δ_s, x_s` is
   a fresh ciphertext (bound `B_fresh`) and `v` is fresh, the output noise bound is independent of the
   history length T except through the ADDITIVE sum over s: `T·N·(2 B_fresh t)` — linear in T, never
   exponential. Falsifier: the same chain with δ_s computed homomorphically from δ_{s-1} (no crossing)
   exceeds the margin at s = 2 at deployed parameters.
**Experiment (Mac, minutes):** state 2 in Lean over the scalar model first (it is `abs_sum_le_length_mul`
plus `mul_relin_noise_le`), then lift.

## F5. The read budget: our smudging bound makes a long dark run leak, and that forces N = 8192 for a reason nobody gave.

**Weakness [READ fhe-core-theory.md security ledger 2].** The smudging theorem is scalar against a
per-party polynomial transcript; the shipped 2^-48 becomes 2^-32 per session after the union factor, and
is vacuous at ~2^32 sessions. (fhe-core-theory.md also records that a statistical 80-bit smudge wants
log q ≥ 138; Codex round 2 showed the right object is the E/S ledger below, not a log Q threshold.)

**Evidence [DERIVED, `tradeoff_space.py` v2 read gate; v1's step function withdrawn after Codex round
2].** The ledger is `ε_run ≤ Σ_events Σ_exposed-shares ε_scalar` with `ε_scalar ≈ E/S` and `E + nS` below
the margin Q/(2t); it is not a function of log Q alone, and E = 2^32 (the window `Smudging.lean:330-376`
proves) is a FOLD envelope, not established for training ct×ct outputs. With that E, n = 3, a dark step at
d = 4096, L = 32 makes ≥ 2L·⌈d/N⌉ = 64 crossing events (more when split dot products must be summed outside
BFV); over 10^6 steps the deployed modulus gives **2^-14.2** — failing a 2^-40 target — while RNS-202@8192
gives ~2^-106 and a 61-bit modulus cannot fit the smudge at all (2^+7.6 per event). 280 of 336 FHE+MPC rows
fail. Codex's caution, accepted: a loose union bound failing the target shows our CONFIDENTIALITY PROOF
fails, not that the run leaks that much.

**Repair.** (a) The read budget is a first-class ledger carried beside the audit `q`, with E, S, n and the
event count supplied per construction. (b) A long run forces a modulus with room for E + nS under the
margin; with the quantum-128 table (F6) that points at N = 8192 and log Q in the 140–202 range.
**FRONTIER-QUEUE G2 is decided by the read budget before it is decided by depth.** (c) The
polynomial-transcript smudging theorem (`TranscriptHybridLedger`, undischarged) is on the critical path.

## F6. PQ: the deployed point is a classical-only point, and a long-lived mind is exactly the harvest-now-decrypt-later target.

**Weakness [READ VERDICTS §7.8].** (N = 4096, log q = 109, t = 2^20) is a classical-line set; Apple ships
N = 4096 at 83 bits for `.quantum128` and N = 8192 / 148 bits at log t ≈ 20. Our script uses quantum-128
ceilings of 101 (N = 4096) and 202 (N = 8192) [CLAIM, HE-standard table, from memory; verify]. On either
source the deployed set misses PQ-128. For inference this is a confidentiality question with a short
shelf life. For a mind whose weights are encrypted for years, ciphertexts recorded today are read by
whoever has a quantum computer later; that is a welfare event, not a data leak.
**Repair.** Make PQ a hard gate on every dark-learning construction (`tradeoff_space.py` does). With F5,
the surviving FHE moduli are N = 8192 with log q large enough for E + nS under the margin and ≤ 202; the
script's RNS-202@8192 row is the only FHE row that passes all four gates, conditionally (ternary-secret
table, HE Standard v1.1 p.31, located by Codex round 2).

## F7. The audit theorem counts corrupt ROUNDS; training damage is displacement, it compounds, and the auditor may not decrypt.

**Weakness [READ `Selvage/AuditSampling.lean` §2–§4].** `sequential_bound` bounds `E[C_τ] ≤ 1/q` and
`leakage_bound` multiplies by a per-round payload cap `b`. For training, three things differ:
1. The quantity that matters is how far a poisoner moves the weights. That is `leakage_bound` with
   `b = B`, the per-step injected-displacement cap, **only if B is enforced on every step**, not sampled.
   A sampled cap is no cap.
2. A corrupt step's effect persists and is amplified by later honest steps (training dynamics are not
   contractive in general). The theorem bounds INJECTED displacement, not final distance. Any sentence of
   the form "the poisoner can move the model at most B/q" is wrong unless "injected" is in it.
3. The checker for a dark step cannot be "decrypt and recompute" (that is a quorum read per audit, F5).
   So `ε_chk` must be the soundness of a proof over ciphertexts (SNARK-over-FHE, VERDICTS §3), which
   inherits F3's certificate cost.
4. CPA-D legs cannot be sampled [READ, crypto lane: 2026/285 Thm 3 needs per-ciphertext hygiene; 2026/203
   Prop 11; 2026/2546]. One unhygienic ciphertext admitted to a decryption is key information. The audit
   theorem is an integrity theorem; it must never be cited for confidentiality.
5. Detection does not localize: after an alarm the last trustworthy state is unknown unless intermediate
   states are committed and bisectable.

**Repair (statements).**
- `displacement_bound`: with `EnvelopeLeg` (every step proves ‖Δ_t‖ ≤ B, unconditionally) and the three
  audit legs, `E[Σ_{t<τ} ‖Δ_t − Δ_t^honest‖] ≤ 2B/q`. This is `leakage_bound` at `b = 2B` (triangle
  inequality on a capped honest and a capped dishonest delta). Falsifier: drop `EnvelopeLeg` and exhibit
  one corrupt step with unbounded displacement passing every sampled check with probability 1 − p.
- ~~`bisect_localizes`~~ ⚠ withdrawn (Astra DL03): local step validity is not monotone; replace with
  bisection on PrefixValid(k) := ∀ i < k, ValidTransition(committed_i, committed_{i+1}, prescribed_input_i)
  (fixed genesis, authenticated boundaries, prescribed randomness). "Does honest replay reach the
  committed W_t?" is NOT a repair: endpoint equality is also non-monotone (honest 0,0,0 vs committed 0,1,0
  gives [True, False, True]; Astra experiment-1 audit). Each prefix query proves every transition in the
  prefix or carries a recursive prefix certificate. Original text: if every step's boundary (W_t commitment or appended factor) is committed, then after
  an alarm the first corrupt step is found with ⌈log₂ T⌉ step proofs (refereed-delegation shape; Verde
  bisects to one operation [READ lit lane: CVC atlas]).
- Keep amplification as a separate named residual `[TRAIN-amplify]`, never folded in.

## F8. The rank-1 "zero rounds" is per sample; batches are rank B; and the float objection must be answered by declaring integer semantics.

**Weakness [READ VERDICTS §5b; lit lane].** `sgd_step_sound` certifies a step whose gradient is one outer
product. A batch of B samples gives rank ≤ B: `ΔXᵀ` with MLE `Σ_b δ̂_b(r_row) x̂_b(r_col)`, which is
`rankK_sound` (B openings, bound flat in B) or a log B-round sumcheck (one-commitment design, +κ·3/|F|,
`low-rank-updates.md`). DARK-TRAINING §1's "you check it in O(n)" is O(nB). And Peigné v3 rejects exact
Freivalds for training because float addition is non-associative (§D.2.2, OP-1) [READ].
**Repair.** (a) State the batch form as the headline (`rankK_sound` at K = B). (b) In the DARK setting the
float objection dissolves by construction: the substrate computes in Z_t; the integer program IS the
training run, and there is no float run for the proof to disagree with. Say so; it is a real advantage of
dark learning over Peigné-style plaintext audits, not a dodge. The cost is that the training recipe must
be integer (factor-quantized, F1), and its accuracy is an ML question we have not measured.

## F9. Folding a training history: the single-transcript fold extractor is vacuous, so "IVC over training where the accumulator is the model" needs the carried-witness form.

**Weakness [READ VERDICTS §3c, 09-05].** `FoldRoundBound … extractFn ε` is false for every extractor
below ε = 1 (zero-absorb attack); the four extractor-parametric callers are vacuous at any binding
instance. The repaired carried-witness reduction has error 0 but the decider checks T+1 openings, and
capacity halves to T ≤ 2^46 − 1.
**Repair.** For a training chain of 10^6–10^9 steps the decider's T+1 openings are the cost. Pair it with
the merge rule: every merge (T = d/(2r) steps, `low-rank-updates.md`) is a decider point that discharges
the carried openings and restarts the accumulator from a recommitted W. The merge is then both the
serving optimization and the knowledge-soundness checkpoint: one event, two jobs. State it as
`merge_discharges_carried_witness`.

## F10. Soundness numbers in dark-learning sketches are aspirations until the PCS regime is pinned.

**Weakness [READ VERDICTS §2].** The deployed FRI reads UDR 34 / JBR 73 bits; "never quote 130". The
rank-1 and low-rank bounds are 2^-26 per base-field point and need Ext4 for ~116 bits. The 2025 FRI
commit bound's citation chain ends in a vendor whitepaper appendix (2026/532 Thm 28/29) [READ
proximity-delta-2026-09-04.md]. The tradeoff script uses ε_chk = 2^-100 as a MODEL constant.
**Repair.** Every dark-learning soundness claim names its regime (UDR/JBR) in the claim. ε_chk in the
audit composition is instantiated from the PCS actually used, and at UDR today it is 2^-34: at p = 0.01
that is still q ≈ 0.0095 (the checker error is not what binds; the audit rate is).

## F11. Custody: tier C, static, and it cannot deliver "no unsanctioned execution" (revised after Codex round 2)

**Weakness [READ DARK-TRAINING §6 2026-09-06 block; pre-constrained-encryption-read.md].** Threshold
custody is tier C: the full quorum reads; credential absence with closure is iO-strength (for GENERAL
constraint classes — not an impossibility for every restricted learn/infer functionality, F14).
**What I claimed first, now refuted.** That per-step crossings gate execution, so withholding
bootstrapping keys gives `NoUnsanctionedExecution`. Codex round 2 [accepted]: a noise upper bound never
implies incapability; relin keys are reusable; Enc(W)·x for chosen public x is ct×pt; shallow fragments on
copied ciphertexts are unbounded in number. A host holding Enc(W) and evaluation keys can always compute
model-dependent fragments of its choosing.
**Repair.** (i) State `NoUnauthorizedService` (program C13) and a `SingleTimeline` with quorum intersection
and durable anti-equivocation; (ii) real "no unsanctioned execution" requires that no reusable evaluation
object for the mind exists outside custody: instance-bound delegated transitions with the reusable model
in MPC (program C21); (iii) tier C is static; the long-lived threat is temporal, answered by
forward-secure epoch custody (program C22). The welfare reading of the custody fork therefore leans to
MPC, independently of cost.

## F12. Gauge freedom means norms of A or B alone are meaningless; caps must be on the product (sound direction only).

**Weakness [READ low-rank-updates.md §4, `lowRankUpdate_gauge`].** (A,B) is bound only up to GL_r. A
drift cap on ‖A‖ alone is not a cap.
**Repair.** Cap `‖A‖_F·‖B‖_F ≤ B` (implies ‖AB‖_F ≤ B: sound, conservative under gauge), or for rank r the
sufficient `Σ_k ‖a_k‖₂‖b_k‖₂ ≤ B` at O(rd) arithmetic. ~~Power-iteration operator-norm certificate~~ —
withdrawn: an exhibited direction gives a LOWER bound on the operator norm, not an upper one (Codex round
2); an upper spectral certificate needs more machinery. And for a mutable adapter the envelope must bound
`Δ(AB) = ΔA·B + A·ΔB + ΔA·ΔB`, not the committed factors (Codex round 2). State the envelope over the
product, never a factor.

## F13. Witness custody: nobody who can run the cheap plaintext proofs is allowed to (Codex round 1; the largest gap)

**Weakness.** `rank1_sound`, `sgd_step_sound`, `lowRank_sound` are proofs a prover runs with the plaintext
δ, x, A, B as witness. In dark learning the host holds only ciphertexts. It can prove ciphertext
arithmetic from a ciphertext trace (SNARK-over-FHE, C1), and that proof is priced by F3's certificates,
not by the 7×10^4× rank-1 saving. The rank-1 saving is available only to a party that knows the
plaintext, i.e. the quorum acting jointly. "~3% ZK overhead" (VEIL-class) is for a prover that HAS the
witness; it does not solve distributed witness custody [Codex round 1, accepted; I had missed this].
**Repair.** Two explicit routes, priced separately, never mixed in one sentence:
(a) **ciphertext-trace proving** by the host (cost: F3 per ct×ct, plus noise certificates);
(b) **distributed plaintext proving** by the quorum inside the crossing — a collaborative/MPC-in-the-head
proof over secret-shared witnesses, where the rank-1 check costs O(d) shared openings. Route (b) is where
the rank-1 and low-rank theorems actually pay, and it makes the crossing the natural place to prove the
step. **Experiment:** one small complete dark training transition with a real verifier on each route,
attacked with: wrong δ, mixed source limbs, unrelated boundary shares, wrong quotient, stale parent,
missing audit response (Codex's list, adopted verbatim).

## F14. The custody/release game is weaker than the program's language

**Weakness [READ `Bfv/Smudging.lean:442`, via Codex].** `TranscriptHybridLedger` takes its hybrid bounds as
hypotheses. "Below threshold cannot read", "the full quorum can read", "permitted outputs leak only f",
and "the host cannot advance an unauthorized history" are four statements; none follows from a scalar
smudging inequality. An ALLOWED identity circuit reveals the weights perfectly with no decryption failure,
so IND-CPA-D (C8) is not model confidentiality. Also: the pre-constrained-encryption lower bound is for
general constraint classes and must not be quoted as an impossibility for every restricted learn/infer
functionality.
**Repair.** One stateful ideal functionality `F_dark` with corruption, release (policy-restricted), rollback,
abort and refresh; prove the masked threshold/MPC transcript simulates it; instantiate the hybrid ledger
from the protocol with the real count `K·m·n·N·2^-48` (K crossings, m ciphertexts per crossing, n party
polynomials; ≈ 2.3×10^-4 at K = 10^6, m = 1, n = 16, N = 4096 — the per-session 2^-32 of F5 is this ledger at
n·N = 2^16). Until then every confidentiality claim is labelled conditional.

## F15. No single executable numerical and learning specification ties the claims together

**Weakness [Codex round 1].** The public-linear noise theorem, the rank-1 field theorem, the measured depth
and `convex_step.rs` are about different operations and representations. Prose shortcuts fail as
general statements: "t = 2^20 binds polynomial nonlinearity to degree ≤ 2" (VERDICTS §3) holds for 8-bit
full-range inputs and is input-domain dependent; "no range checks" for a field-linear update does not
establish integer correctness.
**Repair.** A reference integer learner (exact scales, signed ranges, rounding, clipping, derivative
convention keyed on the pre-activation per F2, optimizer state, randomness consumption), a refinement
proof from the encrypted implementation to it, and learning utility established separately. First
milestone: a complete multi-step trajectory whose arithmetic, confidentiality, provenance and learning all
refer to the same machine. Codex independently found F2's GELU case by hand (outputs ≈ −0.15 at x ≈ −1.0926
and x ≈ −0.4699 with derivatives of opposite sign), corroborating the bf16 count.

---

## What I did NOT find wrong

- The ring lift of `step_noise_le` is genuinely verbatim and correct for its corner [READ].
- The audit theorem's legs, fail-closed tooth and beacon tooth are right; the issues above are about what
  quantity training needs, not about the proof [READ].
- `lowRank_delta_is_the_matmul_output` and the break-even T = d/(2r) stand; F9 gives the merge a second
  job.
