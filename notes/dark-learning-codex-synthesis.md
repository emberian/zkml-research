# Dark learning: two Codex (GPT-6 Astra) reads, and my adjudication

2026-11-05. Model `gpt-6-astra` via `codex exec --sandbox read-only`, run from this repo so it read the
files itself. Prompts: round 1 attacked my eight candidate constructions and asked for new ones and
foundation weaknesses; round 2 attacked the written program, the critique and the tradeoff script.
Verbatim final answers: `notes/dark-learning-scripts/codex-round1-answer.txt`,
`notes/dark-learning-scripts/codex-round2-answer.txt` (the raw transcripts, which include every file it
read, are not committed). Session ids are in the raw headers (round 1: `01a1af03-5ddf-7860-bc1e-4bb644dcc3f4`, round 2: `01a1af11-84e7-7b33-9614-434b5e617d16`).

Adjudication key: **ACCEPTED** (changed the docs), **NARROWED** (accepted in part, the rest argued),
**REFUTED** (kept my version, with the reason), **ADOPTED** (a new construction taken into the program).

---

## Round 1 — attack on C1–C8, new constructions, foundations

| item | Codex said | verdict | what changed |
|---|---|---|---|
| C1 append-only | fresh factors stop depth growth, not forward-sum noise: worst case E_base + T·r·E, up to 11 bits at T = 128, r = 16; merge refreshes nothing; T = d/(2r) is a storage equality, not an optimum; Z_t is not BabyBear (1000·2000 mod t = 967,807), so `rank1_sound` needs no-wrap or an F_t proof (24/t ≈ 2^-15.4); **the host cannot produce the plaintext rank-1 openings** | ACCEPTED | program C4 corrections; new F13 (witness custody) — the most important thing either round found |
| C2 envelope + sample | a cap on the submitted update is not a cap on deviation: 2B for capped honest, B only if ‖u−u*‖ ≤ B is itself certified; linear authenticators do not restrict which combination the host requests unless coefficients, sources, version and label are bound; envelope proofs have soundness error too; authorized-data poisoning is not a corrupt round | ACCEPTED (my draft already had 2B) | C2/F7 wording; authenticator binding requirement noted |
| C3 proof-gated CPA-D | real as a restricted-oracle theorem ("simulation of a proof-gated, policy-restricted threshold release interface"); five missing premises (whole-derivation binding, fresh/eval-key noise justification, refinement of scaling/relin, smudging and combination coefficients in the margin, every party enforcing the gate); small noise relative to SOME plaintext is not enough, it must be the prescribed result; an allowed identity circuit reveals the weights | ACCEPTED | C8 rewritten around 2026/203 + 2026/2546; F14 (ideal functionality) |
| C4 seeded ZO | adversary picks c after seeing z (B/√P per coordinate per step); dense z is not low rank, serving (T+1)d²; two beacons needed; one encrypted scalar is one ciphertext (49,152 felts) | ACCEPTED | C14 corrections; ZO stays off the frontier |
| C5 segment provenance | shared endpoint commitment necessary, not sufficient: the conversion relation Decode(c_in) = Reconstruct(s_in) … must be a proved segment; min_j q_j conservative only if every corruption lands in a covered type | ACCEPTED | C7 correction block |
| C6 single prime | agrees Hole B survives; limb counts are capacity counts, not lower bounds; **p61's 3-adic inertia is about Φ_{3^k}, irrelevant to X^N + 1, which splits over p61** | ACCEPTED | C9 corrected; F3 already framed counts as a model |
| C7 adapter shards | dropping a shard ≠ retraining without a datum (scalar {1,0} counterexample); rename "certified shard withdrawal" | NARROWED | my C10a already retrained the affected shard; I added the comparator, the independence list, and the rename for drop-only |
| C8 precision wall | the "every long run needs a crossing per step" claim is too strong: scale-carrying numerators, pure contractions (w/2 keeps a_k = 1), integer-grid optimizers escape; modular inversion is not division | NARROWED | F1 restated for SGD with non-divisible updates; the general claim withdrawn |

**New constructions (round 1):**
1. MPC-mutable learner with BFV snapshots — already C15; ADOPTED the snapshot-export framing and the
   cost line (3d² secret mults per layer per example = 50,331,648 at d = 4096).
2. Subtractable sufficient statistics — ADOPTED as C18. It is the general form of our own running FIFO
   learner, which I should have seen.
3. Fixed public subspace W₀ + UCVᵀ — ADOPTED as C19. 512× less mutable state than my C4, no merges, and most
   work moves into the public-coefficient corner. Better than my append-only design on every axis except
   capacity.
4. Proof-gated activation of epochs — ADOPTED as C20 and composed with my C13 (the quorum is the activation
   authority).
5. DP inside the transition — already C17b; accepted its cost lines and the falsifier (host choosing among
   seeds).
6. TEE epoch trainer — already C17a as a leg; Codex agrees it fails the requirement if the host includes the
   processor.
7. Ring-native accumulation with a separate integer-scaling relation — merged into C16's revised
   statement; its warning that R_Q has zero divisors, so field Schwartz–Zippel cannot be imported with
   |R_Q| in the denominator, matches `zq_fieldwide_sz_false` already in `Bfv/ZqSumcheck.lean`.

**Foundations (round 1):** (1) the custody/release game is weaker than our language → F14; (2) the
algebraic theorems are not a dark-training verifier because of witness custody → F13; (3) no single
executable numerical and learning specification → F15. All three ACCEPTED. Codex also found the GELU
counterexample to DARK-TRAINING §1 by hand (two inputs, output ≈ −0.15, derivatives of opposite sign),
independently of my bf16 count (F2).

**Where I disagree with round 1.**
- Codex says "a 20-bit plaintext modulus does not universally limit polynomial degree to two". True as a
  general statement and recorded in F15, but VERDICTS §3's claim was made for 8-bit fixed-point inputs,
  where it holds; I narrowed the citation rather than calling VERDICTS wrong.
- Codex calls T = d/(2r) "not an economic optimum". Agreed, and `low-rank-updates.md` never claimed it was;
  it is the commitment break-even. The program now says so and gives the merge a second job (F9).

---

## Round 2 — attack on the written program and the script

Codex re-ran the script (both sizes, reproduced 784/104/8 and 112/9), read the program, the critique,
`AuditSampling.lean` and `Bfv/Mul.lean`.

### 1. The cost model — ACCEPTED in full, script rewritten (v2)

Twelve defects, each with which rows move: (a) dark full backprop charged 4 dense products instead of 3,
and "public full training" stayed public after the first secret update; (b) d²/N is a packing throughput,
not a matvec price: with window k the tiled count is ⌈d/k⌉·⌈d/⌊N/k⌋⌉, and splitting a long dot product
into wrap-safe pieces does not make their BFV sum wrap-free; (c) fractional crossings — the minimum is
2L·⌈d/N⌉; (d) split-sign ct×pt is two multiplications in `bfv_coeff_matmul.rs`; (e) A(Bx) is depth 2;
(f) append-only backward must traverse the history; (g) the wrap gate granted refreshes the cost model
never paid; (h) the envelope "carries most of the promised security" and was nearly free; (i) the smudging
step function confuses scalar and transcript security, and imported a 16-party bound into a 3-party
model; (j) PQ ceilings are real table entries (HE Standard v1.1 p.31) but conditional; 1/q should be 2B/q;
the ×125 "welfare price" compared dark FHE against public MPC (within FHE it was ×6.1). And the power-
iteration "operator-norm certificate" in my F12 gives a LOWER bound, not an upper one — accepted; F12's
sound version is the product of Frobenius norms.

v2 changed three headline conclusions (tradeoff note §4–§5): the opacity price within FHE is ×2.0;
full backprop and append-only reach the fully-dark frontier; and once the envelope is proved on
ciphertexts it is 71% of the cost at p = 0.01, so sampling stops paying below that. Codex's verdict —
"withdraw 'good enough to rank' until there is one consistent numerical program, packing schedule and
mandatory-proof schedule per row" — ACCEPTED; the program now says "shape, not ranking".

### 2. displacement_bound — ACCEPTED, with its Lean statement adopted

Yes, it follows from `leakage_bound` at b = 2B, via a pathwise `injected ≤ 2B·count`, with a SEMANTIC
corrupt predicate, the comparator being the honest update from the actual pre-state, both updates capped,
and adversarial history-dependent amounts allowed. The statement Codex wrote is now the target in program
C2 and §5. Two residuals it found that I had not: the instantiated light-client checker
(`AuditSampling.lean:1036`) covers δ-far falseness only, so small semantic errors need a transport; and a
computationally sound envelope needs a damage bound on its failure event.

### 3. C13 NoUnsanctionedExecution — REFUTED, accepted

My strongest original idea did not survive. A noise upper bound never implies incapability; relin keys are
reusable; Enc(W)x for chosen public x is ct×pt; shallow fragments are unbounded in number. C13 is
rewritten as `NoUnauthorizedService` + a `SingleTimeline` that needs quorum intersection and durable
anti-equivocation. The real P3 needs C21 (below). This changes the welfare reading of the custody fork:
any host holding Enc(W) plus evaluation keys can compute model-dependent fragments of its choosing, so
P3 argues for MPC custody independent of cost. I record this as the most important correction of the day.

### 4. C8 proof-gated CPA-D — NARROWED to a restricted theorem, accepted

Policy-restricted IND-CPA-D with equal-ideal-output decryption plus a threshold transcript simulation;
ZKPoK of coins ≠ fresh sampling; the central hole is partial-decryption simulation; and "zero cost beyond
C1/C2" is false because the gate needs evaluation provenance on EVERY released ciphertext, which sampling
does not supply. C8 rewritten.

### 5. New constructions — ADOPTED

- **C21 instance-bound delegated transitions** (reusable model inside reactive MPC; one-instance garbled /
  randomized encodings bound to input commitment, parent and nonce). This is the construction that
  actually delivers P3.
- **C22 proactive forward-secure custody with epoch retirement** — the temporal threat to a long-lived
  mind; also the custody answer to harvest-now-decrypt-later.
- **C23 contractive continual learner** — turns injected displacement into a bound on persistent
  deviation, at the price of forgetting.

### Where I disagree with round 2

- On (i), Codex says "the run leaks 2^-6" was not justified, only that the bound fails. Agreed and the
  docs now say so; but I keep the read budget as a GATE, because a dark-learning design whose
  confidentiality proof fails at its own run length is not deployable for a mind regardless of what an
  attack achieves.
- Codex keeps "MPC public-trunk low-rank as a serious candidate". So do I; v2 shows the fully-dark FHE
  route is only ×2 its public-trunk sibling, so the program should not let the cheap public-trunk MPC
  point decide the welfare question (base = public is a disclosure ember must choose, §1).

---

## Net effect of the two rounds

Codex contributed: the witness-custody gap (F13), the refutation of C13, the restricted CPA-D game and its
transcript hole, six adopted constructions (C18–C23), the exact Lean statement of `displacement_bound`, an
independent GELU counterexample, and a dozen cost-model defects that changed v1's headline numbers. I
refuted nothing of substance it said; I narrowed two claims (C7 shard withdrawal already retrained; the
degree-2 remark is input-domain dependent and VERDICTS stated it for 8-bit inputs).
