# Dark learning: two Codex (GPT-6 Astra) reads, and my adjudication

2026-11-05. Model `gpt-6-astra` via `codex exec --sandbox read-only`, run from this repo so it read the
files itself. Prompts: round 1 attacked my eight candidate constructions and asked for new ones and
foundation weaknesses; round 2 attacked the written program, the critique and the tradeoff script.
Verbatim final answers: `notes/dark-learning-scripts/codex-round1-answer.txt`,
`notes/dark-learning-scripts/codex-round2-answer.txt` (the raw transcripts, which include every file it
read, are not committed). Session ids are in the raw headers (round 1: `01a1af03-5ddf-7860-bc1e-4bb644dcc3f4`).

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

(appended below when the run completes)
