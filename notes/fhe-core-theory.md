# FHE core theory: the rotation-free inversion, and the honest security ledger

2026-08-13. Theory-mining lane, source-verified against vendor/fhe-dregg and
metatheory/Bfv. Corrects the vFHE agenda's missing-piece list.

## Ground-truth corrections (verified at source)

- **The deployed secret is CBD(20) (variance parameter 10, σ=√10, support ±20) — red-team corrected; earlier labels 'ternary' AND 'CBD(10)' were both misreadings of sample_vec_cbd** (support ±20, dense) — but
  fhegg's threshold shares ARE ternary. Two secret distributions in one tree;
  every noise bound carrying B_key moves ~4.3 bits between them. The "128-bit"
  quote is the lattice estimator's ternary row; 2024's MATZOV model says ~122;
  and no worst-case-to-average-case reduction supports the instance at σ≈3.16
  (though CBD = normal-form LWE dissolves the ternary-secret objection for the
  single-party path via ACPS).
- **r_t(q) = 0.82·t — costing ~7 bits — ⚠⚠ CLOSED NO-OP 2026-08-13 (measured):
  the KPZ fix is ALREADY IN FORCE in the deployed library. There is nothing to
  implement and no depth to recover.** The chain of supersessions, in order:
  (i) it was called a parameter bug wanting a Q≡1(mod t) re-genesis; (ii)
  corrected to an ENCODING bug per KPZ 2021/204's first modification — encrypt
  as `a·s + e + ⌊(Q/t)·m⌉` instead of pre-rounding Δ=⌊Q/t⌋; (iii) **now
  measured: `vendor/fhe-dregg` already encrypts that way.**
  `Plaintext::to_poly` (`vendor/fhe-dregg/src/bfv/plaintext.rs:51-64`) computes
  `−[Q·m]_t · t⁻¹ mod Q` from the per-limb `(−t)⁻¹` scaling polynomial built at
  `vendor/fhe-dregg/src/bfv/parameters.rs:418-436` — which is *verbatim* KPZ
  **Remark 3.1**'s RNS identity `⌊Q[m]_t/t⌉ mod Q = −[Qm]_t/t mod Q`, and
  equals `⌊Q·m/t⌋` exactly. Lineage: KPZ p.4 notes SEAL v3.4.0 independently
  added this; fhe.rs's own comment says "We use the same code as SEAL".
  **The r_t(Q) term is structurally absent from our noise path.**
  ⚠ And the predicted payoff was wrong twice over, both measured at the
  deployed ring (N=4096, log₂Q=109.0, t=1032193, r_t(Q)=843789=0.817·t):
  **deployed depth is 2, not 1** (40/40 draws), and an A/B against a
  hand-built classic Δ·m ciphertext shows the r_t(Q) term is worth **~8 bits,
  and 1/40 of a depth level** — depth 2 in 39/40 draws even *with* the defect.
  A level here costs 33–42 bits, so 8 bits was never going to buy one. The
  "~7 bits ⇒ free depth 1→2" step was a bit-count silently promoted to a
  level-count. The "Fheanor harness confirms depth 1" premise measured a
  *different library* (Fheanor Pow2BFV, ternary sk, DIGITS=3 gadget
  key-switch, budget-hits-0 meter), not our deployed BFV.
  Harness + falsifier: `breadstuffs/fhegg-fhe/tests/kpz_encoding_depth.rs`.

## THE INVERSION: rotation is not the missing piece for our workload

The agenda said "homomorphic slot rotation is the smallest change with the
largest unlock." The depth arithmetic at deployed parameters says otherwise:

**The slot/BSGS diagonal route does not close under the PROVEN worst-case
noise bound at our parameters** — fails by 2.9 bits at D=64, under any
key-switching variant — and lives entirely on the heuristic 2√n expansion
factor that HEIR's own source annotates "experimental result" and Gao–Zheng
(2025/1036) attack specifically for BFV's dependent products.

**The coefficient-encoding route closes with ~49 bits of headroom, uses ZERO
rotations, and is buildable today with zero new key material**: Cheetah-style
(2022/207 §4.1) — the (N−1)th coefficient of a polynomial product IS the
inner product. `Encoding::poly()` exists in fhe.rs and is used NOWHERE in
fhegg (all 31 encode sites are simd). Two structural reasons it wins: no
key-switch noise at all (RNS-BV adds 2^53.91 worst-case per rotation), and
coefficient-encoded plaintext norm is the weight magnitude (2^7 for int8)
instead of ~t/2 (2^19) — a flat 12-bit gift per layer.

For batching: **LZ/Bae PC-MM (2024/1284)** — one plaintext-ciphertext matmul
reduces to two plaintext BLAS GEMMs, zero rotations, EXACT for BFV; noise is
a row-sum bound with **no ring expansion factor**. For general packed shapes:
Rhombus (2024/1611) — needs PackLWEs (CDKS 2020/015), the ONE genuinely
missing primitive. Slots/BSGS are needed only if outputs feed another
homomorphic pointwise nonlinearity — and then N=4096/log q=109 gives one
layer, on a heuristic bound; multi-layer wants n=8192.

**Scheduling law worth naming: key switches AFTER plaintext multiplications,
never before** — 30.5 bits at our parameters, free. And hoisting is *exactly*
noise-neutral at power-of-two m (the automorphism is a signed permutation —
fhe-math rq/mod.rs:329) — a clean Lean theorem replacing HS18's hedge.

## ✅ THE RING LIFT LANDED (2026-08-13, `36dd4578e`, `metatheory/Bfv/Ring.lean`)

**The row-sum bound survived the carrier change VERBATIM** — `stepR_noise_le`
is `step_noise_le` with `Ct P → RCt P N`, `ℤ → Rn N`, `|·| ≤ M →
NormInfLE · M` and *nothing else*: same `RowBound` hypothesis (imported and
reused, not copied), same `G * M` conclusion, **no factor of N**. The proof is
the original with `intro k` prepended. That was the whole bet and it paid.

Also landed, all proved, zero `sorry`, zero obligations (`Bfv` namespace went
62 → 90 kernel-clean theorems):
- **`negaMul` is PROVED to be the ring product, not postulated** — the main
  vacuity risk. `toPoly_injective` + `negaMul_toPoly_dvd` show
  `X^N+1 ∣ toPoly a * toPoly b − toPoly (negaMul a b)` against Mathlib's
  `Polynomial ℤ`, stated in the quotient. An arbitrary bilinear op wearing a
  ring's name would have passed every other test.
- **`negaMul_normInf_le : ‖a·b‖_∞ ≤ N·‖a‖_∞·‖b‖_∞` — the provable δ_R = N,
  and it is proved TIGHT**: attained at *every* N by all-ones inputs
  (`negaMul_expansion_attained`, a general theorem not a case-test), with
  `N−1` refuted. The heuristic 2√N is deliberately not formalized.
- **`deployed_ring_depth`**: at N=4096, G=3, B=2^20, **T=42 steps keep every
  coefficient inside the decrypt margin** — the 42 previously proved about
  one scalar phase now holds on the whole ring.
- Teeth: row-bound necessity, satisfiable-and-not-vacuous, the negacyclic
  signature (`X·X = −1` at N=2 — nonneg inputs, negative output), and
  `negaMul_one_eq_mul` showing the scalar model is the N=1 case so the files
  refine rather than contradict.

Nice bonus: `Bfv/Mul.lean` had already priced this as a named blocker and
carried a hedge inflating the scalar bound by 4096. **That hedge constant is
now a theorem.**

## The Lean convergence (the good surprise)

`metatheory/Bfv/Noise.lean:264-287` already machine-checks `matVecCt` +
`RowBound` + `step_noise_le` — **which IS the LZ/Bae noise bound**, no ring
expansion factor. The scalar model the fhegg audit dinged for "no ring in it"
is exactly the right theorem shape for the rotation-free route; the ring lift
keeps the theorems as-is. `NoWrap.lean`'s capacity gate is also the right
shape, and yields a real quantization law from t: inner dim 512 exactly ⇒
**4-bit weights × 8-bit activations** (c ≤ 504).

## The security ledger (act-on items)

1. **Threshold decryption IS an IND-CPA-D oracle** (CCS'24 2024/127 App B.3),
   and leveled schemes cannot be CPA-D secure unconditionally (2026/203
   Prop 11-12); at log q=109 the negligible-failure escape leaves ~zero
   depth. Mitigation in-tree: the boundary opens only OTP-masked values —
   resting on co-located mask owners, disclosed in-code.
2. **The smudging theorem is scalar; the transcript is per-party polynomial**
   — Noah's Ark union factor makes the shipped 2^-48 into 2^-32 per session,
   vacuous at ~2^32 sessions; `TranscriptHybridLedger` obligation
   undischarged; `deployedCtNoise = 2^32` rests on a named unproven B_fresh.
   Statistical 80-bit smudge wants log q ≥ 138; the Rényi route buys KR-D
   only.
3. **eprint 2026/031** (Lagrange-ratio key recovery vs the
   Mouchet/Lattigo/fhe.rs threshold lineage): does NOT break our 3-of-4, and
   the nonce + exact-roster replay binding is the correct defense — **promote
   it to a named non-negotiable invariant**, it weakens as n grows.
4. Vendored `mbfv/secret_key_switch.rs:76` has NO smudging (literal TODO in
   source) — fhegg uses it only for the relin ceremony; keep it away from
   decryption paths.
5. Scheme-switching BFV↔TFHE between our halves: sound, not worth building
   (t≈20 bits vs PBS's ~11-bit input space). BFV bootstrapping: not needed
   and not usable at log q=109; **bigger modulus is the move**.

## Three things first (adopted)

1. **Build the rotation-free coefficient matmul** — `Encoding::poly()` +
   existing `Mul<&Plaintext>`; no ceremony; the only packed matmul that
   closes under a bound we can PROVE.
2. **Lift `Bfv/Noise.lean` to the ring keeping matVecCt/RowBound/step_noise_le
   as-is**, then name the two folklore facts (signed-permutation neutrality;
   the key-switch ordering law).
3. **Re-genesis with Q ≡ 1 (mod t) primes** and re-run the estimator against
   the SHIPPED secret distributions (both of them).

Clones landed in ~/src: openfhe-development, HElib, SEAL, tfhe-rs, heir,
fhe.rs upstream. HEIR ships six noise models with paper citations in source —
the single most useful artifact for the formalization lane. ~/paperbin now
619 PDFs.
