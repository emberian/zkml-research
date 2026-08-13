# FHE core theory: the rotation-free inversion, and the honest security ledger

2026-08-13. Theory-mining lane, source-verified against vendor/fhe-dregg and
metatheory/Bfv. Corrects the vFHE agenda's missing-piece list.

## Ground-truth corrections (verified at source)

- **The deployed secret is CBD(10), not ternary** (support ±20, dense) — but
  fhegg's threshold shares ARE ternary. Two secret distributions in one tree;
  every noise bound carrying B_key moves ~4.3 bits between them. The "128-bit"
  quote is the lattice estimator's ternary row; 2024's MATZOV model says ~122;
  and no worst-case-to-average-case reduction supports the instance at σ≈3.16
  (though CBD = normal-form LWE dissolves the ternary-secret objection for the
  single-party path via ACPS).
- **r_t(q) = 0.82·t — essentially the worst possible draw**, costing ~7 bits
  after the first multiplication. Free to eliminate: verified alternate
  NTT-friendly prime triples with **Q ≡ 1 (mod t)** at the same widths.
  **A re-genesis, not a cost** — the house doctrine's exact case.

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
