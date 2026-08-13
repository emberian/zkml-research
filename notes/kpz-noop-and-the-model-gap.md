# KPZ fix: CLOSED as a no-op — and three corrections to our own record

2026-08-13. The lane derived it, measured it, and falsified its own falsifier.
A no-op finding done properly is worth more than a positive done loosely.

## The verdict

**fhe.rs already encrypts with KPZ's exact-division encoding.** Derived, not
taken on trust: `parameters.rs:418-436` builds `delta` as the RNS lift of
`(−t)⁻¹ mod Q`; `plaintext.rs:51-64` computes `m ← ((Q mod t)·m mod t)·(−t)⁻¹`;
`secret_key.rs:197` feeds that to `encrypt_poly`, giving `⌊Q·m/t⌋ + e`. With
`Q = tΔ + r`, `−t⁻¹[rm]_t ≡ Δm + ⌊rm/t⌋ = ⌊Qm/t⌋ (mod Q)` — **verbatim KPZ
Remark 3.1.** The r_t(Q) term is structurally absent from our noise path.
(Lineage explicit on both sides: KPZ notes SEAL v3.4.0 added it independently;
`parameters.rs` says "We use the same code as SEAL.")

## ⚑ Three corrections to what we had recorded

1. **Deployed depth is 2, not 1.** Measured, 40 draws, deployed ring: fresh
   4.0 bits → ct+ct add **+0** → pt-ct mul +27 → ct×ct #1 **+42.1** → ct×ct #2
   **+33.0**, against an 88.02-bit cliff. 8.9 bits left after two. **We have
   been quoting depth 1 in several notes.**
2. **The "Fheanor confirms depth 1" premise measured a different library.**
   Fheanor's BFV is the **classic** scheme (`Delta = rounded_div(q,t)` then
   `m*Delta`) with different relin digits and a budget-hits-zero meter rather
   than decode-correctness. Decomposed: encoding accounts for **7.7 bits**,
   key-switch/implementation for **9.2** — a ~9-bit offset straddling a cliff,
   not a contradicting verdict.
3. **The predicted payoff conflated BITS with LEVELS.** The r_t(Q) term is
   worth ~8 bits and **1/40 of a level**; a level costs 33–42 bits here. The
   "~7 bits ⇒ free depth 1→2" step silently promoted a bit-count into a
   level-count. **Worth naming as an error class**: in a budget with a cliff,
   a small absolute saving buys nothing unless it crosses the cliff.

## ⚑ New finding: our Lean model is the PRE-KPZ scheme

`metatheory/Bfv/Params.lean:63` defines `Δ := q/t`; `Bfv/Noise.lean:72`
defines `encrypt P m e := ⟨Δ·m + e⟩`. **The deployed library does not produce
`Δ·m + e`** — it produces `Δ·m + ⌊rm/t⌋ + e`.

The soundness impact is **zero**: the `2(t−1)r` cross-term costs **0.00 bits**
of the 88.02-bit budget (2^40.66 against Q=2^109). `Noise.lean:35`'s comment
that "~2^40, so dropping it is not pedantry" is true as an absolute magnitude
and **worth zero bits of the bound it gates**.

The live gap is **fidelity**: the model's `noiseAt` reads a real fresh
deployed ciphertext at **20 bits, not 4** — a measured 16-bit error. Harmless
for the bound, wrong if the model is ever used to *price* the deployed object.
That is now a named gap, and it is the kind that a bound-only check cannot see.

## The falsifier is constructive, per house law

`fhegg-fhe/tests/kpz_encoding_depth.rs` (landed `3eced8224`) hand-builds the
classic-Δ arm from the public API with the same sk/rk/multiplicator — encoding
as the only variable — and requires the meter to **see** its r_t(Q) term at
~20 bits. So a regression to pre-rounded Δ *or* a blinded meter goes red.

⚠ Shared-tree note: the lane's edit to `fhe-core-theory.md` was absorbed into
a parallel lane's commit `910df26` before it could commit. Content intact in
HEAD, attribution merged, history not rewritten.
