# FHE frontier scout: verdicts and the honest coverage note

2026-08-13. Coverage first: five threads, three delivered. **Transciphering
depth and the bootstrapping/NTRU/amortized frontier have candidate sets on
disk but NO depth verdicts — absence below is not a negative finding.**

## Evaluate now

1. **KPZ encryption fix** — the r_t(q) 7-bit recovery is one line in
   encryption, not a re-genesis (correction applied to fhe-core-theory.md).
   Afternoon experiment: predicted free depth 1→2.
2. **eprint 2026/027 (Zama)** — a MEASURED, Apache-2.0, WHIR+BLAKE3
   (hash-based, PQ) SNARG for public-matrix × encrypted-vector — exactly our
   operation. Its structural move: **the ciphertext modulus IS the proof
   field** (single Goldilocks prime, no RNS). Cloned to ~/src/matvecmul.
3. **The single-prime experiment** [ours; no paper states it as a goal]:
   swap matvecmul's one-line modulus to a ~109-bit NTT-friendly prime
   (verified plentiful, 2-adicity ≥32), P=2^20, inner dim 512 — asking
   whether our 3-limb RNS tower collapses to ONE prime shared with the
   prover, deleting the RNS-emulation-in-circuit cost that dominates all
   prior vFHE. Security margin IMPROVES (log q/N falls). Cost: losing RNS
   on the FHE side.
4. **PIR rotation keys cost 2.01 MB at our parameters** (12 keys × 0.33 MB
   at N=4096; the literature's 857 MB horror is N=2^16). **The field's
   rotation-phobia does not transfer to us** — PIR-for-embeddings is live.
5. **Fheanor** (~/src/Fheanor, built, harnesses written) as the prototyping
   bench — fhe.rs has no GBFV and no non-power-of-two cyclotomics.
6. **Powerformer BPMax** (2024/1429): softmax replacement at depth 3, 18
   key-switches, 82.86% GLUE — the depth-compatible attention nonlinearity.

## Measured facts to carry

- **GBFV at our exact ring**: noise independent of plaintext precision
  (byte-identical curves at 17-bit vs 206-bit primes) — but it TRADES
  PACKING for depth (~19× less plaintext per ciphertext). Quote both
  halves. Coefficient encoding survives; r_t structurally absent.
- **t = 2^20 is the binding constraint on BFV nonlinearity**: 8-bit
  fixed-point needs 2^{8d} < t ⇒ degree ≤ 2 REGARDLESS of levels — BFV
  cannot rescale. Encrypted attention at depth ≤3 is REFUTED (minimum
  published: depth 10, one layer); minimax sign minimum is depth 11. **The
  MPC-boundary / TFHE-PBS architecture for nonlinearities is confirmed as
  the only route at our parameters.**
- Gentry–Lee matrix-native FHE lands on our EXACT t (12288·84 = t−1,
  φ=4096) with pt-ct needing zero key switches — but **no noise bound
  exists in any of its three papers**; theorems are decryption identities
  with no norms. Watch; never quote a GL noise figure.

## Security ledger additions

- **2026/279**: coefficient-isometry hybrid attacks — 2–3 bits off dense
  secrets like our CBD(10) (stacks on MATZOV ~122). The attack mechanism IS
  the signed-permutation fact we use for free hoisting — the same structure,
  wielded by the adversary.
- **2026/366**: ring-structure decoding, up to 13 bits off sparse RLWE sets.
- **2026/285**: working IND-CPA-D PoC against OpenFHE's CKKS→FHEW switch —
  upgrades our scheme-switching verdict from "not worth building" to
  **"hazardous"**, with sufficient conditions supplied if ever needed.
- 2026/316's IND-CCA1 claim is retracted above its own introduction.

## The open problem sitting on our exact intersection

2026/1127 §D: **a ring-native arithmetization-friendly hash** (random-oracle-
like over power-of-two cyclotomic rings, compactly arithmetizable over the
ring) — they show Poseidon-over-rings fails. We hold Poseidon2 machinery and
a Lean hash metatheory. Filed as a research target, not a claim.

## Transciphering, honestly (partial coverage)

No 20-bit-p parameter set exists in the SoK tables (all 25–33-bit); our
gcd(t−1,3)=3 blocks cube-map ciphers at deployed t; and the prize is small —
our expansion is 10.9–27× at 109 KB/ct. Pirouette beats transciphering at
its own game anyway (but needs client-held sk — true for inference, not the
collective-key deployment). Homomorphic-decryption depth verdict: NOT
ESTABLISHED (the lane that owned it never returned).
