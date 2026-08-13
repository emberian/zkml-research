# The vFHE shortest path — and a correction to my own ladder

2026-08-13. Laminate (2025/2285) + packed sumcheck (2025/719) read end-to-end,
md5-verified against the mirror. Two corrections to `vfhe-agenda.md`, then the
milestones.

## Correction 1: my ladder mixed two security statements

"plonky2 20min → packed sumcheck 2.02s → Laminate 5–67×" is NOT one ladder.
The first two are **SNARK-over-FHE**: prove the *ciphertext operations* were
executed correctly; publicly verifiable; no leakage. Laminate is
**FHE-over-SNARK**: prove the *plaintext relation* holds; **designated
verifier** (only the sk-holder); **inherent one-bit leakage** per observed
verdict (Remark 2.5). A server passing Laminate has not proved it performed
any FHE operation correctly. Both useful; different products. Also:

- 719's 2.02 s is a **96-core wall clock** (~194 core-seconds); the ~2,400×
  was not core-normalized. Laminate's 5–67× IS core-normalized — and
  **entirely estimated** (no implementation; operation counts × SEAL
  microbenchmarks), with absolute cost 1.1–43.9 hours at n=2^20, and the
  range mostly reflects how cheap the honest baseline is (5.5× =
  mult-heavy-deep; 66× = add-heavy-uniform).
- Under commit-then-audit, Laminate's repeated one-bit leakage becomes an
  oracle (public verdicts on a chain); and its +1–4.5 levels of noise
  provisioning is paid on 100% of instances at any sampling rate. Sampling
  composes cleanly with the 719 class; poorly with Laminate.
- ⚠ 2026/487's "193× faster than LAMINATE" appears to benchmark a
  blind-BaseFold strawman — Laminate has no blind PCS by design. Unverified;
  do not fold in.
- Attribution fixes: 719 is IIE-CAS + SJTU/ECNU + **Ant Group**; the
  PipeSC/RENTT overlap is two shared authors (Kaixuan Wang, Lei Wang), not
  one lab. And "FHE's RNS limbs embed natively in the proof field" is FALSE
  for BabyBear (36 > 31 bits — hence `fheggQ0_scalar24_base64_fits`); they
  embed natively into THEMSELVES, which is the stronger fact below.

## Correction 2: 719 didn't solve ring-vs-field — it dissolved it

There is no Z_{2^32}→BabyBear embedding anywhere in 719. **They changed
TFHE's ciphertext modulus to BabyBear** (q = Q = p = 2^31−2^27+1, n = N_R =
1024), which eliminates key/modulus switching entirely. The transferable
lesson: *pick the FHE modulus to be the proof field.*

**And that lesson lands better on BFV than on TFHE** — our deployed RNS
limbs are proof-friendly primes and we would not touch fhegg's parameters.
⚠ **BUT the "cheaper than BabyBear at lower k" claim is REFUTED by the
field-choice lane (2026-08-13)**: the p^k comparison dropped the (2k−1)d
numerator — at λ=100 the saving is zero — and the limbs' two-adicity
(13/14/17) is fully consumed by the FHE NTT, leaving nothing for a proof
NTT. The limbs remain *usable* fields; they are not *better* ones. Where BFV is harder: cross-limb binding
(the extended-basis tensor + t/Q rounding is not expressible in any single
limb) — confirmed from our own source as the gap, matching the survey's #1.

## Laminate-for-BFV: three verified facts

- Our t = 1,032,193 is prime with t ≡ 1 (mod 8192): **full 4096-slot SIMD
  batching is available today**, and t is 19.98 bits — inside Laminate's
  sweet spot. R=5 gives 2^99.9; the lane verified **x^5 − x − 1 is
  irreducible over F_t** (40 candidates at R=5), discharging Theorem 5.5's
  depth-1 extension-mult prerequisite.
- **Noise budget kills fold/laned** (+120/+150 bits vs our total 109) but
  **Laminate_base (+32) fits our deployed parameters today** — for a
  depth-1 payload (one ct×ct mult), barely.
- **Laminate_base needs no rotations** — the missing-Galois-keys gap blocks
  fold/laned only. (Galois material exists unused in vendor/fhe-dregg.)

## The milestones (the real deliverable)

**M0 — days.** Wire `p3-sumcheck` (EXISTS at our pinned Plonky3 rev,
prover+verifier, BabyBear-tested; PLAN.md's "Plonky3 has no GKR" is stale
for our pin). Challenger bounds already satisfied by our DuplexChallenger;
Ext4 challenges at 2^123.6. Prove a product-of-MLEs toy.

**M1 — the demo: prove `fold_add` as a VECTOR relation, not 32,768 AIR
rows.** The 98,304-equation BFV family (4 orders × 2 polys × 3 moduli ×
4096 coeffs) is a vector-relation problem arithmetized as AIR rows — which
is why coverage sat at 1 equation. 719's real gift is the arithmetization:
a 4096-coeff negacyclic convolution IS their vector-NTT check; the
pointwise part IS their Hadamard check — one sumcheck each. And
`EmitByName.lean` already emits Lean-authored forward/inverse NTT
descriptors over q0 at production degree. `fold` is per-limb by
construction, so cross-limb binding is out of scope at M1.

**M2 — ct×ct + relin**: needs gadget decomposition (a lookup argument —
73% of 719's 2.02 s) + NTT checks + the cross-limb binding. The hard one.

Missing pieces, named: a vector-lookup IOP (not in-tree; check whether
p3-lookup composes with a sumcheck backend FIRST); a second
`DescriptorProofProver` impl (the seam exists at
`descriptor_proof_backend.rs:106`, HidingFRI is the sole impl — a sumcheck
verifier is NEW machinery, not the existing one); ⚠ **a Lean vector-relation
descriptor kind — house-law tripwire: a sumcheck claim IS a constraint
system; writing it in Rust is the drift and it will compile green**; check
whether minidregg's existing Lean sumcheck verifier (degree-1 + the
quadratic module) already reaches degree-2 fold relations before building;
defer packed sumcheck (ship Ext4 first, swap later — it also answers
`MixedFieldBudget.lean`'s question with a third option neither branch
considered: k=5 base-field-only at ~128 bits, 2.78× cheaper).
