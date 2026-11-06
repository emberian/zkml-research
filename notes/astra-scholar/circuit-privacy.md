# The HE return: phase smudging is not statistical circuit privacy

2026-11-06. [READ] Audited `he_matvec.py:35–52, 92–138, 170–178`, `bfv_ref.py:102–149`, `run_he_matvec.py`, and decision §11. Source SHA-256 values and every numerical result are retained in `research/dark_learning_2026_11_06/scholar_privacy_results.json`. No existing lane file changed. The Python harness is an arithmetic model, with deterministic test randomness; none of its keys are deployment keys.

## Finding and replacement claim

[REFUTED: full-ciphertext statistical privacy from the implemented flooding] Adding a fresh public-key encryption of zero and flooding **only c0** does not make the returned ciphertext statistically independent of the secret matrix. Its c1 marginal remains a translated, sparse distribution. Even the narrower phase-only budget misses 2^-40 per step at every requested width. Its bound also omits accumulated block noise in the original `noise_bits` routine.

[INFERRED] The useful replacement is **computational circuit privacy plus an explicit statistical phase-smudging term**, contingent on a correctly generated public polynomial, a bounded valid input ciphertext, a suitable RLWE rerandomization assumption, and complete proof/transcript composition. Alternatively, generate correlated zero encryptions with a genuinely uniform c1 through secure computation; that can support a statistical return simulator, but it is another preprocessing functionality, not the implemented `enc_zero_pk`.

## Why the full return has large statistical distance

[DERIVED] Work in R_Q = Z_Q[X]/(X^N+1). For one block, the second returned component is

    c1_out = P·a_sent + a_pk·u + e1,

where u is ternary and every coefficient of e1 lies in [-8,8]. For fixed a_pk, D = a_pk·u+e1 has support S of size at most 51^N. Neither the uniform plaintext mask M nor the arbitrarily wide c0 flood changes c1.

[DERIVED] Compare P=0 and P=1, conditioning on the receiver's sent ciphertext. Choose a_sent uniformly in R_Q and disclose it in both views, as the receiver knows its own ciphertext. For any D supported on S,

    E_a[TV(D,D+a)] >= 1 − |S|/Q^N >= 1 − (51/Q)^N.

Proof: use the membership event S. D(S)=1, whereas averaging the translated distribution over uniform a gives probability |S|/Q^N of landing in S. The joint distributions including a have TV equal to the average conditional TV. This is a statement about the **joint known-input view**, not the marginal obtained by hiding a from the receiver. Uniform M makes the masked plaintext output uniformly distributed in both worlds; conditioning on an equal output merely chooses M to compensate the product, and does not change c1.

[DERIVED/MEASURED] At N=8192, log2 Q≈183, the lower bound is `1−2^-1452667.49`. This does **not** exhibit an efficient distinguisher under honestly generated keys: membership in S can be hard. It refutes a small *statistical* distance for the present return, not computational RLWE security. `c1_support_control` enumerates the actual ternary/[-8,8] randomness for N=2: a fixed shift gives disjoint supports, exact TV=1. Flooding c0 cannot repair a marginal that is untouched.

[MEASURED] A separate **efficient malicious-key** falsifier uses a_pk=1, b_pk=−s, e_pk=0, with ternary s, and sends the valid zero encryption `(−32s,32)`. The return has `c1=32P+u+e1`; rounding each coefficient divided by 32 recovers P exactly because |u+e1|≤9. Across 25 executions, all eight P coefficients are recovered, while decrypting the fully masked/flooded return still gives the correct uniform M. A second 25-run control also survives a **public-key** bounded-opening relation: send `(−s,1)` with m=0,u=1,e0=e1=0; choose P on the 32-integer grid. Now `c1=P+u′+e1′`, so rounding to that grid recovers P. This distinguishes two allowed secret matrices with identical zero cross-term plaintexts. The first variant covers arbitrary P in the toy plaintext interval; the second covers the stated grid. Every bounded key/ciphertext equation holds. This is an attack on accepting attacker-chosen a_pk, **not** on the honest `OwnKey` sampler. The ZKPoPK lane's pinned public a_pk registry is the proposed repair; proving knowledge of bounded key-generation witnesses alone does not establish random generation. Input wellformedness must be checked before sending the return; a later Freivalds rejection cannot retract a privacy leak.

## The ring smudging lemma, instantiated

[DERIVED] For independent coefficientwise uniform U in [-F,F]^N and a fixed integer shift δ,

    TV(U,U+δ) = 1 − product_k max(0, 1−|δ_k|/(2F+1))
              <= min(1, ||δ||_1/(2F+1)).

This follows by counting the intersection of two equal-volume integer boxes. Reduction modulo Q is deterministic, so cannot increase TV. Conditioning on any pre-flood transcript and then averaging preserves the bound. It applies to mixtures of bounded shifts as well: couple each component to the same independent U. Fresh, independent flooding for each response then permits the sequential hybrid sum. [MEASURED] The exhaustive N=2, F=3, δ=(1,2) control gives TV=19/49, exceeding the incorrect scalar-only 2/7 and below the ring union bound 3/7.

[DERIVED] Let A=floor(t/2), n_c=d/d_c, n_r=d/d_r, d_c=min(d,64), d_r=min(d,N/64). The exact-encoding fresh ciphertext phase differs from (Q/t)m by at most 8+1/2 per coefficient. Each plaintext block has at most d_r d_c nonzeros bounded by A. The fresh Enc_pk(0) phase is `−e_pk*u+e0+s*e1`, bounded by 16N+8 when s,u are ternary and all errors are at most8. Including the mask encoding and the final canonical output encoding costs at most one further unit. Thus safe integer envelopes relative to Encode(y) are

    B_forward = ceil(8.5 n_c d_r d_c A) +16N+9,
    B_backward = ceil(8.5 n_r d_r d_c A) +16N+9.

These bounds cover **every returned coefficient**, not only the extracted dot products. The factor n_c/n_r covers all summed blocks. Reducing the plaintext sum modulo t changes its ideal phase by a multiple of Q; it does not introduce an unaccounted carry. Rounding errors are bounded before the plaintext multiplication. Small model weights do not make shares small: the full-size additive shares require A.

[DERIVED] With two forward matvecs and one transpose, there are C_f=12n_r and C_b=6n_c responses. Define A_step=N(C_f B_forward+C_b B_backward). The phase-to-simulator error is at most

    ε_phase,step <= min(1,A_step/(2F+1)).

The simulator here keeps c1's distribution and replaces the phase by Encode(y)+U; this is **not yet a circuit-private simulator**. Bounding distance directly between two arbitrary real evaluations costs twice this simulator bound. All tables below price the one-sided simulator error, with that convention explicit.

## Current parameters and required margins

[MEASURED/DERIVED] `scholar_privacy.py` recomputes the three61-bit primes and t from the harness. Q≈2^183, t≈2^61, margin Q/(2t)≈2^121. The implemented F is exactly2^118. The following are conservative phase upper bounds; bounds above1 are capped at1, not claims of that much leakage.

| d | returned ciphertexts | log2 phase bound per step | bound over 10^6 steps | minimum log2 Q for phase ≤2^-40 per step | minimum log2 Q for phase ≤2^-40 over 10^6 steps |
|---:|---:|---:|---:|---:|---:|
|64|18|−26.743|0.008906|>193.258|>213.189|
|1024|192|−18.743|1 (vacuous)|>201.258|>221.189|
|4096|768|−14.743|1 (vacuous)|>205.258|>225.189|

[DERIVED] Modulus requirements solve `F >= A_step H 2^40/2` together with `F+max(B_forward,B_backward)+1 < Q/(2t)`, for H=1 or10^6. They allow an arbitrary integer F; power-of-two F choices cost up to one additional bit. A **per-step** 2^-40 budget composes to at most10^6·2^-40≈2^-20.07 over the run. Requiring 2^-40 for the run needs ≈19.93 additional bits. The code's `phase_parameter_gate` checks these inequalities with integers and refuses every current row for the million-step target.

[READ/SOURCE] The November2018 HE Standard, §2.1.5 p25 and ternary quantum table p28 (PDF indices24,27), specifies Gaussian error σ≈3.2 and lists logq202 at N8192 and411 at N16384. These are conditional historical estimator recommendations, not security certificates for this harness's uniform[-8,8] errors. Source: [HE Standard v1.1](https://homomorphicencryption.org/wp-content/uploads/2018/11/HomomorphicEncryptionStandardv1.1.pdf). At d4096 even the *phase-only per-step* requirement exceeds202. A fourth61-bit prime at N8192 provides correctness room but exceeds that table's ceiling.

[DERIVED/MEASURED] One conservative arithmetic alternative is N16384, four61-bit primes (Q≈2^244), the same plaintext prime, d_c64/d_r256, and F=2^165. The phase budget over10^6 d4096 steps is ≤2^-40.811, with ≈17 bits of decryption margin remaining. The integer gate accepts it. Ciphertext wire rises from84,934,656 to188,743,68061-bit elements per step; adding the unchanged SPDZ online remainder gives192,798,750 instead of88,989,726. It remains below the old all-SPDZ online305,897,484, by ≈1.59×, before proof/preprocessing traffic. This alternative is a **formula and parameter gate**, not an N16384 HE execution: existing `HEMatvec` hardcodes three limbs in its live wire accounting. Separate same-security recosting of the FHE fork is required before declaring a fork winner.

## What closes next, and what this does not promise

[INFERRED] A plausible computational proof first smudges the phase as above, then replaces the surviving c1=`a_pk*u+e1+known translation` by uniform via an RLWE hybrid. The reduction needs honest/publicly generated a_pk, security for the actual sampler and many samples, and simulation of the input proof and malicious receiver's auxiliary information. The pinned registry excludes the exhibited degenerate key; it does not itself prove this reduction. At worst a hybrid across returns pays one assumption loss per response; a multi-sample reduction should state its concrete resources. No increase in Q or N alone repairs the full-ciphertext statistical obstruction.

[INFERRED] If statistical circuit privacy is mandatory, preprocess `(c0,c1)` with c1 genuinely uniform and `c0=−s*c1+e` via secure multiplication with the secret-key owner; keep the randomizer private from that owner until use. Adding it makes c1 uniform, then the ring smudging lemma handles the phase. Its generation and malicious-security proof must be priced; it cannot be credited as a cheap local public-key Enc(0).

[READ/SOURCE] GForce's AppendixC.2 explicitly defines circuit privacy against a secret-key holder, discusses flooding and warns that maliciously oversized input noise invalidates the chosen bound. This is useful motivation, not a proof of our return format: [Ng–Chow, USENIX Security2021, AppendixC.2](https://www.usenix.org/system/files/sec21-ng.pdf).

[OPEN] Neither these controls nor a repaired HE phase ledger establish whole-run confidentiality. The SPDZ truncation/statistical masking budget, actual ZK simulator, preprocessing, key setup, authentication, abort behavior, release policy and adaptive composition remain distinct terms. In particular, the existing scalar KAPPA40 truncation budget cannot be silently omitted from a claimed million-step 2^-40 guarantee.

[EXECUTED] `python3 research/dark_learning_2026_11_06/scholar_privacy.py > research/dark_learning_2026_11_06/scholar_privacy_results.out.txt` exits0. It executes all falsifiers and parameter-gate assertions. Large rows are integer formulas only; polynomial products run only at N2/N8 on the Mac. No hbox jobs. Research used two free web search queries, primary-paper/standard reads, zero Kagi queries and no ePrint downloads.
