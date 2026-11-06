# Dark learning gen 4: grounding

2026-11-06. Lane: dark-learning gen 4 (initiative #3). Starts from gen 3's transcript (`cv show aa3465e30b26e46e5`)
and the merged verifier at `4b58721b` (local `dev` was fast-forwarded to it; the eight identical untracked copies
were moved aside first and removed after the fast-forward matched them byte for byte).

## What I reuse, by file

| from | what | how |
|---|---|---|
| `research/dark_learning_2026_11_06/bfv_ref.py` | `ntt_primes`, `is_probable_prime`, `negacyclic_mul` (exact Kronecker products), `centered` | The ciphertext moduli (three, or four, 61-bit NTT primes) and t = the SPDZ prime come from here, as in every other brick. The verifier's folded-coefficient vectors are exact negacyclic products. |
| `scholar_zkpopk.py` (Astra scholar) | **the relation**: secret-key BFV with exact scaling, ternary s and [-8, 8] errors, the registered key `b + a s + e_pk = 0` with `a = public_a(seed)`, one integer witness across limbs, the context-bound statement; `public_a`; the Stern backend as the comparison and the attack list | The relation is kept, and re-stated per prime (below). `public_a` is imported unchanged, so the pinned-key check is the scholar's. Stern stays the reference price. |
| `scholar_zkpopk_lazer_params.py` | the relation compiler's column structure (one binary column per range digit, linear rows over the statement modulus) | Same idea, two changes: ranges use a top digit of adjusted weight, so one decomposition per variable, not value plus complement; and padding coefficients carry no plaintext digits (see below). |
| `cozk.py`, `cosnark.py` | the Ligero tests (proximity, linear with a zero-sum mask, quadratic with a vanishing mask), masks committed before the challenge they hide, distinct column sampling, Merkle paths, the (3/4)^T convention for rate 1/4 | Same tests, re-implemented for one prover over a large NTT field (cozk's O(k^2) Lagrange encoding cannot reach N = 8192). Leaves are salted here (cozk's are not; see the open question at the end). |
| `he_matvec.py`, `he_outer.py`, `step_counts.mask_nonideal` | the schedule: which ciphertexts each custodian sends per call, their slot layouts, FHE (b)'s mask ciphertexts | The per-step counts call these functions' layouts, not a copy of them. |
| `notes/astra-scholar/circuit-privacy.md`, `scholar_privacy.py` | the phase envelope, the flood parameters, the `a = 1` key attack, N = 16384 / four primes / F = 2^165 | Step 3 builds on these. |

## The peer call: the backend is not a lattice proof

I built the efficient ZKPoPK as a **hash-based Ligero argument over a 255-bit prime field**, not an LNS/LaZer
lattice proof. Reasons, in the order they decided it:

1. **The witness was the problem, not the backend.** [DERIVED] The scholar's relation commits m and eta at
   every coefficient: 268 binary columns per coefficient. In every schedule here the plaintext occupies at
   most d_c = 64 (forward, outer) or d_r = 128 (transpose; 256 at N = 16384) coefficients. Elsewhere m = 0 and
   the per-prime relation collapses to `c0 + c1 s + e = 0 mod q_i` with e in [-8, 8]: **5 digits per
   coefficient, not 268.** s is shared by the key and every ciphertext of the batch. Any backend gains this.
2. **With that witness, a lattice proof's response is linear in the witness and a Ligero proof is not.**
   [INFERRED] An LNS/ABDLOP-style proof sends a masked response z = y + c s1 with one coefficient of about
   log2(sigma) = 15-20 bits per witness coefficient. A batch of 64 ciphertexts at N = 8192 has 2.6 M digit
   coefficients, so z alone is tens of Mbit, about what the Ligero proof below costs (its size grows as the
   square root of the witness). There is no order-of-magnitude win to buy with the lattice route's costs.
3. **Its costs here are real.** No Sage on the Mac; LaZer needs Linux, AVX-512, GCC 13.2 and Sage 10.2; and a
   homemade lattice proof would need its own MSIS/MLWE parameter estimate, which the scholar advised against
   ("improving homemade lattice cryptography is not the recommended next brick"). Ligero's security rests on
   the hash and the Reed-Solomon proximity bound the harness already uses, and it is plausibly post-quantum
   through the BCS transform [INFERRED; no QROM proof is claimed here].
4. **The cross-limb question has a cheap exact answer over a large field.** [DERIVED] One witness of binary
   digits lives in F_P with P a 255-bit prime. After the digits are committed, Fiat-Shamir draws, per prime
   q_i, random weights rho in [0, q_i) over every coefficient equation, and the prover commits one quotient
   K_i with `sum rho * LHS_i = q_i K_i` over the integers. All terms are bounded so the equation cannot wrap
   modulo P; K_i is range-proved. A coefficient equation that fails modulo q_i survives with probability
   1/q_i. The same digits feed every prime's equation, so mixed limbs are impossible by construction.

What this does not buy: the scholar's LaZer profile remains the route if a lattice proof is wanted for other
reasons (smaller proofs for SMALL statements, or a shared lattice assumption with the HE). The comparison
row in the fork table keeps the old MODEL figure, labelled.

## Item 1 (columns)

T = 97 everywhere (`cosnark.T_COLS`, `cosnark_zk.T_HIDE/T_OPEN`, `proofwire.PARAMS`, HIDE = 2 x 97):
(3/4)^97 = 2^-40.26. **This is a statistical figure.** Under Fiat-Shamir a prover that grinds 2^g transcripts
wins with about 2^(g-40), so 2^-40 is not a non-interactive security level; 2^-128 needs T of about 309 at
rate 1/4. Both are counted. `cosnark_zk.counts_formula` bound K_L/T_HIDE/T_OPEN as default arguments at
definition time, so a pinned T was silently ignored by the formula; it now reads them at call time.

## Open question carried, not mine to fix now

`cozk.py`/`cosnark.py` Merkle leaves are unsalted `H("leaf", column)`. With T_HIDE = T_OPEN, after T openings a
row's polynomial is fixed by its message, so an unopened leaf lets a verifier test a guess of a whole row. That
matters only for rows with guessable content (mostly-public or low-entropy rows). Worth a reviewer's look.
