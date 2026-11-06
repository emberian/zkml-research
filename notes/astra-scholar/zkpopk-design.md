# A ciphertext admission proof that is actually zero knowledge

[READ] Scope: `he_matvec.py` sends **secret-key** BFV ciphertexts through `BFV.encrypt_exact`; its advertised `2L(N−1)+7N` witness count instead sketches a **public-key** encryption relation with `u,e0,e1`. They are different statements. The 6.236 Gbit at d=4096 is an unbuilt committed-witness estimate, not measured proof traffic. This brick keeps the sent ciphertext format, ties it to the custodian's registered key, and builds a real, deliberately expensive zero-knowledge reference backend. Nothing in this note edits §9 of VERDICTS or claims deployment security.

## Decision

[INFERRED] **Select the exact-bound LNS/LaZer family as the efficient implementation target.** Compile the relation below into binary polynomial columns and linear equations; use the library's exact binary proofs. Do not substitute an approximate shortness proof for an exact noise bound. The accompanying compiler and parameter input file exist; a generated lattice security profile and an executed LaZer proof do not yet exist. Consequently no LNS proof-byte figure is claimed.

[MEASURED] **Build a fourth, conservative backend now: a salted-hash Stern proof with exact bounds.** It realizes the same relation without a lattice proof dependency. The verifier receives commitments, masked vectors and partial openings, never the raw message, secret key or noise. Its terrible price makes it a reference and an attack-testing tool, not a recommended large-width deployment. It is an actual ZK proof protocol in the classical random-oracle model under its stated commitment assumptions, rather than a transparent relation checker called ZK. The simulation/extraction argument below is mathematical reasoning, not a machine-checked security proof or an audited cryptographic implementation.

[READ] Candidate comparison, with source depth made explicit:

| Candidate | What was read | Consequence for this instance |
|---|---|---|
| Baum–Damgård/BDLOP and amortized Baum–Lyubashevsky line | Baum–Lyubashevsky, ePrint [2017/759](https://eprint.iacr.org/2017/759), abstract, §1 and §4/Table 1; LNS's description of BDLOP | The extracted shortness bound has **slack**. The concrete BL table has about 2^24 slack. That slack must enter the HE noise and flooding ledger; it cannot be advertised as proving the honest bound8. Its amortization is attractive, but not this exact admission predicate. |
| LNS, *Shorter…via One-Time Commitments* | ePrint [2020/1448](https://eprint.iacr.org/2020/1448), §1, §2.4, §3/Theorem3.4, §3.2, §4.1 | Exact range proofs are explicitly distinguished from approximate ones. The 2021 opening optimization uses an additional **Extended M-LWE** assumption; its 33KB-class example is a dimension2048 statement, not N8192 BFV. Never transplant that byte count. |
| LaZer linear backend | [2024/1846](https://eprint.iacr.org/2024/1846), §3.1; official [`lin-codegen.sage`](https://github.com/lazer-crypto/lazer/blob/main/scripts/lin-codegen.sage), binary [`demo_params.py`](https://github.com/lazer-crypto/lazer/blob/main/python/demo/demo_params.py) profile and [README](https://github.com/lazer-crypto/lazer/blob/main/README.md) | Supports binary witness partitions, arbitrary statement modulus through a lifted relation, and conversion to its small proof ring. Thus the fully split BFV ring need not be the proof ring. The supplied profile has a 244-bit composite **statement** modulus, not a claim that this is a valid lattice **proof** modulus. Codegen/estimation remains necessary. |
| Amortized ring sumcheck | Local `cert_b61.py`, `e2s_proof.py`, `cosnark.py` and FS falsifiers, full source | A polynomial identity check does not establish knowledge, range, or ZK by itself. R_Q has zero divisors; use per-prime fields with common integer witness or a separate proof field, never a `1/|R_Q|` Schwartz–Zippel claim. Building masked PCS/range machinery would duplicate the separate live collaborative-proof ZK lane. |

[READ] The local paper corpus supplied PDFs; none was downloaded from eprint.iacr.org. Seven free web-search queries located titles/official implementations; zero Kagi queries. LaZer README currently requires Linux x86-64, AVX512, GCC13.2 and Sage10.2; this Mac has no Sage. No external build was started and no large N8192 proof was attempted.

## Exact relation, including the key

[INFERRED] Let `R=Z[X]/(X^N+1)`, `Q=q0*q1*q2`, and `t` the SPDZ prime. A registry pins `(key_id, epoch, N, Q, t, a, b)` before accepting ciphertexts. The polynomial `a` is derived by rejection sampling from a **registry-owned, ungrindable public seed**. The producer cannot choose or replace it in a proof. Key relation:

```
b + a*s + e_pk = 0 mod Q,       s ∈ {-1,0,1}^N, e_pk ∈ [-8,8]^N.
```

[INFERRED] For a sent `(c0,c1)`, prove knowledge of `s,e_pk,m,eta` satisfying, coefficientwise in R_(tQ),

```
t*b  + t*a*s  + t*e_pk        = 0,
t*c0 + t*c1*s - Q*m - eta      = 0,
0 ≤ m ≤ t−1,
|eta| ≤ H := 8*t + (t−1)/2.
```

[INFERRED] These equations are linear in the private variables. They contain neither an unchecked polynomial quotient nor independently chosen witnesses for different RNS limbs. They are checked over the **whole negacyclic ring**, not at one evaluation point. Canonical ciphertext coefficients and all vector lengths are enforced before proof verification.

[DERIVED] For odd t, `r=t*round(Q*m/t)−Q*m` lies in `[-(t−1)/2,(t−1)/2]`. The second relation forces `eta≡r modt`, hence `eta=r−t*e` for an integer e. The interval `|eta|≤H` is equivalent to `e∈[-8,8]`: e=9 already gives eta≤−H−1, and e=−9 gives eta≥H+1. Thus the extracted relation implies **the exact fresh BFV encoding with bounded error8**, not merely a vaguely small decryptable phase. The key and ciphertext share the same extracted s. Correctness after a secret matrix multiplication still needs the separate circuit-privacy/noise ledger. This is a proof of membership in the exact bounded relation, **not proof that secret/error samples followed the honest probability distribution**. It proves a canonical plaintext polynomial, not that application-specific padding coefficients are zero or that its nonzero coefficients equal the authenticated input share; layout constraints require additional public linear rows, while share consistency belongs to the later Freivalds integrity check.

[DERIVED] Every scalar interval `[lo,hi]` is encoded by binary digits of `x−lo` and `hi−x`; their sum is constrained to `hi−lo`. Binary digit sums cannot wrap modulo tQ: even the largest eta range has a total digit capacity below68t, whereas three distinct odd ciphertext primes have Q≥105. This pins the integer ranges, including ternary s, exactly. At deployed parameters there are268 binary polynomial columns, N8192, and six polynomial equation rows (two encryption/key rows and four range rows). No bit is credited as 16-bit packed field storage.

[INFERRED] The registry premise is load-bearing. The privacy lane's `a=1,b=−s,c1_sent=32` attack satisfies bounded symmetric encryption equations but exposes a matrix share in the returned c1. This gate rejects that **unregistered** key. It does not prove that a dishonest registry sampled its seed honestly, and a proof of knowledge cannot establish that fact. Joint coin generation with at least one honest participant, persistent key registration, and rejection of seed grinding remain protocol obligations. No claim of statistical circuit privacy for both ciphertext components follows from this proof.

## Executed Stern protocol and Fiat–Shamir ordering

[INFERRED] Flatten the binary columns to B bits and extend each bit to `(bit,1−bit)`. Let `A*x=y` be the public linear relation modulo tQ. Per repetition choose uniform mask `r∈Z_(tQ)^(2B)` and independent pair swaps π, then commit with independent 256-bit salts:

```
C0 = H(salt0, π, A*r)
C1 = H(salt1, π(r))
C2 = H(salt2, π(r+x)).
```

[INFERRED] All repetitions' commitments, the complete public statement and operation context are fixed **before one joint Fiat–Shamir challenge vector**. Challenges are unbiased trits obtained by rejection sampling from SHAKE256. Context binds epoch, parent, step, operation, block, sender and recipient. The witness is bound through hiding commitments; **the raw witness is never hashed into a public proof transcript**.

[INFERRED] Responses are: challenge0 opens `(π,r)` against C0/C1; challenge1 opens `(π,z=r+x)` against C0 using `Az−y` and C2; challenge2 opens `(πr,πx)` against C1/C2 and checks every pair in πx is `(0,1)` or `(1,0)`. Three accepting answers to the same commitments extract `x=z−r`: commitment binding ties the permutations/masks together, the third branch gives exact binary values, and subtraction gives Ax=y. This needs no division or invertible ring challenges, so composite tQ causes no extraction gap. Knowledge error is2/3 per interactive repetition;219 repetitions give `(2/3)^219≈2^-128.107`.

[INFERRED] Each branch has a witness-independent honest-verifier simulation: r and z are uniform; πx is uniform among valid pair encodings. Salted unopened commitments hide the missing branch in the random-oracle model. The committed-then-challenged noninteractive form needs the usual **classical ROM** programming/extraction argument and charges the adversary's oracle-query/grinding budget. The interactive exponent is not an unconditional128-bit NIZK security certificate. **No QROM reduction is claimed**, and SHA256 collision security is not a128-bit post-quantum binding claim. Those are deployment blockers, stated separately from the exact algebra.

## The executable boundary and attacks

[MEASURED] Files beside `he_matvec.py`:

- `scholar_zkpopk.py`: private prover; independent public-only verifier; exact compact codec; `encrypt_and_prove`; fail-closed `accept_ciphertext`; `multiply_verified`, which calls existing `ptxct` only after admission. No other lane's file is edited.
- `scholar_zkpopk_lazer_params.py`: parameter-input generator and sparse polynomial-matrix compiler for the same exact binary relation. Its compiled relation is independently multiplied in tests. It is **not** a measured LaZer proof.
- `scholar_zkpopk_tests.py` and `scholar_zkpopk_results.json`: reproducible small-ring execution and deployed-parameter counts.

[INFERRED] Integration is an explicit admission adapter, not an automatic replacement of `HEMatvec.__call__`. The sender must retain `(s,e_pk)` from registered key generation, and the return encryptor must use that same registry's public key `(b,a)`. `OwnKey` currently discards its key-generation error and chooses a locally random a, so existing objects cannot be silently retrofitted. A caller uses:

```python
reg, s, e_pk = keygen(N, primes, t, registry_seed)
envelope = encrypt_and_prove(reg, s, e_pk, packed_plaintext, context)
# Recipient has reg and a locally expected context, not s/e_pk/plaintext.
product = multiply_verified(matrix_block, reg, envelope, context)
```

[MEASURED] That sender→recipient→existing `he_matvec.ptxct` path executes in the test. A falsifier instruments `ptxct` and verifies **zero calls** for a rejected envelope. Full scheduling, registered-key return encryption and persistent parent/epoch state must be wired by the consumer; a context string is binding only if the verifier compares it to locally expected state. No patch is needed to run this standalone adapter, and the unmodified original schedule still has no admission proof.

[EXECUTED] `python3 research/dark_learning_2026_11_06/scholar_zkpopk_tests.py > research/dark_learning_2026_11_06/scholar_zkpopk_results.json` exits0. N8, three17-bit ciphertext primes, t17-bit;219 proof repetitions. Honest proof, compact roundtrip, independent compiled matrix relation, extraction identity, and verified-then-multiplied ciphertext all pass. Wrong plaintext offset, mixed limb, stale parent/epoch/recipient, changed/noncanonical/short response, nonbinary secret response, missing repetition, bad packet lengths, malformed proof objects and `a=1` key are refused.

[MEASURED] The adaptive Fiat–Shamir falsifier is stronger than a random mutation: `c1=0,c0=floor(Q/(2t))` is outside the allowed noise neighborhood of **every** plaintext. A simulator fabricates accepting branches without a witness when the challenge hashes public data only. The legacy verifier accepts; the commitment-bound verifier refuses. The real recipient gate refuses it before multiplication. Every written falsifier was run.

## Recount, with units kept separate

[MEASURED] At N8 the actual compact proof is **2,795,545 bytes**, exactly the codec formula. At N8192 no cryptographic operation is run: parameter generation and integer arithmetic give B=2,195,456 bits,2B=4,390,912 masked coordinates,244 bits per coordinate and219 repetitions. Each repetition sends three256-bit commitments, two256-bit salts,2B masked residues, B swap/pair bits and a one-byte branch tag; the packet has a10-byte header and explicit padding.

[DERIVED] One exact Stern proof is **29,389,232,581 bytes =235,113,860,648 bits**. These are delivered proof bytes, not committed witness bits:

| d | delivered proofs in existing schedule | Stern proof bits/step | old unbuilt witness bits/step |
|---:|---:|---:|---:|
|64|18|4,232,049,491,664|116,926,020|
|1024|240|56,427,326,555,520|1,559,013,600|
|4096|960|225,709,306,222,080|6,236,054,400|

[INFERRED] This fallback destroys the hybrid's cheap-wire verdict **for this implementation**. It does not refute an efficient LNS proof, nor turn the old witness count into a lower bound. The existing schedule sends the same ciphertext to two peers; an agreed recipient-set context could reuse a proof object, saving prover work and published-object storage, while unicast wire still pays delivery twice. This implementation binds one recipient and claims no such saving.

[OPEN] Next implementation step: run the emitted exact-binary profile through LaZer's pinned estimator/code generator on a qualified machine, instantiate its public sparse matrix/prover/verifier, retain these adversarial envelope tests, then re-count actual serialized proof bytes and validate the resulting QROM/commitment assumptions. Until that is done, the efficient hybrid has a concrete relation and a costly working ZK reference, **not** a finished practical ZKPoPK leg. The library's mature protocol should replace this reference; improving homemade lattice cryptography is not the recommended next brick.
