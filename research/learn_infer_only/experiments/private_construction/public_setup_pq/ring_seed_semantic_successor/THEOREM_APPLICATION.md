# Fixed semantic basis and 384-bit seeded transport

[DERIVED construction, 2026-09-08] This is the implemented semantic specialization of the QROM successor, using a new mandatory 384-bit seed format and the previously completed fixed linear prototype query basis. The application below supplies the message-basis reduction explicitly. It preserves the ring arithmetic, finite Gaussian law, q, Delta and decoder. A single fresh service run is jointly owned with `research/vfhe_2026_09_08/proved_journal/seeded_ring_successor/`; this backend launches no duplicate setup.

## 1. Public basis fixed before setup

[SOURCE/DERIVED] `registry.json` is a byte-identical copy of the completed semantic registry, SHA256 `295c8feed3bc299e0a97f15b36808fdba1e85e03c3d234e6253d136a5b4778b5`. It selects 16 saved text-query vectors of dimension 577 before any seed or credential generation. Their last coordinate is zero, entries are signed int8, and their row rank over F_p is 16. The copied `basis.py` validates the rank and canonical pivot columns. All actors load and validate this registry before their command runs; init therefore fixes the basis before sampling its A seed.

[DERIVED invertible completion] Let Y be these 16 rows and I their 16 pivot columns. Let C be the ascending list of 561 nonpivot columns. The square submatrix Y_I is invertible. Define B by first taking Y and then the identity rows e_c for c∈C. If Bx=0, the identity rows imply x_C=0, and then Y_I x_I=0 implies x_I=0. Thus B is invertible. Its explicit inverse copies the nonpivot coordinates and solves `x_I=Y_I^-1(u_[16]−Y_C x_C)`. This proves the complete basis property, rather than identifying it only from six test inputs.

## 2. Explicit message reduction to coordinate security

[DERIVED] Let Enc_I be the fixed-coordinate ring scheme whose secret row z_i reads coordinate i. Define

```text
Enc_B(x) = Enc_I(Bx mod p),
Decode_B,i(ct) = Decode_I,i(ct).
```

[DERIVED correctness] Encryption uses the centered representative `a(x)=center_p(Bx)` exactly as in `GeneralBasis.transform`. For every registered i, the decoder returns the residue `(Bx)_i = <Y_i,x> mod p`. B is public and invertible; it changes messages, not the Gaussian distribution of any z_i. The recipient still samples only its one prescribed independent row and publishes `<A,z_i>`. No `B^-T` transformation of secret rows, large-coefficient secret combination or additional master key occurs.

[DERIVED security reduction] Given an adversary against the B scheme, a coordinate-game adversary publishes the fixed B/registry as public context and forwards each adaptive pair `(x0,x1)` as `(Bx0 mod p,Bx1 mod p)`. The required condition `Y_J x0=Y_J x1` is exactly equality of the coordinate-game messages on J. It returns the supplied ciphertext with the common deterministic public metadata. Public additions, subtractions, expiry, model comparisons and the adversary's quantum state pass through the same channel. Thus its distinguishing advantage equals that in the B game, with only the cost of the public transforms and metadata added to the reduction. B was fixed before setup, independently of the fresh oracle and key coins, so this is an allowed public auxiliary context.

[DERIVED scope] The underlying algebraic encoding is bijective on F_p^577. This semantic CLI deliberately accepts the restricted issuer domain of signed-int8 residues in the first 576 coordinates and a final zero. Restricting the message domain preserves the above security reduction; it does not prove selected-output simulation or an unrestricted semantic image. Every transformed coordinate is still encoded, including the 561 complement coordinates. This remains a full-vector encoding with restricted readers, rather than a bank containing only 16 permitted projections.

[DERIVED integers versus residues] For a semantic vector x, `|<Y_i,x>|≤127||Y_i||_1`. At capacity two, the saved registry yields the whole-input-domain bound

```text
2 max_i 127||Y_i||_1 = 2,520,950 < floor(p/2) = 14,219,946.
```

[DERIVED] Therefore the first 16 centered transforms equal their signed integer scores, and summing two live inputs gives the intended integer class score without modular wrap. The complement identity rows are also bounded int8 values. Class means divide the decoded integer score by the public class count; the recipient compares exact rational means. The copied query implementation performs this computation. It is a linear prototype learner; no nonlinear feature map is introduced here.

[DERIVED closure] Accumulator updates add the fresh ciphertext and subtract the exact expired original ciphertext. Its original error cancels exactly. The live window has nonnegative unit lineage and capacity two. The broader ring W=32 coefficient/range contract is unchanged, but this application uses its stricter W2 score range. Reducing each input modulo p is not a license to wrap the aggregate signed score; the explicit bound above supplies its unique integer lift.

## 3. New format, two seeds and exact registered-product commitment

[EXECUTED source] The new packed magic is `RINGSSM2`, format_version=3. Every A, registration, key, public bundle and ciphertext header requires `seed_policy="honest-dual-seed-384-qrom-v1"` and integer `seed_bits=384`. The new expander accepts exactly 48 bytes and has protocol tag `ring-seed-semantic/public-rows/v2`. The old 32/64-byte inputs and older container versions are rejected. The frozen predecessors are not altered.

[DERIVED A stage] Init first validates the semantic registry, draws the independent 32-byte setup ID, then draws one 48-byte A seed. Its binding hashes the canonical common A header (including the fixed registry digest, profile, parameters, setup ID, format and seed policy) with domain `ring-semantic-A-384-v1`. The A container has no coefficient payload. Its complete canonical file hash binds all recipient registrations and keys. Public A reconstruction still yields w=64 independent ring rows in the ideal-oracle model, subject to the same finite expander cap.

[DERIVED registration stage] Each of the 16 recipient processes reconstructs A, privately samples only its own finite Gaussian row, and publishes its product. Finalize rejects missing or duplicate coordinates and checks their A/profile/registry context. It forms a commitment to the exact ordered registered-product payload: the canonical context is length-prefixed and includes coordinates 0..15, N, q, semantic registry digest, A-file digest and the mandatory seed policy; the payload uses the unchanged 289-bit canonical residue packing. `products_sha256` is the SHA256 of this domain-separated context and exact payload.

[DERIVED missing stage] Only after that commitment is fixed does finalize sample one independent 48-byte missing seed. Its binding hashes the A-file digest, semantic-registry digest and products commitment with a separate `ring-semantic-missing-384-v1` domain. The public bundle contains those seed descriptors plus only the 16 explicit product rows. It samples no absent-recipient secret, and finalize does not expand the absent public rows. Encryption reconstructs each absent row directly from the public XOF and discards it after its scalar inner product. No rejection-until-a-favorable-seed or grinding step is used.

[DERIVED one-file public bundle] The public header includes exactly the seeded descriptor fields `seed_policy`, `seed_bits`, `a_seed`, `a_binding`, `missing_seed`, `missing_binding`, and `products_sha256`, plus the profile/parameters/setup ID, semantic registry digest and A-file digest. Loading the bundle reconstructs the canonical zero-payload A descriptor and verifies its digest, then recomputes the registered-product commitment. This makes the descriptor/registry chronology explicit without a second products file. The journal additionally commits this full finalized descriptor into its genesis and request identity.

[DERIVED credential binding] Keys are created before the missing seed and therefore bind the A descriptor, semantic registry and mandatory policy. They cannot already bind a later public-file digest. Ciphertexts additionally bind the final public bundle hash. Same-context scalar updates require all those ciphertext bindings to agree. A recipient key is still a direct per-input projection capability on any retained valid ciphertext under that setup; the key is not cryptographically limited to journal-accepted states or one delivery ID.

## 4. QROM theorem specialization and concrete-XOF boundary

[SOURCE/DERIVED] `../ring_seed_qrom_successor/THEOREM.md` and its manifest provide the two full-block primary-theorem comparison, exact finite-table kernel, common quantum channel, and finite-independent removal of the fallback oracle. The new domain prefixes and fixed semantic registry are deterministic public context. The canonical indexed addresses remain injective and family-separated; their rows/chunks and rejection algorithm are unchanged. The A seed is fresh after that fixed context, and the missing seed is fresh after the exact recipient-product commitment. Thus the same proof applies with lambda_A=lambda_M=384.

[DERIVED] With Q_0,Q_1≤2^64 quantum queries before the respective seed disclosures, its exact two-bit-world programming term is

```text
2 beta_Q ≤ 2^-158 + 2^-319.
```

[DERIVED] For the unchanged finite parameters and up to T=384 valid fresh inputs, the inherited non-Ring-LWE terms are below 2^-168. Accounting for the message-basis transform and the explicit oracle simulator in the exact reduction resource bound gives the conditional theorem

```text
Adv_semantic-seeded-QROM < 768 epsilon_QR + 2^-158 + 2^-168 + 2^-319.
```

[DERIVED] For a six-input experiment the computational multiplier is 12 with its corresponding six-input reduction resource budget; the same displayed statistical upper terms remain conservative. Successful execution is not evidence for epsilon_QR. The full theorem continues to require honest independent credentials, a fixed pre-setup coalition, and the same allowed nonuniform/quantum advice class, independent of fresh oracle/setup coins.

[DERIVED resources and limits] The exact hypothesis is QPT decision Ring-LWE with one uniform shared ring secret, w=64 ring samples and ideal power-basis width-2^10 coefficient errors, plus the priced finite-law correction. Its public matrix is structured. The oracle-free wrapper's finite-field lanes, table scans, large coefficient tape, and public field-modulus advice remain part of the assumption's resource budget. This successor does not turn a small statistical term into certified security or reuse a smaller-resource estimator result as a theorem.

[OPEN concrete implementation] The executable expansion is SHAKE256 with OS randomness. Applying the QROM result to that fixed XOF is an explicit heuristic instantiation, not a theorem from hidden-seed PRG security. There is no certified PQ security, concrete-SHAKE reduction, malicious seed/registry/grinding guarantee, secure-erasure or constant-time claim. No new Gaussian, modulus, Delta, or ring arithmetic substitution is made to obtain the smaller bundle.

## 5. Shared continuing-state semantics

[SOURCE/DERIVED orchestration contract] The separate journal successor owns the one fresh six-teach/two-expiry service run. Its public evaluator recomputes each full `acc+fresh−old` candidate before the journal atomically accepts the current-parent transition. Its recipient-specific delivery path executes only after public closure and uses explicit delivery identities; retained ordinary keys remain broader capabilities as stated above. These local continuity/integrity and visibility controls are not a succinct proof or history-bound cryptographic release theorem.

[EXECUTED shared completion] The single fresh seeded001 service run passed: six accepted updates, two exact expiries, 16 identified recipient deliveries, 32 scalar scores and 16 decisions matched their plaintext reference. Public closure preceded every recipient query. The run took 202.715739 seconds; the final issuer public bundle is 9,471,117 bytes. REPORT.md and RUN.json attribute the complete measurements and public packet pins. No old private key, old setup, or old cryptographic workload was replayed by this backend package.
