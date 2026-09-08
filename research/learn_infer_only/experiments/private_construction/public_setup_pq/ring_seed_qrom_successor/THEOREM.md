# An honest-seed quantum-oracle successor for the two programmed namespaces

[DERIVED, 2026-09-08] The frozen seeded ring transport has an honest-setup QROM reduction through the **single common wrapper** defined below. The endpoint comparison uses a primary adaptive-reprogramming theorem on two independent large-output oracles. The intermediate Gaussian setup and mask tables are only inputs to a common quantum channel; they are never asserted to remain random-oracle tables. The result is conditional on the exact power-basis QPT Ring-LWE problem at explicit reduction resources. It does not instantiate SHAKE256 or certify numerical post-quantum security.

## 1. Primary theorem actually used

[SOURCE: full game, theorem and proof read] Grilo–Hövelmanns–Hülsing–Majenz, [Tight adaptive reprogramming in the QROM](https://eprint.iacr.org/2020/1361), local PDF SHA256 `a185688a1ffd8352f433033545a73c9698539df92de517dbea29342c5fe56e53`. Figure 2 and Theorem 1 pp.6–7 permit classical adaptive position distributions and fresh uniform replacement outputs. Theorem 6 §5.2 proves the single-stage case; Appendix A gives its composition and side-information extension. The theorem is information-theoretic for finite domains/ranges and includes quantum prequeries and subsequent position disclosure.

[SOURCE formula, distinguishing-gap convention] If a sampled position has expected maximum point probability at most p and there are q prior quantum queries, a single reprogramming contributes at most

```text
g(q,p) = sqrt(q p) + (q p)/2.
```

[DERIVED source scope] This is reprogramming to a **fresh independent uniform output**, not a theorem authorizing arbitrary prescribed correlated outputs. We use it only for the two uniform-target endpoint experiments. An explicit rejection-table kernel then identifies that endpoint with a wrapper receiving uniform A and missing products. Statistical data processing handles all other target distributions.

## 2. Game, chronology and finite query interface

[DERIVED] Use the same honest fixed profile, fixed full-rank policy/basis B, and fixed coalition `J⊆{0,...,r−1}` as the classical successor. The adversary is QPT and makes quantum queries to the public XOF oracle, but registration, credential delivery, challenge pairs and encryption are classical interfaces. Each of its at most T fresh pairs satisfies `Y_J x0=Y_J x1`. It may retain quantum state. Any permitted quantum advice is independent of the fresh oracle, setup/secret coins and challenge bit, and the exact Ring-LWE hypothesis allows the same advice class; one copy is passed to a target reduction.

[SOURCE/DERIVED exact chronology] The actual descriptor contains an honestly sampled 32-byte A seed and an independent 32-byte setup ID. The A binding hashes all descriptor fields except that seed. All r honest independent recipient rows and their public products are generated after the descriptor. The exact registry is fixed and may be revealed before the missing seed. Only then is a separately fresh 32-byte missing seed sampled; its binding hashes the descriptor and registry digests. Each corresponding table is installed immediately before its seed is revealed. This matches `../ring_seed_transport/seed_transport.py` and the classical successor §2.

[DERIVED] Let `Q_0` bound the adversary's oracle queries before A-seed disclosure and `Q_1` those before missing-seed disclosure. These are bounds valid under the comparison hybrids. `Q_0≤Q_1≤Q` for total Q queries; a query in superposition over families is counted once in each applicable stage's upper bound. We do not use the classical disjoint-family counting shortcut or a classical transcript search for prior hits.

[DERIVED finite oracle model] Fix an upper bound a_max on input bytes and an upper bound ell on requested output bits; both are polynomial in the QPT circuit's size. Inputs are length-delimited and padded injectively into n-bit strings. A query coherently supplies an input and requested prefix length; a fixed ell-bit answer register is XORed on the requested positions only. Prefix requests of different lengths share one underlying ell-bit oracle value. Take ell at least the implementation's 303,104-bit chunk length. This finite model covers every bounded execution and longer-prefix recomputation within its declared limit; an infinite-output quantum gate is not an implementation primitive.

[DERIVED transcript boundary] The adversary receives the public descriptors, registrations, exact registry, public manifest, ciphertexts and deterministic arithmetic metadata, its own coalition keys, and the quantum oracle interface. The selected challenge plaintext/issuer filename, private sampling tapes and timing/memory side channels are not disclosed. No malicious setup, adaptive corruption, artifact substitution, decryption oracle or integrity claim is added. Context SHA256 is the same deterministic public function in both worlds; this honest-artifact privacy proof does not need to assume its collision resistance or infer authenticity.

## 3. Exact decomposition into blocks and residual tails

[DERIVED] Fix the repaired profile and the exact canonical address format from the frozen expander. Put

```text
K=1024, c=ceil(4N/K)+16, M=Kc,
t=ceil(ceil(log2 q)/8), L_chunk=8Kt.
```

[DERIVED] Decompose the ideal byte oracle into three mutually independent functions:

```text
G_A : (seed,binding) -> all w*c chunk prefixes, each L_chunk bits;
G_M : (seed,binding) -> all (d−r)*c chunk prefixes, each L_chunk bits;
R   : original address -> ell residual bits.
```

[DERIVED] A canonical address with the fixed N,q, family `A`, row 0 through w−1 and chunk 0 through c−1 takes its first L_chunk bits from the indexed slot of G_A. The corresponding `missing-P` address uses G_M with row r through d−1. The two families are disjoint. Its bits beyond L_chunk come from R at that original address. All other addresses use R in full. Unused residual prefix bits are ignored. Distinct block slots and residual bits are independent, so this defines exactly the same ideal oracle law as independent random strings at every address. In particular, arbitrary alternate contexts, rows, chunks beyond the cap, parameter encodings and longer output tails are not silently discarded.

[DERIVED coherent parsing] The length-prefix fields, fixed family/parameter checks and index bounds can be parsed reversibly. Invalid or ungrouped inputs follow the residual branch. No address or requested length is measured. The decomposition is over disjoint **bits of oracle values**, not a claim that a structured ring matrix is a uniform scalar matrix.

[DERIVED one-query routing] An ordinary XOR query to H can be simulated using one query to each relevant independent block oracle and one to R. Apply Hadamard gates to the caller's answer register, obtaining Fourier label z. Reversibly route the requested label bits for a block into a zeroed full-block label register; all unrequested positions receive zero. Hadamard that register, make one full-block XOR query, and undo the Hadamards and routing. The ancilla returns to zero and the caller acquires exactly the phase of its requested block bits. Residual bits are handled the same way. A final Hadamard on the caller's answer gives the required XOR query. Ignored labels correspond to |+> and do not require computing and uncomputing the black-box oracle twice.

[DERIVED] This circuit establishes a query-count reduction even for superpositions of addresses, families and prefix lengths. Its large workspace is real and priced below. The information-theoretic reprogramming theorem permits this large-output oracle; it does not make that oracle a unit-cost hardware operation.

## 4. Two endpoint reprogrammings and their loss

[DERIVED endpoint hybrid] First replace the A block at `(s_A,b_A)` by a fresh independent uniform block immediately before revealing s_A. Then replace the missing block at `(s_M,b_M)` in the same manner immediately before revealing s_M. The replacement blocks are full independent bit strings, including all rejected candidates, high padding, unused chunks and abort possibilities. The source theorem applies in this uniform endpoint experiment.

[DERIVED entropy] At the A stage, the nonce/context/binding are fixed before the independently uniform seed is selected. At the missing stage, the complete registry, binding and prior quantum interaction are fixed before its independently uniform seed is selected. For seed lengths lambda_A and lambda_M, the corresponding position distributions have maximum probabilities `2^-lambda_A` and `2^-lambda_M`, even if the fixed binding was adaptively determined by the prior interaction. No entropy of SHA256(registry) is credited.

[DERIVED source application without an unnecessary cross-family query] Apply the single-stage Theorem 6 twice. For the A comparison, G_A is the source oracle and the independent G_M and R are part of the source distinguisher's other computation. For the missing comparison, the already handled G_A and independent R are other computation, and G_M is the source oracle. The one-query routing costs at most one target-family source query per adversarial H query. An honest A-block read after its reprogramming is not a query to G_M, so it does not add a spurious +1 to the missing-stage count. Each comparison permits arbitrary subsequent computation and oracle queries. Thus

```text
beta_Q = g(Q_0, 2^-lambda_A) + g(Q_1, 2^-lambda_M).
```

[DERIVED] The auxiliary source distinguishers may be unbounded, as the cited theorem is information-theoretic; other independent random functions need not be efficiently materialized in that proof. The actual QPT Ring-LWE reduction is instead the single finite-independent wrapper in §6. Confusing these two simulation costs would leave an external ideal oracle inside the computational assumption.

[DERIVED relation to the supplied targets] After a fresh block is installed, read it classically and extract all its rows with the exact capped expander. Conditional on success, its accepted residues are independent uniform field values. The classical successor's finite-table kernel gives the precise reverse joint law: supply independent uniform target rows, sample base words, and overwrite only the first N accepted low words per row. Averaging the target rows restores the **entire** fresh uniform block, not merely its accepted outputs. On cap failure, the unchanged table and unused independent target are retained. The kernel therefore identifies this fresh-block endpoint with the target-driven wrapper, up to the charged failure behavior, while preserving every subsequent quantum recomputation value.

[DERIVED cap term] For one row let `f_exp=Pr[Binomial(M,q/2^ceil(log2 q))<N] <2^-5461`. There are only `R_pub=w+d−r` distinct public rows in one setup. Their cap failures have total probability at most `R_pub f_exp`. Repeated encodes and recomputations reuse those same oracle values. Comparing full unconditioned games charges failure regardless of when a CLI would report it; no arbitrary success-conditioned regularity theorem is used.

[DERIVED wrapper endpoint bound] For either privacy bit b, the final distinguishing gap between the real honest-seed QROM experiment and the wrapper on the bare uniform-setup game is at most

```text
beta_Q + R_pub f_exp.
```

[DERIVED] This is a quantum distinguishing bound, not a classical bad-query event with probability Q/2^lambda. There is no measurement of prequery support and no claim that quantum prequery state is unchanged exactly. Two privacy-bit worlds contribute twice this bound, once for the whole experiment, not once per ciphertext.

## 5. One common quantum wrapper for all statistical and Ring-LWE hybrids

[DERIVED algorithm W_Q] Start with an independent fallback function on the original finite address/output domain. Receive the bare game's complete target tuple but keep each part hidden until its public stage. Before each seed disclosure, install the finite-kernel tables for that stage as explicit classical overlays. Queries thereafter evaluate the overlaid prefixes and fallback tails coherently. Reveal registrations/coalition keys in the honest order, compute the exact registry and digests, and forward challenge pairs to the bare game while adding the deterministic seeded file metadata. No query is measured or logged as a list of classical queried addresses. Previously returned quantum states are retained; only the subsequently available function changes.

[DERIVED common-channel claim] For fixed target tuple, fallback function and kernel coins, every overlaid query is a well-defined reversible XOR function. The full adaptive interaction is therefore one CPTP map of those inputs and the adversary's independent initial state. A TV bound delta on the complete classical target tuple remains a trace-distance bound at most delta on the resulting interaction. This remains true when table entries are correlated with retained products, registry digests or the adversary's eventual challenge history. It never requires those intermediate tables to be independently random.

[DERIVED] In the actual endpoint A is uniform and missing products are independent uniform given the honest registry, so §4 establishes the QROM comparison. In the Gaussian setup comparison, absent rows are proof-only Gaussian-derived products. In the augmented-mask comparison, the complete `(A,u,P,mask,Z_J)` tuple changes together; any changed unexposed registered products also change the registry and its binding through the same wrapper. These are precisely applications of the one common channel. A replaced row's secret is not retained next to its independently replaced syndrome.

[DERIVED] Consequently the existing fixed-coalition QPT Ring-LWE proof, with its finite-Gaussian correction, applies to W_Q as its adversary. This addresses both A and missing rows. Merely assuming a seeded Ring-LWE instance would not establish this quantum auxiliary-information and missing-row simulation step.

## 6. Removing the external oracle from the QPT reduction

[SOURCE/DERIVED] The primary finite-independence results and a full coherent implementation are pinned in `quantum_simulation/SIMULATION.md`. Zhandry 2012/076 Theorem 3.1 gives quantum moment equality; §6/Theorem 6.1 applies finite independence to oracle removal. Boneh–Zhandry 2012/606 Lemma 6.4 counts c classical plus q quantum queries with c+2q-wise independence. Their application here is to the independent fallback function, not to the explicit correlated overlay.

[DERIVED finite implementation] Let n be the injective finite address width and ell the fixed maximum output width. Choose a power-of-two `m≥max(n,ceil(log2 k),1)` and a public certified irreducible polynomial defining F_(2^m). Map each address injectively into that field. For `s=ceil(ell/m)` independent output lanes, sample a degree-(k−1) polynomial with independent uniform field coefficients, concatenate the lane outputs, and truncate to ell bits. This is k-wise independent. A fixed public irreducible modulus can be included in the finite simulation parameters/classical advice; its construction is not hidden inside an unbounded sampling loop. The Ring-LWE assumption must permit that same advice class. This establishes the stated nonuniform-advice reduction; a strictly uniform field-construction version is not silently supplied.

[DERIVED quantum calls] A phase-kickback mask suppresses fallback output bits covered by an explicit table, and the table supplies their phases directly. Each adversarial query therefore needs at most one fallback oracle query. Honest expansion uses only its installed table entries; no honest fallback evaluations are needed. With at most Q total adversarial queries, take `k=max(1,2Q)`. Moment equality then removes the independent ideal fallback with **zero distinguishing error**. Adaptive classical choices of seeds, overlays and registry are ordinary operations within this algorithm and do not invalidate the query-count theorem.

[DERIVED resources] Store ksm random field bits and evaluate the lane polynomials reversibly. Direct Horner evaluation takes O(s k m^2) elementary bit operations for schoolbook field arithmetic; an XOR oracle circuit computes and uncomputes every lane value, so there are two arithmetic passes even though it is one oracle query in the information-theoretic accounting. A direct scan of all explicit chunk entries supplies the overlay without an assumed constant-time quantum RAM. The child specification prices address comparisons, prefix masks, table bits and workspace. These are polynomial bounds in the declared finite parameters and Q, potentially enormous in concrete terms. The exact QPT Ring-LWE epsilon must include them.

[DERIVED] No ideal Gaussian is sampled inside this bounded reduction. The previous finite G_K/G_e algorithms and capped private-uniform simulation apply unchanged. Finite independence introduces no CSPRNG assumption; its polynomial coefficients are independent bits. The selected field modulus is public, whereas these fresh function coefficients are reduction-private coins. No sampler, quantum circuit or cryptographic workload is executed by this package.

## 7. Full theorem and implemented-seed price

[DERIVED notation] Let `L=wN`, `nu_K,nu_e<68·2^-256`, `delta_G,h(k)=min(1,delta_h(k)+hLnu_K)` for h>0 and zero for h=0. Let `C=L(8sigma_K)(8sigma_e)`, `S_G=min(1,dC/(2F+1))`, and `U_red=T(N+d)`. These are the exact finite-law bounds established in the classical successor, now applied through W_Q. Let epsilon_QR bound the exact ideal-error **power-basis ring** decision problem against the resulting bounded QPT reductions with the same permitted advice. Coefficient-expanded matrices are structured; no scalar-LWE replacement or numerical hardness is inferred.

[DERIVED theorem, honest fixed coalition] For at most T adaptive valid classical challenge pairs,

```text
Adv_seeded-QROM ≤ 2 delta_G,d−r(1)
 + 2T [epsilon_QR + L nu_e + S_G + delta_G,d−j(2)
       + 2 U_red·2^-512]
 + 2 [beta_Q + (w+d−r) f_exp].
```

[DERIVED] This is our QROM successor conditional on the primary reprogramming theorem, the previously derived structured regularity and finite-law construction, and the exact QPT Ring-LWE resources above. The full public seed transcript and oracle recomputation are inside the model. There is no additional factor T on beta_Q.

[SOURCE/DERIVED actual point] The unchanged implemented profile uses `N=16384,w=64,d=577,r=16,T=384`, `sigma_K=2^25,sigma_e=2^10,F=2^247`, and `q=4294967767·2^256+1`, with **256-bit seeds at both stages**. At `Q_0,Q_1≤2^64`, the exact two-bit-world programming upper bound is

```text
2 beta_Q ≤ 2^-94 + 2^-191.
```

[DERIVED] The other non-Ring-LWE terms, including caps, are below 2^-168 at this fixed point. Therefore a readable, deliberately conditional bound is

```text
Adv_seeded-QROM < 768 epsilon_QR + 2^-94 + 2^-168 + 2^-191.
```

[DERIVED] The `2^-94` term is a reduction loss at the stated quantum query budget, **not a 94-bit or 128-bit security claim**. QPT Ring-LWE plus QROM does not imply concrete SHAKE256 security. The quantum loss is much larger than the classical successor's `2Q/2^256` term and must not be replaced by it.

## 8. Future seed lengths and actual simulation scale

[DERIVED parameterized corollary] With fresh lambda-bit seeds at both stages and `Q_0,Q_1≤2^64`,

```text
2 beta_Q ≤ 2^(34−lambda/2) + 2^(65−lambda).
```

| Both seed lengths | Quantum programming term at 2^64 prior queries | Encoding status |
|---|---|---|
| 32 bytes / 256 bits | `2^-94 + 2^-191` | Actual frozen transport |
| 48 bytes / 384 bits | `2^-158 + 2^-319` | Future scheme/format; unsupported by current seed validation |
| 64 bytes / 512 bits | `2^-222 + 2^-447` | Future transport format; expander alone accepts 64-byte seeds |

[DERIVED] Each row also retains the same finite ring/sampler losses and epsilon_QR at its actual resources. These are parameterized mathematical alternatives, not implemented mutations or a claim that seed length alone certifies security. Honest sampling and the two-stage registry chronology remain necessary.

[DERIVED block cost] Each chunk is 37,888 bytes; each row's capped table is 3,031,040 bytes. The A block is 193,986,560 bytes (1,551,892,480 bits). The missing block is 1,700,413,440 bytes (13,603,307,520 bits). The simple block-query routing thus uses a largest block label register of over 13.6 billion qubits plus ancillary registers. It incurs no multiplicative row/chunk factor in the reprogramming loss, but its output/workspace cost is explicit. This is an information-theoretic proof construction, not a proposed physical oracle service.

[DERIVED computational cost] The single ordinary-domain wrapper instead stores the 625 finite tables in 1,894,400,000 classical bytes and evaluates their controlled phases reversibly. There are 50,000 chunk prefixes. A no-QRAM implementation scans them using canonical address comparisons and masked output operations; field evaluation and this scan are charged for every quantum query. Source query counts do not hide the coefficient storage `max(1,2Q)s m`, two arithmetic passes per lane/query, or the Q-fold gate cost. For the illustrative input-byte cap 466 and ell=303104, n=3737, m=4096 and s=74 suffice for k≤2^4096. The coefficient tape has `606208 Q` bits, already 11,182,563,831,435,319,866,032,128 bits at Q=2^64. Larger adversarial input/output bounds require the corresponding parameters. This package does not assign epsilon_QR from a smaller-resource lattice estimate.

## 9. Remaining boundary

[DERIVED] The finite rejection kernel and common quantum channel close the honest-seed namespace programming obligation in this model. A constructor still creates no absent recipient secret. Proof-only all-row keys remain a comparison device, and actual recipients retain separate rows.

[OPEN] A maliciously selected or ground seed can remove the source theorem's fresh min-entropy premise; a malicious registry also changes the independent credential game. Concrete SHAKE256 has fixed, unprogrammable outputs. Neither a hidden-seed PRG argument nor a seeded Ring-LWE hypothesis alone proves its replacement by this QROM. Those extensions, physical side channels and semantic learner integration are separate tasks. All frozen implementations and the existing ideal-uniform learner are untouched.
