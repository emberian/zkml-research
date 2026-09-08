# A classical programmable-ROM reduction for both seeded public-row families

[DERIVED theorem, 2026-09-08] The frozen `ring_seed_transport` admits a concrete classical programmable-random-oracle reduction to the uniform-setup fixed-coordinate ring construction. The reduction programs **both A and the missing recipient products**, with their exact chunk rejection tapes and subsequent oracle recomputation. It uses the implementation's honest chronology: fresh A seed, honest recipient registrations, fixed registry, then a separately fresh missing-row seed. This closes that joint simulator obligation in the model stated here. It does not prove a concrete SHAKE256 instantiation, quantum-oracle security, or security under adversarial setup selection.

## 1. Exact game and oracle model

[SOURCE: frozen implementation] `../ring_seed_transport/seed_transport.py` implements `init`, `register`, `finalize`, and `encode`. `../ring_seed_transport/expansion/public_expander.py` specifies the indexed SHAKE256 expansion. The source hashes and primary mathematical inputs are pinned by this package's manifest. No prior package is modified.

[DERIVED game] Fix the validated profile, the public invertible basis B, and a coalition `J ⊆ {0,...,r−1}`, `j=|J|`, before setup. All registered recipients sample independently and honestly. The adversary can make classical oracle queries before and between every public protocol step, retain all public files and recomputation answers, and obtain each row `z_i`, `i∈J`, when that recipient registers. All other recipient rows remain private. It receives at most T adaptively chosen left/right fresh encryptions with `Y_J x0=Y_J x1` for each pair. This is difference-of-output-probabilities advantage, not success probability minus one half. Signed combinations and exact expiry are arbitrary public postprocessing subject to the separate correctness range contract.

[DERIVED public transcript] Include the A descriptor, every published registration, the exact packed registry, the public manifest, ciphertexts and their deterministic header/lineage metadata, public outputs of authorized arithmetic, and all oracle inputs/answers. The reference chronology may reveal the registry before the missing seed, so it covers that intervening query interval. The selected challenge plaintext and its issuer input filename are not disclosed. Honest private sampling tapes, secret-dependent running times, operating-system state, memory traces, arbitrary file replacement, decryption oracles, malicious registrations and adaptive corruptions are not interfaces in this game. Existing execution receipts and readable public test-fixture inputs are performance observations, not an operational secrecy or side-channel theorem.

[DERIVED ROM] Replace SHAKE256 by an oracle H assigning an independent infinite random byte string to each input byte string. Queries request a finite prefix; repeated, shorter and longer requests are mutually consistent. In the reduction H is simulated and its as-yet-unexposed values can be programmed. The adversary is classical probabilistic polynomial time, with bounded total query-output length. Fixed classical nonuniform advice may be carried through once if the Ring-LWE hypothesis permits the same advice class. No superposition queries or QROM theorem are asserted.

[DERIVED hashing boundary] The context/header SHA256 functions are executed as the same deterministic functions in both experiments. No collision-resistance assumption is needed for this **honest, fixed-artifact** privacy reduction: contexts and digests are common functions of the same complete input tuple. The raw fresh seed also appears explicitly in the XOF address. This observation does not supply artifact authenticity or security against substituting a different registry with the same digest.

[DERIVED randomness boundary] In this theorem public seeds and private sampling bits are independent unbiased bits. The finite Gaussian law G is exactly the frozen finite sampler's output law, including threshold rounding and fallback. The implemented native screening preserves that law. The concrete use of OS randomness remains an entropy/implementation assumption; no long independent random tape is statistically derived from a short CSPRNG seed here.

## 2. The exact two-stage address chronology

[SOURCE/DERIVED] `init` draws independent 32-byte `setup_id` and A seed `s_A`, and publishes canonical JSON containing the validated parameters, profile, policy, recipients, setup ID, and seed. Define

```text
a_context = all descriptor fields except seed
b_A = SHA256("ring-A-context-v1\0" || canonical(a_context))
A_j = Expand(s_A,b_A,"A",j,N,q),  j=0,...,w−1.
```

[SOURCE/DERIVED] Each recipient independently generates `z_i←G_K^(wN)`, publishes `P_i=<A,z_i>`, and retains its own row. Its registration binds the exact descriptor digest and setup ID. Finalize assembles the exact ordered registry bytes and its hash `h_R`, then samples independent 32-byte `s_M`. With descriptor hash `h_A`, it publishes

```text
b_M = SHA256("ring-missing-context-v1\0" || h_A || h_R)
P_i = Expand(s_M,b_M,"missing-P",i,N,q),  i=r,...,d−1.
```

[DERIVED] The second seed is sampled **after** the registered products and all intervening oracle activity are fixed. No unpredictability claim about SHA256(registry) is used. A simulator reserves each namespace immediately before disclosing that seed. Although the actual `init` and `finalize` do not expand their rows at publication, lazy oracle sampling makes pre-reserving fresh addresses distributionally valid. Revealing a seed and later deciding what values to program would not suffice.

[SOURCE/DERIVED exact address] Write `lp(v)=len(v).to_bytes(4,"big") || v`. Every used address is

```text
lp("ring-seed-transport/public-rows/v1") || lp(seed) || lp(binding)
|| lp(family) || row_index_BE64 || N_BE64 || lp(q_minimal_BE)
|| chunk_index_BE64.
```

[DERIVED] These canonical addresses are injective in the listed fields. The A and missing families are distinct even if their seeds or binding digests coincide. Adversarial inputs need not be canonical; only inputs exactly matching an eventual used address can conflict with programming. Queries at larger chunk indices or other addresses remain ordinary oracle queries.

## 3. Full rejection-tape programming, including unused bytes

[DERIVED] Put `b=ceil(log2 q)`, `t=ceil(b/8)`, `K=1024`, `c=ceil(4N/K)+16`, and `M=Kc`. Each raw word has `8t` bits, of which the low b bits are the candidate and the remaining bits are ignored padding. A row is its first N candidates below q, or it fails when its M candidates are exhausted. Let

```text
alpha = q/2^b ≥ 1/2
f_exp = Pr[Binomial(M,alpha)<N]
      ≤ 2^N(3/4)^M < 2^-5461.
```

[DERIVED finite kernel] For target `u∈F_q^N`, sample all M raw words independently. On success, overwrite only the low b bits of the first N accepted words with the N target residues. Retain every acceptance position, rejected candidate, ignored high bit, later accepted word, unused final-chunk suffix, and later capped chunk. On cap failure change nothing and retain the failure. Every additional oracle suffix remains independent and prefix-consistent. The child note `transcript_programming/KERNEL.md` gives the complete proof.

[DERIVED exact law] For a fixed target u and complete output table t, the probability density relative to an independent uniform raw table is 1 on failing tables, `q^N` on successful tables extracting u, and zero on other successful tables. There are exactly `q^N` preimages of a successful table, obtained by varying its overwritten accepted low words. Averaging a uniform target therefore restores the entire independent-uniform table law pointwise. On success, target and table are correlated exactly by extraction. On failure an unused uniform target can be attached independently. This is not the false claim that a public seed and an independent target remain independent of the programmed table.

[DERIVED] For any nonuniform or correlated targets the same algorithm is still a well-defined common randomized kernel. Thus a full joint target-distribution distance δ remains at most δ after appending the seeds, exact registry, full programmed oracle and arbitrary later interaction. Its ideal-table identity is used only in the real uniform-target comparison. Its data-processing property does not require uniform targets in the Gaussian or augmented-mask hybrids.

## 4. One public wrapper around the uniform-setup game

[DERIVED compiler W] Given the bare public tuple `(A,P_0,...,P_(d−1))` and coalition rows from the uniform absent-master game, run the seeded adversary and lazily simulate all unrelated oracle queries. The bare tuple may have been generated in advance; keep it hidden until its corresponding public step.

1. After the adversary's pre-setup queries, draw the descriptor coins. Check whether an already queried address conflicts with any used A address. On conflict mark `Bad_pre`. Otherwise apply the kernel independently to the w target rows of A and reserve their full namespaces before revealing the descriptor.
2. Publish each already supplied honest registered product in the exact registration format and reveal only the corresponding coalition credential. Answer intervening oracle queries from the reserved table or ordinary lazy oracle. Form the exact registry. Pre-sampling honest independent recipient coins rather than delaying them until registration changes no view.
3. After the registry and intervening queries are fixed, draw the fresh missing seed. Check for conflicting prior missing-family addresses. On conflict mark `Bad_pre`; otherwise kernel-program the d−r supplied missing targets before disclosing the public manifest.
4. Forward valid fresh challenge pairs to the bare game; format the resulting ciphertexts with the seeded public-file hashes and deterministic lineage metadata. Continue answering arbitrary recomputation consistently. All public encryption used by the adversary itself agrees because successful expansion returns the supplied A and P.

[DERIVED] Kernel cap failure marks `Bad_cap`. The compiler may stop with a fixed output on either bad event. This is a coupling argument on the **unconditioned** experiments: on the complement of bad, the complete views match. On bad, we charge its probability, including any difference in when the actual CLI emits a failure. We do not silently replace the actual failure transcript by a success-conditioned law.

[DERIVED fresh-seed bound] Let `Q_A` bound distinct queried input addresses in the A family before A-seed disclosure, and `Q_M` bound distinct queried addresses in the missing family before missing-seed disclosure. At each draw the new 256-bit seed is independent of the existing transcript. Each canonical prior input guesses at most one such seed. Consequently

```text
Pr[Bad_pre] ≤ (Q_A+Q_M)/2^256.
```

[DERIVED] This coarse bound needs no multiplier for row or chunk count. The two families are disjoint, so `Q_A+Q_M` is at most the total number Q of adversarial oracle input queries, when each query is counted in its own family. Counting all prior queries at each stage instead is also safe but gives the looser `2Q/2^256`. A query made after disclosure is harmless because its namespace was already reserved. A shorter prefix query made before disclosure counts as a conflict, even if its particular answer happens to be compatible.

[DERIVED cap bound] Only `R_pub=w+d−r` distinct rows are used by one setup. Repeated registrations, encodes, recipient recomputations and expiry do not redraw the oracle. Thus

```text
beta_wrap = (Q_A+Q_M)/2^256 + (w+d−r) f_exp
TV(real seeded ROM world b, W(bare uniform world b)) ≤ beta_wrap.
```

[DERIVED proof] In the bare real game A is uniform, independently of the fresh A descriptor context. Registered keys are independent G rows. Missing targets are independently uniform conditional on A, all actual rows, their products, and the exact registry. The kernel's uniform-target theorem applies in that order. The lazy oracle and fresh-seed coupling handle all earlier queries; deterministic serialization and later interaction preserve the equality off bad. Honest registration prefixes add no secret-dependent selection of A or missing products. This proves the displayed complete-view comparison.

[DERIVED consequence] For every seeded adversary D there is a bare-game adversary `W[D]` with

```text
Adv_seeded-ROM(D) ≤ Adv_uniform(W[D]) + 2 beta_wrap.
```

[DERIVED] This compiler is applied **once to the whole experiment**. It is then the adversary to which the bare ring proof is applied. Its consistency therefore survives the setup and challenge hybrids as a common channel. No oracle value is overwritten after disclosure, and no new seed-guess or cap factor is multiplied by T. This is the required missing-row programming argument; assuming only a seeded Ring-LWE challenge would leave it out.

## 5. Exact finite-Gaussian regularity and the Ring-LWE reduction

[SOURCE/DERIVED] Let `L=wN` and let `nu_K,nu_e` bound the coefficient-level distances of the actual finite Gaussian laws from `D_(Z,sigma_K)` and `D_(Z,sigma_e)` with mass proportional to `exp(−pi k²/sigma²)`. The frozen finite sampler proves `nu_K,nu_e < 68·2^-256`; it outputs only `|k|<8sigma`, including zero fallback. Let `delta_h(k)` be the independently derived full joint structured-ring bound in `../ring_candidate/RING_REGULARITY.md`, with its prime, complete-splitting, width, ideal/CRT and dimension hypotheses unchanged.

[DERIVED finite-key lemma] For k uniform ring equations and h replaced rows,

```text
delta_G,h(k) = min(1, delta_h(k) + h L nu_K),   h≥1;
delta_G,0(k) = 0.
```

[DERIVED proof] Replace only the h unexposed finite-law rows by ideal Gaussian rows, costing at most `hL nu_K`. Apply the ideal full joint regularity lemma to their products, retaining every other row with its original finite law and its products as a common channel of the uniform matrix. The uniform comparison side has no secret for a replaced row, so no second Gaussian replacement term is needed. For setup retain all r actual rows and take `(h,k)=(d−r,1)`. For the augmented mask retain only `Z_J` and take `(h,k)=(d−j,2)` with matrix `[A;u]`. A replaced row's secret is never retained alongside its independently uniformized syndrome. The wrapper is subsequently applied to the full tuple, including any changed registered public products and their recomputed registry digest. There is no conditioning on a chosen public transcript.

[DERIVED bounded smudge] Set `BK=8sigma_K`, `BE=8sigma_e`, `C=L BK BE`, and

```text
S_G = min(1, d C/(2F+1)).
```

[DERIVED] For all finite-law keys and errors, `|const(<z_i,e>)|≤C` deterministically. Translating d independent floods uniform on the integer interval `[-F,F]` therefore costs at most S_G, retaining even all Z and the original error. There are no ideal-Gaussian tail events to add to this finite-law smudge step. The finite laws also make the corresponding coefficient-bound correctness event deterministic in the abstract arithmetic model.

[HYPOTHESIS exact classical Ring-LWE] Let epsilon_R be an upper bound, at the actual resources of the bounded reductions below and the allowed classical advice class, for distinguishing

```text
(A, A s+e)  from  (A,u),
A,u independent uniform in R_q^w; s uniform in R_q;
e has L independent ideal D_(Z,sigma_e) power-basis coefficients.
```

[DERIVED] This is a uniform shared-secret **ring** assumption, not uniform scalar LWE on a coefficient-expanded structured matrix. No numerical hardness, worst-case reduction, or canonical-embedding width conversion is inferred. Using finite-law e instead changes the target challenge tuple by at most `L nu_e`; the reduction's own key generation already uses finite G_K and requires no exact unbounded Gaussian sampler.

[DERIVED hybrid reduction] In the proof-only all-row setup sample d independent finite G_K rows. For a target ciphertext, smudge to `h_i=const(<z_i,c0>)+f_i+Delta a_i`. The Ring-LWE distinguisher takes A and c0 from its challenge, computes P from its known Z, and computes this h without knowing s or e. After replacing c0 by uniform u, apply the finite-key augmented lemma and project its second ring outputs to their constant coefficients. Those unexposed scalars are independent uniform masks even given all P and the simulated oracle. Exposed coordinates agree by challenge validity. Other ciphertexts use public encryption, so one target challenge suffices per hybrid.

[DERIVED strict reduction accounting] Private exact uniform rejection in the implemented transport has an almost-sure uniform output law but no worst-case iteration bound. To make the computational reduction strictly bounded, cap each of its private uniform coefficient/flood draws at 512 trials, falling back to zero. Each replacement costs at most `2^-512`. A safe per-reduction count is `U_red=T(N+d)` (other encryptions plus target floods). Its two challenge worlds then add `2 U_red·2^-512` to the computational step. Oracle-table bits require no rejection loop. The reduction's finite Gaussian costs are explicitly bounded by the frozen 4096-attempt sampler. This proves a bounded reduction for the implemented distributional game; replacing the actual transport's private uniforms by the same cap would additionally cost at most `2T(N+d)2^-512` over its two bit worlds.

[DERIVED finite theorem] Combining the complete-experiment wrapper with the finite-law bare proof gives

```text
Adv_seeded-ROM ≤ 2 delta_G,d−r(1)
  + 2T [epsilon_R + L nu_e + S_G + delta_G,d−j(2)
        + 2 U_red·2^-512]
  + 2 [(Q_A+Q_M)2^-256 + (w+d−r) f_exp].
```

[DERIVED] Setup is paid once in each bit world. The sampler correction is charged at the rows actually replaced, rather than through an assumed infinite-support sampler inside a bounded reduction. The T challenge hybrids remain straight-line. This is our derived classical-ROM theorem conditional on the stated exact Ring-LWE hypothesis and honest game; it is not an invocation of the source paper's adaptive-key theorem.

## 6. Repaired profile, finite losses and reduction resources

[SOURCE/DERIVED] The frozen full repaired point is `N=16384,w=64,d=577,r=16,T=384`, `sigma_K=2^25,sigma_e=2^10,F=2^247`, and `q=4294967767·2^256+1`. Its prior prime/splitting and smoothing certificates give `delta_h(k)<(2h+1)2^-192` for k=1,2. Thus `L=2^20`, `C=2^61`, and `R_pub=625`. `CHECKS.json` evaluates the exact rational ledger for all 17 coalition sizes without drawing any cryptographic randomness. For `Q_A+Q_M≤2^64`, every non-Ring-LWE term is below `2^-168`. The following is explicitly **our derived classical programmable-ROM corollary**, conditional on honest fixed-coalition setup and the exact power-basis Ring-LWE hypothesis at the reduction resources stated above:

```text
Adv_seeded-ROM < 768 epsilon_R + 2^-168.
```

[DERIVED] Here `2^-168` measures only the displayed statistical, cap and programming terms. It is not a security level, certified post-quantum guarantee, or concrete-XOF result. The exact formula, rather than this rounded corollary, applies at other query budgets. The seed-guess contribution alone is `2(Q_A+Q_M)2^-256`.

[DERIVED oracle resource count] Each full row-programming table has 80 chunks, 81,920 raw words, and 3,031,040 bytes. All 625 tables cost 1,894,400,000 independent random bytes in the simple eager simulator. A coupled lazy implementation prepares strictly fewer than 1,250,304 expected bytes per row, or 781,440,000 total, before extra adversarial queries. It retains complete final chunks and produces untouched later chunks/tails on demand. These counts exclude the supplied target arrays, ciphertext simulation, and the adversary's requested output bytes. They are probability/arithmetic counts, not an executed simulator benchmark.

[DERIVED Gaussian resource count] One conservative target reduction generates `dL` key coefficients and at most `TL` error coefficients internally, each by the bounded finite sampler, plus at most U_red bounded private uniform outputs. The frozen direct threshold algorithm uses at most 4096 attempts per coefficient; its exact integer arithmetic can be used in a strict reference reduction. Native screening can reduce actual work while preserving the law, but no runtime measured for the earlier three-encode workflow is substituted for a worst-case T=384 reduction bound. Epsilon_R must be assessed at these actual reduction resources; this theorem supplies no unpriced efficiency shortcut.

## 7. What the result does and does not instantiate

[DERIVED] The missing-row obstruction is resolved here by an explicit common simulator, not a hidden-seed PRG claim. Registered products stay explicit and credential rows stay private. The actual public constructor still creates no missing secret rows; those rows exist only in the statistical comparison and Ring-LWE reduction.

[REFUTED: attempted proof extension] If an adversary chooses a seed after querying its A or missing-row addresses, freshness can fail with probability one. Its already returned chunk prefixes generally cannot be changed to independent prescribed targets. Likewise honest seeds selected by a grinding rule need not leave a uniform matrix independent of retained Gaussian rows. The `Q_pre/2^256` bound does not apply to such selected seeds. This is an obstruction to this reduction, not an asserted attack on the implemented privacy scheme. A bounded candidate-selection theorem would have to retain the entire selection transcript and prove its own joint target law.

[OPEN] SHAKE256 fixes one unprogrammable function. The classical ROM theorem does not prove that a public `(seed,Expand(seed))` tuple is close to a seed plus an independent matrix, and ordinary hidden-seed PRG security cannot do so: the public seed lets anyone recompute. A concrete instantiation requires an explicitly stated ROM-to-SHAKE heuristic or another construction/theorem. Quantum oracle queries, malicious keys/registry replacement, selected-output simulation, integrity, side channels, and general-B semantic integration are also outside this theorem. The completed restricted-query linear prototype learner remains ideal-uniform; a quadratic-lift successor is a separate construction lane.

[SOURCE provenance] Mera–Karmakar–Marc–Soleimanian 2021/046 §5 pp.21–22 supplies the noiseless product syntax; our prior ring candidate changes its sampling, ciphertext projection and proof. Lyubashevsky–Peikert–Regev 2013/293 Definitions 2.20–2.21 and §2.6 supply ring-distribution context, not a finite hardness certificate for this power-basis error. The new wrapper and finite-law derivations above are ours. No external searches were needed; local primary extracts and frozen mathematical/implementation files were read.
