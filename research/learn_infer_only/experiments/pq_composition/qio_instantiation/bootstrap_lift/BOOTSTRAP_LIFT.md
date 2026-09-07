# A conditional one-copy quantum-advice lift of the xiO bootstrap

[DERIVED; author draft, 2026-09-07] The inspected xiO → weak FE → randomized encoding → bounded-circuit iO bridge admits a straight-line lift with one arbitrary quantum advice state. The theorem below assumes explicitly stated quantum-advice games for **static single-key Boolean succinct FE, a puncturable PRF, a PRG and xiO**. It does not identify that suite with LWE. The [preceding frozen audit](../INSTANTIATION.md) can supply its xiO premise conditionally from its `AVI_QA`/`SMS_QA` contracts. The remaining LWE instantiation question is the base suite and its quantitative advice/correctness guarantees, rather than a missing quantum-state operation inside the bridge proved here.

[SOURCE / access] Primary sources read locally: **2016/006**, Definitions 3–5 pp.5–6, Theorems 6–7 pp.9–11; **2015/720**, Definitions 20–25 pp.28–30, Theorems 11–13 pp.30–36 and circuit consequence Theorem 15 p.37; the child-coin hybrid is also explicit in §4.1 pp.22–23. The bit-indexed succinct encoding below makes the multi-bit step in the latter paper's p.32 footnote 8 explicit while preserving a short public key. It is our construction detail, not a quotation of that footnote. Source hashes and commands are in `audit.json`/`ACCESS.md`. All claims concern this finite-input circuit construction; the additional unbounded-input/Turing-machine transformations are outside scope.

## 1. Games and quantifiers

[HYPOTHESIS model] Use the nonuniform quantum circuit model fixed in the [accepted interface lemma](../../qio_interface/QIO_INTERFACE.md): a classical circuit description, initialized work registers, and **one** arbitrary `q`-qubit advice state. Fix all classical input-length, description, gate, addressed-wire and advice budgets before taking each worst-case probability-gap envelope. Advice may depend on the fixed classical challenge pair/function/program and the security parameter, but is independent of fresh challenger coins. Arbitrary mixed states are allowed. Gate/description/workspace costs of classical wrappers count; no extra quantum advice is silently added. Security is the absolute difference of acceptance probabilities, not the half-sized guessing advantage.

[HYPOTHESIS `B`] A public-key, static, single-function-key, single-challenge **Boolean** succinct FE scheme for polynomial-size classical circuits. The fixed function `f` and equal-width messages `m0,m1` are selected before fresh `Setup`, and satisfy `f(m0)=f(m1)`. The challenge view is `(pk,sk_f,Enc(pk,m_b))`. Its quantum-advice gap is `eps_B` at the actual resources. `pk` has length `p0(kappa)` independent of the admitted function/time/output bounds; encryption takes `poly(kappa,|m|,log s_max)` time. Setup/key generation and decryption are polynomial in their explicit public bounds. Correctness is perfect for every admitted function/message and all honestly supported coins; decryption is deterministic. This is the strengthened interface of 2016/006 Definitions 3–5, with the short-key convention of 2015/720 Definition 20 stated explicitly.

[HYPOTHESIS `P`] A selectively puncturable classical PRF with exact off-point evaluation. For every fixed puncture point, `(K\{i},F_K(i))` and `(K\{i},U)` have quantum-advice gap `eps_P`; fresh key/point-value randomness is independent of advice. This is a classical-string challenge. No coherent secret-key oracle is assumed or used. Output length covers the bounded encryption random tape.

[HYPOTHESIS `G`] An extensible classical PRG with a `kappa`-bit seed and any required polynomial output length `L`. `G(U_kappa,L)` versus `U_L` has quantum-advice gap `eps_G`. Its time is at most `L*poly(kappa,log L)` (absorb logarithmic factors below). This explicit efficiency condition suffices for the tree's common polynomial time bound; a generic polynomial-output-time assertion alone should not silently be substituted into that bound. The source allows arranging a stronger sublinear exponent to accommodate polynomial PRG work (2015/720 §5 p.25). We use the stated, simpler sufficient PRG interface instead. A separate `eps_G,corr` denotes the same PRG game's envelope for the efficient classical failure tests used in correctness.

[HYPOTHESIS `X`] Quantum-advice worst-case xiO for classical circuits with `h=O(log kappa)` input bits: all equally padded equivalent circuit sequences and all admitted advice states have gap `eps_X`. Obfuscation is classical with time `poly(kappa,|C|,2^h)` and output length `2^(h(1-alpha))*poly(kappa,|C|)` for a fixed `alpha>0`. Public evaluation is deterministic. Its fresh-object **all-input** correctness error is at most `delta_X`, uniformly over every admitted fixed circuit. This includes sampled circuits independent of fresh obfuscation coins by averaging. It is not a per-query correctness contract.

[DERIVED quantifier discipline] Envelopes below are evaluated at the maximum circuit/message/output bounds encountered and at the final distinguisher's resources plus the specified honest work. They are uniform over every fixed classical instance and every admitted advice state. Therefore independently sampled setup packages/program parameters can be adjoined by averaging. If a proof mathematically fixes a classical sample, the conditional residual state is an allowed advice state in the same `q`-qubit space; the reduction neither prepares that conditional state nor tests an equivalence event. The all-sequence-to-uniform-envelope argument and its nonuniform convention were proved in the accepted interface lemma. All classical constants fit in the charged description budget.

[DERIVED API scope] All setup, key, message and challenge interfaces here are classical. The final adversary can process the resulting classical public code quantumly, including reversible local evaluation. No coherent secret decryption interface, quantum-valued classical setup sampler, state rewinding, state cloning, random oracle or QROM lifting is used.

## 2. Explicit encoding bridge and its primitive losses

[SOURCE] 2016/006 Theorem 6 encrypts a multi-output FE message by obfuscating

```text
G[pk,K,m](i) = B.Enc(pk,(m,i); F_K(i)).
```

[DERIVED] Let `s` be a power-of-two padded output-position bound, at least the largest admitted output length. The source also upper-bounds this by maximum function size; using the output-position bound here keeps the distinction explicit. The one Boolean function key computes the indexed output of the requested function. A threshold hybrid changes one position at a time: use exact-equivalence xiO switches to isolate that position, replace its punctured PRF value by uniform encryption coins, use a single static `B` challenge on `(m0,i),(m1,i)`, then reverse the two wrappers. The source has two boundary xiO switches in addition. Consequently its weakly compact FE `W` satisfies the conservative bound

```text
eps_W(s) <= (2s+2) eps_X + 2s eps_P + s eps_B.                 (1)
```

[DERIVED] Every Boolean FE challenge is compatible because the original complete outputs agree. Its messages/function are chosen before current FE setup. For an xiO switch, the reduction samples the other classical material and submits an exactly equivalent padded pair; fresh xiO coins remain independent of the retained advice. Each primitive reduction invokes the final distinguisher once, with polynomial honest overhead. No correctness event is needed to assert equivalence of the raw classical circuits. Under perfect `B` correctness, one correctly obfuscated `G` gives every output position correctly, so `delta_W <= delta_X`; there is no additional factor `s` in that fresh-object bound.

[SOURCE] 2015/720 Theorem 12 transforms multi-output FE into simulated randomized encodings. With `U` a bounded universal circuit and output length `l`, choose `c=G(s0,l)` and issue the key for

```text
F_U,c(Pi,x,s,b) = U(Pi,x)                 if b=0,
                 c XOR G(s,l)           if b=1.
```

[DERIVED] Real encryption uses `(Pi,x,0,0)`. To simulate output `y`, choose `c=y XOR G(s,l)` and encrypt `(0,0,s,1)`. The pad hybrids cost two PRG games; the final FE messages have the same output `y`. Neither PRG reduction needs the seed underlying its challenge pad: before the FE-message switch, the encrypted branch is still real. Applying (1) gives a weakly compact RE `R_W` with

```text
eps_RW(l) <= 2 eps_G + eps_W(s),          delta_RW <= delta_X, (2)
```

[DERIVED] where `s` pads `l`. Its ciphertext length is at most `T^(1-alpha')*poly(kappa,|Pi|,|x|)` for a fixed `alpha'>0`: `l<=T` under the padded time convention, and the raw indexed-encryption circuit has size polynomial in message width and logarithms of the circuit/time bounds. All public keys stay short. `R_W`'s simulator outputs its own `(pk,crs,ct)` and receives only `y` and fixed public length/time metadata, not `Pi` or a hidden seed.

### The succinct encoding uses one public key and one Boolean function key

[DERIVED construction `R_S`] The needed succinct RE can be built directly from `B`, avoiding an unstated many-function-key FE assumption. For output bound `l`, sample one pad `c=G(s0,l)` and one `B` setup, and issue exactly one key for

```text
F_U,c(Pi,x,i,s,b) = [U(Pi,x)]_i           if b=0,
                   c_i XOR [G(s,l)]_i    if b=1.
```

[DERIVED] The public encoding key is the one `B` public key. The CRS is this one function key. Encode `(Pi,x)` with `l` independently randomized public-key ciphertexts of `(Pi,x,i,0,0)`, for `i=1..l`. To simulate `y`, sample `s`, set `c=y XOR G(s,l)`, generate the single setup/key, and encrypt `(0,0,i,s,1)` at every position. Pad metadata and vectors to their public bounds. Both messages at position `i` have function output `y_i`.

[DERIVED proof] Two pad-PRG switches followed by `l` single-challenge FE hybrids give

```text
eps_RS(l) <= 2 eps_G + l eps_B.                              (3)
```

[DERIVED] In the `i`th FE reduction the function and two messages are fixed before setup. Given the one challenge `(pk,sk_F,ct_i)`, it encrypts every other position publicly under **that same `pk`**, retaining the same `sk_F`. Thus the multi-ciphertext view follows from one-key, one-challenge security without supplying extra function keys or assuming independent public keys by position. A fresh invocation of the final adversary uses its single advice state. Perfect `B` correctness makes this RE perfectly correct for every encoding tape. Its encoding time is `l*poly(kappa,|Pi|,|x|,log T,log l)`; its public key remains independent of `l,T`. The possibly long universal-function key belongs in the CRS, as permitted by the source's definition.

[SOURCE / DERIVED composition] Apply 2015/720 Theorem 11 with `R_S` outside `R_W`. With independently generated outer and inner setups, encode under `R_S` the program

```text
H[Pi,zeta,pk_W](x) = R_W.Enc(pk_W,Pi,x; G(zeta,r_W)).
```

[DERIVED] Here `r_W` is the fixed padded inner random-tape length. The simulator first obtains `(pk_W,crs_W,ct_W)` from `Sim_W(y)`, then `(pk_S,crs_S,ct_S)` from `Sim_S(ct_W)`. The hybrids are: simulate the outer encoding; replace the inner PRG tape by uniform coins; simulate the inner encoding. After the first step, `zeta` is absent from the exposed view, so the PRG reduction needs only the challenge string. With `l_H` the padded inner ciphertext length, the resulting sublinearly compact RE `R` has

```text
eps_R <= eps_RS(l_H) + eps_G + eps_RW(l)
      <= (l_H+s) eps_B + (2s+2) eps_X + 2s eps_P + 5 eps_G.    (4)
```

[DERIVED] If all primitive gaps are at most `eps` and `s,l_H<=B`, then `eps_R <= (6B+7)eps`. Each reduction adds polynomial setup/encoding/simulation work, with one call to its quantum distinguisher. Encoding takes `p(kappa,|Pi|,|x|)*T^(1-beta)` time for some constant `beta>0`, shrinking the exponent to absorb logarithms. `H` has a short description because `pk_W` is short; its potentially long execution is represented by a program and a binary time bound, not by writing all its computation into its description.

[DERIVED fresh correctness] The outside `R_S` is perfectly correct, including on PRG-derived coins. A fresh `R` encoding can fail only if its inner `R_W` fails on the PRG-derived tape. For a fixed program and fresh setup, the test

```text
bad(t) := R_W.Eval(R_W.Enc(pk_W,Pi,x;t),crs_W) != U(Pi,x)
```

[DERIVED] is an efficient classical PRG distinguisher; it samples setup independently of the challenge and never needs `zeta`. Hence

```text
delta_R,fresh <= delta_X + eps_G,composition-corr.            (5)
```

[DERIVED qualification] This is a **marginal failure test**, not a simulation of the complete outer real encoding from an unknown PRG seed. It correctly charges the computational change from uniform to pseudorandom encryption tapes. Simply applying fresh-coins correctness while conditioning on a revealed ancestor seed would not justify (5).

## 3. Bounded tree algorithms and polynomial resources

[DERIVED normalized construction] Fix equally padded equivalent Boolean circuits `C0,C1` of input length `n`. Choose common public program-description, time, output and random-tape bounds as below. Generate independent `R.Setup` instances `(pk_i,crs_i)` for `i=0..n`. A node program with prefix `v` at depth `i`, seed `R_v`, and all later public keys computes:

```text
P[C,i,v,R_v,pk_(i+1)..pk_n]():
    if i=n: return padded C(v)
    (R_v0,omega_v0,R_v1,omega_v1) = G(R_v,2*kappa+2*r_Enc)
    ct_0 = R.Enc(pk_(i+1), P[C,i+1,v0,R_v0,later_keys], empty; omega_v0)
    ct_1 = R.Enc(pk_(i+1), P[C,i+1,v1,R_v1,later_keys], empty; omega_v1)
    return padded (ct_0,ct_1)
```

[DERIVED] All encodings have fixed public widths, and each `omega` is a complete encoding random tape. The root uses a fresh uniform seed and an independent fresh encoding tape. Publish its encoding and all level CRS values. The proof may additionally publish every level public key, a stronger view; evaluation only needs the CRS values. Evaluation decodes one node per input bit, chooses that child, and decodes the leaf. All decoding after obfuscation is deterministic.

[DERIVED fixed-point efficiency] Node programs are generated by one fixed program template carrying parameters; they do not recursively inline two copies of each descendant's source code. Formally the bounded universal machine can recognize a fixed node-program tag whose payload is `(C,i,v,R_v,future_keys,bounds)`; making a child means writing another tagged payload. This fixes the interpreter once and avoids a recursive source-code expansion. Before selecting `T`, payload length is `M0+O(log T)`, with `M0=poly(kappa,|C|,n)` including the `n*p0(kappa)` future-key package; the tape/output bounds have logarithmic descriptions as well. Absorb these logarithmic factors into a smaller positive sublinear exponent. If encoding takes at most `p(kappa,M)T^(1-beta)` steps, its tape and ciphertext lengths satisfy the same bound. The stated PRG efficiency then makes two child encodings, their tapes and the template work take at most

```text
A(kappa,M0) T^(1-beta') + B0(kappa,M0),      beta'>0.
```

[DERIVED] Choose an integer `T` at least `2*B0`, the padded leaf work, and `(2*A)^(1/beta')`. Then every node runs within `T`; choose the common output bound at most `T` with an adjusted constant for its pair encoding. Now `M=M0+O(log T)` is polynomial in the original parameters, closing the choice without assuming a time bound in its own coefficient. Constants and logarithmic factors were absorbed once into `A,beta'`. This is a single polynomial bound for every depth, not a recurrence raising a runtime polynomial to a new power at each level. Setup and CRS sizes are polynomial in these bounds, and there are `n+1` levels. The resulting obfuscator and evaluator therefore have polynomial time and output size for fixed polynomial circuit families.

[DERIVED resource ledger] Let `W` bound one level's classical simulation, sibling generation, public setup generation, and the internal wrappers used by (1)–(4), including their classical descriptions and scratch space. It is polynomial in the fixed global bounds. Following one hybrid path from root to a primitive challenger adds at most `(n+1)W` work to `T_A`; the analogous addressed-wire/description overhead is additive. Only one child continues as the reduction challenge at each step; the other child is generated honestly. **The exponential number of hybrid terms is an advantage loss, not the size of any one reduction.** The same `q` advice qubits continue throughout, with no copies or fresh state depending on a challenge outcome. If one instead uses a uniform-unitary model, classical code initialization must be separately charged as described by the accepted interface review; the exact unchanged-`q` statement here uses the explicitly selected nonuniform circuit model.

## 4. Quantum-advice privacy induction

[DERIVED joint invariant] At depth `i`, compare the two experiments outputting the node encoding together with **all current and later public keys and CRS values**. Generate later-level packages first; then choose the current program/seed; then run fresh current setup. This preserves pre-current-setup independence. The retained adversary advice is adjoined to that entire joint view. Mathematical averaging over the independent later package invokes the fixed-instance bounds; no sampler must condition on a challenge bit or prepare advice. The two children share the same next-level setup, as the algorithm requires.

[DERIVED base] At a leaf, raw program output is `C0(v)=C1(v)`. Their padded metadata agree. Apply `R`'s simulation security on each side to the same simulator output. The gap is at most `2 eps_R`.

[DERIVED step] At an internal node use the following six transitions:

1. `[DERIVED]` Real `C0` node → `Sim_R` of its raw output: `eps_R`.
2. `[DERIVED]` Its PRG-generated `(R0,omega0,R1,omega1)` → an independent uniform tuple: `eps_G`. The current seed appears only in the already removed real node program, so the reduction can compute the raw output and simulator from its challenge tuple without knowing that seed.
3. `[DERIVED]` Switch child 0 using the next-level joint induction: `a_(i+1)`.
4. `[DERIVED]` Switch child 1 similarly: `a_(i+1)`.
5. `[DERIVED]` Reverse the child-tape PRG replacement for `C1`: `eps_G`.
6. `[DERIVED]` Reverse current simulation: `eps_R`.

[DERIVED shared-key point] During a child switch, the reduction receives that child's `(ct,pk_(i+1),crs_(i+1),later package)`, generates the sibling **publicly under the supplied same public key** with independent coins, and applies `Sim_R` to the pair. It does not need next-level secret setup coins or another independently generated CRS. It runs the continuing distinguisher once. Thus neither reuse of a level key nor the exposed correlated package calls for a many-key FE security assumption.

[DERIVED exact recurrence] Taking uniform envelopes at the expanded resources,

```text
a_n <= 2 eps_R,
a_i <= 2 eps_R + 2 eps_G + 2 a_(i+1),
Delta_IO <= (2^(n+2)-2) eps_R + (2^(n+1)-2) eps_G.            (6)
```

[DERIVED] Every raw-equivalence, pad and program-output equality is classical and exact. The quantum part is the same final distinguisher applied to the generated classical view and its one original advice state. The proof does not extract a witness, rewind that distinguisher, test/condition on successful quantum behavior, or invoke an adversary-dependent quantum simulator. Correctness failure of xiO is absent from (6), since the privacy hybrids use its exact raw-circuit equivalence game.

## 5. Uniform all-input correctness, including pseudorandom tapes

[DERIVED] Define the **latent** complete depth-`n` tree by the raw program equations, regardless of whether any actual decoder returns a wrong output. It has `M_n=2^(n+1)-1` node encodings. If every latent encoding decodes to its raw program output, evaluation succeeds on **all** `2^n` inputs simultaneously. This tree is used only for the union bound; neither obfuscation nor a reduction enumerates it.

[DERIVED fixed-prefix lemma] For one fixed prefix of depth `d`, the marginal pair `(R_v,omega_v)` is computationally indistinguishable from an independent uniform pair with gap at most `d*eps_G,tree-corr`. Prove this by the `d` seed-expansion hybrids along that prefix, selecting the indicated seed/tape block and discarding ancestor data. Future/current setup is independent of these seeds. A failure predicate for this node takes `(R_v,omega_v)` and independently generated level packages, constructs its program, runs its raw output and its actual encoding/decoding, and compares them. This is a polynomial-time test under the global bound. It never needs a hidden PRG seed, and it does not expose or condition on an ancestor seed or encoding. The fresh-pair failure probability is bounded by (5), after averaging the node seed and future keys; the current setup is independent of its program.

[DERIVED all-node union] No independence of different node-failure events is required. Therefore

```text
eta_IO <= (2^(n+1)-1) (delta_X + eps_G,composition-corr)
          + ((n-1)*2^(n+1)+2) eps_G,tree-corr.                 (7)
```

[DERIVED] The second coefficient is `sum_(d=0)^n d*2^d`. With a common upper bound for both classical PRG failure tests,

```text
eta_IO <= (2^(n+1)-1) delta_X
          + (n*2^(n+1)+1) eps_G,corr.                         (8)
```

[DERIVED scope] This is uniform over admitted fixed circuits, and its event covers all inputs. It is stronger than a bound for polynomially many observed queries. Perfect base-FE correctness was an explicit sufficient premise; replacing it by ordinary per-message negligible error requires new uniform error accounting and is not done here. The extra PRG term is necessary for this proof: a distribution of pseudorandom tapes cannot be treated as fresh uniform tapes after conditioning on their known seed. A toy bad-range control below illustrates that logical error without asserting an attack on a secure PRG.

## 6. Conditional endpoint and the remaining instantiation premise

[DERIVED conditional theorem] Under `B,P,G,X` as stated, the bounded tree gives quantum-advice worst-case iO for classical Boolean circuits, with polynomial construction/evaluation cost, primitive-to-RE loss (4), privacy loss (6), and uniform all-input correctness loss (7). Equally padded multi-bit circuit outputs can also be carried at leaves with the corresponding public output bound. The theorem permits any one independent advice state within the fixed budget and hence feeds the already accepted qualified-QIO averaging lemma.

[DERIVED sufficient parameters] Suppose, at all the polynomial honest bounds above, primitive privacy gaps are at most `2^(-kappa^a)` against the needed quantum circuits, and `delta_X <= 2^(-kappa^c)` for constants `a,c>0`. Assume the PRG correctness-test gaps have the same security exponent, as they are efficient classical instances of its game. Choose `n <= kappa^gamma`, where `gamma < min(a,c)`, and allow final distinguisher gates/workspace at most `2^(kappa^b)` for `b<a`, keeping its advice budget explicit (ordinary polynomial advice suffices here). The additive honest overhead fits the base budget for large `kappa`; the factors `2^n*poly(kappa,|C|)` in (4), (6), (8) are dominated by the stated exponents. A smaller positive common exponent yields stretched-exponential privacy and correctness. For an external security parameter and an admitted polynomial circuit-size/input family, polynomially enlarge `kappa` as a public function of that parameter and circuit size to satisfy the input inequality. Padding equal-size challenge circuits selects the same parameters.

[DERIVED connection to 2025/2215] The preceding main-transform audit supplies `X` when its **quantitative** `AVI_QA` precondition-to-postcondition promise, `SMS_QA`, statistical equivocation, and efficiency contracts hold. At the required resources it gives `eps_X <= sqrt(N)*eps_AVI` once the promise is eligible, and `delta_X <= N*delta_SMS` for perfectly correct aviO (or add `sqrt(N)*delta_AVI` under a uniform error premise). A merely qualitative aviO promise does not supply the subexponential numerical transfer needed here. No precondition error is silently added to a postcondition advantage as though Definition 6 furnished such a transfer.

[OPEN exact LWE-and-aviO instantiation] This closes the **algorithmic bootstrap lift** that the frozen predecessor left open. It does not derive `B,P,G` or the main transform's `SMS_QA` from a particular LWE distribution against arbitrary quantum advice. For example, 2016/006 Theorems 3–4 cite a base succinct-FE/depth-bootstrap chain; 2015/173 Appendix C pp.56–57 spells out an intermediate bounded-key route. Those references do not license deleting the named `B` game, its short-key/perfect-correctness contract, or its quantitative advice convention from this theorem. The first unclosed premise for compressing this result to **LWE + aviO alone** is a base-suite instantiation with precisely those quantum-advice/subexponential and correctness contracts. No blocking extraction, rewinding, or quantum conditioning step was found in the actual bridge (1)–(8). This is a scoped positive conditional result, not a field-wide absence or a shipped PQ implementation claim.

[OPEN review status] This is the author's proof. Independent review and its exact target hash, if supplied, are recorded separately; executable controls alone do not certify cryptographic security.

[EXECUTED] `python3 research/learn_infer_only/experiments/pq_composition/qio_instantiation/bootstrap_lift/controls.py > research/learn_infer_only/experiments/pq_composition/qio_instantiation/bootstrap_lift/controls.stdout.txt` exited 0. The controls retain 145,636 Boolean-key compatibility cases, 225 rational privacy-recurrence cases, 25 all-node coefficient checks, 4,096 composition coefficient checks, 32,906 latent-tree failure-mask cases and 1,056 fixed-point examples. The separate audit script pins the source and proof bytes and checks local links. See `ACCESS.md`, `controls.json`, and `audit.json` for precise scope and command/output provenance; none is a cryptographic theorem checker.
