# Relaxing perfect base-FE correctness with an explicit error budget

[DERIVED; author supplement, 2026-09-07] The frozen [bootstrap theorem](BOOTSTRAP_LIFT.md), SHA256 `ec9f721f2402d31a49a9fd4ee14f978b4cf7474429600710347dc555fe0d9792`, assumes perfect base Boolean FE correctness. This supplement replaces that sufficient premise with **uniform pointwise correctness over fresh setup, key-generation and encryption coins**. Its privacy games, construction and probability-gap bounds are unchanged. The result still gives uniform **all-input** correctness of the final iO object. No source's unspecified negligible error is promoted to a stretched-exponential rate.

## Replacement premise

[HYPOTHESIS `B_correct`] For every admitted fixed classical function `f` and message `m`, chosen independently of the fresh current setup, require

```text
Pr[ B.Dec(sk_f, B.Enc(pk,m)) != f(m) ] <= delta_B,
```

[HYPOTHESIS] where probability is over fresh `B.Setup`, one honest `B.KeyGen(f)` and fresh uniform encryption coins. The bound is uniform over all the theorem's fixed public size bounds. It need not assert an all-message correctness event for one key or correctness for every tape. Decryption remains deterministic with the public polynomial runtime cap. All other efficiency/security contracts of the frozen theorem remain in force.

[DERIVED averaging] Classical function/message parameters sampled independently of that current setup are permitted by averaging this pointwise bound. Reuse of a setup and function key across several messages is permitted by a union bound; those failures need not be independent. None of this permits choosing a message as a function of the current setup's secret coins. The construction's program/message dependency order is why the pointwise bound applies.

## Weak FE: one marginal PRF test per position

[DERIVED] In 2016/006 Theorem 6, a correctly obfuscated raw indexed-encryption circuit returns

```text
c_i = B.Enc(pk,(m,i);F_K(i)).
```

[DERIVED] Fix an output index `i`. Sample the current `B` setup and key for the fixed indexed function `f'`. Given a puncturable-PRF challenge `(K\{i},V)`, ignore the punctured key and test

```text
B.Dec(sk_f', B.Enc(pk,(m,i);V)) != f'(m,i).
```

[DERIVED] This is an efficient **classical** distinguisher in the PRF point-value game, at the actually charged setup/key-generation/decryption cost. When `V` is uniform its failure probability is at most `delta_B`. When `V=F_K(i)` it is exactly that indexed message's marginal failure probability in the raw weak-FE object. Setup is independent of the PRF challenge. Therefore this marginal probability is at most `delta_B+eps_P,corr`, where the latter is the PRF game's envelope for these failure tests. No hidden PRF seed or coherent secret-key oracle is required.

[DERIVED] Union bound over the `s` padded positions and add xiO's uniform fresh-object all-input error:

```text
delta_W <= delta_X + s*(delta_B+eps_P,corr).                   (C1)
```

[DERIVED] Correlations between the xiO error and the Boolean FE errors do not affect this union bound. XiO's raw circuit may depend on `pk,K,m`; these are independent of its fresh obfuscation coins. A correctly obfuscated object is correct at all positions simultaneously. The source proof's exact raw-circuit equivalences and FE challenge compatibility are independent of whether any subsequent decryption is correct, so the privacy bound (1) in the frozen theorem is unchanged.

## Succinct and composed RE

[DERIVED] The bit-indexed succinct `R_S` uses one function key and `l` ciphertexts under its public key. For each position, its function `F_U,c` and message `(Pi,x,i,0,0)` are fixed independently of the current `B` setup after averaging the pad and program parameters. Each has fresh uniform encryption coins. Consequently

```text
delta_RS,fresh(l) <= l*delta_B.                              (C2)
```

[DERIVED] This is only a fresh-encoding bound; this supplement does **not** assert that `R_S` remains correct for every pseudorandom tape. In a fresh composed `R` encoding, however, the outer `R_S` coins are fresh uniform coins independent of its program `H[Pi,zeta,pk_W]`. The inner public key belongs to an independent setup, and `zeta` is a fresh independent seed, so averaging those parameters preserves (C2) for the outer setup.

[DERIVED] If outer decoding is correct, it returns the intended inner ciphertext. The inner `R_W` ciphertext's tape is `G(zeta)`. The same efficient marginal PRG failure test used for equation (5) of the frozen theorem compares it to a fresh-uniform-tape `R_W` encoding, now using (C1). With `l_H` the padded inner ciphertext width and `s` the padded output-position bound, the union of the outer and inner failures has probability at most

```text
delta_R,fresh <= l_H*delta_B + delta_W + eps_G,composition-corr
              <= delta_X + (l_H+s)*delta_B + s*eps_P,corr
                 + eps_G,composition-corr.                  (C3)
```

[DERIVED] The failure test can compute the desired bounded program output and compare actual decoding in polynomial time under the global public bounds. It only consumes the supplied PRG tape; it does not need its hidden seed or a real outer encoding of an unknown-seed program. Outer and inner failure events may be correlated. Only the union bound is used.

## Complete bounded tree

[DERIVED] Keep the frozen theorem's latent-tree proof. For a fixed prefix at depth `d`, replace its marginal node seed and complete encoding tape by independent uniform values at cost `d*eps_G,tree-corr`. The node's program contains only later public keys, independent of its current setup. The fresh-pair case is therefore covered by (C3). This marginal step also covers the outer `R_S` tapes when they are produced by an ancestor PRG; no all-tapes correctness claim about `R_S` is needed.

[DERIVED] Write

```text
M_n = 2^(n+1)-1,
S_n = sum_(d=0)^n d*2^d = (n-1)*2^(n+1)+2.
```

[DERIVED] With uniform maximum bounds on `l_H,s` over all level instances, the final object's all-input error satisfies

```text
eta_IO <= M_n * [delta_X + (l_H+s)*delta_B + s*eps_P,corr
                + eps_G,composition-corr]
          + S_n*eps_G,tree-corr.                             (C4)
```

[DERIVED] If `l_H,s<=B` and a common PRG failure-test envelope is used, this simplifies to

```text
eta_IO <= (2^(n+1)-1)*[delta_X + 2B*delta_B + B*eps_P,corr]
          + (n*2^(n+1)+1)*eps_G,corr.                        (C5)
```

[DERIVED] This bound is uniform over the admitted fixed circuit family and concerns simultaneous correctness for every input. There is no extra `2^|m|` union over every possible base-FE message. Instead, one mathematically fixed tree prefix supplies one program, then the polynomially many indexed FE messages within that node are union-bounded; finally the `M_n` latent tree nodes are union-bounded. The tree is not enumerated by the reduction.

## What this removes and what it leaves open

[DERIVED] The algorithmic bootstrap does not intrinsically require perfect base-FE correctness. Uniform pointwise `delta_B` suffices through (C5). If `delta_B <= 2^(-kappa^c_B)` and the other error/security exponents satisfy the frozen theorem's resource conditions, choose the input exponent `gamma` below `c_B` as well. The polynomial `B` factors are then absorbed while retaining a stretched-exponential final error. This explicitly weakens the correctness premise; it does not weaken the static message/function timing, short-public-key, compactness or quantum-advice privacy requirements.

[SOURCE / inherited scope] The base source chain read in the preceding audit includes 2012/733's correctness condition with negligible error, while 2016/006 Definition 3 prints perfect correctness. This supplement is a derived reconciliation of the **type of correctness contract**, not a primary-source assertion that their exact lattice parameters already yield the numerical `delta_B` required by (C5). The independent base-source lane is auditing those quantitative rates and the public-key succinctness/depth-bootstrap interface. No copied source algorithm or frozen proof is changed here.

[OPEN] A source statement of merely `negl(kappa)` does not alone ensure that `2^n*poly(kappa)*delta_B` is negligible for the selected growing input length. An instantiated rate, or a proved correctness-amplification/parameter argument with its costs, remains necessary. The present supplement identifies the exact rate needed without treating the absence of a printed exponent as an impossibility result.

[OPEN review status] This supplement is author-derived and must be reviewed separately from the frozen theorem. `pointwise_controls.py` checks only its finite coefficient algebra and dependency counts; it is not a cryptographic theorem checker.
