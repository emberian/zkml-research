# Same-scheme encrypted-output randomized FE

[DERIVED; 2026-09-06] Preissued finite-command keys can have the right closed
syntax in the inspected iO-based randomized-FE construction. Ciphertext length
does not recursively grow with its authorized function. The published security
theorem nevertheless does **not** establish the proposed private resident: for
distinct next states, a cheap ciphertext comparison violates its unusually tight
randomized-output compatibility premise. This is a theorem-applicability
obstruction, not a break of randomized FE or an impossibility of a dynamic game.

[EXECUTED] `python3 rfe_recurrence.py` produces `rfe_recurrence.stdout.txt` and
`results/rfe_recurrence_results.json`. It checks exact fractions, finite disjoint
supports, an illustrative size recurrence and a continuing ideal interface.
Neither FE nor secure PKE is implemented. The JSON records four absolute local
PDF paths, SHA-256 hashes, access levels and search accounting.

## Candidate and surviving credentials

[HYPOTHESIS candidate] Fix a finite command alphabet C, a fixed-width state S and
bounded-size deterministic transition circuits. After setup publishes EK, issue one key per
command for the randomized function

```text
F_cmd(s; r) = (Enc_rFE(EK, Step(s,cmd).state; r), Step(s,cmd).answer).
```

[DERIVED syntax] A host evaluates an exposed command key on the current
ciphertext, retains the returned ciphertext, and releases its answer. Two
successive updates call `Dec(K_cmd1,ct0)` and `Dec(K_cmd2,ct1)`. The plaintext fed
to the second encryption is the next state, not the previous ciphertext. A
finite alphabet can encode unknown future **public** observations through a
fixed bit-ingestion protocol; it need not precommit their values. A private
observation ciphertext needs a separate composition, such as an audited
multi-input construction. It is not automatically an extra argument to this
single-input ciphertext. A private PRG seed can be part of the state, but that
does not provide entropy arriving after setup. A genuinely randomized Step
requires a separate analysis of its joint next-state/output distribution; the
distinct deterministic next-state test below is not asserted for every such law.

[SOURCE: actual algorithms] In
[(Multi-Input) FE for Randomized Functionalities, Revisited](https://eprint.iacr.org/2025/330),
Construction 2, printed pp.48–49, one slot has

```text
EK = (pk0,pk1,E_tilde)
MSK = (sk0,sk1,K_auth)
Enc(EK,x; r0,r1) = (c0=Enc_PKE(pk0,x;r0), c1=Enc_PKE(pk1,x;r1),
                    z=E_tilde(c0,c1,x,r0,r1)),  r0,r1 uniform lambda-bit strings
K_f = iO(G[f,sk0,K_auth,K_f_random])
G(ct): authenticate ct; x=Dec_PKE(sk0,c0);
       r_f=PRF(K_f_random,(c0,c1)); return f(x;r_f).
```

[SOURCE] The public obfuscated E program verifies that both PKE components
encrypt the same supplied plaintext with the supplied coins, then provides their
PRF authentication value. Decryption additionally checks this value through an
injective one-way function. Definition 4.4 pp.23–24 permits polynomially many key,
encryption-key and challenge queries in adaptive order. This is not a one-key
theorem. Its stated assumptions include subexponentially secure iO and specified
puncturable PRF/OWF security; no post-quantum reduction was audited here.

| [DERIVED] artifact after initialization | authority / required erasure |
|---|---|
| Public EK | issues fresh state ciphertexts; no raw master is needed online |
| One obfuscated key per command | evaluates that command on every accepted ciphertext, including snapshots and newly issued states |
| Raw sk0 or sk1 | reads every state through the corresponding PKE component; erase all copies |
| Raw MSK, function-key construction inputs and un-obfuscated G code | retain read-all material; erase after issuance |
| Raw K_auth | authenticates ciphertext pairs outside the public E issuance interface; erase as part of setup state |
| Issued obfuscated E/G code containing secrets | remains exposed; protection needs the actual source security theorem, not the assertion that code is sealed |
| Encryption-local plaintext and coins | reveal that issuer's input; initialization/input-erasure assumptions remain |

[DERIVED] The proposed deployment therefore has a syntactically complete honest
erasure ceremony. Erasure is an assumption, and the presence of read-all secrets
inside obfuscated function keys is exactly where a relevant theorem is needed.
The failed premise below prevents labeling this a proved tier-A resident.

## Circuit-size closure: one scoped negative and one syntax positive

[SOURCE] Goldwasser et al.,
[Reusable Garbled Circuits and Succinct Functional Encryption](https://eprint.iacr.org/2012/733),
Remark 3.6 p.22 distinguishes one-key security from bounded-key extensions whose
ciphertext grows with the bound. Remark 3.7 p.23 explicitly analyzes chained FE
outputs under successive public keys and obtains ciphertext size exponential in
the chain length for **that construction**. The following §3.1 handles a
multi-bit output by repeating its one-output-bit construction.

[DERIVED scoped size obstruction] In that repeated-copy implementation, if one
output bit costs b ciphertext bits, a next ciphertext of L bits plus a answer
bits requires at least `b(L+a)` input ciphertext bits. A single fixed format
would need `L >= b(L+a)`, impossible for b>1 and L>0. A bounded acyclic chain can
choose different sizes backwards. This is not inferred merely from a polynomial
upper bound, and is not a lower bound for every FE scheme.

[EXECUTED illustrative control] With illustrative b=8, a=1, terminal width 8, six
backward expansions yield widths `[8,72,584,4680,37448,299592,2396744]`.
15,360 positive-width/base pairs reject the same-format inequality. These numbers
are an exact recurrence example, not secure cryptographic parameters or costs.

[SOURCE] The alternative iO construction of Garg et al.,
[Candidate Indistinguishability Obfuscation and Functional Encryption for all Circuits](https://eprint.iacr.org/2013/451),
§6.1 pp.23–24, encrypts using two PKE encryptions plus a consistency NIZK. The
function lives in its issued obfuscated key; encryption does not contain it.
The §6 game requires equal deterministic function outputs on its challenge pair.
Reading its algorithms establishes the compact dependency structure, not a
randomized-function or recurrent-privacy theorem.

[DERIVED syntax positive for 2025/330] Its Construction 2 has the same useful
separation. Fix state width and the base PKE parameters first. E depends on
those parameters and K_auth, not on F_cmd or the issued G code. F_cmd can then
contain public E's code and the transition circuit, and G can contain F_cmd.
There is no dependency back from F_cmd into E. With polynomial bounds/padding
chosen for these descriptions, this is a finite circuit family. Ciphertexts keep
the fixed format `(c0,c1,z)` through both updates and any later syntactically
valid update. The ciphertext width depends on the state/encryption parameters,
not on accumulated history. No latency or useful-model efficiency follows.

[DERIVED] The alphabet needs |C| keys. An a-priori one-key FE theorem cannot
silently issue them all. Conversely, one cannot invoke a one-input dispatch key
`F(s,cmd)` while leaving unspecified how a new cmd reaches the encrypted state.
The actual2025 multi-key syntax avoids the first issue. A same-state repeated
evaluation under one issued key deterministically reuses the PRF-derived coins;
distinct ciphertexts and keys can produce other coins. The ideal must retain
forking and this caching behavior, rather than promise fresh random coins per
identical call or a nonforkable continuing history.

[SOURCE / DERIVED] Definition 4.5 pp.24–25 models adaptive malicious-encryptor
queries with a fixed stored key and exact-ciphertext output caching. Its tested
key remains with the decryption oracle. That functionality check alone does not
establish privacy when the host holds the deployed key and the next private
input is itself the preceding function output; the malicious-decryptor premise
examined below remains necessary for the proposed theorem application.

## The exact compatibility obstruction

[SOURCE: old games] Goyal–Jain–Koppula–Sahai,
[Functional Encryption for Randomized Functionalities](https://eprint.iacr.org/2013/729),
Definition 2.4 pp.7–8 permits computationally indistinguishable function-output
laws when functions are chosen **before** the public key. Definition 2.6 p.9
permits post-public-key functions but requires statistically indistinguishable
output laws. Remark 2.8 explicitly uses public-key-dependent re-encryption to
explain why simply replacing the latter requirement with computational
indistinguishability is circular. The candidate F_cmd embeds the actual same
EK, so the former timing does not apply.

[DERIVED] Perfectly correct encryption has disjoint ciphertext supports for
distinct plaintexts at a fixed valid public key. Therefore encrypting distinct
next states has statistical distance 1, even when both transitions release the
same outward answer and those states are interface-equivalent. The old
post-public-key statistical premise fails. Computationally hiding ciphertexts
are not statistically equal randomized outputs.

[SOURCE: new game] Definition 4.3 pp.22–23 of 2025/330 gives the compatibility
distinguisher the function description and left input as advice. Definition 4.4
applies the resulting `(A,epsilon)` predicate to cumulative queries. Theorem 6.1
p.50 requires `epsilon=2^(-2*n*s-lambda_iO)`, where s is the length of one base
PKE ciphertext. §6.1 p.48 sets `lambda_iO=lambda`; Construction 2 consumes two
lambda-bit PKE coin strings per encrypted input. Definition 3.8 p.18 requires
**perfect** PKE correctness, and Definition 3.9 requires exact iO functionality.

[DERIVED exact test] Take n=1, a fixed command, and challenge states with equal
outward answers but distinct `u0=Step(s0,cmd).state` and `u1`. The compatibility
distinguisher computes, using its provided function/input advice,

```text
c_star = PKE.Enc(pk0,u0; 0^lambda)
D(F_cmd,s0,(ct_next,answer)) = [ct_next.c0 == c_star].
```

[DERIVED] Under the true uniform randomness in the function's ideal output law,
the all-zero first coin occurs with probability `2^(-lambda)`. Hence
`Pr[D(F_cmd(s0))=1] >= 2^(-lambda)`. Perfect correctness forbids that same c0
from encrypting distinct u1, so `Pr[D(F_cmd(s1))=1]=0`. Collisions between coin
strings encrypting u0 only increase the first probability. Consequently

```text
gap >= 2^(-lambda) > 2^(-2*s-lambda) = epsilon,  for every s>0.
```

[DERIVED scope] Only the first ciphertext component is compared: no assumption
`s>=lambda`, second-coin guess, tag extraction, master secret or decryption is
needed. The test is polynomial time and needs only public data already in this
compatibility game. The same program can be included as the advice-input branch
of a game adversary. That adversary's challenge/function queries fail the
theorem's compatibility predicate. This demonstrates an unmet theorem premise,
not that the actual deployment is efficiently distinguishable with non-negligible
advantage. The exhibited gap is ordinarily negligible; a usual CPA theorem is
entirely consistent with it. A proof for all resident adversaries cannot dismiss
this adversary as if the source theorem covered its challenges.

[EXECUTED] Disjoint-support finite tables for lambda 1 through 6 give statistical
distance 1 and first-component event probabilities exactly `2^(-lambda)` versus0.
65,536 positive lambda/s pairs verify the exponent inequality. Same-next-state
controls have distance 0; within-plaintext collision controls increase event mass.
The table labels expose their message and are deliberately insecure: the tests
exercise correctness/support reasoning, not a cryptographic implementation.

## Composition, nonvacuity and residuals

[EXECUTED] A tiny ideal state `(visible mod4,hidden bit)` undergoes three updates
and two inference calls. Equal visible coordinates and opposite hidden bits
remain related; outputs are `[ACK,ACK,0,ACK,1]` in both worlds, while next states
remain distinct after every step. Eight complete relation checks cover both
commands. Different visible parities give different permitted inference answers,
so the interface is not constant. Restoring the initial snapshot changes the
current inference answer 1 back to 0. The hidden bit is a behavioral quotient;
it does not claim useful secret influence on some later permitted output.

[DERIVED] This witness separates equality of the resident's outward traces from
equality of its concrete encrypted-next-state output laws. The target ideal
would retain the former and represent private state by opaque handles. The
randomized-FE admissibility games examined here compare the latter.

[SOURCE / DERIVED] The 2013/729 Definition 2.3 simulation ideal pp.6–7 supplies
the simulator actual function outputs, and its simulator chooses public
parameters. Theorem 4.1 p.14 gives 1-SIM security with bounded-q extensions
discussed in §4. Calling this theorem alone does not supply a simulator from
only outward answers and opaque resident handles: for a function that returns
encryption under the simulator's chosen key, those ideal outputs can encode raw
next states decryptable with the simulator's setup secret. An additional
composition argument is still needed; “one initial challenge” does not resolve
this mismatch by itself.

[DERIVED] Public-key-dependent functions are not automatically key-dependent
**messages**: this candidate encrypts state, not an FE master key. No KDM or
circular-security conclusion follows merely from embedding public EK. The
specific circularity is attempting to use same-scheme ciphertext privacy to
justify the function-output compatibility needed to prove that privacy. Hiding
next-state encryption under an independent terminal key can avoid that literal
same-key dependency, but it then needs a separate authorized reader/continuation
path and corresponding lifecycle proof. It is not an indefinite closure proof.

[OPEN / next] Preserve the syntax positive. A stronger dynamic or composable
security theorem could potentially justify the recurrence with an opaque-state
ideal; none of the four inspected source statements does so as applied above.
Alternatively, a bounded independent-key chain can be audited backwards with
its terminal functionality and total setup/key size explicit. General iO alone
is not a black-box theorem for arbitrary unequal obfuscated transition programs.
The finished static full-hiding predicate positive remains unchanged.

[EXECUTED accounting] This tranche used one new Scry SQL query, zero schema
queries and two web search queries. Lane totals: eight Scry SQL plus one schema,
Kagi 0, web 28. Scry returned zero rows at zero recorded spend; its limited query
is not evidence of literature absence. All four primary PDFs were read by
absolute local-mirror path; no PDF was downloaded in this tranche. The corpus
and exact access levels are recorded in `results/rfe_recurrence_results.json`.
