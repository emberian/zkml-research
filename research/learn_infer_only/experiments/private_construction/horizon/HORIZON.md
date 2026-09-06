# Uniform horizon bound for the independent-key ladder

[DERIVED conditional positive; 2026-09-06] The inspected source supports a
uniform logarithmic-horizon extension of the finite ladder, for a fixed
branching command alphabet and the same classical source-conditional assumptions.
The argument uses the source's unconditional one-message SIM theorem and its
explicit simulator. It does not promote qualitative randomized-output
compatibility into an invented quantitative FE theorem.

[DERIVED scope] For B fixed commands and horizon H, let
`N_H=1+B+...+B^H`. The strict-PPT reduction below has advantage exactly
`Delta_ladder/M`, where `M=2^ceil(log2(2*N_H))` and `2*N_H<=M<4*N_H`,
and adds polynomial work in H to the host's runtime.
Thus polynomial N_H suffices. For fixed B>1, this gives `H=O(log lambda)`;
for B=1, it gives polynomial H, with no branching choice of command. The proof
does not establish polynomial horizon for fixed B>1 under ordinary negligible
security alone. All initial states and Step circuits remain independent of
setup randomness. Public commands, honest erasure, full forks and the absence
of private fresh-input composition remain as in the fixed H=2 candidate.

[DERIVED uniformity premise] This uniform corollary assumes a uniform PPT host
and a uniform PPT pre-setup sampler for the initial candidate pair and public
Step descriptions, or uniformly computable families supplying them. Polynomial
description length alone does not imply such a sampler. Arbitrary nonuniform
or quantum advice requires a corresponding stronger SIM security convention or
separate lift; it is not imported from the source's distinct nonuniform
IND_pre statement. The explicit m=lambda, initial-pair(0,1) witness is uniformly
computable. The frozen fixed-H IND_pre claim remains separate.

[EXECUTED] `python3 audit.py` writes `stdout.txt` and `results.json`. It checks
uniform hybrid indexing, exact counts/fractions, a negligibility diagonal
counterexample and nonvacuous finite interfaces. These are proof/resource
controls, not encryption implementations or measured primitive advantages.
The four frozen H=2 files are unchanged.

## Source statements and normalization

[SOURCE: simulator and reduction read]
[Goyal–Jain–Koppula–Sahai, Functional Encryption for Randomized Functionalities](https://eprint.iacr.org/2013/729),
§5.1 pp.14–15 supplies explicit uniform algorithms S1/S2 for its one-message
simulation. S1 generates a simulated public key and zero-encryption challenge.
S2 receives each function's ideal output and obfuscates a program containing
that output at the challenge point. It does **not** obfuscate the adversary.
Theorem 4.1 p.14 states 1-SIM security. §5.2 pp.15–17 and Appendix A pp.19–24
give eleven hybrid transitions proving it.

[SOURCE] Appendix C p.25 proves SIM-to-IND_pre through
`Real0 ~ Ideal0 ~ Ideal1 ~ Real1`. Footnote8 explicitly observes that the
middle step appends the **current** `(MPK,MSK)` to the function-output auxiliary
distribution. Independence from the current public key justifies that step.
Our reverse setup order supplies exactly this independence; the full future
package remains in the auxiliary state and can be internally correlated.

[SOURCE normalization] Figures1/2 print an inverted signature-check branch.
Observation A.2 p.19 explicitly defines rejection when `Verify=0`, as required
by the following validity proof. The source-conditional algorithms here use that
normalization. No implementation of the erroneous printed branch is claimed.
Exact classical correctness/equivalence contracts are inherited from the source
reading; a different primitive with nonzero correctness error needs its own
uniform error accounting, as in the separate PQ audit.

## Exact one-level expansion

[DERIVED] Keep the finite-ladder relations R_i and package P_i from
`../FINITE_LADDER.md`, now for a uniformly computable horizon H(lambda). Let
`Delta_i(A;u,v)` be a **signed** difference of A's output probabilities on
`(P_i,Enc_i(u))` and `(P_i,Enc_i(v))`. At each level, simulate both endpoints
using the actual source S1/S2. This gives the identity

```text
Delta_i(A;u,v)
  = e_i,left(A,u)
    + Delta_ideal-output_i(D;u,v)
    - e_i,right(A,v),

where e_i(A,x) = Pr[A in source Real(x)] - Pr[A in source Ideal(x)].
```

[DERIVED] This is an identity between probability differences, before assuming
any term negligible. The source SIM theorem applies to each e term without a
randomized-output compatibility condition. In the middle term, D receives the
entire P_(i+1) and all B encrypted next-state outputs. D samples the independent
current simulated setup, constructs its simulated keys using those outputs,
and runs A. All current setup secrets therefore belong to D's independent
postprocessing. It never receives an omitted future master.

[DERIVED joint frontier] Telescope the middle term over the B ciphertext
positions. Each resulting term is
`Delta_(i+1)(A_c;T_c(u),T_c(v))`. The reduction A_c uses one common P_(i+1)
and publicly encrypts the other known left/right candidate messages under that
same public key. This preserves correlations with **all** future keys and the
conditional independence of honest encryption coins. Answers agree under R_i.
At the terminal level, g(u)=g(v), so the ideal-output term is exactly zero.

[DERIVED] Expanding the identities down the tree expresses the root gap as
the sum of **2N_H signed one-SIM gaps**. The finite H=2 proof's compatibility
argument has become an explicit telescoping reduction. No premise of the form
“each depth's output distance is at most a selected epsilon” was introduced.

## One uniform reduction, not an increasing list of negligible functions

[DERIVED construction; strict bounded-time sampler] Put
`k=ceil(log2(2*N_H))` and `M=2^k`. Sample exactly k fair bits, independently of
all setup randomness. Ranks below 2N_H identify a node and left/right side.
A larger rank instead runs a valid-domain one-message SIM experiment on the
all-zero message, makes zero key queries and outputs a constant bit. Its gap
is exactly zero. This padding avoids rejection sampling and expected-time
assumptions. For a real rank, the chosen node is a command prefix p.
Compute `(T_p(s0),T_p(s1))` from the selectively chosen initial candidate pair.
The selected side determines which one is submitted as the source's sole
challenge plaintext.

[DERIVED] In its first phase, generate the entire independent future package,
define the challenged level's command functions using only its next public
key, and retain the necessary original-state/path information for the reduction.
The current public key has not been generated yet. The source experiment then
supplies this level's public key, its requested function keys and its one real
or simulated challenge ciphertext.

[DERIVED] Wrap that challenged layer in the ancestor distinguishers from the
one-level expansion. At each ancestor, publicly encrypt all sibling candidate
states according to that ancestor's hybrid position, use S1/S2 to create its
simulated keys and challenge, and continue toward the original host. The
original host sees the entire assembled package. It does not receive the
reduction's retained plaintext candidate pairs or raw setup secrets. For a
right-side choice, complement the final test bit to reverse the sign of that
source Real-minus-Ideal gap.

[DERIVED exact advantage] Every real node/side has probability 1/M and dummy
ranks contribute zero, so the executable strict-PPT reduction satisfies

```text
signed_gap(one-SIM adversary) = Delta_root / M,
2*N_H <= M < 4*N_H.
```

[DERIVED arithmetic identity] An ideal uniform finite choice over the original
2N_H sides has average `Delta_root/(2*N_H)`. That remains the exact arithmetic
identity, not the fair-coin implementation when 2N_H is not a power of two. The
previous draft did not distinguish these sampling conventions; the padded
selector above is the primary executable reduction.

[DERIVED] The path can be unranked without enumerating the tree. Its length is
at most H, and its rank uses O(log(H+1) + H log B) bits, including the B=1
case. All child challenge pairs are
computed from setup-independent Step and initial states before their challenged
instance's setup. A path selected in response to the host's actual ciphertext
behavior would not have this selectivity justification; that is not this
reduction. Auxiliary data includes the complete future package throughout.

[DERIVED resource bound] Each ancestor wrapper invokes the previous
distinguisher once. The simulator obfuscates `Sim.G_f`, whose size depends on
the original bounded Step/encryption circuits, one next-public-key literal and
one fixed-format output. It never contains the preceding distinguisher's code.
Consequently the source's polynomial simulator cost is **not iterated as
T -> poly(T) -> poly(poly(T))**. With an explicit polynomial C bounding one
layer's setup, key generation, encryption and state-computation work, the
selected reduction has runtime at most `T_host + O(H*C)` and polynomial
description size. Integer/rank arithmetic also has polynomial cost in H.
All primitive/state/circuit bounds must be uniform polynomials in lambda.

[DERIVED corollary] If H is polynomially bounded and N_H is polynomial in
lambda, a non-negligible host gap would yield a non-negligible uniform
one-SIM gap, contradicting the source theorem. This proves the claimed
logarithmic horizon for fixed B>1 without requiring a published numerical
advantage bound. When B=1, N_H=H+1, giving polynomial horizon for a single
preauthorized transition sequence. Stopping, restoring or repeating that one
transition does not create a new choice of command. The source's ordinary
asymptotic claim has been used only against a single uniformly constructed PPT
adversary.

## Resource-indexed primitive accounting

[SOURCE / DERIVED] For a challenged level with q preissued keys and **zero
external decryption-oracle queries**, source transitions H6→H7, H8→H9 and
H10→H11 are identical. Local execution of the exposed key programs by the host
does not count as a query to that external source oracle. The remaining
Appendix A reductions have these multiplicities on each SIM side:

| Term | Number of computational hybrid edges | Source |
|---|---:|---|
| iO | 3q | A.1/A.4, A.9, A.16 |
| punctured PRF | q | A.5 |
| commitment hiding | 1 | A.6 |
| NIWI witness indistinguishability | 1 | A.7 |
| PKE IND-CPA | 2 | A.8, A.14 |

[DERIVED conditional envelope] If each epsilon below bounds its indicated
primitive game at the **actual uniform reduction resources**, a conservative
one-SIM bound is

```text
E(q,R) <= 3q*eps_iO(R') + q*eps_PPRF(R') + eps_Com(R')
          + eps_WI(R') + 2*eps_PKE(R') + 2q*nu_NIWI.
```

[DERIVED scope] R' includes honest circuit generation and the selected wrapper's
runtime. The source supplies no numerical epsilon values or concrete parameter
table. This formula is explicit conditional accounting, not a selected
compatibility threshold. The NIWI term conservatively charges bad-equivalence
events per key switch. Any additional nonperfect correctness/equivalence error
must be added; it is not silently set to zero for an alternative implementation.
For the qualitative logarithmic result, the uniform one-SIM reduction above
already suffices and avoids assuming an unspecified universal concrete bound.

[DERIVED tree bound] Let L=B^H be the number of leaves and
`I=(B^H-1)/(B-1)` the internal nodes when B>1. Each internal node has q=B and
each terminal node q=1. With common valid resource envelopes, the root bound is

```text
|Delta_root| <= 2*I*E(B,R*) + 2*L*E(1,R*).
```

[EXECUTED structural check] At B=3,H=2, I=4 and L=9. There are 26 one-SIM
sides and 272 computational primitive edges: 126 iO,42 PRF,26 commitment,
26 WI and52 PKE. The strict selector has M=32, uses five fair bits and six
zero-gap dummy ranks. These are counts, not measured loss values. The script
uniquely unranks every one-SIM side and primitive edge, including right-side
orientation, and verifies the padded selector.

## What remains obstructed for branching polynomial horizons

[DERIVED scoped reduction obstruction] For B>1 and superlogarithmic H,
N_H is superpolynomial. The selected-path reduction can still run in polynomial
time for polynomial H, but its advantage can be negligible even if the host's
gap is substantial. This is a limitation of the audited tree expansion, not a
lower bound against every proof or an attack on the ladder construction.

[EXECUTED control] The negligible function `2^(-sqrt(lambda))`, multiplied by
the binary proof-tree size at `H=sqrt(lambda)`, gives a bound at least1 on the
tested square parameters. Ordinary negligibility alone cannot pay a
superpolynomial branch factor. Separately, the family
`d_h(lambda)=[lambda <= 2^h]` is eventually zero for every fixed h, while its
diagonal `h=ceil(log2(lambda))` is1. Thus reusing the fixed-H conclusion without
the uniform reduction above would have been invalid even for logarithmic H.

[DERIVED frontier audit] Grouping every depth's child ciphertexts into one
joint frontier does not remove their count: depth j has B^j honest encryptions.
The source's q-SIM discussion pads function keys linearly in an a-priori
challenge count q and uses preselected challenge messages. It is not an
on-demand simulator for an unknown set of private states discovered after
setup. Issued keys are program strings the host can inspect and evaluate
locally, so the reduction cannot simply intercept its calls and charge only
branches the host appears to execute. Restricting the interface to an oracle,
or supplying a suitable adaptive/composable simulation theorem, would be a new
premise. No such frontier improvement was established in this source audit.

[OPEN] A separately established subexponential resource/advantage bound could
pay for a larger branch tree through the displayed inequality, or another
proof could avoid that tree. Neither is supplied by ordinary 2013/729 IND_pre
negligibility. Increasing the state space/horizon also requires rechecking that
the interface relation still has nonidentical admissible states.

## Nonvacuity and boundaries of the positive

[DERIVED / EXECUTED] Generalize the byte witness to m-bit state with commands
add1, double and highest-bit infer. Let `m=lambda` and
`H=floor(log_3(lambda))`. For sufficiently large lambda, starting states0 and1
remain below the highest-bit threshold under every permitted path, with
distinct raw states and equal outward traces. The finite script checks 390
complete paths at widths8,16,32,64,128,256. When H>=2, the state
`2^(m-2)-1` has terminal bits1 versus0 under add-then-double and
double-then-add within the allowed horizon. The width8 check has H=1 and uses
the immediate infer operation's nonconstancy instead. This is a nonconstant finite interface with genuine future
state effects, not an encryption benchmark.

[DERIVED] The proof retains actual encrypted next states, but still has a
preissued end. It gives no masterless extension beyond that end, no hidden
fresh observation, no unbiased selected lifetime, and no receipt/finality
binding. Same-key closure retains its separate compatibility obstruction.
The H=2 artifacts and the static predicate positive remain unchanged.

[EXECUTED accounting] No new queries or downloads. Lane totals remain eight
Scry SQL plus one schema, web28, Kagi0. The absolute local source PDF, hash,
sections read and exact replay are recorded in `results.json`.
