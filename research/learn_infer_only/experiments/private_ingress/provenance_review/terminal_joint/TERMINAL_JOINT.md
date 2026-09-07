# Terminal joint-output lemma with a binding current parent

[DERIVED conditional result; 2026-09-07] For the explicit single-prefix,
single-fresh-pair experiment below, a terminal FE message reduction can
include the complete preceding/current/terminal issued-key package, the
next semantic commitment, and its public provenance proof. It never needs
the terminal master secret. Under the inspected source FE and Groth--Sahai
games, the resulting distributions are computationally indistinguishable.
This is an averaged honest-setup **terminal output lemma**, not an H=2
private-ingress construction or a proof of the current rMIFE admissibility
predicate for every realized function/key package.

[DERIVED quantitative form] With all gaps defined as absolute differences
of acceptance probabilities, the reduction below gives

```text
Delta_joint <= delta_CRS(B0) + delta_CRS(B1) + delta_terminal_FE(A) + 2*eta.
```

[DERIVED / SOURCE-conditioned refinement] For the source SXDH CRS and the
source terminal FE proof, this becomes

```text
Delta_joint <= 4*(d1+d2) + 2*p + Q_source(t)*2^(-t) + 2*N*2^(-b).
```

[DERIVED notation] Here d1,d2 bound the specified DDH games in the two source
groups; p bounds one-challenge ordinary PKE at terminal parameter t; and N
counts the bounded field samples whose bit samplers have slack b. The source
FE proof supplies a polynomial Q_source, not explicit numerical coefficients
or a measured reduction time. Every primitive bound must cover the actual
reduction's circuit size and running time. Ordinary PKE/DDH negligibility
does not imply that the displayed sum is at most the current `2^-E`.

[DERIVED parameter premise] For the qualitative source-security consequence,
all other parameters, widths and simulation costs are polynomial in each
challenged primitive parameter. In particular t, the next GS parameter
kappa, and the earlier-layer parameters are chosen in fixed polynomial
relations. A computation polynomial only in an unrelated, much larger
parameter would not automatically be a PPT source-game reduction.

## 1. Exact nonvacuous experiment, before the proof

[DERIVED fixed policy] Work over canonical byte states and a prime-order
group with p_group>256. Genesis is state 0. The first authorized observation
a is in {32,33}, and the first Step replaces the state by a. The final
observation x is in {0,1}, and the final Step is `s'=s+x mod256`, with public
answer ACK. The only terminal function is `g(w)=highbit(first_byte(w))`.
It ignores the remaining payload and all functional coins. These public
membership predicates are the entire authorization policy for this lemma;
no signature, signing key or hidden issuer authority is assumed.

[DERIVED commitment/trace layout] A binding current CRS sigma_C is used for
the genesis commitment `G=Com_C(0;r_G)` and current parent
`C=Com_C(a;r_C)`. The canonical current payload is
`w=(a,r_C,H1)` with `H1=(r_G,a)`. Its relation checks the genesis opening,
a in {32,33}, equality of the duplicated state, and the current opening.
No ignored witness fields or padding carrying arbitrary data are accepted.
The current public proof pi_C proves this true relation. It is not stored
as private history randomness. Fixed-width encodings use zero padding and
reject noncanonical scalars/bytes. Algorithms of the selected groups and
proof system determine their finite encodings; no size measurement is claimed.

[DERIVED observation pair] Both current state messages are w. The two
observation messages are

```text
z0 = (x=0, G, epoch=1, C, pi_C, auth=empty)
z1 = (x=1, G, epoch=1, C, pi_C, auth=empty).
```

[DERIVED distinct terminal messages] In world j the function produces
`s_j=a+j`, samples a next opening r_j, and forms
`H2_j=(r_G,a,r_C,j)`, `m_j=(s_j,r_j,H2_j)` and
`C_j'=Com_N(s_j;r_j)`. Both histories descend from the same G and current C.
Their next states are distinct, and `g(m_0)=g(m_1)=0` for both a=32 and a=33.
An actual host need not know a. The theorem compares the same prefix in both
worlds; it does not prove confidentiality of the prefix state itself.

[DERIVED next provenance relation] R2 checks the genesis opening, the first
membership/Step, the current commitment recomputed from a,r_C, the final
membership/Step, and `Com_N(s_j;r_j)=C_j'`. Its public statement is
`(G,policy,epoch=2,C_j')`; sigma_C and sigma_N are fixed public verifier
parameters. Use the bounded Boolean verifier for these checks and translate
it into scalar quadratic equations: every wire is Boolean, AND is z=xy,
NOT is z=1-x, and the accepting output is 1. Linear copy constraints permit
the source's two scalar-variable lists. This specifies a polynomial relation
compiler at the mathematical level; no compiler implementation or cost
estimate is asserted. Its ordinary true witnesses are the indicated trace
and verifier wires. The proof concerns semantic commitments, not FE
ciphertext bytes.

[DERIVED corrected current function] F checks canonical parsing, G, epoch,
the observation's public proof, authorization, the current commitment
opening, **and the full current history relation internally**. It then
computes the next payload/commitment as above, makes a real proof
`pi_j'=Prove(sigma_N,R2(C_j'),H2_j with openings)`, encrypts m_j using the
terminal state-slot EK, and returns `(success,ct_j',C_j',pi_j',ACK)`.
On any failed check it returns one fixed, publicly distinguishable FAIL.
The terminal ciphertext and commitment/proof use independent allocated
coins. Next proof coins are not copied into the encrypted history. Only
sigma_N will change mode in the proof; sigma_C remains binding throughout.

[DERIVED adversary order] Fix a uniform PPT distinguisher before sampling
the honest setup. No advice depending on the realized hidden setup coins
is supplied. This uses the source terminal game's stated PPT class, without
assuming an additional nonuniform-advice extension. If a chosen terminal
FE theorem also covers nonuniform advice, the same reduction permits advice
fixed before the fresh setup; it still does not permit advice selected
afterward to contain that setup's terminal secret.

[DERIVED output experiment J_j] Generate the full honest package as in
section 2. Evaluate the **ideal randomized F** on (w,z_j), using fresh coins
independent of the package. Give the distinguisher its output, all issued
keys/public descriptions, and the common prefix snapshots. To cover the
current compatibility tester's known-left-input advice, also give it w,z0.
This is stronger than the corresponding host view, which omits those
plaintexts. Do not append an actual current fresh-input challenge ciphertext
or its repeated-evaluation transcript as if it were common auxiliary data.
That would be a different game needing its own bridge to this ideal output.

## 2. A concrete generator for the complete key package

[DERIVED exposure set] The terminal instance is Construction 2 of 2025/330
with n=1, one exposed EK_T and exactly one issued key SK_g. Its terminal
functional coin width can be literally t because g ignores its coins. The
current and predecessor instances have their actual exposed encryption keys
for both state/observation slots and their issued transition keys SK_F and
SK_F0. Include their public function descriptions, all public proof/commitment
parameters, G, current C/pi_C, and the actual ciphertext/snapshot transcript
of the common prefix. Include any common public randomness, but no raw FE
masters, erased per-key generation coins, or setup trapdoors. There is no
further terminal Learn key or second terminal reader in this experiment.

[DERIVED reduction generator] Given public group parameters, sigma_N,
EK_T and SK_g:

1. [DERIVED] Generate sigma_C in binding mode, the genesis opening/G, and
   the independent current FE setup locally. Its master is available to
   the generator, and its encryption keys are public.
2. [DERIVED] Define F with literals sigma_C, sigma_N, G, policy and EK_T;
   issue SK_F using that local current master. F does not contain a future
   dynamic C' literal or SK_g.
3. [DERIVED] Generate the predecessor setup locally. Define F0 with the
   current state EK and sigma_C. Issue SK_F0. Generate the genesis state
   ciphertext and an honestly issued first observation a in {32,33}.
   Run the genuine predecessor evaluation and save all its snapshots.
4. [DERIVED] Recover the produced current payload inside the generator
   using its own current-layer master (for Construction 2, its first PKE
   decryption key suffices). Obtain the actual r_C/H1 paired with the public
   C/pi_C. This preserves any correlations with SK_F0 and its PRF coins.
5. [DERIVED] Output the prescribed erased package and retain w privately
   for making the challenge/advice. The raw local masters and proof setup
   secrets never go to the distinguisher.

[DERIVED predecessor definition] F0 takes the genesis state/opening and an
epoch-0 observation a bound to G. It checks the literal genesis state 0,
its opening/proof and a in {32,33}; chooses r_C; constructs
`(a,r_C,(r_G,a))`, `C=Com_C(a;r_C)` and the true R1 proof; and returns their
current-state encryption, public metadata and ACK. Its only next FE literal
is the current state EK. All its samplers and failure encoding are fixed
public algorithms. The generator runs its issued key, preserving the actual
coin derivation and correlations, rather than substituting a freshly sampled
unrelated current ciphertext.

[DERIVED why it is a reduction] Every step is polynomial at fixed depth
and uses EK_T, not the terminal master. Public terminal EK may therefore
occur literally inside F and inside its exposed issued key. The reduction
does not rely on function hiding, a sealed wrapper or a hidden state EK.
Previous ciphertexts of known-to-the-generator data are generated honestly.
The current/predecessor FE instances need correct public algorithms here;
their confidentiality theorems are not used to establish this terminal
output lemma. Any required wider functional PRF output is explicitly typed
in those local algorithms, with no appeal to the source's general-ellR
security proof for the current layer.

[DERIVED exclusions with a reason] A retained terminal master, an additional
terminal key separating m0,m1, or auxiliary data whose generator requires
the terminal challenge bit defeats this generator's stated premise. A
malicious setup authority retaining a GS extraction/equivocation secret is
outside the honest-erasure experiment. Public Prove and honest issuance of
any known observation remain available; neither is a secret state reader.

## 3. All replacement cases for this pair

[SOURCE game] 2025/330 Definition 4.3, pp.22--23, quantifies over U subsets
of the exposed slot set and gives the tester one identical replacement
plaintext in each replaced slot, f and the remaining left plaintexts. Both
current slots are public here. There is one stored challenge row.

| Replaced slots U | [DERIVED] Consequence for this pair |
|---|---|
| none | The genuine pair (w,z0)/(w,z1); both pass and terminal messages are distinct with equal g. |
| state only | All guards on a candidate w' are identical against z0 and z1. Invalid w' gives FAIL on both. A valid canonical w' equals w: binding fixes a and r_C; fixed G fixes r_G; the one-step policy fixes the rest of H1. Thus the accepting case is the same terminal pair. |
| observation only | The complete arguments (w,z') are identical, including malformed z'. The two ideal output laws are identical without a cryptographic hop. |
| both | The complete arguments (w',z') are identical; the same conclusion holds. |

[DERIVED binding calculation] For the source scalar binding commitment,
`Com(s;r)=((r+t_C*s)P,(r+t_C*s)*alpha_C*P+s*P)`.
Equality of two commitments first gives equality of s modulo p_group by
subtracting alpha_C times the first coordinate, and then equality of r.
Byte/scalar canonicalization gives literal equality. The history relation
above removes free auxiliary fields. This is why a valid state replacement
does not carry an arbitrary extra next-CRS trapdoor as ignored advice.
More general histories with extra authorization/witness fields need their
own joint-advice argument; they are not covered by this uniqueness proof.

[DERIVED terminal compatibility] The terminal source game has n=1 and
I={state}. For U empty, g(m0)=g(m1)=0 exactly, for every pair of openings
and correct histories constructed below. For U={state}, the source uses
the same replacement plaintext in both worlds, so the deterministic output
is identical. Thus the terminal query is admissible with epsilon=0. It is
not borrowing the current layer's desired tiny compatibility bound.

## 4. Hybrid proof of the terminal output lemma

[SOURCE ingredients] Groth--Sahai 2007/155 section 9, pp.24--28, gives the
scalar binding/hiding CRS modes under SXDH. Definition 5, pp.9--10, and
Theorem 18, pp.35--36, give perfect equality between real and simulated
proof distributions on a simulated CRS, even when the tester knows the
simulation trapdoor and chooses its true statement/witness afterward.
The compiled scalar-quadratic relation is the language used here.

[DERIVED H0 -> H1, CRS] H0 is J0 with ideal uniform field sampling. Change
sigma_N from binding to hiding and otherwise run precisely the honest
generator and left output computation. A CRS distinguisher given sigma_N
can perform this entire computation, including all FE setup/key generation,
common-prefix evaluation and left advice, without a next-CRS trapdoor.
The loss is delta_CRS(B0). Programs containing sigma_N change during this
hop by efficient postprocessing of the challenged CRS. No iO equivalence
claim about those differing public programs is used.

[DERIVED H1 -> H2, proof] Describe the hiding distribution as sampled
`(sigma_N,tau_N)` and initially ignore tau_N. Replace the next proof by
`SimProof(sigma_N,tau_N,statement(C'))`. This changes the law by zero under
the source's perfect simulated-CRS property and ideal field sampling. The
tester in that property can compute the package, encrypted payload and all
other correlated data, since it may know the true witness and tau_N.
The statement is true; no false-history simulation is required.

[DERIVED H2 -> H3, common commitment and FE] For the scalar component of
the hiding CRS, let `u_N=t_N*u1_N`. Sample uniform r0 and define

```text
C' = Com_N(s0;r0),
r1 = r0 + t_N*(s0-s1) mod p_group.
```

[DERIVED] Both terminal payloads open exactly the same C'. Each r_j is
uniform, including conditional on the sampled trapdoor and common package,
so both marginals match honest hiding-mode openings. Update every relevant
copy in the canonical payload/history and its relation witness. The same
simulated proof pi' of C' is retained. The terminal FE adversary samples
the group/proof parameters before choosing its FE widths, obtains EK_T
and SK_g from the source oracles, runs the generator in section 2, creates
this pair, and sends `(m0,m1)` as its one terminal challenge. Its returned
ciphertext, together with C',pi' and the saved auxiliary package, is exactly
H2 or H3 according to the terminal bit. It never selects a package after
learning that bit. Loss: the ordinary terminal FE absolute gap.

[DERIVED H3 -> H4, proof] Restore a real proof using the right true witness.
Perfect simulated-CRS equality again gives zero loss. The affine opening
translation is a bijection, so this is the honest right hiding-mode output
distribution, jointly with its correlated encrypted history and package.

[DERIVED H4 -> H5, CRS] Return sigma_N to binding using the right honest
generator. Loss: delta_CRS(B1). H5 is J1 with ideal field sampling. The
current CRS, G and current parent remain in their honest binding mode;
the two endpoint hops never need a trapdoor for the challenged next CRS.
This completes the inequality stated at the start.

## 5. Quantitative source losses and the current threshold

[DERIVED CRS loss] Define d_j for the DDH game in source group j with the
same public bilinear parameters and exponent-sampling convention as the
CRS: alpha is uniform nonzero as on p.24, and t is uniform in Z_p as in
the full CRS algorithms on p.27. Its two distributions are
`(P,alpha*P,t*P,alpha*t*P)` and
`(P,alpha*P,t*P,R)` for independent uniform R. Binding uses the product;
hiding subtracts P in the last coordinate. Bridging through uniform R costs
at most 2*d_j because R and R-P have identical laws. Switching both group
components gives `delta_CRS <= 2*(d1+d2)`. Two endpoint hops cost
`4*(d1+d2)`. This states the exact coefficient convention rather than hiding
it in “commitment security.” If a quantified DDH assumption uses different
zero/nonzero exponent conventions, its conditioning/statistical conversion
must be charged before substituting its numbers for d_j.

[SOURCE / DERIVED terminal FE loss] Use 2025/330 Theorem 6.1 p.50 with n=1,
one key query and one challenge message. Its two ordinary PKE switches are
Hybrid 0->1 (Lemma 6.2 p.64) and Hybrid 3->4 (p.63). Each switches exactly
one ciphertext and can include the generated package by running the
terminal adversary. If p bounds one such **absolute** PKE gap, their sum is
at most 2*p. Definition 3.8 p.18 instead writes a success advantage above
1/2: a bound alpha_PKE in that convention contributes 4*alpha_PKE here.

[SOURCE-conditioned bound] Section 6.1's primitive parameters and Lemmas
6.3--6.8, pp.64--66, bound the internal hops; the p.67 sum cancels the
`2^(2*s_T)` enumeration against per-hop exponents. Including the reverse
traversal and outer equivalent-circuit changes yields

```text
delta_terminal_FE <= 2*p + Q_source(t)*2^(-t)
```

[DERIVED outer iO accounting] The quantitative bound on the outer
equivalent-circuit changes uses section 6.1's stated weak-extractability
gap `2^(-3*s_T-t)` for equivalent circuits. Merely invoking the ordinary
negligibility wording of Lemma 6.3 would leave another unquantified term.

[OPEN quantitative precision] Q_source is a fixed polynomial for the
specified polynomial resource family, absorbing the source's O() constants
and hybrid/reduction costs. The paper does not provide an explicit finite
numeric Q or fully enumerated resource bound; this note does not invent
one. This refinement is conditioned on the source's stated reduction and
weak-extractability/PRF/OWF assumptions for those circuit families, not an
independent repair of Lemma 6.8. Determinism of g establishes exact terminal
challenge compatibility; it does not make every internal program switch
functionally equivalent at all malformed ciphertexts.

[DERIVED finite coins] If a computation needs N field samples, obtain each
from m+b uniform bits reduced modulo its domain size, where m is the ceiling
logarithm of that size. Each sample has statistical distance at most 2^-b
from uniform, by counting preimages. Sequential coupling bounds the full
transcript error by eta<=N*2^-b, including all public proof metadata and
correlated payloads. Allocate independent coin blocks. Comparing both real
endpoint implementations with the ideal-sampling proof costs 2*eta. Any
setup-field samples approximated in the same way count in N too. The proof's
affine coupling and perfect simulation are applied in the ideal-sampling
games, not asserted exact for biased finite-bit samplers.

[DERIVED sampler scope] This statistical replacement applies only to
values requested from fresh uniform coin blocks in setup or the single
ideal F output. The genuine prefix's PRF-derived coins and correlated
snapshots are left untouched in every game. They are not reclassified as
independent uniform field samples or paid for by this statistical bound.
The prefix needs a true correctly formed trace for its actual coins; no
uniformity or confidentiality theorem for that prefix is invoked here.

[DERIVED exact sufficient budget] To make this joint upper bound at most
current epsilon=2^-E, the following four allocated budgets suffice:

```text
d1,d2 <= 2^(-E-5);
p     <= 2^(-E-3);
t - log2(Q_source(t)) >= E+2;
b >= E+3+ceil(log2(N)).
```

[DERIVED] Each of the four summands is then at most 2^(-E-2). These are
conditions on explicit primitive/resource bounds, not numbers supplied by
the ordinary source PKE/DDH theorems. Under additionally quantified rates
`p(t)<=q_P(t)*2^(-t^cP)` and
`d_j(kappa)<=q_Dj(kappa)*2^(-kappa^cDj)` with fixed positive exponents and
fixed polynomial q, a sufficiently large polynomial parameter lift in E
meets the conditions asymptotically; `log Q_source=O(log t)` as usual.
N must be the actual bounded encoding/proof computation's sample count.
No finite parameter set or fit to the earlier illustrative sizing table is
certified here.

[DERIVED first unresolved threshold transition] The ordinary inspected
PKE and SXDH statements supply negligible gaps, not the specified
subexponential rate with these resources. They therefore give the qualitative
terminal lemma, but do not by themselves justify replacing its upper bound
by current `2^-E`. This is the precise missing quantitative premise for
that promotion, separate from the following game-quantifier boundary.

## 6. What this completes and what remains

[DERIVED completed] The joint package is generated in an actual terminal
FE reduction; the correlated proof/commitment switch is given explicitly;
the final payload pair differs and has exact terminal function equality;
all four current replacement subsets are accounted for at the single
canonical parent; and primitive-game losses are separated. The honest
current parent never becomes equivocal. This establishes a classical,
honest-erasure, source-conditioned terminal output lemma for the stated
bounded experiment.

[SOURCE exact compatibility conventions] Definition 4.3 p.22 is headed
`(A,epsilon)-I-randomized-compatible`. It starts from specified input and
function collections and universally quantifies U, replacement plaintexts,
remaining row indices and a function index. Its displayed test calls A on
`(f,U,replacements,left remaining inputs,f(mixed inputs))`; its inequality
is a directed probability difference. No separate next-key generator,
key-conditioned advice variable or averaging over f is displayed there.
Definition 4.4 p.23 quantifies over PPT A, lets it generate its function and
challenge queries adaptively after the current setup, and applies the
compatibility check to the resulting collections using the same A symbol.
It does not explicitly spell out a retained-state interface between this
oracle adversary and its invocation as the compatibility tester.

[SOURCE limited convention search] The notation on p.15 adds no global
nonuniform-advice or setup-generator convention. Explicit nonuniform
adversaries occur in the iO/NIZK definitions, pp.18,21. Footnote 6 p.29
discusses uniform versus nonuniform adversaries for the recalled older
definition/counterexample; it is not an explicit declaration that arbitrary
key-dependent advice is available in Definition 4.3. This finding is limited
to the pinned full-text search for nonuniform/auxiliary/generator/compatible
terms and the cited definition/proof passages reread. It is not a claim that
the source's intended interpretation has been settled by author clarification.

[DERIVED actual lemma order] Writing K for the sampled public package and
the relevant public context, the statement proved here has order

```text
fix D; sample honest setup and K; sample the appropriate ideal F output;
bound |Pr[D(K,Y0)=1] - Pr[D(K,Y1)=1]|.
```

[OPEN current compatibility boundary] The source application would still
need a justified relationship between that experiment and its check on
the realized current function/query collection. An averaged joint-law gap
does not automatically establish a bound for every realized K or every
fixed function sequence. In particular, `|E_K[d_D(K)]|` is not a bound on
`E_K[|d_D(K)|]`, let alone on all conditional gaps. Exceptional-setup,
retained-state and tester-order arguments must be stated rather than
silently provided by the lemma.

[DERIVED hardwiring distinction] The stronger order “sample/fix K, then
choose a polynomial-size tester/advice containing K's terminal decryption
secret” would permit direct decryption of the distinct next messages. That
is a different exposure/quantifier order from the one proved here. Since
Definitions 4.3--4.4 do not explicitly supply that extra advice convention,
this observation is **not** asserted as an obstruction or refutation of the
actual source game. Conversely, the source text does not itself provide the
honest-next-setup averaging bridge needed by this application. Its precise
instantiation remains open.

[OPEN remaining scope] There is no switch between different current states,
no multiple-parent or multiple-row challenge theorem, no claim about
malicious setup/issuance retaining secrets, and no lift to QPT or an
indefinite horizon. Actual fresh-input challenge ciphertexts and their
deterministic repeated evaluation under the issued current key are not
covered by an unsupported correctness-with-auxiliary assumption. The next
proof target, if authorized separately, is the source admissibility bridge
with a quantified primitive rate; this tranche ends with the terminal lemma.

[SOURCE access] Primary algorithms/games were reread from retained local
PDF extracts for [2025/330](https://eprint.iacr.org/2025/330) and
[2007/155](https://eprint.iacr.org/2007/155). Exact mirror paths, SHA-256s,
read locations and frozen input identities are in `sources.json`.
[EXECUTED accounting] Two primary HTML metadata opens; zero search, Scry
SQL/schema or Kagi queries; zero new PDF extracts/downloads; zero attack,
recovery or extraction runtimes. Existing frozen notes/reviews are unchanged.
