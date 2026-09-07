# General fixed-kernel adaptive DDH lemma

[DERIVED; new proof, scaling review pending] The source IPFE equations support
adaptive input privacy for a fixed query matrix of any polynomial dimension,
with all of its function-key scalars exposed. The proof below generalizes the
previous rank-two, dimension-three lemma. It does not attribute adaptive-key
security or this quantitative bound to the source's selective theorem.

## Completion of the independently reviewed 3D statement

[SOURCE: independent local review] `../../../adversarial_review/fixed_span/REPORT.md`
accepts the frozen `../ADAPTIVE_FIXED_SPAN.md` (SHA256
`091403d6f3e1a7a65e5baef3977dc789595584582d17bbbf2190878fa18874d9`).
It found no blocking algebraic/hybrid error and requires three qualifications:
(1) a selected request never reached returns a fair bit; (2) every invalid pair
causes the same public rejection, including in intermediate games; (3) dyadic
padding makes rank sampling bounded, while exact uniform field sampling is a
separate ideal/expected-time convention. These qualifications are adopted below.
The frozen 3D bytes remain unchanged. This records review completion for that
lemma; it does not label the present generalization independently reviewed.

## Game, fixed basis and source boundary

[DERIVED definition] Let G be a cyclic group of prime order q, with generator g,
and let Y be an m-by-d matrix over F_q of rank r, fixed before honest Setup.
Write k=d-r. Dimensions, a public maximum T of challenge requests, and the
algorithms generating Y and all other public descriptions are polynomially
bounded/uniform for the asymptotic claim. The concrete fixture has d=577,
m=r=16, k=561. A single fixed 2048-bit group is a measured reference, not an
asymptotic group family or a numerical DDH-security estimate.

[DERIVED definition] Choose a d-by-r complement L and d-by-k kernel basis N
such that U=[L N] is invertible and YN=0. Honest setup is equivalently

```
t <- F_q^r, a <- F_q^k; s = Lt+Na
h_i = g^(s_i); all issued key scalars = Ys = YLt.
```

[DERIVED] This produces exactly uniform s because U is invertible. For a
full-row-rank Y with pivot columns P and free columns F, one explicit choice
is L_P=I, L_F=0, N_P=-(Y_P)^(-1)Y_F, N_F=I. Redundant query rows may first be
removed to construct the basis; all original keys remain YLt. No assumption
about a kernel vector's squared norm or orthogonal-complement direct sum is
needed. `linear_audit.py` verifies all 561 rational basis columns for this Y;
its nonzero small pivot determinant also makes the same basis valid modulo q.

[DERIVED definition] The adversary receives h, Y, all m scalar keys, all prior
ciphertexts and its independent initial auxiliary state. It can run any
efficient local operation on them, including malformed-ciphertext computations
and all derived span keys. No master-correlated extra secret, issuer plaintext
or encryption coins are leaked. It adaptively submits at most T pairs (x0,x1)
after seeing this package and preceding replies. The public LR interface checks
Yx0=Yx1 on every actual transcript and otherwise ends with one fixed public
rejection/output in both worlds. One common bit selects every valid reply.
All transitions below use this same common-rejection convention.

[SOURCE] ABDP2015/017, Figure2 / Construction3.1 / Theorem3.2, printed pp.7–9,
supplies Enc(h,x;r)=(g^r,(h_i^r g^x_i)_i), key_y=<s,y>, and a selective
IND-FE-CPA theorem under DDH. The arbitrary fixed-basis, adaptive-message
lemma here is a direct proof for this narrower fixed-key game. It is classical
IND, not a simulator theorem, post-quantum claim or malicious-setup guarantee.

## One challenge: randomize the whole kernel

[DERIVED] Write A_j=g^(a_j). The public key is
`h_i=g^((Lt)_i) product_j A_j^(N_ij)`. For fresh B=g^b the challenge ciphertext is

```
c0 = B
ci = B^((Lt)_i) product_j C_j^(N_ij) g^(x_mu[i]),
```

where initially C_j=A_j^b. These are exactly honest source ciphertexts. Use k
hybrid transitions, replacing C_1,...,C_k in order by independent uniform group
elements. In transition ell, embed one supplied DDH tuple
`(A_ell=g^a, B=g^b, C_ell)`; generate the other a_j and t locally. Earlier
C_j are sampled uniformly, later C_j=B^(a_j). All function keys YLt are known.
The public setup stays exactly honest in both DDH worlds and is generated
without a challenge message. The selected B and C are not used before that
request, so adaptive messages may depend on the complete preceding view.

[DERIVED] Once all k masks are independent uniform, an admissible difference
x1-x0=Nv is removed by the bijection `C_j -> C_j g^(-v_j)`. Conditional on the
whole public setup, the preceding transcript and B, this preserves the joint
uniform mask law. Thus the full selected ciphertext, and every later
interaction, have the same law for both values of mu. The argument uses a
joint mask distribution, not independent indistinguishability claims for
individual coordinates. For k=0, admissibility already requires x0=x1 and
the endpoint gap is exactly zero.

## Adaptive histories and the quantitative reduction

[DERIVED] Let H_j answer the first j requests with x0 and the remainder with
x1, and let p_j be the probability of final output1. At the selected request
j, the reduction chooses an independent fair mu and returns the above selected
ciphertext, with earlier requests answered left and later requests right.
Let s_(j,ell) denote its success probability `[final_output=mu]` after ell
kernel masks have been randomized. Then

```
s_(j,0) = 1/2 + (p_(j-1)-p_j)/2
s_(j,k) = 1/2
sum_(j=1..T) sum_(ell=1..k) (s_(j,ell-1)-s_(j,ell))
    = (p_0-p_T)/2.
```

[DERIVED] Choose one pair (j,ell) by a padded rank: M is the least power of
two at least max(1,Tk), and exactly log2(M) fair bits select a rank. Ranks
outside the Tk real transitions return a fair bit. A selected request that
is never reached also returns a fair bit (equivalently mu was sampled before
execution and never influenced the view). The same one-run adversary and
common-abort interface are used in every transition. Signed averaging, before
taking an absolute value, gives one DDH distinguisher with exact event gap

```
Delta/(2M), where Delta=abs(p_T-p_0).
```

[DERIVED exact-group-sampling bound] Under ideal exact uniform group/field
sampling, or the usual expected-time sampling convention, this proves
`Delta <= 2M epsilon_DDH` for the actual reduction resources. If T,k>0,
`Tk<=M<2Tk`, so `Delta<4Tk epsilon_DDH`. This is a uniform polynomial-time
reduction for polynomial d,m,T with efficient group operations and matrix
algebra. It never chooses a favorable hybrid by nonuniform advice. Its
public-key simulation may require O(dk) group powers and must be included
in the DDH adversary's running time; it is not the measured setup algorithm.
No numerical epsilon is assigned to the concrete group.

[DERIVED literal bounded-bit correction] Field sampling is not automatically
strict worst-case polynomial time. Cap each scalar draw at R trials of
ceil(log2 q) fair bits and abort with a fair output if all fail. The reduction
owns at most d+k+T scalar draws, a conservative bound covering t, all known
a_j, randomized earlier masks, and ordinary encryptions. Hence a coupling
error at most `delta_samp=(d+k+T)2^(-R)` per DDH world suffices. A conservative
literal bounded-bit bound against the ideal endpoint game is

```
Delta <= 2M (epsilon_DDH + 2 delta_samp).
```

[DERIVED] This prices the reduction's own sampling cutoff, not arbitrary
side channels or a separate concrete protocol sampler. The actual Python
code uses rejection sampling and variable-time arithmetic. A strict-time
implementation of the endpoint game requires its own corresponding sampling
contract/coupling if substituted for the ideal game.

[DERIVED fixture coefficients] For one 577-coordinate challenge, k=561 gives
M=1024 and coefficient2048. For the contemplated T=384 inputs, M=262144 and
coefficient524288. These are proof-loss arithmetic, not measured performance
or asserted security bits. The latter run is not performed in this tranche.

## Closure, lifecycle and nonvacuity

[DERIVED] Each public-route aggregate is the product of its at most32 active
ciphertexts. Public insertion multiplies by a fresh input; expiry multiplies
by the inverse of the exact old ciphertext. The aggregate remains encryption
of the exact integer window sum, with randomizers added modulo q. There is no
DDH ciphertext noise or refresh credential. Copying, retaining, combining and
reading all artifacts is permitted efficient postprocessing of the exposed
package; the theorem does not enforce a single history or revoke old inputs.

[DERIVED] Every paired fresh input must agree on all16 projections, including
inputs whose ciphertexts are retained after expiry. Equality of only the current
window's score or class is insufficient. Fixed keys also reveal group-valued
projections and every linear combination in their span on each ciphertext.
The integer decoder's interval does not impose a cryptographic output gate.

[DERIVED] An honest private initializer can generate the uniform master, issue
only these fixed keys, export the public key/keys, and erase its master and all
copies. Later issuers need only that public key and private input coins. This
supplies no online writer master, but requires private honest setup, adequate
erasure, and an issuer boundary hiding raw observations/coins from the host.
The measured process arrangement checks artifact arguments; it cannot prove
those physical assumptions or exclude variable-time execution leakage.

[EXECUTED nonvacuity] The ambient integer kernel witness has entries in [-3,3]
and support in the first32 coordinates. Both zero and that vector lie in the
signed-int8 box and have identical16 projections. Adding the witness to the
first public fixture contribution also stays in [-22,24], preserves its bias
and all16 projections. This does not prove the shifted vector is the encoding
of any text, nor ambiguity for every valid observation from an arbitrary prior.

[DERIVED functional limit] Invisible kernel differences cannot affect any
permitted future fixed-span answer under these linear updates. A plaintext
implementation storing each Yx would realize the same observable learner.
IPFE additionally retains the raw vectors encrypted, with conditional
representation privacy. It does not turn those invisible distinctions into
secret cognition, narrower sign-only release, or an upgradeable query policy.
