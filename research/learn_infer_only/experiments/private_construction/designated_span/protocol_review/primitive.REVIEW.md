# Recipient-hidden fixed-span DDH variant: independent construction review

[DERIVED verdict] **The proposed transform is correct. Its complete static
coalition view is exactly equivalent, by an efficient distribution-preserving
change of variables, to ordinary fixed-span IPFE with that coalition's
projection-key scalars exposed.** Thus the existing conditional classical DDH
lemma extends to this package without an additional distinguishing-advantage
loss. The host-only specialization has no permitted projection leakage;
the full surviving credential coalition has the entire fixed span.

[DERIVED scope] This is an algebraic and game-based review, not a novelty
claim, a new literature theorem, a formal Lean proof or an implementation.
No construction, extraction, routing or runtime tests were run. Parent-owned
contract/implementation files and all previous lanes were left unchanged.
Local inputs and their hashes are recorded in `sources.json`.

## 1. Exact package and a realizable private setup

[DERIVED definition] Let `G=<g>` have prime order `q`. Arithmetic in exponents
is over `F_q`. Fix polynomially many public rows `y_i∈F_q^d` before the
secret setup and let `Y` be their matrix. Choose

```
s <- F_q^d,       h_j = g^s_j,
k_i = <s,y_i>,   H_i = product_j h_j^y_ij = g^k_i,
a_i <- F_q independently for every i,
A_i = g^a_i,     tau_i = k_i - a_i.
```

The host receives all `h,Y,A,tau`. Recipient `i` receives its dedicated
scalar `a_i`. Public keys, rows, transform tokens, group and recipient
identities belong to one authenticated setup description. The secrecy claim
concerns outputs, not recipient anonymity: the rows and recipient assignment
are public.

[DERIVED setup obligation] Knowing `k_i` and a recipient-supplied group
element `A_i` alone does not give an efficient way to compute the **scalar**
`tau_i=k_i-a_i`. The formula must not conceal a discrete-log operation.
There are two straightforward honest realizations:

1. A private initializer samples `s` and all dedicated `a_i`, privately
   delivers each `a_i`, publishes the package, and erases its secrets/copies.
2. The private initializer supplies the ordinary IPFE scalar `k_i` to
   recipient `i` over an authenticated private channel. That recipient chooses
   its own independent `a_i` and publishes `(A_i,tau_i)`.

The second realization gives genuine recipient-generated key ownership and
does not reveal `a_i` to the initializer. Keeping `k_i` at that recipient adds
no capability beyond `(a_i,tau_i)`, which reconstructs it anyway. Requiring
erasure of this redundant recipient copy is unnecessary for the stated
coalition lemma. The initializer must still erase `s`, its copies of the
issued projection scalars, and other master-correlated setup material. If
the initializer also generated recipient keys, its copies of those keys
must be erased for **host-only** output hiding.

[DERIVED public consistency] Everyone can check

```
g^tau_i * A_i = H_i.
```

In a prime-order cyclic group this forces the intended scalar relation
modulo `q`. It establishes neither recipient possession of `a_i`, honest
master generation, erasure, nor authenticated identity ownership. Those
come from the setup/delivery protocol. A public proof of possession or other
added transcript is not silently included in the lemma below; its joint
simulation must be justified if added. Fresh keys dedicated to this package
avoid importing an unmodeled prior key-use transcript.

## 2. Correctness, joint randomizers and exact linear closure

[DERIVED] Honest public encryption is

```
Enc_h(x;r) = (c0=g^r, c_j=h_j^r * g^x_j),  r <- F_q.
```

For any row, the public transform produces

```
D_i(C) = (c0, product_j c_j^y_ij / c0^tau_i)
       = (g^r, g^(r*k_i + <x,y_i> - r*tau_i))
       = (g^r, A_i^r * g^<x,y_i>).
```

Recipient division by `c0^a_i` gives exactly `g^<x,y_i>`. This is an ElGamal
pair with plaintext a **group-valued inner product**. An integer readout
requires a separately specified injective interval and discrete-log decoder.
For a window of at most `W` inputs with coordinate bound `B_x`, the bound
`B_i=W*B_x*sum_j |y_ij|` suffices; `q>2*B_i` makes the interval
`[-B_i,B_i]` injective. Efficient decoding in the intended interval does not
restrict the group-valued information held by a key holder.

[DERIVED] The same `r` across all coordinates of **one** ciphertext is
intentional. So is the same `c0` across its recipient transforms. The proof
below concerns this full joint package; it does not multiply independent
ElGamal-security claims for its correlated recipient public keys.

[DERIVED] Componentwise multiplication and inversion satisfy the exact
identities

```
Enc(x;r) * Enc(u;t) = Enc(x+u; r+t),
Enc(x;r) / Enc(u;t) = Enc(x-u; r-t),
D_i(C*E) = D_i(C)*D_i(E).
```

Consequently an aggregate is the encryption of the sum of its active inputs
with the sum of their randomizers. Insertion and inversion of the exact old
ciphertext implement a sliding window without a writer master or noise
refresh. Every retained input, intermediate aggregate, transformed pair and
fork remains efficient public postprocessing of the issued ciphertext
history. The aggregate randomizers need not be independent across snapshots.
The mathematical closure is continuing additive state at fixed dimension
and fixed policy, not arbitrary private nonlinear learning.

[DERIVED limitation on coins] Fresh independently issued inputs require
independent private uniform randomizers. Reusing one unknown `r` for two
fresh inputs changes the model: `c_j/c'_j=g^(x_j-x'_j)`, so the host learns
group-valued coordinate differences. Publishing an input's `r` similarly
removes every coordinate mask. These are algebraic observations, not executed
tests. They do not apply to the intended within-ciphertext shared randomizer
or invalidate public arithmetic on a history of independently randomized
inputs. Ordinary polynomially many random collisions are already part of
the probabilistic DDH game; an infinite lifetime is not covered.

## 3. Perfect static-coalition view equivalence

[DERIVED lemma] Fix a subset `J` independently of the secret setup and before
the challenge history. It may depend on the already fixed public `G,Y`.
Let its complete exposed scalar projection package be

```
K_J = (k_i=<s,y_i>) for i in J.
```

Given only ordinary IPFE public material `h`, the public rows `Y`, and
`K_J`, the following simulator constructs the designated public package and
all coalition recipient secrets **without knowing s**:

```
for every i: sample tau_i <- F_q independently
             H_i = product_j h_j^y_ij
             A_i = H_i / g^tau_i
for i in J: a_i = k_i - tau_i
```

For every fixed `s`, the map `a -> tau=Ys-a` is a bijective translation of
`F_q^m`. Thus in the real setup `tau` is uniform and independent of `s`,
and `A_i=H_i/g^tau_i` holds exactly. Revealed `a_i=k_i-tau_i` have precisely
the required correlations with `h,A,tau,K_J`. This proves equality of the
**joint distribution**, not merely equality of marginals or computational
indistinguishability. It remains true for redundant, zero or dependent rows.

[DERIVED converse] From a designated coalition view, discard the extra
public fields and compute `k_i=tau_i+a_i` for `i∈J`. This yields the ordinary
IPFE exposed-key view exactly. Supplying private setup messages `k_i` to
corrupted recipients changes nothing: those messages are already derivable.
All ciphertexts are unchanged by the view map; every public transform can
be computed from `tau` without recipient secrets. Therefore arbitrary
efficient uses of the available coalition keys and public group elements
are covered, not just calls to an approved decoder interface.

[DERIVED consequence] Every adversary against the designated package gives
an ordinary fixed-key IPFE adversary with exactly the same output
probabilities. Simulation adds polynomial work, including the `m*d` public
group-power products and `m` uniform scalar draws. No extra hardness
assumption or multiplicative advantage loss comes from this affine key
translation itself. This statement is a perfect *setup/view* simulation;
it is not a simulation of encrypted states from leakage and not a general
simulation-security or virtual-black-box theorem.

## 4. Adaptive messages and polynomial histories

[DERIVED conditional theorem] Assume classical DDH for a uniform efficient
prime-order group family. For fixed `Y,J`, let

```
r_J = rank(Y_J),  k_J = d-r_J.
```

After receiving `h,Y,A,tau` and the recipient secrets for `J`, an adversary
may adaptively submit at most a public polynomial bound `T` message pairs
`(x0,x1)`. Every actual request is checked for

```
Y_J*x0 = Y_J*x1 in F_q.
```

A failing pair causes the same public rejection in both worlds and every
hybrid. Every valid reply encrypts the selected side using fresh independent
private coins. A single hidden bit selects the entire history. Public
additions, exact expiry, transforms, copies, retained past artifacts and
efficient adaptive continuation are included as postprocessing. No extra
master-correlated auxiliary secret, input coin or unmodeled plaintext
feedback from an uncorrupted recipient is exposed.

[SOURCE: reviewed local theorem] The ordinary game is exactly the game of
`fixed_span/scaling/GENERAL_FIXED_SPAN.md`, specialized to `Y_J`.
`experiments/adversarial_review/fixed_span_scaling/REPORT.md` accepts its
conditional classical fixed-key lemma. The present review also checked its
basis sampling and hybrid obligations: choose an invertible complement/kernel
basis before seeing messages; exposed keys eliminate the unknown kernel
coordinates; randomize all kernel masks with a shared challenge `g^r`;
translate the joint random masks for an admissible difference; use a padded
uniform rank and a fair output for an unreached request. Nothing requires
predicting a future adaptive message.

[DERIVED bound] Write `Delta` for the absolute final-output probability gap
between the two designated worlds and take the least power of two
`M >= max(1,T*k_J)`. The perfect view reduction followed by that lemma gives

```
Delta <= 2*M*epsilon_DDH
```

under ideal exact uniform/expected-time scalar sampling, with the reduction's
actual added resources included in `epsilon_DDH`. If `T=0` or `k_J=0`, the
gap is zero; the latter case has only identical admissible messages. The
uniform corollary is `Delta <= 4*T*k_J*epsilon_DDH` when `T,k_J>0`.
No numerical security estimate is assigned to a particular group.

[DERIVED bounded-bit qualification] Applying the same capped rejection
sampler as the reviewed note, with at most `R` trials per field draw, adds
the simulator's `m` token draws to its conservative budget. A per-DDH-world
coupling bound is

```
delta_samp = (d+k_J+T+m)*2^-R,
Delta <= 2*M*(epsilon_DDH + 2*delta_samp).
```

This is a mathematical sampling convention/correction, not a constant-time
implementation claim. A changed endpoint sampler needs its own coupling.

[DERIVED host-only specialization] For `J=empty`, `Y_J` has no rows, so
**there is no inner-product admissibility restriction at all**. The host's
public package can be produced from `h` and independent `tau`; all inputs
are computationally hidden in the stated classical IND game. Plaintext
answers, signs, decoding-success behavior or timing returned to that host
must be included as additional declared leakage. They do not disappear
merely because the recipient's key file is private.

[DERIVED fixed-coalition specialization] For any predetermined `J`, including
the full surviving recipient set, the information protected is the
difference in `ker(Y_J)`. Every individual issued input must satisfy the
pairing condition, including inputs later expired. Equality only of the
current aggregate, selected score or class is insufficient because the
coalition can process every retained ciphertext with its recovered keys.

[DERIVED fixed-upper-bound corruption] Online revelations within a fixed
predeclared upper-bound set `J0` are safely covered by giving all `J0`
secrets from the start and using `Y_J0` admissibility. This follows immediately
from the static theorem, but uses the whole upper-bound span rather than the
smaller eventually revealed span.

### Adaptive recipient disclosure with an explicit subset-guess loss

[DERIVED definition] A stronger experiment may let the adversary request
recipient scalars after seeing setup and ciphertexts. Each fresh message
pair must agree on all already revealed rows; each later key request must
annihilate **all previous** message-pair differences. Otherwise the
experiment halts with one fixed public rejection and final output zero.
This is a security-game admissibility restriction, not an implemented
mechanism preventing real-world key exposure. Let `J_final` denote the set
of actually revealed indices.

[DERIVED reduction] For each candidate subset `S`, construct a static-key
adversary `B_S` receiving ordinary IPFE keys for `Y_S`. It generates the
designated package by the exact view map and runs the adaptive adversary:

- Reveal requested `a_i=k_i-tau_i` if `i∈S` and the original all-past
  admissibility rule passes; otherwise return final output zero.
- Before forwarding any message pair, additionally require `Y_S*x0=Y_S*x1`;
  return zero if this fails.
- At termination output one exactly when the simulated adversary outputs
  one **and** the set of revealed indices is exactly `S`.

The additional early exits do not discard any output-one run whose eventual
set is `S`. A requested index outside `S` permanently prevents equality of
the eventual sets. A pair differing on a row of `S` permanently prevents
that row from later being revealed in an admissible run; if that row was
already revealed, the original pair check already rejects. A later common
rejection itself has output zero. Thus, for either hidden bit `b`,

```
Pr[B_S outputs 1 in static world b]
  = Pr[adaptive A outputs 1 and J_final=S in world b].
```

[DERIVED bound] Pad **every** static reduction to the same power of two
`M0 >= max(1,T*d)`, regardless of `rank(Y_S)`. Unused transition ranks return
fair bits as in the reviewed lemma. Sample `S` with exactly `m` fair bits
and run only its reduction. Signed averaging works because the output-one
events indexed by `J_final` partition the original event, and the common
padding gives the same denominator for every subset. The mixed DDH
distinguisher has absolute event gap

```
Delta_adaptive / (2^(m+1)*M0),
Delta_adaptive <= 2^(m+1)*M0*epsilon_DDH.
```

The algorithm is uniform polynomial time: it samples one subset and computes
one basis, rather than enumerating all subsets. Its **advantage loss** is
exponential in `m`. Consequently this establishes conditional adaptive
recipient-disclosure privacy for fixed `m` (and polynomially many messages),
or for `m=O(log(lambda))` with the usual asymptotic resource bounds. It does
not yield a negligible bound for unrestricted polynomial `m`. For literal
bounded-bit sampling a conservative common per-world term is
`(2*d+T+m)*2^-R`, substituted for `delta_samp` in the parenthesized DDH bound.

[DERIVED illustration] With the contemplated fixed 16-row, 577-coordinate
package and `T=384`, the common padding is `M0=262144=2^18`, so this coarse
adaptive-disclosure coefficient is `2^35`. This is reduction-loss arithmetic,
not a numerical security level or a measured construction. Neither this
adaptive extension nor its bound is attributed to the source paper.

[OPEN] Removing this subset-guess loss for arbitrary polynomially many fixed
recipient keys needs a further reduction or stronger source theorem. The
plain static-coalition/host-only theorem above does not incur that loss.

## 5. Correlated keys and the exact span leakage

[DERIVED] For any public coefficients `beta`,

```
sum_i beta_i*tau_i = <s, sum_i beta_i*y_i> - sum_i beta_i*a_i.
```

Thus if `sum_i beta_i*y_i=0`, the host learns the scalar mask combination
`sum_i beta_i*a_i = -sum_i beta_i*tau_i`. The associated public recipient
keys are correlated after the tokens are exposed. This does not contradict
host-only input hiding: that combination's plaintext projection is zero,
and the perfect view simulation already includes the correlation.

[DERIVED recipient-key isolation limit] If an uncorrupted row `y_l` lies in
`span{y_i:i∈J}`, the coalition computes `k_l` by the same linear combination,
then obtains the entire recipient scalar `a_l=k_l-tau_l`. A zero row makes
its `a_l=-tau_l` public even for the empty coalition. Consequently these
keys are not independently protected, reusable **general-purpose** ElGamal
keys after publication of `tau`. The exact security property is fixed-span
input confidentiality. Linear dependencies also mean different designated
recipients are not separate authorization domains beyond that span.

[DERIVED] Independent fresh masks are essential to the host-only claim.
With one intentionally shared scalar `a`, the public difference
`tau_i-tau_l=k_i-k_l` is already the ordinary IPFE scalar for `y_i-y_l`.
Independent uniform masks avoid that deterministic cancellation; they do
not mean mask collisions are impossible. The stated probabilistic game
includes rare collisions and identity public keys.

[DERIVED full surviving coalition] If all recipients collude with the host,
they obtain every `k_i` and every linear combination in `rowspan(Y)`. There
is no additional surviving master credential in the listed package. A
proper hidden-state claim requires `rank(Y)<d` **and** two distinct permitted
inputs with the same projections. Public `h` information-theoretically fixes
`s` through discrete logs, so “the master is absent” must mean its scalar
credential was honestly erased and efficient unrestricted recovery is
excluded by the computational assumption; it is not an information-theoretic
claim that the public key admits multiple masters.

[DERIVED] If an efficient procedure recovered an `s'` with `g^s'=h`, this
could be publicly checked. On that event it distinguishes encryption of two
known distinct vectors with the same `Y` projection by removing their masks.
The nonvacuous fixed-span DDH lemma therefore rules out efficient master
recovery as well. If `Y` has full column rank, the scalar projection keys
already solve for `s`, and that privacy game is vacuous. A rank-deficient
map can also be injective on a restricted encoder image; ambient kernel
dimension alone does not prove semantic uncertainty for actual text inputs.

## 6. What this enables and what still needs a separate contract

[DERIVED] This is a positive fixed-policy construction direction: private
initialization can leave public input encryption and additive continuation
usable after the master is erased; the host transforms each permitted
projection to a dedicated recipient key without learning its value; even
the complete listed credential coalition retains only the fixed projection
space, subject to its exact leakage and nonvacuity conditions.

[OPEN] Correctness above assumes a valid input ciphertext and the specified
transform. The ciphertext algebra supplies no binding to genesis, parent,
recipient identity, authorized state, provenance, update count or finality.
The publicly checkable token relation is not such an execution certificate.
Group membership/canonical encoding, authenticated setup/key delivery and
an endpoint contract remain implementation obligations; this review runs no
malformed-input or routing experiment.

[DERIVED] Old ciphertexts remain readable by a recipient after its key is
given out; changing its `a_i` and token does not revoke a previously recovered
`k_i`. Nor do expiry or a decoder interval enforce deletion, query quotas,
current-window-only release or sign-only access. Inputs/coins known to an
issuer coalition or a publicly replayable history are not made unknown by
this construction. Honest private issuance and any erasure needed before
later issuer exposure stay explicit.

[OPEN] The result is classical DDH, not post-quantum. It does not deliver an
evolving private nonlinear policy, unrestricted future query directions,
recipient anonymity, loss-free arbitrary-polynomial-key adaptive corruption, or a universal
simulation of everything communicated by an endpoint. These are the precise
remaining boundaries of the proposed fixed-span variant, not a negative
verdict on recipient-private protected computation.
