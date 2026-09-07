# A positive public linear continuation in a moving encryption frame

[DERIVED proposal] Extend additive state with a fixed finite public set of
invertible linear transitions. Transform the ciphertext **and its public
encryption frame together**. A fixed basis of the observable row-space
closure then suffices for designated output keys. This is a written
construction and conditional reduction, not an implementation or a novelty
claim. All calculations below are symbolic; no construction/runtime or
disclosure test is performed.

[SOURCE boundary] The encryption/mask equations and conditional DDH game
are reused from the frozen [designated review](../review/REVIEW.md),
sections 2–4, particularly lines 173–233 for the game and reduction bound.
Observable closure, the moving frame, transported expiry and their reduction
below are this note's derivations. The source snapshots are in `sources.json`;
no literature novelty or source-implementation refinement is claimed.

## 1. Functionality and its observable closure

[DERIVED definition] Over `F_q`, let the private state be `x∈F_q^d`.
Let `G=<g>` be the source scheme's prime-order group of order `q`.
Permit `Learn(u): x<-x+u`, `Step(A): x<-A*x` for `A` in a fixed finite
public family `mathcal A ⊂ GL_d(F_q)`, and selected observations `y_i*x`.
The group, rows and transition family are fixed before private setup.
Messages and subsequent choices among the permitted operations may be
adaptive. This is a public linear control system, not private nonlinear
training.

[DERIVED output contract] The general cryptographic output is the group
element `g^(y_i*x)`. Equality of these outputs is equivalent to equality of
the field projections because `g` has order `q`; this gives the same
behavioral quotient below. Efficient recovery of the scalar is promised
only for a separately bounded, unambiguous integer range with an affordable
decoder. General matrices over `F_q` do not silently provide efficient
arbitrary-field discrete logarithms.

[DERIVED] Define its observable row space

```
W = span{ y_i * A_l * ... * A_1 : every finite allowed word,
                                      including the empty word }.
```

It can be computed without enumerating all words: start with `W0=rowspan(Y)`
and repeatedly replace `Wn` by `span(Wn union {w*A : w in a basis of Wn,
A in mathcal A})`. Each nonstationary iteration raises dimension, so at most
`d` iterations suffice. Matrix/row reduction is polynomial for polynomial
dimensions and a polynomially specified transition family. This is a
derivation of an algorithm, not a measured run.

[DERIVED behavioral lemma] Let `K=ann(W)`. Then

```
x ~ x' for every permitted future trace  iff  x-x' in K.
```

For sufficiency, each `W*A ⊂ W`, so `A*K ⊂ K`; common additions preserve
the difference, and every output row annihilates `K`. Induction gives equal
adaptive traces. For necessity, if a difference is not annihilated by `W`,
some generating row `y_i*A_l*...*A_1` does not annihilate it; that finite
allowed continuation gives a differing selected answer.

[DERIVED exact quotient] Choose a full-row-rank basis matrix `B` of `W`,
with `r=dim(W)`. For every allowed `A` there is a unique matrix `P_A`
satisfying `B*A=P_A*B`, and every `y_i` has coefficients `beta_i` with
`y_i=beta_i*B`. The plaintext quotient `z=B*x` therefore evolves as

```
Learn(u): z <- z+B*u;
Step(A):  z <- P_A*z;
Infer(i): return g^(beta_i*z), or its specified bounded integer decoding.
```

Because `A` is invertible, right multiplication by `A` preserves row-space
dimension; hence `W*A=W`, `W*A^-1=W`, and `P_A` is invertible. A nonzero
`ker(B)` is forever irrelevant to this whole functionality. Directions in
`ker(Y)` outside `ker(B)` may be hidden from a present answer yet affect a
future one.

## 2. Why a fixed-public-key correction is a different credential

[DERIVED] Applying `A` only to ciphertext coordinates gives

```
product_k C_k^A_jk = g^(R*(A*s)_j + (A*x)_j).
```

This is encryption under public key `g^(A*s)`, not under the original
`g^s`. Restoring the old public key by supplying the host a scalar vector
`delta_A=(A-I)*s` would make the equations work, but that vector is itself
a collection of extra IPFE projection keys. Its leakage need not be confined
to the intended observable space. For example, `A=-I` over an odd-order
field gives `delta_A=-2*s`, which determines the whole master. This is a
scoped algebraic credential gap in that obvious implementation, not a runtime
test or a limitation of the ideal state transition.

## 3. Moving-frame construction: no scalar rekey vector

[DERIVED setup] Sample one original master `s`, publish `h_j=g^s_j`, and
issue only the `r` basis scalars `k=B*s` through the existing private
recipient setup. The intended recipient bundle independently chooses
`a_l∈F_q` for each basis row and publishes

```
P_l=g^a_l,  tau_l=k_l-a_l,  g^tau_l*P_l=product_j h_j^B_lj.
```

The original master and initializer copies are honestly erased. This
proposal uses one recipient bundle holding the full basis mask vector;
multi-recipient policy partitioning is not silently supplied by that choice.

[DERIVED invariant] Maintain a public invertible frame `F`, initially `I`,
and its public key vector

```
h_F[j] = product_k h_k^F_jk = g^(F*s)_j.
```

The encrypted state has the invariant

```
C = Enc_(h_F)(x;R) = (g^R, h_F[j]^R*g^x_j).
```

For a public matrix `L`, define the group operation

```
Phi_L(C) = (C0, product_k C_k^L_jk for j=1..d).
```

Group commutativity and exponent arithmetic give
`Phi_A(Phi_F(C))=Phi_(A*F)(C)`. Thus the authorized transition is simply

```
F' = A*F,   h_F' = A applied multiplicatively to h_F,
C' = Phi_A(C) = Enc_(h_F')(A*x; R).
```

All operands are public group elements and public field coefficients.
There is no surviving scalar `s`, `(A-I)*s`, decryptor, or private rekey
operation at the host. `h_F` is a public frame of the original setup, not
a fresh independent setup whose missing secret must be supplied.

[DERIVED ingress] An honest issuer encrypts each fresh private `u` with
independent private `r` under the authenticated current `h_F`; multiplying
it into `C` gives `Enc_(h_F)(x+u;R+r)`. The issuer must bind that public frame
to the authorized history. Arbitrary externally substituted contexts are not
included in this honest-encryption specification.

[DERIVED recipient transform] For selected row `y_i` in frame `F`, put
`v=y_i*F`. Closure gives a unique `alpha` with `v=alpha*B`. Derive publicly

```
tau_v = alpha*tau,
P_v   = product_l P_l^alpha_l.
```

The recipient can derive `a_v=alpha*a`. Then

```
(C0, product_j C_j^y_ij / C0^tau_v)
  = (g^R, P_v^R*g^(y_i*x)).
```

The recipient divides by `C0^a_v` to obtain exactly the intended group-valued
answer. New words need no new secret setup: all derived output keys and
tokens are linear combinations of the fixed basis package. There may be
many frames, but the secret basis has only `r<=d` scalars.

[DERIVED mask distinction] This uses independent **basis masks**, with a
different derived scalar `alpha*a` for each functional direction. It does
not use one unchanged scalar mask for all directions; that would publish
unmasked differences of projection keys through token differences. All
correlations among the derived keys are deterministic postprocessing of the
already reviewed independent-basis package.

## 4. Exact FIFO continuation, if retained

[DERIVED] To combine this system with a bounded window, keep each original
admitted ciphertext and its public admission frame `F_j`. At current frame
`F`, its active contribution is

```
Phi_(F*F_j^-1)(Enc_(h_Fj)(u_j;r_j))
  = Enc_(h_F)(F*F_j^-1*u_j; r_j).
```

The aggregate is the product of these transported active contributions.
An authorized `Step(A)` transforms all their meanings together by `A`.
An expiry divides the aggregate by the transported **exact original**
record. This removes its evolved message and its original randomizer.
No new private credential is used. Context/frame provenance is additional
public state that must be bound to each record and the continuing history.

[DERIVED] The logical functionality is therefore a window of contributions
that evolve under every later public transition, not a window that forgets
those transitions when old inputs expire. Its behavioral quotient stores
the ordered `B`-projected current contributions, together with the public
frame and FIFO metadata. The FIFO lemma in `SCOPE.md` applies with observation
closure `B`: each slot is distinguished by some allowed transition word and
row when zero-input expiry continuations and those readouts are permitted.

## 5. Conditional privacy reduction and restrictions

[DERIVED normal form] Since `F` is invertible, every honest fresh input
ciphertext has the exact public normalization

```
Phi_(F^-1)(Enc_(h_F)(u;r)) = Enc_h(F^-1*u; r).
```

Its inverse operation `Phi_F` is public. Thus the whole framed ciphertext
history is public postprocessing of ordinary IPFE encryptions of normalized
inputs `F_t^-1*u_t`, with independent private coins. Frame choices and inputs
may depend on the actual preceding public transcript; a reduction computes
each current frame and inverse online without predicting future choices.

[DERIVED] For the full recipient bundle, the existing static exposed-key
lemma applies to the fixed matrix `B`. Its admissibility condition is
`B*F_t^-1*u0 = B*F_t^-1*u1` for each issued input. Since `W*F_t^-1=W`, this
is equivalent to the frame-independent condition `B*u0=B*u1`. The reviewed
DDH adaptive-message bound transfers with polynomial public matrix/group
overhead and the already stated sampling convention. This is a direct
conditional reduction for the group equations, not a Rust/Python source
proof or an executed experiment.

[DERIVED quantitative corollary] More explicitly, take a static full-bundle
adversary making at most `T` honest-encryption challenge requests and a
polynomial number of public frame/continuation operations. At every reached
request, its two candidate inputs obey `B*u0=B*u1`; invalid requests use the
source game's common fixed abort. Put `k=d-r`, and let `M` be the least power
of two at least `max(1,T*k)`. With exact uniform source sampling, the final
event-probability gap is at most `2*M*epsilon_DDH`, where the DDH resources
include the frame calculations and the fixed-basis reduction. If `T=0` or
`k=0`, admissible endpoint views are identical. Under the frozen review's
capped `R`-trial rejection convention, use
`2*M*(epsilon_DDH+2*delta_samp)` with the conservative per-world bound
`delta_samp=(d+k+T+r)*2^(-R)`: the last term prices the independent basis-token
draws. No additional challenge or hybrid loss comes from public framing.
The host-only specialization uses rank zero for its exposed-key matrix,
still with `r` token draws. These are conditional asymptotic/reduction
statements, not a concrete security-bit estimate or an infinite-lifetime
guarantee.

[DERIVED] The host-only specialization remains full input IND hiding:
the independent basis-token package is exactly simulatable from `h`, and
all moving-frame/output operations are public postprocessing. If only an
arbitrary subset of basis scalars is exposed, its exact per-record leakage
uses that subset's rows multiplied by `F_t^-1`; a frame-independent smaller
span claim additionally needs that exposed span to be transition-invariant.
Recipient bundles built from complete invariant observable subspaces can
satisfy that condition. This proposal does not assume it for arbitrary
partial scalar exposure.

[DERIVED proper-closure condition] If `r=d`, the full basis scalars `B*s`
solve for the original master. To retain the no-raw-master positive under
the full surviving bundle, require `r<d` and a nonvacuous admissible input
pair in `ker(B)`. Some transition families make `W` full: a cyclic shift of
all coordinates together with observation of the first coordinate makes
every coordinate eventually observable. In that example the ideal interface
itself communicates the full vector through permitted transitions and
queries. That is interface learnability, not an extra cryptographic
inspection privilege.

[DERIVED restriction to invertible transitions] The proposal does not
silently allow singular `A`. Besides losing the normal form, a singular
frame can leave fresh ingress coordinates without a master mask: a zero
row of `F` has `h_F[j]=1`. Restricting ingress to a preserved image or
changing the encryption primitive would need a different contract.

[DERIVED numeric restriction] General matrices can amplify integer state
or cause modular wrap even while field equations remain correct. Integer
readout bounds require a separate invariant. The concrete permutation
example below preserves coordinate magnitude and supports the ordinary
bounded-window bound. No unlimited-integer or fixed-cost discrete-log
decoding claim follows from abstract field closure.

## 6. Concrete bounded positive: two visible registers and one residual

[DERIVED witness] Take `d=3`, initial observation `y=(1,0,0)`, and a single
allowed matrix swapping the first two coordinates and fixing the third:

```
A = [0 1 0; 1 0 0; 0 0 1],  A^2=I.
W = span{(1,0,0),(0,1,0)},
B = [1 0 0; 0 1 0],
ker(B) = {(0,0,z)}.
```

The states `(0,0,z)` and `(0,1,z)` have the same current answer. After one
permitted swap they have answers zero and one. A previously unobserved
register therefore affects future permitted behavior. Both frames are
public permutations, so the state and public-key bodies swap in the same
way and integer coordinate bounds are preserved.

[DERIVED] The recipient bundle holds independent `a_0,a_1`; the tokens are
`s_0-a_0` and `s_1-a_1`. In frame `I`, the selected output uses the first
derived key; in frame `A`, it uses the second. The host never receives
`s_1-s_0` as a scalar correction. The full bundle recovers `s_0,s_1`, but
not the raw master component `s_2` under the proper-kernel DDH statement.
The residual third coordinate is forever irrelevant to this functionality.
This is a symbolic witness, not a test result or a claim about meaningful
text-encoder ambiguity.

## 7. What this next step would and would not accomplish

[DERIVED] The positive is a closed public transition mechanism with
recipient-hidden outputs and no new host read credential. State hidden from
an answer prefix can affect a future answer; a proper observable closure
leaves a restricted full-coalition raw-state privacy claim. State ciphertext
size remains `d+1` group elements. The fixed recipient basis uses `r`
scalars and public mask keys/tokens; each output is two group elements plus
public binding metadata. These are algebraic sizes, not measured costs.

[DERIVED limit] The full recipient bundle already holds the entire closure's
functional keys. It can obtain the second register's projection before the
actual swap, and it obtains the group-encoded quotient of every retained
record, with numerical recovery where its output bounds permit decoding.
Thus this step does **not** realize selected-history-only release against
that bundle. It advances public protected-state continuation, not the
separate restricted-release problem. The same distinction applies to a
larger proper closure: its forever-hidden kernel cannot be the source of
future observable behavior.

[OPEN implementation boundary] Any future implementation must bind original
setup, legal frame transitions, current frame, selected row, derived
recipient key/token, and each old record's frame into the accepted history.
The existing fixed-row envelope/context code cannot be assumed to support
this new semantics unchanged. No implementation, source mutation, protocol
test, performance result, nonlinear protection or post-quantum claim is
provided here.
