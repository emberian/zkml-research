# Independent review: designated setup from public field-element coins

[DERIVED verdict] **Accepted as an exact-distribution construction and a
conditional classical fixed-coalition privacy reduction under the proposal's
stated assumptions.** The public constructor need not compute a scalar master
or receive/deliver scalar projection keys. Publishing the specified public
coins adds no distinguishing advantage to the already reviewed designated
scheme. This is a meaningful removal of the honest dealer's unrestricted
secret and its erasure step, conditional on the specified sampling model.

[DERIVED boundary] This review is written mathematics only. No cryptographic
runtime, disclosure/routing experiment, implementation validation, machine
proof or novelty search was performed. The frozen proposal and local proof
dependencies are identified in `sources.json`. A later implementation must
meet the prerequisites in section 7; this review does not establish them by
inspection of an unbuilt successor.

## 1. Statement and order of the exact experiment

[DERIVED reviewed contract] Let `p=2q+1` be prime, with `q` odd prime. Let
`G=<g>` be the order-`q` quadratic-residue subgroup of `F_p^*`. Fix a full-row-
rank matrix `Y` with `m<d` over `F_q`, its deterministic pivot permutation,
and a static exposed-recipient subset `J`, before honest independent recipient
key generation. Work in the permuted coordinates, so

```
Y = [Yp Yf],  R = Yp^-1,  L = -R*Yf,  n = d-m.
```

Every recipient independently samples private uniform `a_i∈F_q` and publishes
`A_i=g^a_i`. Afterwards the public constructor samples independent uniform
`tau∈F_q^m` and `U∈(F_p^*)^n`, without a secret logarithm or other correlated
setup auxiliary value. Define

```
B_j = U_j^2,
H_i = A_i*g^tau_i,
h_free = B,
h_pivot_i = product_l H_l^R_il * product_j B_j^L_ij.
```

The observer receives the accepted public values `Y,A,tau,U,h`, fixed group
parameters and the recipient scalars `a_J`. All authenticated context fields
derived from this material are public postprocessing. Authentication and
sampling honesty are assumptions; algebraic consistency alone proves neither.

[DERIVED] The order matters to the stated theorem: the rows and exposed
subset are fixed, recipients use independent honest keys, and constructor
coins are independent of those keys. The result does not silently allow
correlated/adaptive registrations, arbitrary public-key substitution, a
malicious sampler, extra setup secrets or a preselected external beacon
transcript. These would be different experiments.

## 2. Correctness and complete joint distribution

[DERIVED squaring lemma] In `F_p^*`, the equation `u^2=B` for `B∈G` has
exactly two solutions. Squaring has kernel `{1,-1}` and image `G`, so uniform
`U∈F_p^*` induces uniform `B∈G`. Independent draws give independent `B_j`.
The zero field element is excluded. The identity `B=1` is valid and has the
two roots `1,-1`; it requires no exceptional rejection.

[DERIVED coupling] Define `b_j=log_g(B_j)` only as a mathematical random
variable. It is uniform in `F_q`; no algorithm computes it. Put

```
k = a+tau,
s_free = b,
s_pivot = R*k+L*b.
```

The public constructor's `h` is exactly `g^s`, and

```
Y*s = Yp*R*k + (Yp*L+Yf)*b = k.
```

For each fixed `a`, the pair `(k,b)` is independent uniform, and the map
`(k,b) -> s` is a bijection with inverse `s -> (Y*s,s_free)`. Consequently
`s` is uniform and independent of `a`. The full marginal law
`(s,a,h,A,tau)` equals ordinary designated setup with independent uniform
`s,a` and `tau=Y*s-a`. This proves the joint law, not merely uniformity of
the public key or an informal assertion that no one knows a logarithm.

[DERIVED atomic check] For a compatible full tuple `(s,a,tau,U)`, the new
experiment assigns probability

```
q^(-m) * q^(-m) * (2q)^(-n)
    = q^(-(d+m)) * 2^(-n).
```

The old experiment samples `s,a` with probability `q^(-(d+m))` and then a
uniform choice of one of two roots per free coordinate, giving the same
probability. Incompatible tuples have probability zero in both experiments.
Thus the roots can be added to the old setup without changing its meaning.

[DERIVED endpoint correctness] The proved identity `Y*s=a+tau` gives

```
product_j h_j^Y_ij = A_i*g^tau_i,
(C0, product_j C_j^Y_ij / C0^tau_i)
  = (g^r, A_i^r*g^(Y_i*x)).
```

The recipient removes `C0^a_i`. Existing addition and exact-original expiry
equations are unchanged. This establishes a group-valued projection;
bounded integer decoding retains its separate range/injectivity contract.

## 3. Exact simulator for the accepted public coins

[DERIVED root simulator] Because `q` is odd, `(q+1)/2` is an integer. For
`B∈G`, define `v=B^((q+1)/2)`. Then `v^2=B^(q+1)=B`. Since `p≡3 mod 4`,
`-1` is outside `G`; `v` and `-v` are the two distinct roots. An independent
fair sign therefore produces precisely the conditional law of `U` given
`U^2=B`, including `B=1`. The operation uses one public exponentiation and
one fair bit per free coordinate, with no discrete logarithm.

[DERIVED static-view theorem] Given an ordinary IPFE public key `h` and its
exposed projection scalars `K_J=(Y*s)_J`, do the following:

1. Sample independent uniform `tau`.
2. Compute `H_i=product_j h_j^Y_ij` and `A_i=H_i/g^tau_i` for every row.
3. Give each exposed recipient `a_i=K_i-tau_i`.
4. For each free coordinate `B_j=h_free_j`, sample its root using the
   preceding lemma.

The existing independent-mask view lemma proves steps 1–3 have the complete
designated distribution. Step 4 samples the exact conditional distribution
of the additional transcript. The pivot formula recomputes the supplied
`h_pivot`: it holds in exponents by invertibility of `Yp`. Hence the complete
new view has a perfect efficient simulator from the old IPFE view.

[DERIVED chronology] The simulator may privately sample `tau` before
presenting `A`. This does not change the distribution of the displayed
chronological transcript: it can reveal `A` first and reveal the remaining
values later. No adversarial registration or external coin service must be
answered in between under this contract. If such interaction is added, the
same static coupling does not automatically provide its online simulator.

[DERIVED converse] From the new view, compute `K_J=a_J+tau_J` and retain
`h,Y`; this is the ordinary IPFE view. Thus the accepted coins are neither
a new projection key nor a hidden read-all credential in this experiment.
The statement covers any efficient use of the complete available view, not
only the nominal transform method.

## 4. Transfer of adaptive-input security

[SOURCE boundary] The frozen designated review, section 4, and its reviewed
general fixed-span dependency establish a conditional classical DDH theorem
for a static exposed matrix and adaptively chosen honest-encryption message
pairs, with a common invalid-request rule and bounded polynomial history.
They are local derived results, not an adaptive claim attributed here to an
external paper.

[DERIVED corollary] Let `r_J=rank(Y_J)` and `k_J=d-r_J`. After receiving
the new view, an adversary may adaptively request at most `T` encryptions of
pairs satisfying `Y_J*x0=Y_J*x1`. Each honest issuance uses fresh independent
private encryption coins. A failing request uses the source game's same
fixed rejection in both worlds and every hybrid. Public additions, retained
objects, exact expiry and polynomial adaptive computation are postprocessing.

Put `M` equal to the least power of two at least `max(1,T*k_J)`. Under the
source's exact uniform/expected-time sampling convention, the distinguishing
event-probability gap obeys

```
Delta <= 2*M*epsilon_DDH.
```

The resources defining `epsilon_DDH` include public root reconstruction and
all context work. There is no extra advantage factor for this setup. `T=0`
or `k_J=0` gives identical endpoint views. The host-only case has `J=empty`
and no input-pair projection restriction. Recipient feedback, extra setup
secrets and plaintext/encryption-coin exposure are not silently included.
This is not an infinite-lifetime or concrete-bit-strength claim.

[DERIVED] Under the frozen review's ideal capped scalar-sampler correction,
its per-DDH-world budget `(d+k_J+T+m)*2^(-R)` still suffices for the accepted-
coin simulator: roots add only exact fair signs, not field draws. A successor
that changes the endpoint sampler or publishes extra randomness must give
its own coupling. No fixed cap or numerical error budget for an unbuilt
successor is certified here.

## 5. Optional extension: the complete ideal rejection tape

[DERIVED separate lemma] The accepted-value boundary can be broadened for
one precise sampler. To sample uniformly from a finite acceptance set
`S⊂{0,1}^ell`, draw independent uniform `ell`-bit words until the first word
in `S`. Publish the complete sequence, including rejected words and the
accepted word. For `tau`, use integer words in `[0,q)`; for `U`, use words
in `[1,p)` with `ell=ceil(log2(p))`. Each has acceptance probability greater
than one half for the stated prime parameters.

[DERIVED conditional-tape proof] Fix an accepted value `u∈S`. A transcript
of `t-1` specified rejected words followed by `u` has unconditional
probability `2^(-ell*t)`. Since the accepted value is uniform on `S`, its
conditional probability given `u` is

```
|S| * 2^(-ell*t).
```

This conditional law is independent of which `u` is fixed. To simulate it,
run the same independent-word sampler until it first accepts, retain only
its preceding rejected words, and replace the final accepted word with the
already specified `u`. The count and rejected words have exactly the required
law. Apply this independently to the `tau` values and simulated roots `U`.
The result is a perfect simulator for **all bits consumed by this literal
ideal sampler**, with expected fewer than two candidate words per draw.
Unused independent words, if a fixed independent tail is also published,
can simply be sampled afresh.

[DERIVED limits] This optional lemma removes any need to erase rejected
coins from that ideal direct sampler. It does not simulate a CSPRNG seed,
its correlated internal state, a hash preimage, a public-beacon attestation,
or any arbitrary deterministic generator transcript. Those are different
objects. A capped sampler also has a failure event; a cap of `R` candidates
per value makes the union probability at most `(m+n)*2^(-R)=d*2^(-R)` for
this setup's public values. That is a setup coupling term, not by itself a
replacement for the complete DDH simulator's scalar-sampling budget.

## 6. What public verification cannot establish

[DERIVED scope counterexample, no experiment] Choosing `U=±g^c` with a
uniform scalar `c` and a fair sign gives **the same uniform distribution on
`F_p^*`** as the honest accepted public value. Yet a party retaining `c`
knows `log_g(U^2)=2c`. With the full recipient projection package `k`, such
a party can reconstruct `s_pivot=R*k+L*b` and `s_free=b`. Therefore even
perfect marginal uniformity and all public consistency equations do not
certify absence of auxiliary logarithms. The promise includes the specified
direct field-element sampling algorithm and absence of such extra setup
information, not merely a statistical assertion about `U`.

[DERIVED] Publishing an exponent or using `g^(hash(seed))` with a public
scalar hash is precisely the wrong implementation of the free group sample.
The root transcript is safe because it is efficiently reconstructible from
the group point; an exponent transcript is a different capability. This is
a mathematical comparison of setup interfaces, not a runtime disclosure test.

[DERIVED registration boundary] The host-only statement also relies on
honest independently secret recipient masks. A deliberately public recipient
scalar supplies that projection to the host. Correlated registrations can
likewise invalidate the independent-mask view theorem. Group membership and
the equation `g^tau_i*A_i=h^Y_i` do not prove independent generation or secret
ownership. The proposal correctly excludes these cases; this review does
not silently replace that assumption with a proof-of-possession protocol.

[DERIVED remaining functionality] All recipients together still have the
complete fixed projection span on every issued input, including expired
inputs. `m<d` is necessary here for a nontrivial ambient residual, and actual
input-image nonvacuity remains separate. The result removes the specified
dealer master; it does not enforce selected-output-only release, conceal
nonlinear learning, give post-quantum security or defeat a shared-machine
operator who can read recipients' memory.

## 7. Prerequisites for a positive implementation successor

[DERIVED implementation contract] A normal successor can proceed under the
accepted mathematics if it makes these requirements explicit:

1. Pin the actual safe-prime group and order, nonzero/subgroup domains and
   canonical encodings. Do not reject identity samples merely because their
   logarithm happens to be zero; rejection would change the specified law.
2. Use the fixed full-rank matrix and an inverse verified over `F_q`, with
   coordinate permutation restored correctly. The earlier independently
   reviewed workload reports first-16 pivots and determinant `-812032080`;
   this review reads that evidence and does not recompute it.
3. Keep independently sampled recipient scalars private in their owning
   process; publish only authenticated `A_i`. No scalar projection delivery
   or scalar master generation belongs in the public constructor.
4. Sample `tau` directly uniformly modulo `q` and `U` directly uniformly in
   `F_p^*`, with an explicit unbiased rejection method. Compute `B=U^2`.
   Generating group points from sampled scalar exponents is a different
   algorithm, even when their public marginals look uniform.
5. Bind and retain the exact accepted transcript, matrix/pivots, recipient
   identities and recomputed public context. The verifier recomputes `B,H,h`
   and every token equation. If publishing a full ideal tape, use precisely
   the separately analyzed sampler and bind that transcript too.
6. State who supplies the honest independent public randomness and which
   auxiliary information is in scope. A passing recomputation is consistency
   evidence, not a beacon-security, entropy or no-retained-log proof.
7. Preserve private independent fresh encryption randomness. Public setup
   coins never become the issuance randomizer. Keep the existing bounded
   decoder, exact-original expiry and selected-history assumptions visible.
8. Keep earlier evidence immutable. Report normal source/byte/correctness
   checks as implementation evidence, separately from this conditional
   mathematical privacy theorem and the remaining operator/erasure assumptions.

[DERIVED final disposition] No mathematical blocker was found for the scoped
positive successor. Its justification is the exact joint simulator, including
the public roots; it does not rest on an unsupported assertion that publicly
sampled group points necessarily have unknown logarithms under every setup
procedure.
