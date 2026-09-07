# Independent mathematical review of semantic scope and moving frames

[DERIVED verdict; 2026-09-07] **Accepted as written mathematics and a
conditional classical DDH reduction, with the explicit resource and output
qualifications below.** No blocking error was found in the ordered projected
FIFO quotient, its distinction from raw credential leakage, the invertible
moving-frame equations, online adaptive normalization, independent basis-mask
simulation, transported expiry, or the stated probability-gap bound. This
acceptance does not establish selected-trace-only release against the recipient
bundle, a real/ideal protocol theorem, an implementation, or post-quantum privacy.

[SOURCE / EXECUTED identity] The complete frozen targets read were
[SCOPE.md](../semantic_scope/SCOPE.md), SHA256
`97669d67bbf114ee46d6cd04752e36de2dfff6f07e686ec782a480ca482be70c`, and
[LINEAR_CONTINUATION.md](../semantic_scope/LINEAR_CONTINUATION.md), SHA256
`d52086249ebdc317c0e333096df7da3779a3ded4d24748963f5a71e73a14d172`.
The reviewer is the separately assigned `pq_composition` lane, not the author
of either target. `review_manifest.json` records exact source hashes and read
scopes; `commands.txt` and `hashes.stdout.txt` retain the identity-check command
and output. The argument below is independent written review, not a formal or
machine-checked proof. No mathematical construction, disclosure, routing,
extraction, malformed-input or runtime tests were run; no executable artifact
was added. Literature, web, Scry and SQL query counts are all zero.

## 1. Exact quotient and the credential boundary

[SOURCE] `SCOPE.md` lines 54–104 states the raw-key relation and the separation
from the completed selected trace; lines 106–158 states the aggregate/FIFO
quotients and their continuation prerequisites. The designated
[construction review](../review/REVIEW.md), sections 3–5, supplies the exact
static coalition view map and its conditional IND game. These are mathematical
notes, not evidence of a deployed protocol or a leakage simulator.

[DERIVED] For a fixed observer row matrix `Y_J`, the surviving credentials
give `K_J=tau_J+a_J=Y_J*s`. Conversely, from the ordinary IPFE view `(h,K_J)`,
sampling every public token `tau_i` independently and setting
`P_i=g^(y_i*s)/g^tau_i`, with `a_i=k_i-tau_i` for exposed recipients,
reconstructs the designated view exactly. For each fixed master the map from
independent masks to tokens is a bijective translation. Correlated public
recipient keys and redundant rows are therefore included jointly. No extra
independence premise about those public keys is needed.

[DERIVED] The available per-input projection is a **group encoding**
`g^(Y_J*x_t)`. Equality of group encodings is exactly equality over `F_q`;
numerical recovery requires a valid decoder interval. Consequently the phrase
“whole plaintext behavioral quotient” in `SCOPE.md` lines 185–192 must retain
the group-encoding qualification already given at lines 62–83. It does not
assert efficient discrete logarithms for arbitrary field elements. The IND
equivalence relation does not by itself supply a simulator from that leakage.

[DERIVED] Holding metadata, admission state and the observer's available rows
fixed, aggregate equivalence is `Y_J(S-S')=0`: common additions preserve the
difference and a differing available row distinguishes immediately. For equal
length FIFO queues, sufficiency of equality of every ordered `Y_J*x_j` follows
by induction over appends and expiry. For necessity, append `W-n` zeros to fill
capacity without changing old contributions, then append `n` more zeros.
Writing `P_j` for the projected sum after the first `j` old records expire gives
`P_(j-1)-P_j=Y_J*x_j`. If one slot differs, some accessible row differs, and
not all adjacent aggregate observations on that row can coincide. This uses
at most `W` zero appends and `n+1` observations of the chosen row to distinguish
that pair; it does not need a copied or rewound history.

[DERIVED qualification] This exact quotient uses the permitted observations,
zero admissions and sufficient continuation horizon expressly assumed in the
target. It is not the quotient of a sign-only decoder, a row unavailable to
this observer, an exhausted query quota, or a policy forbidding that continuation.
Those restrictions can yield a coarser quotient. A group-valued readout suffices
for the same equality argument: replace subtraction by division of encodings.
The argument concerns equality of behavior, not the cost of scalar recovery.

[DERIVED] The Learn-only separation is valid: two known, admissible inputs
with unequal available projections can have identical acknowledgments and no
delivered Infer answer, while their raw-credential projection views differ.
Knowledge obtainable by a later permitted FIFO continuation does not make it
part of the already completed selected trace. Conversely, learning ordered
projections from observations actually permitted by an ideal interface is not
extra inspection privilege. The two notes keep these statements separate.

## 2. Observable closure, finite witnesses and public resources

[SOURCE] `LINEAR_CONTINUATION.md` lines 18–78 defines the field functionality,
closure, quotient and invertibility argument; lines 203–253 states the privacy
game. All closure and moving-frame claims are the author's derivations rather
than a sourced new iO/FE theorem.

[DERIVED] Let `W` be the span of rows `y_i*A_l*...*A_1`. Appending a matrix
on the right gives another allowed word, so `W*A` is contained in `W`.
Since `A` is invertible, these spaces have the same dimension: `W*A=W`, and
then `W*A^-1=W`. A product frame `F` and its inverse have the same invariance.
Thus `K=ann(W)` is preserved by every state transition. If a difference is not
in `K`, some generating row has a nonzero pairing with it, so the corresponding
word and final observation distinguish it. Common additions cancel in the
difference. Equality up to each earlier answer also preserves any adaptive
command choice made by the same strategy and coins.

[DERIVED] For a full-row-rank basis `B`, choose any fixed right inverse `D`
with `B*D=I_r`. Then `P_A=(B*A)*D` is the unique matrix satisfying
`B*A=P_A*B`; it is invertible by the preceding row-space equality. A row
`v` in `W` has its unique coefficients `alpha=v*D`. These formulas justify
the quotient transition and make all coefficient calculations effective.

[DERIVED resource qualification] The stated closure iteration is polynomial
when the transition family is an **explicitly enumerable list of polynomial
cardinality** `p`, its entries have `O(log q)` bits, and `d` and the initial
row count `m` are polynomial. A polynomial-length succinct description of an
arbitrarily large family is not enough unless it supplies a polynomial-time
routine for computing the needed span images. Under the explicit-list reading
of “polynomially specified” at lines 47–48, a conservative bound for the
literal repeated-basis algorithm is `O(m*d^2 + (p+1)*d^4)` field operations.
This is a derived upper bound, not a measured cost or an optimal algorithm.

[DERIVED] After at most `d-rank(Y)` strict dimension increases the closure
stabilizes. Basis provenance can be retained as independent generating rows,
so a distinguishing word of length at most `d` exists when a difference is
observable. There is no need to enumerate an exponential word set or perform
an exponentially long distinguishing continuation. This does not remove an
external policy's horizon restriction.

[DERIVED] Each public frame is a `d`-by-`d` matrix over `F_q`, regardless of
word length. Multiplication/inversion costs polynomial field work; for example,
naive matrix multiplication takes `O(d^3)` field operations and `Phi_F` uses at
most `d^2` group exponentiations. Normalizing an input uses a matrix-vector
product; a derived row uses the fixed right inverse. With polynomially many
commands and records, the entire wrapper is polynomial. These costs belong in
the DDH distinguisher's resources, rather than in its advantage coefficient.

## 3. Encryption, independent masks and exact FIFO transport

[SOURCE] The equations under review are `LINEAR_CONTINUATION.md` lines 80–201.
The independent-mask setup and common-randomizer joint view used there are
covered by the designated construction review, sections 1–3.

[DERIVED] For any matrix `L`, coordinate multiplication gives

```
Phi_L(Enc_(h_F)(x;R)) = Enc_(h_(L*F))(L*x;R).
Phi_A(Phi_F(C)) = Phi_(A*F)(C).
```

[DERIVED] Thus replacing `(F,C)` by `(A*F,Phi_A(C))` preserves the invariant
with the **same** `R`. The frame key is correlated public postprocessing of
the original setup, not an independently sampled public key. No argument
assumes it is uniform independently of an adaptively chosen `F`. Fresh ingress
alone introduces an independent private randomizer. Multiplying it into the
state adds both plaintext and randomizer; later aggregate randomizers may be
correlated or cancel, and are already part of the joint ciphertext history.

[DERIVED] In frame `F`, write `y_i*F=alpha*B`. Then
`alpha*(tau+a)=y_i*F*s`, so the transformed second component is exactly

```
g^(R*y_i*F*s+y_i*x-R*alpha*tau)
  = (product_l P_l^alpha_l)^R * g^(y_i*x).
```

[DERIVED] Recipient division using `alpha*a` gives the intended group answer.
The basis masks must be independent uniform scalars; all derived masks are
allowed to be correlated linear combinations of that vector. The already
proved affine view map covers these correlations by public postprocessing.
Using one unchanged mask across distinct basis directions would instead
expose their projection-key differences through public token differences.
The fixed-key correction example is also correct: for odd `q`,
`(A-I)s=-2s` at `A=-I` determines the whole scalar master. The moving-frame
proposal does not publish that scalar correction.

[DERIVED] For an input admitted in frame `F_j`, its current transported
contribution is exactly

```
Phi_(F*F_j^-1)(Enc_(h_Fj)(u_j;r_j))
  = Enc_(h_F)(F*F_j^-1*u_j;r_j).
```

[DERIVED] The order `F*F_j^-1` cancels the admission frame on the right.
Multiplication over active records establishes the aggregate invariant, and
division by the transported exact old record removes precisely its evolved
plaintext and original randomizer. This realizes contributions evolving under
every subsequent Step, including steps before other records expire.

[DERIVED] The moving FIFO quotient is the ordered `B` projections of these
**current** contributions. For necessity, choose one differing slot and a
word/row witnessing its closure difference; first apply that word to the whole
queue, then use the zero-expiry argument with that one row. If every aggregate
observation agreed, the slot's projected difference would vanish, a
contradiction. No simultaneous exposure of all closure rows is required for
the mathematical necessity argument. The public frame and FIFO/admission
metadata remain equal and explicit. Sufficiency follows from the quotient
transition `P_A`, common `B*u` admissions and exact FIFO removal.

## 4. Adaptive privacy reduction and probability budget

[SOURCE] `LINEAR_CONTINUATION.md` lines 205–253 invokes the fixed-key adaptive
game of [GENERAL_FIXED_SPAN.md](../../fixed_span/scaling/GENERAL_FIXED_SPAN.md),
lines 22–62 and 92–145. Its earlier independent
[review](../../../adversarial_review/fixed_span_scaling/REPORT.md), sections
1–3, accepts the shared-mask transitions, adaptive history, signed padded
averaging, unreached-request convention and sampling budget. I reread the
complete base lemma and those review sections; I did not rerun their controls.

[DERIVED] There is an exact online reduction to that fixed-key game. Give
the framed adversary the simulated designated package for exposed keys `B*s`.
Maintain its actual public frame `F`. For each reached pair `(u0,u1)`, submit
`(F^-1*u0,F^-1*u1)` to the ordinary challenger and return `Phi_F` of the reply.
All continuation and recipient transforms are computed from the same public
history. The identity

```
Phi_(F^-1)(Enc_(h_F)(u;r)) = Enc_h(F^-1*u;r)
```

[DERIVED] proves the exact conditional distribution of each reply, with its
original fresh `r`. Since `B*F^-1=P_(F^-1)*B` with invertible `P_(F^-1)`,
the normalized pair is admissible if and only if `B*u0=B*u1`. This holds for
each actually reached transcript, even when frames and pairs depend on the
public key, exposed keys and earlier ciphertexts. The reduction runs the
adversary once, predicts no future frames and never independently resamples a
frame key. Invalid pairs use the same fixed abort in every game. No new hybrid
or challenge guess is needed for framing.

[DERIVED accepted bound] Let `r=rank(B)`, `k=d-r`, and let `M` be the least
power of two at least `max(1,T*k)`. For the static full-bundle game and ideal
exact uniform/expected-time scalar sampling, the absolute final-event gap is

```
Delta_frame <= 2*M*epsilon_DDH(t_reduction).
```

[DERIVED] Here `t_reduction` includes the original adversary, the base
fixed-basis simulation, the `r`-mask designated setup map, and all matrix/group
work just described. If `T=0` or `k=0`, the two endpoint distributions are
identical. This is a finite polynomial-history bound, with no assigned
numerical DDH strength and no new adaptive recipient-corruption theorem.

[DERIVED] The base reduction owns at most `d+k+T` field draws. Its designated
setup adds `r` independent token draws; deterministic frame algebra adds none.
For the same `R`-trial capped rejection convention, each draw fails with
probability at most `2^-R`. Coupling the two DDH worlds gives the conservative
accepted correction

```
delta_samp = (d+k+T+r)*2^-R,
Delta_frame <= 2*M*(epsilon_DDH(t_reduction)+2*delta_samp).
```

[DERIVED qualification] This prices the reduction's bounded sampler against
the stated ideal endpoint game. A different endpoint sampler needs its own
coupling. For host-only privacy set the exposed rank to zero, hence `k=d`,
but retain the original `r` basis-token draws. Its setup package is exactly
simulatable from `h`, and there is no projection restriction on message pairs.
This excludes separately leaked recipient answers, coins or master-correlated
auxiliary secrets, as the source game does. No arbitrary additional secret
advice is assumed admissible.

[DERIVED] For a partial static exposed basis `B_J`, the per-record condition
is instead `B_J*F_t^-1*u0=B_J*F_t^-1*u1`. Replacing it by equality under
`B_J` is justified only if that smaller row space is frame-invariant. The
target expressly records this limitation. The full closure bundle satisfies
the stronger invariance needed for its stated frame-independent game.

## 5. Swap witness, decoding and residual obligations

[DERIVED] The proposed swap has `A^2=I`, sends `e_1` to `e_2` on the right,
and fixes `e_3`. Therefore its observable closure is precisely
`span(e_1,e_2)`. The pair `(0,0,z),(0,1,z)` has equal current selected output
and unequal output after one swap. This is a future-relevance witness, **not**
an admissible privacy pair against the full two-row bundle: that bundle
already has both register projections. A distinct privacy witness is
`(0,0,z),(0,0,z')` with `z!=z'`; its difference lies in `ker(B)` and never
affects any permitted answer. Both are ambient field witnesses only.

[DERIVED] Proper closure is necessary for the claimed absence of a raw
master credential from the full bundle: if `r=d`, the exposed vector `B*s`
solves for `s`. If `r<d`, a meaningful protected-input claim additionally
needs two allowed actual inputs with the same `B` projections. Public
`h=g^s` still fixes the master information-theoretically; the surviving
privacy statement is computational and uses honest setup/erasure and the
stated DDH assumption. Neither rank deficiency nor this swap witness proves
ambiguity on a real encoder image.

[DERIVED explicit decoding bound] In the swap/permutation example, suppose
each admitted integer coordinate has absolute value at most `U` and at most
`N` contributions are active. Every transported contribution remains a
permutation of its admitted vector, so every aggregate coordinate has
absolute value at most `N*U`. For the selected coordinate, the integer interval
`[-N*U,N*U]` is injective modulo `q` when `q>2*N*U`. More generally a fixed
integer row has bound `N*U*sum_j abs(y_j)`. A bounded discrete-log algorithm
still has to be affordable for the chosen interval; ordinary baby-step/giant-
step needs square-root-sized work/storage in its interval width, not in its
bit length. These are symbolic conditions, not measured decoder results.

[DERIVED] Arbitrary field matrices preserve the group equations but need
not preserve a small integer interval. The target correctly leaves that
numeric invariant separate. Singular matrices are outside this proof because
`F^-1` is needed; its zero-row example correctly illustrates possible unmasked
fresh coordinates. This review makes no impossibility claim about alternative
singular-transition constructions.

[OPEN unchanged boundary] An implementation must authenticate the original
setup, legal transition, current frame, selected row, derived recipient
key/token, and each record's admission frame. The existing fixed-row journal
or decoder does not automatically implement this new semantics. Raw basis
credentials continue to expose the group-encoded behavioral quotient before
or outside selected releases. No runtime refinement, receiver-independent
release enforcement, nonlinear learner, encoder-image theorem, erasure
mechanism or post-quantum instantiation is established by this acceptance.
