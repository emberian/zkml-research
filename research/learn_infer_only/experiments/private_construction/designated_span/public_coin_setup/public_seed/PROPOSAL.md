# Publicly verified seed derivation for the designated setup

[DERIVED; proposed theorem, not independently reviewed] **Yes in a classical
programmable random-oracle model, with a polynomial seed-selection loss.**
The square-root simulator extends to the complete recipient-key and oracle
transcript. A malicious party may choose and grind the public seed after
honest registration; no honest beacon or secret seed is required. The result
does not establish this guarantee for a concrete hash function or in QROM.

[SOURCE: local proof boundary] The equations and static accepted-value
simulation are in [the frozen setup review](../review/REVIEW.md), §§1–4.
Its adaptive-input DDH dependency is
[GENERAL_FIXED_SPAN.md](../../../fixed_span/scaling/GENERAL_FIXED_SPAN.md),
“Adaptive histories and the quantitative reduction.” Exact source pins and
primary-source access levels are in [SOURCES.md](SOURCES.md).

## 1. Game, independence and chronological order

[DERIVED definition] Fix an efficient classical DDH group family with safe
prime `p=2q+1`, odd prime `q`, and generator `g` of `G=QR_p`. Fix full-row-rank
`Y∈F_q^(m×d)`, `1≤m<d`, its deterministic pivot rule, authenticated recipient
slots, and a static exposed subset `J`. All descriptions and bounds below
are polynomial. Recipient authentication is a separate assumption; there is
no possession proof or other key-use transcript in this game.

[DERIVED order] The following is the entire setup interface:

1. Before registration the adversary may make at most `Q_pre` classical
   oracle queries and retain arbitrary independent auxiliary state. Neither
   keys nor oracle randomness are maliciously correlated with that state.
2. Recipients independently sample dedicated uniform `a_i∈F_q`, independently
   of that prehistory and of the random oracle. They publish `A_i=g^a_i` as
   one fixed complete registry; the adversary also receives `a_J`. No key
   substitutions, redraws selected after inspecting their keys, correlated
   keys, or subsequent registrations are allowed by this theorem.
3. The adversary sees the registry, makes arbitrary classical oracle queries,
   computes candidate setups, and chooses a single seed `z*`. It may choose
   a seed based on any part of this transcript, its own coins and `a_J`.
   It may choose a constant seed or a previously unqueried seed. All setup
   coordinates must come from this one seed. Setup failure gives the fixed
   public rejection and final output zero.
4. Once a valid seed is selected, the ordinary fixed-coalition LR game starts.
   The adversary submits at most `T` adaptive pairs with
   `Y_J x0=Y_J x1`; a failing pair uses the same rejection/output zero in both
   worlds. Honest issuance uses fresh independent private scalar coins. The
   adversary can continue querying the public oracle, retain failed seeds,
   all oracle answers, ciphertexts and their public postprocessing. It cannot
   change the deployed setup or obtain an additional LR oracle under another
   candidate key. One hidden bit chooses the whole valid history.

[DERIVED independence clarification] The **oracle and recipient coins**, not
the selected seed, are independent. A seed independent of the oracle is not
required. Malicious polynomial oracle precomputation is allowed and counted;
an externally supplied oracle-correlated secret or a hash chosen by the setup
adversary is not part of the ROM assumption. Registration remains honest.

## 2. Deterministic public recipe and exact rejection

[DERIVED definition] Use an injective, canonical, length-delimited encoding

```
D = enc("designated-public-seed-v1", p,q,g,Y,pivots,cap R,
        complete ordered recipient identities and A values)
query = enc(D,z,role,coordinate,counter)
```

Use the complete registry bytes, not an unproved collision-resistant digest.
The seed is a byte string with one canonical encoding. Group and policy
parameters are fixed before registration. Any allowed salt/domain choice is
included in `z` and counted as a new candidate, not a free knob.

[DERIVED definition] Let `ell_q=ceil(log2 q)` and `ell_p=ceil(log2 p)`.
There are independent domain-separated random-oracle words of `ell_q` bits
for role `tau`, and `ell_p` bits for role `U`. Equivalently use one
`ell_p`-bit oracle, truncate tau answers, and include the unused independent
suffix bits in the simulated view. For each coordinate, inspect counters
`1,...,R`, choosing the first accepted word:

```
tau_i: accept integers 0 <= w < q
U_j:   accept integers 1 <= w < p
```

Fail that candidate seed if any coordinate has no accepted word. Every
counter and failure rule is fixed; the constructor cannot skip an earlier
valid word, substitute a chosen root, or cherry-pick coordinates. Verification
recomputes the exact first-accept rule. `R≥1` is public and polynomial.

[DERIVED unchanged completion] In pivot coordinates let
`Y=[Yp Yf]`, `C=Yp^-1`, `L=-C Yf`, `n=d-m`. For a successful candidate:

```
B_j = U_j^2 mod p;             H_i = A_i*g^tau_i
h_free_j = B_j
h_pivot_i = product_l H_l^C_il * product_j B_j^L_ij.
```

Thus `h^Y_i=A_i*g^tau_i`, and the existing designated transform is unchanged.
The actual public recipe computes no scalar master, no discrete logarithm,
and no private projection-key delivery. Recipient `i` can compute its usual
projection scalar `a_i+tau_i`.

[DERIVED rejection law] Put
`beta_q=1-q/2^ell_q`, `beta_p=1-(p-1)/2^ell_p`. Both are strictly below
`1/2` for these parameters. For one seed first touched after registration,
conditioned on success its accepted tau/U vector is exactly the product of
uniform `F_q` and `F_p*` values. Its failure probability is exactly

```
f_R = 1-(1-beta_q^R)^m*(1-beta_p^R)^n
    <= m*beta_q^R+n*beta_p^R < d*2^-R.
```

Zero U is rejected along with out-of-range words; zero tau is valid.
`U=±1`, hence `B=1`, is valid and must not be repaired. Identity occurs with
probability `1/q` per unselected successful free sample. Squaring is two to
one, so accepted B is exactly uniform in G. There is no modulo-reduction
bias. Across at most `C_seed` adaptively touched fresh seeds, probability
of any failure is at most `C_seed*f_R`. An adversary can deliberately select
failures or bias accepted values; the selected seed is not claimed uniform.

## 3. Programming a whole candidate, including failed tapes

[DERIVED root lemma] Given any `B∈G`, compute
`v=B^((q+1)/2)`. Then `v²=B^(q+1)=B`. The two distinct roots are `v,-v`;
choose each with probability one half. This is exactly the conditional
uniform `U∈F_p*` law given `U²=B`, including `B=1`. No logarithm is used.

[DERIVED finite-tape lemma] Let `S` be a nonempty subset of `ell`-bit words.
Given a prescribed accepted value `u∈S`, sample an ordinary uniform list
`W=(w1,...,wR)`. If W has a first accepted position t, replace `w_t` by u;
leave all other words unchanged. If W has no accepted position, change
nothing. Call the resulting list `P_u(W)`.

[DERIVED proof] If u is uniform in S and independent of W, `P_u(W)` is
**exactly uniform among all R-word lists**. For a particular successful
output list with first acceptance t and accepted value v, u must equal v
(probability `1/|S|`), while the original `w_t` can be any of `|S|` accepted
words; all other words are fixed. Its probability is therefore `2^(-ell R)`.
For a failing output list there is one W and every u works, giving the same
probability. Failure is independent of u. Conditional on success, the
accepted output is u and the rest has exactly the real conditional law.
Suffix bits discarded from a fixed-width tau oracle remain independent.

[DERIVED joint-key simulator] Receive an ordinary IPFE setup `(h,K_J)`.
Before displaying the registry, privately sample independent uniform tau*;
set `H_i=h^Y_i`, `A_i=H_i/g^tau*_i`, and `a_i=K_i-tau*_i` for `i∈J`.
For each free coordinate compute a random-sign root `U*_j` of `h_free_j`.
The frozen exact view lemma and full rank of Y give the identity in law

```
(a, tau*, U*) = independent uniform
               F_q^m × F_q^m × (F_p*)^n
```

where a outside J is only a mathematical variable, never computed. In
particular `(tau*,U*)` is product-uniform conditional on the displayed
registry and `a_J`. The simulator need not know any undisclosed recipient
scalar. This full conditional fact is what allows the registry to be shown
before the candidate seed is known.

[DERIVED online programming] At the **first query of any coordinate/counter
for the guessed candidate seed**, initialize all its d finite R-word lists
using `P_tau*` and `P_U*`. No earlier oracle answer for that seed is changed.
Queries can arrive out of coordinate/counter order; the already sampled
lists answer consistently. Queries beyond R are independent ordinary words.
If the target seed succeeds, its accepted values complete to precisely the
received h. If it fails, its public transcript is still exact and the game
cannot issue a challenge under it. Other seed lists are sampled normally and
their keys are computed publicly from the same fixed A. They require neither
knowledge of a nor another IPFE challenge setup.

[DERIVED chronology check] Before the target's first touch, its latent
`(tau*,U*)` has influenced no response except through A, conditional on which
it is independent uniform. All other seed tapes are independent conditional
on A. Adaptive choice of the target string at that stopping point therefore
preserves the required conditional law; no already exposed value is patched.

[DERIVED] The preceding lemmas give the exact **joint** law of all recipient
keys, successful and failed candidate tapes, partial and out-of-order oracle
answers, selected seed and completed key. Timing, memory, CSPRNG state,
authentication coins dependent on recipient scalars, and an external beacon
transcript are not consequences of this oracle-transcript equality.

## 4. Seed-selection loss and pre-registration queries

[DERIVED counting convention] Number distinct seeds whose relevant-domain
oracle inputs are first touched after registration, in order. Count a seed
even if the first query is only one coordinate or an out-of-cap counter.
If z* was never queried, the verifier's first query inserts it as one last
seed. Let `C_seed` bound this count **through selection**. With `Q_post`
adversarial raw queries before selection, `C_seed≤Q_post+1`. Query repetitions
do not add candidates; postselection queries remain in running-time budgets.
Let `N` be the least power of two at least `max(1,C_seed)`.

[DERIVED reduction] Sample `i∈{1,...,N}` using fair bits. Use the preceding
joint-key simulator at registration, and program only the i-th first-touched
seed. At selection output zero unless the selected seed's index S equals i
and its setup succeeds. Otherwise forward every subsequent LR request to the
ordinary fixed-span IPFE challenger. Padded i values never selected output
zero. This simulator is uniform and runs once; it does not enumerate seeds,
rewind a seed chooser, predict messages, or need to detect known logarithms.

[DERIVED event identity] First suppose no relevant-domain query precedes
registration. For each fixed i and either LR bit b, exact online simulation
and common setup rejection give

```
Pr[B_i outputs 1 | b] = Pr[A outputs 1 and S=i | b].
```

The disjoint S events partition the original output-one event, including
all malicious selection biases. Averaging before taking absolute values
gives IPFE event gap `Delta/N`. Applying the existing fixed-span theorem with
`k_J=d-rank(Y_J)` and least power of two `M≥max(1,T*k_J)` yields

```
Delta <= 2*M*N*epsilon_DDH.
```

All root, oracle-table, bit-tape, group-completion and adversary work belongs
in the DDH resource bound. Failed seeds are simulated exactly; **f_R is not
an additive privacy error** in this explicitly capped protocol. `T=0` gives
identical endpoints. The same zero-gap observation applies if k_J=0 in a
generalized game, though full row rank m<d here ensures k_J>0.

[DERIVED prequery correction] In the full experiment, let Bad mean that a
pre-registration query already contains the exact eventual D. The complete
fresh A vector is uniform on G^m independently of the prehistory. Every
canonical query guesses at most one such vector, so
`Pr[Bad]≤min(1,Q_pre/q^m)`. This uses fresh independent registration; it is
not a random-beacon assumption and includes J=all when scalars are revealed
only upon registration. Run the reduction above in a modified game that
aborts with output zero on Bad. It can detect Bad from its stored queries.
Coupling each endpoint to this game gives the conservative bound

```
Delta <= 2*M*N*epsilon_DDH + 2*min(1,Q_pre/q^m).
```

[DERIVED sampling convention] The finite oracle tapes and signs use fixed
numbers of fair bits. The only expected-time uniform scalar sampling is the
existing DDH reduction plus its m tau* draws. If each such draw is capped at
`S_cap` trials, the frozen proof's conservative per-world budget remains
`delta_red=(d+k_J+T+m)*2^(-S_cap)`. Replace epsilon_DDH in the last display by
`epsilon_DDH+2*delta_red`. This reduction cutoff is distinct from the public
protocol cap R and its exactly modeled setup failures.

## 5. Finite witness, falsifiers and limits

[EXECUTED public finite arithmetic] [finite_witness.py](finite_witness.py),
run by the command retained in [SOURCES.md](SOURCES.md), checks `p=7,q=3,g=2`,
`Y=(1,1)`, R=2. The accepted real and simulated joint laws have the same 54
atoms. The capped joint simulator's 55,296 equally likely choices produce
all 3,072 real registry/tape transcripts with exactly 18 preimages each.
Every successful completion matches its supplied h. Single-candidate failure
is exactly `31/256`. This exhaustive public arithmetic is not DDH evidence.

[EXECUTED nonvacuity and falsifiers] The distinct messages `(0,0)` and `(1,2)`
have the same Y projection. Omitting the random sign yields only three of
six possible U values. Selecting an identity-bearing sample from two
independent successful candidates changes its probability from `1/3` to
`5/9`. These falsify respectively a deterministic-root simulation and a
no-grinding-bias assertion, not the conditional theorem above.

[DERIVED boundary] This is classical ROM, not QROM: recording first queries,
lazy programming and the seed-index guess use classical access. Ordinary
DDH is not post-quantum anyway. Concrete SHA/XOF instantiation, its internal
state, physical timing, malicious recipient registration, multiple deployed
keys/challenge oracles, and adaptive recipient corruption need separate work.
The prequery term uses m≥1; for m=0 use an explicit fresh-domain condition
or a different reduction, not a nonexistent registry entropy bound.

[SOURCE: implementation distinction] RFC 9380 §5 uses wide reduction and
rejects rejection-sampling implementations for its own constant-time goal;
§10.5 discusses simulating a field output through a random preimage. This
proposal is a different, explicitly capped public bit-oracle recipe, not
an RFC 9380 suite or a constant-time implementation claim.
See [RFC 9380](https://www.rfc-editor.org/rfc/rfc9380.html#section-5).

[DERIVED conclusion] Public seed verification can replace the earlier
**honest direct sampler** assumption by an explicit **classical programmable
ROM plus bounded seed-search** assumption while preserving honest independent
recipient registration. It does not certify any concrete hash's random-oracle
behavior. Full recipient coalitions still obtain their complete per-input
fixed projection span, including expired inputs; no selected-answer-only
release, semantic image ambiguity, nonlinear learning, or system isolation
claim follows from this setup improvement.
