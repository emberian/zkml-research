# Public seeded expansion: exact boundary and proof obligation

[DERIVED] This implementation compresses a deterministic public matrix into
a public seed plus context. It does **not** establish that revealing a seed
and expanding SHAKE256 preserves the earlier construction's uniform-public-
matrix security theorem. Successful encryption/decryption checks cannot
establish that missing theorem either.

## The comparison that is false

[DERIVED] Let `E(s,b)` be the deterministic expanded matrix at a fixed public
binding `b`, with `m` residues modulo `q`, on a successful expansion. The two
joint distributions

```
(s, E(s,b))       versus       (s, U),  U uniform in Z_q^m independently of s
```

are efficiently distinguishable: recompute `E(s,b)` and compare it to the
provided matrix. The equality test accepts the first distribution always
and the second with probability `q^-m`. Its distinguishing gap is therefore
`1-q^-m`. A hidden-seed PRG theorem does not apply when the seed is revealed.

[DERIVED] Even without revealing the seed, at a fixed binding a deterministic
lambda-bit seed has at most `2^lambda` possible expanded matrices. Hence its
matrix marginal has statistical distance at least `1-2^lambda/q^m` from
uniform whenever that expression is positive. This is a support-count
obstruction to an information-theoretic replacement, not a refutation of
seeded computational constructions. The joint-distribution test above
does not need this counting argument or an unbounded adversary.

## What rejection actually establishes

[DERIVED conditional ideal-XOF statement] Assume every distinct full chunk
address is assigned an independent uniformly random byte string of its
requested fixed length. For `b=ceil(log2 q)`, masking a candidate byte word
to `b` bits gives exactly uniform `X` in `[0,2^b)`. Accepting only `X<q`
gives a uniform residue in `[0,q)`; no modulo reduction is used. Distinct
candidate words are independent under this idealization. A repeated address
repeats its prior output and is not a fresh independent sample.

[DERIVED finite cap] For a row of `N` coefficients, the algorithm allows

```
C = ceil(4N/1024) + 16 chunks,
M = 1024*C candidates >= 4N + 16384.
```

The ideal candidate success probability is `p=q/2^b >= 1/2`. For the success
count `S`, Markov's inequality applied to `2^-S` gives

```
Pr[S<N] <= 2^N E[2^-S]
         = 2^N (1-p/2)^M
         <= 2^N (3/4)^M
         <= (81/128)^N (3/4)^16384
         < 2^-5461.
```

The last step uses `(3/4)^3=27/64<1/2`. The implementation raises an explicit
error if the cap is exhausted and emits no fallback row. Conditional on
success, the first `N` accepted values are still exactly independent uniform
residues: acceptance indicators determine the success event and are
independent of the uniform values assigned to accepted positions. This
statement is about an ideal random chunk function, not a measured failure
probability over all seeds of fixed SHAKE256. It also does not silently
condition an entire protocol security game on avoiding aborts; that game
must include or charge the abort event.

## Two sufficient kinds of future theorem

[DERIVED: seeded missing-row correction] Seeding only `A` and seeding a
missing public row are distinct changes. If the latter is
`P_missing=Expand(seed_missing,binding_missing)`, then replacing that row by
`Z*A` while retaining the same disclosed seed and unprogrammed SHAKE function
breaks an efficiently checkable relation whenever the replacement differs.
The adversary recomputes the expansion and compares it to `P_missing`.
An ordinary seeded Ring-LWE assumption for `A` alone does not justify this
full-setup hybrid. In particular, do not assume statistical joint
`(seed_missing,P_missing)` regularity against a replacement that ignores
the deterministic expansion constraint: that is the same recomputation
obstruction in another location. A repair requires a full joint simulator
that programs the oracle consistently with all disclosed seeds and rows,
or a new direct construction proof that avoids this invalid hybrid.

[OPEN: direct seeded construction] State and prove hardness for the actual
distribution used here: the challenger samples and reveals the public seed
and bound context, expands `A`, and supplies the construction's Ring-LWE
challenge objects using that same `A`. In both challenge worlds the seed,
public matrix and expansion relation must remain consistent. The statement
must fix the actual number of rows, modulus, dimension, noise law, exposed
credentials, adversary class and allowed seed/context selection. It must
also establish the rank/smoothing/regularity event required by the private
construction under this seeded distribution, without postulating the
impossible joint-seed replacement described above. If missing rows also
carry public expansion seeds, the direct proof must cover that full joint
setup and cannot stop at a seeded Ring-LWE statement for `A`. Neither claim
follows merely from conventional uniform-matrix Ring-LWE or from small
execution tests.

[OPEN: ideal programmable-XOF route] Alternatively give an explicit oracle
model and a reduction that programs fresh seed/domain addresses consistently
with the entire simulated setup, including both `A` and seeded missing rows,
the full-Gaussian `Z*A` hybrid if used, and the rejection transcript. The
proof must handle adversarial oracle queries before seed disclosure, later
recomputation from the public seed, chunk/domain collisions, aborts and
adaptive registry/context dependencies. If the security claim permits
quantum queries/advice, a classical lazy-sampling argument alone is
insufficient: the required quantum programming/query bound must be supplied.
Finally distinguish that ideal-oracle theorem from its concrete SHAKE256
instantiation assumption. This package supplies none of those reductions.

[DERIVED scope] The independent-ideal-XOF statement can explain the intended
uniform public-row distribution inside such a future proof. It is not a
standalone pseudorandomness claim about the revealed seed. Existing
uniform-setup regularity bounds cannot be imported without this bridge or
a separately proved condition applying to the actual expanded matrix.

## Context dependencies and implementation limits

[DERIVED] The parent must choose `binding` before expanding the rows that
depend on it. Bind a profile/parameter digest and a setup identifier at that
stage; include a registry digest only when that registry is already fixed
independently of those rows. Hashing a final registry that itself depends on
the expanded matrix would make the definition circular. Different stages
can use different explicit family names or separately defined bindings,
but their dependency order is part of the parent construction.

[OPEN] Malicious seed selection, seed grinding, cross-protocol reuse,
context substitution and unauthorized reseeding need treatment in the
parent security game. The expander enforces a canonical address, not who
may choose its fields. It uses standard-library SHAKE256 without a new
cryptographic analysis and gives no constant-time or hostile-host claim.
