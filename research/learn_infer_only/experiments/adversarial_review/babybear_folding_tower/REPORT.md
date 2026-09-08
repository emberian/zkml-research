# Independent review of the actual BabyBear folding tower

[DERIVED verdict, 2026-09-08] **Accepted for the existing ideal sampled
model.** The package constructs the actual 19-round tower over the existing
BabyBear quartic field, proves source-root/order and domain/fibre laws, and
instantiates a far initial word with both accepting and rejecting query
witnesses. Its use of the frozen full-UD consumer is correct. No additional
security budget is obtained by constructing the tower, and actual p3 array,
coset, variable-arity, batching-injection and transcript realization remain
separate obligations.

[EXECUTED scope] The review used all four frozen Lean sources, retained
dependency-ordered isolated checks, independent source/axiom/patch census,
and pure modular/rational arithmetic. It did not launch Lean or duplicate
root's combined closure build. Author artifacts, companion trees, shared
ledgers and commits were untouched. Exact source, evidence and dependency
pins are retained in `INPUTS.json`; this review's manifest binds its outputs.

## 1. Frozen package and evidence

[EXECUTED] Author package:
`research/proof_frontier/2026-09-08/formal/babybear_folding_tower/`.

| Artifact | SHA-256 |
|---|---|
| `manifest.json` | `ae965e4e43fdded42b7992ee8ee9a1a265085c9ab861e2c481fef75ca1e14dc2` |
| `babybear-folding-tower.patch` | `900f184c759ff80a1debe2e585ca9f493b4bd13d65a77feb8762f9d07651779a` |
| `src/Selvage/BabyBearTwoAdic.lean` | `470ebf789a733f160523e816570079bb08ef05276b5b025b92d0fd60379b5eb0` |
| `src/Selvage/PowerTwoRootFolding.lean` | `96b937887805230da7cda826287beefb5b8fb7836168a4e0f56db31d6ca1acaf` |
| `src/Selvage/BabyBearFoldingTower.lean` | `3233a666603b5f1fa98871b7349f3573462a526efac1a770ee82578013a6a314` |
| `src/Selvage/BabyBearFoldingWitnesses.lean` | `5d22c5a62ffac9030378b4fbcf747bf13aad468001a48955ce95485f9c3fdb0f` |

[SOURCE/EXECUTED] The isolated checkout records base commit
`6937394e1dc2c2aaff986c7d4b3a258aca5d16fd` and toolchain
`leanprover/lean4:v4.30.0`. All four `logs/freeze-01…04.json` records match
the exact current source hashes, `source_unchanged=true`, exit code zero
and empty diagnostic logs. Their saved commands compile the four modules
in dependency order. This is retained execution evidence, not a fresh
reviewer build or a claim about root's separate umbrella result.

## 2. Root certificate and actual field

[SOURCE] The base field is the existing
`/Users/ember/dev/minidregg/Selvage/BabyBearExt4.lean:29–59`:
`BabyBear=ZMod 2013265921`, with its existing proved primality instance and
kernel-computed repeated-squaring operation. Lines 109–131 prove
`X^4−11` irreducible and define `Ext4=AdjoinRoot extensionPolynomial`.
The tower does not introduce a parallel finite field or replace this quotient
by a cardinality-only surrogate.

[SOURCE/DERIVED] In `BabyBearTwoAdic.lean:20–48`, the statement-first
`GeneratorContract` is discharged by proving

```text
g = 440564289 = 31^15 mod 2013265921,
g^(2^26) = −1 ≠ 1,
g^(2^27) = 1.
```

[DERIVED] Since the order divides `2^27` but not `2^26`, it is exactly
`2^27`. The proof uses mathlib's `orderOf_eq_prime_pow` with prime 2,
not the Rust constant's label as an assumption. The repeated-squaring
equations and small source-value equality use ordinary Lean kernel
computation; no `native_decide` or external arithmetic oracle appears.
The explicit squared-generator falsifier correctly rules out retaining the
larger order after squaring. This certifies the required two-primary root;
it is not a claim that every unrelated multiplicative-generator fact was proved.

[SOURCE/DERIVED] `extension_generator_primitive:66` transports exact order
through the injective field algebra map. `omega bits` is the mapped root
raised to `2^(27−bits)`; `omega_primitive:79` uses exact power descent for
`bits≤27`. The 20-bit value is the image of `195061667`, and successive
root squaring and half-turn negation are proved. Characteristic-two
exclusion is independently discharged through the same injective base-field
map in `BabyBearFoldingTower.two_ne_zero:29`.

[SOURCE/EXECUTED] The scalar source
`prover/src/babybear.rs:3–13,60–76` supplies the same modulus, adicity,
root and repeated-squaring convention. The active p3 source is the
Cargo-pinned `82cfad73cd734d37a0d51953094f970c531817ec` checkout, whose
`baby-bear/src/baby_bear.rs:42–50` contains its two-adic table. The independent
checker verifies the base prime by trial division, the two order equations,
and **all 28 table entries**, including the exact 20-bit root. These arithmetic
controls corroborate the proof and source mapping; they do not replace the
Lean derivation on the actual extension carrier.

## 3. Domain, square projection, sections, and tower length

[SOURCE/DERIVED] `PowerTwoRootFolding.lean` uses the existing
`PowerTwoFriLevels ell n=Fin(2^(ell−n))`, `FoldingData` and `FoldingTower`.
At level `n`, its root and embedding are

```text
g_n = g^(2^n),           domain_n(i) = g_n^i.
```

[DERIVED] For `n≤ell`, exact root order makes the restricted power map
injective. Every point is nonzero. Levels beyond `ell` are singleton types,
so the definition of domains for every natural number is harmless; folding
data are supplied only below the finite height. There is no impossible
infinite-halving tower hidden in this type.

[SOURCE/DERIVED] For a supported transition let
`N=2^(ell−n)` and `H=N/2`. The exact index functions are:

```text
sq(i)  = i mod H,
sec(k) = k,                  0≤k<H,
neg(i) = (i+H) mod N,
paired(k) = k+H.
```

[DERIVED] Root squaring gives `g_(n+1)=g_n²`. Modulo reduction uses its
proved order, so `domain_(n+1)(sq i)=domain_n(i)²`. The section is a genuine
right inverse; the half-turn is `−1`, so `domain_n(neg i)=−domain_n(i)`.
The existing `FoldingData` laws then give two-element fibres, involutive
negation, and nondegenerate denominators. `negative_section:93` and
`fold_pair:150` explicitly identify the source pair `k,k+H` and denominator
`2g_n^k`; those array choices are not merely inferred from cardinalities.

[SOURCE/DERIVED] `coherent_index_powers:134` starts in the **first folded
pair-index domain**, not the initial full domain. For a seed `s`, its selected
point in level `j+1` is `domain_1(s)^(2^j)`. This follows from exactly the
existing modulo `powerTwoRoundIndex`; no independent-round sampling assumption
is inserted. Round batches remain correlated while their relevant marginals
are uniform in the predecessor theorem.

[EXECUTED/DERIVED] At `ell=20,m=19`, domain sizes run from `2^20` to 2,
and code degree bounds from `2^19` to 1. All nineteen transitions and
twenty used levels satisfy rate exactly one half. The final code is therefore
constant words on two points; there is no extra twentieth fold. Independent
controls cover 193 boundary/interior domain-law cases and 152 coherent-path
cases across the actual nineteen transitions. The general laws are proved
by the Lean source, not by those finite controls.

## 4. Farness and actual verifier witnesses

[SOURCE/DERIVED] `BabyBearFoldingTower.farWord:82` evaluates `X^(2^19)`
on the actual multiplicative embedding. `farWord_not_mem:85` applies the
existing polynomial root-count bound against any polynomial of degree below
`2^19`; equality on all `2^20` distinct points would contradict that bound.
The witness is not merely assumed to be high degree or compared only with
base-field-coefficient polynomials: the RS code is over Ext4.

[DERIVED] Both the witness and every legal source codeword belong to the
larger degree-below-`2^19+1` window, and they are distinct. Its exact RS
minimum-distance bound is
`1−((2^19+1)−1)/2^20=1/2`. Thus the proof of `farWord_relDist:111`
correctly yields distance at least one half, which is strictly greater than
the consumer's `2/5` radius. Increasing the permitted degree to `2^19+1`
does make this word a codeword; `source_degree_falsifier:130` records that
boundary. This is actual-domain farness for one explicit word, not an
initial-farness reduction for arbitrary prover inputs.

[SOURCE/DERIVED] `BabyBearFoldingWitnesses` instantiates the existing
`idealCommitment`: its root is the entire word, verification is pointwise
equality and binding is proved. This is a nonsuccinct, perfectly binding
mathematical witness. Its prefix-indexed transcript selects `farWord` at
level zero and the constant word 1 thereafter; `root_eq_commit` is proved.
It is an actual inhabitant of the transcript interface, not a hypothesized
binding commitment or an event supplied as an assumption.

[DERIVED] The first source polynomial has even degree. Values at opposite
roots are equal, so the odd fold component vanishes for **every Ext4
challenge**, and the first fold at pair index `k` equals
`g^(k·2^19)=(-1)^k`. Query zero therefore checks 1, while query one checks
−1 against the claimed next value 1. Since 2 is nonzero these are distinct.
Later constant-one words fold to constant one and pass the terminal code.

[SOURCE/DERIVED] Consequently `zero_queries_accept:85` constructs real
ideal openings for every challenge vector and any query count at zero seeds.
`query_one_falsifier:117` uses binding to reject the actual one-query first
round at index one. `consumer_inhabited:112` combines initial farness and an
accepted execution; `witnessed_probability_positive:128` proves the acceptance
event has strictly positive finite counting probability. This closes the
empty-event and uninhabited-premise issues for this specific consumer instance.

[DERIVED additional review observation] For this particular ideal strategy,
the only nontrivial conditions are that every initial pair seed is even.
Exactly half of `Fin(2^19)` is even. With the predecessor model's independent
sampling with replacement, its acceptance probability is therefore `2^-3603`.
This counting consequence is not a new exported Lean theorem and does not
improve the general adversarial `2^-55` upper bound. It further confirms that
positive acceptance and rejection coexist without contradiction. The checker
also exercises 32 concrete first-fold arithmetic cases; the source's even-power
argument, not testing base-field challenges, establishes the all-Ext4 statement.

## 5. Full-UD probability application and remaining premises

[SOURCE/DERIVED] `BabyBearFoldingTower.coherent_sound:144` supplies the
constructed tower to the frozen `FullUDSamplingBudget.lean:333`,
`fullUDSampling_babyBear_55`. The remaining external head explicitly takes
a family of `BindingCommitment` structures, its prefix-adaptive transcript,
and that transcript's initial `2/5` farness. Root types and openings remain
parameters; binding is carried as a proposition in the structure, not installed
as a new axiom. `witnessed_sound:145` instantiates all these ideal premises
with the concrete witness.

[SOURCE/DERIVED] The exact experiment samples 19 independent uniform Ext4
challenges and 3603 independent uniform initial pair indices, with replacement.
The transcript may depend on prior challenges, but not future challenges or
the subsequently sampled query seed. Acceptance is the existing sampled
opening/equation predicate plus terminal RS membership, not a replacement
predicate defined to make the theorem easy.

[DERIVED/EXECUTED] The frozen schedule starts at radius `2/5`, uses first
fold radius `1/5`, then radii `(19−j)/95` through zero at level 19.
Its tail radii are positive and below `1/4` in the required rounds, and each
next-radius/query-gap inequality has gap exactly `1/95`. The field has the
previously proved actual cardinality `p^4`. Independent exact rational
arithmetic confirms the existing budget, without optimizing or changing it:

```text
19·2^20 / 2013265921^4 + (94/95)^3603 ≤ 2^-55.
```

[DERIVED] Constructing this tower discharges the mathematical domain/field
inhabitation premise; it does not shrink that error expression or grant new
bits. The full-UD predecessor proofs and constants are unchanged dependencies.
The result is about a finite uniform challenge/query experiment, not the
distribution produced by a deployed Fiat–Shamir challenger or proof of work.

## 6. Source and deployment boundaries

[SOURCE] The scalar Ext6 helper in
`/Users/ember/dev/minidregg/prover/src/mle_kernels.rs:407–438,565–572,650`
pairs natural-order positions `k,k+half` and uses `1/(2g^k)` twiddles.
Its index convention matches the formal one. Its Ext6 carrier is not the
formal Ext4 carrier, so the package correctly declines an execution-equivalence
claim from this syntactic match.

[SOURCE] The active vendored p3 FRI path in
`/Users/ember/dev/breadstuffs/vendor/plonky3-fri-82cfad73/src/two_adic_pcs.rs:230–278`
uses bit-reversed subgroup powers, adjacent conjugate rows and bit-reversed
inverse twiddles. `src/prover.rs:214–245` selects arity, commits rows, obtains
the challenge, folds, and may add the next-height input multiplied by
`beta^arity`. `src/verifier.rs:268–325` processes extra query bits and shifted
row indices. Those array indices are not literally the formal natural-order
indices and modulo projections without a transport theorem.

[SOURCE/DERIVED] The outer PCS source describes evaluations on
`Val::GENERATOR·H` (`two_adic_pcs.rs:626–677`), while the inner binary fold
uses unshifted two-adic roots. The formal tower is the unshifted subgroup.
Coset/polynomial-variable pullback, initial PCS-to-FRI interpretation,
bit-reversal/row-index transport, chosen binary arity, input injection and
extra-query-bit decoding remain visible residuals. The independently assigned
transport lane may consume these frozen laws; this review does not duplicate
or declare that work finished.

[OPEN] Actual initial input-farness, concrete row/MMCS commitment binding,
Fiat–Shamir/challenger/proof-of-work composition and complete transcript
realization remain outside the accepted theorem. The frozen arbitrary-root
timing reduction remains semantic; this package adds no efficient collision
extraction theorem or cost bound. No field-wide negative verdict follows.

## 7. Axiom, dependency, and patch audit

[EXECUTED] An independent comment/string-masking lexer enumerates every
qualified theorem declaration and matches it to an exact `#guard_msgs` /
`#print axioms` pair and to the saved census. All 48 guards are unique and
correctly qualified. Forty-six expect `[propext, Classical.choice, Quot.sound]`;
the two elementary arithmetic lemmas `size_halves` and `levelRoot_succ`
expect `[propext, Quot.sound]`. There are no private theorem omissions,
unmatched guards or extra theorem names. The final saved Lean checks enforce
the exact guarded messages, rather than merely trusting those comment strings.

[EXECUTED] The independent lexical scan finds no owned `sorry`, `admit`,
new `axiom`, `native_decide`, unsafe/external implementation, custom elaborator
or macro, `#eval` or `#reduce`. Ordinary proof tactics and kernel `decide`
remain. These standard logical axioms are not “axiom-free”; no additional
cryptographic or algebraic axiom appears in the pinned theorem dependencies.

[EXECUTED] All sixteen frozen predecessor files match both their original
packages and the isolated checkout. Seven existing carrier/folding/RS/
commitment/probability modules also match the companion and checkout bytes.
All fourteen source-evidence file hashes match. The root census script matches
its recorded hash. The package contains four additive modules, 683 lines and
48 theorem declarations/pins; the proposed umbrella import is solely
`Selvage.BabyBearFoldingWitnesses`.

[EXECUTED] Independent patch reconstruction yields exactly the four frozen
source files, with new-file hunks only and no predecessor edits. Retained
clean `git apply --check`/apply evidence and the isolated import-boundary log
both pass. The patch depends on the named frozen predecessor modules and
existing companion base; it is not presented as self-contained in a bare
checkout. Root owns the combined closure/integration result. This review
does not replace that whole-source build with an assertion about isolated
compiled dependencies.

[EXECUTED] Command and output:

```text
python3 research/learn_infer_only/experiments/adversarial_review/babybear_folding_tower/check.py > research/learn_infer_only/experiments/adversarial_review/babybear_folding_tower/stdout.txt 2> research/learn_infer_only/experiments/adversarial_review/babybear_folding_tower/stderr.txt
```

[EXECUTED] PASS; stdout equals `results.json`, stderr is empty, and all
114 frozen public input/evidence files remain unchanged. The checker records
source/guard census, root table, level sizes, arithmetic cases, exact budget,
and patch/dependency comparisons. No reviewer Lean, crypto or runtime protocol
execution occurred. Source discovery used named local files and `rg`; new web
queries 0, Scry queries 0 and PDF downloads 0. No new absence claim is made.
