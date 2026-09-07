# A compact normal form for this specific finite learner

[DERIVED / EXECUTED] The generic exponential fork table is unnecessary for the
mistake-driven learner in `README.md`. Its exact remaining-horizon quotient has
a closed form. This is a visible mathematical abstraction, not encryption of
original scores. The original table/compiler/evaluator artifacts remain frozen.

[DERIVED definition] At `r>0` remaining commands, replace each score `w` by

```
q_r(w) = max(-r, min(r-1, w)).
```

At `r=0`, use one terminal representative. To evaluate, use the same prediction
and mistake update on the representative, decrement `r`, and normalize both
coordinates for `r-1`. The program stores only the two visible representatives
and the public remaining horizon. It does not store a precomputed tree or a
catalog. At H=4 the representatives range over `{-4,...,3}²`, exactly 64 classes.

[DERIVED simulation proof] For every integer score and `r>0`, normalization
preserves its sign, so it preserves the current prediction and the condition
for a mistake update. Let `g_+(w)=w+1` for negative w and w otherwise; let
`g_-(w)=w-1` for nonnegative w and w otherwise. Then

```
q_(r-1)(g_y(q_r(w))) = q_(r-1)(g_y(w)).
```

For `r=1` both successors are terminal. For `r>1`, scores already in the
normalization interval are immediate. If `w<-r`, both sides after either update
normalize to `-(r-1)`; if `w>r-1`, both normalize to `r-2`. The unchanged other
coordinate commutes with nested normalization as well. These identities give
an exact forward simulation for every finite future command sequence, including
adaptive choices and forks. There is no cryptographic or probabilistic premise.

[DERIVED converse] Distinct normalized scores are distinguishable within r
commands. Different signs need one inference. For negative `a<b`, use `-b`
positive observations and infer; this takes at most r commands. For nonnegative
`a<b`, use `a+1` negative observations and infer, again at most r commands.
A differing coordinate can be queried independently. Thus equality of the
normal form is exactly complete fork-interface equivalence, rather than merely
a sufficient relation. On the original finite domain, all 289 initial states
have distinct representatives by H=9; the privacy challenge then has no
nonidentical admissible pair.

[DERIVED size and lifecycle] Initialization takes a constant number of integer
operations, and each step takes a constant number, on integers with O(log H)
bits. There is no exponential preprocessing for this specific functionality.
The initial H4 class contains six bits of information; the actual JSON resident
uses 87 bytes and the self-contained source, including its audit mode, uses
7,840 bytes. These are the actual artifacts, not a six-bit total software claim.
The inherited honest PRIVATE initialization and erasure assumptions still
apply. The normalized confidence values are public. No raw original scores,
key, private observation channel, integrity gate or continuity resource is
present at runtime.

[EXECUTED] The independent table-class comparison checks all 83,521 ordered
initial pairs at H4. There are 20,808 local output/successor commutation checks
(all 289 states, six commands, every remaining horizon 1 through 12), and
449,106 full-tree runtime edges are compared to the independent direct oracle.
All pass. The all-integer/all-finite-horizon statement above is a paper-and-pencil
derivation; the executable has an explicit 0..12 horizon guard and these finite
checks. It is not a Lean theorem.

[EXECUTED] Run the compact deployment from the repository root:

```sh
python3 -I -B research/learn_infer_only/experiments/private_construction/practical_bounded/compact.py run --resident research/learn_infer_only/experiments/private_construction/practical_bounded/results/compact_resident.json --commands infer_1,learn_1_positive,learn_1_positive,infer_1
```

Output is `{"outputs": [0, "ack", "ack", 1], "remaining": 0}`. The synthetic
initial state is `(-8,-2)`; the public resident contains `(-4,-2)` at r=4.
Its second context adapts during the permitted interface, while the first
context's original confidence remains indistinguishable from `(-7,-2)`.
Separate initializer and evaluator processes use isolated Python mode; the
initializer accepts the synthetic raw pair on stdin. Their exact commands,
outputs and the source hash are in `results/compact_results.json`.

[EXECUTED horizon falsifier] Honest H8 initialization distinguishes those two
original states after seven positive observations in context zero and inference,
with outputs zero and one. Editing the old H4 resident's counter from four to
eight produces output one for the `-8` case, where the original process would
output zero. The discarded confidence cannot be restored by changing a counter.
The larger program can run a guessed representative further; that is not a
functionality-preserving extension of this resident.

[EXECUTED] Replay with:

```sh
python3 -B research/learn_infer_only/experiments/private_construction/practical_bounded/compact.py audit > research/learn_infer_only/experiments/private_construction/practical_bounded/compact.stdout.txt
```

[DERIVED scope] This sharpens the earlier table result: generic expansion is
exponential, but a particular behavioral quotient can admit a compact public
normal form. Both realize the same narrow complete-fork ideal. Neither hides
useful state differences from every possible future command indefinitely, and
neither supplies fresh private ingress or a decrypt-and-release mechanism.

[REPORTED] No searches, downloads or additional dependencies in this variant.
