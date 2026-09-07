# Actual bounded quotient deployment

[DERIVED follow-on] `COMPACT.md` and `compact.py` give a verified compact public
normal form for this same learner, without the catalog. The table below remains
a measured generic representation; exponential expansion is not intrinsic to
this particular finite quotient. Its frozen table code and exports are unchanged.

[EXECUTED / DERIVED] This is an actual end-to-end software implementation of a
finite forkable learning interface. It uses no encryption and has no master key.
Its resident is a **behavioral class**, not an opaque original model state.
The complete allowed fork table is already sufficient to determine that class.
Thus this is a deliberately extensional bounded positive, not a practical
implementation of general FE/iO or an indefinitely private learner.

[EXECUTED] Run the saved synthetic deployment from the repository root:

```sh
python3 -I -B research/learn_infer_only/experiments/private_construction/practical_bounded/results/synthetic_deployment/runtime.py --package research/learn_infer_only/experiments/private_construction/practical_bounded/results/synthetic_deployment --commands infer_0,learn_0_positive,infer_0
```

[EXECUTED] Output: `{"node": 197, "outputs": [0, "ack", 1]}`. A public positive
example changes the model's subsequent classification for context zero.
The synthetic initial pair `(-1,2)` is intentionally public in the audit; no
user's private data was used.

## Functionality and exact privacy statement

[DERIVED definition] There are two contexts and scores `(w0,w1)` in
`{-8,...,8}²`. Prediction for context `i` is `1[w_i >= 0]`. A labeled
observation `(i,y)`, for `y in {-1,+1}`, changes `w_i` to `w_i+y` exactly when
the current prediction disagrees with `y`; otherwise it leaves it unchanged.
This mistake-driven update preserves the finite score domain. The six public
commands are four labeled observations and two context inferences. Learning
returns a fixed acknowledgment. Every command consumes one of four steps.

[DERIVED] Let `T_H(s)` list every edge's released value, in fixed breadth-first
order, over the complete six-ary command tree of depth H. Define
`s ~_H t` iff `T_H(s)=T_H(t)`. The ideal interface permits arbitrary restore and
fork from every reached history, with **no total query quota**. It therefore
permits obtaining all `6(6^H-1)/5` edge values. Equivalently, the ideal may release
the entire table at initialization. This equivalence is about allowed
information, not identical time-to-answer or a limited query budget.

[DERIVED exact simulation] The public catalog consists of all distinct tables,
lexicographically sorted. The deployed resident is the index of its table.
Given the complete ideal interface, a simulator reads all edges and finds that
index; all three deployed files then follow deterministically. Conversely,
reading the resident and catalog reconstructs the complete interface. Hence
for every valid pair `s ~_H t`, the entire deployed package is **byte-identical**,
and any adversary observing that package and the evaluator's future execution
has zero extra distinguishing advantage under the same execution environment.
There is no computational assumption in this argument. Evaluator timing and
memory cannot depend on a further secret input because none is supplied.

[DERIVED setup boundary] The initializer is private and honest, with its raw
input, working memory, stdin transport, logs, backups, swap, crash images and
any other copies erased or inaccessible after handoff. This is an assumption.
The code neither proves erasure nor protects an initializer observed by a
malicious host. In particular, measured setup time/RSS is **not** a constant-time
or side-channel argument. Only the fixed public dimensions, final artifact
contents and sizes, and post-handoff runtime are covered by the statement.

[DERIVED nonvacuity and its limit] The model learns and the initial private
class affects future answers. For example `(-1,0)` and `(-2,0)` initially make
the same prediction, but a positive observation followed by inference separates
them; those are not an admissible privacy pair at H=4. In contrast `(-8,-8)`
and `(-7,-8)` have identical H=4 tables and exact identical packages. Seven
positive observations in context zero followed by inference separate them at
H=8, which is outside this deployment. The hidden difference is a possible
lifetime distinction that the finite compiler deliberately discards.
No two members of one class can affect any permitted future answer differently
within the stated horizon; claiming otherwise would contradict the definition.

## What actually crosses the initialization boundary

[EXECUTED] `compiler.py catalog` performs public preprocessing over all 289
possible initial pairs. `compiler.py initialize` receives the initial pair on
stdin, computes its table and class, and exports exactly:

| Deployed file | Bytes | Meaning |
|---|---:|---|
| `program.json` | 133,001 | Public common catalog and command/horizon metadata |
| `resident.bin` | 1 | Initial behavioral class index |
| `runtime.py` | 2,671 | Standalone evaluator; imports no compiler or state machine |
| Total | 135,673 | Complete three-file synthetic package |

[EXECUTED] The initializer subprocess exits before the external evaluator
starts. The evaluator uses isolated Python mode, a restricted environment and
only the exported files. The audit records exact commands, outputs, file sizes
and SHA256 hashes in `results/results.json`. It also launches two independent
initializers for the admissible pair and compares all exported bytes.
These process and inventory checks establish the explicit software boundary,
not forensic secure deletion of all machine state.

[DERIVED] Sixty-four distinct classes require at least six bits in a fixed-length
injective class code; this format uses one byte. The public catalog cost is
real and is not included in that one-byte number. A simpler standalone
representation is the 1,554-byte raw table plus public topology/evaluator code.
The class label is minimal in information, not necessarily the smallest total
package. Catalog preprocessing enumerates all initial states as well as all
command histories. A variable-depth future is not supported.

[EXECUTED] The horizon is enforced by the honest evaluator, which refuses a
fifth command. A hostile reader can inspect the entire table immediately,
copy snapshots and compute any consequence of the table. This is permitted by
the stated ideal. A snapshot node alone reveals the selected public command
history. There is no private future observation channel.

[EXECUTED integrity negative] Replacing the public resident class byte changes
inference from zero to one and is accepted. The package makes no authentication,
genesis binding, finality, single-history, quota, anti-rollback or integrity
claim. A content hash records what was tested; it does not authenticate an
origin to an attacker who controls both artifact and hash.

## Exhaustive checks and measured cost

[EXECUTED] Replay:

```sh
python3 -B research/learn_infer_only/experiments/private_construction/practical_bounded/audit.py audit > research/learn_infer_only/experiments/private_construction/practical_bounded/stdout.txt
```

[EXECUTED] Saved result is PASS: 289 initial states; 64 classes; 1,554 edges per
state; 449,106 comparisons against a separately written direct oracle;
99,456 calls to the deployed runtime covering every edge of every class;
225 additional states share their representative's exact deployed label.
The audit checks learning-dependent separation, noncommuting observation order,
full-fork class reconstruction, horizon refusal, metadata ingress disclosure,
package equality for an admissible pair and the explicit integrity negative.
From `(0,0)`, negative-then-positive observations predict one; reversing their
order predicts zero. These witnesses use three commands, within H=4.

[EXECUTED measurement] Python 3.14.7, macOS 26.6.1 arm64, cryptography 50.0.1.
Each table row below is one fresh measurement subprocess; setup is the median
of five calls including serialization but excluding interpreter startup.
A separate sixth call records peak Python allocation with `tracemalloc`;
process RSS includes imports, all runs, allocator retention and native memory.
The full raw samples and before/after RSS appear in `results/results.json`.
These are local measurements, not latency guarantees or security parameters.

| Construction | H | Branches | Serialized bytes | Median setup ms | Python allocation peak bytes | Process peak RSS bytes |
|---|---:|---:|---:|---:|---:|---:|
| One plaintext learner table | 4 | 6 | 1,554 | 0.380 | 69,476 | 29,868,032 |
| One plaintext learner table | 5 | 6 | 9,330 | 2.467 | 386,421 | 30,670,848 |
| One plaintext learner table | 6 | 6 | 55,986 | 14.304 | 2,301,481 | 37,289,984 |
| Public learner catalog | 4 | 6 | 133,001 | 115.626 | 662,003 | 30,932,992 |
| Public learner catalog | 5 | 6 | 1,244,501 | 747.769 | 4,119,983 | 38,436,864 |
| Earlier AES byte tree | 5 | 3 | 25,951 | 1.626 | 97,022 | 34,390,016 |
| Earlier AES byte tree | 8 | 3 | 698,818 | 44.447 | 2,557,733 | 40,435,712 |

[SOURCE instrumentation] Darwin reports `ru_maxrss` in bytes:
`/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/share/man/man2/getrusage.2:94-95`.
The audit pins this installed primary manual's hash and refuses to interpret
RSS this way on another OS. Python-traced memory excludes untracked native
allocations; RSS is an absolute process high-water mark, not an object size.

[EXECUTED] In the already-loaded evaluator, the three-command path averaged
799.379 ns over 10,000 repetitions on this run. This excludes process startup,
file loading, the one-time catalog decode and public preprocessing. It is a
small dictionary/indexing benchmark, not encrypted-learning throughput.

## What this adds to the earlier AES tree

[EXECUTED prior artifact] `../bounded_tree.py` already uses real AES-GCM for a
byte's plus-one/double/infer interface. At H=5 it has 363 encrypted edges,
62 classes, a 25,951-byte artifact, and separate initializer/evaluator
subprocesses. All 256 initial states and 92,928 edges were checked previously.
The new measurement script imports that code unchanged; its source hash is
pinned. This is a different three-command functionality from the six-command
learner, so the table is not an equal-work AES-versus-plaintext speed ratio.

[DERIVED] In that older tree, possession of the root key permits traversing
every child and collecting the entire bounded table. Coupling all independent
node keys makes the artifacts for equivalent inputs exactly equal. Encryption
adds no privacy in this **complete forkable interface** game; the plaintext
byte table itself has only 363 response bytes at H=5. Its utility would need a
different exposure or access assumption, which is not claimed here.

[DERIVED conclusion] The new result is an actual runnable finite adaptation
functionality, a fully enumerated observational quotient, explicit artifact
lifecycle, and measured exponential costs. Yes, the plaintext table is the
ideal interface implemented directly. It demonstrates why a narrow bounded
no-master-read statement can be true without encrypting an evolving hidden
state. It does not solve the intended long-lived private resident, and should
not be used to relabel a trusted plaintext reader as masterless.

[OPEN next boundary] Retaining useful private distinctions while accepting
unbounded or fresh private observations requires another primitive/game.
The independent-key FE ladder remains a separate source-conditional route;
this experiment neither implements it nor removes its assumptions.

[REPORTED search accounting] This tranche: zero Scry SQL/schema, web or Kagi
queries. Cumulative lane counts remain Scry SQL 8, schema 1; web 28; Kagi 0.
No new papers or third-party source were fetched. New Python code is original;
the AES baseline uses the existing installed cryptography package unchanged.
