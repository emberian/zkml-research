# Independent review: compact TMRE dependencies and indexed completion

[DERIVED review verdict; 2026-09-08] **Qualified acceptance.** The source
dependency audit and the indexed whole-output construction's conditional
privacy/correctness bounds are supported. Its compact encoder and decoder
polynomial in the declared clock are supported. The wrapper does **not yet
prove AJ's full actual-runtime decoder interface for arbitrary loose time
bounds**. Acceptance is therefore for fixed-clock computations (or the
explicit weaker declared-bound decoder contract), not an unqualified
instantiation of AJ §8.1. This qualification does not change the stronger-iO
dependency conclusion or refute any source theorem.

[EXECUTED frozen subject] `COMPACT_TMRE.md` SHA256
`af5e6acb0feb544b739c08838dcc8c88dff63244d33c16e18792d992e662a445`.
All 12 author-directory files other than Python cache files, including the
ignored source extracts, were unchanged by the review; before/after hashes
are in `results.json`. The author validator writes its own ledgers, so it
was inspected but not replayed in place. Independent controls are in this
directory. Shared ledgers, companion trees and commits were not changed.

## 1. The material qualification: actual runtime versus declared clock

[SOURCE: exact efficiency definition] AJ 2015/173 §8.1 printed/PDF p45
requires Encode time polynomial in `(kappa,|A|,|x|,log T)` and Decode time
polynomial in `(kappa,|A|,|x|,t)`, where t is the actual running time of A(x).
The equal-input-length IND game additionally requires equal output and equal
actual running time. The displayed guessing inequality omits its one-half
baseline; the note correctly does not interpret that literal typo as a
security definition. I checked the full page visually as well as in text.

[SOURCE: matching H contract] KLW 2014/925 §7 printed p36/PDF p37 likewise
requires Mc.dec polynomial in actual `t*`. Definition 7.1 and Remark 7.1
require equal outputs, equal actual halt times, equal machine-description
widths and matching tape schedules for the compared machines. This was
also visually checked.

[SOURCE: reviewed author's construction] The frozen note §4 pads
`B[A,x](i)` to a common runtime for every admitted A,x and index i, with
`t_B,T_B` polynomial in the original declared time/work bounds. Its displayed
decoder bound is `L*poly(kappa,|A|,|x|,T_B,log L)`. It does not derive a
bound in the original actual t.

[DERIVED finding] A compiler that executes an explicitly declared common
clock may erase the original early termination. An input computation that
halts in two steps can still be passed a much larger legal T. Padding its
compiled machine to T steps gives t_B=T, despite original t=2. The H
efficiency premise permits decoding work proportional to t_B; it does not
give a bound independent of that padding. Thus substituting this premise
into the wrapper proves polynomial-in-declared-T decoding, not
polynomial-in-original-t decoding. Formally, an allowed upper bound involving
an independently unbounded parameter T does not imply a universal bound
that omits T. No runtime lower bound for all H constructions is asserted.

[DERIVED sufficient restriction] The existing proof is sufficient if the
encoded *functionality itself* is the padded fixed-clock machine, and its
actual runtime includes that clock. More generally, a declared-time bound
polynomially controlled by original t, input/description lengths and kappa
also suffices. These restrictions must be stated at the consumer. They
cannot be obtained from an arbitrary caller-supplied loose upper bound alone.

[OPEN repair target] To claim AJ's general interface, derive an interpreter
and bit-selection compiler that preserves instance runtime up to a uniform
polynomial while preserving the paired halt-time/tape-schedule restrictions;
price evaluation of the compact generator and reading its clock metadata too.
Alternatively restrict the claimed output theorem to explicitly clocked
families and verify that the actual AJ consumer satisfies that restriction.
This review does not silently revise the frozen construction.

## 2. Source dependency checks that passed

[SOURCE: AJ introduction and construction] AJ 2015/173 printed p4 names
the three cited time-independent TMRE works and says all use iO. Section 8
Figure 9 printed p46 makes EncFunc first decode the entire public-key tuple,
then encrypt and output all per-component ciphertexts. Theorem 9 printed
p47 is conditional on a secure RE-for-TMs interface and semi-compact FE.
This is a positive conditional theorem, not an independent construction of
that RE premise from LWE.

[SOURCE: BGL construction/game] BGL 2015/356 Definition 1-3 printed pp13-15
and Theorem 5 printed p19 distinguish the space-dependent garbling interface
from its stronger efficiency notions. Section 3.2's succinct generator
produces transition-block garblings at an index; the blocks process the
space-bounded configuration. The construction therefore retains the S
parameter. Its simulation receives runtime, output and public parameter
metadata; the source's subexponential indistinguishability statement bounds
the gap for PPT distinguishers and explicitly distinguishes it from hardness
against subexponential-time distinguishers.

[SOURCE: BGL output compression] Section 5.1 printed pp38-41 develops
probabilistic/succinct iO and a whole-output IND corollary through a bit-indexed
machine. Its index-enumeration loss grows with the index domain, hence
polynomially with the output width when that domain is logarithmically
described. The no-input specialization avoids the full exponential-original-
input loss. Space dependence remains. Definition 3's output-dependence
discussion on printed p15 distinguishes the IND alternative from the
output-only simulation notion. The note preserves this distinction.

[SOURCE: CHJV algorithms] CHJV 2014/769 §6.4.2 Algorithm 18 printed p37
first pads the input to the declared space bound, initializes ORAM/freshness
state and encapsulates the initial memory word by word. Algorithm 19 grows
the computation during Eval. Section 6.6 Theorem 7 printed pp44-45 still
has size `S*poly(kappa,n)+poly(|A|,kappa,n)`. Its evaluator improvement does
not remove that explicit encoder-space term.

[SOURCE: KLW algorithms/premises] KLW 2014/925 §7.1 printed pp36-37
encodes the supplied input, initializes a sparse accumulator/iterator and
obfuscates a transition checker. Theorem 7.1 printed p38 lists its PKE, iO,
PRF, iterator, accumulator and signature games. Section 4.1/Figure 3 printed
pp13-14 sets the accumulator parameters to `iO(H)` for a circuit taking two
ciphertext-width strings and an index. Section 5.1/Figures 9-13 printed
pp21-22 obfuscates signature circuits with two kappa-bit signature components;
its proof uses injective PRG. These are not merely log-index inputs covered
by the frozen X contract. No component security reduction was promoted from
classical to quantum-advice security by this review.

[SOURCE / DERIVED syntax qualification] KLW's explicit output tuple in §7.1
omits initialized encrypted state that its decoder subsequently parses, and
the decoder also needs public accumulator parameters. The author's
self-contained-public-context hypothesis correctly exposes this issue;
the new wrapper is not a claim that those printed tuples are a byte-complete
implementation. A full repaired KLW construction/reduction is outside this
bounded review.

[SOURCE / DERIVED X mismatch] The frozen bootstrap X premise has time
`poly(kappa,|C|,2^h)` and size `2^(h*(1-alpha))*poly(kappa,|C|)`.
2016/006 Definition 8 printed pp7-8 expressly permits this time dependence.
At a step index `h=ceil(log T)`, `2^h` is between T and 2T (up to the singleton
domain convention). That upper bound does not establish poly(log T)
encoding. Its restricted `h=O(log kappa)` input class must also remain
respected. KLW's ordinary iO calls do not become valid X calls by naming
their timestamp component.

## 3. Indexed whole-output proof accepted under its explicit premises

[HYPOTHESIS scope retained] H is a self-contained compact Boolean
machine-hiding encoder with the stated one-quantum-advice IND and uniform
fresh correctness envelopes. O is ordinary circuit iO with the stated QA
gap and fresh all-input correctness error. P is a selectively puncturable
PRF covering H's random tape, with exact off-point agreement. Circuit
descriptions, H encodings and tape/clock bounds are padded uniformly.
These are independent assumptions; the cited classical KLW theorem does
not by itself instantiate their QA rates.

[DERIVED algorithm acceptance] The short generator evaluates H.Enc on
the bit-selector machine and public index; it does not execute the long
selector computation itself. If H's encoder clock is compact, unrolling it
and applying polynomial-description O preserves compact encoding work
`poly(kappa,|A|,|x|,log T,log L)`. The L selected H encodings are materialized
only during Decode. Fixed public output width L and the common runtime/tape
schedule make each compared machine pair conforming. Hardwiring x in B
uses machine hiding rather than an unstated input-hiding extension.

[DERIVED privacy acceptance] For each real index j, puncture the PRF at j
and hardwire that single H encoding. This changes only the representation
of an exactly equivalent generator, so costs eps_O. Replace its tape by
uniform (eps_P), switch the uniform-randomness H encoding between the two
conforming machines (eps_H), restore the PRF tape (eps_P), and unpuncture
back to the next generator (eps_O). Pad both sides of each iO comparison.
All other real indices keep their exact encodings. The fixed-zero generator
branch for `i>=L` is necessary to identify the last hybrid with the entire
second real generator; equal decoded out-of-range bits alone do not do so.

```
[DERIVED] eps_TMRE <= L*(2*eps_O + 2*eps_P + eps_H).
```

[DERIVED] This is a single H challenge and a single invocation of the final
quantum distinguisher per reduction. The fixed classical hybrid index and
ordinary independently sampled side records do not require copying or
rewinding advice. Every envelope must cover the actual padded generator,
obfuscation work, description length, residual advice and reduction resources.

[DERIVED correctness acceptance] On O's all-input correctness event, the
generator returns its exact PRF-randomized H encodings at all indices.
For each index, the note's failure test computes B(i) and evaluates H at
the declared work bound. A PRF marginal hybrid compares its failure
probability with fresh uniform H coins. Union bounding gives

```
[DERIVED] delta_TMRE <= delta_O + L*(delta_H + eps_P,corr).
```

[DERIVED] The L PRF tapes need not be independent. The failure-test envelope
must include B's computation and H.Decode's work, which may be polynomial
in the declared T_B. A primitive PPT theorem with bare negligible error
does not automatically furnish a stronger uniform quantitative rate.

## 4. Evidence, integration boundary and resume point

[EXECUTED] From repository root:

```
python3 research/learn_infer_only/experiments/adversarial_review/compact_tmre/review.py > research/learn_infer_only/experiments/adversarial_review/compact_tmre/stdout.txt 2> research/learn_infer_only/experiments/adversarial_review/compact_tmre/stderr.txt
```

[EXECUTED] Exit 0; stderr empty. `results.json` records all frozen-input
hashes, fresh extraction commands and before/after author-file hashes.
For output widths 1 through 64, finite controls check 2,080 adjacent-index
hybrids, 111,634 off-point equalities, the five-step loss coefficients, and
58 out-of-range negative controls. Four exact clock-arithmetic examples hold
original t=2 fixed while increasing declared T. These controls exercise the
proof bookkeeping and illustrate the runtime distinction; they are not
cryptographic runs or substitutes for the general reasoning above.

[EXECUTED source access] Five local PDF extractions (AJ 2015/173,
2016/006, BGL 2015/356, CHJV 2014/769 and KLW 2014/925); zero web, Scry SQL,
Scry schema, Kagi queries or PDF downloads. Local PDF SHA256 values and
matching independently extracted text hashes are in `results.json`.
`visual_access.json` records the exact rendered definition pages. No crypto,
model, protected-output or adversary runtime was executed.

[DERIVED integration recommendation] Retain the source dependency finding
and the conditional fixed-clock indexed construction. Qualify any summary
calling the wrapper a complete AJ §8.1 instantiation until §1's runtime
obligation is discharged. The ordinary-iO dependency remains a separate
reason that this is not a B/P/G/X-only or LWE-only foundation for the current
bootstrap. The source's positive Boolean compactness theorem is preserved;
no change to `docs/VERDICTS.md` and no field-wide absence/refutation are
proposed.

[OPEN resume] An owner may either state the fixed-clock restriction at the
actual AJ consumer or prove a runtime-preserving selector/interpreter
normalization. A subsequently changed construction needs review at its new
hash. An independently instantiated QA compact-H premise remains a separate
construction task, with public decoding context and full resource/error
rates explicit.
