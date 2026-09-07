# What supplies AJ's compact Turing-machine encoding?

[SOURCE result] AJ2015/173 §1, printed p4, explicitly attributes all three
cited time-independent TM randomized-encoding constructions to iO. Its §8
Theorem9 is a positive **conditional** construction from compact TMRE and
semi-compact FE. It is not, by that substitution alone, an independent
construction of compact TMRE from LWE.

[DERIVED result] There is a concrete way to complete the cited KLW Boolean
machine-hiding interface into a whole-output compact IND encoding: obfuscate
one short generator indexed by output bit, and expand its encodings during
decoding. Section4 states that conditional construction and its loss. It uses
ordinary circuit iO in addition to compact machine hiding; KLW itself uses
ordinary iO inside its accumulators, iterators and signatures. This does not
instantiate those premises from the frozen logarithmic-input X contract.

[OPEN result] BGL's logarithmic-input generator is a distinct, potentially
weaker premise. It still retains space dependence, and the frozen X resource
contract permits polynomial dependence on `2^h=T`. Neither fact can be erased
when claiming AJ's encoder has work polynomial only in `log T`. This is an
identified parameter obligation, not an impossibility result or a refutation
of the source theorems.

## 1. The requested interface and the three source meanings of succinct

[SOURCE, AJ2015/173 §8.1 pp44–45] For a machine A, input x and binary time bound
T, AJ requires

```
Encode(kappa,A,x,T): time poly(kappa,|A|,|x|,log T)
Decode(encoding): time poly(kappa,|A|,|x|,t_actual)
```

The complete encoding length is bounded by Encode's bit work, hence does not
have a separate linear output-length or space-bound argument. Decoding may
write the whole output and perform the long computation. Its IND game compares
equal-width inputs to the same machine, with identical output and **identical
actual runtime**, not merely the same upper bound. A clocked interpreter is
needed when reducing variable-runtime programs to that game. The printed
success-probability inequality omits the `1/2` baseline; the intended ordinary
IND interpretation is explicit here, as in the independent depth review.

[SOURCE] The cited records are [BGL2015/356](https://eprint.iacr.org/2015/356),
[CHJV2014/769](https://eprint.iacr.org/2014/769), and
[KLW2014/925](https://eprint.iacr.org/2014/925). The latter two identifiers are
also in 2016/006's bibliography. All PDFs were read from the local mirror;
`access.json` records exact hashes/extraction commands. This is a focused
audit of these cited records, not a corpus-wide claim about current TMRE.

| Source interface | Encoding dependence | Decoding / security | Starting assumptions |
| --- | --- | --- | --- |
| BGL Thm5 basic TM garbling | polynomial in space S and output length L, polylog T | roughly T·poly(S), static simulation with explicit metadata | circuit iO, OWF |
| BGL §5.1 output-independent corollary | still polynomial in S; no linear L term | IND; whole output can be expanded later | iO-based succinct obfuscation; restricted-index cases need a quantitative substitution |
| CHJV §6.4 Algorithms18–19 | explicitly initializes all S cells | iterative RAM evaluation; one-time simulation | circuit iO, injective OWF as stated in its introduction, and its ACE/PRF/ORAM components |
| KLW §7 McHE | poly(kappa,description,input,log T), no S argument | one-bit machine hiding, equal actual time and tape schedule | ordinary iO, PKE, puncturable PRF, enforcing accumulator/iterator, splittable signatures |
| Section4's completed indexed encoding | poly(kappa,description,input,log T,log L) | L compact-McHE expansions; whole-output IND | compact McHE plus ordinary circuit iO and puncturable PRF |

## 2. BGL and CHJV: exactly what is compressed

[SOURCE, BGL §§2.2–2.3 pp13–18] Definitions1–3 distinguish garbling from
input encoding and distinguish space-dependent from optimal efficiency.
The joint garbling/input representation has a simulator receiving output,
actual runtime, input length, description size and the declared `(n,L,S,T)`.
Security is static against nonuniform classical distinguishers. Correctness
is negligible-error for each polynomial-time family. Their term
"sub-exponentially indistinguishable" bounds the gap against PPT adversaries;
the source explicitly distinguishes this from hardness against subexponential
time. These quantifiers cannot supply our uniform quantum-advice envelopes
without an additional argument.

[SOURCE, BGL §3.2 pp25–28] The encoder chooses PRF seeds and obfuscates

```
P(t): generate the PRF-coordinated garbling of transition block t.
```

It also encodes the initial configuration. Decode evaluates P at successive
timesteps, evaluates each emitted garbled block, and passes its garbled
configuration to the next. Thus neither the whole transition circuit chain
nor its T-step execution is produced by the encoder. However, one block
processes an S-bit configuration, and its garbling/generator has
`poly(kappa,|A|,S)` size. The decoder's work remains proportional to the number
of simulated steps, with polynomial space overhead. The source's transition
hybrids hardwire one current configuration at a time, which is exactly why S
remains in the encoding bound.

[SOURCE, BGL §3.2 pp29–33] Adjacent hybrids puncture PRF points, hardwire
their values, replace them by uniform coins, switch a real garbled block to
a simulated one, then reverse. There are T transition hybrids. Correctness
also transfers from true garbling coins to PRF-generated coins using an
efficient failure test; it is not upgraded here to perfect correctness.

[SOURCE, BGL §1 p8 and §5.1 pp38–41] The basic generator's input is only
`h=ceil(log T)` bits. For bounded polynomial time the source notes a sufficient
NC1/logarithmic-input iO assumption with suitable puncturable PRFs. The
output-independent IND corollary instead considers a bit-indexed version of
the computation and constructs succinct iO, then encodes a fixed computation
by obfuscating a no-input machine. The index contributes `log L` input bits;
the associated input-enumeration loss is polynomial in L. The broad
all-input succinct-iO theorem uses subexponential assumptions. Its no-input
encoding specialization does not automatically require that broad theorem's
full exponential-input loss. Neither statement removes the S dependence.

[SOURCE, BGL §2.2 p15] The source separates IND from output-only simulation:
an output-independent simulator could compress a long pseudorandom string
given only that string, contradicting the usual incompressibility argument.
Therefore AJ's IND-only output compression must not be silently promoted to
an output-only simulator for arbitrary L-bit strings. The new construction
below claims IND only.

[SOURCE, CHJV §6.4 pp36–38] Algorithm18 first pads the input to S words,
initializes ORAM/freshness data, obfuscates the composed transition machine,
then encapsulates every initial memory word. This literal loop has S
iterations even if the source program is short. Algorithm19 performs the
reads/writes and transition calls during evaluation. Theorem6 proves one-time
simulation via execution hybrids; §6.6 Theorem7's resulting obfuscated size is
`S·poly(kappa,n)+poly(|A|,kappa,n)`. CHJV's faster evaluator does not erase
the encoder's S term.

[DERIVED, AJ substitution] AJ's printed EncFunc first decodes the whole tuple
of L public keys, then encrypts under them (§8.2 Figure9 p46). That literal
materialized tuple has at least L bits of storage. Even if SetupFunc can be
implemented as a streaming loop, inserting BGL/CHJV's space-dependent encoder
around the printed EncFunc does not prove an L-independent bound. A redesign
using indexed/random-access decoding may be possible; it needs its own joint
security and space analysis. No lower bound against all such redesigns follows.

## 3. KLW: a compact step mechanism with stronger iO dependencies

[SOURCE, KLW §7 pp35–41] Definition7.1 compares equally sized machines
M0,M1 on the same input x, producing the same **bit** after the same t*<T
steps. Remark7.1 additionally fixes the tape-movement function; oblivious
simulation supplies a common schedule with polylogarithmic overhead.
Encoding work is `poly(kappa,|M|,|x|,log T)`, decoding work is polynomial in
t*. The theorem is a classical IND statement; the input is public in this
machine-hiding game. Section7.3 sketches additional IND-CPA hybrids to hide
the input and obtain randomized encoding.

[SOURCE, KLW §7.1 pp36–37] Mc.enc initializes an accumulator/iterator and
encrypts only the supplied input symbols. Its obfuscated transition program
checks a read proof, last-write time and signature, derives timestep-specific
encryption keys from a puncturable PRF, decrypts the current symbol/state,
executes a transition, and encrypts/authenticates the result. The external
decoder grows the sparse store and drives the transition circuit. The real
encoding need not allocate the entire maximum tape. Section7.2 and AppendixB
move a selected enforcement point through the execution and erase later
logic/symbols using iO, PRF and PKE hybrids.

[SOURCE, exact assumption sites] Theorem7.1 assumes IND-CPA PKE, iO,
puncturable PRF and the listed iterator/accumulator/signature games. Those
tools are constructed earlier, not assumed to be ordinary collision-resistant
hashing. Section4.1 pp13–15 makes accumulator parameters `PP=iO(H)` where
`H(h1,h2,index)` encrypts zero under PRF-derived coins. Its inputs contain
**two ciphertext-width strings** plus an index. Section5.1 p21 creates
signature verification keys by obfuscating code on `(m,sigma1,sigma2)`, with
two kappa-bit signature components. Its proof also requires an **injective**
PRG; generic PRG security alone does not imply injectivity. The abstract names
iO, OWF and injective PRG; here the explicit PKE/perfect-correctness and
component-game premises are retained rather than collapsed without auditing
their reductions and rates.

[SOURCE / boundary] These interfaces have polynomial-length inputs, not only
logarithmic-length timestep indices. Replacing every iO call by the frozen X
contract is not a valid substitution. Full ordinary circuit iO already implies
the functionality the xiO bootstrap is trying to derive; assuming it here
would make this route an iO-dependent conditional construction rather than an
independent foundation for that bootstrap.

[OPEN source normalization] The printed Mc.dec syntax lists M,x,T, while the
actual decoder is described as operating on enc. The emitted tuple omits
items used by that decoder: its initial encrypted state is present in the
decoder's parse, and public accumulator parameters are required for
Prep-Read/Prep-Write. A self-contained package must specify those items.
Their initialization is explicit in the source algorithm, but this note does
not claim byte-level correctness or a full repaired KLW reduction. The next
lemma requires a compact McHE interface with the complete public decoding
context included in its game. Source correctness for an explicit bound is
also distinct from the intro's asymptotic `T=2^kappa` timeout convention.

## 4. A precise conditional whole-output completion

[HYPOTHESIS `H`] A compact Boolean machine-hiding encoding with the KLW
efficiency bounds, a self-contained deterministic decoder (public metadata
allowed), and a **one-quantum-advice** IND envelope eps_H. It handles every
fixed conforming machine pair on the same public input, independently of
fresh encoding coins. Its uniform fresh correctness error is delta_H.
Ordinary circuit obfuscation `O` has time/size polynomial in security and
circuit description, QA gap eps_O, and fresh all-input correctness error
delta_O. A selectively puncturable PRF has QA gap eps_P and exact off-point
agreement. The output length of that PRF covers the H encoder's random tape.
These are explicit premises; this note has not lifted every KLW component
reduction into H's QA game. Length-prefix and pad H's classical encoding to
one public bound E for the admitted machine/input widths; this remains compact
and Decode removes that padding.

[DERIVED compiler] Fix public padded description/input widths, output width
L>=1 and a strict time bound. Construct B[A,x](i): simulate A(x) on a clocked
oblivious interpreter, then return output bit i; return a fixed bit for an
out-of-range index. Pad to a common actual runtime t_B<T_B for every i and
every admitted A,x, and a common tape schedule. Both t_B and T_B are polynomial
in the original declared time/work bounds. B's description is polynomial in
`|A|+|x|+log T+log L`. Equal whole outputs give conforming B machines at every
index. Input x is hidden in the machine description, so this use of H does
not separately assume KLW's sketched input-hiding extension.

```
Encode(A,x,T,L):
  sample puncturable PRF seed K
  define C[B,K](i):
    if i >= L: return the fixed E-bit zero string
    else: return padded H.Enc(B, i, T_B; P_K(i))
  return (O(C[B,K]), public clock/width metadata)

Decode(code,metadata):
  for i = 0,...,L-1:
    e_i = code(i)
    y_i = H.Dec(e_i, public index/clock metadata)
  return y_0...y_(L-1)
```

[DERIVED efficiency] The classical circuit C executes **the encoder**, not
B's long computation. Unrolling H.Enc at its fixed public clock gives a
circuit of size `poly(kappa,|A|,|x|,log T,log L)`; O's polynomial-description
efficiency preserves that bound. Each e_i is also compact. The whole output
is expanded only in Decode, whose work is at most
`L·poly(kappa,|A|,|x|,T_B,log L)` and whose output has L bits. For ordinary
machines writing their output, L is bounded by their declared time; this is
still polynomial in the original time bound. It is not necessarily near-linear
decoding and can recompute A(x) L times. No application key/master secret is
issued by this wrapper; its PRF seed is embedded in obfuscated code.

[DERIVED one-copy privacy] Let H_j's generator use B1 below j and B0 at/above
j. For each j<L: (1) replace its full PRF seed at j by a punctured key and a
hardwired e_j generated with the true point value; the generator is exactly
equivalent, so pay eps_O; (2) replace that value by a uniform tape, paying
eps_P; (3) switch the one H encoding of B0 to B1, paying eps_H; (4) restore
PRF coins, paying eps_P; (5) unpuncture into H_(j+1), paying eps_O. Circuits
are padded to cover one hardwired compact e_j. They have only polynomial
description overhead. Thus in acceptance-probability-gap convention,

```
eps_TMRE <= L * (2 eps_O + 2 eps_P + eps_H).
```

Each reduction creates a classical public generator using its one classical
challenge and then invokes the final distinguisher once with its one advice
state. No advice is copied or rewound. Selecting/fixing a classical index is
the usual hybrid argument with charged nonuniform description; envelopes
must be uniform over those fixed instances and all admitted residual advice.
The explicit out-of-range branch makes H_L exactly the second real generator,
including when L is not a power of two; merely giving B a fixed out-of-range
bit would not make its machine-hiding encodings identical outside the hybrid.
This proves the wrapper conditional on H/O/P, not quantum security of the
source H implementation from a classical theorem.

[DERIVED fresh correctness] Condition on O's all-input correctness event.
For each i, an efficient classical test compares H.Dec(H.Enc(B,i;r)) with
the known B(i), using at most polynomial T_B work. Its PRF-to-uniform gap is
bounded by eps_P,corr at those actual resources. A union bound gives

```
delta_TMRE <= delta_O + L * (delta_H + eps_P,corr).
```

This bound does not require the L real encoding tapes to be independent;
they are PRF-correlated. Uniform per-instance error and the marginal hybrids
suffice. No stretched-exponential rate is inferred from the source's bare
negligibility statements.

## 5. Dependency verdict for the current bootstrap

[DERIVED] The following are three different conclusions.

1. **Available conditional construction:** compact H plus ordinary circuit
   O/P supplies whole-output compact IND TMRE as above. KLW is a concrete
   source for the classical compact-H architecture under its stronger iO
   suite. This is useful positive evidence; it is not a plaintext toy.
2. **No independent LWE instantiation from this substitution:** inserting
   ordinary full circuit iO into KLW/TMRE and then using AJ to derive compact
   FE and iO assumes the desired iO object upstream. No source theorem fails;
   the dependency graph simply does not establish an iO-free base.
3. **Restricted-X case remains a separate obligation:** BGL's h=log T
   generator lies in a logarithmic-input class, but frozen X permits
   `Time_X=poly(kappa,|C|,2^h)` and size
   `2^(h(1-alpha))*poly(kappa,|C|)`. At h=log T those retain T dependence.
   An upper bound allowing T work cannot prove poly(log T) work. Even a
   stronger time-compact logarithmic-input obfuscator leaves BGL's S term
   and AJ's materialized key tuple to resolve.

[OPEN] A successful B/P/G/X-only replacement would need a matching compact
encoding-time guarantee, control of space/output dependence throughout the
actual AJ loops, complete public decoding context, and quantified QA security
and correctness rates at the time/description/advice bounds used later.
The full reviewed bootstrap's public-environment improvement does not by
itself supply these missing primitive guarantees.

## 6. Evidence, validation and resume point

[EXECUTED] `python3 compact_tmre/validate.py` (from this directory's parent;
equivalently use the repository-relative path) checks the frozen input/source
hashes, extraction records, focused source anchors and the symbolic wrapper
ledger in `wrapper_ledger.json`. It does not execute encryption, obfuscation,
an attack, or protected-output tests. Actual stdout is in `validation.json`.

[SOURCE access] Two new primary metadata web queries, zero Scry/Kagi queries,
three local PDF extractions, zero PDF downloads. Extracted whole-paper text
and Python caches are ignored by owned rules. All earlier author/review
artifacts remain unchanged. `inputs.json`, `source_spans.json`, and
`artifact_hashes.json` retain provenance.

[OPEN resume] Audit an independent concrete QA compact-H instantiation only
if stronger iO premises are acceptable, or investigate a separately bounded
streaming/random-access AJ redesign under a genuinely time-compact index
obfuscator. The direct vector-GKP audit is owned by the PQ lane and remains
independent of this report.
