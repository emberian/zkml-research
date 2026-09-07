# The cited succinct-FE base and one quantum advice state

[DERIVED result] The **GKP construction's security reduction does admit a
straight-line, one-quantum-advice conditional lift** for its prescribed circuit
family. The required assumptions are quantum-advice security of classical
leveled FHE, selective single-key ABE, and one-time garbling, with explicit
statistical and correctness errors. The actual ABE source also has a
straight-line reduction to LWE and classical statistical sampling properties.
No advice cloning, rewinding, extraction, or quantum function description is
needed in these inspected reductions.

[OPEN result] This does **not yet instantiate the complete base B** used by the
PQ bootstrap lane: Boolean FE for P/poly, encryption time polynomial in
`kappa,input length,log(max circuit size)`, a public key bounded by one fixed
polynomial in kappa independently of the recursive program/time bounds, and
sufficiently small explicit errors. The unresolved issues arise from concrete
source interfaces and parameters, not from the papers' classical notation.

## 1. Exact sources and target game

[SOURCE] 2016/006, Definition3–5 and Theorems3–4, printed pp5–6, cites
GKP13 and the GHRW/ABSV/AJ depth upgrade. 2015/720, Definitions10–12 and
Theorems6–7, pp10–11, gives the corresponding static Boolean succinct-FE
statement. The base GKP reference is **2012/733**, *Reusable Garbled Circuits
and Succinct Functional Encryption*, March24,2013: Theorem3.1/Corollary3.2,
pp20–22; construction pp23–24; Lemmas3.9–3.11 pp26–29; ABE2 wrapper pp47–49.

[SOURCE] The audited ABE instantiation is **2013/337**, *Attribute-Based
Encryption for Circuits*, May31,2013, Sections3–6 and Lemma6.4. The depth-upgrade
sources inspected are **2014/917**, Section4/Theorem3, pp12–14;
**2014/148**, AppendixD, pp34–39; and **2015/173**, AppendixC, pp56–57.
The standard-model CIJ transformation **2013/364**, Section3.3 pp15–17, and
GVW bounded-key transformation **2012/521**, Sections5.1–5.3 pp16–22, were also
inspected after following AJ's explicit reference chain. The pinned CIJ mirror
version includes later references; the audit concerns these exact pinned bytes,
not a claim about the precise 2013 conference-version wording.
`access.json` pins all nine local mirror PDFs and their extracted text hashes.
PDFs were read only from the local mirror. Four web searches identified reference
numbers; no eprint PDF was opened or downloaded through the network. Scry0,
Kagi0; web searches4. Full extracted texts are locally ignored.

[DERIVED exact target] Fix kappa, a supported **classical nonuniform** Boolean
circuit f, equal-length classical messages m0,m1 with f(m0)=f(m1), and an
arbitrary q-qubit state rho. All are independent of fresh setup/encryption
coins; rho may depend on kappa and the fixed classical tuple. One QPT
distinguisher receives

```text
(pk, sk_f, Enc(pk,m_b)) together with one copy of rho,
where (pk,msk) <- Setup and sk_f <- KeyGen(msk,f).
```

The probability-gap bound must be uniform over these tuples, the permitted
nonuniform circuit descriptions, advice width q, and distinguisher gate/time
budget. No superposition encryption or key-query interface is requested.
Any externally retained reference accessible to the distinguisher belongs in
its advice/workspace accounting. Advice correlated with the actual fresh
secret key is outside this game.

[DERIVED target distinction] The PQ owner's frozen `BOOTSTRAP_LIFT.md` assumes
perfect base correctness as a sufficient contract. Its separately reported
fresh-error supplement can instead propagate a uniform fresh-message error
delta_B. This audit supplies the source-level error ledger, rather than
silently upgrading source correctness to perfection or altering that theorem.

## 2. The actual GKP constructor

[SOURCE, 2012/733 §3.1 pp23–24] Let L be the bit length of an evaluated
single-bit FHE ciphertext. Setup creates L independent two-outcome ABE public
keys. KeyGen(f) issues, in instance i, the token for the classical predicate
`P_i(hpk,psi)=bit_i(Eval(hpk,f,psi))`. Encryption generates fresh FHE keys and
psi=Enc(hpk,m), garbles the fixed decryption circuit with its secret key
hardwired, and encrypts the two garbled input labels in each ABE2 instance under
public attribute X=(hpk,psi). The selected label sequence decodes f(m).

[SOURCE] Each ABE2 instance itself has two independent ordinary ABE setups.
Its tokens are for P and its complement; exactly the chosen branch should
decrypt. The ciphertext has both ordinary ABE ciphertexts. The raw constructor
therefore does not have only one underlying ciphertext or one underlying ABE
key, despite exposing one **FE function key**.

[DERIVED static schedule] In the target game f and m are already fixed. For a
hidden-label reduction, sample the FHE pair, psi and the real garbling before
the chosen ABE challenge setup. These random choices are independent of the
ABE keys in the real constructor, so this reordering preserves the joint
distribution. X and every P_i(X) are then known before ABE setup. This meets
selective-attribute timing and determines which ordinary ABE branch is
unopened. Other ABE instances and their tokens are generated locally.

[SOURCE/DERIVED] The full-security ABE2 reduction in GKP AppendixB guesses the
unknown P(X) and loses a factor two. That guess is unnecessary in this narrower
static schedule because P and X are known before the challenge key. One may
also retain the source's factor-two reduction for a conservative bound. Neither
version rewinds or copies the adversary state.

## 3. Conditional one-advice security lemma

[DERIVED lemma; mathematical proof, not Lean-checked] Assume uniform
probability-gap bounds eps_FHE, eps_GC and eps_ABE2 for the following classical
challenge games against one arbitrary quantum advice state:

- FHE single-bit IND-CPA, at the prescribed level/parameter family;
- one-time garbling input-and-circuit simulation privacy, including arbitrary
  quantum side information retained by the generator/distinguisher;
- single-key selective ABE2 hidden-label security for the evaluated predicates
  and complements, with classical attributes and labels.

Let delta_FHE bound fresh evaluated-FHE correctness error, uniformly over the
fixed supported f,m. Use fixed-length padded ciphertext/key/decryption-circuit
templates so the garbling simulator has the same size parameters at both
endpoints. Then, allowing the reductions' explicit polynomial classical
overhead in their gate/time/workspace budgets,

```text
gap_GKP_static <= 2 * (n*eps_FHE + eps_GC + L*eps_ABE2 + delta_FHE).
```

[DERIVED proof] For each fixed message m, connect the real view to the source
simulator's view in three stages:

1. GKP Lemma3.11 changes the unopened garbled label to the opened label in each
   of L independent ABE2 ciphertexts. Embed one hidden-label challenge at one
   index and generate every other instance with known classical coins.
2. Lemma3.10 changes the real garbled circuit plus its selected input labels
   to a simulated garbling. The real garbling evaluates the actual FHE
   decryption result. That result equals f(m) except with probability
   delta_FHE; account for that error when replacing it by the simulator input
   f(m). The source informally calls the corresponding distributions exact,
   while its component correctness definition permits negligible error.
3. Lemma3.9 changes the FHE encryption of m to zeros after the garbling has
   already been simulated. A single-bit hybrid costs at most n*eps_FHE.
   The duplicated simulated label is independent of the unopened FHE plaintext.

The final simulator depends on the message only through f(m) and its length.
It is common to m0 and m1, giving the outer factor two. Each reduction runs
the final quantum distinguisher once with the original rho. The source's
classical side records can be copied; rho cannot and need not be. A hybrid
index may be sampled or hardwired as a classical nonuniform index. Selecting
an index by the mathematical hybrid argument does not mean repeatedly running
the distinguisher on one physical advice state.

[DERIVED statistical seam] If two classical transcript distributions have
total variation distance eta, tensoring the same independent rho leaves their
trace distance equal to eta, in the convention with the one-half factor.
Explicitly the trace norm of their difference is
`sum_x |p(x)-q(x)| * ||rho||_1 = 2*eta`. Subsequent channels and measurements
cannot increase distinguishability. This justifies lifting the source's
statistical sampling replacements; it does not turn a computationally secure
classical primitive into a quantum-secure one without the stated QA game.

[OPEN component instantiation] GKP treats the garbling scheme abstractly and
cites several possible Yao variants. This audit assumes its **QA simulation
game** explicitly; it has not chosen and re-proved a particular OWF-to-PRG-to-
garbling chain. It likewise leaves the chosen leveled FHE's QA IND-CPA bound
explicit. Thus the lemma is not advertised as a fully instantiated theorem
from the phrase “post-quantum LWE” alone.

## 4. Following the ABE reduction down to LWE

[SOURCE, 2013/337 §6.3, Lemma6.4 pp18–20] Setup* embeds the challenge public
keys at the fixed attribute's wire values and generates opposite-value keys
with known trapdoors. KeyGen* walks the supplied classical circuit in forward
gate order. It simulates the active recoding key and uses a known opposite
trapdoor for the other branches. The proof changes two distributions per gate
using statistical recoding simulation and key indistinguishability, then
switches one correlated TOR encoding to uniform. The final mask is protected
by statistical one-time encryption security.

[DERIVED] Every gate value is classically computable from the known predicate
and fixed attribute. No witness extraction, proof-of-knowledge, adversary
rewinding, or nonuniform quantum function evaluation is involved. For the
single static predicate needed here, the only quantum computation can be the
final distinguisher. The paper's separate branching-program “back-tracking”
discussion is not an adversary rewind in this circuit reduction and is not
needed for the audited GKP instantiation.

[SOURCE, 2013/337 §5 pp12–15] The TOR encoding is `A^T s+e`. Recoding matrices
satisfy an exact linear relation; the simulated target matrix is generated by
multiplying public matrices with sampled short matrices. Correlated
pseudorandomness uses a common LWE secret across the public-matrix blocks.
Its concrete cited family has `q=n_LWE^Theta(d_max)` and a polynomially bounded
error distribution; these are level-dependent parameters, not an arbitrary
fixed-modulus LWE assumption.

[DERIVED conservative QA bound] To compare all-real correlated blocks with
real preceding blocks and a uniform final block, insert the all-uniform
distribution. Two decisional-LWE replacements suffice, with the second
reduction using only the preceding blocks. Account separately for the
statistical difference between trapdoor-generated and uniform public matrices.
Writing eta_pk for an aggregate such term and eta_stat for all gate/mask
statistical replacements gives a conservative schematic bound

```text
eps_ABE <= 2*eps_LWE + 2*eta_pk + eta_stat.
eta_stat includes the sum of recoding/key-indistinguishability errors
over the actual predicate gates, plus the one-time mask error.
```

[DERIVED exact subcase] For the literal §5 mask
`E(psi,m)=psi+ceil(q/2)*m mod q`, uniform psi makes the ciphertext uniform for
every fixed message: translation is a permutation of the finite group. Its
one-time mask privacy error is therefore zero, including against quantum
advice independent of this fresh uniform mask. The remaining statistical
sampling terms are not eliminated by this observation.

[DERIVED] This is a probability-gap convention. Source advantages often use
success probability minus one-half; converting conventions changes constants.
The inequality intentionally keeps rates symbolic and conservative instead of
inventing concrete LWE bits. The required LWE assumption is against quantum
distinguishers with one independent advice state for these **classical joint
sample distributions**. It is not a coherent-query LWE oracle assumption.

## 5. Correctness and subexponential rates

[SOURCE] GKP Definitions2.2,2.6,2.8,2.10 and2.12 specify component/FE
correctness as `1-negl(kappa)`. Claim3.8 composes those correctness events.
Consequently the source gives the following useful fresh-message ledger, not
perfect correctness:

```text
delta_FE <= delta_FHE + delta_GC + L*delta_ABE2.
```

[DERIVED] The ABE2 error can itself be bounded using the two ordinary ABE
branches. GVW's actual Dec (p17) explicitly returns failure when C(ind)=0,
so the unopened branch is not silently treated as a valid label. Universal
all-coins correctness would require every underlying bad event to be removed
or separately assumed; a negligible-error statement alone cannot provide it.

[SOURCE] GVW Lemma3.1 p8 states statistical closeness of trapdoor/sample
distributions and overwhelming-probability sampler properties, without a
concrete stretched-exponential rate. Its bounded/truncated Gaussian definitions
support norm estimates; they do not, by themselves, pin every statistical and
algorithm-failure probability needed by the outer bootstrap.

[DERIVED] Polynomially many hybrid terms preserve a sufficiently strong
subexponential envelope **if every computational, statistical and correctness
term has that explicit envelope after parameter selection**. Subexponential
hardness of LWE alone does not assign a rate to an unspecified `negl` term.
For example `2^(-(log2 kappa)^2)` is negligible but eventually much larger
than `2^(-kappa^(1/4))`, even after replacing kappa by a fixed polynomial power
inside the former. `rate_ledger.py` records exact integer-exponent witnesses.
This is a falsifier of the rate shortcut, not a claim that the cited samplers
actually have this slow error.

## 6. Succinctness, output arity and the short-key condition

[SOURCE] GKP's exact ciphertext-size expression (Theorem3.1 p21) is

```text
2*L*ctsize_ABE(n*L+pksize_FHE)
    + poly(kappa,L,sksize_FHE).
```

Its instantiated size depends on prescribed circuit depth, not directly on
circuit size. The raw public key has L ABE2 public keys. GVW Setup explicitly
takes the attribute length h and depth bound; its mpk contains2h+1 public
matrices. Here h=n*L+pksize_FHE. Therefore neither encryption succinctness nor
this literal setup formula alone proves a public key independent of the
message/program bound.

[DERIVED] For a preselected polynomial family, prescribed n and d may be
absorbed into a polynomial in kappa. That observation is not a uniform solution
to the bootstrap's recursive size requirement: node descriptions contain later
public keys, and selecting a message bound that itself must contain a public
key growing with that bound may create a circular size equation. A suitable
short-key/unbounded-input parameterization or a separate compression theorem
must be supplied. This audit makes no absence claim beyond the cited source
construction and the specific transformations inspected here.

[SOURCE] ABSV2014/917 Section4/Theorem3 assumes **multi-output** shallow FE,
then places a randomized encoding of an arbitrary circuit inside its output.
The proof has straight-line SYM pseudorandom-ciphertext, NCFE, weak-PRF and
randomized-encoding hybrids. It explicitly develops the private-key version
and states that the public-key transformation is essentially identical.
GHRW2014/148 AppendixD also starts from arbitrary-output FE; footnote15 says
that a Boolean restriction is equivalent via separate output-bit keys when
**unbounded key queries** are available. AJ2015/173 AppendixC adds IND-to-SIM,
single-to-bounded-key amplification, then the depth upgrade; it notes that
compactness preservation was not explicit in the cited original works.

[SOURCE] GKP itself makes the output cost explicit: Corollary3.5 p22 charges
`q*k` times the single-key Boolean ciphertext size for q keys and k output bits;
Section3.1 p23 repeats the scheme per output bit. Remark3.7 p23 explains the
resulting exponential growth from repeatedly demanding an FE ciphertext as
the FE output. This is direct source evidence for the literal wrapper's cost,
not an inferred impossibility for every IND-secure construction.

[SOURCE/DERIVED, exact amplification subchain] CIJ2013/364 Definition13 and
Theorem14 pp15–17 add a mode bit, q tagged output slots and a symmetric key
to the encrypted message. The non-adaptive simulator programs the slots with
the known authorized outputs; adaptive keys use symmetric encrypted outputs.
Its standard-model proof has one FE indistinguishability switch followed by
symmetric-ciphertext pseudorandomness switches. It has no rewinding or random
oracle programming. For the static one-key use, tags and auxiliary symmetric
coins can be chosen before the fresh underlying setup, and the final quantum
distinguisher is invoked once. The augmented plaintext has length
`n*(2q+1)+s+1` in the printed syntax. Keeping this trapdoor circuit in NC1 needs
an appropriate shallow symmetric decryption circuit; the general-circuit CIJ
theorem alone does not assert this restricted-depth instantiation.

[SOURCE/DERIVED] GVW2012/521 Section5.1 uses N independent OneQFE public keys,
Shamir shares and random zero polynomials. Keys choose subsets Gamma and Delta;
indices in pairwise intersections may reveal shares, while every other index
has at most one underlying function key. Section5.3/Claims5.1.1–5.1.3 replace
those single-key ciphertexts by simulations and then use perfect Shamir privacy
on at most t shares. This is again straight-line for fixed classical queries.
Under a QA one-key simulation game, a conservative bound is N times that
simulation gap plus the two subset bad-event probabilities. The subset events
depend on fresh classical coins, not on the quantum advice.

[SOURCE] Section5.2 p18 actually gives `2^(-Omega(kappa))` bounds for these two
subset events with `t=Theta(q^2*kappa)`, `N=Theta(D^2*q^2*t)`,
`v=Theta(kappa)`, `S=Theta(v*q^2)`. Thus this particular error component has a
stronger stated rate than an unspecified negligible function. Setup/ciphertext
replicate N instances; input to each instance is an `(input_dimension+S)`-tuple
of field elements. D is a prescribed polynomial-degree bound. The needed
OneQFE functions return a field element, so a Boolean instantiation still needs
the explicitly bounded field-bit output interface. These facts substantiate
AJ's bounded-key bookkeeping without supplying an output-size-independent
multi-output primitive or a uniform short public key.

[DERIVED conditional upgrade] If the starting shallow FE already supports the
needed multi-output randomized encoding with one functional key and the
required output-size-independent encryption/short-key bounds, the ABSV
hybrids have the same one-advice lift under QA SYM/weak-PRF/RE/base-FE games.
In the static target, all auxiliary keys/tags and programmed classical
functions can be sampled before the base setup. Functional-message equality
in the FE switch needs exact SYM correctness, or an explicit bad-event term.
No quantum oracle queries or rewind are introduced.

[REFUTED: naive port only] Replacing that multi-output shallow FE by independent
Boolean instances is not a proof of the needed succinctness: an ell-bit
randomized encoding requires ell independent ciphertext copies. When ell
grows with the target circuit size, that wrapper's ciphertext/encryption work
does too. The one-key Boolean premise also does not authorize ell tokens
under one common master key. `rate_ledger.json` records the exact repetition
factor. This does not refute the published depth theorem or every alternative
transformation; it identifies the missing interface in this literal port.

[DERIVED coordination] The PQ owner's bit-indexed universal function constructs
the needed succinct randomized encoding with work linear in its own output
length. That useful result does not automatically make this shallow-FE depth
upgrade independent of the target function's size; the two interfaces remain
separate.

## 7. Delivered boundary and next step

[DERIVED] The positive result is a conditional QA static single-key GKP
security/correctness lemma for the explicitly parameterized supported family,
plus a source-level QA lift of its GVW ABE-to-LWE reduction. The four open
instantiation obligations are: a concrete QA garbling/FHE choice; quantitative
sampler/statistical/correctness rates; the Boolean-to-multi-output/depth
upgrade with its claimed compactness; and one uniform short-public-key bound
compatible with the recursive family. Perfect correctness may be replaced by
the PQ owner's separately tracked sufficiently small fresh error.

[EXECUTED bookkeeping] `rate_ledger.py` checks scalar rate counterexamples,
literal per-bit repetition counts, and a linear advice-use schedule. It is
not an encryption implementation or a machine-checked quantum security proof.
The substantive lemma above is a mathematical source audit requiring
independent review. No companion files, frozen PQ artifacts, shared ledgers,
adversarial service tests or commits were changed.

[EXECUTED provenance] Reproduce the evidence checks from the research root with
`python3 research/learn_infer_only/experiments/pq_composition/base_fe_audit/validate.py`.
`validation.json` retains the commands and their output; `source_spans.json`
states the inspected portions; `artifact_hashes.json` pins retained artifacts.
These checks verify provenance and bookkeeping, not the conditional security
lemma. The nine full extracted texts stay ignored and are reconstructible from
the local PDF hashes and extraction commands in `access.json`.
