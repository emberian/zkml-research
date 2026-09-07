# The exact shallow-to-deep FE interface

[DERIVED result] The inspected ABSV/GHRW construction preserves compact
encryption **when its starting shallow FE already has compact encryption for
the entire multi-output randomized-encoding function**. One final function key
then uses one underlying multi-output key. Its public-key variant is explicit
below, and its fixed-classical-input reductions admit the same conditional
one-quantum-advice treatment as the source audit.

[OPEN result] The literal GKP Boolean scheme plus the cited bounded-collusion
wrapper does not supply that interface with encryption work independent of the
randomized-encoding output bound M. Splitting outputs uses `Q*M` underlying
Boolean keys for Q final function keys. The actual cited amplification charges
its internal collusion bound in encryption/setup. A one-key indexed RE whose
encoder emits M ciphertexts has a different, output-linear interface.

[SOURCE positive theorem] Under succinct NC1 FE and symmetric encryption with
NC1 decryption, 2016/006 Theorem4 explicitly concludes that
“there exists succinct functional encryption for P/poly”, also with the stated
subexponential variants. Its introduction pp2–3 uses this upgrade before its
own XiO construction extends Boolean FE to multi-bit FE. 2015/720 Theorem7
states the same positive depth implication. This note does not refute those
published statements. It identifies the exact interface and parameter
substitution not established by the inspected literal algorithm chain for our
uniform, separately chosen size bounds. A separately proved instantiation or
a matching theorem with its reduction remains a sufficient way to close it.

## 1. Four parameters that cannot share one name

[DERIVED notation] Let n be the encrypted input width; S the maximum target
Boolean function/circuit size; Q the number of externally authorized function
keys; and `M=M(kappa,S,n)` the padded length of the shallow randomized encoding
of one target computation. Write q for the underlying Boolean-FE collusion
bound. In the direct multi-output construction q=Q. After bit splitting q=Q*M.
The source papers also use q for circuit size or a different auxiliary bound;
the following ledger keeps these meanings separate.

[HYPOTHESIS needed shallow interface `NC-MO_Q`] Public-key FE for NC1
functions whose output is the whole M-bit string. One function key returns
all M bits from one ciphertext. Its game handles Q such function keys;
its encryption work/effective encoding-key dependency is
`poly(kappa,n,Q,log S_shallow)`, with a fixed polynomial and **no M or hidden
Q*M argument**. Setup/key generation/decryption may be polynomial in the
explicit function/output bounds. The weaker effective-key convention is the
one proved sufficient by the frozen public-environment successor.

[DERIVED] For the present bootstrap Q=1 suffices externally. That makes the
required shallow premise a single-key **multi-output** FE premise, not a
single-key Boolean one. Encrypting one message and publishing a tuple of
M independently authorized Boolean keys changes the underlying security view.
Calling that tuple one application-level key does not change the collusion
game used in a proof.

## 2. What the definitions actually state

[SOURCE, 2016/006 pp5–6] Definition3 specifies static messages and function,
fresh Setup, one function key and an IND challenge; Definition4 requires
`Time_Enc=poly(kappa,|m|,log s)`, where s is the maximum supported circuit size.
Definition5 calls the Boolean-output restriction succinct FE. Theorem3 cites
GKP for NC1; Theorem4 cites GHRW/ABSV/AJ for the P/poly upgrade. Its theorem
statement supplies the desired conclusion as a source assertion; it does not
print a substitution for the multi-output interface in those references.

[SOURCE, 2015/720 pp10–11] Definitions10–12 likewise distinguish compact FE
from its Boolean restriction. Theorem7 prints the upgrade from succinct NC1
FE to succinct P/poly FE. This is the same source-level claim, not an additional
algorithm closing the output/collusion substitution.

[SOURCE, AJ2015/173 §2.3.1 pp11–12] Definition3's **compact FE** supports its
general output space and requires `|pk|=p(kappa)` and encryption time
`p(kappa,qkey,|x|)`. The explanatory text says the time is independent of
function-family complexity. Definition4 separately names **semi-compact FE**:
the Boolean-output restriction, or a version whose work may depend on output
length. These are distinct source interfaces.

[SOURCE, AJ AppendixC pp56–57] The appendix is a transformation from compact
single-key FE to compact bounded-key FE. Step1 applies CIJ IND-to-SIM for NC1;
Step2 applies GVW bounded-key amplification; Step3 applies GHRW/ABSV to the
compact NC1 scheme. Its Step3 begins with the full compact interface, not an
explicit theorem upgrading arbitrary semi-compact Boolean input while keeping
M absent. AJ notes that compactness preservation is not explicitly stated in
the cited original works. Section8 separately uses semi-compact bounded-key
FE for NC1 and references AppendixC's amplification; that reference does not
make semi-compact and full compact synonymous.

[DERIVED quantifier qualification] These papers describe polynomial-size
families parameterized by kappa. For a preselected family an output bound
M(kappa) can be called a polynomial in kappa. That observation alone does not
establish the fixed uniform polynomial in our separately selected size S:
substitute the actual q argument before absorbing it. We do not infer a logical
contradiction in a published existence statement from this family notation.
The recursive resource proof needs a uniform algorithm/parameter ledger, not
merely a family-dependent assertion that each resulting cost is polynomial.

[SOURCE/DERIVED, ABSV alternative route] Its introduction pp4–5 and Section4
p12 also discuss the Section3 internal-FE route: an outer functional key
produces an internal functional key, and the internal setup can be shallow.
Shallow setup is a depth property; it does not bound the length of the emitted
internal functional key independently of F. That observation alone therefore
does not replace the missing vector-output cost substitution either.

## 3. The public ABSV construction, with the missing premise explicit

[SOURCE, ABSV2014/917 §4 pp12–14] The paper assumes NCFE supports multi-bit
functions and says otherwise one can issue a key per output bit. Its shallow
function is

```text
G_F,CE,tau(x,KP,KE,beta) =
    SYM.Dec(KE,CE),                         if beta=1;
    RE.Encode(F,x;PRF_KP(tau)),             if beta=0.
```

[SOURCE] This function outputs the entire randomized encoding, not the final
Boolean F(x). The paper uses weak PRFs and symmetric decryption in NC1 plus
a randomized encoding whose **encoding circuit** is in NC1. Its encryption
time and output length can grow with the encoded circuit F. The randomized
encoding decoder need not be in NC1.

[DERIVED explicit public variant] Assume `NC-MO_Q`, a suitable classical weak
PRF, pseudorandom-ciphertext SYM with NC1 decryption, and the indicated shallow
RE. All algorithm/tape/length bounds are fixed before setup. Then:

```text
Setup:      (pk,msk) <- NCFE.Setup(kappa,bounds).
KeyGen(F):  sample public tag tau and uniform CE of padded SYM ciphertext length;
            skG <- NCFE.KeyGen(msk,G_F,CE,tau);
            return (skG,F,CE,tau).
Enc(pk,x):  sample KP; return NCFE.Enc(pk,(x,KP,0,0)).
Dec(sk,ct): z <- NCFE.Dec(skG,ct); return RE.Decode(z).
```

[SOURCE/DERIVED] The paper develops private-key syntax and states the public
version is essentially identical. This displayed version is that direct
public substitution: encryption uses pk; setup returns pk and msk; functional
queries are answered through the underlying key generator. No master secret
is added to public encryption or to the final function key. The real-mode
correctness equation is exactly `RE.Decode(RE.Encode(F,x;r))=F(x)` plus
underlying decryption correctness.

[DERIVED parameter substitution] The encrypted input has width `n+O(kappa)`.
If shallow RE, SYM and weak PRF admit the stated depth bounds, the size of G
is `S_G=poly(kappa,S,M)` and its depth is the appropriate NC1 bound. One outer
key uses one G key, so the actual collusion argument remains Q. Encryption is

```text
E_PFE(kappa,n,S,Q) = O(kappa) + E_NCFE(kappa,n+O(kappa),S_G,Q).
```

[DERIVED] Therefore a genuinely output-independent compact `NC-MO_Q` gives
`E_PFE=poly(kappa,n,Q,log S)` when M and S_G are polynomial in the public target
bounds. This is a useful positive conditional substitution. A scheme with
`E_NCFE` polynomial in M gives no such conclusion merely because F's final
output is one bit. Function keys/CE may be long; that alone is allowed.

[DERIVED QA scope] For static F/messages, all tags, PRF keys, symmetric keys
and programmed CE values needed for one hybrid can be sampled before the
current NCFE setup. The equality needed for the NCFE challenge is equality of
the **entire encoded vector**. The remaining proof replaces SYM ciphertexts,
then one NCFE message, then PRF values, then randomized encodings by their
simulations, and reverses for the other message. These are classical-string
hybrids with one final quantum distinguisher invocation. A conditional lift
requires the matching QA games for the Q-key multi-output NCFE and those
particular weak-PRF/SYM/RE interfaces. It does not follow by substituting the
single-key Boolean QA game where the vector challenge is used. Repeated tags,
fresh correctness and statistical errors retain their explicit bad-event
terms; none is assigned a numerical rate here.

## 4. GHRW preserves q only at its own vector interface

[SOURCE, GHRW2014/148 AppendixD pp35–38] FEcirc has arbitrary output size.
Footnote15 says Boolean outputs are equivalent via separate output-bit keys
**in the unbounded-key-query case**. Its function C_FE returns the entire
one-time garbled RAM program and garbled input, or the M-bit pad branch.
FEram.Enc performs one FEcirc encryption of `(x,K0,0,flag=0)`.

[SOURCE] TheoremD.3 preserves q-key-query IND security. The proof explicitly
counts one C_FE query for one RAM program query. SectionD.3 assumes the
underlying FEcirc encryption complexity is `n*poly(kappa)`; this is an
assumption on that starting scheme, not a conclusion derived from Boolean
GKP encryption. It also proposes an optimized key consisting of one key per
output bit to improve key-generation/decryption work.

[DERIVED] Applying the bitwise optimization with bounded Boolean collusion
requires counting the whole tuple: Q program keys with M bits each expose
Q*M Boolean function keys. The unbounded-key model can tolerate this without
changing setup parameters; a bounded-key scheme whose ciphertext cost depends
on q generally cannot. TheoremD.3's direct vector-key q preservation and the
bitwise optimization are both valid at their stated interfaces; they cannot
be silently combined to keep q=Q for a Boolean backend.

## 5. Literal GKP/GVW substitution

[SOURCE, GKP2012/733 Theorem3.1 pp20–21] The basic one-key Boolean ciphertext
contains L two-outcome ABE instances and a garbled decryption circuit; its
size depends on prescribed depth. Corollary3.5 p22 explicitly charges a
`q*k` expansion for q queries and k output bits. Section3.1 p23 repeats the
scheme per output bit; Remark3.7 notes the cost of repeated ciphertext-output
chaining. These source constructors do not claim output-independent vector
FE from the Boolean implementation.

[SOURCE, GKP Remark3.6 p22] The paper explicitly distinguishes the underlying
ABE's many-key security from the resulting FE's single-key guarantee. Thus
GVW's ABE collusion resistance cannot be substituted for FE collusion
resistance when issuing the M different output predicates.

[SOURCE, GVW2012/521 §5 pp16–22; AJ AppendixC] The bounded-key wrapper uses

```text
t       = Theta(kappa*q^2),
N_inst  = Theta(D^2*q^2*t),
S_share = Theta(kappa*q^2),
Enc     = N_inst independent OneQFE encryptions of share/mask tuples.
```

[SOURCE/DERIVED] D is the prescribed polynomial degree of the shallow
arithmetic circuit family; it is not the RE output length. Substituting the
required Boolean collusion q=Q*M yields

```text
N_inst  = Theta(kappa*D^2*Q^4*M^4),
S_share = Theta(kappa*Q^2*M^2).
```

[DERIVED] The instance count alone retains polynomial dependence on M, before
charging increased share-message widths or the OneQFE costs. This is a
parameterized source algorithm, not a measured latency or an exact numerical
constant for Theta notation. The GKP corollary's stated q*k expansion and the
GVW/AJ N-instance formula are separately recorded source bounds; they are not
treated as identical exact implementations.

[DERIVED positive limited case] With a fixed bound on the required Boolean
keys, the wrapper does supply a bounded-key shallow scheme with its explicit
parameter costs. At arithmetic field width b, G_C,Delta returns one b-bit
field element; this bounded field-bit interface can be furnished by a b-output
variant, paying that cost. It does not itself produce an arbitrary M-bit RE
vector independent of M. Packing chunks of b output bits requires at least
`ceil(M/b)` chunk functions; the simple GKP chunk wrapper still charges b
output bits per chunk. `b*ceil(M/b)>=M`, so relabeling output bits as larger
field elements does not remove the literal wrapper's output work.

## 6. An available conditional constructor: AJ's compact TM-RE route

[SOURCE, AJ2015/173 §8 pp44–47/Theorem9] The paper does give an actual route
from semi-compact NC1 FE to **full compact NC1 FE**, followed by the depth
upgrade. It assumes an additional compact **IND randomized encoding for
Turing machines**, defined in Section8.1 with encoder time
`poly(kappa,|Program|,|input|,log T)`. This is a time-compressing primitive,
not merely the NC1-encoding randomized encoding used inside ABSV.

[SOURCE/DERIVED explicit algorithm] For output bound M, a short program
`SetupLoop(Ks)` generates M SCFE setups using the indexed PRF coins `P_Ks(i)`
and returns their public keys. The published FE key is a compact TM encoding
of that program/input; Setup also retains the matching M master secret keys.
For a function F, KeyGen emits the M tokens for its output-bit functions.
To encrypt m, choose a fresh PRF key Ke and compactly encode the short program

```text
EncLoop(encoded_setup,Ke,m):
    (pk_1,...,pk_M) := TMRE.Decode(encoded_setup);
    return (SCFE.Enc(pk_i,m;P_Ke(i)))_(i=1..M).
```

[DERIVED notation completion] SetupLoop and the stored master keys must use
the **same explicit** `P_Ks(i)` tapes. The setup prose specifies them; the
printed loop figure omits those tape arguments. The punctured versions in the
proof must likewise insert the supplied challenge pk/ciphertext at the selected
index and use off-point PRF evaluation elsewhere. We state these requirements
explicitly rather than treating the abbreviated figures as executable code.

[DERIVED parameter substitution] There are M independent SCFE instances, but
each instance receives only Q keys for Q outer functions. Thus its collusion
bound stays Q. The work to **execute** EncLoop is `M*E_SCFE` plus decoding
the setup; actual encryption only **encodes** that loop with the compact TMRE.
The loop description has logarithmic M metadata and fixed algorithm code.
Given a uniformly efficient SCFE and the stated TMRE, actual encryption has
`poly(kappa,n,Q,log M,log S)` work after including its short encoded setup
key and logarithmic execution bound. Long output expansion is paid during
decoding. Setup and function-key generation can still cost polynomially in M.
This is an actual conditional output-compression mechanism, rather than a
renaming of M ordinary encryption operations.

[SOURCE] The efficiency paragraph on printed p47 explicitly requires the
encryption polynomial to be selected before the function space is designed.
That confirms the intended uniformity of its compactness argument; simply
hiding an M-dependent amplification cost inside a new family-specific
polynomial would not reproduce this argument.

[SOURCE/DERIVED proof scope] AppendixB pp53–56 uses an index-by-index sequence:
replace setup/encryption loop encodings by versions punctured at one index;
make that index's setup and encryption tapes uniform; switch its SCFE
ciphertext; reverse those replacements. Other positions remain locally
generatable. Each target SCFE instance uses Q function queries, not Q*M.
Under fixed classical external functions/messages, this is a candidate
straight-line QA lift with explicit QA puncturable-PRF, Q-key SCFE and compact
TMRE games. To compare different program descriptions with a same-machine
TMRE IND definition, use one fixed universal machine and put the padded
program description in its input; equal outputs and matching time metadata
are then explicit. No claim is made here to derive this new compact TMRE
game from the earlier B/P/G/X assumptions or from LWE.

[OPEN] The source constructor therefore locates a genuine alternative closing
premise: a compact TMRE for these setup/encryption loops. Granting that
primitive supplies the desired full shallow interface. The inspected
LWE→Boolean-GKP construction does not itself supply it, and the frozen
indexed `R_S` only has output-linear encoding work. Full quantitative QA
security/correctness bookkeeping for this extra route remains separate.

## 7. Why indexed RE and public environments do not fill this slot

[SOURCE/DERIVED] The frozen bootstrap's `R_S` issues one key for an indexed
Boolean function and encrypts `(m,index,...)` M times under the same pk. The
one-key multi-ciphertext privacy proof is legitimate because every index gets
its own public encryption. Its work is linear in the emitted output length.

[DERIVED] The ABSV NCFE ciphertext encrypts only `(x,KP,0,0)`. Its functional
key must reveal all M RE bits from that one ciphertext. An index placed in the
encrypted message fixes only one bit; an unencrypted caller-controlled index
would be an extra public-input functionality not supplied by ordinary B. One
key for a universal indexed predicate is therefore not an implementation of
this all-bits-from-one-ciphertext interface. Emitting M encryptions preserves
the valid RE construction but introduces precisely the M-dependent work at
issue here.

[DERIVED] The public-environment successor solves a different size feedback:
future keys can live in specialized public functions instead of node plaintext.
It also derives an effective small key from compact encryption circuits under
an explicit computation model. Neither transformation deletes gates/output
writes already needed to produce M Boolean ciphertexts or the cost of Q*M
collusion parameters. In particular, moving long function descriptions into
Setup does not turn the described shallow ciphertext constructor into an
output-independent one.

## 8. Exact stopping point and next proof target

[DERIVED] An actual closing artifact can take either of two forms: an
explicit shallow `NC-MO_1` implementation for the encoded-vector/pad functions
above with a uniform output-independent encryption/effective-key bound; or
a different direct succinct Boolean P/poly construction whose complete
source reduction and parameter choice are audited. The inspected direct
ABSV/GHRW algorithms close the depth upgrade **conditional on** the former.
The inspected GKP and bounded-key wrapper retain M in that slot.
AJ's compact TMRE construction supplies a concrete way to obtain the former
interface, conditional on that additional time-compressing primitive.

[OPEN] This read did not establish such an implementation from the named
LWE/QA primitives. The absence statement is limited to the nine locally
pinned papers and the exact sections listed in `inputs.json`/the prior
source-span register, inspected through their extracted text. It is not a
search of all FE literature, an impossibility result or a verdict that a
published theorem fails. No new metered or web searches were used.

[OPEN review status] This is a source/parameter audit for independent review.
The accompanying ledger performs symbolic resource substitutions and arity
counts only. It does not run encryption, protected-output tests or a quantum
adversary. Frozen predecessor notes and all shared/companion files stay intact.

[EXECUTED bookkeeping] `arity_substitution.py` records 12 exact query-count
rows and 36 chunk-width rows, including the `Q*M` substitution and normalized
M^4/M^2 source monomials. Those monomial ratios are not exact implementation
cost ratios with unknown Theta constants. Run
`python3 research/learn_infer_only/experiments/pq_composition/base_fe_audit/depth_interface/validate.py`
to verify the 23 source/frozen input pins and saved arithmetic. Commands and
output are retained in `validation.json`; `artifact_hashes.json` pins the seven
delivered files. No cryptographic runtime or protected-output test is run.
