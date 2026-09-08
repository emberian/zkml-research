# Public setup for fixed-policy lattice IPFE

Date: 2026-09-08. Scope: mathematics and primary-source audit only.

[DERIVED, conditional positive] The fixed-policy direction does have a concrete
lattice candidate. First change the plaintext basis so the authorized rows become
coordinate reads. Independent recipients generate only the short secret rows for
those coordinates. The public constructor samples the remaining public-key rows
uniformly, without generating their short preimages. ALS's Gaussian syndrome
regularity lemma makes the complete joint setup statistically close to its proved
IPFE setup. This avoids the generally invalid operation of solving an arbitrary
Gaussian affine fiber by field pivots. The result is a fixed, honest-registration,
IND construction; its post-quantum security is conditional on the corresponding
QPT security of the source IPFE game. No QROM or malicious-registration theorem
is silently supplied.

[SOURCE] Agrawal–Libert–Stehlé, 2015/608, §4.2, printed pp17–20,
Theorems 3–4 and Appendix C Lemma 10, printed p34. The actual algorithms,
distribution, game/reduction statements and regularity lemma were read locally.
See SOURCES.md and SOURCE_MANIFEST.json for access levels and immutable hashes.

## Baseline and scope

[SOURCE] Prior local artifacts read first: PRIVATE_CONSTRUCTION.md's ALS
construction; experiments/private_construction/RLWE_AUDIT.md; and
designated_span/public_coin_setup/PROPOSAL.md, review/REVIEW.md,
sources/PRIOR_ART.md and implementation_review/REVIEW.md. The accepted DDH
construction uses exact uniform translation, uniform affine fibers and a
conditional public-root transcript simulator. It establishes fixed-span leakage,
not selected-trace release. The prior RLWE audit already records finite-noise
closure and issuer/master-state issues; none of its experimental work is rerun.

[DERIVED scope] Fix a prime p, plaintext dimension d, and r designated rows
Y in F_p^(r×d), with row rank r<d. Fix a coalition J contained in [r] before key
generation. All recipients and public setup follow the algorithms below. Each
recipient gets its complete designated projection on every retained input.
Arbitrary public replay and allowed linear state operations add no leakage
beyond those per-input projections. This statement neither enforces a selected
trace nor certifies privacy on a particular resident encoder's semantic image.

## Source scheme and the Gaussian seam

[SOURCE] In ALS §4.2, use q=p^k and Δ=q/p. Setup chooses
A uniform in Z_q^(m×n), Z from the prescribed τ on Z^(d×m), and U=ZA mod q.
The master is Z. For linearly independent key queries y in F_p^d, the key is
(the canonical integer lift of y, z_y=lift(y)^T Z). Dependent queries use a
stateful integer lift rule. Encrypt a∈F_p^d as

    c0 = A s + e0                   mod q
    c1 = U s + e1 + Δ lift(a)       mod q,

where s is uniform and e0,e1 have the specified discrete Gaussian errors.
The decryption phase is Δ(y·a mod p)+lift(y)·e1−z_y·e0 mod q.
Theorem 3 requires m≥4n log_2 q and prescribed τ; Theorem 4 reduces the
multi-hint extended-LWE assumption to LWE with its stated dimension/noise loss.

[SOURCE] τ has mutually independent rows. Each row's first m/2 entries are
independent centered D_Z,σ1 samples. Its second half is an independent Gaussian
row of width σ2 with the source's specified integer center. The widths are
chosen by the reduction, not freely minimized: §4.2 includes the quantity
K'=(sqrt(d) p)^d. Appendix C Lemma 10 applies to uniform A'∈Z_q^(M×n)
and z∼D_Z^M,σ,c when M≥2n log_2 q and σ≥Ω(sqrt(n+log M)); it bounds
SD((A',z^T A'),(A',u)) by η(n)=2^−Ω(n). The displayed source widths can be
chosen to meet this lower bound; retain all the source's other inequalities.

[DERIVED, refutation of one literal transfer] Arbitrary independent recipient
choices do not reproduce the unmasked source keys YZ for a fixed non-coordinate
Y. For one first-half column of Z, let its independent entries have variance
v>0. With rows (1,0,1) and (0,1,1), the two actual key entries have covariance
v, whereas independently sampled recipient entries have covariance zero.
Both rows are linearly independent, so full row rank alone does not repair
this exact-distribution mismatch. This observation concerns this unmasked
sampling proposal, not all lattice public setups.

[SOURCE/DERIVED] The conditional law in ALS's Lemmas 1–2, printed pp15–16
and pp19–20, is a shifted lattice Gaussian on the integer kernel of the queried
row matrix. In elementary form, for z∼D_Z^d,σ,c and exact integer constraints
Yz=k, the mass on an admissible z is proportional to
exp(−π||z−c||²/σ²). It is not uniform on the fiber. Modular pivot inversion also
need not preserve a short integer representative; the correctness term uses
the actual integer key against e0. These are the missing premises in a literal
DDH-to-LWE replacement. The construction below does not perform this sampling.

## Algorithms: public basis, recipient rows, uniform hidden syndromes

[DERIVED construction] All setup parameters, Y and the coalition scope precede
the recipients' independent draws. Choose a deterministic public completion
B∈GL_d(F_p) whose first r rows equal Y. Complete Y by a fixed ordered scan of
standard basis rows. This algorithm depends only on Y. There is no requirement
that an integer lift of B preserve a Gaussian: B acts on messages, not secrets.

1. PublicSetup: choose A uniformly entry by entry in Z_q^(m×n). Publish A,
   the source parameters, Y and B. For each j>r, independently sample a public
   row u_j uniformly in Z_q^n. The accepted public coins are precisely A and
   these u_j values. Never sample a secret row for these coordinates.
2. RecipientGen(i), for i≤r: privately sample z_i from the i-th row marginal
   τ_i of the source's d-dimensional τ. Publish u_i=z_i A mod q and keep z_i.
   The private state is the sampled Gaussian vector, under the usual ideal
   distribution convention. No curator obtains a copy of it.
3. PublicCompile: assemble U with the published recipient rows and the uniform
   remaining rows. Publish encoding key (A,U,B,Y,parameters) and the public
   setup transcript. This is public deterministic computation after step 1.
4. Encode(x): compute a=B x mod p and run the displayed ALS encryption of a
   with fresh independent private encryption coins. B is invertible, so the
   encrypted mathematical state retains all of x; it is not just Yx.
5. Read(i,c): compute c1_i−z_i·c0 mod q and round to the nearest Δ multiple.
   The output is a_i=Y_i x mod p whenever the source error bound holds.

[DERIVED lifecycle] A public constructor holds only public matrix entries and
ordinary deterministic work buffers. Each recipient holds one restricted
coordinate key. No algorithm constructs Z's other d−r rows, a trapdoor for A,
an arbitrary-row key generator, or any aggregate full master. Encryption issuers
know the current plaintext x and their own fresh coins, as in public-key IPFE;
they are not given z_i and need no online writer secret. Public setup coins are
not encryption coins. There is no erasure of a previously generated unrestricted
decryption credential in this algorithmic account.

[DERIVED boundary] This describes honest independent draws and their accepted
values, not arbitrary CSPRNG seeds, Gaussian rejection tapes, user-written key
software, or a malicious public randomness service. A constructor deliberately
forming every hidden u_j=z_j A with known z_j is outside this honest experiment.
Public consistency alone does not certify absence of retained preimages.

## Full joint setup distribution

[DERIVED lemma] Let R=[r]. Define the source comparison distribution S by
sampling A uniform and all independent Z_i∼τ_i, setting U_i=Z_i A, and exposing
(A,U,Z_R). Define P by the real public setup above, exposing exactly the same
tuple. Then

    SD(S,P) ≤ (d−r) η(n).

Proof. Split A=(A_L;A_R) into m/2-row blocks and Z_i=(L_i,R_i).
The source's L_i∼D_Z^(m/2),σ1 is independent of R_i, the other rows, and A.
Theorem 3's m≥4n log_2 q gives the dimensional hypothesis of Lemma 10 for
A_L. First fix independent A_R,R_i and apply that lemma to (A_L,L_i A_L).
Adding R_i A_R preserves distance to a uniform syndrome. Thus each missing
U_i may be replaced by an independent uniform row at statistical cost η(n).
All other row samples and products are randomized postprocessing of A with
fresh independent randomness, so adjoining them, including every actual
recipient secret Z_R, cannot increase this distance. Replace the d−r rows in
sequence and use the triangle inequality. The source's nonzero second-half
centers cause no problem because that block contributes only the fixed shift
within the argument. This proves the joint bound, not merely a marginal bound.

[DERIVED transcript lemma] Append public coins (A,(u_j)_{j>r}), B,Y and
recipient announcements to S or P by copying their already present public
entries. Statistical distance cannot increase. From an ordinary source IPFE
view, the transcript simulator simply copies A and U_j and labels them as the
accepted public draws. There is no conditional Gaussian-preimage sampler.
In the comparison experiment, their distribution is close to public uniform
coins, exactly as bounded above. This is statistical, not exact, equality.

[DERIVED role simulation] For a coalition J, ask the source key oracle only
for e_i, i∈J. These coordinate vectors are linearly independent modulo p and
the source key is exactly z_i, with lift e_i. Public announcements of other
recipients are their existing source U_i rows. The simulator needs neither
their short vectors nor any non-recipient vector. A challenge pair x0,x1 with
Y_J x0=Y_J x1 maps to a0=B x0,a1=B x1 with e_i·a0=e_i·a1 for every i∈J.
Thus source challenge admissibility is exact. Stateful dependent-key handling
is never invoked by this reduction.

## Conditional security theorem and nonvacuity

[DERIVED theorem] Suppose ALS §4.2 with the stated parameters is single-challenge
IND-secure for adversary class C, with classical public/key/challenge interfaces,
under its actual source game. Run the construction above with honest independent
registration, fixed full-rank Y and static J. For any C adversary receiving the
public setup transcript, coalition keys, at most T adaptive classical challenge
pairs with Y_J x0,t=Y_J x1,t, and arbitrary efficient public postprocessing of
the retained ciphertext history,

    Adv_public ≤ T · Adv_ALS(single challenge, corresponding resources)
                 + 2(d−r)η(n).

Here advantage means the difference of acceptance probabilities between the two
worlds. Each world differs from its source comparison by at most (d−r)η;
a standard T-step public-encryption hybrid reduces the comparison experiments
to the exact source game. The hybrid samples the other ciphertexts itself and
passes the selected adaptive challenge to the source challenger. No secret
setup reconstruction or retained-state erasure is used. Public postprocessing
is just part of the adversary, so storing or recombining the full history does
not require a new confidentiality game. Correctness of allowed recombinations
still has the separate finite-noise premise below.

[DERIVED/PQ boundary] The joint distribution and transcript arguments are
statistical and remain valid with quantum auxiliary state produced from the
classical view. The black-box encryption hybrid is straight-line for QPT
adversaries with classical challenge messages. Accordingly the theorem is a
genuine conditional PQ construction if the source ALS game is secure for that
class. The source labels Theorem 3 fully secure under multi-hint extended LWE
and gives Theorem 4's LWE reduction; this tranche has not certified every step
of those reductions as a QPT theorem. It therefore does not state an
unconditional published QIND-IPFE result, infer a QROM theorem, or replace the
specific source assumption/parameters with an arbitrary practical RLWE scheme.

[DERIVED nonvacuity witness] Over any F_p, take d=3, r=2 and

    Y = [1 0 1; 0 1 1],       B = [1 0 1; 0 1 1; 0 0 1].

B has determinant one. For any x, let h=(−1,−1,1). Then Y(x+h)=Yx while
the protected coordinate g(x)=x_3 changes by one, and B h=(0,0,1).
Thus even the coalition of both recipients can have nontrivial equal-output
challenge pairs while the encrypted full states differ. This uses the same
overlapping rows that defeated literal independent sampling of YZ. It is a
mathematical witness on the full domain F_p^3, not an assertion that the current
resident encoder contains this pair. For an actual image X, require x,x'∈X
with Y_J x=Y_J x' and protected g(x)≠g(x'). If Y_J is injective on X, absence
of a scalar/matrix master says nothing useful about semantic confidentiality.

## Arithmetic closure and costs

[DERIVED] Since B is linear modulo p and q=pΔ, coordinatewise ciphertext
addition/subtraction represents the same operation on x modulo p, with the
corresponding signed sum of errors. No large lift of B multiplies a secret or
an error: Encode reduces Bx modulo p before encryption. Public plaintext
offset v is added as (0,Δ lift(Bv)); this adds no encryption error. For a finite
window with exact original ciphertext expiry, canceled inputs' errors cancel
too. This is the same finite-noise algebra already audited for ALS.

[DERIVED sufficient bound] If every retained input t has coordinate-read
phase error |e1,t,i−z_i·e0,t|≤E_i as an integer representative, then a signed
combination with coefficient L1 norm at most W decrypts correctly when
W E_i<Δ/2. Tail failure probabilities and a union bound must cover the actual
number of generated inputs and retained windows. Unbounded histories or
arbitrary coefficient growth are not admitted by this correctness claim.

[DERIVED integer interpretation] The proved output is in F_p. Interpreting it
as an intended integer requires an injective promised output interval, for
example a centered interval with absolute value below p/2, including cumulative
window bounds. Modular correctness alone does not supply that promise. Closure
here is for scalar combinations under the same public key and plaintext offsets.
A general update x←T x would transform c1 by B T B^−1 and change U to
B T B^−1 U; the existing coordinate keys generally no longer cancel its mask.
Such a transform needs a separate evolved-key/span argument and is not claimed.

[DERIVED counts, algebraic not benchmarks] The public matrices have mn+dn
residues; each input ciphertext has m+d residues; each recipient stores m
integers of the source Gaussian widths. Each recipient publishes n residues.
The additional transform stores a d×d public field matrix and takes at most
d² field multiply-add terms per input. These are structural counts, not a
parameter estimate; the source modular construction's d-dependent widths can
be costly. Public setup generates (d−r)n additional uniform residues, and no
hidden Gaussian rows. This has the original IPFE ciphertext shape and encrypts
the entire invertible message basis, unlike a bank of ciphertexts only of Yx.

## Current registered/decentralized sources: what they establish

[SOURCE] 2023/395, Registered (Inner-Product) Functional Encryption, gives
registered inner-product predicates from asymmetric pairings/generic groups;
its general-circuit result uses iO and somewhere-statistically-binding hashes.
The title's inner product is not a numeric LWE-IPFE instantiation. 2025/836
does give numeric attribute-weighted sums, but its instantiations use bilateral
k-Lin pairings. Neither is the lattice setup theorem required here.

[SOURCE] 2021/046 §6 and Appendix D.4 decentralize input-owner key-generation
authority. The compiler first produces underlying FE master state plus local
masks; its Enc and local KeyGen interfaces take retained client master state.
The local client is not merely an independently keyed restricted output
recipient. Removing one centralized entity does not remove that credential.
Static-corruption/ROM qualifications also persist. No previous RLWE failures
were re-executed.

[SOURCE] 2024/1572 gives adaptive SIM registered FE for circuits under a setup
bound Q on corrupted users, including a lattice path under LWE plus evasive LWE
and ROM. The checked syntax excludes malicious registration. Its §4.1 public
PKE CRS is generated by PKE.Setup producing (pk,sk), with sk omitted thereafter;
§5.1's basic compiler also generates dummy-user keys. A later lattice variant
removes the dummy-key step, so it is not a universal obstruction. This tranche
has not shown that the unused PKE secret alone is a universal reader. The
precise unresolved application issue is whole-setup credential generation and
public-coin transcript exposure, together with the Q bound and security model;
a public curator by itself does not establish that stronger lifecycle claim.

[SOURCE] 2025/967 gives registered FE for pseudorandom functionalities under
LWE plus an evasive-LWE-based primitive. Its required pseudorandom output
property for every adversarially seen input is not ordinary numeric inner
products: a fixed zero vector forces a known zero output. This is a scope
mismatch, not a refutation of that registered primitive.

[SOURCE, positive adjacent construction] Wee–Wu 2025/1039, Remarks 4.13
(printed p22) and 5.31 (p51), explicitly gives transparent distributed broadcast
encryption and unbounded key-policy registered ABE via decomposed LWE.
The public matrix-commitment parameters replace the basic TrapGen-based
structured string by (Bhat,W,R), where W is uniform, R is a public discrete
Gaussian matrix, and Bhat is their specified public algebraic function.
The source says these parameters derive from uniform public randomness.
This is a real lattice access-control setup result, not merely the absence of
a retained curator key. It uses decomposed LWE, not a deduction from plain LWE.

[SOURCE] In its Construction 5.11, independently generated user state is
r_i∈{0,1}^m, with public t_i=B r_i+A_f G^−1(H1(i))+p and a proof of knowledge.
Public aggregation computes the aggregate encryption matrix and helper keys;
encryption needs only public data. A policy f authorizes an attribute a when
f(a)=0 in this paper's convention. This releases the entire separately encrypted
message for authorized attributes; it does not compute numeric Yx on a hidden
message. Theorem 5.14 proves attribute-selective security without corruptions;
Remark 5.4 describes a ROM corruption compiler and complexity leveraging for
adaptive attributes. Remark 5.6 says the proof uses secret-key extraction while
simulating adversarial random-oracle queries. The transparent ABE remark does
not itself audit every NIZK CRS coin or establish QROM security. Those are
explicit remaining premises before a full public-transcript/QPT application.

[SOURCE, abstract only/open] Liu–Wang–Fu, arXiv:2505.11744, reports lattice
multi-authority noisy/evasive IPFE and a modulus-switching exact variant. Its
abstract states static ROM security under LWE and new evasive-IPFE assumptions.
The full construction and exact authority/issuer credential lifecycle were
not read from a local mirror in this tranche. This is an unresolved related
source, not evidence of absence and not an instantiated repair.

## Handoff

[DERIVED recommendation] Independently review the basis-change construction,
the Appendix C Lemma 10 joint hybrid (including all recipient keys and public
accepted coins), and the source-QPT premise. The Gaussian covariance mismatch
is a warning about an unmodified proposal, not the final outcome of this lane.
The transparent registered-ABE source is an adjacent positive result with a
different functionality and assumptions. The finite projection-PKE bank was
only considered as a weaker control; it is unnecessary for the construction
proved here and is not promoted as an equivalent full-state implementation.

[OPEN next bounded steps] (1) QPT audit of ALS Theorems 3–4 under classical
interfaces; (2) a symbolic semantic-image witness for any concrete authorized
row system; (3) independent finite-parameter/noise feasibility analysis if this
theorem is adopted; (4) full local-source reading of the identified 2025
multi-authority paper if its issuer model becomes relevant. None authorizes
runtime extraction, disclosure, signer routing, or any previously stopped work.
