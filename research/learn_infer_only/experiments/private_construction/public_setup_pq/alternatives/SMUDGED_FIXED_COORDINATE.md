# A separate fixed-coordinate smudging theorem

[DERIVED, review candidate, 2026-09-08] The single-block algebra of Han–Yi–Liu–Gu
(HYL), ePrint 2025/1613 Fig.6 p28, admits a restricted proof using noise
smudging, ordinary LWE, and Gaussian syndrome regularity. This note does not
invoke HYL Theorem3, its parameter table, ALS's multi-hint LWE reduction, or
an estimator. It is a new conditional theorem, not a claim that the source's
full adaptive functional-key theorem holds at the parameters below.

[SOURCE] HYL Fig.4 p25 gives independent Gaussian rows K and P=KA, and its
public/private evaluation comparison p26 bounds the change caused by Ke
using independent uniform flooding. Fig.6 p28 specializes to one block when
its parameter L equals its plaintext dimension. The smudging step below
retains all K, which is stronger than the restricted exposure it needs.

## 1. Algorithms and exact exposure

[DERIVED] Fix an odd prime p, d>r, independent policies Y in F_p^(r×d), and
a public invertible B in F_p^(d×d) whose first r rows are Y. Let
X=(p−1)/2. The full plaintext space is F_p^d. Define the bijection
a(x)=center_p(Bx), from F_p^d to the integer cube [−X,X]^d.
Fix a prime q, l≥n+1, Gaussian widths σK and σe, and integer F≥1. All
Gaussian widths use mass exp(−πz²/σ²). Set D=dX and Δ=floor(q/D).

[DERIVED algorithms]

1. Public setup draws A uniformly from F_q^(l×n).
2. Each recipient i in [r] independently samples k_i from D_(Z^l,σK),
   publishes P_i=k_i A mod q, and retains k_i. No other recipient's row is
   needed. Each missing P_i, i>r, is drawn directly uniformly from F_q^n.
   The public key is (p,q,B,A,P,Δ); no k_i for i>r is generated.
3. Enc(x) samples w uniformly from F_q^n, e from D_(Z^l,σe), and f uniformly
   from the integer cube [−F,F]^d. It returns

       c = Aw+e mod q,       h = Pw+f+Δ a(x) mod q.

4. Coordinate recipient i computes h_i−k_i c mod q. For an issued input it
   decodes to the nearest Δt for t in [−X,X]. For an allowed aggregate it
   uses t in [−WX,WX], then returns t mod p. A centered integer score is
   returned only when the separate application range promise makes it unique.

[DERIVED encryption-coin boundary] Each encryption uses fresh private w,e,f
and private sampling tapes. These are not public setup coins. The challenge
game gives ciphertexts and exposed recipient rows, not the challenge coins;
exposing f would invalidate the stated smudging transition. There is no
long-lived secret encryption credential: encryption uses only the public key
and fresh coins, although an encryptor knows its own input and coins.

[DERIVED credentials] Recipients possess their integer Gaussian rows, not
just residues or a generic functional key. A coalition J⊆[r] receives those
entire rows. Its linear combinations give the corresponding row span; these
credentials remain real functional/read capabilities. The public constructor
has only public A, public P, and their direct sampling values. It never
generates a matrix master, absent row, trapdoor, or input read credential.
Honest recipient participation and a fixed policy are premises; malicious
registration, interactive proof of correct sampling, and adaptive corruptions
are outside this theorem. There is no erasure premise for absent rows.

[DERIVED transcript] Copies of directly sampled public values add nothing
to (A,P). An implementation's rejection logs need an output-conditional
simulation argument before inclusion; the theorem is about ideal exact
sampling outputs and the stated exposed rows. It does not expose hypothetical
random tapes used to generate missing k_i in the comparison experiment.

## 2. Honest joint setup distribution

[DERIVED] Compare actual setup with a hypothetical honest setup sampling all
d independent k_i and setting every P_i=k_i A. This hypothetical master is
used only in the proof. Let δ_h(N) bound the joint replacement of h Gaussian
syndromes of a uniform l×N matrix by independent uniforms, retaining the
matrix and any other independent Gaussian rows.

[SOURCE/DERIVED] The explicit general bound in
../../../adversarial_review/public_setup_pq/quantitative_regularity/BOUND.md
§§2–3 applies. For prime q, let

    ηZ = sqrt(ln(2l(1+1/ε0))/π), t=ηZ/σK<1,
    S_N=(q^N−1) max(q^−1,t)^l,
    R_N=(1+ε0)(1+S_N)−1,
    ρ_N < q^(N−l)/(q−1).

[DERIVED] Then δ_h(N)≤min(1,ρ_N+2h R_N). The proof uses MP2011/501
Lemma2.4 and GPV2007/432 Corollary2.8, retaining all exposed rows through
a common conditional kernel given A. It does not assert prime-field
universality for arbitrary short secrets.

[DERIVED joint statement] Actual (A,P,k_[r]) and hypothetical honest
(A,KA,k_[r]) have statistical distance at most δ_(d−r)(n). Thus this is a
statistical replacement of the honest valid full-vector public-key image,
unlike a primal-Regev switch justified only by computational LWE. The theorem
permits the same negligible setup failure as the comparison, and makes no
pointwise assertion about every public matrix produced by grinding.

## 3. Fixed-coalition confidentiality proof

[DERIVED game] Fix J⊆[r] before setup. Give the adversary (A,P,B,k_J).
It may make at most T classical adaptive pairs (x0,x1) from F_p^d satisfying
Y_J x0=Y_J x1. Return Enc(x_b) for a common hidden bit b. Other public
computations and classical queries may be adaptive; the adversary may retain
quantum state. Compatibility is equivalent to a_J(x0)=a_J(x1) as integers.
The theorem assumes the exact decision-QPT-LWE problem (n,q,σe,l), uniform
secret in F_q^n and independent D_Z,σe errors. The LWE advantage below is
the difference between acceptance probabilities in its two distributions.

[DERIVED advice convention] The adversary and LWE assumption use the same
uniform/nonuniform QPT convention. If polynomial-size quantum advice is
allowed, the LWE premise must cover that same QPT/qpoly class. Advice may
depend on public parameters but is independent of fresh setup randomness
and the challenge bit. No hardness claim against a weaker adversary class
is promoted to the stronger class by this proof.

[DERIVED tail and smudge term] Choose BK,BL with

    τK ≥ Pr[max_(i,j)|K_ij|>BK],
    τe ≥ Pr[max_j|e_j|>BL],
    s = d l BK BL/(2F+1) + τK + τe.

[DERIVED] Conditional on all K,w,e and the classical message, translating
the independent uniform f by Ke changes its joint distribution by at most
Σ_i |(Ke)_i|/(2F+1), capped at one. On the bounded event this is at most
d l BK BL/(2F+1). Thus an honest challenge can change from
(Aw+e, Pw+f+Δa) to (c,Kc+f+Δa), retaining even all K, at cost s.
This is an exact discrete uniform shift estimate, not Gaussian covariance
matching and not an independent-noise claim about Ke.

[DERIVED LWE step] Now c can change from Aw+e to independent uniform u
using ordinary LWE. The reduction samples K independently, sets P=KA,
and computes Kc+f+Δa itself. Its ability to know hypothetical K is normal
simulation knowledge; it is not an actual credential generated in public setup.
It never needs the challenge error e, so there is no multi-hint LWE seam.

[DERIVED mask step] The matrix [A|u] is uniform in F_q^(l×(n+1)). Apply
the joint regularity lemma to all h=d−|J| unexposed rows. This replaces
their pairs (P_i,k_i u) by independent uniform pairs, retaining k_J and
the exposed pairs. The unexposed h_i values are now uniform, even conditional
on public P and any adaptive classical choice of a. Exposed coordinates
have identical a_i by compatibility. The target bit is therefore hidden.
Statistical distance remains valid with the adversary's quantum state as
a common classical-input quantum channel.

[DERIVED multi-query detail] Use the usual T hybrids changing one target
challenge bit at a time. All non-target ciphertexts remain the original public
Enc algorithm, which can be simulated from P without hidden rows. Consequently
one augmented column suffices per target hybrid; the proof does not replace
all T ciphertexts simultaneously while ignoring their common-K correlation.
Earlier transcript, target adaptive messages, and later public encryptions
are the same conditional channel on the tuple used in each hybrid.

[DERIVED conditional theorem] With distinguishing advantage measured as a
difference of acceptance probabilities, the following conservative bound holds:

    Adv_public ≤ 2 δ_(d−r)(n)
               + 2T [ε_QPT-LWE(n,q,σe,l) + s + δ_(d−|J|)(n+1)].

[DERIVED] This proof is straight-line classical sampling and arithmetic
around a QPT adversary, with statistical transitions. It assumes classical
encryption/query interfaces; it does not claim a quantum superposition
encryption oracle. Exact ideal Gaussians are the model. A concrete approximate
sampler contributes its own total variation error and runtime obligation.

## 4. Correctness, full space, and closure

[DERIVED] In the hypothetical full-key comparison, every coordinate phase is
Δ a_i+f_i−k_i e. On the bounded event let E=F+l BK BL. Any scalar combination
of issued ciphertexts with coefficient L1 norm at most W has error ≤WE and
integer encoded coordinate magnitude ≤WX. If

    D ≥ 2WX+1,       Δ>2WE,

then the points {Δt mod q: |t|≤WX} are separated by at least Δ, including
the wrap gap. Nearest-point decoding is unique. Actual issued recipients
satisfy this cancellation algebra exactly, without a setup comparison. The
joint setup theorem additionally justifies the full-state comparison for
missing coordinates, except its bounded statistical discrepancy.

[DERIVED] This encoding is not a bank of selected projection encryptions:
all d centered coordinates of the bijective B transform enter h. Under the
honest comparison every coordinate has a valid Gaussian cancellation key.
The input domain has p^d points. A nonzero vector in ker(Y_J) supplies
distinct ambient admissible challenge inputs. This alone does not prove that
the original learner's semantic encoder image contains such a pair.

[DERIVED] Addition/subtraction of the exact original ciphertext supports
finite windows and exact expiry. Public offsets add Δ times their encoded
integer vector to h only when the total accumulated integer lift in every
coordinate stays within [−WX,WX] and total error stays within [−WE,WE].
An offset is not free merely because it cancels modulo p. Decode the integer
sum before reducing mod p; modular
wrap inside individual a(x) contributes no encryption noise. No arbitrary
matrix transform, fresh re-encryption on expiry, new recipients, nonlinear
learner operation, or unlimited coefficient growth is certified here.

## 5. Public arithmetic witness, not a security level

[EXECUTED] public_arithmetic.py and results.json check the following exact
inequalities without drawing keys/errors/ciphertexts or running an estimator:

    d=577, r=16, p=28,439,893, X=14,219,946, W=32, T=384,
    n=1024, l=16,384, prime q in (2^288,2^289),
    σK=2^32, σe=2^10, F=2^244, BK=8σK, BL=8σe.

[DERIVED] Such a prime exists by Bertrand's theorem; no specific modulus has
been selected or primality-certified for implementation. The exact assumed
LWE problem is parameterized by that selected q. Its noise width is 1,024,
not the flooding bound, Gaussian-key width, or an ALS transformed width.
No computational security bits follow from these numbers.

[DERIVED/EXECUTED] With ε0=2^−192, ηZ<8 and t<2^−29. For N=1024 and 1025,
S_N is below 2^−179200 and 2^−178911 respectively. The general regularity
bound gives δ_h(N)<h·2^−189. The complete regularity contribution is at most
444,258/2^189<2^−170 for the worst fixed coalition J=empty.
The bounded smudging contribution is below 443,136/2^183<2^−164.
The elementary Gaussian tail used in the frozen cost note gives even the
conservative 2T repeated tail charge below 2^−189+2^−220.
Thus the displayed theorem's statistical terms are <2^−163, while its
computational term is 768 times the exact QPT-LWE advantage.

[DERIVED storage event] The 36-bit signed key-coordinate price uses the
strict event |K_ij|<BK=2^35, whose complement is bounded by the computed
Pr[|K_ij|≥8σK] tail. The inclusive bound BK remains a conservative algebraic
overbound in correctness and smudging. An inclusive integer storage interval
[−BK,BK] would need 37 bits and is not the event priced here.

[DERIVED/EXECUTED] The same integer checker verifies correctness on all
F_p^d inputs and all allowed W combinations. The old source Table2 and its
Theorem3 conditions are not premises of this new proof. This is a mathematically
inhabited conditional parameter point, not an implementation clearance.

[OPEN] Independent source/math review, selection and certification of a
specific prime, Gaussian/flood sampler contracts, transcript coverage, actual
LWE hardness evaluation, exact learner integration and semantic nonvacuity
remain before any implementation proposal. No such execution occurred here.

[DERIVED scope reminder] Each recipient can evaluate its permitted coordinate
on every retained issued ciphertext. The fixed-span construction does not
enforce a selected execution trace or make its real read capabilities disappear
on the learner's semantic encoder image.
