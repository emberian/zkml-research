# Independent third review: fixed-coordinate QPT public setup

[DERIVED disposition, 2026-09-08] **Accept the derived fixed-coordinate theorem
and its asymptotic premise witness**, subject to the explicit distribution,
adversary-class and negligible-error conditions below. No counterexample or
source-formula mismatch was found. This acceptance concerns a new restricted
variant proved through ALS Lemmas 3–5 and 10; it does not reduce Theorem 3's
arbitrary-key widths, establish concrete QPT security, or instantiate a resident.
The earlier frozen candidate remains conditional on its source-game premise.

[EXECUTED subjects] The reviewed files are:

| Subject | SHA256 |
| --- | --- |
| `adversarial_review/public_setup_pq/FIXED_COORDINATE_QPT.md` | `4c43bce409495edf9c9d5b8e4ada0581af5be0ecf6ff949fbd99fdbfd3da62fe` |
| `private_construction/public_setup_pq/notes/AUDIT.md` | `2c6f649fa0891be05dd1f3a1f89c935692091195e71f0b1959d78b5ef9061007` |

[SOURCE primary evidence] ALS, *Fully Secure Functional Encryption for Inner
Products, from Standard Assumptions*, local ePrint 2015/608 PDF:
`/Users/ember/dev/gh/forks/IACR-eprint-mirror/2015/608.pdf`, SHA256
`a7d5c231b70961ea59ca544c91b2392fb35c166c88e42b898640cfdc7dbb94d0`.
Read Definition 4 on printed p11, §4.2 algorithms/parameters pp17–18,
Lemma 3 and its proof pp21,34–35, Lemmas 4–5 pp21–22, and Appendix C
Lemmas 6–10 pp33–34. Printed pp21,22,34 were rendered and visually inspected
to check the square-root boundaries and complete reduction interface.
The source's classical statistical sampler lemmas are used as sourced
mathematical results; their referenced lattice-Gaussian machinery is not
reproved or implemented here.

[EXECUTED access] A new `pdftotext -layout` extraction has SHA256
`a1170661edc061a9b011367d43b9b75ed6dfc073cfd0aa477459c20f14d1ecdd`.
Local `rg` found the author note after one initially incorrect path read, and
located the named lemmas in the local text. Network/web/Scry/Kagi queries and
PDF downloads: zero. No search-based field-wide absence claim is made.

## 1. Exact algorithms, all recipient keys, and public transcript

[SOURCE / DERIVED] Set `m=2M`, use `q=p^k` for prime p, and choose τ to be
the first d rows of the independent Gaussian law in ALS Lemma 4. Each left
row is centered with width σ1; each right row has width σ2 and its own
canonical unit-vector center in `Z^M`. Since `d<n≤M`, all those centers exist.
The row law is the product law τ, not the possibly exceptional output of
the reduction's unimodular-completion sampler G. Lemma 5 accounts for the
latter sampler's statistical discrepancy.

[DERIVED] `B∈GL_d(F_p)` is public and fixed before setup, with first r rows
Y. Encode reduces `Bx` in `F_p` before encryption. Thus every coordinate key
is exactly one independent Gaussian row; B does not transform the secret or
error distribution. A completion chosen by a deterministic ordered basis
scan depends only on Y. The arbitrary integer-lift/key-dependence machinery
responsible for Theorem 3's `K'=(sqrt(d)p)^d` is not used.

[DERIVED joint setup proof] For one nonrecipient row split
`Z_i=(L_i,R_i)` and `A=(A_L;A_R)`. Lemma 10 applied to `(A_L,L_i A_L)`
is joint in A_L. Append independent `A_R,R_i` and shift by `R_i A_R`.
Generate all other Gaussian rows, their syndromes, and already replaced
uniform syndromes through one common randomized kernel given A. This
retains every exposed recipient key `Z_[r]` and proves

```text
SD((A,ZA,Z_[r]), (A,U_public,Z_[r])) ≤ (d-r) η0.
```

[DERIVED] This proves the original audit's strongest setup comparison:
all r recipient keys may be exposed together. It then applies to any fixed
coalition `J⊆[r]` by projection. It does not certify independently sampled
unmasked keys `YZ`; the original covariance objection to that different
proposal remains correct.

[DERIVED transcript boundary] The accepted public sampler transcript is
precisely the public matrix A and direct-uniform nonrecipient syndromes.
Appending copies of those entries, B,Y and the existing announcements is
a deterministic operation on the compared views. Neither proof conditions
on a fixed syndrome or an externally selected acceptance event. Conditioning
on an event of probability ρ can require a distance bound of order η/ρ;
the unconditioned lemma cannot be substituted for it. A rejection tape, seed,
timing trace, correlated registration or malicious randomness service needs
a separately specified common conditional kernel or a new theorem.

## 2. The augmented regularity lemma

[DERIVED] In the comparison distribution let `A,v,Z` be independent with
A and v uniform, and put `U=ZA`, `w=Zv`. For each unexposed row the matrix
`H=[A_L|v_L]` is uniform in `Z_q^(M×(n+1))` and independent of L_i.
ALS Lemma 10 therefore applies with column dimension `n+1` provided

```text
M ≥ 2(n+1) log_2 q,
σ1 ≥ c_L sqrt(n+1+log M)
```

[DERIVED] Here and below the positive source constants must actually be
met. The stronger width statement is necessary at the boundary: the earlier
`M≥2n log_2 q` alone does not imply it. The specified Lemma 4 lower bound
on σ1 dominates the augmented Lemma 10 bound asymptotically.

[DERIVED proof] Append independent `(A_R,v_R,R_i)` and add the shift
`(R_i A_R,R_i v_R)`. Each output pair `(U_i,w_i)` becomes uniform jointly.
The other rows and all exposed `Z_J` can be generated through a common
kernel given `(A,v)`, retaining those public inputs throughout. Sequential
replacement yields error `(d-j)η+` for the full tuple `(A,v,Z_J,U,w)`.
No independence of the different row products conditional on a particular
bad matrix is asserted; this is an average joint-distribution statement.
For the whole recipient coalition `J=[r]`, exactly d-r pairs are replaced.

## 3. Challenge simulation and the error-dependence issue

[SOURCE exact input] Definition 4 gives the distinguisher `(A,c,Z,h)` with
`h=Z e0`; in its two ideal distributions, Z, e0, uniform u and A are
independent before the indicated products. It gives the whole Z to the
reduction. The FE adversary receives only its permitted rows `Z_J`.

[DERIVED computational transition] The simulator computes `U=ZA`, runs
the adversary on the setup/key view, receives classical valid `a0,a1`, and
returns

```text
c0=c,   c1=Zc-h+e1+Δ a_b,   Δ=q/p.
```

[DERIVED] In the LWE world this is exactly `c1=Us+e1+Δa_b`. Neither s
nor the unknown e0 is required by the simulation: h is the supplied hint.
The full Z and h remain private simulator variables. In the uniform world,
the challenge is `(u,Z(u-e0)+e1+Δa_b)`.

[DERIVED statistical transition] Only now put `v=u-e0`. Translation by e0
is a bijection, so `(A,v)` is independent uniform and independent of `(Z,e0)`.
In the ideal Definition-4 distribution, e0 is also independent of Z. Apply
the augmented joint lemma before appending the independent e0,e1; then
recover `u=v+e0`. Every missing mask w_i is uniform independently of U,
all other masks and the exposed keys. It hides any adaptively selected
`Δa_b,i+e1_i`. Exposed coordinates have identical challenge messages.

[DERIVED critical distinction] The reduction in source Lemma 5 does use
G-dependent correlated Gaussian operations internally. Its theorem says the
**resulting joint tuple** is statistically close to Definition 4's ideal
tuple. That joint discrepancy must be charged first. One must not assert
that its internal error is already independent of G, condition on h and
then claim Z stays a product Gaussian, or apply regularity to the genuine
LWE c0 before the computational transition. The reviewed proof does none
of these. Nonlinear dependence through the supplied hint is handled by the
sourced full-joint reduction statement, not silently discarded.

[DERIVED adaptive history] Other challenge positions can be encrypted with
public `(A,U)` and fresh private coins. Even when the statistical hybrid has
replaced some U rows, no missing secret is required to simulate those public
encryptions or arbitrary efficient history processing. Each fresh pair must
agree on every row in J. Equality of a final accumulated output alone does
not imply this admissibility condition.

## 4. QPT lift and explicit advantage ledger

[SOURCE] Lemma 3, with t=d and input noise β, maps LWE of dimension n-d
to dimension-n first-d-errorless LWE. Its Appendix D proof samples a public
full-rank prefix, completes it, and maps the remaining samples; it consumes
at most m source samples. Lemma 5 applies when
`β≥c_β sqrt(n)/q` and `ξ≥c_ξ sqrt(nM)σ2`, and outputs mheLWE at noise
`2βξ`. Thus choosing `β=α/(2ξ)` is the correct noise conversion.

[SOURCE / DERIVED] Both transformations are classical randomized sampling
algorithms followed by one invocation of a distinguisher. Lemma 5 samples
G, computes its inverse and correlated noise, prepares a classical tuple,
and returns the oracle's single decision. No step measures an unknown
adversary workspace, extracts its secret, rewinds it, or asks for a copied
state. Their ideal/classical distributional bounds apply unchanged to a
QPT final measurement by trace-distance contraction.

[DERIVED advice qualification] A single independent advice state ρ_n can
be passed once to that QPT adversary and preserved across its adaptive
history. This requires QPT-LWE hardness for the same advice class; uniform
QPT hardness alone is not an assumption about arbitrary QPT/qpoly advice.
Secret-correlated external advice, quantum key/challenge interfaces and
superposition sample access are outside this game. Quantum workspace
generated by processing the classical view is covered. A sequential
ciphertext hybrid needs one adversary run per reduction invocation, not
cloning or restarting its advice. A uniformly selected hybrid position is
also possible by the usual signed telescoping sum.

[DERIVED explicit safe ledger] Use acceptance-probability difference. Let
δ3 bound the per-world statistical discrepancy of Lemma 3; its proof gives
`δ3≤2^(d-n+1)`. Let `δ5=2^-Ω(n)` include all per-world sampler/failure
discrepancies in Lemmas 4–5. A conservative convention-transparent bound is

```text
ε_mhe ≤ ε_LWE + 2δ3 + 2δ5,
Adv_public ≤ 2(d-r)η0
             + 2T[ε_LWE + 2δ3 + 2δ5 + (d-j)η+].
```

[DERIVED] This agrees with the note's `ε_red=O(2^(d-n))+2^-Ω(n)`.
The factor two on each statistical distribution comparison is visible;
the source's guessing-advantage convention cannot silently remove it.
There are two bit-world transitions per selected ciphertext and two setup
comparisons total. Setup error is not charged T times. The old conditional
source-Theorem-3 transfer has a different `T Adv_ALS` computational term;
neither term should be exchanged without its own convention.

[DERIVED nonnegligible-loss boundary] The inequality remains true for d<n,
but a negligible-privacy conclusion additionally needs
`n-d=ω(log n)` and polynomial T (d<n already bounds d). More generally the
displayed full loss must be negligible. The note's witness `d≤n/2` satisfies
this. Mere d<n is not enough to declare its reduction loss negligible.
Actual/approximate Gaussian sampling and extra transcript channels need
their own additive errors; they are not numerical consequences of LWE hardness.

## 5. Correctness, nonvacuity, and parameter feasibility

[DERIVED correctness] For a matching recipient,
`c1_i-Z_i c0=Δa_i+e1_i-Z_i e0 mod q`. On the stated norm event,
`|e1_i-Z_i e0|≤αq t(1+L sqrt(m))`. Integer coefficients with L1 norm W
are therefore safe under `α^-1>2pWt(1+L sqrt(m))`. This deterministic
bound also tolerates adaptive coefficient choices on a simultaneous good
event. Exact subtraction of original ciphertexts cancels their errors.
A polynomial number of product-Gaussian coordinates admits the stated
negligible tails for t=log n and `L=O(σ2 sqrt(m)t+1)`; numerical constants
and a finite tail union budget remain to be selected for an implementation.
Residue correctness, centered integer no-wrap and general matrix-update
closure are separate; the original audit correctly distinguishes them.

[DERIVED asymptotic check] For the proposed family the required orders are:

| Requirement | Required order | Chosen value |
| --- | --- | --- |
| σ1 from Lemma 4 | `n log n` | `n^2` |
| σ2 from Lemma 4 | `n^7 log^2 n` | `n^8` |
| ξ from Lemma 5 | `n^9 sqrt(log n)` | `n^10` |
| βq lower bound | `sqrt(n)` | between `(1/2)n^5` and `n^5` |
| Aggregate relative error | tends to zero | `O(n^-4 log^3 n)` |

[DERIVED] Take C sufficiently large for `M=Cn ceil(log_2 n)`, notably its
augmented width and `M≥c_2 n log(σ1n)` constraints, then take n sufficiently
large for the remaining fixed source constants. The listed inequalities
are simultaneously satisfiable; q is a valid power of prime p=2 and the
LWE dimension is at least n/2. This is an existence witness, not an
identified finite secure parameter set: the source's hidden constants,
finite Gaussian sampling/tail budget, precise adversary resources and the
specific small-noise QPT-LWE hypothesis still need concrete values.

[DERIVED nonvacuity] For `d=3,r=2`, use
`Y=[1 0 1;0 1 1]`, `B=[1 0 1;0 1 1;0 0 1]`, and `h=(-1,-1,1)`.
Then det B=1, Yh=0 and Bh=e3 over every prime field, including p=2.
Thus even the whole recipient coalition has distinct full-domain states
with equal outputs and changing third coordinate. On the restricted image
`X={(x1,x2,0)}`, Y is injective. A claimed application must exhibit a pair
in its actual image; full-domain nonvacuity alone does not supply it.

## 6. Executed controls and completion

[EXECUTED] `check.py` runs only public mathematical controls. It checks the
four subject/source/extract pins; exhaustively evaluates a small uniform-row
analogue of the joint/shift/exposed-row argument over fields 2 and 3; checks
160 full-coalition nonvacuity pairs and 38 injective-image points; and verifies
explicit inequality ratios at `n=2^16,2^32,2^64`, C=128 with unit source
constants. The exact ratios are retained in `results.json`. Those points
are conditional arithmetic controls, not concrete security parameters.
The finite distribution analogue is not a proof of Gaussian Lemma 10.

```text
python3 research/learn_infer_only/experiments/adversarial_review/fixed_coordinate_qpt/check.py > research/learn_infer_only/experiments/adversarial_review/fixed_coordinate_qpt/stdout.txt 2> research/learn_infer_only/experiments/adversarial_review/fixed_coordinate_qpt/stderr.txt
```

[EXECUTED] Exit 0; stderr empty. All author/source files remain unchanged.
No keys, ciphertexts, Gaussian samples, private files, runtime crypto,
protocol controls, stopped-task artifacts or network tools were used.
The final manifest pins this report and retained controls; extract/render
hashes and visual access are retained separately without adding PDF bytes.

[OPEN next] A concrete use must fix the QPT/advice class and resource bound,
source constants and sampler precision, total transcript, complete tail/union
budget, finite p/q/n/d/m parameters, and an application-image witness.
No repair to either frozen note is required for the bounded theorem itself;
the loss/advice qualifications above should accompany future summaries.
Parent owns shared ledgers, integration and commits.
