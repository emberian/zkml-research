# Compact public-setup IPFE alternatives

[DERIVED outcome, 2026-09-08] The strongest new primary source is
Han–Yi–Liu–Gu (HYL), ePrint 2025/1613. Its single-block Gaussian-syndrome
algebra supports a concrete absent-master setup comparison and full-vector
encoding. Its published general-function parameter table does not give a
small finite replacement for the frozen ALS example: a source theorem's
matrix-height premise fails at small table substitutions. A separate
fixed-coordinate smudging proof, in SMUDGED_FIXED_COORDINATE.md, avoids that
premise and gives a substantially smaller conditional arithmetic point.
Neither point is a concrete security-level claim or implementation approval.

[EXECUTED scope] Only source discovery, local PDF extraction/rendering,
public integer inequalities and hashing were performed. No keys, ciphertexts,
Gaussian/flood samples, estimator, protocol runtime, attack, or disclosure
experiment was run. Earlier frozen files are unchanged. Search counts and
source pins are in SOURCES.md and MANIFEST.json.

## 1. HYL's actual construction and game

[SOURCE] 2025/1613 Def.1 p17 permits all bounded integer vectors
x,y∈Z^d with ||x||∞≤X and ||y||∞≤Y. Def.2/Fig.1 p18 gives classical
multi-challenge IND security with adaptively queried functional keys and
the exact compatibility condition <x0,y>=<x1,y>. This is numeric IPFE, not
an inner-product-zero predicate. It is not a registered-key or absent-master
game, and the stated adversary definition is PPT rather than an explicit
QPT formalization.

[SOURCE] Rename the paper's message dimension m to d, LWE sample height l
to l, and block count to t=ceil(d/L). Fig.6 p28 samples independent
K_b←D_(Z^(d×l),σK), publishes A←F_q^(l×n), P_b=K_b A, and retains all K_b.
KeyGen(y) returns (y^T K_1,...,y^T K_t,y), with products represented mod q.
Encrypt(x) samples independent w_b∈F_q^n, e_b←D_(Z^l,σL), and uniform
f_b∈[−F,F]^d, then outputs

    c_b=Aw_b+e_b,    h=Σ_b(P_b w_b+f_b)+floor(q/(dXY)) x  mod q.

[DERIVED] Choosing L=d gives t=1, still a full d-vector encryption. The
source's security-loss expression becomes d(8cn+1) times its ordinary LWE
advantage plus its stated statistical loss; choosing one block does not keep
the loss claimed for a constant L=5 or L=100. The source allows L∈N; for
the fixed d=577 fixture this is a fixed finite choice. When d varies, this
factor must be included in the asymptotic analysis.

[DERIVED credentials] For fixed coordinate keys, recipient i needs row i
of each K_b. Those independent Gaussian rows can be sampled locally by the
recipients, with each P_(b,i) published. Publicly generated uniform rows for
i>r require a joint Gaussian-syndrome regularity bound to match the honest
game. A computational LWE slogan is unnecessary here: P is a Gaussian
syndrome, precisely the structural feature that made the ALS setup work.
The complete master {K_b} never needs to be generated in this transformation.

[DERIVED source-game qualification] Fig.6's coordinate key is K_i mod q,
whereas a recipient knows its integer Gaussian row and its local sampling
history. Recovering the integer row from the residue uses the event
||K_i||∞<q/2 and centered lifting; its tail must be included in a reduction
to the source game. The direct restricted proof explicitly exposes integer
rows and therefore does not rely on this key-format shortcut. Raw sampler
logs need a separate output-conditional simulation argument.

## 2. Full input space and the printed decoder seam

[SOURCE] Fig.6 p28, visually inspected, prints Δ=floor(q/(dXY)), a phase
in Z_q, and a minimization over integers in [−dXY,dXY]. Def.1 p17 promises
all signed bounded integer inner products. The page does not specify whether
the phase absolute value uses a centered representative or circular distance.

[DERIVED scoped concern] Even under circular distance, the generic range
contains roughly twice as many Δ-spaced points as the circle accommodates
without near collisions. Writing R=dXY and q=RΔ+s, 0≤s<R, the encodings of
0 and R are separated modulo q by at most s<R, not by Δ. Thus the printed
condition E≤Δ/4 alone does not prove unique generic decoding when Δ≫R.
This is a scope-limited printed-decoder/correctness issue. It is not a claim
to have refuted the paper's IND statement, whose game does not call Dec.
No source-wide repair is silently assumed.

[DERIVED restricted resolution] For the original fixed-coordinate task set
p=28,439,893, X=(p−1)/2=14,219,946, and the HYL scalar key bound Y=1.
Use a(x)=center_p(Bx) for every x∈F_p^577, where B's first 16 rows are the
original policies and its remaining rows are the existing identity completion.
This is a bijection onto [−X,X]^577, so the entire F_p^577 input space is
represented, including the 561 unselected coordinates. No full-vector input
coordinate is discarded or replaced by a selected-projection bank.

[SOURCE/EXECUTED] The frozen public fixture calculation in costs/FEASIBILITY.md
gives B invertible modulo p, maximum policy-row L1 norm 3,499, individual raw
coordinates in [−127,127], and W=32. Hence individual policy-coordinate
integer magnitudes are ≤444,373 and original window scores ≤14,219,936.
The bijective full-space bound X is ten larger than that window bound.

[DERIVED] A recipient for e_i returns center_p((Bx)_i), then reduces mod p.
Coalition compatibility over F_p is exactly equality of these exposed centered
integers, so it maps to the source fixed-coordinate compatibility. At most W
arbitrary full-space centered inputs have coordinate sum bounded by
WX=455,038,272. Since D=dX=8,204,908,842>2WX, using the printed Δ with a
new explicitly restricted decoder over [−WX,WX] avoids its generic endpoint
seam. The separate note proves spacing, noise and modulo-p recovery directly.

[DERIVED] Prime-q scaling is not an F_p-module homomorphism: generally
Δp≠0 mod q. Addition and exact subtraction work on accumulated integer
centered lifts, followed by modulo-p decoding. Public offsets must respect
the same accumulated integer interval and noise budget; modular cancellation
alone does not justify unlimited offsets. Arbitrary matrix state evolution,
key switching and nonlinear closure remain unproved.

## 3. Published general-function costs

[SOURCE] HYL Theorem3 p27 requires l′≥2n log_2 q and
σK≥sqrt(d) X l′. Theorems2 and 4 add separate reductions/entropy premises,
including equation (8) and l≥(l−l′+1)log q+2λ. Corollary1 p29 requires all
of these plus negligible ε_pp in equation (7). It is not enough to inspect
Fig.6 dimensions or the abstract's compactness claim.

[SOURCE] Table2 p29 (visually checked) suggests the asymptotic family

    n=11λ, q≈2^(7sqrt(λ)), l=λ², l′=λ²−2λ,
    σL=λ^(5/2) 2^sqrt(λ), σK=2^(3sqrt(λ)),
    σs=2^(1.5sqrt(λ)), σLWE=λ, F=2^(6sqrt(λ)), c=2λ.

[SOURCE] Page29 expressly attributes its super-polynomial modulus to
noise smudging. Equation(7) includes l BK BL/F and (l−l′) Bs/σK as
statistical errors; they are not identically zero. The global reduction
constant C in Theorem2 is another finite obligation. Table2 is not a
numerical 128-bit security prescription.

[DERIVED] Ignoring rounding, Theorem3's height condition requires
λ−2≥154sqrt(λ) for this particular family. Small substitutions fail the
premise even before security estimation. For exact arithmetic use square
λ=s² and an unspecified prime in (2^(7s),2^(7s+1)); Bertrand guarantees
existence and the extra bit supplies conservative storage bounds.

| [EXECUTED] source table substitution | λ=256 | λ=1,024 | λ=24,025 |
|---|---:|---:|---:|
| n | 2,816 | 11,264 | 264,275 |
| l | 65,536 | 1,048,576 | 577,200,625 |
| l′ | 65,024 | 1,046,528 | 577,152,575 |
| lower required 2n log q | 630,784 | 5,046,272 | 573,476,750 |
| height premise | fails | fails | sufficient upper-bound check passes |
| one-block ciphertext bytes, upper bound | 933,847 | 29,507,429 | 78,355,063,172 |
| public-key bytes, upper bound | 2,629,710,688 | 332,371,670,400 | 20,707,284,319,648,163 |

[DERIVED] The last column checks only the displayed height premise, not
every theorem premise, finite reduction loss, computational hardness, or
decoder correctness. It is an explicit bottleneck in this source family,
not a lower bound on lattice IPFE or on all HYL parameter choices.

## 4. A narrower derived improvement

[DERIVED] SMUDGED_FIXED_COORDINATE.md supplies a complete conditional
game/proof using the one-block public encryption algebra, independent
recipient Gaussian rows, uniform missing syndromes, and the exact interval-TV
smudging bound. It changes one target challenge at a time to a private
evaluation, applies ordinary QPT-LWE, and then masks unexposed coordinates
using [A|u]. It does not use HYL's arbitrary functional-query kernel lemma,
its l′ requirement, its tight multi-secret LWE conversion, or ALS's hinted-LWE
gadget. No source theorem is being applied outside its premises.

[DERIVED/EXECUTED] Its arithmetic witness uses n=1,024, l=16,384,
q any prime in (2^288,2^289), σK=2^32, σe=2^10, uniform flood radius 2^244.
For T=384, the proved statistical terms are <2^−163, plus
768·Adv_QPT-LWE(1024,q,D_Z,1024,16384). This exact LWE assumption is not
evaluated by the note and cannot inherit a security level from n, the modulus,
the small statistical term, or a classical estimator for another scheme.

| [EXECUTED] conditional arithmetic cost | new smudged row | frozen restricted ALS n=1024 row |
|---|---:|---:|
| ciphertext bytes | ≤612,717 | 84,433,593 |
| public-key bytes | ≤627,421,312 | 86,459,998,464 |
| recipient key bytes on stated Gaussian tail event | 73,728 | 14,548,992 |
| modular products per encoding | 17,368,064 | 2,148,074,496 |
| modular products per coordinate decryption | 16,384 | 2,097,152 |
| live 66 ciphertext bytes | ≤40,439,322 | 5,572,617,138 |
| all 384 issued ciphertext bytes | ≤235,283,328 | 32,422,499,712 |

[DERIVED] Storage is bit-packed arithmetic excluding metadata and B's
already costed 9,232-byte policy matrix. The new prime has only an interval
existence proof, hence the byte upper bounds. Gaussian keys have unbounded
support; the fixed byte size is conditional on the separately bounded tail.
Matrix products count scalar modular products, not wall-clock time. The old
and new rows assume different exact LWE problems and have different reduction
obligations. These figures compare conditional arithmetic, not equal security.

## 5. Two adjacent candidates and their seams

[SOURCE] Abdalla–Bourse–DeCaro–Pointcheval, 2015/017, Construction4.1
pp9–10 and §6.2 pp22–24, has a primal-Regev instantiation. Setup samples
s_i∈F_q^n, small e_i∈Z^m, and p_i=As_i+e_i for each input coordinate.
Encrypt shares r∈{0,1}^m and returns c0=A^T r and
c_i=<p_i,r>+floor(q/p)x_i. Key_i=s_i, with general functional keys
Σ_i y_i s_i. Ciphertext size is n+d residues, recipient key n residues,
and public key m(n+d) residues. Its source input/key alphabet is bounded
nonnegative integers; it does not directly promise all F_p^d inputs.

[DERIVED scoped obstruction] Independent recipients can produce their own
(s_i,e_i,p_i), but absent p_i sampled uniformly match honest setup only by
a computational LWE switch in this syntax. In a parameter regime where
honest errors lie in [−E,E]^m except probability τ, the bounded-error key
image has at most q^n(2E+1)^m points for each fixed A. Therefore its statistical
distance from a uniform public row is at least

    1−τ−q^(n−m)(2E+1)^m,

whenever that lower bound is positive. Such uniform rows need not represent
the source's valid small-error public-key image. This is the precise reason
that the compact primal ciphertext does not automatically repair the requested
honest absent-master/full-state setup. A different oblivious valid-key
generation theorem could change the conclusion; it was not found in this
bounded source read. Generating and then erasing every absent secret violates
the requested no-generation lifecycle.

[SOURCE triage, not accepted construction] Roy–Dutta 2025/2232 Algorithms
23–26 pp28–29 uses a full Gaussian Z, W=AZ, and random-oracle index columns
u_i∈{−1,1}^lmax. A coordinate key is Z u_i rather than an independently
sampled row. Encryption still has an m-residue common component, and its
parameters retain m≥2n log q. Algorithm23 generates the entire Z master;
the earlier Algorithm5 generates a trapdoor T. The numerical n=5 timing
caption p8 is an implementation report, not evidence of cryptographic
hardness at this task's exact problem.

[DERIVED triage] Independently choosing coordinate keys would need the
joint law of ZU, whose columns share Z and are generally correlated; replacing
it by independent Gaussian recipient rows does not follow from that source.
Programming the RO to coordinate unit vectors also changes the stated
distribution. This source therefore does not provide a direct cost repair
for this lane. No implementation or security claim from it was reproduced.

## 6. Status and next boundary

[OPEN] Independent review of the derived proof is the next gate. If accepted,
the meaningful next non-cryptographic work is exact prime selection and
finite sampler/transcript specification, then analysis of the exact LWE
assumption. The source audit has not authorized or begun crypto execution.
Semantic encoder-image nonvacuity, full learner closure and the stopped
receipt/routing experiments remain separate. The bounded search does not
establish absence of better constructions beyond the named corpus/instrument.
