# Finite coherent oracle wrapper and exact oracle removal

[DERIVED construction, 2026-09-08] The finite programmed chunk table admits
an efficient coherent oracle wrapper. A phase-kickback implementation uses
**one** fallback-oracle query per exposed query, with no measurement of its
address or prefix-length registers. For a declared bound of Q such queries
and c additional classical fallback evaluations, a `(2Q+c)`-wise independent
fallback removes the external ideal oracle exactly. This is a polynomial
time reduction under the finite bounds and advice conditions below; it is
not a practical quantum circuit or a concrete SHAKE256 security theorem.

## 1. Finite function and prefix model

[DERIVED] Fix polynomial bounds D on input **bytes** and L on requested
output **bits**, with L at least the chunk length 303,104 bits. The domain
contains every byte string of length at most D, including strings that do
not parse as our protocol. Encode it injectively into
`d=8D+ceil(log2(D+1))` bits using a length tag and zero-padded bytes. Invalid
register encodings or out-of-bound length requests have one specified
deterministic zero answer in every compared game. Bounds apply to the
complete reduction, including preprocessing and honest evaluations.

[DERIVED] Let `F:{0,1}^d -> {0,1}^L` be the residual function. A finite
classical table contains at most B distinct canonical addresses, each with
a programmed prefix `(a_j,t_j,p_j)`, where `p_j<=L`; the actual chunk
entries have `p_j=303104`. Repeated programming replaces the prior entry
at that address. Define

```
H_T(x)[i] = t_j[i]    if x=a_j and i<p_j,
           F(x)[i]   otherwise.
```

For a request length ell, the oracle is
`|x,ell,y> -> |x,ell,y XOR P_ell(H_T(x))>`, where `P_ell` retains positions
below ell and zeros the rest of the L-bit answer register. Request length
is **not** part of F's input: shorter and longer requests share the same
stream prefix. Beyond a programmed chunk prefix, F supplies the consistent
residual tail. Entire unused capped chunks remain table entries when the
kernel supplies them; indices outside that programmed set use F.

[DERIVED scope] L is a declared upper bound, not an infinite XOF output.
If the adversary can request longer strings, the proof must enlarge L and
its resource counts. The frozen serialization's largest q289 address is
466 bytes at a 64-byte seed and a 255-byte family; this is an honest-format
maximum, **not** permission to restrict adversarial queries to 466 bytes.

## 2. One-query coherent circuit

[DERIVED] For a fixed table T, validity/prefix flags and equality tests are
reversible Boolean computations. Put the caller's answer register into the
binary Fourier basis by applying `H^L`; call its basis label z. Define the
coherent fallback label

```
a_i(x,ell,z) = z_i * 1[valid request and i<ell]
                    * 1[bit i is not covered by an overlay at x].
```

Execute the following operations without measuring x, ell or z:

1. Reversibly compute a into an initially zero L-bit ancillary register.
2. Apply `H^L` to that ancillary register, giving the Fourier character
   `|chi_a> = 2^(-L/2) sum_w (-1)^(a dot w)|w>`.
3. Make one ordinary XOR query to F with x and this ancillary register.
4. Apply `H^L` again and reverse the label computation, returning the
   ancillary register exactly to zero.
5. Apply the known table phase
   `(-1)^(sum_(j:x=a_j) sum_(i<min(ell,p_j)) z_i*t_j[i])`, controlled on
   request validity. Uncompute all lookup/prefix scratch registers.
6. Apply `H^L` to the caller's answer register again.

[DERIVED verification] XOR by F(x) has `|chi_a>` as an eigenvector with
eigenvalue `(-1)^(a dot F(x))`. Thus steps 1–4 clear the ancillary register
and contribute precisely the requested, **unoverlaid** fallback bits.
Step 5 contributes precisely the programmed bits. The total phase is
`(-1)^(z dot P_ell(H_T(x)))`; conjugating by the two caller Hadamard layers
implements the desired XOR oracle. This basis-wise identity extends by
linearity to arbitrary superpositions and entanglement. A zero label gives
`|+>^L`, so ignored bits cause no phase, even though the full fallback query
is made. No quantum query is treated as a classical cache lookup.

[EXECUTED symbolic controls] `PHASE_CHECKS.json` records 4,096 exact
four-bit XOR-character identities and 5,120 prefix/overlay phase identities,
including cleared ancillary labels. Omitting the fallback exclusion mask
gives 736 counterexamples. These are deterministic GF(2) parity checks;
no quantum state, random process or physical circuit was simulated.

[DERIVED] The same argument routes a requested chunk's Fourier-label bits
into their positions in a giant block register, leaving every other label
zero. One giant-block XOR query suffices for that selected chunk/prefix.
This saves a factor of two in **oracle-query accounting**, not all gate
work: compiling a function XOR oracle still requires internal reversible
compute/use/uncompute arithmetic.

## 3. Exact finite-independence replacement

[SOURCE: theorem and construction] Zhandry, eprint 2012/076, Theorem 3.1
(PDF p.6; local extract lines 250–257), proves that q-query quantum output
probabilities depend only on the oracle's 2q-point marginals. Its Theorem
6.1 and Section 6 (PDF p.13; lines 626–657) explicitly construct an efficient
oracle-free simulator using finite independence. [Primary paper](https://eprint.iacr.org/2012/076).

[SOURCE: mixed-query density-matrix proof] Boneh–Zhandry, eprint 2012/606,
Lemma 6.4 (PDF pp.23–24; local extract lines 1260–1336), extends this to
`c+2q` independence for c classical and q quantum queries, proving equality
of the averaged final density matrices. [Primary paper](https://eprint.iacr.org/2012/606).

[DERIVED application] Treat the **whole** reduction, including its table
construction, preprocessing, adaptive classical interactions, and the
adversary, as the algorithm with access to the base F. The phase circuit
makes at most Q quantum F calls. Count every other honest/base evaluation
in c; choosing `k=2Q+c` gives identical final quantum states for uniform F
and a k-wise independent F. A looser alternative is twice the total number
of all base evaluations. The parent's current construction generates its
overlay tables from supplied targets and fresh independent finite coins,
and honest Expand reads those overlays, so it declares c=0 and k=2Q.
If its implementation changes, recount c rather than retain that shortcut.

[DERIVED] Sample the finite function at the beginning of the entire oracle
interaction. Do not first expose an ideal oracle, inherit oracle-dependent
quantum advice, and then independently replace it. Fixed quantum advice may
be passed once to the adversary and may be entangled with a reference, but
must be independent of the fresh fallback coefficients. Any earlier
oracle-dependent preprocessing must occur inside the counted interaction.
External Ring-LWE challenge data can be fixed before the lemma is applied,
then averaged over, provided the simulator's fresh function coins are
independent of that challenge and initial advice.

## 4. Explicit finite family and its cost

[DERIVED] If Q=c=0, no fallback needs instantiation. Otherwise k>=1; let m
be a power of two at least `max(d,ceil(log2 k),1)`. Include a fixed public
monic irreducible polynomial of degree m over GF(2) in the
simulation parameters. View d-bit inputs injectively as field elements.
For `s=ceil(L/m)` independent lanes, sample k uniform field coefficients
and form degree-at-most-`k-1` polynomials `P_1,...,P_s`. Define F(x) as the
first L bits of their concatenated m-bit evaluations. Vandermonde
invertibility at distinct inputs gives k-wise independent uniform field
outputs in each lane; independent lanes and final truncation give exactly
k-wise independent uniform L-bit outputs.

[DERIVED bounded setup] Coefficient randomness is exactly `k*s*m` bits.
The irreducible modulus is **not** found by an unbounded random search.
It is fixed public classical advice depending only on the security
parameter and declared bounds. For power-of-two m>1, its irreducibility can
be checked deterministically by the standard criterion
`X^(2^m)=X mod f` and `gcd(X^(2^(m/2))-X,f)=1`; repeated squaring and the
Euclidean algorithm give polynomial verification. The source papers supply
the finite-field/Vandermonde construction; no particular modulus is
instantiated or tested in this task. The final Ring-LWE assumption must
allow the same nonuniform advice class. A strictly uniform version needs
its own bounded field-construction argument; it is not silently asserted.

[DERIVED coherent cost] Schoolbook arithmetic in the fixed polynomial basis
uses `O(m^2)` Boolean gates per field product. Horner evaluation uses
`s*(k-1)` field multiplications. Reversible compute/use/uncompute supplies
the XOR-F oracle with two arithmetic passes and clean scratch. A direct
reversible linear scan of B entries costs
`O(B*(d+L_chunk))` gates; it needs no assumed quantum RAM. Prefix-mask
generation can be bounded by `O(L log L)` gates. Therefore a conservative
per-exposed-query gate order is

```
O( ceil(L/m)*k*m^2 + B*(d+L_chunk) + L*log L ).
```

The independent-polynomial coefficients occupy `k*s*m` bits; the table
occupies `B*(d+L_chunk)` bits up to record overhead. A straightforward
reversible implementation uses polynomial additional workspace for Horner
intermediates, labels and prefix flags. This proves polynomial cost when
the declared bounds are polynomial; it does not make the concrete circuit
small or preserve the adversary's original running-time budget unchanged.

[EXECUTED arithmetic] With 64 A rows, 561 missing rows and 80 capped chunks
per row, B=50,000. Programmed values alone occupy **1,894,400,000 bytes**.
At an illustrative D=466 bytes and L=303104 bits, d=3737; choosing m=4096
and k<=2^4096 gives s=74. With c=0, the fallback coefficient seed occupies
`75,776*Q` bytes, and compute/uncompute performs `148*(k-1)` field
multiplications per exposed query. These are deterministic counts, not a
quantum benchmark; all dependence on Q remains explicit in `COUNTS.json`.

## 5. Correlated hybrid tables are common channels

[DERIVED] For fixed classical table data and fallback coefficients, the
wrapper is an efficiently specified unitary query map. Sampling the
table from input targets and coins, updating it at classical events, and
running the adversary gives a common quantum channel. Consequently trace
distance cannot increase when the same wrapper/channel is applied to two
already-close joint input distributions. A computational hybrid can likewise
embed its challenge into this explicit simulator, subject to its running
time and advice bounds.

[DERIVED limitation] None of this asserts that an **arbitrary correlated
programmed table** is a random oracle. Only the independent fallback F is
removed by the finite-independence lemma. Whether endpoint tables are
marginally uniform, how they correlate with registered keys and A, and
whether changing them is justified require the parent's kernel/regularity
and reprogramming arguments. The common channel remains meaningful in
intermediate hybrids even when that table is not random-oracle distributed.

## 6. Separate information-theoretic source helpers

[SOURCE: supplied GHM paper] GHM 2020/1361, Theorem 1, Proposition 1 and
Appendix A concern finite-domain/output reprogramming at a newly sampled
uniform value and give information-theoretic query bounds. Appendix A
explicitly implements later programming using an overriding list. They
do not directly license arbitrary target-correlated replacements.

[DERIVED source-interface refinement] The parent can use separate independent
giant helpers `G_A(seed,binding)` and `G_M(seed,binding)`. Their values pack
all capped chunks of 64 A rows and 561 missing rows respectively. No padding
of A to the missing-family size is required. In an information-theoretic
application to one target helper, fix/average the other independent helper
as part of the unbounded distinguisher's inter-query computation. One ordinary
H query uses at most one phase-routed query to each target helper, and only
queries to the helper currently being reprogrammed enter that source bound.

[DERIVED conditional count] Under the parent's stated chronology, the
pre-reprogramming counts are `qhat_A=Q_before_A` and
`qhat_M=Q_before_M`. An honest A-table read queries G_A, not G_M, so there
is no extra `+1` in the missing-helper count. This requires that no other
honest step actually queried the old G_M and that the family/profile
namespaces are disjoint. The parent's endpoint hybrid must still establish
the freshly uniform replacement and fresh-seed position premises.

[EXECUTED arithmetic] The giant G_A output/label has 1,551,892,480 bits;
G_M has **13,603,307,520 bits**. These helpers serve the source-bound argument.
The eventual efficient Ring-LWE reduction uses the ordinary-address finite
function and explicit table above; it need not evaluate either giant helper
in each query. The information-theoretic source application does not hide
an external ideal oracle inside that final computational reduction.

[OPEN] Parent must finish the full namespace block-reprogramming and joint
FE/Ring-LWE hybrid proof and charge this simulator's gate/time overhead at
the claimed hardness resources. No quantum circuit, crypto execution,
estimator or random simulation was run here. No security statement about
concrete SHAKE256 follows just from replacing the ideal fallback internally.
