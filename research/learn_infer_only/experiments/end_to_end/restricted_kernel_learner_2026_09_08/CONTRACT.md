# Fixed quadratic kernel, continuing encrypted sums

[DERIVED] This construction changes the plaintext feature representation and the
registered query policies. It uses the predecessor's unmodified ideal-uniform
ring FE transport, not ciphertext multiplication or a new FE assumption. The
trusted issuer sees each plaintext source vector and computes its degree-two
lift. Each independently generated recipient key yields one fixed nonlinear
kernel score on any issued input or supported linear state.

## Fixed map and exact identity

[EXECUTED] The map was fixed in `kernel.py` and sent to the parent before the
sole evaluation in `prepare.log`. For the existing final-zero 577-coordinate
signed-int8 vector v, set

    z_i = Σ_{j=0}^{575} s_ij v_j,      0 ≤ i < 32,
    s_ij = +1 iff bit0(SHA256(domain || BE16(i) || BE16(j))[0]) = 1,
    domain = ASCII("restricted-kernel-learner-2026-09-08/map-v1/").

If M=max_i |z_i| is zero, set x=0. Otherwise set

    x_i = sign(z_i) floor(4 |z_i| / M + 1/2).

Ties are away from zero; the code uses exact integer division. Every coordinate
is in [-4,4]. This deterministic public feature-map hash is unrelated to public
matrix sampling or secret encryption coins. It supplies no security assumption.

[DERIVED] Order pairs (i,j), 0≤i≤j<32, lexicographically. There are
32·33/2=528 pairs. Define issuer coordinates φ(x)_ij=x_i x_j and query
coefficients ψ(q)_ii=q_i², ψ(q)_ij=2q_iq_j for i<j. Append 49 zero coordinates
to both vectors. Then over the integers:

    <φ(x),ψ(q)> = Σ_i x_i²q_i² + 2Σ_{i<j}x_ix_jq_iq_j
                = (Σ_i x_iq_i)².

The identity follows by partitioning the ordered cross terms of the square into
diagonal terms and pairs (i,j)/(j,i). The bound |x_i|,|q_i|≤4 implies
|φ_i|≤16 and |ψ_i|≤32, so both are within the predecessor's signed-int8 input
and query-row checks, with final coordinate zero. The diagonal value 16 and
off-diagonal query value 32 are inclusive.

## Actual class-state transition

[DERIVED] For class c, retain a public FIFO queue Q_c of at most two original
ciphertexts. A trusted plaintext issuer computes x=compact(v), φ(x), then invokes
public `encode` with the canonical field residues of φ(x). The public host
computes C'_c=C_c+C_new, or C'_c=C_c+C_new−C_old when Q_c is full. The other
class remains unchanged. The original ciphertext digest identifies expiry;
the unchanged `window` command checks it is a live original ciphertext.

For query q_j, the recipient output is

    S_c(q_j) = Σ_{x∈Q_c} (x·q_j)².

The application compares S_c(q_j)/|Q_c| exactly using rational arithmetic,
with a fixed alphabetical tie break. All three tested checkpoints have equal
class counts. Expiry cancels the exact stored ciphertext, including its noise;
the supported state is a linear sum of the live fresh ciphertexts. Continuing
updates may repeat indefinitely with bounded live weight, subject to the
predecessor's finite workload correctness and privacy accounting; a single
finite run does not certify an unbounded cryptographic lifetime.

[DERIVED] For any bounded compact vectors, |x·q|≤32·16=512, hence one
kernel score is in [0,262144]. A positive two-item sum is at most 524288. More
generally, integer ciphertext coefficients a_t with Σ|a_t|≤32 give

    |Σ_t a_t (x_t·q)²| ≤ 8388608 < floor(p/2)=14219946,
    p=28439893.

Thus all supported integer kernel outputs have unique centered field lifts.
The remaining basis coordinates are individual lift coordinates bounded by 16;
their weight-32 combinations are bounded by 512. No modular wrap is needed in
these basis coordinates either. This is a domain-specific kernel bound; it does
not extend the general signed-int8 predecessor's application contract.

## Setup and surviving credentials

[SOURCE/EXECUTED] `basis.py` is copied unchanged from
`../restricted_query_learner_2026_09_08/basis.py`. It places the actual 16 rows
ψ(q_j) first, then adds identity rows at ascending nonpivot columns. The fixed
registry has row rank16 modulo p; `PREPARATION.json` records six exact forward
and inverse basis checks. Therefore B is invertible on F_p^577. This is an
ambient algebraic statement, not evidence of ambiguity on the compact quadratic
image or natural-language source domain.

[SOURCE] The unchanged `transport.py`, `source/fast/` and `codec/` implement
the predecessor's strict RINGSEM1 registry/setup/parameter/header binding. The
full ideal-uniform profile is N=16384, w=64, d=577, r=16,
q=4294967767·2^256+1, σ_key=2^25, σ_error=2^10, F=2^247, W=32,
D=8204908842, Δ=floor(q/D). The exact parameter and correctness values are
pinned in `SOURCE_PINS.json`. Each registered recipient generates its one row;
the 561 missing public rows are sampled directly and uniformly, with no missing
secret row generated. Public A is sampled with the unmodified ideal-uniform
law. All registration and encryption distributions remain unchanged.

[DERIVED] A fresh registry means a fresh setup and fresh recipient keys; none of
the predecessor's keys or ciphertexts may be reused. The surviving state is
public A, public row products, the registry and ciphertexts, plus the sixteen
individual recipient rows held by their respective recipients. There is no
master issuer or universal reader in this construction. The trusted plaintext
issuer requires public encryption data, not a secret encryption master.

## Precisely conditional claim and limits

[DERIVED] Assume the exact existing ideal-uniform fixed-coordinate transport
privacy/correctness theorem and its stated honest registration, sampler,
parameter, exposure, workload and computational assumptions. Pull its message
game back through the public deterministic map v↦φ(compact(v)) and the fixed
invertible B. A coalition J's compatibility condition is equality of
(compact(v)·q_j)² for every j∈J on every challenged input. A simulator computes
the public feature map and uses these vectors as transport messages; deterministic
postprocessing does not enlarge the transport distinguishing advantage.
The same reduction carries supported public linear states, and the exact
identity/range argument above supplies their integer kernel semantics. This
adds no security claim beyond the predecessor and its explicitly conditional
hardness premise.

[SOURCE/DERIVED] The exact underlying statement is
`../../private_construction/public_setup_pq/ring_candidate/CANDIDATE.md` §3:
for a fixed coalition J, at most T adaptive classical challenge pairs, and
difference-of-acceptance-probabilities advantage,

    Adv ≤ 2δ_(d−r)(1) + 2T[ε_RLWE + S + δ_(d−|J|)(2)].

Here the source defines δ as joint ring regularity, S as scalar flooding plus
coefficient tails, and ε_RLWE for its exact uniform-secret coefficient-error
Ring-LWE tuple and matched QPT advice class. The deterministic kernel adapter
preserves this bound for valid image-domain challenge pairs. The source is a
locally derived conditional theorem, not the source paper's full adaptive-key
theorem. `ring_candidate/hardness/AUDIT.md` §§3–4 gives the N16384 coupled
parameter extension and explicitly distinguishes its generic lattice proxy
estimates from Ring-LWE hardness certification. `ring_implementation_fast/README.md`
§§"Derived sampling"/"Open" describes the finite sampler and expected-time
uniform sampling boundaries; implementation discrepancies are not silently
identified with ideal sampling.

[SCOPE] Exposed keys can read each fixed query score on every retained input,
including expired inputs, and can combine their outputs. The scheme enforces
neither journal acceptance, intended routing, query quotas nor final-state-only
access. Setup roles on the same administered host are process boundaries, not
a trusted-hardware boundary. No claim is made that the 16 scores fail to identify
this known public dataset. The protocol expects an honest plaintext issuer:
the underlying `encode` command accepts general int8 vectors and does not prove
membership in the quadratic image. `issuer.py` is the honest feature adapter.
No fresh general text-query key can be issued after setup; changing the policy
registry requires new setup. This kernel also identifies x and −x, so its
semantics differ from ordinary signed dot-product similarity.

[EXECUTED] The one fixed plaintext evaluation gave 8/16, 9/16 and 10/16 correct
at revisions 2,4,6, compared with the predecessor's 16/16 at each revision.
This weak result is retained without tuning or reselection. No cryptographic
run has been launched in this successor as of this contract.
