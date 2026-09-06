# HE closure and complete learner costs

[DERIVED] 2026-09-06 tranche: **low-rank state is not a ciphertext refresh
operation**. To reduce the whole private computation bill, restrict where
private information enters, or change the learner. Fewer trainable parameters
alone do neither.

[DERIVED / EXECUTED] A restricted positive repair now exists: an encrypted
sliding window has a history-independent noise bound when expiry subtracts
the **same ciphertext** that entered. The queue, fresh ingress and bounded
readout supply this property; rank does not. See §8.

[EXECUTED] Exact arithmetic models and genuine BFV probes cover finite packed
Learn/Infer and noise/rounding falsifiers. Full test keys remain: no Dark
resident. No CPU/GPU timing is claimed; §6 labels heuristic attack costs.

## 1. Landed foundation and correction

[SOURCE: repository/formal statements read] VERDICTS §3/§5c/§7.8 govern:
deployed depth 2; low-rank commitment/matvec savings already proved; PQ gap
open. `minidregg/Assurance/ZkmlLowRankUpdate.lean`'s `matVec_chainUpdate`
has one base matvec plus T thin pairs; it claims no ciphertext refresh.
`/Users/ember/dev/breadstuffs/metatheory/Bfv/Noise.lean:164`, `noiseAt_add`,
states exact phase-noise addition; `:172`, `abs_noise_add_le`, gives the sum
bound. These are reads of existing theorem statements, not new builds here.

[REFUTED: low rank alone refreshes additive BFV state] DARK-TRAINING §4's third
alternative and §7.1's refresh preference need correction. Actual addition is
componentwise (`/Users/ember/dev/breadstuffs/vendor/fhe-dregg/src/bfv/ops/mod.rs:15`).
For an integer phase encoding, `e(c+d,m+n)=e(c,m)+e(d,n)`; actual BFV also has
its encoding's rounding/carry conventions. Rank never changes that operator.
Addition may preserve a finite usable margin; it does not replenish it.

[DERIVED] Keep these choices separate:

| Representation/update | Saving | Remaining obligation |
|---|---|---|
| Accumulated encrypted W | Fixed state count | Old and update noise combine |
| Fresh independent factors stored separately | Individual factor noise unchanged | Issuance; T-dependent storage/readout; sum noise |
| Factors computed from prior private state | Potential arithmetic/storage saving | Inherited private dependency and noise |

[DERIVED] Balancing an addition tree changes scheduling, not the final
ciphertext. Adding Enc(0) rerandomizes and adds its error. An indefinitely
growing sum has no noise reset from this identity. A finite moving window
can instead remove old contributions exactly (§8). This does not refute
bootstrapping or specialized learners with another explicit noise invariant.

## 2. Genuine BFV evidence and exact parameter pin

[EXECUTED] `experiments/he_closure_costs/bfv_probe/` is an isolated Rust
package; Cargo.lock pins offline dependencies. `source_manifest.json` pins
source hashes and breadstuffs commit `3e51def6a5a95424e54fbe7432539b06088de5c3`.
Its own target directory is ignored; companion source trees were untouched.

```text
python3 research/learn_infer_only/experiments/he_closure_costs/ledger.py
cargo run --offline --release --manifest-path research/learn_infer_only/experiments/he_closure_costs/bfv_probe/Cargo.toml
```

[EXECUTED] Parameters returned by the real library: N=4096,
Q factors `[68719403009,68719230977,137438822401]`, exact
Q=`649033470896967801447398927572993`, log2(Q)=108.99999191685718,
**t=1032193**. The last is a 20-bit prime, not literal `2^20`.
`parameters.rs:198–220` searches for the NTT prime; the probe prints/asserts
`params.plaintext()`. Proposed precision correction: use this actual t when
instantiating VERDICTS §3's shorthand against this executable.

[SOURCE: sampler read] `keys/secret_key.rs:42–44` calls `sample_vec_cbd` with
variance=10 (`parameters.rs:272`). Pinned `fhe-util-0.1.1/src/lib.rs:22–54`
takes the difference of two 20-bit popcounts: support ±20, variance 10.
This agrees with the landed `notes/fhe-core-theory.md` correction. Apple
ternary-secret tables differ; Gaussian σ3.19 is also not exactly this CBD.

[EXECUTED] Start Enc(1), apply `c←c+c`, check coefficient zero against
`2^j mod t`. Embed that scalar as entry (0,0) of a rank-one 2×2 matrix.
Updates remain nonzero rank one. **No ciphertext multiplication, division,
rescale or nonlinearity occurs.** Four ChaCha20 seeds produce:

| Seed byte repeated 32 times | First monitored-coefficient mismatch, additions | Expected | Observed |
|---|---:|---:|---:|
| 7 | 81 | 771091 | 771092 |
| 19 | 78 | 741507 | 741506 |
| 43 | 79 | 450821 | 450820 |
| 101 | 79 | 450821 | 450820 |

[EXECUTED scope] These are specified-seed failures, not a universal safe
horizon, a worst-case noise theorem, or the earliest failure among all
polynomial coefficients. The library noise meter decrypts internally; its
logged values are diagnostics only for public synthetic fixtures. No noise
meter output from real private data should be given to the host.

[EXECUTED positive] Across all four seeds, 128 independently encrypted fresh
1's added to an initial Enc(1) decrypt to 129. Thus finite additive learning
can work; fresh inputs and recursively reused state have different noise.

## 3. A finite encrypted Learn/Infer arithmetic loop

[EXECUTED] Pack c into polynomial coefficients 0…15, initially encrypted zero.
For 64 steps, the issuer chooses `u_i∈{-1,0,1}`, encodes negatives modt,
public-key encrypts u; the host adds it to c. No intermediate state decrypts.
A public query `φ_i∈{0,1}` is reversed into a plaintext polynomial: one
ct×pt product places `Σ c_i φ_i` at coefficient 15. Product degree≤30<N,
so no negacyclic wrap affects this equality. `|c_i|≤64`, `|score|≤1024<t/2`.
All four seeds pass after a state-codec roundtrip; seed 101's score is 6.

[EXECUTED / DERIVED] Full implemented-core bill, per seed:

| Item | Count / bytes | Scope |
|---|---:|---|
| Init | 1 keypair + 1 zero encryption | Full sk retained by test reader |
| Each Learn | 1 encode + 1 public-key encryption + 1 ct addition | 64 steps |
| Persistent state | 1 ct;111646 serialized bytes | 16 used coefficients |
| Input traffic | 7145344 bytes for 64 ct | 111646/Learn, excluding auth/framing |
| Infer | 1 query encode + 1 ct×pt product | Zero rotations/relinearization |
| Encrypted readout | 111646 bytes | Whole output polynomial, not scalar envelope |
| Public key | 55859 serialized bytes | No secret-key bytes logged |
| State RNS array | 196608 bytes | 2×4096×3×8; excludes object/temporary buffers |
| Dependencies | Issuer→host/Learn;host→test reader/Infer | No arithmetic interaction |
| Proof/auth/continuity | Unimplemented | Not priced as zero |
| Protected recipient release | Unimplemented | Test reader opens all coefficients/state |
| Refresh/migration | None within this horizon | No indefinite-horizon claim |

[OPEN] This is additive memory, not SGD or order-sensitive adaptation. The
full key is an explicit read-all credential. A context receipt still needs
an implementation that hides its witness and releases only coefficient 15.
Positive result: encrypted arithmetic closure for the tested finite loop,
not tier-A/B closure of the entire resident.

## 4. A bounded order-sensitive learner, and its honest cost

[DERIVED contract; EXECUTED carrier check] Fixed public features, private
`c∈[-127,127]^r`: `Learn(c,u)=floor((7c+u)/8)` coordinatewise, u in that
same interval. This is fading state, not claimed gradient descent. Numerators
lie in[-1016,1016]; floor keeps c in[-127,127]. The Python ledger exhausts
all 65025 scalar pairs and checks `0≤7c+u−8c'<8`. +120 then−120 from zero
gives−2; reversed order gives+1. State persists after removing the input.

[EXECUTED schedule counts] At r=16: Learn =16 private×public products,
16 private adds, **16 secure floor-by8 operations**. Infer for public
features =16 private×public products,15 adds,1 recipient-bound score
release; |score|≤2032 for |φ|≤1. Private features instead require 16
private×private products and their private issuance/computation. Secure
floor, proofs, authentication and release are unresolved system terms.

[REFUTED: modular inverse substitutes for integer rounding] t=1032193 has
inverse(8)=903169: Enc(1)×inverse(8) decrypts to 903169, whereas floor(1/8)=0.
Python and genuine BFV execute this. Enc(16)→2 is the satisfying exact-
divisibility control. Exact rationals replace rounding with size growth:
repeating `(7c+1)/8` from zero has denominator 8^T,61 denominator bits at T=20.

[DERIVED interface limit; EXECUTED witness] Allow all r basis queries and
full scores, and r queries recover c. This cannot promise state secrecy
against that complete oracle. Restricting outputs requires a nontrivial
preserved relation, not merely omission of a decrypt method.

[EXECUTED refinement: representation changes rounding cost] `ema_bits.py`
realizes the exact scalar rule as two 11-bit ripple adders: compute
`(c<<3)-c+u`, then retain the upper eight bits. This arithmetic right shift
is wiring after the additions have been paid. All 65025 valid scalar pairs
match integer floor. At r=16 the fixed circuit has 704 AND, 1056 XOR and
176 NOT logical gates; persistent state is 128 logical bits. A 12-bit
accumulator for public Boolean feature scores adds 360 AND and 540 XOR
gates, and passes 196608 boundary/subset cases. **Logical gate counts do
not specify ciphertext sizes, bootstraps, noise, security or latency**.
In particular, XOR need not be cheap in the selected Boolean HE backend.
This supplies a concrete exact-rounding target instead of treating floor
as an unimplemented magic operation. Actual Boolean-FHE execution is
recorded separately below from these exhaustive plaintext circuit checks.

[EXECUTED actual TFHE] `tfhe_ema_probe/`, cached TFHE-rs=1.6.3, Boolean-only
features, performs four real encrypted EMA updates on one 8-bit coefficient.
Inputs are issued using a public encryption key. Histories [120,-120] and
[-120,120] produce -2 and +1, respectively; the continuing state is never
decrypted/re-encrypted between updates. The test reader holds the full client
key. Its 176 AND,264 XOR,44 NOT API calls are counted, not timed; backend
bootstraps are not instrumented. Serialized sizes: one 8-bit state=27112
bytes; shared public key=90316428 bytes; server key=157865796 bytes. The
chosen `PARAMETERS_ERROR_PROB_2_POW_MINUS_165` tuple is printed in the log;
the source's failure/security label was not independently re-estimated.
This establishes actual order-sensitive encrypted arithmetic adaptation,
with an explicitly surviving read-all test credential and no protected
output release. It is not a Dark realization.

[HYPOTHESIS] A public feature extractor followed by a protected final
learner changes the complete private bill. If the issuer already knows the
raw observation, it may compute fixed public features then send Enc(features)
without holding a resident key. Count that compute, provenance and numerical
conformance. This fails once feature extraction depends on prior private
resident state. The utility lane separately prices a real frozen backbone.

## 5. Low-rank full readout and downstream taint

[EXECUTED] `lowrank_counts.csv` prices `W0x+Σ A_j(B_j^T x)`, W0 public,
A/B private. An instrumented d=4/r=2/T=3 evaluator agrees with dense arithmetic
and all formulas, for public/private x. At d=4096, r=16:

| Term | Public x | Private x |
|---|---:|---:|
| W0x |16777216 public products|16777216 private×public|
| Each thin pair |65536 private×public +65536 private×private|131072 private×private|
| Each pair's private adds, including output accumulation |131056|131056|
| Factor state per delta |131072 private scalars|131072 private scalars|

[DERIVED] T=128 makes factor storage equal d², matching the known VERDICTS
§5c break-even. This is no refresh threshold. Packing, rotations,
relinearization/rescale, factor generation and range controls remain extra;
scalar counts are neither HE instruction counts nor measured speedups.

[EXECUTED taint falsifier] d=32/r=2 private adapter: 64 private×public and 64
private×private products. Follow with public 32×32 dense, 32 activations,
public 64×32 readout: **3072 more private×public products  + 32 private
nonlinearities**, with all 64 logits private. Counting only 128 adapter
multiplications misses this. Norms,attention,sampling,optimizer states add
their own rows in an actual model.

[DERIVED] Additive statistics also need readout: private `Σxxᵀ` requires a
private solve/inverse for ridge readout; Sherman–Morrison puts an inverse
denominator in each update. With public features x, covariance may be
public while `Σxy` stays private. That changes the privacy split and should
be stated, not treated as a free private inverse.

## 6. PQ/parameter source pin and proposed §7.8 refinement

[SOURCE: implementation] Apple commit44fa0ee913ebd76a8c045712a514e17f00b2f93b,
[`EncryptionParameters.swift:181–205`](https://github.com/apple/swift-homomorphic-encryption/blob/44fa0ee913ebd76a8c045712a514e17f00b2f93b/Sources/HomomorphicEncryption/EncryptionParameters.swift#L181),
uses ADPS16 at estimator8b25d433… (2022-10-25), ternary secrets,error σ3.2.
`.quantum128` max total bits: 83 at N=4096, 165 at N=8192. Listed 28+60+60-bit
N=8192 example uses t=557057; **last 60 bits are reserved for key switching**
(`:70–80`,`:379–388`). Its 148 total bits are not 148 compute-modulus bits.
These are configuration claims, not a new estimator run.

[SOURCE: local paper] ePrint 2024/463 SHA256
`44419917b3a117dc995696799b97f3298ff5420c74ab7c7df37ace48e4af594a`,
PDF creation metadata 2025-01-06,§4.3 pp9–10 removes the earlier quantum
tables. §5.1 uses estimator8f1ff7e (2024-08-27), MATZOV classical model.
Table 5.2 p.12 gives N=4096 max logq=106 (ternary secret),108 (Gaussian secret),
both with Gaussian error σ3.19, Gaussian secret also σ3.19, Category 128.
Our CBD variance 10 is not either exact distribution tuple. The paper notes
Gaussian modeling of nearby CBD errors, but this comparison is **not an
exact security estimate**. The actual~109 is above both rounded rows.

[DERIVED proposal] Keep §7.8 open; distinguish old Apple quantum cost model,
newer classical MATZOV table and actual distribution. Candidate changes:
smallerQ at N=4096 loses noise margin; largerN needs full total/compute/key-
switch accounting. Three-limb radix2 NTT butterfly counts are 73728 at N=4096,
159744 at N=8192; raw two-component u64 state bytes 196608→393216. Geometry
only; not a GPU/library benchmark or validation of either full parameter set.

[EXECUTED estimator follow-up] Isolated Sage 10.8 now runs estimator commit
53da5982597709ba0fdf94ea37a84d822310fd84 on n=4096, the exact Q83/Q109
products, and **Xs=Xe=CenteredBinomial(20)** (variance 10). Minimum completed
named lattice-attack log2 costs at m=4096:

| Reduction model | Q83 | Q109 | Attaining attack |
|---|---:|---:|---|
| MATZOV classical | 172.579637 | 127.556093 | BDD |
| ADPS16 classical core-SVP | 145.708 | 98.112 | uSVP |
| ADPS16 quantum core-SVP | 132.235 | 89.040 | uSVP |

[EXECUTED / OPEN] These are heuristic generic-LWE attack costs, not a PQ
theorem for structured BFV. Fresh-process checks reproduce these rows.
Sample-access semantics, Gaussian-shaped subroutine approximations,
additional attacks/errors/timeouts, locks and commands are documented in
`experiments/he_closure_costs/estimator/AUDIT.md`. Full test keys still read.

## 7. Primary nearby constructions, with actual boundaries

[SOURCE: construction] Frery et al.,
[`Private LoRA`,arXiv2505.07329v1](https://arxiv.org/html/2505.07329v1),
§4.1 Eq. 5: client decrypts each outsourced public-weight linear result,
computes private LoRA/nonlinearities, reencrypts next-layer input, and
optimizes locally. Refresh comes from a plaintext holder; its server/GPU
numbers do not price an exposed-host resident with no reader. A protected
client or quorum is an additional declared trust/cost assumption.

[SOURCE: construction/methodology] Pirillo–Colombo,
[`ReBoot`,AAAI2026](https://ojs.aaai.org/index.php/AAAI/article/view/39670/43631),
§4 uses local-loss blocks,polynomial activation,momentum,bootstrapping of
both weights and velocities. Table 1: eMLP-1 N=2^16, l=24;eMLP-2 N=2^17, l=27.
§5.1 checks encrypted-vs-plaintext MNIST runs, then explicitly uses plaintext
for broad accuracy studies. Table 4 reports 198.37 seconds/iteration for its
1-1-1 MLP on the stated CPU system; not measured here. Approximate CKKS
accuracy is no exact-refinement theorem; no no-master-read release is
constructed. [OPEN] Source implementation/estimator profile unaudited here.

## 8. Positive closure: exact ciphertext sliding windows

[DERIVED] Let A be the sum of the current queue of at most W ciphertexts.
Append fresh c, expire identical oldest o: A←A+c−o; A=Σqueue at every turn.
Reencryption of o's plaintext is insufficient. A host may archive old
ciphertexts; expiry is an arithmetic operation, not cryptographic erasure.

[EXECUTED actual BFV] `sliding_window_probe/` uses the same pinned library,
independently fresh public-key encryption per observation and fixed N=4096.
Saved command/build/output and source hashes are in `window_results.json`:

```text
CARGO_TARGET_DIR=research/learn_infer_only/experiments/he_closure_costs/bfv_probe/target cargo run --offline --release --manifest-path research/learn_infer_only/experiments/he_closure_costs/sliding_window_probe/Cargo.toml
python3 research/learn_infer_only/experiments/he_closure_costs/window_ledger.py
```

[EXECUTED] Each case runs 1,024 updates. Every 64 steps, serialized A equals
an independently recomputed queue sum exactly, and decoded coefficients
match the integer reference. These test-reader checks do not feed state
back into the computation. No bootstrapping or ciphertext multiplication:

| Case | t | Expiries | Readout | Result |
|---|---:|---:|---|---|
| d=16,W=8, inputs ±1; seeds 23/71 | 1032193 | 1016 each | 1 ct×pt; Boolean query | Both exact score 6 |
| d=577,W=128, inputs/query ±127; seed 109 | 4294828033 | 896 | 2 ct×pt + 1 ct subtraction | Exact score 3594582 |

[DERIVED / EXECUTED] The wide case splits signed query coefficients into
positive/negative plaintext polynomials. Reversed coefficients place the
dot product at coefficient 576; product degree≤1152<N. State bound 16256;
score bound **1191223424<t/2**. N is selected by degree, because the default
parameter iterator filters entries differently at 32-bit plaintext modulus.
The label `default_parameters_128` is not our security certification.

[SOURCE equations / DERIVED bound] `keys/public_key.rs:64–94` has phase
floor(Qm/t)+e·u+e1+e2·s; `plaintext.rs:51–61` and `parameters.rs:418–436`
implement floor(Qm/t) mod Q. With the pinned CBD support ±20, a negacyclic
product coefficient is a sum of N signed products, giving fresh integer
noise E≤2N·20²+20=3276820. Each floor contributes less than one additional
unit relative to ideal Qm/t. Thus a fixed public readout with coefficient
L1 norm L has ideal-phase error ≤W·L·(E+1), independent of history length.
Exact scale-and-round decoding is sufficient when 2tW L(E+1)<Q. For the
wide case L≤73279, this is 264008552994527828978432<Q: a 78-bit integer
threshold for this conservative bound, not a security estimate or an
implemented parameter migration. Input/range authenticity is assumed.

[EXECUTED algebra only] `window_ledger.py` checks 2401 floor-carry cases,
2401 signed-rounding cases and 10000 exact queue/debt group steps. In the
floor encoding, canonical window-noise correction lies in [−(W−1),0];
do not silently port the exact-scale W·E formula. The source-equation
bound is distinct from sampled library noise diagnostics (14/16 bits), and
is not a newly proved refinement of the library's scaler/decryptor.

[EXECUTED falsifiers] In the d16 cases, substituting fresh Enc(old plaintext)
breaks exact queue equality while immediate plaintext still agrees. For a
stronger failure, Z=2^72 Enc(0) is checked to decrypt entirely to zero, and
old+Z initially decrypts identically to old. Expiring old+Z leaves −kZ debt.
Seed 23 first changes monitored coefficient 0 after 40 replacements (0→1);
seed 71 after 160 (0→1032192). This is valid homomorphic rerandomization,
not a fresh-distribution claim. The wide run skips these falsifiers; its
generic final PASS line reuses the small run's label.

[EXECUTED / DERIVED complete implemented core] Wide state: accumulator
111646 serialized bytes + queue 14290688 = **14402334 bytes**. Each Learn
requires one source encoding/encryption, one ct addition and (after warmup)
one ct subtraction; ingress is 111646 bytes/step, 114325504 bytes total.
Readout is 111646 bytes. Public key: 55859 bytes. Raw persistent ct RNS
arrays total 25362432 bytes; transient ct-array peaks are 25559040 during
update and 25755648 during signed readout. Plaintext/key/codec/allocator
and reference-test buffers are additional. No allocator traffic was measured.

[EXECUTED parameter improvement] `sliding_window_83_probe/` repeats the wide
1,024-step window at N=4096 with primes **2199023190017,4398046486529**:
Q=9671406214650060397780993, exact bit length 83. Both primes and the same
t=4294828033 are 1 mod 8192. Seeds 109/137 each pass 16 exact queue checks
and signed scores 3594582/1702855. Q exceeds the conservative threshold
above. Both primes are computation primes; **no special key-switch prime**,
rotations, relinearization or ct×ct products are used. CBD variance 10 is
unchanged. The pinned Apple 83-bit table uses a different distribution;
this is arithmetic compatibility with its ceiling, not a PQ security claim.

[EXECUTED cost improvement] Q83 ciphertext=85022 bytes; public key=42547;
state+queue=10967838 serialized bytes; raw ct arrays=16908288 bytes (2/3 of
Q109). Ingress totals 87062528 bytes/1,024 steps; readout=85022 bytes.
`window_83_results.json`, separate build/run logs and `window_cost_rows.csv`
preserve both configurations. Prior Q109 source and output were unchanged.

[OPEN] The full test key still opens all retained/archived inputs and state.
Scalar-only recipient release, hidden proofs, input range/provenance, queue
identity/currentness and full PQ assurance remain open. An issuer
knowing a label and public fixed features can encrypt their product; a
private state-dependent learning error cannot be moved to that issuer
without changing the trust split. Utility results are separately recorded in `ADAPTATION_UTILITY.md`; its
new selected representation histories match this 577-coordinate/W128 bill.

[EXECUTED Lean / conditional algebra] `formal/he_closure_costs/README.md`
records exact-floor, signed-readout and modular queue-composition theorems,
actual Q83 nonzero witnesses and expiry/margin/range falsifiers. The proposed
patch retains explicit Rust/RNS/scaler and restricted-release obligations.

## 9. Resume, execution and search accounting

[EXECUTED] Python results/run log, lowrank CSV, BFV build/run logs,Cargo.lock,
source_manifest preserve commands,seeds,outputs,versions/hashes. Final BFV
run includes codec sizes and the full packed loop; debug logs remain.

[EXECUTED] Scry: **2 SELECTs +1 schema call**; Kagi 0. LoRA query returns 4
metadata rows. Exact conjunction homomorphic/continual/learning returns 0;
this is not literature absence. Corpus: OpenAlex snapshot named in returned
JSON. Both SELECTs report free_slack and spend_nanodollars=0. Web supplied
primary source reads; CVPR page/PDF returned 403 and direct arXiv failed;
web construction read worked. No companion or shared truth file was written.
[OPEN] Next: realize exactfloor+scalar release with complete credential/PQ
profile; join issuer-side fixed features to utility/provenance controls;
then audit one bootstrapped changed-learner implementation including weights,
velocities,readout,error/leakage. Do not seek refresh in the low-rank identity.

[EXECUTED final source core] [Source phase45](formal/he_closure_costs/source_phase/README.md) constructs the negacyclic phase homomorphism from source encryption equations, proves the selected reversed-query coefficient, and supplies nonzero/failure witnesses. It passes the final651-pin collection check. The additional BfvNoiseSource/ResidentBfvSourceWindow successor is explicitly unfinished and excluded; this is not a completed Rust/NTT/sampler refinement or secrecy proof.
