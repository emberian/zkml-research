# Fixed-span feasibility on the actual 577-coordinate fixture

[EXECUTED micro and completed full run] This tranche tests the existing DDH
IPFE equations on the frozen public research fixture: 577 signed-int8 features,
16 fixed queries, and a separate last-32 window for each of two public routes.
The initial feasibility tranche ran one encrypted contribution. The subsequently
authorized full384-input run is separate under `full_run/`. Only this directory
is owned; no3D files, shared ledgers or companions were changed.

[EXECUTED full result] The uninterrupted full run finished in1537.085seconds:
all384 learning updates,256 expirations,384 exact queue-product checks and96
selected encrypted scores passed. Every score matches the independent integer
oracle, preserving all utility successes and failures. See
`full_run/outputs/SUMMARY.json` and `full_run/README.md` for complete timings,
retained-storage costs and the same restricted fixed-span privacy scope.

[DERIVED scope] Giving the host all 16 function keys reveals their entire
linear span on every input ciphertext and retained snapshot. This is a larger
interface than the original sign-only, selected-query E2E release interface.
It supplies no future policy changes, recipient privacy, finality, verified
erasure, post-quantum security or hidden nonlinear updates. The question is
whether the same feature arithmetic has a restricted, source-conditional
realization after honest private initialization and master erasure.

[SOURCE] Read first: `../README.md`, `../ADAPTIVE_FIXED_SPAN.md`, the original
`../../additive_ipfe.py` audit, and `../../../end_to_end/utility/README.md`.
ABDP, ePrint 2015/017, local October 1, 2015 revision, Figure 2 / Construction
3.1 / Theorem 3.2, printed pages 7–9, gives the equations and a selective
IND-FE-CPA theorem under DDH. Generalizing the fixed-kernel adaptive argument
in `GENERAL_FIXED_SPAN.md` is a new proof, not attributed to that theorem.

[EXECUTED preliminary] The public query matrix has exact rational rank 16.
Its first 16 columns have determinant −812,032,080. A single deterministic LLL
pass on a 32-column public lattice found an integer kernel vector with maximum
absolute coordinate 3. This is ambient bounded-domain nonvacuity; it does not
establish a collision within the text encoder's actual image.

[EXECUTED] Reproduction, hashes, costs and decoding are recorded below. No
extraction or state-recovery experiment is run. No crypto package is installed
or downloaded. The public fixture does not empirically test confidentiality
of an unknown observation.

## Matrix, nonvacuity and proof

[EXECUTED] `linear_audit.py` checks all561 basis columns in the compact form
`N_free=I; N_pivot=-RREF[:,free]`. The rational top block is hashed in
`linear_results.json`; the nonzero small determinant makes it valid modulo the
prime group order as well. One deterministic LLL call on the first32 columns,
embedded as `[I_32 | 10^6 Y_first32^T]`, returns the following integer kernel
witness, padded with zeros through coordinate576 (indices start at zero):

```
0,3,1,0,-1,-3,2,0,-2,2,2,-1,-1,-1,-2,1,
-1,-2,-2,-1,1,0,-2,3,1,0,-2,-1,0,-1,1,-2
```

[EXECUTED / DERIVED] Its squared norm is80 and max absolute coordinate3.
Zero and this different vector are admissible in the signed-int8 box. Adding
the witness to the first actual public fixture contribution also preserves
all16 projections and its bias, with both vectors in[-22,24]. The alternative's
membership in the encoder's text-image manifold is unproved. This is neither
ambiguity for every actual observation nor a ciphertext/dictionary experiment.

[DERIVED; new proof] `GENERAL_FIXED_SPAN.md` writes a uniform master as
`s=Lt+Na`, where N is a kernel basis and `[L N]` is invertible. Exposed keys are
YLt. Replacing k kernel masks by uniform group masks makes an admissible pair
identical in distribution, with the basis fixed before messages. A signed,
padded hybrid over Tk transitions gives `Delta <= 2M epsilon_DDH`, where M is
the least power of two at least max(1,Tk), under exact group sampling. It
explicitly handles unreached ranks, common rejection of invalid pairs and a
bounded-bit scalar-sampling correction. It is classical IND, not simulation,
general adaptive-key security or numerical strength for the concrete group.

[DERIVED] With k561, T1 has M1024/coefficient2048; T384 has
M262144/coefficient524288. Those are proof-loss arithmetic, not performance or
security-bit measurements. The note records independent acceptance and three
required qualifications of the frozen3D lemma. This generalization is separately
sent for review and is not labeled independently reviewed here.

[SOURCE] The mirrored2015/017 PDF hash is
`353f454857a5ef421ab7b17545b9657f5d192dc0a37f022cca7b71e916f84712`.
Read scope is Fig2 / Construction3.1 / Theorem3.2, printed pp.7–9. Its theorem
is selective IND-FE-CPA under DDH; the stronger fixed-span adaptive lemma is ours.

## One actual contribution, two arithmetic backends

[EXECUTED] Both micros separate honest initializer, issuer and evaluator into
subprocesses. Setup exports the public key and16 scalar keys and exits. Issuance
receives only the public key and one public research contribution. Evaluation
receives only ciphertext, fixed keys and public queries. The authorized q00
score is1435 and matches a separate integer oracle. This is one contribution,
not an encrypted W32 history.

| Operation | Python micro, seconds | Native micro, seconds |
|---|---:|---:|
| Setup and fixed-key issuance | 16.313 | 6.420 |
| One577-coordinate encryption | 28.316 | 1.264 |
| All578 subgroup checks | 21.887 | 1.170 |
| One fixed group projection | 0.180 | 0.174 |
| Decoder table setup | 0.00388 | 0.00365 |
| Authorized score decode | 0.04845 | 0.04964 |

[EXECUTED] These are separate single measurements under shared machine load,
not equal-load speedup estimates. JSON records retain exact nanoseconds, sources,
fixture and artifact hashes. After native measurement,2315 exponentiation
results matched Python `pow`. Those checks ran separately inside their private
role; operands were never serialized. They are excluded from native timings
and are not repeated per ciphertext in the authorized full run.

[SOURCE: installed primary documentation] OpenSSL3.6.4's local
`/opt/homebrew/opt/openssl@3/share/man/man3/BN_mod_exp_mont.3ssl`, DESCRIPTION
lines169–176, describes the fixed-window `BN_mod_exp_mont_consttime` routine's
special layout for protecting exponents. The installed dylib SHA256 is
`bae675614cd791d37ec35416ea9f87edcc85407d020810504cf458119b63522c`.
`native_public_probe.py` independently checks five public powers and pins the
manual/library. The group, parameters and FE equations are unchanged.

[DERIVED] This API call does not make the Python protocol constant-time.
Conversions, message-table lookups, memory handling and Python inversion for
negative powers retain explicit side-channel/private-boundary qualifications.
The source theorem is not a side-channel proof. No package was installed.
gmpy2, PyNaCl and PyCryptodome were absent; `cryptography` and system libcrypto
were present. This is an arithmetic backend change, not a security upgrade.

## Decoder, bytes and lifecycle

[EXECUTED / DERIVED] Max query L1 is3499, hence the common W32 score bound is
`32*127*3499=14,219,936`, versus the generic297,805,856 bound. A common
baby-step/giant-step decoder uses5333 baby entries and at most5333 giant
iterations. Raw group values occupy1,365,248 bytes; the measured Python table
plus entries occupies1,614,848 bytes, excluding interpreter/allocator overhead.
The observed score uses2667 iterations. Integer decoding is unique far below
q/2. This interval is an application contract, not an enforced leakage gate.

| Raw artifact | Bytes |
|---|---:|
| Group element / scalar encoding | 256 |
| Public key | 147,712 |
| Sixteen fixed keys | 4,096 |
| Ciphertext | 147,968 |
| Two W32 queues plus two aggregates | 9,765,888 |

[DERIVED] The last total excludes keys, metadata, past ciphertexts/checkpoints,
interpreter memory and the issuer model. Ciphertext multiplication and exact
old-byte inversion preserve the product-of-current-queue invariant without
noise or an online writer master. Expired ciphertexts remain retainable.

[DERIVED] Master and all copies must be erased after private honest setup.
Issuers need only the public key but must hide raw inputs and fresh coins from
the host. Separate processes check the API; they do not prove OS isolation or
physical erasure. Private timing diagnostics are research instrumentation,
not the deployed host interface. Every challenged fresh input must agree on
the full16-dimensional observable span. Current-window/class equality alone
does not suffice, and keys remain usable on every retained input/snapshot.

[DERIVED] Invisible kernel differences cannot affect future permitted fixed-
span answers under linear updates. Plaintext Yx values implement the same
observable learner. FE additionally retains full vectors encrypted, with
conditional representation privacy; this is not secret cognition from those
invisible distinctions or an upgradeable sign-only release policy.

## Replay and accounting

[EXECUTED] From the repository root, run the named scripts in this directory:

```sh
python3 -B research/learn_infer_only/experiments/private_construction/fixed_span/scaling/linear_audit.py
python3 -B research/learn_infer_only/experiments/private_construction/fixed_span/scaling/micro.py
python3 -B research/learn_infer_only/experiments/private_construction/fixed_span/scaling/native_public_probe.py
python3 -B research/learn_infer_only/experiments/private_construction/fixed_span/scaling/native_micro.py
```

[EXECUTED] Stdout/JSON records are saved. Generated group artifacts are gitignored;
exact hashes/bytes remain recorded. `provenance.py` preserves the original Python
micro record and annotates its bookkeeping references after the independent
matrix audit added561 basis checks; it changes no crypto result or timing.
The replay commands write fresh results: preserve this delivered snapshot before
rerunning. Fresh encryption randomness changes artifact hashes. `seal.py` checks
the delivered snapshot and its frozen metadata, not an arbitrary later rerun.
Search counts here: ScrySQL0/schema0/Kagi0/web0, downloads0, installs0.
Cumulative lane counts remain ScrySQL10/schema1/web30/Kagi0. No commits,
companion edits, extraction tests or resumed paused tasks were performed.
