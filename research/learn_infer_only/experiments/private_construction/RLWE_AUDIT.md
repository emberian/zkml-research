# Practical RLWE IPFE: source audit, native build limit, decoder falsifier

[SOURCE / EXECUTED; 2026-09-06] This is the follow-up to the LWE section of
`../../PRIVATE_CONSTRUCTION.md`. It audits the author implementations of
[2021/046](https://eprint.iacr.org/2021/046) and
[2023/721](https://eprint.iacr.org/2023/721). It does not instantiate ALS2015/608's
modular scheme. Complete encryption reproduction stopped at an architecture
failure; only an exact standalone decoder function was compiled and executed.

## Pinned source and security scope

[SOURCE: algorithms/game/proof inspected] Mera–Karmakar–Marc–Soleimanian2021/046
§2.3 pp.9–10 defines adaptive IND and its selective restriction; §4 pp.16–20
constructs and proves the selective scheme. Its Theorem3 bounds advantage by
multi-hint extended RLWE, RLWE and negligible terms under the prescribed widths.
The challenge vectors are fixed before setup. Equal integer inner products are
required for every issued key. This is not simulation security, integrity,
malicious setup, or an all-roles exposure theorem retaining the master secret.
§5's adaptive construction uses vectors of ring polynomials and a different setup;
its theorem cannot be assigned to the implemented selective construction.

[SOURCE] In `R_q=Z_q[X]/(X^n+1)`, with nonnegative bounded integer x and y,
`K>d*Bx*By`, and `Δ=floor(q/K)`, the implemented selective syntax is:

```text
msk=(s_i); mpk=(a, pk_i=a*s_i+e_i)
Enc(x): c0=a*r+f0; c_i=pk_i*r+f_i+Δ*x_i*J(X)
sk_y=Σ_i y_i*s_i
phase_y(c)=Σ_i y_i*c_i-c0*sk_y=Δ*<y,x>*J(X)+ε_y
ε_y=Σ_i y_i*(e_i*r+f_i-s_i*f0)
```

[SOURCE] The tested vector API uses `J(X)=Σ_{j=0}^{n−1}X^j`, the polynomial with
all n coefficients one; the ring's multiplicative identity is the constant1.
The same output is replicated with different coefficient noises. An additional
matrix API encodes different rows in the coefficients; that is a different
declared functionality. The source bounds fresh-ciphertext noise by
`d*(2*n*κ*σ1*σ2+sqrt(κ)*σ3)*By` on its stated tail event. The source's quantum
security estimates are estimates, not reproduced here. Table1's medium row says
119.2 bits; nearby2021 prose says129. Neither number is promoted to verified.

[SOURCE] Adhikary–Karmakar2023/721 §3.4 pp.4–5 explicitly implements the selective
scheme and refers security/parameters to2021/046. Its OpenMP/AVX2 performance
results are not new FE security guarantees. The algorithms, relevant parameter
and performance sections were read; the later biometric protocol's proof was not
audited and is not used as a resident construction.

## Surviving credential and continuation contract

[DERIVED] Honest initialization may issue only one key, such as
`y=(1,1,0,…,0)`, encrypt initial x, then erase all s_i, initial x/coins, setup
seeds and intermediate secret material. Retained mpk allows anyone to encrypt
new observations; there is no online writer master. The host holds c, mpk, y and
sk_y. Keys for the original fixed span are derivable by linear combinations.
Equal-y raw states such as `(1,0,0,…)` and `(0,1,1,…)` remain distinct admissible
representations under public additive updates that stay within the declared range.
The hidden common-kernel differences never affect this interface's future output.

[DERIVED] Public updates add `Δ*u_i*J(X)` to each c_i and leave c0 untouched:
noise is unchanged while the integer trajectory/output stays within its bounds.
This floor-scaled scheme does not support unbounded mod-K wrapping for free.
Private encoded additions add every ciphertext ring element and sum their noises.
For H fresh additions, require an explicit bound on `|ε_initial|+Σ E_i` as well
as the final integer inner product. An output decoder using `round(K*phase/q)`
also has floor-scaling bias: for t=<y,x>, its unwrapped rounding displacement is
`(K*ε-(q mod K)*t)/q`. A sufficient strict rounding condition is
`|K*ε-(q mod K)*t|<q/2`, with canonical treatment of the residue-circle boundary.
The library's boundary treatment has the executed defect below.

[DERIVED] A width-W queue can update `A←A+Enc(u_new)−c_old` using the **exact old
ciphertext**. Then A equals the sum of the W current ciphertexts, and error is
bounded by their sum rather than total stream length. Re-encrypting the expired
plaintext does not cancel its original error. This supplies a source-level path
to arbitrarily long sliding-window processing, conditional on `W*input_bound≤Bx`
and a W-input noise contract. It is not cumulative learning, secure forgetting,
or an executed RLWE-library result. Window8 memory counts below are storage counts,
not a claim that the default medium Bx4 parameters admit eight binary inputs.

[DERIVED negative controls specified, not executed as encryption] Retained msk
issues each coordinate key and reads all encoded state coordinates. Holding sk_y
reads each standalone private observation's projection immediately before any
release gate. Publicly encrypting a replacement state is permitted by the API;
restoring an old ciphertext repeats its output. Ciphertexts and function keys do
not bind genesis, command authorization, receipts or finality. Any private-input
ideal must admit these immediate projections; Learn-ack-only is not realized.

## Actual source and execution findings

[SOURCE] Author repos pinned without modifying their source trees:

| Repository | commit |
|---|---|
| [fentec-project/IPFE-RLWE](https://github.com/fentec-project/IPFE-RLWE) | `283975175b2407ab5a77e718e254d4d01671ca3a` |
| [s-adhikary/IPFE](https://github.com/s-adhikary/IPFE) | `06801d086b1468cdf1a5db84ef9f43552035f3f1` |

[EXECUTED] `make -C vendor/IPFE-RLWE/src` exits2: native Apple clang21 rejects
`-mavx2` on `arm64-apple-darwin25.6.0`. The original sampler includes x86 intrinsics
and AES-NI; the optimized repository also requires AVX2 assembly and OpenMP.
`rlwe_build.stdout.txt` preserves the exact failure. No compatibility installation,
full encryption execution, ported sampler, or substituted randomness was attempted.

[SOURCE / DERIVED: initialization defect] In original `src/rlwe_sife.c:41`, setup
passes `state_secret` to `gaussian_sampler_S1` without initializing that AES context;
only `state_error` was initialized. At line100 encryption similarly passes
uninitialized `state_s3`; its matrix variant repeats the pattern. The sampler's
`gauss.c:441` / `:624` immediately calls `aes256ctr_squeezeblocks`; `aes256ctr.c:152`
reads the supplied round keys and counter. Optimized2023 retains the missing
initializations at `rlwe_sife.c:45` and `:117`. Thus the checked source does not
establish the paper's sampled-distribution premise. No runtime exploit was tested.

[SOURCE / DERIVED: parallel race] Optimized2023 `rlwe_sife.c:32–46` shares the same
mutable PRG contexts across its parallel Gaussian loop. Lines93–97 schedule two
tasks with shared state_s2; lines115–117 share state_s3 again. AES squeeze advances
the supplied counter without synchronization. This is a source-level data-race
finding when those calls overlap; no race detector or exploit ran.

[EXECUTED exact decoder falsifier] `python3 rlwe_source_audit.py` extracts each
repository's unmodified `round_extract_gmp` into a standalone C translation unit.
Both were compiled with installed native GMP6.3.0; optimized OpenMP pragmas run
serially. The original medium parameter header is used for both checks. For
phase `q−1`, representing zero plaintext with noise−1, both functions return
K=50,241 instead of canonical0. Positive control `Δ*5+1` returns5. This is an
actual decoder-boundary execution, not a complete encryption test or a failure
probability. A caller's explicit canonical reduction can repair this boundary;
the checked API/test does not perform that reduction.

[EXECUTED] Result source hashes, exact function start lines, C harness hashes,
binaries, build commands and outputs are in `results/rlwe_source_results.json`
and `build/{IPFE-RLWE,IPFE-2023}/`. The script's initial brace parser encountered
a commented-out brace; masking comments fixed that extraction-only failure before
the recorded successful decoder checks. No vendor source was changed.

## Exact storage and operation counts

[EXECUTED arithmetic from source] `rlwe_source_audit.py` parses every original
parameter set and verifies q equals the CRT-modulus product and Δ=floor(q/K).
Arrays use four bytes per CRT residue; these are actual in-memory array sizes,
not an optimized wire format or measured peak process memory.

| Set | d,n | ciphertext / mpk each | master key | fixed key | q mod K |
|---|---|---:|---:|---:|---:|
| low |64,2048|1,597,440 B|1,572,864 B|24,576 B|231|
| medium |785,4096|38,633,472 B|38,584,320 B|49,152 B|21,866|
| high |1024,8192|134,348,800 B|134,217,728 B|131,072 B|670,066|

[DERIVED / EXECUTED counts] With t CRT moduli, one ciphertext occupies
`4*(d+1)*t*n` bytes. An encrypted addition is `(d+1)*t*n` residue additions;
a public offset is `d*t*n` additions plus scaled-message preparation. Fresh
encryption samples `(d+2)*n` Gaussian coefficients, performs t forward and
`(d+1)*t` inverse NTTs, and `(d+1)*t*n` pointwise modular multiplies. The medium
row therefore has 3,223,552 sampled coefficients, 3 forward /2,358 inverse NTTs,
and 9,658,368 pointwise products. Key generation costs `d*t*n` multiply-adds;
decryption also needs the c0*sk_y polynomial product, CRT recovery and rounding.
An accumulator plus eight stored medium ciphertexts is347,701,248 bytes before
mpk, transient encoding buffers or allocator overhead. No timing claim follows.

## Decision and resume

[DERIVED] Keep practical RLWE IPFE as a restricted source-conditional candidate;
do not claim its published code has supplied a secure running instantiation here.
On compatible hardware, first repair/review initialization and parallel state,
pin explicit range/decoder semantics, then execute the full exposure/ingress and
two-update tests. An ARM port needs a separately reviewed sampler/PRG strategy.
Neither fixing these implementation defects nor executing addition would close
the remaining Learn-ack-only, private nonlinear utility, or finality obligations.

[EXECUTED accounting] This tranche used zero Scry queries and zero web searches,
two primary GitHub page opens and two shallow source clones. Running lane totals
remain three Scry SQL queries plus one schema call, Kagi0, web-search queries11.
Both papers were read from the absolute-path local mirror; no ePrint PDF downloaded.
