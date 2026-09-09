# Exact CRT-NTT external product: native result

[EXECUTED] One complete native external product succeeded on the previous genuine TFHE accumulator-difference input. All2,048 output coefficients from the new CRT-NTT backend match both a complete signed integer reference and TFHE1.6.3's existing Karatsuba external product. The one actual Fourier comparison also produced identical ciphertext bytes. This is a measured agreement for the retained fixture; it is not a theorem that arbitrary floating FFT runs equal exact integer arithmetic.

| Same-input native work | Measured time |
|---|---:|
| One raw GGSW encryption | 0.730416 ms |
| New general CRT-NTT external product | 1.227708 ms |
| Direct signed integer reference | 0.558958 ms |
| Existing TFHE exact Karatsuba path | 0.408750 ms |
| Raw→Fourier public conversion | 0.066792 ms |
| Existing TFHE Fourier external product | 0.031458 ms |

[EXECUTED] The comparison is a construction/consistency result, not an NTT speedup claim. All commands/stdout/stderr are retained under `results/`. `capture-001` is the only setup/capture. Its exact37 source/binary/input pins were recorded before setup in `capture_pins.json` and rehashed unchanged afterward. The previous modulus-switch, initial-rotation and exact-decomposition proofs all verified before capture.

[EXECUTED] The old raw evaluation key had not been retained. This run generates one new public raw GGSW encryption of the public selector1, using the actual u32/N512/GLWE-size4/base10/levels2 parameters and a fresh ephemeral binary GLWE key. It saves no client key, seed or RNG state. The saved initial accumulator/difference has zero masks, so its public body is valid under this fresh key. This intentionally does not preserve the original805-dimensional LWE selector identity and is not a complete original PBS continuation.

[EXECUTED] Existing `decrypt_glwe_ciphertext` with the ephemeral key measured maximum error28,160 native torus32 units against the public input delta over512 body coefficients. The key exists only inside that capture process and is not retained. There is no secret-key erasure, host-security or security-level claim.

[DERIVED] The general new backend centers each raw u32 GGSW coefficient into[-2^31,2^31−1], uses the exact signed digits in[-512,512], performs twisted512-point cyclic NTTs for negacyclic convolution, sums all8 level/row terms for each of4 output polynomials, reconstructs the signed coefficient with CRT, then reduces modulo2^32. Each coefficient has at most4,096 products; its absolute value is at most2^52. The prime product2,009,731,336,725,594,113 exceeds2·2^52, giving unique centered reconstruction within that bound. Centering raw coefficients changes their integer lift but not the final residue modulo2^32.

[EXECUTED kernel] `Compiler/TfheCrtRange.lean` proves the generic per-product and4096-term list bound, signed CRT uniqueness from the two coprime residues, centered-u32 residue preservation and exact256×low24 scaling. Eight guarded axiom prints pass in `results/crt-final-001.*` (5.132 seconds, exit0, empty stdout/stderr). The negative-one CRT witness has no axioms; all other prints use only the usual Lean foundational axioms. These are arithmetic reconstruction lemmas, not a proof of the native NTT loop or a new cryptographic theorem.

[EXECUTED] Pure preflight checked both primes by complete trial division and verified1024th roots with half-power−1: `(p,psi)=(2013265921,341742893)` and `(998244353,258648936)`. Root candidates31 and3 need only supply these certified-order roots for this512-point transform. Every signed CRT coefficient matched the complete direct reference, before torus reduction; every reduced coefficient matched existing Karatsuba.

[SOURCE] Source boundaries, relative to TFHE1.6.3 `src/core_crypto/`:

- `algorithms/ggsw_encryption.rs:103`: raw GGSW encryption, level order2 then1 and native row order.
- `algorithms/lwe_programmable_bootstrapping/karatsuba_pbs.rs:314`: exact existing external product; same SignedDecomposer/tensor iterator, followed by wrapping polynomial products.
- `algorithms/ggsw_conversion.rs:18`: existing raw-to-Fourier conversion.
- `algorithms/lwe_programmable_bootstrapping/fft64_pbs.rs:270` and `fft_impl/fft64/crypto/ggsw.rs:483`: Fourier external product, same decomposition, integer forward transform, floating multiply-add and torus conversion.
- `boolean/parameters/params.rs:10`: actual DEFAULT_PARAMETERS profile/noise. This package does not adopt that source's security-bit claim for the new backend.

[EXECUTED] Public raw GGSW:65,592 bytes, SHA256 `cdb69a441c980a2ce408ec355775fd4b87f3ad7ab64bf3e2c0fb59aa8b567aed`. Public Fourier representation:131,376 bytes. Each output ciphertext:8,232 bytes. Exact output SHA256 `100b074017320fdcb3968250569cb27bf98ed7fa48986b234aeb2473b09da1c1`. `ntt_public.json` retains public transforms, residues and signed reconstructions. `recurrence_public.json` exposes indexed active key24-bit residues and scaled output words; `public_rows46.json` gives the exact canonical public reader rows for the generated proof.

[EXECUTED] The separate generated recurrence proof under `formal_recurrence/` has now passed, including fresh public verification and changed-output refusal; see `PROOF_RESULT.md`. The raw GGSW encryption's correctness, native NTT loop implementation and cryptographic security are not inferred from a successful byte comparison. The recurrence proof is intended to check the actual complete integer output independently of how the producer computed it. No full blind rotation, later CMUX, key switch or whole PBS was run or proved here.
