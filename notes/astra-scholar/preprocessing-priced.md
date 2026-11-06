# A concrete dealer replacement: MASCOT, with the correlated objects charged

[READ] 2026-11-06. Scope: `spdz.py` in the dark-learning harness and its MPC/FHE/HE-matvec callers. This is a **protocol price**, not an implemented OT backend. The executable counter is `../../research/dark_learning_2026_11_06/scholar_preprocessing.py`; its output, source hashes, small live-engine inventory and falsifiers are in `scholar_preprocessing_results.json`. No other lane's file changed. Local paper SHA-256: `53a149efe7ef1cb6362076eada78eb1217d13ea75cea4a63c1248c264e01e3b9`. External search: one web tool call containing two queries; zero Kagi queries, zero PDF downloads.

[INFERRED] **The ideal dealer hides a large structured-product bill.** The HE matvec removes three matrix triples, but retains two dense outer-product tuples. At d=4096 those tuples alone need 33,554,432 secret scalar products under the conservative compiler below. The stored number of authenticated values is not a price for generating them. “The same object in both forks” does not imply a common additive cost: FHE(b) eliminates those two tuples.

## Protocol choice and exact unit

[READ/SOURCE] Keller–Orsini–Scholl, *MASCOT: Faster Malicious Arithmetic Secure Computation with Oblivious Transfer*, [ePrint 2016/505](https://eprint.iacr.org/2016/505), local `/Users/ember/dev/gh/forks/IACR-eprint-mirror/2016/505.pdf`: Protocol 3 (pp.12–14) authenticates private inputs using COPE and a masked consistency check; Protocol 4 (pp.17–19) multiplies, combines, authenticates five values and sacrifices; Protocol 5 (p.19) supplies owner-known input tuples; §7.1 (p.22) derives communication. I read these constructions and the privacy-amplification argument in Appendix C, pp.38–39; I did not implement their security reduction.

[INFERRED/DERIVED] Choose this prime-field protocol, **not SPDZ2k**: the latter's arithmetic is not the harness's F_p arithmetic. Let n=3, k=61, OT extension parameter λ=128 and combining width τ=4. Count total directed network payload, in bits. For large batches:

- An owner-known authenticated input tuple costs `I=(n−1)(k²+k)=7,564` bits.
- A jointly hidden uniform authenticated field value costs `R=nI=22,692` bits: each party privately inputs an independently sampled uniform contribution, and the shares are added. One honest contribution suffices. Giving a single owner the complete mask would break `auth_plain`, so `I` cannot replace `R` there.
- Protocol 4's §7.1 main triple payload is `n(n−1)[τλk+(τ+5)k²]=388,326` bits. I additionally charge the five share-distributions omitted in that approximation and both sacrifice openings: `T=388,326+5n(n−1)k+2n(n−1)k=390,888` bits per usable authenticated triple.
- One all-party field opening costs `O=n(n−1)k=366` bits.

[READ/INFERRED] These are **amortized payload counts**, not a finite-batch serialized upper bound. They exclude base OTs, OT-extension batch consistency overhead, authenticated-channel framing, coin-generation/commitment and batched MAC-check fixed costs, and retransmission. Source §7.1 explicitly omits fixed setup and batch costs; this note does not relabel them zero. Batches of 2^16 or larger make these fixed costs amortizable, but no measured batching implementation is claimed. The source's Table 2 k=64 number is not the unoptimized formula above with λ=128; I use the explicit formula, parameters and decomposition rather than transplanting that table entry. At the paper's λ128, k64, τ4, the formula gives 69,632 bits per ordered pair, while the table prints 53.25 kbit. Thus this model avoids an unresolved table/parameter discrepancy.

[INFERRED] λ128 here is a classical baseline. Lattice base OT alone does **not** certify the whole composition post-quantum: the OT extension, PRG, correlation-robust hashing, commitments and adaptive composition must also receive an appropriate security argument. Substituting λ256 raises `T` to 578,280 bits in this same formula; it is a sensitivity price, not a PQ certification. None of these parameters makes the harness's seeded Python RNG deployable.

## Compiling each ideal dealer object

[INFERRED/DERIVED] This compiler uses ordinary scalar MASCOT triples even for structured correlations. It is deliberately concrete and conservative; specialized matrix/outer-product OT/HE preprocessing may be much cheaper.

| Dealer object | Replacement | Extra online-style MPC during preprocessing |
|---|---|---|
| Owner input mask | Protocol 5 tuple | Already charged by I |
| Hidden random field mask | Sum n privately authenticated random inputs | R |
| Matrix tuple `(A,b,Ab)` | Sample `d²+d` hidden fields; compute every `A_ij b_j` with a scalar triple, sum locally | `d²(T+2O)` |
| Outer tuple `(u,w,uwᵀ)` | Sample `2d` hidden fields; multiply every pair | `d²(T+2O)` |
| Lookup powers `r,…,r^255` | Sample one hidden r; multiply along the power chain | `254(T+2O)` |
| Truncation tuple `(r, low s bits, rhi)` | Generate **K+40** independent authenticated random bits; form r and rhi by local linear sums | `(K+40)B` |
| HE returned-vector authentication | One fresh jointly hidden mask per output coefficient | R per value |
| FHE real mask pairs | Keep §8's posted ciphertext/proof/link schedule; supply its `n·used+n·pairs` owner input tuples | I per tuple, added to existing mask wire |

[INFERRED/DERIVED] Here `B=R+T+3O=414,678` bits per successful random-bit attempt. The bit protocol samples hidden uniform r, computes and opens `r²` with a sacrificed triple, rejects zero, takes a public canonical square root s, and outputs `[b]=(1+[r]/s)/2`. Conditional on nonzero r, its two signs are equiprobable and b is exactly a bit. There are two Beaver-difference openings plus the square opening. Expected attempts multiply by `p/(p−1)`; the table below prints one attempt per bit and the JSON records the omitted expected retry term explicitly. This odd-prime construction is algebraic, not an empirical claim about an OT implementation.

[INFERRED] The high part is essential: generating only the s low bits and an unrestricted authenticated field element `rhi` does not produce `r∈[0,2^(K+40))`. At d4096 the four truncations have K values 19,19,8,19, so generating complete masks requires `4096·(59+59+48+59)=921,600` bits. Authentication does not establish a range or a power/outer-product relation. Conversely, computed correlation outputs inherit their MACs; independently authenticating all stored outputs would double-charge them.

## Per-step prices

[MEASURED/EXECUTED] Run from the repository root:

```
python3 research/dark_learning_2026_11_06/scholar_preprocessing.py > research/dark_learning_2026_11_06/scholar_preprocessing_results.json
```

[DERIVED] Decimal Gbit. “Total” adds the existing online wire and, for FHE, §8's real-mask wire; **proof transmission, proof construction, and fixed backend overhead remain separate**. No clocks. Genesis weight input is excluded, as in §11. FHE(b), including the d64 row, is a schedule model with unbuilt relinearization.

| d | fork | scalar triples, excluding bit generation | random-bit triples | preprocessing Gbit | total payload Gbit |
|---:|---|---:|---:|---:|---:|
| 64 | MPC/SPDZ matvec | 39,104 | 13,248 | 21.097 | 21.104 |
| 64 | MPC/HE matvec | 27,008 | 13,248 | 16.081 | 16.191 |
| 64 | FHE(a) | 26,816 | 13,248 | 16.197 | 16.324 |
| 64 | FHE(b), model | 18,624 | 13,248 | 12.803 | 12.940 |
| 1024 | MPC/SPDZ matvec | 5,565,440 | 224,256 | 2,344.070 | 2,345.272 |
| 1024 | MPC/HE matvec | 2,422,784 | 224,256 | 1,041.958 | 1,043.306 |
| 1024 | FHE(a) | 2,419,712 | 224,256 | 1,088.431 | 1,093.727 |
| 1024 | FHE(b), model | 322,560 | 224,256 | 219.551 | 221.060 |
| 4096 | MPC/SPDZ matvec | 85,225,472 | 921,600 | 34,900.879 | 34,919.539 |
| 4096 | MPC/HE matvec | 34,906,112 | 921,600 | 14,052.676 | 14,058.105 |
| 4096 | FHE(a) | 34,893,824 | 921,600 | 14,809.700 | 14,881.544 |
| 4096 | FHE(b), model | 1,339,392 | 921,600 | 907.607 | 913.638 |

[DERIVED] At d4096, the ordinary online nonlinear multiplications consume 299,008 triples; HE Freivalds adds 12,288; lookup-power generation adds 1,040,384; the HE-MPC outer tuples add 33,554,432. Their sum is 34,906,112, before bit generation. The JSON retains the complete decomposition at all three widths. This is why billing 35.8M “authenticated values” uniformly was not meaningful.

[INFERRED] **§11's wire parity is refuted for this specified preprocessing backend.** FHE(b)'s priced total is approximately 15.4 times smaller than HE-MPC's at d4096. This is a cost verdict on the conservative MASCOT compiler, not a lower bound for MPC or a completed FHE deployment. FHE(a) still loses to HE-MPC. At small d, preprocessing even reverses the online-only preference between ordinary SPDZ matvec and HE matvec. Proof sizes, proof traffic, circuit privacy, relinearization, latency and custody can reverse a whole-system choice; this table claims no whole-system winner.

## Security budget and falsifiers

[READ/INFERRED] MASCOT Protocol 4's τ4 theorem supplies statistical security at the field-bit scale, not automatically 128 bits. The separate MAC and sacrifice errors also depend on p. At p≈2^61, a conservative union over roughly 35.8M generated HE-MPC triples per step and 10^6 steps is on the order of `2^−16`, before constants and other legs. This is a **failed sufficient run bound**, not a measured leak. Batching can improve some check-error accounting but does not erase privacy-amplification obligations. A 2^−40 full-run requirement needs a justified stronger instantiation (larger-field authentication/checking and revised amplification, or another backend) and a new bill. Repeating a check with the same sacrifice mask is not automatically sound privacy amplification: two different opened linear combinations can reveal its retained secret. Do not advertise the baseline table as a deployable run-secure protocol.

[MEASURED/EXECUTED] The script executes the actual `mpc_fork.run_step` at d8 and checks every dealer tag multiplicity against an independent inventory and `step_counts`; all agree. It exhausts p=97 sacrifice challenges: an honest tuple accepts 97/97, an incorrect product 1/97. A witness selected after the sacrifice challenge passes despite a wrong product, exhibiting the commit-before-challenge requirement. Wrong high-part, power-chain and outer-product witnesses are refused by their exact relation controls. The random-square bit generator produces exactly 48 zeros and 48 ones over the 96 nonzero field elements. These tests validate the compiler's arithmetic obligations, **not malicious OT or distributed execution**.

[INFERRED] Next useful preprocessing brick: generate the two dense outer tuples with batched HE or specialized correlated OT, including authentication, malicious input consistency and sacrifice, then rerun the same inventory. The fresh HE-matvec keys are not a free secure preprocessing service: their well-formedness and circuit-privacy obligations must be solved before that substitution earns a price.
