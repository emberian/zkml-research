# Independent counts and adversarial transcript controls

2026-11-06. [MEASURED/EXECUTED] `scholar_rederivation.py` independently enumerates the exchange schedule, derives the primitive counts, runs the actual collaborative prover/checker at d=4,16,32,64, and executes the adversaries below. Command from repository root:

```
python3 research/dark_learning_2026_11_06/scholar_rederivation.py > research/dark_learning_2026_11_06/scholar_rederivation_results.json
```

[READ] The JSON pins hashes of `he_matvec.py`, `cosnark.py`, `spdz.py`, and `step_counts.py`. No original file was changed. Full-size HE executions were not repeated: the existing d64/d128 reports were read, while new execution uses small shared algebraic spines and the actual transcript methods. The independent formulas are then checked against the original code, rather than being defined by calls to its count functions. No literature search was needed for this brick.

## The counts reproduce; the units need repair

[MEASURED/DERIVED] With three parties and three matvecs (two forward, one transpose), each directed pair sends `2d/dc+d/dr` ciphertexts and returns `2d/dr+d/dc`. Each ciphertext is `2NL=49,152` 61-bit residues. Authentication costs `18d` field elements; Freivalds costs `36d+18`. The remaining step consumes the input, four truncation, lookup, Hadamard, two outer-mask and final MAC-check messages in the source.

| d | sent / returned ciphertexts | steady SPDZ online | steady HE online | HE authenticated dealer values |
|---:|---:|---:|---:|---:|
| 64 | 18 / 18 | 107,148 | 1,805,214 | 34,688 |
| 1024 | 240 / 192 | 19,703,820 | 22,099,998 | 2,607,104 |
| 4096 | 960 / 768 | 305,897,484 | 88,989,726 | 35,766,272 |

[MEASURED] These reproduce §11 exactly, within its printed rounding. The executed d128 report uses fixed small-d shifts; the width model widens shifts. They are different recipes and should not be silently interchanged. The obsolete §10 double-MAC-return schedule is not what §11 implements.

[DERIVED] The spine has `4d²+9d` reconstructed witness elements. Thirteen commitments and twenty evaluations imply seven matrix and thirteen vector evaluation row-combinations, plus one proximity combination per commitment. Thirteen sumcheck polynomial values per log2(d) round cost `13 log2(d)` opened fields; `13(d−1)` Beaver products give `26(d−1)+13 log2(d)` proving openings. These derivations match every executed counter at four small sizes.

| d | witness elements | proof fields, 64 / 148 queries | proof hashes, 64 / 148 queries | proving wire fields |
|---:|---:|---:|---:|---:|
| 64 | 16,960 | 65,733 / 148,389 | 14,823 / 34,227 | 10,308 |
| 1024 | 4,203,520 | 877,801 / 1,982,569 | 21,351 / 49,323 | 160,380 |
| 4096 | 67,145,728 | 3,395,907 / 7,669,827 | 24,615 / 56,871 | 639,768 |

[READ/INFERRED] **4.1 Gbit is the reconstructed witness's field representation, not the sum of custodian storage or the network proof size.** The three custodians hold 12.288 Gbit of raw share witnesses and encode 49.151 Gbit at rate 1/4 at d4096. The 39 roots themselves are only 9,984 bits. At 148 queries the transcript's field/hash payload is about 482.42 Mbit (60.30 MB), before framing; it is not 4.1 Gbit. The source also counts 39 commitment markers as both fields and hashes, so the field/hash total is a small conservative overcount unless those are separate tags. These categories must remain separate when comparing FHE certificates, SPDZ views, ZKPoPKs and proof transmission. The old ×50–100 committed-bit headline does not represent an equal-storage comparison.

[INFERRED] If collaborative proofs replace MPC-view audit integrity, summing both view storage and collaborative witness storage is an optional implementation choice, not a required cryptographic bill. Extension-field challenges, actual ZK masking, elementwise gates, and all their traffic remain separate. The live Claude lane owns those upgrades; this note neither repeats their work nor declares the full step proved.

## Adversaries run

[MEASURED/EXECUTED] The output retains each verdict and rejection reason.

- **Early Freivalds challenge:** for a visible rho, choose nonzero error `(rho[1],−rho[0],0,0)`. Its dot product is exactly zero. Applying that error to the actual authentication transcript and recomputing `HEMatvec.coins` changes rho; the resulting residual is nonzero and the attempted attack fails. This supports the existing commit-before-rho ordering against this adversary, unlike the old quotient FS hole. It does not prove general ROM/QROM soundness or eliminate grinding.
- **Omitted context:** changing an older transcript prefix leaves the suffix-based rho unchanged. This is executable evidence that the challenge omits model/epoch/instance context, not a successful false-product forgery. W, v, z, shape, transpose flag, key epoch, parent, and invocation must be fixed and bound before an unpredictable challenge. The mathematical error is at most `1/p` for a fixed nonzero residual and a uniform independent rho; the concrete SHA/PRNG code requires a separate computational argument.
- **Fixed-seed MAC cancellation, actual source accepts:** one malicious party alters two opened share values by `rho[1]` and `−rho[0]`, retaining their original MAC shares. `Engine.mac_check('known')` accepts without learning alpha. The coins are predictable from a caller-provided fixed seed. A control deriving the seed from the complete frozen broadcast transcript rejects both alterations. This is an adjacent, real integrity defect: public fixed coins cannot substantiate “the MAC always catches a deviator.” Production needs committed broadcasts, unpredictable joint check coins (or a justified transcript transform), and real commitment/opening enforcement for sigma values; changing a seed alone is not a complete MPC implementation.
- **Parent/child chaining:** a valid no-update algebraic edge accepts twice against the same parent, because its child roots equal its parent roots and the verifier has no instance counter, nonce or policy field. An independently wrong parent is refused. The positive result verifies algebraic continuity; it does not establish one accepted occurrence or durable anti-equivocation. The supplied in-memory `AcceptanceLedger` refuses duplicate counters/nonces and context splices, with a stated premise that the proof binds the expected context. It is a reference state-machine contract, not consensus or crash recovery.
- **Existing full-collusion mutations rerun:** wrong child entry, wrong z1, forged sumcheck rounds and a row-combination lie are all refused by the actual small verifier. These are targeted controls, not a security reduction.

## Integration obligations

[INFERRED] Move the verifier out of the prover's closure and accept a strictly parsed proof object: fixed degree/round counts, dimensions, canonical field values, verifier-derived evaluation points and proximity challenges. Today `evals`, shapes and proximity data are shared Python objects produced by the same function; honest control flow supplies invariants a hostile serialized proof cannot be assumed to satisfy. This note does not claim an exploited standalone network verifier, because that interface does not yet exist.

[OPEN] Before a million-step claim: fix the MAC challenge discipline; bind complete step context to proofs and Freivalds; implement atomic durable parent advancement with quorum intersection; account for base-field check error across the run; and re-price equal security levels. The conditional audit theorem does not discharge any of these protocol premises.
