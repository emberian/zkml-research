# Independent review of the static base-FE source audit

[DERIVED / independent review, 2026-09-07] **Accepted in its stated conditional static scope, with one explicit accounting clarification.** The GKP constructor and inspected ABE reduction admit the claimed straight-line lift with one quantum advice state. The GKP privacy and fresh-correctness ledgers are correct. The displayed ABE coefficient `2 eps_LWE` is supported by a direct all-block replacement on each message leg; it should not be obtained by silently composing the separately displayed two-LWE TOR bound. This review supplies that direct reduction below.

[REFUTED: literal recursive payload only] The source's explicit GKP/GVW public-key layout also yields a concrete obstruction stronger than an unspecified circularity concern: a full next-level key cannot fit in a plaintext under the same common size bound. Allowing separate bounds across levels gives at least exponential growth for this uncompressed layout. This does not refute the published FE/depth theorems or an alternative public-environment/short-key construction.

[EXECUTED / identity and preservation] Reviewer: `/root/entropy_composition`; author: `/root/he_closure_costs`. The frozen target [BASE_FE_AUDIT.md](../../pq_composition/base_fe_audit/BASE_FE_AUDIT.md) has SHA256 `3e49e259abbe3ca72da5528b96ca8080b96a3589a442e6b3a38ea66841c60d2d`. All target text and the relevant pinned source definitions, constructors and proof passages were read. [results.json](results.json) records unchanged before/after hashes for eight audit artifacts, nine source PDFs and nine extracted texts. No author source, companion, shared ledger or frozen bootstrap file was edited. No commits, downloads or network queries were made by this review.

## 1. Source coverage and what is conditional

[SOURCE / primary text inspected] The source locations used are:

| Local eprint | Inspected material | Finding relevant to this review |
|---|---|---|
| [2012/733](https://eprint.iacr.org/2012/733) | Definitions 2.1–2.8, pp.12–15; Theorem 3.1 and Corollaries 3.2–3.5, pp.20–22; Remark 3.7 and §3.1, pp.23–24; Claim 3.8, simulator and Lemmas 3.9–3.11, pp.24–29; Appendix B, pp.47–49 | The actual bitwise FHE/garbling/ABE2 constructor, its component correctness events, one-key simulation hybrids, two ordinary ABE branches, and literal key/output costs. |
| [2013/337](https://eprint.iacr.org/2013/337) | ABE and LWE definitions, pp.7–8; Lemma 3.1 p.8; TOR definitions, pp.9–11; §5 construction/analysis, pp.12–15; §6 algorithms and Lemma 6.4, pp.15–20 | Classical joint LWE samples, statistical recoding properties, explicit matrix key layout, selective attribute timing and exact false-predicate refusal. |
| [2014/917](https://eprint.iacr.org/2014/917) | §4, Corollary 1 and Theorem 3, pp.12–14 | The shallow-to-general transformation assumes multi-output FE and shallow symmetric decryption/randomized encoding; its printed private-key treatment says the public-key version is essentially identical. |
| [2014/148](https://eprint.iacr.org/2014/148) | Appendix D.1–D.3, pp.34–39, including footnote 15 | The starting circuit FE has arbitrary output length. The suggested Boolean equivalence uses unbounded key queries. The source preserves a bounded number of *multi-output* function keys. |
| [2015/173](https://eprint.iacr.org/2015/173) | Appendix C, pp.56–57 | The cited IND-to-SIM, bounded-key and depth-upgrade chain, including explicit additional bookkeeping and compactness caveats. |
| [2013/364](https://eprint.iacr.org/2013/364) | Definition 10 p.12; §3.3, Definition 13 and Theorem 14, pp.15–17 | Standard-model trapdoor slots, one underlying FE switch and symmetric-ciphertext switches. Its general-circuit theorem does not itself prove the required NC1 restriction. |
| [2012/521](https://eprint.iacr.org/2012/521) | §5.1–§5.3, pp.16–22, including Claims 5.1.1–5.1.3 | N independent setups, field-valued polynomial functions, the subset conditions, static Shamir simulation and the expressly stated exponential subset-error rates. |
| [2016/006](https://eprint.iacr.org/2016/006), [2015/720](https://eprint.iacr.org/2015/720) | Definitions/citation chain at pp.5–6 and pp.10–11 respectively; RE public-key/CRS definitions at 2015/720 pp.28–30 | The static Boolean succinct-FE target and the separate short-public-key requirement used in the reviewed bootstrap. |

[EXECUTED / access] All nine PDFs are the exact files under `/Users/ember/dev/gh/forks/IACR-eprint-mirror/` pinned by the author's `access.json`. The already available `pdftotext -layout` outputs were inspected and their hashes independently checked against those records; PDFs were also rehashed. [results.json](results.json) retains every full path and hash. The author's four earlier reference-identification web searches are not counted as new reviewer searches.

[DERIVED / scope] The positive statement assumes quantum-advice security of the actual classical primitive challenge games. It does not infer quantum security just because a classical reduction is straight-line. In particular, this review does not instantiate a particular garbling scheme, leveled FHE, worst-case-to-average-case lattice reduction, or quantitative Gaussian sampler. The author preserves those limitations correctly.

## 2. Static GKP reductions and exact coefficients

[DERIVED / accepted] The target fixes `f,m0,m1,rho` before current setup, with `f(m0)=f(m1)`, and keeps fresh challenger coins independent of the one advice state. For an ABE label switch, the reduction can sample the FHE key pair/ciphertext and the garbling before the selected ABE setup. These are independent components in the real constructor. Consequently the attribute `X=(hpk,psi)` and the predicate value `P_i(X)` are already known when placing the ordinary ABE challenge key.

[DERIVED] In ABE2 branch zero the token is for the complement predicate; in branch one it is for the predicate itself. The selected unopened branch always has predicate value zero. The reduction generates the other ordinary ABE key and all other GKP instances locally. It does not guess this branch in the static experiment. Thus `eps_ABE2 <= eps_ABE` is available for this narrower scheduled use. Retaining the source's factor-two guessing reduction is conservative but unnecessary here. One FE function key still contains many underlying tokens; the proof is valid because each independent ordinary ABE master has only one such token.

[DERIVED] On one fixed-message leg, change the L unopened labels, simulate the one garbling, then change the n bitwise FHE encryptions to zero. The garbling simulator initially gets the actual FHE decryption result. Replacing that result by `f(m)` costs at most `delta_FHE` by coupling the two simulations using the same other coins. No garbling-correctness term is needed in this privacy step: it uses garbling simulation security rather than correctness. After simulation, the FHE reduction needs no FHE secret key. The padded decryption-circuit/key templates supply the simulator's required length metadata without that secret.

[DERIVED] A common simulation endpoint for both equal-output messages gives precisely the author's conservative bound

```text
gap_GKP_static <= 2 [n eps_FHE + eps_GC + L eps_ABE2 + delta_FHE].
```

[DERIVED] The outer factor two is for the two real-to-common-simulator legs. The factor n is the single-bit FHE hybrid count, not a count of oracle calls made on a quantum state. Every selected primitive reduction constructs a classical view and calls the final quantum distinguisher once. Classical sampled tuples and descriptions can be copied. The proof neither copies its advice nor repeats measurements to locate a useful hybrid.

[DERIVED / resource qualification] These are uniform bounds at the final distinguisher's budget plus all local setup, key generation, garbling, predicate evaluation, encryption and simulation work. The circuit family and all required output/message widths must be admitted by the primitive games. The classical statistical replacements remain valid with the same independent advice state because `||(p-q) tensor rho||_1 = ||p-q||_1`; later processing cannot increase trace distance. This does not establish an adaptive quantum key-query theorem or a coherent secret-key oracle theorem.

## 3. The ABE bound needs the direct all-block route

[SOURCE] GVW's KeyGen* uses the known classical attribute to compute wire values, simulates the active recoding keys, and uses known opposite trapdoors for the other branches. Its two per-gate changes are statistical recoding simulation and key indistinguishability. The joint statistical statements include the necessary classical auxiliary key material. The ABE proof then invokes correlated TOR pseudorandomness and a final one-time mask.

[DERIVED / accounting clarification] Write `eps_LWE` for an **absolute probability-gap** bound on the complete `(h+1)m`-sample LWE challenge, and `eta_pk` for the aggregate distance between the challenge's h+1 public matrices and the corresponding trapdoor-generated public matrices on one message leg. The following direct argument gives the displayed coefficient:

1. For each fixed ABE message, replace the key-generation transcript by the KeyGen* transcript, paying that leg's aggregate statistical error.
2. Replace the active public matrices by uniform public matrices, paying `eta_pk`. The inactive keys and their known trapdoors are sampled locally; KeyGen* never needs a trapdoor for an active challenge matrix.
3. Replace **all h+1 correlated encodings together** by independent uniform blocks, paying one `eps_LWE`. The public opposite keys and all simulated tokens are postprocessing of these public matrices; they do not require the unknown common LWE secret.
4. In this all-uniform experiment, the final independent mask makes the transcript distribution identical for the two messages. Reverse steps 3–1 on the other message leg.

[DERIVED] Therefore, with `eta_stat` defined to aggregate the statistical transcript errors on **both** message legs and any message-mask error,

```text
eps_ABE <= 2 eps_LWE + 2 eta_pk + eta_stat.
```

[DERIVED] For one fixed g-gate predicate, if `eta_rec` and `eta_key` are per-replacement total-variation envelopes, the corresponding gate contribution is bounded by `2g(eta_rec+eta_key)` across both legs. Rates must apply to the actual joint transcripts, including sample failures as necessary. The literal mask is a translation in a finite group, so its privacy error under an independent uniform mask is exactly zero.

[DERIVED / distinction] The separate TOR comparison between all-real blocks and real preceding blocks with a uniform last block can be bounded by **two** full LWE comparisons through the all-uniform middle. Composing that TOR bound as a black box with an ABE real-to-uniform-mask argument on each message leg safely gives `4 eps_LWE`, not the displayed two. The direct route above avoids this duplication. The frozen paragraph places these arguments next to each other without spelling out the direct route; the author confirmed this intended interpretation in review coordination. No target bytes were changed.

[DERIVED] A uniform final marginal alone is insufficient: it must be independent of the preceding transcript, or controlled jointly by the reduction. This is why the complete LWE sample package and the statistical public-matrix replacements matter. No numerical LWE security estimate or quantum worst-case lattice lift follows from this bookkeeping.

## 4. Correctness, amplification and the depth boundary

[DERIVED / accepted] The source's fresh-message correctness composes as

```text
delta_FE <= delta_FHE + delta_GC + sum_i delta_ABE2,i
          <= delta_FHE + delta_GC + L delta_ABE2.
```

[DERIVED] The random decryption circuit/input are independent of fresh garbling coins; the random attribute/labels are independent of their fresh ABE coins. Uniform pointwise component bounds therefore suffice by averaging and a union bound. No independence between the eventual error events is needed. The exact false-predicate refusal in GVW's Dec strengthens the literal ABE2 case: its inactive branch always returns refusal, so only the active branch's correctness error need be charged. For a generic ABE with a possibly erroneous false branch, charging both branch errors is safe. Neither observation supplies missing numerical sampler/error rates.

[SOURCE / DERIVED] The cited depth transformations do not authorize an uncharged conversion from one Boolean function key to an arbitrarily long output under that same key. ABSV explicitly assumes multi-bit outputs; GHRW's Boolean replacement invokes unbounded key queries. CIJ's standard-model conversion is straight-line in the fixed static subcase, but has the printed augmented message bound `(2q+1)n+s+1` and requires a suitable shallow symmetric decryption circuit for an NC1 instantiation. It does not itself prove that every general-circuit instantiation remains shallow.

[SOURCE / DERIVED] The GVW bounded-key scheme replicates N independent OneQFE instances and encrypts an `(input_dimension+S)`-tuple of field elements in each. Outside the union of subset intersections, at most one functional token occurs per instance. Its Shamir simulation uses no adversary rewind. Under a uniform QA one-key simulation game, the N replacements and the two classical subset-event probabilities give the stated conservative ledger. The subset events have source-stated `2^(-Omega(kappa))` bounds; that stronger source fact should be retained. The field-valued output interface, N-instance public key, and degree/field-size requirements also remain in the accounting.

[DERIVED / scope] The target reports GKP's printed qk output repetition claim and separately audits the actual N-instance GVW transformation. The latter's N, S and degree factors must be used for a concrete parameter substitution; a quoted high-level corollary is not a substitute for that constructor's dimensions. Similarly, merely negligible trapdoor/correctness errors do not automatically acquire an exponential rate from the LWE hardness assumption. The author's rate counterexample correctly identifies that logical limitation without claiming the actual samplers have the slow example rate.

## 5. A concrete obstruction for the literal full-key payload

[SOURCE] In GKP §3.1 p.23, the FE public key is an explicit tuple of L ABE2 public keys. Appendix B p.47 makes each ABE2 public key a pair of ordinary ABE public keys. In GVW §6.1 p.16, each ordinary ABE public key explicitly stores `2h+1` matrices, where GKP uses attribute width

```text
h = N L + |hpk|,
```

[DERIVED] with N the FE plaintext bound and L the padded single-bit FHE ciphertext width. Let `b_mat` be the positive encoded bit width of one stored matrix, omitting any extra metadata. For this literal uncompressed tuple,

```text
|pk_GKP(N)| >= 2L(2h+1)b_mat
            >= 4N L^2 b_mat
            >= 4N,              since L,b_mat >= 1.
```

[REFUTED: common-bound literal substitution] The frozen bootstrap's node tag explicitly carries `future_keys`; its program contains at least the complete next-level public key. If both plaintexts use a common positive bound N and that next-level GKP instance supports the next payload under that bound, the containing plaintext requires `N >= |pk_next(N)| >= 4N`, a contradiction. Enlarging kappa or choosing a larger common N does not solve that inequality for the literal representation.

[REFUTED: variable-bound literal substitution at growing depth] With separate bounds, a full-key payload instead satisfies `N_i >= |pk_(i+1)(N_(i+1))| >= 4N_(i+1)`. A positive leaf bound gives `N_0 >= 4^d` across d such edges. The relaxed smallest-constant recurrence, ignoring all circuit/prefix metadata and taking `L=b_mat=1, |hpk|=0`, is already `N_i >= 4N_(i+1)+2`. These deliberately weakened constants suffice to establish the growth. The complete composed RE public key includes its inner weak-RE public key, so packing additional outer components cannot reduce this lower bound for the stated full-key-in-plaintext layout.

[DERIVED / exact limit] This argument counts the source's explicit matrix representation and assumes the full next-level public key is actually embedded in the plaintext. It is not an entropy lower bound on every representation, a refutation of the source FE theorem, or a claim that all recursive constructions require short public keys. Independent Boolean repetition, public-key compression, different environmental interfaces and other setup arrangements are different constructions and require their own proofs.

[HYPOTHESIS / concrete next seam] One possible escape is to fix the future public-key environment in each level's universal **function key/CRS**, generated after later setups and before current setup, while keeping those full keys out of the encrypted node program. The outer succinct RE might likewise specialize its interpreter to its independently sampled inner public key. That requires a parameterized public-environment RE simulation definition, consistent simulated inner keys, a fresh joint-induction proof and full function/depth/runtime accounting. It is not established by this review. The existing depth/multi-output and quantitative primitive obligations would still remain even if this layout change succeeded.

## 6. Executed evidence and decision

[EXECUTED] The command

```text
python3 research/learn_infer_only/experiments/adversarial_review/base_fe/review.py > research/learn_infer_only/experiments/adversarial_review/base_fe/stdout.txt 2> research/learn_infer_only/experiments/adversarial_review/base_fe/stderr.txt
```

[EXECUTED] exited 0 with empty stderr. [review.py](review.py), [results.json](results.json) and [stdout.txt](stdout.txt) preserve 2,145 finite-group message-pair checks, 32 ABE2 return-value implication cases, eight exact-refusal cases, 69,632 literal key-width checks, 33 per-level lower-bound rows and 16,384 coefficient checks. A direct two-leg translation example has one-leg distance `1/8` and message distance `1/4`; a separate ternary example has all-block distance `1/9` and correlated-to-uniform-last distance `4/27`. A final marginal can be uniform while the translated joint distributions have distance one. These are finite probability/size facts, not encryption or runtime privacy experiments.

[EXECUTED] The author's `rate_ledger.py` was copied byte-identically into an owned ignored directory and run there. It reproduced the author's JSON exactly: nine rate examples, four repetition rows and four declared one-advice schedules. Those schedule strings are bookkeeping, not verification of a quantum reduction. All 26 reviewed input files remained unchanged. No test failed; the failed-premise examples are deliberate passing controls.

[DERIVED / decision] The frozen audit's positive static QA statement and its separation of remaining source interfaces are supported. Record the direct ABE all-block derivation when using the two-LWE coefficient. Promote the literal public-key embedding concern only to the scoped representation obstruction proved here. The complete bootstrap base remains uninstantiated: this review does not erase the concrete garbling/FHE choice, quantitative errors, depth/multi-output compactness or public-key/environment closure obligations.
