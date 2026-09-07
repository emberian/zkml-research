# Independent review of the terminal joint-output lemma

[DERIVED / independent review, 2026-09-07] **Accepted as the stated classical, honest-setup-averaged, source-conditioned terminal output lemma.** No blocking error was found in the complete-package reduction, shared-parent replacement analysis, affine commitment coupling, or displayed probability-gap accounting. This acceptance does not establish the current rMIFE compatibility predicate at each realized package, the requested current numerical threshold, or an H=2 private-ingress construction. The public-parent clarification in §6 below must be preserved.

[EXECUTED / roles and target] Author: `/root/private_ingress`; independent reviewer: `/root/pq_composition`. The full target [TERMINAL_JOINT.md](../../private_ingress/provenance_review/terminal_joint/TERMINAL_JOINT.md) was read at SHA256 `1c698c8361cd4d6e5bfefc96ee34d1bcc4d090ec59f09f6efaad378d5195717c`. Its note, manifest-listed evidence, and two primary PDFs/extracts have matching before/after hashes in [results.json](results.json). The author's files, prior frozen artifacts, shared ledgers and companions were not edited. No cryptographic extraction, recovery, routing or service-adversary runtime was executed.

## 1. Primary source scope

[SOURCE / actual reads] The review used these already retained local sources, with no new PDF extraction or download:

| Source and PDF SHA256 | Locations read and relevance |
|---|---|
| 2025/330, `b7133ad8161f287b2a4b4d1a15664c4ace47fbce451d5f569a6d795261108fd2` | Notation p.15; PKE/iO definitions p.18; NIZK definition p.21; rMIFE syntax/correctness and compatibility/security games pp.21–23; older recalled game and footnote 6 p.29; parameters and Construction 2 pp.48–49; Theorem 6.1 and initial hybrids p.50; terminal/reverse-traversal boundary pp.63–64; Lemmas 6.2–6.8 and final sum pp.64–67. The source's Theorem 6.1 and its internal weak-extractability argument remain source-conditioned ingredients, rather than newly reproved theorems in this review. |
| 2007/155, `45358698cdd4007dddbabf74f7e32e7762d963637c8e3bfae5be2235df64868e` | Definitions 4–5 pp.9–10; scalar/general quadratic language p.10; SXDH and binding/hiding commitments pp.24–25; full CRS and scalar proof algorithms pp.27–28; Theorem 18, its simulator and perfect simulated-CRS equality pp.35–36. The scalar-quadratic route is within the source's simulated language; restrictions on general pairing-product targets are not silently bypassed. |

[EXECUTED / access instrument] Reads used `sed`, `rg` and Python page slicing on the pinned retained extracts listed in `results.json`. A full-text `rg` search of 2025/330 for `non-uniform|nonuniform|auxiliary|auxilliary|generator|coin tosses|probability is over`, followed by the listed page reads, found no additional explicit setup-key-dependent advice convention for Definition 4.3. This is a bounded statement about this instrument and PDF, not an author-intent or literature-wide absence claim. Zero SQL/schema/web/Kagi queries were made in this review.

## 2. The terminal challenge and the complete preceding package

[DERIVED / accepted] The terminal reader `g` is a deterministic function of the first byte and ignores every functional coin. For the two allowed prefix states, the terminal state pairs are `(32,33)` and `(33,34)`. They are distinct, and all four states have high bit zero. Updating the canonical opening/history fields therefore preserves exact `g(m0)=g(m1)` while producing genuinely different terminal messages. The terminal claim is not made vacuous by encrypting the same payload twice.

[SOURCE / DERIVED] Definition 4.4 p.23 explicitly gives the adversary a parameter-selection phase before terminal setup. Thus the construction can select bounded FE widths consistent with its independently generated group/proof parameters. All widths and work must obey the note's fixed polynomial relations in every challenged primitive parameter. No algorithm polynomial only in a much larger unrelated parameter qualifies automatically. Fixed worst-case width padding would also permit moving independent group sampling after terminal setup; no unusual secret-advice convention is needed for this preprocessing.

[DERIVED] After obtaining `EK_T` and the sole terminal key `SK_g`, the reduction generates the current and predecessor setups itself. It can issue `SK_F` with the supplied terminal **public** encryption key literally embedded in `F`, then issue `SK_F0` with the current public encryption key embedded in `F0`. It has the local current master, so it can recover the actual current payload produced by genuine predecessor evaluation. It never needs the terminal master or its setup coins. There is no circular request for a terminal transition key or another terminal reader.

[DERIVED] This generator preserves the preceding encryption keys, issued transition keys, public function descriptions, proof parameters and genuine common-prefix ciphertext/snapshot transcript. In particular, it does not replace the actual PRF-correlated current ciphertext/opening by an unrelated fresh sample. Its own locally generated current master is not an additional terminal secret exposed by the FE challenger. The generated keys and ciphertexts are classical postprocessing of the terminal public interface, so the complete package can be included in an ordinary terminal FE reduction.

[SOURCE / DERIVED correctness scope] Source Definitions 3.8 and 3.9 p.18 require perfect PKE and iO correctness. Together with exact deterministic PRF evaluation and GS completeness, these support the genuine prefix's correctly formed trace for its actual coins. The proof does not need to assert that the prefix's PRF-derived coins are statistically uniform. More generally the note explicitly requires correct public current/predecessor algorithms; it does not apply their confidentiality or distributional-correctness theorem with an unproved auxiliary-input extension.

[DERIVED] The tested current output is the **ideal randomized `F` output with fresh independent coins**. Giving `w,z0` and the common package to the distinguisher is permitted: the terminal adversary knows and can generate them before its challenge. An actual current fresh-input challenge ciphertext and its deterministic repeated-evaluation transcript are not common auxiliary data in this experiment. The note correctly leaves their separate bridge open. Public computation the distinguisher performs using the already supplied keys is, of course, included in that distinguisher's runtime.

## 3. Shared-parent replacement cases

[DERIVED / accepted] For state-only replacement, the guards before the final step are identical in the two worlds. Their observations share `G,C,pi_C,epoch` and differ only in `x=0` versus `x=1`, both authorized. Any invalid replacement therefore gives the same `FAIL` law. For a valid replacement, the binding current commitment fixes the byte state and opening, and the genesis commitment fixes its opening. Checking the full current history internally and rejecting noncanonical/free fields fixes the remaining history. Thus a valid current replacement equals the original `w`.

[DERIVED algebra] The source scalar binding commitment's forward map is

```text
(s,r) -> ((r+t*s)P, (alpha*(r+t*s)+s)P).
```

[DERIVED] Its two scalar coordinates form an injective linear map of `(s,r)` over the prime field. Since the group order exceeds the byte range and scalars/bytes are canonical, equality of commitments gives literal equality of the encoded values. This is a mathematical uniqueness argument, not an executed extraction algorithm. The public current proof is not an ignored witness field that could smuggle in arbitrary extra advice.

[DERIVED] Observation-only replacement supplies the same complete pair `(w,z')` to both worlds, and replacing both slots supplies the same `(w',z')`. Their ideal output laws are identical even for malformed inputs. With neither slot replaced, the nonvacuous terminal pair above applies. At the **terminal** source instance, `n=1`: its unreplaced messages have equal deterministic `g` outputs, and replacing that one slot gives literally the same input in both worlds. Terminal compatibility is therefore exactly zero for every tester and every realized terminal challenge pair. This does not depend on interpreting the source tester as having additional advice.

## 4. Joint proof/commitment/FE hybrids

[DERIVED / accepted] Both endpoint CRS reductions can sample the full earlier/current/terminal package and the left or right honest output from the challenged next CRS without knowing its trapdoor. The current binding CRS stays fixed in distribution and binding in every hybrid. Current function descriptions and their issued keys change as efficient postprocessing of the challenged next CRS; there is no claim that these differing programs are iO-equivalent.

[SOURCE / DERIVED] GS Definition 5 permits the interactive tester to know the simulation trapdoor, choose a true statement and witness afterward, and retain correlated state. On the simulated CRS its real and simulated proof laws are exactly equal. Theorem 18 supplies that property for the full scalar-quadratic relation used here. Thus the surrounding package, true payload and separately generated terminal ciphertext can be held jointly while the next proof is replaced. Only the fresh next proof is switched; the genuine prefix's proofs and coin correlations are untouched. The encrypted history excludes the next proof's random tape, which is necessary for the stated straightforward simulation step.

[DERIVED] On the hiding scalar CRS, write `u_N=t_N*u1_N`. With `s1=s0+1`, define

```text
r1 = r0 + t_N*(s0-s1) mod p_group.
```

[DERIVED] The two payloads then open the same public `C'`. For every fixed trapdoor and complete common package, this is a bijection of the uniform opening domain. In particular the **joint** right-hand payload/history, common commitment and simulated proof have exactly their intended marginal law. Separate assertions that each opening is uniform would not be sufficient without this joint calculation. All duplicated opening/history fields must be updated consistently, as the target specifies.

[DERIVED] The terminal FE adversary builds both payloads, their common commitment and the simulated proof before issuing its one challenge. It supplies the challenger ciphertext to the final distinguisher together with the saved package. Its auxiliary data does not depend on the terminal challenge bit. The supplied terminal key only computes `g`, so this pair is admissible exactly. Replacing the simulated proof by the right real proof and reversing the next-CRS hop gives the desired right endpoint.

[DERIVED] The proof uses source FE privacy to change the **encrypted** payload; it does not assert that the plaintext payload laws are identical. The affine calculation establishes each endpoint marginal around that cryptographic switch. No terminal master, terminal challenge randomness or key-dependent secret advice must be supplied to the final distinguisher.

## 5. Exact coefficients and sampling scope

[DERIVED / accepted] In absolute acceptance-gap convention, the hybrid path gives

```text
Delta_joint <= delta_CRS(B0)+delta_CRS(B1)+delta_terminal_FE(A)+2*eta.
```

[DERIVED] For the note's exact DDH distributions, translating a full-field uniform last coordinate by `-P` leaves its law unchanged. Binding → uniform → hiding costs at most `2*d_j` for one group, hence `2*(d1+d2)` for one complete CRS switch and `4*(d1+d2)` for the two endpoint switches. Source Definition 14 p.24 samples all DDH exponents nonzero, while the full CRS algorithms p.27 sample the `t` exponents over the whole field. The note explicitly defines `d_j` for its required convention and requires any conversion before substituting numerical bounds. This qualification must be retained: a uniform **nonzero** coordinate is not invariant under subtraction of `P`.

[SOURCE / DERIVED] With one terminal slot, one functional key and one challenge, the two ordinary PKE ciphertext switches contribute `2*p` when `p` is an absolute gap. If `alpha_PKE` denotes success above one-half in Definition 3.8, the same contribution is `4*alpha_PKE`. The source's internal exponent schedule and p.67 sum support the conditional form `Q_source(t)*2^(-t)` after the `2^(2*s_T)` enumeration; the reverse traversal and outer equivalent-circuit changes can be absorbed in that fixed polynomial. The outer changes require the stated quantitative weak-extractability bound, rather than ordinary unspecified iO negligibility.

[DERIVED / limit] This is correctly labeled a source-conditioned refinement. It does not independently repair Lemma 6.8, claim every malformed-input circuit switch is equivalent because `g` is deterministic, give an explicit finite numerical `Q_source`, or omit the actual reduction's time/circuit budget. There is no independently instantiated numerical PKE/DDH or weak-extractability guarantee in this note.

[DERIVED] Reducing `m+b` fresh uniform bits modulo a domain of size at most `2^m` has statistical distance at most `2^-b` from uniform. A sequential coupling over at most `N` such fresh samples bounds the complete transcript distance by `eta<=N*2^-b`. Two endpoint implementations therefore cost `2*N*2^-b`. This also covers dependent subsequent computation after the sampled fields. It does **not** reclassify a prefix PRF output or another arbitrary deterministic string as a fresh uniform bit block.

[DERIVED] The displayed sufficient budget checks correctly allocate one quarter of `2^-E` to each of the four aggregate terms:

```text
4*(d1+d2) + 2*p + Q_source(t)*2^(-t) + 2*N*2^(-b).
```

[OPEN / preserved] Ordinary negligible PKE/DDH bounds do not supply these specified stretched-exponential values. The stated polynomial-lift conclusion requires its additional quantified rates and mutual polynomial parameter relations. No current finite parameter set or actual sample count is certified by the algebra.

## 6. The remaining quantifier and public-parent boundaries

[SOURCE / accepted reading] Definition 4.3 is a directed probability inequality for specified message/function collections and a tester, universally quantifying replacement subsets, replacement strings and row/function indices. Its displayed tester receives the function, replacements and remaining left inputs. Definition 4.4 adaptively constructs collections and applies that predicate using the same adversary symbol. Neither the printed definition nor the searched notation expressly provides arbitrary advice chosen after setup to contain that setup's terminal secret. Footnote 6 p.29 concerns the recalled older definition/counterexample and does not supply such a global convention.

[DERIVED] The terminal lemma instead fixes a uniform tester and then samples the honest package before comparing the two full joint laws. A bound on `|E_K[d_D(K)]|` is not automatically a bound on `E_K[|d_D(K)|]`. Even full statistical closeness of two joint laws can coexist with a large conditional gap at a rare realized public setup. Additional exceptional-setup, tester-order and retained-state arguments are needed for the proposed current admissibility application. The exact terminal `g` compatibility does not close that current-layer step.

[DERIVED / secret-advice restraint] A different experiment could explicitly hand a terminal secret to a tester after setup, but that is not a premise established by the source definition. This review neither assumes nor executes such an experiment as an objection to the actual source game. Its quantifier controls use ordinary public setup labels and contain no keys. Nor does the signed-cancellation control claim to refute security against every joint tester; its purpose is only to distinguish the displayed expectations.

[DERIVED clarification, nonblocking] As written, the public `R2` statement is `(G,policy,epoch=2,C')`; it does not include current `C`, and the listed fixed verifier parameters are `sigma_C,sigma_N`. Recomputing an intermediate commitment without binding it to a specified public `C` does not separately certify that particular parent. **The accepted same-parent property is enforced inside `F` and by the fixed common-prefix experiment.** A theorem that the public `R2` proof independently identifies the current parent would need to bind `C` explicitly.

[REPORTED author clarification] The author confirmed this intended scope during review and asked that the frozen lemma not be broadened. No author file was changed. This clarification does not affect the true-witness GS hybrids or the current state's uniqueness argument, which already uses the observation's actual `C` inside `F`.

## 7. Executed independent controls and verdict

[EXECUTED] The command

```sh
python3 research/learn_infer_only/experiments/adversarial_review/terminal_joint/review.py > research/learn_infer_only/experiments/adversarial_review/terminal_joint/stdout.txt 2> research/learn_infer_only/experiments/adversarial_review/terminal_joint/stderr.txt
```

[EXECUTED] exited 0 with empty stderr. [review.py](review.py), [results.json](results.json) and [stdout.txt](stdout.txt) preserve 1,052,672 forward binding-image checks; 42,336 canonical replacement guards; both distinct equal-reader terminal state pairs; 132,098 joint right-marginal records and 257 conditional opening bijections; 178 full-field shift laws and nonzero-domain countercontrols; 858 exact modulo-sampling cases; and 6,425 four-term budget cases. Separate finite public-label controls distinguish signed averaging from conditional gaps and full-joint closeness from a guarantee for every realized setup.

[EXECUTED / scope] These are exact finite algebra/distribution controls, not implementations or tests of FE, GS, DDH, PRFs or a deployed service. Symbolic proof records only check a simulator's dependence on the common statement/coins; they do not establish GS security by testing. No cryptographic adversary, secret-recovery procedure or actual prefix/terminal system was run. All nine pinned input files, including the author's manifest, remained unchanged.

[DERIVED final review verdict] Accept the source-conditioned averaged terminal output lemma, with the public-parent clarification above. Keep the quantitative `2^-E` promotion and current source-game admissibility bridge open. No H=2 ingress, arbitrary-history, multiple-parent, QPT, indefinite-horizon or resident implementation theorem follows from this review.
