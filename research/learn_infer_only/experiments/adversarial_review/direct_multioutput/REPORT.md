# Independent review: direct vector GKP

[DERIVED review verdict; 2026-09-08] **Accepted as a conditional static,
one-vector-key construction, with the stated output-dependent public encryption.**
The author note's three hybrid stages and fresh correctness ledger survive
independent algorithm/game review. This acceptance does not instantiate the
quantum-advice primitive premises, extend the key bound, or supply the compact
multi-output interface needed by the separately reviewed bootstrap.

[EXECUTED frozen subject] The reviewed `DIRECT_MULTIOUTPUT.md` is SHA256
`a72f903330f4b4504947cb2cd49592619912f168b375a8abb4532fd373caf828`.
`results.json` records before/after hashes of every author-directory file
except Python cache files; all 8 files, including ignored source extracts,
were unchanged. No author validator was run in place. Review artifacts are
confined to this directory. Shared ledgers, companion trees and commits are
owned by the coordinator and were not changed by this review.

## 1. The source algorithm and what the extension changes

[SOURCE: algorithms and games] I read the pinned local GKP 2012/733 PDF
through a newly reproduced `pdftotext -layout` extraction: printed pp12-15
(FHE and one-time garbling), pp17-20 (ABE2 and FE games), pp20-29
(Theorem 3.1, Corollary 3.5, complete constructor and security proof), and
pp47-49 (two-ordinary-ABE wrapper). The PDF hash is
`117f9a5a3c2d7eed51c939af7c01f59aa34a33298a06b82fda99157aa28c4d97`.
Exact extraction commands and text hashes are in `results.json`.

[SOURCE] GKP §3.1 printed pp23-24 places fresh FHE key generation,
input encryption, the secret-key decryptor garbling, and all ABE2 label
ciphertexts in FE.Enc. Its FE.Setup and FE.KeyGen precede those fresh
objects. Definition 2.7 grants one input encoding per garbled circuit;
Definition 2.11 exposes one predicate key per ABE2 instance. Lemma 3.11's
hidden-label replacement depends on the other label remaining unopened.

[DERIVED] For an M-bit function, the author's independent ABE2 keys indexed
by `(j,i)` give exactly one predicate key per instance. The common FHE key
and input ciphertext tuple do not create a second predicate query to any
instance. A single garbled circuit takes the concatenated M evaluated
ciphertexts, each of width L, so it still receives only one encoded input.
This is a legitimate one-vector-key FE view. Its component tokens are under
distinct master setups; it is not a renaming of multiple Boolean FE queries
under one setup. The construction supports the explicitly stated external
key bound one, with uniform padded function and circuit bounds.

[DERIVED] No construction correction is required. For fully explicit
notation, L must bound both fresh input-bit ciphertexts and evaluated-bit
ciphertexts; shorter ciphertexts may be padded under the author's fixed
template contract. The displayed `h=|hpk|+n*L` uses that convention, as does
the source's §3.1 definition of its ciphertext-width parameter.

## 2. Independent privacy reconstruction

[DERIVED] Fix `f,x0,x1,rho` as in the note: the entire vector outputs agree,
the classical tuple is chosen before fresh setup/encryption coins, and the
one quantum advice state is independent of those coins. For either fixed x:

1. [DERIVED] At each of the `J=M*L` positions, keep the selected label and
   duplicate it into the unselected branch. The ABE2 selective challenge
   attribute can be chosen before that instance's setup: the fresh FHE tuple
   and garbling coins are independent of ABE setup. All other positions are
   produced locally. The relevant probability-gap charge is `J*eps_ABE2`.
2. [DERIVED] Simulate the single vector garbling at its actual selected
   concatenated input. Its true output is the vector of FHE decryptions,
   giving charge `eps_GC,vec`. Replacing that vector by `f(x)` adds
   `delta_FHE,vec`: couple the two experiments on the FHE correctness event.
3. [DERIVED] In the simulated-garbling view, replace the common-key encrypted
   input by encrypted zeros using n single-bit FHE hybrids. Neither a fresh
   challenge FHE secret key nor its real garbling is needed in this stage.
   The fixed public template determines all simulator sizes. Charge
   `n*eps_FHE`.

[DERIVED] The endpoint depends on the common vector `f(x0)=f(x1)` and public
padded bounds, yielding the author's probability-gap inequality:

```
gap <= 2*(n*eps_FHE + eps_GC,vec + M*L*eps_ABE2 + delta_FHE,vec).
```

[DERIVED] No garbling or ABE correctness loss belongs additionally in this
privacy inequality: their privacy games compare the actual primitive
distributions, including failures. FHE correctness is charged because the
simulator's supplied output changes. The final factor two is the two-sided
comparison with the common simulated endpoint. The note consistently uses
acceptance-probability gaps, not success advantage above one half.

[DERIVED] A reduction retains one `rho` and calls the terminal distinguisher
once. The hybrid index is classical. Averaging over locally sampled primitive
coins and uniform envelopes for the enlarged views does not clone advice.
This verifies the conditional lift's shape; it is not an independent
post-quantum proof of the classical primitives in the paper.

[DERIVED] The Boolean-garbling specialization is also valid under the stated
joint-side-record garbling contract. Independently garble M decryptors, expose
one input per garbling, and replace components successively. Shared FHE
secret/input records remain in the generator's side state. This gives
`eps_GC,vec <= M*eps_GC,bit` at the enlarged reduction resources, not free
reuse of one garbling on M inputs.

## 3. Correctness and cost

[DERIVED] Condition on correctness of all selected-label decryptions, the
single vector garbling, and all evaluated component FHE ciphertexts. The
output is then f(x). The union bound gives exactly

```
delta_vector <= delta_FHE,vec + delta_GC,vec + M*L*delta_ABE2,
delta_FHE,vec <= M*delta_FHE.
```

[DERIVED] Correlations among FHE outputs or shared FHE-key failures do not
invalidate these bounds. They remain fresh-instance guarantees. Uniform
all-input correctness, quantitative error rates, and actual reduction time
and advice envelopes are still separate premises. The author does not claim
otherwise.

[SOURCE: size proof] GKP printed p24 counts an ABE2 ciphertext at each garbled
input position, and Appendix B uses two ordinary ABE instances per ABE2
instance. Independently read GVW 2013/337 §6.1 printed pp16-17: one ordinary
ABE public key has `2h+1` TOR public keys; Enc selects one for each attribute
bit and emits h encodings plus its message mask. Its pinned PDF SHA256 is
`05b5f649f9cd52ab8fb87f5b6a61c90f8cbd7ac7ca7c6fe7228457f3a02030a4`.

[DERIVED] The direct substitution's full public key and ciphertext body are
therefore `2*M*L*K_A` and `2*M*L*C_A + Gsize_vec`, respectively, apart from
the explicitly excluded serialization overhead. Public Enc performs
`2*M*L` ordinary ABE encryptions and materializes the vector garbling.
The literal format contains `M*L` nonempty ciphertext components. Even their
output writes preclude an M-independent bound for this literal constructor.
The conclusion does not require proving a lower bound on arbitrary compressed
keys, packed FHE, or alternate randomized encodings.

[SOURCE: actual consumer] ABSV 2014/917 §4/Figure 2, printed pp12-14, makes
the shallow keyed function emit the entire randomized encoding of the target
function. It explicitly assumes multi-bit shallow FE. Its PDF SHA256 is
`3574f296f030d424c8cf3f818b947ff8e1a0a39c42f86737ec53cc346b3e7896`.
The frozen public-environment note requires total Enc work, including output
bindings and consumed randomness, within a fixed polynomial in
`(kappa,n,log S)`; that note and its source pins were independently reread.

[DERIVED] M may grow polynomially in the target size S. Calling M a
polynomial in kappa after fixing one family does not prove the required
uniform fixed-polynomial bound before selecting that family/size parameter.
The direct construction avoids a particular `Q*M` collusion amplification
but leaves precisely the public-Enc dependence that matters here.

[DERIVED] The two rejected shortcuts are correctly scoped. Moving the
garbling to prior KeyGen loses its dependency on Enc's fresh hsk and label
pairs. Reusing L label positions for several components supplies more than
one predicate key and potentially both labels per ABE2 instance. If two
components correctly decrypt to different bits, their ciphertext strings
must differ somewhere under deterministic decryption. At that coordinate
the hidden-label replacement cannot preserve both exposed branches. This
is a failure to meet the source game's premise, not a full cryptanalytic
break of every redesigned scheme.

## 4. Executed evidence and limits

[EXECUTED] From repository root:

```
python3 research/learn_infer_only/experiments/adversarial_review/direct_multioutput/review.py > research/learn_infer_only/experiments/adversarial_review/direct_multioutput/stdout.txt 2> research/learn_infer_only/experiments/adversarial_review/direct_multioutput/stderr.txt
```

[EXECUTED] Exit 0; stderr empty. `results.json` retains the source pins,
extraction argv/results, author-file hashes, and control counts. The finite
controls cover 3,634 opposite-output pairs across all Boolean decoders on
one through three input bits; 682 independent-label selection vectors;
the two-open-branches negative control; and 8,190 pointwise union-inequality
masks. These exercise the stated general arguments, not FHE/ABE/garbling
security or measured crypto performance. The equations above are justified
by the independent reasoning, not inferred from those finite examples.

[EXECUTED source access] Three local PDF extractions; zero web, Scry SQL,
Scry schema, Kagi queries or PDF downloads. `visual_access.json` records the
rendered source pages checked against the extracted algorithm. No
cryptographic, model, protected-output, or attack runtime was executed.

[DERIVED current-truth impact] No change to `docs/VERDICTS.md` is proposed.
In particular, the published positive Boolean succinct-FE depth theorem
is preserved. The note supplies a conditional vector extension and a scoped
cost finding; it supplies no field-wide refutation, absence claim, LWE-only
replacement theorem, or instantiated PQ resident.

[OPEN resume] The first remaining construction obligation is compact
public encoding of the whole vector interface with a matching quantitative
security/correctness proof. A genuinely packed/encoded alternative must price
the full encoder, its output and effective key dependency. This completed
review need not be repeated unless the author note or primitive contract changes.
