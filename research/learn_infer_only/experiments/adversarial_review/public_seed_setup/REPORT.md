# Independent audit of the public-seed setup game

[DERIVED — accepted with the stated scope] No blocking algebraic or game-reduction error was found in the frozen [proposal](../../private_construction/designated_span/public_coin_setup/public_seed/PROPOSAL.md), SHA-256 `ec9af914cb349e0bc6881bd8a5b99fd493e43b106a869a44eb58edf758083ab3`. Its conditional classical programmable-ROM bound is supported by the joint distribution argument and the existing fixed-span DDH reduction:

```
Delta <= 2 M N epsilon_DDH + 2 min(1, Q_pre / q^m).
```

[DERIVED — exact accepted game] This acceptance requires a fixed full-row-rank policy `Y`, `1 <= m < d`, a static exposed recipient subset, fresh independent honest recipient scalars, and one complete authenticated registry fixed before seed grinding. The adversary has bounded classical oracle access, selects one setup seed, and receives adaptive LR replies only under that selected valid key. Each submitted pair agrees on the exposed projection span; invalid pairs and failed selected setups use the common output-zero rule. `N` is chosen from a public, ex-ante polynomial bound on first-touched seed candidates through selection, including verifier insertion of an unqueried selected seed. `M` is the padded power-of-two bound for `T * (d-rank(Y_J))` ordinary DDH hybrids. Both factors price the actual reduction resources; this is not a numerical DDH-security estimate.

[SOURCE — inspection] This audit read the proposal's complete statement and proof, its public finite witness script/log, the frozen direct-sampling setup review, the designated-span review through its bounded-bit correction, and the general fixed-span proof. The exact dependencies appear in [source_pins.json](source_pins.json). The proposal author's additional prior-art and local PDF pins were checked for integrity only; this audit does not independently certify their literature claims. No author, companion, root-ledger, runtime or private artifact was edited. No cryptographic backend was run. This is a source/math audit with finite distribution checks, not a Lean proof.

## Joint recipient-key and setup law

[DERIVED] The crucial fact is stronger than uniform marginal setup values. In pivot coordinates the linear map

```
s -> (Y s, s_free)
```

is bijective because `Y_pivot` is invertible. Therefore an ordinary uniform master `s` induces independent uniform `H=g^(Y s)` and `h_free`. For independent uniform `tau*`, define the mathematical recipient vector `a=Y s-tau*`. The map `(Y s,tau*) -> (a,tau*)` is bijective. Independent random signs on roots of `h_free` then give independent uniform `(a,tau*,U*)` on `F_q^m × F_q^m × (F_p*)^(d-m)`. Conditional on the displayed registry `A=g^a` and exposed `a_J`, all target values `(tau*,U*)` remain product-uniform. The simulator computes only the exposed scalars as `K_J-tau*_J`; it needs no undisclosed logarithms. This validates proposal lines 145–160, including joint disclosure rather than a marginal-only argument.

[DERIVED] For any `B` in the order-`q` subgroup, `B^((q+1)/2)` squares to `B`. The two roots are distinct because `p` is odd and `B` is nonzero. Choosing their sign fairly reproduces the conditional uniform preimage, including both roots of the identity. A deterministic sign would have half the required support. Pivot completion recovers the supplied `h` whenever all target tapes accept, and the recipient projection is exactly `a_i+tau_i`; no target-dependent completion ambiguity remains. See proposal lines 89–101 and 124–127.

## Whole raw tapes, first touch and selected-seed identity

[DERIVED] The finite-tape lemma in proposal lines 129–143 is exact. For a successful output tape whose first accepted value is `v`, exactly `|S|` possible original accepted words are overwritten, while the target must be `v` with probability `1/|S|`. For an all-rejected tape, every target leaves its unique original tape unchanged. Both cases yield the same probability `2^(-ell R)` for each output tape. The all-fail indicator is independent of the target. This establishes the law of raw oracle words, including rejected prefixes and later accepted words, rather than only the law of the extracted field element.

[DERIVED] Initializing every finite coordinate tape at a candidate's first relevant query supports partial, out-of-order and out-of-cap access: there is no already answered word in that candidate domain to change. Unused suffix bits in the common-width oracle convention are independently uniform. Other candidate tapes depend on the fixed registry and fresh independent bits. Consequently their adaptive history reveals no latent target information beyond the registry before target first touch. This supplies the stopping-time argument at proposal lines 162–183. It depends on injective domain encoding and the complete registry bytes; a concrete digest substitute would need a separate argument.

[DERIVED] For each fixed guessed ordinal `i`, restrict attention to successful selection with `S=i`. The joint registry/oracle view has the real law on that event, and its completed key is the ordinary challenger's key. Forwarding LR requests therefore supplies the real continuation law even when the seed was selected for an unusual or exploitable visible property. On other selection events the simulator returns zero. Thus, for each LR bit,

```
Pr[B_i=1 | b] = Pr[A=1 and S=i | b].
```

[DERIVED] Summing these disjoint events and averaging before taking absolute values gives exactly `Delta/N` for the ordinary IPFE distinguisher. The proof does not require selected seeds or selected setup values to be uniform. An unqueried chosen seed acquires its final ordinal during verification; padded guesses always return zero. Queries after selection remain part of the simulation and resource bound but do not create further deployment choices. A candidate bound chosen retrospectively from the realized transcript would not justify the stated preselected uniform guess; the proposal's term “bound” is read as the ex-ante maximum specified in the game.

[SOURCE/DERIVED] The general fixed-span dependency, [GENERAL_FIXED_SPAN.md](../../private_construction/fixed_span/scaling/GENERAL_FIXED_SPAN.md), lines 64–140, randomizes all `k_J` kernel masks for each selected adaptive request. The fully randomized joint mask law removes any admissible message difference in `ker(Y_J)`. Its fair hidden-bit success test, telescoping over requests and kernel coordinates, and dyadic padding produce event gap `Delta_IPFE/(2M)`. Composing the two signed averages gives the claimed factor `2MN`; it does not require favorable-sign hybrid advice. Common invalid-pair behavior and the treatment of unreached requests remain necessary. `T=0` has zero endpoint gap; `k_J>0` follows here from `rank(Y_J) <= m < d`.

## Pre-registration queries and sampling cutoffs

[DERIVED] Condition on any pre-registration oracle transcript and independent auxiliary state. The complete fresh registry is uniform on `G^m`. An injectively encoded earlier query names at most one full registry vector, so a union bound gives `Pr[Bad] <= min(1,Q_pre/q^m)`. This argument survives disclosure of all recipient scalars at registration: those scalars were not available to the prehistory. It fails for correlated, selectively redrawn or substituted keys, all of which the proposal excludes. Full-rank policy, seed, cap, domain and registry chronology are part of the audited game, not inferred guarantees of an implementation.

[DERIVED] In the modified game that aborts on `Bad`, the simulator can detect the event from stored prequeries and the displayed registry. Conditional target uniformity still holds given that registry and prehistory, so the selected-event reduction applies to the abort game. Coupling its two endpoints to the original game adds at most twice the bad-event probability. Applying this coupling outside the seed guess is why the prequery term is not multiplied by `N`. Proposal lines 227–239 give a conservative valid bound.

[DERIVED] Public acceptance is exact rejection sampling with a fixed cap: `tau=0` is valid, `U=0` is rejected, and `U=±1` is valid. The single-fresh-candidate failure formula and union bound in proposal lines 103–120 are correct. A selected candidate may be deliberately biased or failed. Because failed tapes have the exact real law and a selected failure gives common output zero, the public failure probability `f_R` is not an additional privacy error.

[DERIVED] The reduction's own bounded scalar sampling is a separate approximation. With the dependency's conservative draw count and the additional `m` target-tau draws, `delta_red=(d+k_J+T+m)2^(-S_cap)` is a valid per-DDH-world coupling budget. Replacing `epsilon_DDH` by `epsilon_DDH+2 delta_red` gives the stated strict bounded-bit variant. This does not assert that a concrete endpoint implementation, parser, CSPRNG or timing trace has the ideal distribution. Root signs and public finite oracle tapes themselves use bounded fair-bit draws exactly.

## Independent finite evidence and falsifiers

[EXECUTED] The independent [finite_review.py](finite_review.py) uses public integer arithmetic and exact counters. The command was run from the research repository:

```sh
python3 research/learn_infer_only/experiments/adversarial_review/public_seed_setup/finite_review.py > research/learn_infer_only/experiments/adversarial_review/public_seed_setup/finite.log 2>&1
```

[EXECUTED] It exited zero. [finite_results.json](finite_results.json) and [finite.log](finite.log) retain the output. The final script also checks the frozen author manifest and dependency hashes before its finite checks. The author's script was inspected, not executed by this audit.

| Independent check | Exact result |
| --- | --- |
| Tape lemma for three acceptance sets and caps 1, 2, 3 | Every output tape has exactly `|S|` equally likely preimages; accepted-zero, rejected-zero, noninterval sets and all-fail tapes included |
| Rank-two policy `Y=[1 0 1; 0 1 1]` over `F_3`, group `QR_7` | Real/simulated joint laws agree on 486 atoms, including conditional uniformity with a scalar exposed |
| One-recipient, cap-two full raw tapes | 55,296 simulator choices give all 3,072 real registry/tape transcripts with exactly 18 preimages each; failure is `31/256`; every success recovers its supplied key |
| Adaptive three-seed, cap-one experiment, `N=4` | First `U` answer chooses the second touched seed; selection can force verification of an unqueried third seed; every selected-success ordinal has the exact real joint transcript law |
| Three real selected-ordinal counts among 98,304 choices | `18,432`, `44,928`, `19,656`; all positive; `15,288` common failures; padded ordinal four always aborts |
| Sum over selected events versus uniform guess | Success probability `3459/4096`; guessed-success probability exactly `3459/16384` |
| Complete two-recipient prequery guesses | Exact bad probabilities meet `min(1,Q_pre/9)` for distinct guesses and remain capped under duplicates |
| Witness and falsifiers | Distinct `(0,0)` and `(1,2)` have equal `Y=(1,1)` projection; deterministic roots have support 3 versus 6; two-candidate identity selection changes `1/3` to `5/9` |

[DERIVED — evidence limit] The finite adaptive experiment compares the full recorded registry/scalar/query/selection/completed-key view on each selected event; it does not enumerate LR ciphertext continuations or establish DDH hardness. Those continuations use the source-level reduction above. The small field witnesses inhabit the algebraic and game premises and demonstrate positive selected-success events. They do not supply cryptographic security at the toy parameters.

## Accepted scope and remaining boundaries

[DERIVED] No correction to the frozen mathematical proposal is requested. The accepted improvement is a reduction for an adversarially selected public seed in the explicitly defined classical programmable-ROM experiment. Honest independent recipient registration remains an assumption; selected values may be biased. The result preserves fixed-coalition, per-input projection-span privacy for one selected setup and adaptive valid LR histories.

[OPEN] No claim is established here for QROM, a concrete hash/XOF, key possession or authentication transcripts, actual timing or internal state, malicious or adaptive registration/corruption, additional deployed LR keys, secret oracle-correlated advice, concrete parsing/serialization, selected-answer-only release, revocation of retained projections, nonlinear learning, or semantic ambiguity of application inputs. Those are excluded or separate obligations, not closure supplied by the `2MN` reduction. No new crypto/runtime experiment or private-file inspection was performed.
