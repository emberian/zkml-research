# Review of the parent-bound private-ingress candidate

[DERIVED decision; 2026-09-07] The saved candidate does not currently have a
source-backed H=2 privacy proof. Its natural future-state ciphertext hybrid
fails the actual rMIFE compatibility condition: one exposed observation-slot
encryption key permits a replacement observation that accepts in the left
world and rejects in the right world. The probability gap is 1 for an
observable failure branch. This is a scoped rejection of that application of
the theorem, not an impossibility of private ingress or a cryptanalytic break.

[DERIVED correction] The frozen provenance note's ciphertext-event lower
bound omitted fresh randomness inside the encrypted payload. The corrected
bound is `2^(-rho-lambda_next)`, not `2^(-lambda_next)`. An explicit fixed-width
premise still gives an epsilon obstruction at equal parameters. The stronger
parent-replacement obstruction needs no ciphertext-size or coin-count premise.
The frozen artifacts remain unchanged; §5 below is their correction addendum.

[DERIVED conditional positive] The existing single-input H=2 ladder does
support an initially private input followed by public learning, under its
classical, selective-state rFE assumption and honest erasure. Its full exposed
future package is included in the proof. This does not combine two separately
encrypted, unknown ongoing inputs, or prove the additional provenance guard.

## 1. Reviewed object and exposure

[SOURCE: local candidate read] The object under review is exactly
[`../provenance/PROVENANCE.md`](../provenance/PROVENANCE.md), §1. A state slot
contains `w=(s,r,H)`. An observation slot contains
`z=(x,G,epoch,C,pi,auth)`. The public proof certifies descent of C from fixed
genesis G under the selected policy. Inside the issued F, verification checks
that proof, the exact opening equation `Com(s;r)=C`, and the observation's
authorization. F computes Step, freshly commits to the next state, extends
the private bounded history, proves the new statement and encrypts the next
`(s_next,r_next,H_next)` under an independent next-layer state key. It returns
that ciphertext, public commitment/proof and the restricted answer.

[DERIVED scope] Keep H=2, one common actual genesis, deterministic Step,
honest FE/proof setup and complete erasure of raw masters, raw decryption/PRF
keys, unprotected key-program copies and setup coins. Expose every deployed
FE public/encryption key, every issued transition/terminal key, all public
proof/commitment parameters and metadata, all snapshots and all observation
ciphertexts. Observation issuers know their own observations; secrecy against
a corrupted issuer never includes a value it already knows. The particular
replacement counterexample needs only the observation-slot EK to be exposed.
No state-slot EK, terminal key or proof trapdoor is needed for that finding.

[DERIVED serialization premise] Source F has a fixed output length. The saved
`require` statements must therefore be totalized. For this review, failure is
a reserved public failure encoding; success has a different public tag and
the padded output tuple. This captures an observable error, missing output,
or distinguished success/failure format. It is consistent with the resident
game's explicit failure leakage. If an implementation instead encrypts and
hides the guard result, §3's success-bit test no longer applies directly.
That would be a changed candidate requiring a separate closure and leakage
proof; a publicly invalid next proof could still reveal failure. We do not
assume access to a future key that reads a hypothetically hidden failure bit.

[DERIVED local completeness correction] The displayed guard verifies pi and
the state opening, but never checks that the supplied private H is a witness
for the same relation. A caller who supplies a known valid `(s,r)` can replace
H by garbage, pass those checks and make `Extend/Prove` operate on an invalid
witness. The bounded H=2 circuit can check `Relation(G,policy,epoch,C;H)` inside
F before extending it. This preserves honest evaluation and the counterexample
below. The executable control is a semantic guard check, not a claim that an
attacker can recover an unknown opening or malleate an actual ciphertext.

## 2. The exact source condition

[SOURCE: complete definition reread] Datta–Guan–Korb–Sahai,
[(Multi-Input) FE for Randomized Functionalities, Revisited](https://eprint.iacr.org/2025/330),
Definition 4.3, printed/PDF pp.22–23, takes n slots, q challenge rows and a
set I of exposed encryption slots. For every subset `U ⊆ I`, every replacement
plaintext `z_U`, every independent choice of stored-row index `j_t` for each
non-replaced slot, and every issued f, compare the randomized output laws:

```text
Y_b = f( z_U, {x^b_(t,j_t)}_(t outside U); fresh coins ).
advice = (f, U, z_U, {x^0_(t,j_t)}_(t outside U)).
Pr[A(advice,Y_0)=1] - Pr[A(advice,Y_1)=1] <= epsilon.
```

[SOURCE] The replacement is the **same plaintext in both worlds**. The
advice contains the replacement itself and the left-world non-replaced
plaintexts. The comparison is not limited to pairs of honestly issued
observations on matching stored rows. Definition 4.4, p.23, permits adaptive
encryption-key, challenge and function-key queries; its I is precisely the
set of encryption keys requested. The experiment only credits distinguishing
queries that satisfy this compatibility premise. Construction 2, pp.48–49,
gives a real publicly usable per-slot encryption key and an obfuscated issued
function key. It does not remove the replacement condition.

[DERIVED notation] For the present two slots S and O, the four kinds are:

| Replaced slots U | Comparison that must hold |
|---|---|
| empty | All stored state/observation row combinations in the two worlds |
| O | The same arbitrary observation against each challenged state |
| S | The same arbitrary state against each challenged observation |
| S,O | No challenged coordinates remain; the inputs agree |

[DERIVED] If only O is exposed, the empty and O rows still apply. Supplying
the replacement plaintext in this game does not require stealing a secret
authorization key: a valid already-produced left-world observation packet
is a sufficient witness. This is a mathematical challenge-admissibility
condition. Its quantifier is stronger than the real host's ability to guess
an honestly hidden state opening.

## 3. A satisfying honest pair and an incompatible replacement

[DERIVED proposition: source-application obstruction] Fix a common function
F and global parameters. Let `w_0=(s_0,r_0,H_0)` and `w_1=(s_1,r_1,H_1)` be
valid descendant states, with distinct parent commitments
`C_b=Com(s_b;r_b)`. Let `z_0` be any actual authorized observation packet for
`(G,epoch,C_0,pi_0)` such that F's guards accept `(w_0,z_0)`. If O belongs to I
and success/failure is observable, the state challenge pair is not
epsilon-I-randomized-compatible for any `epsilon < 1`.

[DERIVED proof] Choose `U={O}`, its single replacement `z'_O=z_0`, and the
stored state index holding `(w_0,w_1)`. In world 0 every guard accepts. In
world 1 the equality check compares `Com(s_1;r_1)=C_1` to the **unchanged**
parent C_0 inside z_0 and fails because `C_1 != C_0`. Let A read the public
success tag. Its two probabilities are 1 and 0, independent of F's output
encryption, commitment or proof coins. This A uses no extra auxiliary key.
The left proof is true and already valid; no false-proof simulation, extraction,
or forged authorization appears in the proof. For randomly generated proof
parameters with imperfect completeness, condition on the valid accepting
packets; efficiently produced valid packets give the corresponding near-1
gap, still far above the source epsilon.

[DERIVED honest nonvacuity example] Use byte state, common genesis 0, first
transition `Learn(x):s <- s+x mod256`, and a second private Learn followed by
the restricted high-bit read. In the two worlds, the first unknown observation
is 0 or 1. They produce states 0 or 1, freshly committed with different C_0
and C_1 and true descent histories. The next observation is 0 in each world,
authorized for its own world-specific parent. Both honest executions accept,
retain different states and have the same answers `ACK, ACK, 0`. Both private
state and a separately supplied unknown observation can be present in the
syntax. This is a semantic honest-path pair, not a proved full-cryptographic
challenge pair: privacy of the joint public commitments/proofs is still open.

[EXECUTED] `audit.py` constructs two such coupled stored rows, with state
pairs `(0,1)` and `(2,3)`. For all four state/observation row combinations,
the success matrices agree: diagonal pairs accept in both worlds; off-diagonal
pairs reject in both. This positive control rules out confusing ordinary
cross-row testing with the decisive replacement. The single left-parent
replacement gives `[accept,reject]`; the both-replaced row agrees. A separate
fixed-parent control uses two different observation values and the same state:
its guard projection agrees under all four tested state replacements. These
are exact ideal-registry facts, not randomized-MIFE compatibility proofs.

[DERIVED distinction from a target attack] In the actual target experiment
the public metadata is C_b, and a host need not know both `(s_b,r_b,H_b)`
or the unused world's commitment. The source game's challenge chooser does
know the candidate plaintexts, and its compatibility advice explicitly
provides the left one. The above test therefore rejects the naive FE hybrid;
it does not show that the deployed host can recognize b from its actual view.
Conversely, merely showing equal honest answers and matching stored-pair
acceptance matrices cannot establish this source theorem's premise.

[DERIVED binding qualification] Perfect binding rules out distinct openings
to different states under one fixed commitment. Computational binding rules
out an efficient algorithm producing such a double opening with nonnegligible
probability under honest parameters; it is not a statement that two openings
cannot mathematically exist. For efficiently generated honest distinct-state
pairs, finding `C_0=C_1` together with both openings would violate that binding
condition. A perfectly hiding, computationally binding commitment must not
be treated as having disjoint support merely from the word “binding.” The
proposition itself only assumes the actual C_0 and C_1 are distinct.

## 4. Attempted H=2 hybrids and their first unsupported steps

[DERIVED proposed joint view] A privacy proof must handle one joint law,
including every already issued prior and future function key:

```text
(global parameters, all deployed packages P0,P1,P2,
 public C0,pi0,C1,pi1,C2,pi2,
 all state/observation ciphertexts and all allowed evaluation results).
```

[DERIVED] The actual prior key programs contain the future encryption-key
literals used by F. Ignoring those programs or taking a marginal distribution
of next ciphertexts is not an acceptable hybrid. Source Definition 4.3's
stated advice is not itself a theorem allowing any correlated future-key
package to be added. Here the obstruction is stronger: it already works with
the source's stated advice and no additional future key.

| Attempted transition | Premise or failure |
|---|---|
| Fix C_0,pi_0 and switch encrypted `w_0` to `w_1` | With a fixed left-parent observation, the direct opening guard changes accept to reject. This is §3. |
| Switch both state and observation plaintexts in one rMIFE challenge | Honest diagonal pairs accept, but `U={O}` still fixes a valid left-parent replacement. Same gap 1. |
| Hide C inside the observation slot and publish no C | The source replacement/advice rule still applies to the encrypted observation plaintext. Issuer access to the intended parent also needs a defined protocol. |
| Change C,pi outside FE, then switch the ciphertext | Commitment hiding and proof ZK must remain true jointly with encrypted openings and all exposed evaluation keys. No inspected source supplies that composition. |
| Keep one C by giving both worlds an opening | Under honest binding parameters this is not a general challenge sampler; an equivocal mode needs its own justified mode switch. |
| Change hardcoded genesis G with the world | This changes F itself. Ordinary FE message privacy does not compare those function-key descriptions, and ordinary iO does not identify differing genesis guards. |
| Withhold the observation-slot EK | Removes this exact U={O} row, but changes the required public input-issuance capability and needs a full issuer-corruption audit. It is not the saved public-ingress construction. |
| Withhold only the state-slot EK | Leaves O exposed, so §3 still applies. |

[DERIVED source-conditioned reduction schedule] A direct backward proof
would first establish privacy of the terminal state package, then use it to
justify joint outputs of F_1, and finally justify F_0 with the entire future
package exposed. At the F_1 application, both descendant-state challenge
messages can be selected before that instance's setup in the example above;
the incompatibility therefore does not depend on late selection. The F_1
function's internal parent guard already fails the actual rMIFE condition.
There is no legitimate “apply Theorem 6.1” step after this point, even if
all later output-hiding obligations were separately assumed.

[OPEN exact missing premise] A different proof would have to change the
commitment/proof/FE representation jointly while preserving all usable
guard behavior and all exposed key programs. If it uses dual-mode commitments,
name the honest binding mode and simulated equivocal mode; show their joint
indistinguishability with the FE package; construct the required openings
and proofs; and show that later validity checks remain meaningful after the
simulated transcripts. Alternatively, name a different source game that
proves distributional security while opening-guess probes are allowed. Neither
premise has been instantiated by the four primary texts reviewed here.

[DERIVED trapdoors and authority] A simulator's trapdoor can exist only in
the reduction without becoming a deployed capability. If an exposed trapdoor
actually certifies false provenance or equivocates the parent to arbitrary
states, audit its coalition with the observation and transition keys. If it
extracts the hidden history from public proofs, it can be a reader. These are
conditional capabilities, not generic properties of every ZK simulator or
extractor. An unrestricted state signer similarly restores chosen certified
states in an ancestry-only design, but does not by itself change the immutable
parent inside an unknown observation. The earlier signing attack was correctly
scoped without that parent binding. Public Prove is not such a signer: it
requires a valid witness under the proof system's soundness assumptions.

## 5. Correction addendum: payload randomness and epsilon

[REFUTED: frozen counting argument] The inherited `>=2^(-lambda_next)`
claim in frozen `PROVENANCE.md` §5 does not follow for its augmented payload.
Fix honest accepted challenge inputs and suppose their deterministic next
state components differ. Let rho be the number of fresh random bits in F
that alter the plaintext encrypted for the next layer. In the displayed
candidate, these are the fresh next-commitment opening bits: H_next includes
that opening. Public proof coins do not enter the encrypted payload in this
layout. If another layout includes them, rho must include them too.

[DERIVED corrected event] The source's next-layer state EK contains the
first PKE public key. Given f and the left plaintext inputs as Definition 4.3
advice, choose the all-zero payload-affecting coins and compute their next
payload `m*_0`. Form `c*=PKE.Enc(pk_next^0,m*_0;0^lambda_next)`. Let A test
whether F's returned next ciphertext has first component c*. In world 0,
simultaneously choosing those rho payload bits and lambda_next first-PKE
coins has probability `2^(-rho-lambda_next)`. Additional collisions could
increase it. In world 1, every next payload has a different state component;
perfect PKE correctness excludes the same first ciphertext for any such
plaintext. The right event is zero. This is a test on the **ideal randomized
function outputs** in compatibility, whose coins are fresh and uniform.

[SOURCE] Construction 2, pp.48–49, samples each component PKE encryption's
coins from `lambda` bits. Definition 3.8, p.18, requires perfect correctness.
Theorem 6.1, p.50, gives compatibility threshold
`epsilon_i=2^(-2*n*s_i-lambda_iO)`; §6.1 sets `lambda_iO=lambda_i`, and n=2
here, hence `epsilon_i=2^(-4*s_i-lambda_i)`. These statements are from the
locally pinned [2025/330](https://eprint.iacr.org/2025/330) PDF.

[DERIVED fixed-width corollary] Suppose adjacent commitments use the same
opening width rho, and the current state slot contains its rho-bit opening.
Then `rho <= ellX_i`. Perfect correctness for all ellX_i-bit plaintexts with
fixed s_i-bit ciphertexts entails `ellX_i <= s_i`: distinct messages have
disjoint nonempty ciphertext supports. At equal PKE parameters,
`lambda_next=lambda_i`, so for positive s_i,

```text
rho + lambda_next <= s_i + lambda_i < 4*s_i + lambda_i.
```

[DERIVED] The corrected event still exceeds epsilon in that fixed-width,
equal-parameter application. If next-layer payload randomness or security
parameters grow enough, this particular inequality may fail. A necessary
condition merely to evade this event is
`rho+lambda_next >= 4*s_i+lambda_i`; it is not a sufficient compatibility
proof. The parent-replacement gap from §3 survives all such parameter choices.

[EXECUTED falsifier] The coin-count control chooses rho=2 and first-PKE
coin length 3. Its injective tuple output has fixed-event probability 1/32,
not 1/8, and probability zero in the other state. This finite example
falsifies the omitted-payload-coins counting step. It implements no encryption
and supplies no claim of CPA security.

## 6. Which actual composition results were checked

[SOURCE: compiler and privacy hybrids reread] Badertscher–Kiayias–Kohlweiss–Waldner,
[Consistency for Functional Encryption](https://eprint.iacr.org/2020/137),
§6.1, Figures 14–15 and Theorem 6.2/Lemmas 6.3–6.4, printed pp.28–32
(PDF pp.30–34), has a genuine FE+NIZK privacy argument. Its proof simulates
the CRS/encryption-range proofs, switches the base FE challenge, and restores
honest proofs, with bound `2 Adv_ZK + Adv_FE`. The compiler returns the
unmodified base function key. The proved statement is membership in the
base encryption algorithm's range.

[DERIVED source boundary] Putting the range proof around the saved candidate
does not establish base-F compatibility; that is precisely the premise needed
at the middle FE switch. Putting the entire parent guard only in the wrapper
allows the exposed base key to bypass it. Putting the guard inside F returns
to §3. This compiler does not perform a public parent-commitment switch while
simultaneously changing the opening consumed by F. Its theorem is positive
within its actual scope; it is not the missing joint guarded-state theorem.

[SOURCE: games and construction theorem reread] Badrinarayanan–Goyal–Jain–Sahai,
[Verifiable Functional Encryption](https://eprint.iacr.org/2016/629),
Appendix D, Definitions 12–14, pp.35–37, defines verifiable MIFE and requires
exact output equality for every stored/replaced input combination. Appendix G,
Definition 15 and Theorem 8, pp.54–56, gives a selective deterministic
construction for the special family Feq, assuming iO, one-way permutations,
perfectly sound NIWI and perfectly correct PKE. Feq requires suitably short
witnesses of equivalence for partially fixed residual circuits.

[DERIVED source boundary] Verifiability does not waive the exact mixed-input
privacy restriction. The accept/reject pair fails that restriction too.
Treating the fresh output-encryption coins as deterministic inputs would
change the slots/exposure game and cannot be imported as a randomized theorem.
No Feq membership proof or matching randomized composition theorem was
constructed here. We did not use the abstract's general compiler claim as
an unrestricted two-input randomized-state theorem.

[SOURCE / DERIVED corpus boundary] The fourth primary source is the old
single-input randomized-FE theorem used in §7. The above absence conclusion
is limited to these four locally pinned PDFs, the cited definitions,
constructions and selected proof steps, read with `pdftotext`, `rg`, and `sed`.
It is not a new literature-wide absence claim. The older provenance tranche's
additional predicate/robustness papers were not independently re-audited here.

## 7. Initial private input, followed by public learning

[DERIVED exact narrower statement] Fix a public deterministic initializer
`Root(x)` and the public command circuits before all FE setup randomness.
Choose distinct private input values x_0,x_1 for which
`R0(Root(x_0),Root(x_1))` holds in the existing H=2 public-command relation.
Generate the three independent FE packages backwards, erase every raw master,
and let the initial issuer publicly encrypt `Root(x_b)` under pk_0. After it
erases x_b, the root and encryption coins, the host receives every deployed
public key and every issued function key. Subsequent observations/commands
are public. No live master or reader is needed to issue this one root.

[SOURCE] Goyal–Jain–Koppula–Sahai,
[Functional Encryption for Randomized Functionalities](https://eprint.iacr.org/2013/729),
Definition 2.4, pp.7–8, places the message pair, functions and auxiliary state
before the current instance's setup and requires joint computational
indistinguishability of `(st1,{f(x_0)})` and `(st1,{f(x_1)})`. Lemma 2.9, p.9,
and Theorem 4.1, p.14, yield the stated IND_pre primitive from the paper's
1-SIM construction under iO and one-way functions. The complete cryptographic
reduction is source-assumed, not re-proved in this tranche.

[DERIVED precise backward proof] Write P_i for the entire package from layer
i onward, including every issued future key. At the terminal layer,
`g(u)=g(v)` gives exact compatibility. At layer 1, A1 generates P_2, sets
`st1=P_2`, and chooses all
`F_1,c(s;r)=(Enc_2(pk_2,T_c(s);r),a_c(s))` before Setup_1. Equal answers and
terminal relatedness give joint compatibility of all these outputs using
one common P_2. A standard finite ciphertext hybrid switches the independently
encrypted child messages one at a time, publicly encrypting the remaining
known candidates under that same key/package. Layer 1's source theorem then
provides privacy with its own keys exposed. Repeat with `st1=P_1` and the
F_0,c functions before Setup_0. Current-layer keys are delivered by the source
game after its setup; they are not silently put into an impossible pre-setup
auxiliary state. This is the proof already recorded in
[`../../private_construction/FINITE_LADDER.md`](../../private_construction/FINITE_LADDER.md).

[EXECUTED distinct positive and falsifier] Taking `Root(x)=x`, x_0=0 and x_1=1,
with public commands add-one, double and high-bit infer, gives equal complete
fork trees for two commands and terminal high-bit read. The independent
check covers all nine command paths and all 256 roots; it reproduces 14
behavioral classes, with the class containing 0 equal to 0 through 31.
The roots 63 and 64 have distinct trees and are rejected as a challenge pair.
Raw private state persists and updates are nonconstant; the positive is not
a constant-output encoding or identical-state witness.

[DERIVED limits] The input pair must be selected independently of all FE
parameters even if actual encryption occurs later. If an issuer retains the
sole initial secret, it can replay every later deterministic public update;
privacy against its later exposure requires the stated erasure, or excludes
that already-known value from the privacy objective. This candidate has no
ongoing input privacy, unbiased developmental-randomness guarantee, QPT claim,
malicious-setup guarantee, finality, or source-proved binding-genesis wrapper.
Adding the frozen proof/commitment guard to it would reintroduce the §4
hybrid obligations. It cannot be called a solution to fresh private ingress.

## Status and reproducibility

[DERIVED status] Freeze this as a completed scoped review. The saved
parent-bound syntax still illustrates a capability repair, but none of the
reviewed source theorems proves its full private-state/private-input closure.
The first explicit failed application is the exposed-observation-slot
compatibility row. The initial-private-input/public-learning specialization
is the available source-conditional positive.

[OPEN next] A subsequent cryptographic attempt needs an actual joint
representation/composition lemma overcoming §3–§4, with a nonidentical
same-genesis distributional challenge, full exposed package and all allowed
input-slot replacements. Repeating the same ordinary FE switch or increasing
epsilon parameters does not discharge that obligation. The practical public
BFV/authority/full-key-reader lane remains a separate useful construction.

[EXECUTED] Run `python3 research/learn_infer_only/experiments/private_ingress/provenance_review/audit.py`.
The exact command, Python version, program SHA-256, structured results and
complete stdout are in `results.json` and `audit.stdout.txt`. The models are
ideal registries and finite counts; no encryption, commitment, signature,
proof system, or obfuscation is implemented. `source_manifest.json` pins the
four PDF/extract paths, SHA-256 values, exact reading scopes and comparisons
to frozen manifests. `frozen_hashes.json` records the prior artifacts without
editing them.

[EXECUTED search accounting] This review used zero Scry SQL/schema queries,
zero Kagi queries, zero web search queries, four HTML metadata opens at the
four cited eprint landing pages, and zero PDF downloads. All theorem evidence
comes from existing local mirror PDFs/extracts, checked against the frozen
source hashes. Prior ingress/provenance query counts are unchanged.
