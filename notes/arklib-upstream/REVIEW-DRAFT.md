# Review draft: ArkLib #1274 → #1277 → #1283 (state restoration → Fiat–Shamir)

For ember to post or not; nothing here has been posted. It is written as one review comment on #1277
(the FS headline), referencing the stack. Basis: PR heads fetched read-only on 2026-11-06
(`pr-1274` fc626459b, `pr-1277` 3371c7a5f, `pr-1283` 2c7809a97) and `main` 34613d617.
Cross-model: gpt-6-astra attacked the merged base theorem (GROUNDING.md, "Cross-model check 1");
its acceptance-test caveat is finding 1 below. GitHub handles are written without the at sign.

---

## Comment (paste below this line)

Thanks for this stack. I read the headline statements of #1274, #1277 and #1283 against
Canetti et al. (STOC 2019), BCS (TCC 2016-B), Chiesa–Yogev's textbook, and WARP (ePrint 2025/753,
Thm B.4). We have an independent formalization of the same RBR → state-restoration → FS route in our
own Lean library, in a much narrower game (deterministic adversaries over finite coins). This stack
is strictly more general than ours: adaptive and interleaved coins, fresh-key accounting, early
rejection, and per-round errors. We are now deriving our theorem from your merged
`restored_extraction_bound` instead of maintaining our own. The certificate translation is done:
our WARP Def 4.1/4.2 instances satisfy `IsProverPreserving` and `IsLocallyBounded`, and your
`badChallenge` is literally our per-round event. So the comments below come from someone who wants
this merged.

### 1. No acceptance client exercises an adaptive restoration (concrete gap, proposed test)

The merged clients run the theorem at `Q = 0`
(`ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean`, `actual_game_bound`, pure adversary)
and at `Q = 2` with a non-adaptive adversary. That second adversary queries one key twice, discards
both answers, and returns a fixed selection (`StateRestorationBudget.lean`, `adversary`, lines ~229–233).
#1274, #1277 and #1283 add no `ArkLibTest` files. Nothing therefore exercises the defining move of
state restoration: **selecting the transcript after seeing an oracle answer.**

All current tests are upper bounds, so they cannot detect a regression in that move. Suppose a
refactor broke the cache handoff, so that completion resampled instead of reading the adversary's
cached answers. Every bad-event probability would drop to at most the single-shot error, and every
existing `≤` test would still pass. The CONTRIBUTING guidance to "exercise a boundary or a necessary
hypothesis when that distinguishes the intended statement from a weaker one" applies here.

Proposed client (one round, so it stays small):

- `Message := Fin 8`, `Challenge := Fin 8`. Knowledge states as in the existing client, with the
  challenge-node state `challenge = 0 ∧ witness ≤ message`. Then `badChallenge ↔ challenge = 0`, and
  `IsLocallyBounded` holds at `error = 1/8`.
- Adaptive adversary, `Q = 2`: query `Key.here 0 0 ()`. If the answer is `0`, select message `0`.
  Otherwise query `Key.here 0 1 ()` and select message `1`. Return witness `6` (so the extracted
  `6 + message` fails `≤ 0`, as in the existing client).
- Assert both:
  - the theorem's bound, `Pr[bad] ≤ (2 + 1) * (1/8) = 3/8` (and `Q·max ε + Σε = 3/8` for the
    nonuniform/stopped forms);
  - **the exact value `Pr[bad] = 15/64`** (`= 1/8 + 7/8 · 1/8`), strictly above the single-shot
    `1/8`. This equality is the regression detector: it is false for any game in which completion
    does not reuse the adversary's cache.

A stopped-game variant for #1274 is the same adversary with a guard that rejects message `1`. The
exact probability then drops to `1/8`, which tests that a rejected prefix makes no challenge
query and contributes no charge. A single-salt FS variant for #1277 puts the same selection behind
`singleSalt_knowledge_soundness_queryBound`.

### 2. Scope of "Fiat–Shamir" should be stated in the #1277 module docstring

Keys are `(statement, global salt, message prefix, per-round salt)`. Previous challenges are absent
from the key, and the statement is bound into every key (strong FS). This is CY's "basic" prefix-keyed
FS. Deployed transcripts usually hash a running state (hash-chain or duplex sponge), so the chain to
deployment still needs the hash-chain/duplex bridge (#469 and the design's `FiatShamir` pass, 04 §5).
One sentence in the docstring would stop readers from over-reading "FS knowledge soundness" here.

### 3. `Round.finiteMessage`: needed by the proof, or only by the presentation?

Every round requires `Finite Message`. The probability argument goes through VCVio's
arbitrary-domain cached-oracle lemmas, and inputs and salts may already be infinite, so finiteness
of messages looks needed only for `Key.instFinite`/table-based lemmas. If it is not load-bearing,
dropping it would admit protocols whose prover messages are unbounded (polynomials of unbounded
degree, variable-length vectors) without a quotient. If it is load-bearing, a note on where would
help. On our side we found the gap removable for any fixed adversary in our deterministic
finite-coin game, by restricting to the finitely many messages the adversary can produce. That trick
does not transfer to adversaries with unbounded private coins.

### 4. One-directional `outputLaw` (#1274/#1277/#1283) versus the merged `iff`

The stacked theorems take `Rout → terminalState.holds` (and, in #1277, also gated by `accepts`)
instead of the merged `iff`. That is a weaker hypothesis and so a stronger theorem. It may be worth a
corollary or a remark that the merged `iff` forms are instances, so readers comparing the two
generations do not suspect the event changed. The event itself (`z ∈ Z ∧ Rout ∧ ¬ Rin (extract …)`,
with the adversary's own witness as the seed) is unchanged and is the straightline event of WARP
Def B.2.

### 5. Nonvacuity checks that came back clean

We tried to find hypotheses the framework makes trivially true:
- `bounded` at `error ≥ 1` is trivial, but so is the conclusion.
- `Z = ∅` or `Rout ≡ False` empty the event, but nothing forces them.
- `terminalWitness`/`seed` cannot force an empty carrier (identity on a nonempty constant carrier is
  always available).
- The `IsLocallyBounded` quantifier over every authored prefix, including zero-probability ones,
  is the right strength for state restoration, since the adversary can reach any prefix.
- `badChallenge` keeps the existential witness inside the probability.

We found no vacuity. Finding 1 is the only gap we would ask to close before merge.

### 6. Nit

In #1277, `singleSalt_knowledge_soundness_queryBound` counts `freshKeysOfLog` over the adversary
phase only, and adds `Σ_j ε_j` for completion. A short docstring line saying that repeated adversary
queries are free, and that completion keys already queried by the adversary are not charged twice,
would make the improvement over the textbook `(Q + k)·ε` visible to readers.

---

## Notes for ember (not for posting)

- Finding 1 is the substantive one. If you want, I can write the proposed client against `main`'s
  merged theorem on the fork (one acceptance file, `ArkLibTest/…/StateRestorationAdaptive.lean`) and
  prove the `15/64` equality. That would be a small, clearly welcome upstream PR, and it is not
  initiative (c).
- The "we are deriving our theorem from yours" sentence is true as of
  `lane/arklib-sr-bridge` 681b3c7d9 (certificate translation proved). Keep it only if the bridge
  lands before you post; otherwise soften it to "we are working on deriving".
- Do not post during their restack; all five PRs were mergeable and CI-green on 2026-11-06.
