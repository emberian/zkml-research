# Lane brief template — the shape that works

Distilled from ~50 lanes (2026-08-11..13). Every section earned its place by a
failure. Fill all of them; deleting a section is a decision, not an omission.

## 1. ROLE + ONE-SENTENCE GOAL
Research / red-team / implementation / experiment / writing. One sentence of
what done looks like.

## 2. SPEC POINTERS (ground truth first)
The note/doc that IS the specification, read-first order. Lanes that reconstruct
the interface from prose build a mirror and verify against their own
reconstruction — paste REAL signatures, REAL paths, REAL theorem names.

## 3. CORRECTIONS BAKED IN
Every claim near this lane's territory that has been narrowed/refuted, stated
inline. A lane must not be able to re-derive a dead claim from a stale note.
(The audit-scaffold lane succeeded because the ε_beacon and "attained"
corrections were IN the brief.)

## 4. WHAT YOU MUST NOT ASSUME
The specific over-claims this lane is most likely to make, named. ("The
grinding theorem is NOT an ε_beacon statement.")

## 5. HAZARDS + PREFLIGHT
Point at swarm/PREFLIGHT.md. Name the shared-tree state (who is dirty, which
files are untouchable), the tooling landmines, the evidence-corrupting races.

## 6. GATES
What "done" must survive: build command + host, detached-clone HEAD
verification for anything committed, axiom pins for anything proved,
boundary/hygiene scripts. "Green in your worktree" is not a gate.

## 7. DELIVERABLE SCHEMA
The exact sections the report must have. Always include:
- claim tags: PROVED / MEASURED / COMPUTED / SOURCED / INFERRED-BY-ME
- what was NOT done, as its own section (absence ≠ negative finding)
- for multi-thread lanes: per-thread return status — a thread that never
  returned must be REPORTED as such, never silently absorbed

## 7b. SUBSTRATE LAW (state in every brief that touches proving)
**We are abandoning Plonky3 and every third-party prover stack as fast as we
can.** The trust path is Lean-authored and formally verified — ours. Upstream
crates may be READ for API shapes and may serve as throwaway differential
oracles in tests; they never enter the trust path, they are never a
"foundation," and **"it already exists upstream, unwired" is not a reason to
wire anything.** A lane that proposes adopting an upstream engine has
misunderstood the project. If a capability is missing, the answer is that we
build it in Lean, in Selvage.

## 7c. A CONFESSION'S LOCATION LIST NEEDS THE SAME GREP AS A CLAIM
Found 2026-08-13, and it cost a cleanup lane real time. A lane self-corrected
with *"I cited this wrongly, including in file Y."* That location list was
**recalled, not grepped** — file Y had cited it correctly all along. I put the
false accusation into a brief, and the next lane had to disprove it.
**When a lane confesses, the WHERE is a claim too: grep it before propagating.**

## 7d. HASH/LINEAR-LAYER DESIGN GATE (2026-08-17, paid for by Weft — **AMENDED the same day, paid for by re-opening it**)

⚑ **The first draft of this gate said "compute the branch number FIRST." That
was the wrong half of Weft.** `notes/weft2.md` re-opened the kill and measured
it: **branch 6 was NOT disqualifying** (at GF(2³²) one active `x⁻¹` S-box is
worth 30 bits on *both* sides ⇒ 180 bits per 2 rounds against a 128-bit bar —
and **Poseidon2's own internal layer is branch 2 and ships**). What killed Weft
was a **fixed lane** — `output lane 0 = input lane 0` — that **no branch number
can see**: the whole 23-rotation family changes the structure completely while
`B_d` and `B_l` do not move at all (a permutation preserves Hamming weight).

**Branch number is a ONE-ROUND quantity. Everything that kills these designs is
MULTI-ROUND.** So, in this order:

1. **STRUCTURE FIRST — the invariant-subspace / subspace-trail search.** For a
   lane-wise 0-fixing S-box the invariant coordinate subspaces are *exactly* the
   closed sets of the support digraph (`i → j ⟺ L[j][i] ≠ 0`) — so enumerate the
   **whole lattice** by closure, on **`M` and `Mᵀ` both**, and ⚠ **index from
   b = 0**: the kill's own script looped `range(1, 5)` and the level it skipped
   was the fatal one. `∞` diffusion depth is a hard fail.
2. **A QUOTIENT IS NOT A SUBSPACE.** "Broken by round constants" is the standard
   escape for an invariant *subspace*. It is **false** for an invariant
   *quotient* — the constant just becomes the small map's own round constant.
   State which one you found.
3. **The subfield test, entry-level AND twisted.** Do the entries lie in a proper
   subfield (`x⁻¹` preserves every subfield)? Does any two-sided diagonal twist
   put them there — i.e. what subfield do the **cross ratios** generate? ⚑ **MDS
   does not answer this**: the systematic-RS repair is MDS by theorem and *still*
   a GF(2⁸) matrix at the natural point set. Then test the round **constants** the
   same way — a small-integer transcript tag lives in GF(2⁸).
4. **`deg(minpoly)` + per-lane observability**, if any partial/internal round is
   contemplated. Poseidon2's internal condition is **observability of `(eⱼᵀ, M_I)`**,
   not a branch number. ⚑ An involutory MDS layer (`A² = I`) passes every branch
   test and leaves a 22-lane subspace on which partial rounds are linear.
5. **THEN the branch number — on BOTH sides.** `B_d(M)` *and*
   `B_l(M) = B_d(Mᵀ)`; they are different quantities off MDS, and the kill
   computed only the first while the second read **2**. Score against **the bar**
   (S-box DP/LP × branch), never against the MDS ideal, and against a
   **same-characteristic** comparator — the kill's Poseidon2 row was BabyBear,
   and `M_E`'s {1,2,3} entries have no char-2 instance.
6. **If the layer is inherited from another object, THE POINT SET is the design
   decision.** Weft died by evaluating *inside its own interpolation window*.
   Moving the evaluation set off the window is **free** (same butterflies, shifted
   twiddles) and is the difference between branch 6 with a fixed lane and branch 8
   (one transform) or 25 (two transforms, MDS *by theorem*).

Tooling we own: `~/src/ring-ro-hash/weft2_structure.py` (steps 1–4 + both branch
sides), `weft_branch.py` (the self-certifying `branch(M) = branch(M⁻¹)` passes),
`mark32_sysrs_branch.py`. Corollary kept from the first draft, now with its real
mechanism attached: **a linear layer inherited from another object imports that
object's structure — and the import is through the POINT SET, which is free to
change.**

## 8. STANDING ORDERS (copy verbatim into every brief)
- Read theorem statements, not abstracts, for anything you call a bound.
- Verify claimed absences with multiple spellings AND post-mirror via web.
- A quote you cannot re-find by grep does not exist. (A lane fabricated one;
  the grep caught it.)
- Statement-first with refutation teeth for anything formalized; a named
  obligation Prop is a good outcome, a `sorry` is not.
- If blocked >2/3 of budget on one step, write the partial report FIRST, then
  continue. Silent lane death costs more than partial results.
- Under-claiming is correct. The report gates decisions; err toward breaking
  your own findings.

## 9. ⚑ THE HANDOFF RULE (added 2026-08-13, paid for by a transcript audit)

A transcript-mining lane found that **every high-value loss in this project
had the same mechanism: a lane produced the result and the DELIVERY CHANNEL
failed** — credits exhausted mid-write-up, `SendMessage` rejected as "prompt
too long", or a consolidation pass that kept the verdict and dropped the
model. The recording discipline is excellent; **the handoff between a lane
finishing and a note existing has none.**

Therefore, every lane:
1. **Writes its note FIRST, incrementally, not at the end.** Create the
   notes file early and append as findings land. A note that exists at 40%
   completeness beats a perfect report that dies at 95%.
2. **Leaves a pointer for every on-disk artifact it creates** — scripts,
   Lean files, test files, cloned repos — in that note. Finished work with
   no pointer is deleted work. (Recovered examples: `~/src/ring-ro-hash/
   design_*.py`, `minidregg/Theory/IntegerFingerprint.lean`, two claude.ai
   decision memos whose URLs appear nowhere in the repo.)
3. **Never reports a number only in prose to the orchestrator.** If it was
   computed, it goes in a file.
