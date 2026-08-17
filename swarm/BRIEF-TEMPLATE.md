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

## 7d. HASH/LINEAR-LAYER DESIGN GATE (added 2026-08-17, paid for by Weft)
**Compute the branch number FIRST — before any other analysis, before naming
the candidate, before a single security argument.** It is four exact passes
with tooling we own (`~/src/ring-ro-hash/weft_branch.py`, the
`branch(M) = branch(M⁻¹)` duality making it self-certifying), and it would
have killed Weft on day one instead of after a full obligations table.
Corollary: **a linear layer inherited from another object (an encoding map, a
fold operator) imports that object's structure — and structure is the
opposite of diffusion.** Alignment lives in the proof toolkit, not the matrix.

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
