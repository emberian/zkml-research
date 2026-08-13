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
