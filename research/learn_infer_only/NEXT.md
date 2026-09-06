# Decisive follow-ons — first three now in flight

1. [OPEN: runtime integrity integration] Replace the staged restore adapter's
   empty-rootWrites witness with a real materialized cell/DataIntent carrying the
   same receipt context. Prove `receipt.next = installed post-root`, accepted genesis/
   parent openings, and full `Intent.preflight` acceptance. Execute crash/retry
   controls: consume-before-release, crash after commit, duplicate exact packet,
   stale snapshot and check/install race. Pass criterion: one actual durable path
   with its witness and falsifier, not a second parallel gate. Minidregg changes
   remain patches from a research run.

2. [OPEN: smallest privacy-changing experiment] Instantiate one restricted release
   and input-issuance mechanism for a tiny closed state update; enumerate every
   surviving key/program/coin, then expose the union required by tier A. Start with
   the fixed-Step/NISC or narrowly constrained construction question identified in
   `CANDIDATES.md`, or explicitly choose C/D as a comparison. Pass criterion: two
   distinct interface-admissible private states, two continuing protected updates,
   authorized output, and no equivalent read-all capability in any exposed role.
   Fail criterion: exhibit the exact surviving credential and a recovery path.
   Existing GKS23/PCE audits and trace/routing lemmas need no duplication.

3. [OPEN: randomized composition] For a candidate that survives task 2, bind private
   development coins to a preauthorized parent/command and prove actual distribution,
   not merely a seed commitment. Model malicious issuer, restore and selective abort/
   branch grinding together. The current finite witness shifts a fair bit's chance
   of 1 from 1/2 to 3/4 by selecting from two fair draws; reproduce it as a broken
   sibling. Add the adaptive multi-context receipt/continuity game and then price
   all assumptions, including QROM/PQ dependencies if claimed. Deterministic Stage 0
   and a public beacon do not discharge hidden entropy or this composition.

[DERIVED resume instructions] Read `STATUS.md`, `SECURITY_GAME.md`, `DECISION.md`,
then `formal/README.md`. Reproduction commands are in the latter. Keep the generated
patch un-applied until the maintainer folds it; never edit companion trees from this
research run. Inspect current dirty state and the companion before choosing work:
another run may have landed an object since this tranche. The active swarm and output ownership are recorded in STATUS.md; the current
goal runs through 2026-09-06 10am EDT. Inspect that table before starting a lane.
