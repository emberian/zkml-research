## Context shared by the analytic lanes (2026-11-07)
Ember (https://ember.software) has said, three times in eleven days, that the program is too empirical. The directives that got built are runs, censuses and measured demos; the ones that never got built are generators, calculi, proof-repair transports and analytic bounds. Read /Users/ember/dev/whatember/DIRECTIVES-DIG-2026-11-07.md first. It holds ember's own words, with dates and session ids, and the status of each directive. Your lane is one of its "§2 analytic and synthetic opportunities". Ember's themes (§3) are binding taste: proofs that mean something; Lean first, then generate everything else; no downscoping and no "minimal slice"; first principles and categorical derivation; composition across the stack; frontier synthesis, "not whatever default bullshit your latent space has".

Ground truth first, or you build a mirror. Before you write anything, read the real Lean you build on and paste its actual signatures into your notes:
- minidregg (Selvage spine, Lean v4.35.0), /Users/ember/dev/minidregg;
- breadstuffs metatheory (Dregg2, now Lean v4.35.0, main 6cfc27c26), /Users/ember/dev/breadstuffs/metatheory;
- zkml-research docs: /Users/ember/dev/zkml-research/docs/PROOF-SYSTEM-SPACE.md and COST-MODEL.md.
Don't invent field names. If what you need doesn't exist, say so and build it.

Bars: working Lean objects with an executable consumer, real theorems, and stated assumptions. No vacuous statements: nothing of the form P → P, no hypotheses that make the conclusion trivial, and every "for all" checked for a non-trivial instance. A theorem's statement is the product; read it adversarially before you call it done. There are no publication goals; the bars are features, maturity and depth.

Lean policy (ember's): facts about concrete data are compiled checks (`#guard`, an exe, or `native_decide` with the axiom pinned via `#assert_compiled`/`#guard_msgs`). General theorems stay kernel-proved. No kernel `decide`/`rfl` over big data.

Engineering:
- Work in your own git worktree on a branch `lane/<your-name>`, never in the shared checkout. Merge to main only after a whole-tree build on bb2 is green: a systemd-run --user --scope with MemoryMax=48G and LEAN_NUM_THREADS ≤ 8, or `swarm-build` on hbox.
- Fix known causes directly; no cold "before" measurement builds.
- Never run an unfiltered `-p <crate>` or bare `cargo test`.
- Read ~/swarm/MACHINES.md before using a box. pug is off limits, as are nanodregg and ~/hellas.
- No GPU or cloud rentals. This is analytic work.
- Git: commit named files only (never `git add -A`); use `git -c commit.gpgsign=false commit -F <msgfile>`, with the message ending `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`. NEVER `git stash`, rebase or reset. Push your branch.
- Disk pressure: stop, report, wait. Delete only what you created.
- You may spawn sub-lanes. Brief them as doers, with absolute paths and real signatures pasted in.
- Use Codex `gpt-6-astra` (`codex exec -m gpt-6-astra ...`) once for an adversarial review of your main theorem statements before you merge.

Stopping processes: PID file or nothing (incident 2026-10-10). A subagent ran `pkill -f "cat" -u ember` to clear its own stuck `cat`. `-f` matches the whole command line, every app lives under `/Appli**cat**ions`, and 44 of my apps and agents got SIGTERM.
- **Never kill by pattern.** No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`.
- **A process you started is stopped by the PID in its PID file**, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead.
- If you must look first, `pgrep -fl` and read the list; it is never the argument to a kill.
- Every subagent brief you write quotes this block verbatim.

Reporting: report on events (something lands, something is red, you're blocked, you need a decision); no status chatter. Keep a notes file at /Users/ember/dev/zkml-research/notes/analytic/<your-name>.md. When something lands, add or update a row in /Users/ember/dev/whatember/INITIATIVES.md, committing that file by name and pushing. Your final message: the theorem statements verbatim, the SHAs, and what's next.
