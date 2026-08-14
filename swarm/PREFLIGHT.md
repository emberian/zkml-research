# Preflight — known landmines (check before working, add when you hit one)

- **Lean/mathlib**: `~/src/mathlib4` must resolve (symlink →
  breadstuffs-codex checkout, rev 1c2b90b, oleans warm). `lake env lean`
  writes NO olean — `lake build <Module>` before importing. minidregg
  importGraph symlink repaired; **breadstuffs/metatheory's is still dangling**.
- ⚑ **`Bfv/Mul.lean` and `Bfv/Smudging.lean` are in NO default build target**
  (the `Bfv` lean_lib has no globs, so only `Bfv.lean` + transitive imports
  build). **43 keystones are unpinned by CI** and `#assert_namespace_axioms`
  never walks them. Both build green standalone. This is the
  gating-defaults-to-silence class, in our own tree, found 2026-08-13.
- **Kernel landmines** (CyclotomicInertia lane): the CommRing/Field Semiring
  diamond DIVERGES at ZMod p for our primes — state helpers over [Field R].
  Never route `Splits` through X^q−X (kernel normalizes a 2^31+-degree poly).
- ⚑ **`git commit --only` LEAVES THE INDEX STALE** (found 2026-08-14, a *new
  route* to the recorded mass-revert hazard). After committing with `--only`,
  the files still showed `MM` — **the index held pre-`rustfmt` versions, so a
  bare `git commit` by any lane would have reverted part of the work.**
  **After an `--only` commit, re-add your own paths** so the index matches
  what you committed.
- ⚑ **`--only` gives NO STANDING PROTECTION AGAINST A LATER `--amend`** (found
  2026-08-13, cost: four of another lane's staged deletions swept into a
  commit titled for something else). `--only` protects **the invocation you
  type it on**. A follow-up `git commit --amend` takes **the index**, which by
  then may hold a sibling lane's staged work. **If you must amend, use
  `--only` again on the same paths, and verify the tree hash is unchanged for
  a message-only fix.**
- **Shared trees**: minidregg + breadstuffs worktrees carry codex's
  uncommitted work (Compiler.lean, prover/src/lib.rs, untracked Uwueave
  files). `git status` first; commit `--only` named paths; never `add -A`,
  never stash. `--only` is PATH-granular — a dirty shared file sweeps foreign
  hunks.
- ⚑ **DISK: the boot volume hit 0 bytes free twice on 2026-08-13**, killing a
  build and costing another lane a measurement cell. Recovered to 136 GiB on
  its own (APFS purgeable). **Where it goes, measured**:
  `breadstuffs/metatheory/.lake` **7.3 G** · `breadstuffs/target` **5.8 G** ·
  `~/.cargo/registry` 4.9 G · `minidregg/.lake` 1.2 G. **Reclaimable without
  touching our work** (ember's other projects, cargo rebuilds them):
  `~/src/continuwuity-recon/target` 3.1 G, `~/src/xilem/target` 1.8 G,
  `~/src/conduit/target` 1.7 G. ⚠ **Deleting `~/.cargo/registry/cache` is
  safe** (`.crate` archives, re-downloaded on demand — a lane did this and
  cargo re-fetched without incident); **`registry/src` is NOT** — that is the
  unpacked source everything builds against.
- **hbox**: builds via `swarm-build` ONLY (memory cgroup). The shared scratch
  (`/tank/dregg-build/minidregg-checks/scratch/*`) is an evidence-corrupting
  race for verification — detached clone at the committed SHA is the gate.
- **Rust**: private CARGO_TARGET_DIR is a trap; bare SIGABRT + no panic = the
  Lean archive is missing.
- **zsh**: `for f in $VAR` does not word-split — use xargs. Backticks in
  double-quoted commit messages get command-substituted — `commit -F file`.
- ⚑ **CORPUS BLINDNESS — the biggest instrument failure so far.** The IACR
  mirror is **cryptology papers only, and not even all of them.** It cannot
  see: arXiv (cs.LG/CL/PL/LO/AR/DC — where ML systems, formal methods and
  hardware live), math journals and math.NT (where our own number theory
  lives!), ITP/CPP/CAV/POPL, MICRO/ISCA/ASPLOS, USENIX/OSDI, NeurIPS/ICML,
  and ALL grey literature (engineering blogs, ethresear.ch, audit reports,
  talks without papers, GitHub design docs). **Two proofs of the failure:**
  the "MoE router binding: zero papers in 7,090" claim was refuted by two
  arXiv papers **sitting in our own ~/paperbin, correctly named, pulled the
  same day the absence was declared**; and Powdr's logup*-for-Twist/Shout
  note — a genuine contradiction to a law we had recorded — was never posted
  to eprint. **NO absence claim may be quoted as [measured] on the strength
  of the eprint mirror alone.** State the corpus AND the instrument with
  every absence; a first-2-page keyword cache cannot see a §4.3 or an
  appendix, and "verified twice" with one blind instrument is one witness.
- **paperbin/mirror**: eprint fetch works with browser UA (`/tmp/eprint.sh`).
  Mirror ends 2026/777 (~April). Full-text cache:
  scratchpad/ft/YEAR-NUM.txt + heads.tsv. ⚠ IoTeX filenames swap 858/861.
- **Scratchpad is shared across concurrent lanes** — generic filenames
  collide (a lane's file was clobbered mid-task). Use unique prefixes.
- ⚑ **NEVER pipe `cargo` into `head`/`grep -m`** (found 2026-08-14, cost ~25
  min and one phantom "it built but produced no binary"). `head -N` exits at
  N lines → SIGPIPE → **cargo dies mid-build with exit 0 through the
  pipeline**, leaving a `.d` file and no test binary. And `| tail -N` is the
  opposite trap: it buffers everything, so a live build looks *hung* and gets
  killed. Redirect to a file (`cargo … > log 2>&1 &`) and grep the file.
- **breadstuffs `target/` has ONE cargo lock across all lanes.** "Blocking
  waiting for file lock on build directory" means another lane's `cargo`/
  `cargo nextest` owns it (a `fhegg-fhe --release` GPU suite held it for
  many minutes). It is not a hang — wait, do not kill.
