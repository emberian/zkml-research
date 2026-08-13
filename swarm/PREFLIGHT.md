# Preflight — known landmines (check before working, add when you hit one)

- **Lean/mathlib**: `~/src/mathlib4` must resolve (symlink →
  breadstuffs-codex checkout, rev 1c2b90b, oleans warm). `lake env lean`
  writes NO olean — `lake build <Module>` before importing. minidregg
  importGraph symlink repaired; **breadstuffs/metatheory's is still dangling**.
- **Kernel landmines** (CyclotomicInertia lane): the CommRing/Field Semiring
  diamond DIVERGES at ZMod p for our primes — state helpers over [Field R].
  Never route `Splits` through X^q−X (kernel normalizes a 2^31+-degree poly).
- **Shared trees**: minidregg + breadstuffs worktrees carry codex's
  uncommitted work (Compiler.lean, prover/src/lib.rs, untracked Uwueave
  files). `git status` first; commit `--only` named paths; never `add -A`,
  never stash. `--only` is PATH-granular — a dirty shared file sweeps foreign
  hunks.
- **hbox**: builds via `swarm-build` ONLY (memory cgroup). The shared scratch
  (`/tank/dregg-build/minidregg-checks/scratch/*`) is an evidence-corrupting
  race for verification — detached clone at the committed SHA is the gate.
- **Rust**: private CARGO_TARGET_DIR is a trap; bare SIGABRT + no panic = the
  Lean archive is missing.
- **zsh**: `for f in $VAR` does not word-split — use xargs. Backticks in
  double-quoted commit messages get command-substituted — `commit -F file`.
- **paperbin/mirror**: eprint fetch works with browser UA (`/tmp/eprint.sh`).
  Mirror ends 2026/777 (~April). Full-text cache:
  scratchpad/ft/YEAR-NUM.txt + heads.tsv. ⚠ IoTeX filenames swap 858/861.
- **Scratchpad is shared across concurrent lanes** — generic filenames
  collide (a lane's file was clobbered mid-task). Use unique prefixes.
