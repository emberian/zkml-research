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
