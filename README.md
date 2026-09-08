# zkml-research

Open research toward verifiable machine learning: proving that a specific model,
with specific weights, produced a specific output — with post-quantum,
hash-based proofs and no trusted setup.

**Everyone deserves verifiability.** The point of doing this in the open is that
verifiable inference should not be an enterprise feature. If it works, it should
be something anyone can run against any model they care about.

## Why this repo exists

Notes, measurements, and design work live here rather than in an implementation
tree, so that thinking-in-progress stays clearly marked as such. Nothing here is
a claim about a shipped system.

## Standing on

- **Attestable** published the first production-scale numbers for LLM inference
  proving and stated their limitations plainly. That made the design space
  concrete.
- **catgrad** (Hellas AI) is a categorical deep learning compiler whose models
  are open hypergraphs and whose backends are NdArray implementations — an
  unusually clean seam for a proving backend.
- **Plonky3** and the STARK/FRI line of work; sumcheck/GKR for tensor ops.

Where this work disagrees with published choices it is because a different point
in the design space looks reachable, not because the published choices were
wrong for the people who made them.

## Contents

- **`docs/VERDICTS.md` — start here.** The single current-truth file: what we
  believe now, in final form, with the open questions in its §7. **Where any
  other file disagrees with it, it wins and the other file is history.**
- `notes/README.md` — the index of research-lane findings: what each one
  measured, and which file holds each of the questions that are still open.
- `docs/` — design notes. Each states what is verified, what is sourced, and
  what is guessed.
- `notes/` — research-lane findings as they land.
- `notes/archive/` — files whose central claim died. Kept whole, with what
  replaced them. History, not truth; not for citing.

## House rule

Every note separates **verified** (computed or proved here), **sourced** (with
citation), and **inferred** (mine). If a number has no provenance it does not go
in.

## Research website

[Explore the research index](https://emberian.github.io/zkml-research/) for
result cards, linked evidence and limitations, with reading paths through proof
systems, encrypted learning and mental autarky.
