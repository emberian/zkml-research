# forcodex — the full handoff

Written 2026-08-16 for codex, who has not been in these sessions.

## What this is

A research campaign on **verifiable computation over ML and FHE workloads**,
run mostly as swarms of subagents against three repos, over roughly five days.
This directory is everything: what was steered, what was explored, what was
measured, what died, what is live, and — importantly — **the error classes we
kept committing**, because those recur and are cheaper to inherit than to
rediscover.

## How to read it, in order

| file | what it holds |
|---|---|
| `01-STEERS.md` | ⚑ **Ember's corrections, verbatim where possible.** The highest-signal file. Most of the campaign's turning points are here, and each one names a real failure mode. |
| `02-LANDSCAPE.md` | what was explored, and the verdict on each |
| `03-MEASUREMENTS.md` | every number **with its conditions** — and the methodology that had to be retracted to get them |
| `04-DEAD-ENDS.md` | priced, each with the number that closed it. *Months not spent.* |
| `05-ERROR-CLASSES.md` | ⚑ the recurring failure shapes, with instances |
| `06-OPEN.md` | what is genuinely live |
| `07-ARTIFACTS.md` | what is on disk, where, and what state it is in |

## The one-paragraph version

We hold a **machine-checked compilation layer for a proof system** — the part
between "an interactive protocol is round-by-round sound" and "a deployed
non-interactive verifier accepts only true things." Nobody else has both legs
(ArkLib's composition theorems are `sorry`; Binius64 and Flock carry no formal
content). Over these days we measured the prover honestly for the first time,
discovered most of our cost estimates were in the wrong unit, found and closed
several vacuities including one where **the anti-vacuity tooth was itself
vacuous**, and established that **13 of 18 keystones are field-agnostic** — so
a binary-field instantiation is reachable. The stance is **basic research: a
bag of composable formal ingredients, charting a landscape**, not a product.

## Three things to know before believing anything here

1. **Operation counts are the primary instrument; wall clock is secondary and
   was wrong for two days.** Every timing taken on the laptop (load 16–95, 36
   sessions) is an upper bound at best. `hbox` + `circuit/tests/hbox_rig.rs`
   is the trustworthy path, and even there **hbox was building the scalar
   Poseidon2** until 08-14.
2. **A percentage without its denominator is not a measurement.** Two lanes
   disagreed about "grind is 18% vs 23%" purely because they summed different
   phase sets and neither said so.
3. **Absence claims here have been wrong more often than right.** Four papers
   refuting our "nobody has done this" claims were sitting *in our own
   `~/paperbin`*. The corpus is `~/dev/gh/forks/IACR-eprint-mirror/` (complete,
   2026→1053+) — the scratchpad cache stops at 777.
