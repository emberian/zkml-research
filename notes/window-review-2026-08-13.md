# Context-window review — ledger, confession, map

2026-08-13. Written at the end of a long window, for the next one.

## The arc

Research campaign (~60 lanes: format, field, hash, audit economics, recursion,
FHE, lookups/RAM, hardware) → pivot to implementation on ember's call → **a
refutation cascade** when the wider-corpus sweeps landed → **four hard course
corrections from ember** → a design phase that produced the two best artifacts
of the run in its final hours.

## Durably on disk

**Lean, kernel-checked, zero `sorry`:**
- `Selvage/AuditSampling.lean` — the commit-then-audit theorem. Per the
  sweeps, the first machine-checked one anywhere. The fail-open wound class is
  a *theorem*: unpriced refusal makes the legs uninhabitable, priced refusal
  forces q ≤ 0.
- `Theory/CyclotomicInertia.lean` — the 127·2ⁿ+1 family law, KoalaBear
  re-derived as an instance, a 67-digit counterexample proved, Goldilocks
  proved prime, and the domain-availability lemma whose negative instance *is*
  the matvecmul panic.
- `Assurance/TwoRegimeQueryBudget.lean` — **regime in the type**; UDR and JBR
  errors are different types and cannot be compared; `cbr_not_reportable` is a
  theorem. The squared-rational trick avoids interval enclosures entirely.
- `metatheory/Bfv/Ring.lean` — the noise model lifted to the ring with the
  row-sum bound surviving **verbatim**, `negaMul` *proved* to be the ring
  product, and δ_R = N proved **tight**.
- `minidregg/prover/src/sumcheck.rs` — the Selvage engine, vector-bound to the
  Lean verifier, fail-closed.

**Rust, tested:** `fhegg-fhe/src/bfv_coeff_matmul.rs` (12 bits/matmul, depth 2
after, 466 µs, capacity gate that fires); `registry/` (⚠ mis-specified — see
below); `sumcheck-toy` (recon only, debt to delete).

**Notes:** ~40 committed files. **The recording discipline is genuinely good.**

## The confession: what was refuted, and the pattern

Roughly **fifteen** of our own claims fell in one day. The five that matter:

| claim | fate |
|---|---|
| "MoE router binding: zero papers in 7,090" | refuted by **two papers in our own paperbin** |
| carrier census / vacuity instruments | **reinvention** — mathlib 2020, model checking 2001 |
| the prime + family law | **folklore**, in a 1994 Birkhäuser table |
| "multilinear/GKR substrate absent everywhere" | **six shipped systems**, one on Ethereum mainnet |
| "proof-aware QAT in nobody's paper" | refuted by **two more papers in paperbin** |

**Four mechanisms, all now in PREFLIGHT**: corpus blindness (the eprint mirror
is cryptology-only); instrument blindness (a first-2-page cache can't see a
§4.3); **we didn't grep our own holdings**; and arXiv's `all:` field is
metadata-only, so our zero-hit queries were weaker than they read.

**And the registry**: I shipped a commitment **no prover can open** (SHA-256
over a manifest — proving weights against it means hashing 14 GB in-circuit),
then called it "the anchor everything else references" **in the same message
where I quoted its own not-done list saying "no consumer."**

## The four corrections, and what they were really about

1. **No moats.** "Moat" imports the assumption that value comes from what
   others can't have — the opposite of a project whose position is that
   verifiability isn't an enterprise feature. Purged, along with the land-grab
   framing ("unclaimed," "the position is vacant") I'd used all session.
2. **Vacuity-checking is tacit behavior, not a contribution.** Not novel *and*
   not AI-specific — careful people do it, and early-development vacuous
   assumptions are normal. The only real difference is doing it mechanically
   and marking what stays open.
3. **Stop the soundness theater.** Counted: ~15 refutations, 4 audits, 3
   corrections-of-corrections against 1 design artifact and 2 builds. *A
   perfectly honest ledger of a system that's 100× too slow is still 100× too
   slow.* New rule: **verification is a gate on claims, not a source of them.**
4. **We are abandoning Plonky3.** "It already exists upstream, unwired" is a
   *temptation*, not an opportunity. Now §7b of the brief template.

**My repeated failure mode, named**: reach for a novelty framing → get
corrected → reach again in a different costume. "Novel instrument" → "novel
failure mode" → "the anchor everything references." Three times in one day.

## The open contradiction (do not quote either side)

- **Floor lane (derived)**: hash-bound at every blowup ≥ 2, 94% at our lb=6.
- **Recon lane (measured here)**: FRI proving is ~19% hashing with Blake3,
  ~40% with Poseidon2 — LDE and folding are the larger half.

This decides whether the field/hash migration is worth ~3.4× or much less.
**Resolve by profiling one real IR-v2 proof at lb=6 and lb=4.**

## The map — what the design phase actually established

- **The AIR commits the interior of a relation; the sumcheck commits its
  boundary.** 5,461× at n=4096, Θ(n).
- **Thaler's 0.18–0.33% is the B≈n case** — overhead is 1/B + 1/n, so **at
  B=1 it's 100.02%, and decode is B=1.**
- **`fold_add` has a proof, not a ratio**: MLE is linear ⇒ one common-point
  opening, zero sumcheck rounds, zero range checks, ratio = B.
- **The base→extension boundary is a measured ~3× cliff** ⇒ *the emitted AIR
  must be polymorphic in the value ring from day one.*
- **Jagged PCS** is the highest-value available idea and `sumcheck-toy`
  already proves its primitive.
- **Our soundness posture is the outlier** — 4 of 5 production systems refuse
  the capacity conjecture; 100 UD bits costs us **86 queries instead of 19
  with log_blowup unchanged**, i.e. 4.5× on the query phase and **zero on the
  commit phase.**
- **Ring hash: build it, τ=2** — τ is the challenge-space exponent (q^τ), which
  makes the fork a trilemma; the Feistel's 4% survived the modelling check.

## For the next window

The queue is not "what to verify." It is: **profile the contradiction**;
**pin the AIR's value-ring polymorphism before more constraints are written**;
**build toward Jagged**; **switch the default to the proven regime and publish
both columns**; **build the ring hash at τ=2**; and **re-specify the registry
commitment as Poseidon2-over-field-elements at a leaf granularity the circuit
opens.**

And one process rule that earned itself: **write the note first and
incrementally.** Every high-value loss this window was a lane that finished and
had no note — the recording discipline was excellent, the *handoff* had none.
