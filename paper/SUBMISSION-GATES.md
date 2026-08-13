# SUBMISSION GATES — Rock 1 paper

2026-08-13. What must land before DRAFT.md is submittable, in dependency order. A gate is
closed by an artifact (a committed script, a pinned transcript, a built Lean theorem), not
by a lane's summary — harvest with `cv workflow`, audit statements, build the tree.

## The three briefed lanes

- **G1 · Red-team reproduction of the Zama ceiling (C2).** Re-reproduce the
  `Domain::new(2^32)` panic at a **pinned commit** of the 2026/027 codebase; commit the
  command + panic transcript + the derivation of D·t·n ≤ 2³¹ from the domain bound, and
  measure their current parameters' distance to it (the "one doubling" of abstract
  sentence two). *In flight per brief.* Falls ⇒ abstract sentence two and the intro's
  "constraint binds in production" paragraph reshape.
- **G2 · Lean certificate suite (C4, C5, C9).** Instantiate the
  minidregg `Theory/CyclotomicInertia.lean` route at p61; prove the family law (127·2ⁿ+1:
  inertia ⟺ n ≡ 0,2 mod 6) with KoalaBear and p61 as corollaries; primality, 2-adicity,
  NTT legality, fold identity; and the **domain-availability lemma** whose negative
  Goldilocks instance is the G1 panic (C9.2 — the artifact section's centerpiece). Named
  theorems + `#assert_axioms` footprints; no bare `#guard`s (GUARD-DISCIPLINE). Note the
  scan side: C3.1/C5.2 rows above 2⁶⁴ are 40-round MR — certified primality for the
  specific primes the paper *names* (p61 is deterministic already; n=214 and census
  examples want certificates) closes that caveat. *In flight per brief.*
- **G3 · The modulus-swap experiment (C6).** The one-line swap + F2 constants; register
  the four predictions of draft §5 before the run; report "what was not one line" at full
  resolution. **If the prediction fails the paper reshapes** — census + family +
  certificates stand; the empirical-centerpiece framing does not. *In flight per brief.*

## Gaps found while scaffolding (nobody owns these yet)

- **G4 · Census reconciliation — REAL DISCREPANCY.** The brief says "104 Solinas + 106
  Proth"; the committed script finds **117 Solinas** in a ∈ [96,130] (and confirms the
  notes' 93 at 2-adicity ≥ 20). Either commit the original census lane's script and
  reconcile parameterizations, or adopt `paper/scripts/verify_candidate.py` as the
  census of record and renumber the draft. Also owns the Proth-side census (C3.3).
  **Until closed, the draft quotes only 117/93.**
- **G5 · Enumerate the six adopt-a-proof-prime papers.** Only 2026/027 and GBFV are named
  in notes. Related work (C1.2) needs all six with citations, and a quote-check of
  HELIOPOLIS §6.2 and 2025/286 (C1.3) — these two get full-credit framing, so get their
  claims exactly right.
- **G6 · Corpus pin for the boundary claim (C1.4, C7.4-novelty).** "39 hits in 25,765
  papers, none FHE" needs the corpus manifest (what's in it, snapshot date) + the exact
  grep committed. Without it the claim demotes to "we found none".
- **G7 · Estimator runs, committed (C8.1, C8.2, C6.3, C3.5).** Lattice-estimator commit
  pin, scripts, Kyber-768/1024 validation rows, and runs against **both** shipped secret
  distributions (CBD(10) + ternary shares); re-derive the ~37-bit floor behind C3.5.
- **G8 · Barrel-shift uniqueness artifact (C7.1).** The 65–160-bit uniqueness scan exists
  only in lane notes. Commit the scan script, or better: it is theorem-shaped (cyclotomic
  identities, already script-checked) — a candidate for the G2 lane's queue.
- **G9 · Name the 0.27% harness (C7.4).** The NTT-share-of-proving measurement needs its
  profiling harness + command + workload pinned, or the number leaves and "worthless"
  softens to the committed-quotient + ZK-forfeit arguments alone.
- **G10 · The cost model artifact (C3.4).** The step-function/one-word-band analysis that
  locates the optimum just under 64 bits is ASSUMED-BY-BRIEF with no committed artifact.
  Commit the model (a page of arithmetic + a script), or §3 loses its "why 61 and not 109"
  keystone.
- **G11 · The binary-secrets observation, done right (C8.3).** Pin file+line at a commit;
  check all paper versions/docs for a stated distribution before publishing; phrasing
  stays neutral (reproducibility observation, NOT an attack); courtesy contact to the
  authors before eprint is the right etiquette here — it is their code, our observation.

## Editorial gates

- **G12 · De-tag and final audit.** Strip `[Cn · STATUS]` tags; verify every remaining
  number traces to a closed gate; re-run `paper/scripts/verify_candidate.py` at the
  submission commit; abstract to ≤ 200 words (currently over); title decision (draft
  recommends candidate 3); adversarial read of §7 for anything that scans as an attack
  claim; confirm Rock 2 is exactly one sentence.

## Current gate state

| gate | owner | state |
|---|---|---|
| G1 | red-team lane | in flight (per brief) |
| G2 | Lean lane | in flight (per brief) |
| G3 | experiment lane | in flight (per brief) |
| G4–G11 | unowned | open — found during scaffolding |
| G12 | writing lane | blocked on all above |

Submittable = G1–G12 closed, or the reshaped no-C6 variant with G1/G2/G4–G12 closed and
§5 rewritten as negative result + "what was not one line".
