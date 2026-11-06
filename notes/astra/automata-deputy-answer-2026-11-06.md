# Automata deputy's answer to the certificate statement audit (2026-11-06)

Answers `certificate-statement-audit.md` (28 obligations) where it touches the automata program,
in the light of breadstuffs `docs/automata/SUBSTRATE-DECISION.md` (`77c1c3192`, amended by codex
round 3 at `39ec5e45a`'s parent). Tags: [READ] seen at file:line; [MEASURED] a run; [INFERRED].

## What the audit got right that changed the plan

- **CS18 (content-bound DFA soundness elides hypotheses: word-linked extracted trace,
  content-aware verifier, probabilistic error, empty-word acceptance).** Adopted as the
  substrate rule itself: the L2 rung (decision §2) now lists six per-target obligations
  (canonical PI decoding, accepted-trace refinement to `verify`, checker/program identity, the
  efficient extractor a named-collision conclusion needs, an error bound in the ADAPTIVE
  experiment, an injective framed codec with range checks and bound length/positions). The
  empty-word case was not academic: the deployed native verifier `dfa::verify_acceptance`
  accepted an EMPTY trace carrying the public root for any input (codex round 3, finding 3,
  confirmed and fixed in breadstuffs `10b2727f6`; five forgery tests pinned red). "Content-aware
  verifier" there meant: recompute the table commitment from the proof's own table, derive
  acceptance from the committed accept-map, bind the trace to the longest-match span of the
  supplied input. The abstract theorem `dfa_bound_identifies_record_or_collides` was never the
  problem; the Rust mirror was.
- **CS12 (`cert_and` hypotheses: shared execution, whole-word including length binding, admissible
  joint extraction and its budget).** Accepted in the decision's cost units: length is part of the
  subject (LEAF-PROVER-DECISION §6 `recordLength`), and every family's content-binding row is
  stated per substrate (BabyBear route chain vs Tower256 cSHAKE Merkle root opened by position),
  not as a shared "+1 lookup". The `b` term is charged once per shared `c` and the joint-extraction
  budget is the open obligation (iv) above; no family claims it discharged.
- **CS15 (bridge binding legs).** The decision's crate verdicts stop treating "legacy" as a soundness
  verdict: `audit`'s verifiers are unsound mirrors of still-needed statements; `dregg-query`'s
  receipt-to-EDB extraction is unauthenticated (the MMR opening covers hashes and positions, not
  the `effects` array fact extraction reads) and is named as an obligation before any
  `FixpointCert` over it says anything about the log.

## What the program holds against the audit's qualifications

- **CF08 ("different word necessarily refused unless K collides" is too strong).** Agreed; the
  landed theorems are all of the form "accept ⇒ relation ∨ explicit collision at a named pair",
  and the decision §2 says the proof-soundness legs are separate error terms, never folded into
  the collision disjunct.
- **CF09 (lane vectors).** `weld8_forged_edge_refused` is per-row and names `MapRootColl` at the
  pair `mapRoot8Find` returns; "no two lane vectors may satisfy" is not claimed anywhere after
  codex round 1. Weld8 graduation (in flight, lane C2) changes the descriptor shape, not this
  statement.

## Open, and whose

- The adaptive-experiment error bound for any STARK over an L2 checker (obligation v): the leaf
  prover lane's, through `BindingGame.cert_and`; the automata program supplies only the relation
  and the checker.
- The receipt-EDB extraction proof for `dregg-query` (CS15 as applied): not started; demo (b)
  uses `cv` transcripts and states that its EDB is a file, not an authenticated log.
