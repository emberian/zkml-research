# Efficient root-binding audit checkpoint

[SOURCE, 2026-09-08] Read the frozen five-module full_ud_commitment_timing
author package and independent full_ud_root_resolution review. Their accepted
claim is a finite semantic reduction, with initial canonical-word farness and
an explicit existential BadRoots event. Neither claims efficient extraction.
Read the companion BinaryMerkle verifier and deterministic collision lemma
without modifying companion files.

[DERIVED complete] AUDIT.md supplies a lossless observed-two-opening game,
an exact counterexample to pricing semantic existence, and a classical-ROM
prefix-log successor. The honest two-leaf root has semantic double-opening
probability 1−(1−1/N)^(2N), despite zero observed conflicts. The narrower
index-zero event has probability 1−(1−1/N)^(N+1); both are enumerated. The prefix-log
theorem charges at most [((3q²+q)/2)+Rq]/N, including verifier queries, and
requires actual supplied openings and initial extracted-word farness.
It makes no QROM, Fiat–Shamir or concrete-hash instantiation claim.

[EXECUTED] Finite controls passed all 177,211 semantic function tables,
22,016 accepted prefix/opening cases and 1,071 integer budget identities.
An unflagged F5 log gives a word at distance 1/2 from all affine codewords
and positive raw acceptance with a terminal word fixed before queries.
Read BCS2016 §3.1, Block et al. 2023 §3.4 and VCVio ffd0ca1's checkpoint game and
explicit global-query theorem, including its raw-digest-leaf limitation.

[OPEN next] Root must review the new model/event/farness contract before
any formalization. The frozen semantic author/review files remain unchanged.
Searches used three web queries, zero Scry SQL and two local-mirror PDFs;
no PDF download, crypto attack/implementation, Lean run or companion edit.
