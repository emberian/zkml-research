# SUBMISSION GATES — Rock 1 paper

2026-08-13. What must land before DRAFT.md is submittable, in dependency order. A gate is
closed by an artifact (a committed script, a pinned transcript, a built Lean theorem), not
by a lane's summary — harvest with `cv workflow`, audit statements, build the tree.

**Updated 2026-08-13 (late): G1–G3 closed** — results in notes/two-rocks.md "GATE RESULTS
(2026-08-13)", applied to DRAFT.md + CLAIM-LEDGER.md the same day. New gates G13–G15
created from what the lanes found.

## The three briefed lanes — ALL CLOSED 2026-08-13

- **G1 · CLOSED — red-team reproduction of the Zama ceiling (C2).** Reproduced at a
  pinned commit with the mechanism made precise: `Domain::new` returns `None`, the
  `.expect` in `WhirConfig::new` panics, and rate log_rho_inv = 1 turns the 2³² domain
  cap into D·t·n ≤ 2³¹; the one-doubling distance measured. Also delivered: the family
  law independently re-derived; the boundary claim (C1.4) re-grepped with pinned counts;
  the security-model reconciliation **closed to the 2019 HE standard's own formula and
  table row**; and **four mandatory corrections**, all applied 2026-08-13 —
  (1) prior-art: p61 appears in a 2014 candidate-moduli table, never deployed (C4.7);
  (2) noise floor **55–59 bits, not 51** (C6.2); (3) candidate core-SVP **213.7, not
  205**, and the deployed secret is **CBD η = 20**, not ternary/CBD(10) (C6.3, C8.1,
  C8.4); (4) barrel-shift uniqueness restated with its true scope (C7.1). Two precision
  notes folded without changing conclusions: the early notes' literal
  `Domain::new(2^32, 2)` call overshot the boundary 4× and named the wrong call.
  Transcripts → G15 bundle.
- **G2 · CLOSED — Lean certificate suite (C4, C5, C9).** minidregg
  `Theory/CyclotomicInertia.lean` @ **641ceeb** (+697 lines): the family law verbatim
  (`familyP_maximalInertia_iff`); p61 fully certified (**kernel-checked Lucas**
  `p61_prime`, 2-adicity exactly 54, `p61_mod_8192`, inertia via the law, conductor-81
  field); the n = 214 counterexample proved (`familyP_214_prime` — 67 digits,
  `card_factors_9_familyP_214` — Φ₉ into exactly three quadratic factors);
  `goldilocks_prime`; and the domain-availability lemma with
  **`goldilocks_no_domain_two_pow_33` = the §1 panic as mathematics**. Zero `sorry`, no
  `native_decide`, axiom pins ≤ [propext, Classical.choice, Quot.sound]. **Residue:** the
  fold congruence 2⁶¹ ≡ 2⁵⁴ − 1 (C4.4) is script-only — a two-line theorem, folded into
  G12's audit.
- **G3 · CLOSED — the modulus-swap experiment (C6).** **CONFIRMED on mechanism** (domain
  ceiling 2³² → 2⁵⁴ by execution at the pinned WHIR rev; e2e prove/verify to ν = 29;
  p61 **10–40% faster** at equal proof sizes — one machine, M2 Max, interleaved runs),
  **REFUTED on "one line"** (four hidden Goldilocks structures; **12/12 unit tests green
  while decryption was garbage**; ~20-line field-generic repair, 13/13 on both fields).
  §5 rewritten as the result — the refutation is the thesis's second witness. Artifacts
  → G15.

## Gaps found while scaffolding (nobody owns these yet)

- **G4 · Census reconciliation — REAL DISCREPANCY, unchanged by today's gates.** The
  brief says "104 Solinas + 106 Proth"; the committed script finds **117 Solinas** in
  a ∈ [96,130] (and confirms the notes' 93 at 2-adicity ≥ 20). Either commit the original
  census lane's script and reconcile parameterizations, or adopt
  `paper/scripts/verify_candidate.py` as the census of record and renumber the draft.
  Also owns the Proth-side census (C3.3). **Until closed, the draft quotes only 117/93.**
- **G5 · Enumerate the six adopt-a-proof-prime papers.** Only 2026/027 and GBFV are named
  in notes. Related work (C1.2) needs all six with citations, and a quote-check of
  HELIOPOLIS §6.2 and 2025/286 (C1.3) — these two get full-credit framing, so get their
  claims exactly right. **Also owns pinning the C4.7 prior-art references**: the 2014
  stylewarning/lisp-random candidate-moduli table and the hypergeometrica comment
  carry-over — URL + file + commit for each.
- **G6 · Corpus pin for the boundary claim (C1.4, C7.4-novelty).** "39 hits in 25,765
  papers, none FHE" needs the corpus manifest (what's in it, snapshot date) + the exact
  grep committed. The red team re-grepped with pinned counts 2026-08-13 (unchanged); the
  committed manifest is still the artifact owed. Without it the claim demotes to "we
  found none".
- **G7 · Estimator + noise-floor runs, committed (C8.1, C8.2, C6.2, C6.3, C3.5).**
  Lattice-estimator commit pin, scripts, Kyber-768/1024 validation rows, and runs against
  **both** shipped secret distributions — **CBD η = 20 (support ±20, variance 10; the
  corrected reading)** and ternary shares. Must reproduce the quoted numbers: candidate
  core-SVP **213.7 (β = 732)**; deployed actual-distribution **98.1 / 130.5**; Zama
  **104.6 / 74.2**. Also commits the **noise-floor derivation** (55–59 bits, the 2.4-bit
  margin at 8-bit weights, the exact-division-encoding dependence), and re-derives the
  ~37-bit floor behind C3.5.
- **G8 · Barrel-shift scan artifact (C7.1, C4.6) — restated scope.** The claim is now:
  primes Φ_m(2ᵇ) in **64–160 bits with 2-adicity ≥ 9** ⇒ Goldilocks unique; the six-way
  form identity; the 37-prime count at 65–160; the F₇ 73-bit-factor
  sufficient-not-necessary example; ord_p61(2) ≈ 2⁵⁷. Commit the scan scripts + outputs.
  **Blocked on G13 + G14** — the red team spot-corrected the conclusions, but the scripts
  themselves still carry the bugs and must not ship in the artifact until fixed and
  re-run.
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

## New gates from the gate results (2026-08-13)

- **G13 · Fix the factorint-limit bug in the scan scripts.** sympy `factorint` called
  with a `limit=` silently returns composite cofactors as though fully factored — a real
  bug the red team found in the barrel-shift scan scripts. Fix, re-run, and diff the
  output against the red team's corrected counts before the G8 artifact ships.
- **G14 · Fix the primesearch `ms` list.** The prime-search script's `ms` list (the
  cyclotomic indices it scans) needs the red team's fix; apply it, re-run, and confirm
  the six-way form identity and the adicity ≥ 9 uniqueness reproduce from the committed
  script.
- **G15 · The execution artifact bundle (C2, C6).** Everything currently living only in
  lane transcripts: the pinned 2026/027 commit + the `WhirConfig::new` panic transcript
  and D·t·n derivation (G1); the pinned WHIR rev, the swap diff **plus the ~20-line
  encode/decode repair**, the ν = 29 e2e transcript, the raw interleaved benchmark
  outputs behind "10–40% at equal proof sizes, M2 Max", and the
  12/12-green-while-decryption-was-garbage reproduction — the paper's best exhibit.

## Which number comes from which artifact

Provenance map so the artifact bundle is checkable line-by-line. "Committed" means in
this repo (or pinned sibling commit); everything else names the gate that commits it.

| number(s) in the draft | source artifact | status |
|---|---|---|
| census 117 / 93; 2-adicity 54 + ω of order 2⁵⁴; fold congruence; Crandall ≤ 12; family scan n ≤ 80 (n = 214 found); Goldilocks Φ-identities + adicity 32 | paper/scripts/verify_candidate.py (output pinned: verify_candidate.out) | committed |
| primality (p61, Goldilocks, familyP 214); family law ⟺; inertia; domain availability (incl. `goldilocks_no_domain_two_pow_33`) | minidregg Theory/CyclotomicInertia.lean @ 641ceeb | committed (sibling repo — pin the commit in the artifact bundle) |
| D·t·n ≤ 2³¹ mechanism; one-doubling distance | red-team transcript at pinned 2026/027 commit | uncommitted → G15 |
| domain 2³² → 2⁵⁴ by execution; ν = 29 e2e; 10–40% at equal proof sizes; 12/12-vs-garbage; 13/13 both fields | experiment at pinned WHIR rev | uncommitted → G15 |
| noise floor 55–59; 2.4-bit margin at 8-bit weights | red-team noise derivation (fhe.rs sampled distributions, exact-division encoding) | uncommitted → G7 |
| 213.7 (β = 732); 98.1 / 130.5; 104.6 / 74.2; Kyber validation rows | red-team estimator scripts | uncommitted → G7 |
| 37 form-primes in 65–160; adicity ≥ 9 uniqueness; six-way identity; F₇ 73-bit factor; ord_p61(2) ≈ 2⁵⁷ | scan scripts | uncommitted → G8, **blocked on G13/G14** |
| 39 hits / 25,765 corpus | corpus grep (red-team re-run, counts pinned in its notes) | uncommitted → G6 |
| the 2014 candidate-moduli listing | stylewarning/lisp-random + hypergeometrica references | unpinned → G5 |

## Editorial gates

- **G12 · De-tag and final audit.** Strip `[Cn · STATUS]` tags; verify every remaining
  number traces to a closed gate; re-run `paper/scripts/verify_candidate.py` at the
  submission commit; abstract to ≤ 200 words (currently over); title decision (draft
  recommends candidate 3); adversarial read of §7 for anything that scans as an attack
  claim; confirm Rock 2 is exactly one sentence. **Added 2026-08-13:** land the two-line
  fold-congruence theorem (the G2 residue, C4.4) or re-word §4's reduction row to
  "script-checked"; and verify the four red-team corrections survived editing — grep the
  final text for `205`, a bare `51`-bit floor, `65–160` as the uniqueness window,
  `CBD(10)`, and any prose implying p61 has barrel-shift twiddles.

## Current gate state

| gate | owner | state |
|---|---|---|
| G1 | red-team lane | **CLOSED 2026-08-13** (transcripts → G15) |
| G2 | Lean lane | **CLOSED 2026-08-13** (minidregg @ 641ceeb) |
| G3 | experiment lane | **CLOSED 2026-08-13** (artifacts → G15) |
| G4–G11 | unowned | open — found during scaffolding |
| G13–G15 | unowned | open — created from the gate results |
| G12 | writing lane | blocked on all open gates |

Submittable = G4–G15 closed. The "reshaped no-C6 variant" contingency is **retired**:
C6 landed with a split verdict, and §5 as now written already carries it — the mechanism
confirmed, and "what was not one line" promoted from fallback to centerpiece.
