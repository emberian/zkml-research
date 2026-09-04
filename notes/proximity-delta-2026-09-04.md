# Proximity-gap delta, 2026-08-15 → 2026-09-04 — and what it does to UDR 34 / JBR 73 / "never quote 130"

2026-09-04, proof-system-theory lane. Question: what moved on Reed–Solomon proximity gaps,
correlated agreement (CA / MCA), FRI/STIR/WHIR soundness and the regime question since the
campaign's last activity (2026-08-18), and does it change VERDICTS §2's accounting.

Provenance legend: **[READ]** quoted from source at URL/page · **[DERIVED]** my arithmetic from
named inputs · **[INFERRED]** my reconstruction · **[OURS]** measured/proved in our tree, cited by
note. Ground truth read first: VERDICTS §1b, §2, §7; `notes/two-regime-calculator.md`,
`grey-lit-corrections.md` §4, `num-queries-pin.md` §5, `blowup-drop.md` §7,
`multilinear-pcs-landscape.md` §6.5/§8, `formalization-frontier.md`; breadstuffs
`metatheory/Dregg2/Circuit/FriLedger.lean:195-285`; minidregg `Selvage/JohnsonRegime.lean`,
`Selvage/HalfThresholdRegime.lean`, `Assurance/TwoRegimeQueryBudget.lean:80-135`.

## 0. Verdict in one paragraph

**Nothing published in the window moves UDR 34, JBR 73, or the "never quote 130" rule.** No
proximity-gap / CA / MCA / FRI / STIR / WHIR paper appeared on eprint (ids 1661–1861 by title) or
arXiv (catalog to 2026-08-27) after 2026-08-15; `ethereum/soundcalc` has not committed since
2026-07-23 and still reports UDR + JBR only; `starkware-libs/stwo` has not committed since
2026-08-13. **Three things did move, and two of them touch VERDICTS sentences:**
(a) ⚑ **the "personal communication" legs of BCSS25 (= eprint 2025/2055) are now both public** —
`[Sta25]` is eprint **2026/532** (S-two whitepaper, Mar 2026, App. A.2 Thm 28/29) and `[Hab25]`
is eprint **2025/2110** — so VERDICTS §1b's caveat and `FriLedger.lean:270`'s *"Neither is
public"* are stale (pre-window publication, undigested by us); (b) ⚑ **Plonky3 `p3-security`
v0.7.0 (2026-09-03/04) re-added the withdrawn-regime formula as `legacy_conjectured_error =
log_blowup·num_queries + query_pow`** — *literally our `capacityBits` = 130* — beside a
DG25-"random-words" conjectured bound that reads **128.40** at our IR-v2 config; the rule
"never quote 130" is now also a rule about what a downstream `p3-security` call will hand back;
(c) ⚑ **Ethereum Foundation's `better.codes` (launched 2026-08-20)** puts a Lean/ArkLib
kernel-checked proximity-gap bound on a public leaderboard: on a KoalaBear-sextic interleaved-RS
toy at ρ = 1/2 the *proven* lower bound is **68.02 bits** against an explicit *attack* at
**116.13 bits** (baselines 64.00 / 116.49) — the proven-vs-conjectured gap, measured at source,
is ~48 bits on the Prize's own instance. Grinding: three independent sources read at source
(2026/532 §5, `p3-security/src/grinding.rs`, `soundcalc/common/utils.py`) all treat PoW as
additive-to-the-round-it-precedes and regime-free — VERDICTS §2's sentence holds, with one
refinement (§3.4).

## 1. What we hold (the numbers at stake)

- **[OURS]** IR-v2 (lb = 6, q = 19, pow = 16): **UDR 34 / JBR 73 / CBR 130**; per query 0.9776 /
  3 / 6 bits; `ir2_three_regimes` (`TwoRegimeQueryBudget.lean:354-357`), `cbr_not_reportable`
  a theorem (`:146`). `FriLedger.lean:203-204` exports only `johnsonBits := q·lb/2 + pow` and
  `capacityBits := q·lb + pow`; no UDR column in the exported ledger. VERDICTS §2.
- **[OURS]** Commit column ε_C is BCIKS20 Thm 8.3, reading 51 at the deployed wrap; the query
  column and ε_C are deliberately NOT composed (`TwoRegimeQueryBudget.lean:84-93`); VERDICTS
  §1b prices the 2025 bound at +17–21 bits with the caveat *"BCSS25 states no FRI theorem and
  its Thm 4.3 plugs into a personal communication."*
- **[OURS]** `FriLedger.lean:262-280`, the sentence this note stales: *"Thm 4.3's entire proof
  is 'obtained by plugging in the improved bounds in the proof of [Sta25, Theorem 22]' — and
  [Sta25] is a PERSONAL COMMUNICATION (S-two whitepaper), as is [Hab25], which Thm 4.6 rests
  on. Neither is public."*
- **[OURS]** Selvage carries MCA past unique decoding as a *named* `Prop`
  (`JohnsonRegime.WHIRConjecture412`; the hard core `JohnsonMcaBridge.HaboeckTheorem2` is a
  hypothesis), and `HalfThresholdRegime.lean` formalizes the Chai–Fan 2026/858 half-threshold
  lemma. `formalization-frontier.md` already records IoTeX's Lean (2026/858), zksecurity's
  `simple-rbr-fri` (2025/1993 Thm 5.2, conditional on `FRI_MCA_Hypothesis`) and
  deltastar.computer. Nothing below is "new to us" on those.

## 2. The window sweep — corpus + instrument

| corpus | instrument | result |
|---|---|---|
| eprint 2026 year listing, ids **1661–1861** (two pages, `?offset=0,100`, titles+authors, parsed 2026-09-04) | title regex `proxim\|correlated\|agreement\|list.?decod\|johnson\|FRI\|STIR\|WHIR\|Reed\|fold\|grind\|proof.of.work\|soundness\|IOP\|capacity\|DEEP\|Basefold\|Ligero\|polynomial commit\|linear code\|interleav\|batch\|STARK\|hash-based\|code-based\|Fiat\|round-by-round` | **∅ on proximity gaps / CA / MCA / FRI / STIR / WHIR.** Adjacent hits only: 1839 Quasar (QA-code BaseFold PCS, "100-bit security", regime unstated in abstract), 1838 Fenzi (FS on generated R1CS), 1857 LatticeBlindFold, 1809 PikkuFold, 1679 Critical-Round Special Soundness (Aug 13, pre-window). 1839/1838 are owned by `eprint-delta-2026-09-04.md`. ⚠ The listing is paginated at 100/page, not "one fetch". |
| IACR mirror `/Users/ember/dev/gh/forks/IACR-eprint-mirror/2026/` | `ls`, ids > 1718 landed at read time: 1719–1724 | none relevant |
| scry `academic.catalog` (built through 2026-08-27, `freshness_lag` 8.4 d) | `hasAllTokens(title,['proximity','gaps']) OR ['correlated','agreement'] OR abstract ['proximity','gaps','reed']`, LIMIT 40, ORDER BY published_at DESC | newest relevant = **2607.10572 (2026-07-12)**, then 2605.07595 (v2 2026-07-10), 2607.08516 (07-09), 2601.10047 (v2 06-10), 2604.09724 (04-09). **Nothing after Jul 22 on these tokens.** |
| kagi, 7 queries (proximity gaps 2026; soundcalc; capacity refutations; MCA August; Proximity Prize status; grinding composition; WHIR/STIR since August) | ranked web | no post-08-15 paper; surfaced `blog.ethereum.org/2026/08/20/better-codes-challenge`, `proximityprize.org` ("$0 in prizes" awarded), hclivess/stark-soundness-analysis (grey, unread), IoTeX repo (known) |
| `gh api repos/ethereum/soundcalc/commits?since=2026-08-15` | GitHub API | **∅**; `pushed_at 2026-07-23T16:28:22Z`; last 15 commits are zkDTVM v0.8.0 / OpenVM 2.0 / SWIRL loader (Jul 13–23) |
| `gh api repos/starkware-libs/stwo/commits?sha=dev&since=2026-08-15` | GitHub API | **0 commits**; `pushed_at 2026-08-13T07:00:46Z` |
| `gh api repos/Plonky3/Plonky3/commits?path=fri&since=2026-08-15` and `security/CHANGELOG.md` | GitHub API | **5 FRI commits** (incl. #1982 merged 08-17; v0.7.0 released 09-04) and **3 `p3-security` PRs** (#1998, #2007, #2018) — §3.3 |
| `~/paperbin` (1,659 files) | `ls \| grep` proximity/MCA/FRI/etc. | holds **2026/1432, Chojecki ×2, 2607.10572, 2607.08516, 2026/1561, 2025/870, 2025/2054** — none of which `grep -rli` finds in `notes/` or `docs/` (§3.1) |

## 3. Item by item

### 3.1 Target 1 — literature since Aug 15: none; a July digestion gap instead

**Since 2026-08-15: nothing** (table above). The last movement in the band is July 2026, and
five of those papers sit in `~/paperbin` un-noted. What they prove, and why none touches us:

- **eprint 2026/1432, Jo (Georgia Tech), July 2026, "RS MCA Beyond the Johnson Radius"**
  [READ, abstract p.1]: *"Fix integers r ≥ 2 and h ≥ 1 … at error budget E = n − ⌊√(n(K−1))⌋ + h
  … every affine line has at most O_{r,h}(K⁶) bad parameters. Hence ε_mca(C,E) = O_{r,h}(K⁶/q)
  … in relative-radius units, the gain is O(1/n)."* Concrete: *"With K = 2¹⁸, the first
  post-Johnson budget has MCA error below 2⁻¹²⁸ at rates 1/2, 1/4, 1/8, and 1/16"* over an
  explicit prime **Q < 2²⁵⁶**. [DERIVED] At our BabyBear⁴ (|F| ≈ 2^123.6) and K ≤ 2²¹, K⁶/q ≈
  2^{126−123.6} > 1: **vacuous at our field**; and an O(1/n) relative-radius gain at n = 2²⁷ is
  ~2⁻²⁷ of radius. Touches JBR's *definition* (θ = 1−√ρ) by an integer step; moves **no** number.
- **arXiv 2607.10572, Gao–Yang–Xu–Kan (Fudan), 2026-07-12** [READ, abstract]: *"Given an explicit
  counterexample to the (p,L)-list-decodability of a linear code over F_q, we construct a related
  code C′ of the same length and dimension such that err_MCA(C′,p) ≥ (1/q)⌈(L+1)q/(q+L)⌉, while
  decreasing its minimum distance by at most one."* A **negative** transfer (list-decoding
  counterexamples ⟹ MCA error floors), RS as the Vandermonde specialization. Corroborates the
  CBR withdrawal; moves nothing.
- **arXiv 2607.08516, Goyal–Guruswami–Sun–Wootters, 2026-07-09, "Locality of Curve-Decoding and
  Improved Proximity Gaps"** [READ, abstract]: improved proximity gaps for **random** ensembles
  (random linear codes, *"Reed-Solomon codes with random evaluation points"*, Gallager LDPC),
  matching [GG25]'s subspace-design parameters by a black-box transfer. **Not smooth domains** —
  our D is a 2-adic coset — so it does not reach FRI as deployed. Positive result, wrong code.
- **Chojecki (Ulam.ai), July 17/23 2026, "Shortening Bounds for RS MCA" and "Conjectures and
  Barriers for RS–MCA"** [READ, abstracts]: single-author, self-described partial: *"The
  unrestricted subexponential-budget smooth/circle frontier remains open because shortening has
  positive exponential cost and the analytic payment … are not yet available."* Grey-adjacent;
  no theorem at our parameters.
- **eprint 2026/1561, DeepBrake (CAS/Xidian)** [READ, abstract]: row-wise RS Brakedown-style
  commitments for arbitrary points that *can* exploit Johnson-radius proximity; a PCS design,
  not a bound. Not our route (BaseFold at RS per `multilinear-pcs-verdict.md`).
- ⚠ **2026/680 (Arnon–Boneh–Fenzi) was UPDATED in July 2026** — eprint abstract page: *"July 2026
  Update: Updated KKH comparison and concrete estimate of attacks."* Both our copies
  (`~/paperbin/open-problems-…-2026-680.pdf`, mirror `2026/680.pdf`) are the **April 8, 2026 v1**
  (`pdftotext -l 1` → "April 8, 2026"; `grep KKH` → ∅). The "concrete estimate of attacks" is the
  part that would bear on how far above Johnson a real attacker gets. **Refetch via the mirror
  sync, not by hand.**

**Verdict-relevant?** No. JBR 73 is a θ = 1−√ρ query count and none of these lowers the Johnson
radius for smooth-domain RS at our field; UDR 34 needs no literature; the CBR withdrawal is
*strengthened* (2607.10572).

### 3.2 Target 2 — BCSS25's "personal communication" legs are now public; the FRI theorem question

**Identification** [READ]: "BCSS25" in VERDICTS §1b / `koalabear-migration.md:837,1071,1399` /
`FriLedger.lean:262-280` is **eprint 2025/2055, Ben-Sasson–Carmon–Haböck–Kopparty–Saraf,
"Proximity Gaps for Reed–Solomon Codes"** (soundcalc and `p3-security` call it BCHKS25). Its
bibliography (`~/paperbin/proximity-gaps-reed-solomon-bensasson-habock-2025-2055.txt:2847`):
*"[Sta25] StarkWare Team. S-two whitepaper. 2025. (Personal communication)."* and `:2816`
*"[Hab25] Ulrich Haböck. A note on mutual correlated agreement. 2025. (Personal communication)."*
Thm 4.3 (`:1581-1593`): *"The theorem is obtained by plugging in the improved bounds in the proof
of [Sta25, Theorem 22]. Notably, the theorem immediately implies the weighted correlated agreement
theorem in a simpler form than stated by [BCI+20, Theorem 7.2]."*

**What is public now** [READ]:
- **[Sta25] = eprint 2026/532**, "S-two Whitepaper", Carmon, Goldberg, Haböck, Lerer, Lesokhin
  (StarkWare) + Papini, Samocha (Attestable), posted March 2026 (`mirror-mine-2026-08.md:41`
  noted the paper; nobody connected it to [Sta25]). **Appendix A.2 "Correlated agreement under
  constraints"** (`~/paperbin/stwo-whitepaper-eprint2026-532.txt:3040-3290`): *"two strengthened
  statements on correlated agreement, Theorem 28 and 31 below, which are a byproduct of the proof
  in [BCI+20], yet require an explicit discussion. We focus on the Johnson regime, with proximity
  parameter θ ∈ [δ/2, 1−√(1−δ))."* **Theorem 25 ([BCI+20, BCH+25])** — curve-decodability up to
  Johnson with the improved bounds: threshold `a = ℓ_GS(θ)·b`, `b ≥ (2ℓ_GS(θ)⁴/3·(1−δ)+1)·M·|D|`.
  **Theorem 28 (CA over given sets)**: *"If |S| > ℓ_GS(θ)·(2ℓ_GS(θ)⁴/3·(1−δ)+1)·M·|D| … then
  there exists z₀ ∈ S and (p₀,…,p_M) ∈ C^{M+1}, so that (p₀,…,p_M)|_A = (f₀,…,f_M)|_A over
  A = A_{z₀}."* Proof: *"By Theorem 25 there is a curve of polynomials …"* — self-contained given
  Thm 25. **Theorem 29 (CA with weights)** follows; **Remark 30**: *"the proof of both Theorem 28
  and Theorem 29 carry over to the unique decoding regime, with the smaller bound |S| > M·|D|."*
  (The numbering shifted: 2055's "[Sta25, Theorem 22]" is 532's Thm 28; 532's Thm 22 is the BCS
  transform bound.)
- **[Hab25] = eprint 2025/2110** (Haböck, "A note on mutual correlated agreement for
  Reed-Solomon codes", Nov 2025) — in paperbin and already cited by `JohnsonRegime.lean` and
  `multilinear-pcs-landscape.md`; the tree simply had not matched it to Thm 4.6's citation.

**So: the citation chain for a 2025 FRI commit bound is now readable end to end.** BCIKS20 Lemma
8.2 needs weighted CA over curves per round (Thm 7.2); 2055 Cor 4.4 supplies it with the improved
constants, via Thm 4.3, via 532 Thm 28/29 — a published (eprint, non-peer-reviewed, vendor
whitepaper) document. The **weaker-than-2020** part of §1b's caveat is now *"rests on a vendor
whitepaper's appendix"* rather than *"rests on something we cannot read."*

**Has a FRI-specific theorem with the 2025 bounds appeared?** Partly, and not for our FRI:
- **2026/532 Theorem 19** [READ `:1836-1875`], *"(IOPP soundness multi-domain circle FRI). For
  proximity parameter θ ∈ [δ/2, 1−√(1−δ)) … Protocol 3 is a round-by-round knowledge-sound IOP
  … (Batching step) ε_FRI,batch = (M−1)·ℓ_GS(θ)·(2ℓ_GS(θ)⁴/3·(1−δ)+1)·|D₀|/|F|; (Folding
  steps) ε_FRI,fold,k = 3·ℓ_k(θ)·(2ℓ_k(θ)⁴/3·(1−δ_k)+1)·|S_k|/|F|; (Query phase) ε_FRI,query =
  (1−θ)^s."* Preceded by *"We state soundness using the recently improved bounds from [BCH+25]."*
  **This is a FRI theorem carrying the 2025 bounds, at Johnson — for circle codes over M31.**
  Its own text (`:2684`): *"The not yet published manuscript [HHM25]"* for lifted/non-circle FRI
  — the classic-FRI variant is **still announced, not published** (kagi/eprint: no HHM25 found;
  absence line in §6).
- **2024/1553** (Atapoor–Delpech de Saint Guilhem–Kindi, "STARK-based Signatures from the RPO
  Permutation") [READ, mirror] — **Theorem 2 (DEEP-ALI RbR Soundness, list decoding)** and
  **Theorem 3 (unique decoding)**, with App. A.2 "Correlated Weighted Agreement" restating
  BCIKS20's weighted CA. This is the FRI RbR theorem `p3-security` composes with 2055 Thm 4.2/1.5
  (`security/src/fri.rs:3-5`: *"Proven regime: round-by-round, [2024/1553] Theorems 2 & 3, with
  the BCHKS25 LDR commit bound ([2025/2055] Theorem 4.2)."*). So upstream's "proven LDR" FRI
  number is exactly the assembly `FriLedger.lean:279` calls *"an assembly that is OURS, resting
  on a citation we cannot read"* — and the citation is now readable.

**Moves 34/73/130?** No. It moves the **commit column** (ε_C = 51 at the wrap, BCIKS20) by the
already-priced +17–31 bits (VERDICTS §1b, `FriLedger.lean:262`), and only once the composition is
done. **Re-derivation cost** [INFERRED from the files]: a second ε_C formula transcribed into
`FriLedger.lean` beside `friCommitLedger` (2055 Thm 1.5 eq. (1), the form `p3-security`
`commit_phase_error_ldr_m` implements at `fri.rs:158-201`), plus a `FriLedgerSound` lemma of the
`ledger_perFoldBits_sound` shape — days, not weeks; the paper-level step "BCIKS20's round
analysis accepts 532 Thm 29" is a citation now, not a hole. Pessimistic reading: 532 is a vendor
whitepaper with *"proofs postponed to the Appendix"* and no peer review; its Thm 28 proof is a
half page and I did not audit it line by line.

### 3.3 Target 3 — deployed calculators and libraries

**`ethereum/soundcalc`** [READ, README @ main, unchanged since 2026-07-23]: *"UDR (Unique
Decoding Regime): θ ≤ (1−ρ)/2 … JBR (Johnson Bound Regime): (1−ρ)/2 < θ < 1−√ρ"*; *"we have
incorporated: The improved UDR and JBR security bounds of BCHKS25 … The removal of the CBR
regime, following the results of DG25 and CS25."* `apply_grinding(error, g) = error·2^{−g}`.
Nothing to update; `two-regime-calculator.md` stands (license still absent — `gh api` returns
`license: null`).

**Plonky3 `p3-security` v0.7.0 (released 2026-09-04)** — three PRs in the window plus one two
days before it:
- ⚑ **#2018 (merged 2026-09-03) "add legacy conjectured FRI soundness bound"** [READ, PR body]:
  *"Add a legacy variant for computing the (old) conjectured security bound as specified in the
  ethSTARK paper, for downstream users who may need an easier compute methodology at the cost of
  few bits offset."* `security/src/fri.rs:109-111`:
  `legacy_conjectured_error = log_blowup * num_queries + query_pow_bits`, docstring *"(ethSTARK
  2021/582, pre-random-words) … does not account for the commit-phase folding round … kept for
  callers that specifically want the older, simpler heuristic bound."*
  **[OURS] That is `FriLedger.lean:204` `capacityBits := numQueries·logBlowup + powBits` = 130,
  character for character.** The regime soundcalc deleted is back upstream under the word
  "legacy". VERDICTS §2's *"Never quote 130"* is unchanged in force and gains a concrete
  attack surface: any downstream that reads `legacy_conjectured_error` reports our 130.
- **The non-legacy "conjectured" is DG25's random-words heuristic** [READ `fri.rs:80-99`]:
  *"Conjectured low-degree-test soundness (random-words, [2025/2010] §1.5). b = num_queries ·
  (−log2(ρ+η)) + query_pow, with η ≈ (log2(e/ρ)·ρ)/log2(q)."* [DERIVED, BabyBear⁴ modulus_bits
  = 123.628]: at (6,19,16) **5.916 bits/query → 128.40**; at (3,38,14) 126.06; (3,38,16)
  128.06; (2,57,16) 127.74; a child's (6,1,16) **21.92** (vs our CBR 22). So Plonky3's
  "conjectured" is CBR-shaped to within 1.6 bits at our config — the number the withdrawal
  removed, re-justified by *"treats a malicious prover's committed word as distributed like a
  uniformly random word, whose distance to the code concentrates at capacity 1−ρ"*
  (`proximity.rs:53-61`). `SecurityAssumption::CapacityBound` also still exists in
  `assumption.rs:53-56` (*"Requires conjecturing capacity-rate list decodability and correlated
  agreement up to capacity"*), though `fri.rs:14` says FRI's commit phase does not support it.
  ⚠ VERDICTS §2 *"Four of five production systems refuse the capacity conjecture; we are the
  outlier"* — Plonky3-the-library keeps two capacity-shaped columns; whether any *system* quotes
  them was not checked here.
- **#1978 (merged 2026-08-13, two days pre-window, undigested)** [READ, PR body]: *"Conjectured
  security was computed from the FRI query phase alone. Two other things also limit it, and
  neither was counted: the FRI folding rounds … the instance itself … Both omissions push the
  reported number up, so the fix pushes it down."* Table: `compute_ldt_only` blowup 2: 128 →
  125; blowup 8: 128 → **119**; `compute_from_params` 96-bit field: 84…66 → 82…64. Touches
  VERDICTS §7.9 (*"Plonky3's p3-security says [d=5] reaches 128"*): that 128 predates #1978.
- **#2007 (merged 2026-09-03)** [READ, PR body]: the OOD round *"bounded the DEEP-ALI degree as
  (d+1)·height, implicitly assuming a single out-of-domain point per column. An AIR that also
  opens next-row rotations references a second out-of-domain point, which needs an extra
  (combo−1)·(d−1) term — omitting it understated the round's error (i.e. overstated security)
  by a fraction of a bit."* [OURS] `FriLedger.lean` has no `combo`/OOD term at all (`grep -in
  'combo\|ood\|deep'` → only the BCSS25 prose at `:272`); our DEEP-ALI column lives elsewhere or
  nowhere — **a check item, sub-bit, not a number to quote.**
- **#1982 merged 2026-08-17** (`gh api pulls/1982`: `state=closed merged_at=2026-08-17T08:48:31Z`,
  "fix(fri): call bit_reverse_rows after coset_dft_batch in get_evaluations_on_domain").
  **VERDICTS §7.0 says *"PR #1982 is the same change and is STILL OPEN / CHANGES_REQUESTED
  (checked 08-14)"* — stale.** Owned by `systems-delta-2026-09-04.md` §7; recorded here because
  it is the FRI extrapolation path our vendored patch carries.
- **VERDICTS §1b** *"there is no `p3-security` crate (it is `uni-stark/src/security.rs`)"* —
  [READ] `security/Cargo.toml` `name = "p3-security"` exists since #1686 (2026-07-08);
  `uni-stark/src/security.rs` **also** still exists (27,098 bytes at HEAD). Both true now.

**StarkWare S-two** (2026/532, Table 5/6 [READ `:2555-2600`]): example parameters *"for 100 bit
soundness, with maximum grinding difficulty of 26 bits"*, Johnson regime `log₂(1−θ)` 0.45–1.83
with `s_θ` = 41–165 queries, and a *separate* Table 6 *"in the conjectured regime, for distances
θ up to the Elias radius"* — StarkWare publishes both columns and labels the second conjectured.
No stwo code movement since 08-13.

**WHIR / STIR**: no new soundness analysis found (kagi q7; eprint titles). Plonky3 shipped
`p3-whir` v0.7.0 and a `stir` module in `p3-security` (#1998 *"fallible config derivation &
dedup eta-parameterized security formulas"*) — engineering, not bounds; `p3-whir` is not a
dependency of ours (`FriLedger.lean:276`).

### 3.4 Target 4 — grinding composition: three sources agree, one refinement

VERDICTS §2: *"`pow` is additive and regime-free; a query is multiplicative and regime-bound."*
At source, in the window and just before it:
- **2026/532 §5 "Grinding"** [READ `:2435-2455`]: *"This reduces the soundness error ε_i of that
  round down to ε′_i = 2^{−z_i}·ε_i, at the cost of completeness … We stress the fact that salts
  do not affect Theorem 22, since the BCS state-restoration analysis presumes them per default."*
  Per-round, multiplicative on error = additive in bits, no regime term.
- **`p3-security/src/grinding.rs`** [READ, full file, 88 lines]: *"A grind sited immediately
  before a Fiat–Shamir challenge forces a malicious prover to redo 2^pow_bits work per
  resampling attempt, so it adds pow_bits to the round-by-round error of the round that
  challenge opens (ethSTARK 2021/582 §5, and 2024/1553 §2)."* `boost(error, pow) =
  error.bits() + pow`. And: *"The low-degree test's own grinding sites (e.g. FRI's query- and
  commit-phase proof-of-work) are not modeled here: a LowDegreeTest implementation carries
  those itself (`FriRegime::query_pow_bits` / `FriRegime::commit_pow_bits`)."*
- **soundcalc** `apply_grinding = error · 2^{−g}` [READ].

**Nobody disagrees.** The refinement worth writing down: grinding is additive **to the round it
precedes**, so query-PoW never reaches ε_C — which is our theorem
`query_and_pow_cannot_pass_epsC` (`koalabear-migration.md:841`) — **but commit-phase PoW does**:
`fri.rs:153` adds `commit_pow_bits` to `commit_phase_error_udr`, and `:194,201` to the LDR
variant. [OURS] every `commit_proof_of_work_bits` in our tree is 0 (`grind-phase.md:87`;
`commit_pow_cost_measure.rs` prices the knob's cost). If the binding column at Johnson is ε_C
= 51, commit PoW is the one additive lever on it, and upstream's own model says so. Not a
number; a priced-cost/unpriced-benefit pair.

### 3.5 Target 5 — mechanized proximity-gap results

- ⚑ **`better.codes` (EF Formal Verification team + Yukon + zkSecurity), launched 2026-08-20**
  [READ, `blog.ethereum.org/2026/08/20/better-codes-challenge`]: *"takes a self-contained problem
  from the Proximity Prize research, formalized in Lean, and puts its soundness bound on a public
  leaderboard … raising the machine-checked soundness bound of koalaIRS12, a Reed–Solomon
  proximity problem … formalized end to end in ArkLib … A comparator checks that each
  submission's exported theorem exactly matches the pinned statement and the Lean kernel checks
  the proof."* Leaderboard [READ, better.codes, 2026-09-04]: *"The current interval is 68.02 to
  116.13 bits … Attack ↓ 116.13 bits, Soundness ↑ 68.02 bits, LITERATURE BASELINE 116.49 /
  64.00 bits … 70 promoted submissions, 22 solvers, current lower bound 68.02 bits"*; target
  128; progress *"1 − (Attack − Soundness)/(116.49 − 64.00)"* = 8.344 %.
  The instance: `proximityprize.org` [READ]: *"targets the toy protocol [ABF26, Construction
  6.9]"* — 2026/680 `:1903-1940`: one random linear combination `f₁ + γ·f₂`, soundness error
  **exactly** `ε_mca(C,δ) + |Λ(C^{≡2},δ)|/|F|` (Lemma 6.10; lower bound `≥ ε_ca(C,δ)`, Lemma
  6.13). 680 §6.3 parametrization [READ `:1635-1651`]: *"F is a sextic extension of B = F_q where
  q = 2³¹−2²⁴+1 (the Koala Bear prime); k = 2²⁰, s·n = 2²¹ so that ρ = 1/2; t = 128 … C :=
  IRS[F,L,k,s]"* with L smooth. [INFERRED] the "12" in `koalaIRS12` is a log-size the leaderboard
  page does not state; the challenge repo is not indexed (`gh search repos koalaIRS12` → ∅;
  `gh search code` → one newsletter). **What it is for us**: the first kernel-checked,
  adversarially-scored measurement of proven-vs-attack on a Prize instance: **~48 bits of gap at
  ρ = 1/2 over a ~2^186 field**, closing at ~0.01–0.4 bits per promoted proof. It corroborates
  "the regime lives in the type" — the leaderboard *is* a UDR-ish lower bound and a
  list-decoding-shaped upper bound reported as an interval, never one number. Pessimistic
  number: **68.02 proven.** Not a verdict change; a citation for VERDICTS §2's framing.
- **Proximity Prize** [READ, proximityprize.org 2026-09-04]: *"$0 in prizes"* awarded;
  *"Preliminary version … details may still change."*
- IoTeX 2026/858 Lean, zksecurity `simple-rbr-fri` (2025/1993 Thm 5.2 modulo `FRI_MCA_Hypothesis`),
  deltastar.computer — all pre-window, all in `formalization-frontier.md`; no new release found.

## 4. VERDICTS sentences at risk (for the operator; no edits made)

| section | sentence | status |
|---|---|---|
| §1b | *"BCSS25 states no FRI theorem and its Thm 4.3 plugs into a personal communication."* | **stale**: [Sta25] = eprint 2026/532 App. A.2 Thm 28/29 (public since Mar 2026); [Hab25] = 2025/2110. "No FRI theorem" remains true of 2055 itself; 532 Thm 19 is a circle-FRI theorem at Johnson with the 2025 bounds, and the classic-FRI paper [HHM25] is still unpublished. Suggested: *"…plugs into eprint 2026/532 App. A.2, a vendor whitepaper's appendix."* Same fix at `FriLedger.lean:270` (*"Neither is public"*). |
| §2 | *"Never quote 130."* | **unchanged, sharpened**: Plonky3 `p3-security` v0.7.0 ships the identical formula as `legacy_conjectured_error` (#2018, 2026-09-03), and its non-legacy conjectured reads 128.40 at IR-v2 [DERIVED]. |
| §2 | *"`pow` is additive and regime-free"* | **holds at three sources**; refinement: additive to the round it precedes; commit-PoW (ours = 0) is the additive lever on ε_C. |
| §2 | *"Four of five production systems refuse the capacity conjecture"* | unverified as to systems; the *library* Plonky3 keeps `CapacityBound` + DG25 random-words + legacy. |
| §7.0 | *"PR #1982 … STILL OPEN / CHANGES_REQUESTED (checked 08-14)"* | **stale**: merged 2026-08-17 (sibling lane owns). |
| §7.9 | *"Plonky3's p3-security says [d=5 KoalaBear] reaches 128"* | pre-#1978 number; conjectured columns dropped 128 → 119–125 at `compute_ldt_only` after 2026-08-13. |
| §1b | *"there is no `p3-security` crate"* | false since 2026-07-08; both the crate and `uni-stark/src/security.rs` exist. |

**UDR 34 / JBR 73: untouched by anything read.**

## 5. What I could NOT verify

- 2026/532 Thm 28's proof line by line (read the statement and the first paragraph of the proof
  only); and whether 2055's Thm 4.3 hypotheses match 532 Thm 28's exactly (the "|S| as large as
  in Theorem 4.2" vs 532's explicit threshold).
- Whether [HHM25] (non-circle multi-table FRI soundness) has appeared under another title.
- The exact koalaIRS12 parameters (log-size, δ, s) — the challenge repository is not public-indexed.
- Which *systems* (vs libraries) quote Plonky3's conjectured/legacy columns.
- The July 2026 revision of 2026/680 (our copies are v1); the "concrete estimate of attacks" it added.
- `hclivess/stark-soundness-analysis` (kagi hit; grey, unread).
- Semantic Scholar MCP failed to connect (timeout); no citation-graph cross-check was run.

## 6. Absence claims — corpus + instrument

1. No proximity-gap/CA/MCA/FRI/STIR/WHIR eprint since 2026-08-15: **eprint 2026 listing ids
   1661–1861 (two pages fetched 2026-09-04), title regex in §2 → ∅.** Titles only; abstracts of
   1839/1838 read; other abstracts not read.
2. No arXiv paper since Jul 22: **scry `academic.catalog` (coverage `built_at` ≤ 2026-08-27), title
   tokens `proximity gaps` / `correlated agreement`, abstract tokens `proximity gaps reed`, LIMIT 40
   → newest relevant 2607.10572 (2026-07-12).**
3. No soundcalc change: **`gh api repos/ethereum/soundcalc/commits?since=2026-08-15` → ∅;
   `pushed_at 2026-07-23`.**
4. No stwo change: **`gh api repos/starkware-libs/stwo/commits?sha=dev&since=2026-08-15` → 0.**
5. [HHM25] unpublished: **kagi q1/q4/q7 and eprint titles 1661–1861 → no "lifted FRI" /
   Haböck–?–? multi-table FRI paper; 532 `:2684` calls it "not yet published".**
6. Undigested-in-notes: **`grep -rli` over `notes/ docs/` for `2026/1432`, `2607.10572`,
   `2607.08516`, `chojecki`, `2026/1561`, `2025/870`, `2025/2054`, `Sta25`→532 link, `#1978`,
   `#2018`, `better.codes` → ∅** (each present in `~/paperbin` or on GitHub).
7. Proximity Prize awards: **proximityprize.org 2026-09-04: "$0 in prizes."**
