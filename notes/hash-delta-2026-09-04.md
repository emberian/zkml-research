# Hash delta, 2026-08-15 → 2026-09-04 — what moved in AO hash design/analysis, and whether it touches our verdicts

2026-09-04. LITERATURE lane. Question: what moved in arithmetization-oriented hash design and
cryptanalysis since ~2026-08-15, and does any of it change a hash verdict we hold?

Ground truth read before searching: `docs/VERDICTS.md` §1, §1b, §5f, §5g, §5h, §5k, §5l, §7;
`notes/gsr-poseidon-2026-1692.md` (full); `notes/poseidon2-audit-verdict.md`;
`notes/hash-landscape.md` (headline, §3, ADDENDUM 4); `notes/hash-verdict.md`;
`notes/decidable-by-design.md` §0, §1f, §5; `notes/weft-c-spec.md` §0–§2h;
`notes/ring-hash-attacks-2-3-4.md` (headers); `notes/formal-cryptanalysis-pipeline.md` §C3;
`SLVG_THOUGHT.md` §IV-f–§IV-k.

**The pinned deployed hash** `[OURS, gsr-poseidon-2026-1692.md §2a]`: Poseidon2, BabyBear,
`t=16, α=7, R_F=8, R_P=13`, 21 rounds, unanimous across nine transcriptions. Capacity 8 base
elements; the ~124-bit claim lives at CICO-8 `[OURS, VERDICTS §5h]`.

Labels: `[READ]` quoted from source at URL/page · `[DERIVED]` arithmetic from named inputs ·
`[INFERRED]` reconstruction · `[OURS]` measured/proved in our tree, cited by note.
Every absence claim carries corpus + instrument (§6).

---

## 0. VERDICT

> ⚠ 2026-09-04, later the same day: the named computation ran
> (`nst-1792-at-our-node.md`). VERDICTS §5h's sentence **holds for 1792 by
> ≥ 264 bits** on the Merkle node; the "six full rounds below 2^128" and the
> "R_P 13→20" readings below are withdrawn (see the note at §7.2). The
> compression-mode identification stands.

**No hash verdict moves on what has been read. Four new items are real; one of them names
a computation we have not run — and after the full read of 2026/1792 (§7.2) that computation
is the one thing standing between VERDICTS §5h's sponge sentence and a counter-instance on
the deployed Merkle node; one offers a candidate explanation for something VERDICTS calls
"unexplained".** 1760 and 1792 were read in full (§7); 1842 is abstract-only.

⚑ **The sharpest line, after the reads** `[DERIVED §7.2 from 1792 §4.1 + our source]`: on the
deployed Merkle internal node (`TruncatedPermutation<Perm16,2,8,16>`, `c=0, d=8`) 1792's
nonlinear subspace trail has length `2E_c = 2(t−d) = 16 > R_P = 13` — the whole internal
layer absorbed with three rounds to spare — and in their model every tabulated α=7 instance
crosses 2^128 only at the first partial round *beyond* the trail, i.e. **six full rounds alone
do not carry 2^128 there.** Our point (`r_F=8, p≈2^31, d=8`) is outside their tables; the
cost is uncomputed by anyone; §5h's `R_P 13 → 20` repair would put four partial rounds beyond
the trail, its `13 → 15` containment would not. **Run the ~100-line calculation (§7.2) before
the next VERDICTS edit.**

| # | item | what it is | touches | verdict moves? |
|---|---|---|---|---|
| 1 | **eprint 2026/1792** (Li–Liu–Wang, rec. 08-24, appr. 08-26) — *Beyond Linear Subspace Trails: Nonlinear Subspaces for Gröbner Basis Attacks on Poseidon/Poseidon2 and Neptune* | GB-attack line (GKR ToSC-2025 lineage), **not** GSR's interpolation line; nonlinear subspace trails cover up to `2·E_c` internal rounds vs `E_c` linear; "reaches or even exceeds the recommended number of internal rounds" on GKR25's instances | VERDICTS §5h ("R_P sits below its threshold"; the 3-round CEILING; "the instances GSR breaks are not the instances carrying our security claim") | **NOT YET — a computation is named** (§1.2). ⚑ **And the shape it needs is DEPLOYED**: our Merkle internal node is `TruncatedPermutation<Perm16,2,8,16>` = `Trunc₈(P(x))`, `c=0, d=8` `[OURS, read at source §1.2]`, where the linearizable window is `t−d = 8` partial rounds in GKR25's own linear model and up to 16 under 1792's claim — vs `R_P = 13`. The leaf sponge (`c=8`) has window 0. No cost at `p≈2³¹, α=7` is published by anyone; that is the computation. |
| 2 | **eprint 2026/1760** (S. Jo, rec. 08-21) — *Midpoint Reset: A Full-Round Poseidon Collision from an Adaptively Chosen MDS Matrix* | explicit **full-round (8+20) collision on the Initiative's KoalaBear Poseidon1 `(16,3,8,20)`** — with the MDS chosen **after** the round constants; submitted to the Initiative **31 July 2026** | hash-landscape §3 "AO graveyard" row for Poseidon ("no full-round break"); the "paused as of 2026-08-01, unexplained" line in hash-verdict.md and hash-landscape.md §3 | **No** for us (our matrices are fixed and constants-independent). **It is a rules result, not a Poseidon result** — but it is the first published full-round Poseidon collision *of any kind*, and the graveyard row should say so with the qualifier. Candidate explanation for the pause: `[INFERRED]` submission 07-31, pause 08-01. |
| 3 | **eprint 2026/1842** (Campa–Roy–Steiner–Trevisani, 09-01, ToSC 2026(3)) — *Arion: Arithmetization-Oriented Hashing for Zero-Knowledge Proof Systems* | the ToSC version of Arion; **"the first hash function whose security analysis is explicitly based on the algebraic invariant of the underlying ideal — the quotient ring dimension"**, i.e. a `D_I`-based security argument, for CICO-t at any t, both modes | decidable-by-design.md §1f/§5 (`D_I` as the decidable half; Perrin's "security arguments based on D_I are the future"); hash-landscape §3 graveyard row "Arion — BROKEN (2025/259)" | **No** verdict moves; **one framing line needs a neighbour**: decidable-by-design's "nobody has written it down" is about the *ledger*, and stays true, but a `D_I`-primary security analysis of a *shipped* AO hash now exists in print. Parameter sets pending the PDF (§2.2). |
| 4 | **eprint 2026/1653** (Samanta–Grenouilloux–Gong–Li, ~08-11) — *Lumora: permutation-based wide-block ciphers over `F_{2^n}`, n∈{16,32,64}* | an AES-like SPN over **GF(2³²)** (among others) with S-box `L(x⁻¹)+c`, MDS MixColumns, wide-trail ≥25 active S-boxes/4 rounds, FreeLunch/GB analysis; **10 rounds at n=32** | weft-c-spec.md (Twill: GF(2³²), `x⁻¹`, t=24, R=26 S-box layers) — the first published sibling on the same field with the same S-box | **No.** Different object (keyed cipher, 4×4 cells, target 2^{-16n} full-codebook). But it is the only in-window char-2 `x⁻¹`-SPN analysis, and its per-bit provisioning is 2.6× lighter than Twill's `[DERIVED]` §3.1 — a data point for Twill's leg 7 prior, not a refutation. |

Sibling lane `notes/eprint-delta-2026-09-04.md` triaged the same three eprints at abstract
level (its axis-2 rows) and marked each *"READ when landed"*; this note carries what that
triage cannot — the deployed-mode reading (§1.2), the derived windows, the Lumora comparison
(§3.1), the Initiative-rules reading of 1760 (§1.3), and the PDF reads in §7.

**Absences that hold** (instruments in §6): no Poseidon/Poseidon2 designer response, no
parameter change in Plonky3 (`p3-poseidon2` v0.7.0 = clippy only), HorizenLabs/poseidon2,
Stwo, plonky2, SP1, RISC Zero, OpenVM; no 3MI Labs follow-up yet (they say *"more results
are coming"*); nothing new on Vision Mark-32, Grøstl-in-Binius, Skyscraper, Monolith, Tip5;
no public post-mortem *analysis* of Poseidon's margin after the EF L1 decision — only trade
press and tweets.

---

## 1. Target 1 — GSR (eprint 2026/1692) follow-ups

### 1.1 Responses from the parties named in the brief — none found

| party | instrument | result |
|---|---|---|
| Poseidon/Poseidon2 authors (Grassi, Khovratovich, Rechberger, Schofnegger, Koschatko) | eprint-classic 2026 listing, ids 1692–1861, author regex `[READ]` | **∅** — no eprint by any of them in the window |
| HorizenLabs/poseidon2 (reference impl) | `gh api repos/HorizenLabs/poseidon2/commits?since=2026-06-01` and `issues?since=2026-08-01` | **∅ commits, ∅ issues** |
| Plonky3 | `gh api repos/Plonky3/Plonky3/commits?path=poseidon2&since=2026-08-15` → `c7271f10` (clippy) and `fb938268` (v0.7.0 release, 09-04). Release notes for `p3-poseidon2-v0.7.0` `[READ]`: *"Chore: fix latest stable clippy (#1994)"* — that is the whole list. `p3-poseidon1`, `p3-poseidon2-air`, `p3-koala-bear`: empty. Issues since 08-01 matching `oseidon|round|GSR|1692|partial`: only `p3-security`/STIR items (#1978, #1984, #1989, #2007), none about the hash. | **no round-count or constant change** |
| Polygon plonky2 / StarkWare stwo / Succinct SP1 / RISC Zero / OpenVM | `gh api search/commits q=repo:<r>+poseidon+committer-date:>2026-08-15` | **0 / 0 / 0 / 0 / 0** |
| Poseidon Cryptanalysis Initiative | `poseidon-initiative.info` (WebFetch 09-04, both `/` and `/home`) | **no entry after 08-01** (*"THE PROGRAM IS PAUSED STARTING 1 AUG 2026 AoE"*); no mention of 1692/GSR/3MI. Zero-test record still `RF=6, RP=12` (07-27); CICO `RF=6, RP=10` (07-06). |
| ethresear.ch | kagi ×2 (`ethresear.ch Poseidon 2026 S-box skipping…`); scry `forums.posts` title match since 08-13 | **∅ on-topic** (scry returned one 4chan thread about a streamer) |
| 3MI Labs (GSR authors) | LinkedIn post `[READ, WebFetch]`: *"the first (but not last) work product of this effort … grant number FY26-2457 … Stay tuned, more results are coming."* | **follow-up announced, none published.** ⚠ The "Top Gun: Degree Annihilation" item surfaced from `@TomerAshur`'s feed is **2026/1254 (Sanso–Vitto, June)** — already in our GSR lineage table (`gsr-poseidon-2026-1692.md` §3) — not a new 3MI paper. |
| citations of 2026/1692 | eprint abstract page shows Google-Scholar *"Cited by 1"* `[READ]`; mirror grep (first 3 pages, ids 1650–1730) for `2026/1692` → only 1692 itself; kagi `"2026/1692"` → the paper, IACR news, social posts, an EU biocide regulation with the same number | **resolved in §7.1: the citer is 2026/1760** (its ref. [3]); 1792 does not cite 1692 |

### 1.2 ⚑ The one real sibling: eprint 2026/1792 — nonlinear subspace trails for GB attacks

`[READ, abstract page https://eprint.iacr.org/2026/1792, received 2026-08-24, approved
2026-08-26; Enyan Li (ECNU), Fukang Liu (Institute of Science Tokyo), Gaoli Wang (ECNU)]`.
Verbatim, the load-bearing sentences:

> *"The main contribution of this paper is to extend the existing linear subspace trail
> framework to nonlinear subspaces. … we first introduce a parametric Macaulay matrix method.
> … for the CICO problem with `E_c` extra constraints, we give a concrete constraint pattern
> that extends a linear subspace trail into a nonlinear one. … the nonlinear subspace trail
> can cover up to `2E_c` internal rounds, whereas the previous linear subspace trail can cover
> up to `E_c` rounds. … For the Poseidon/Poseidon2 and Neptune instances proposed by Grassi et
> al. in ToSC 2025, our experiments show that, under the same complexity bound and the same
> Gröbner basis cost model, the nonlinear subspace model can analyze approximately twice as
> many internal partial rounds as the linear subspace model considered in ToSC 2025. For
> several concrete instances, our method reaches or even exceeds the recommended number of
> internal rounds given by the designers in sponge mode or compression mode."*

**Which lineage this is, and why it is not "GSR again".** GSR (`gsr-poseidon-2026-1692.md`
§1b) fixes the single active S-box input to an arbitrary constant `δ` and *interpolates*
(Sylvester resultant + Cantor–Zassenhaus); its reach is `t − 2k` partial rounds *by
degree-of-freedom counting*, independent of solver. 1792 is the **GKR ToSC-2025 line**
(`Grassi–Koschatko–Rechberger, eprint 2025/954`) — restrict the state to a subspace so that
partial rounds stay *linear in the Gröbner model*, then pay a GB cost. GKR25's linear trail has
length `ℓ = t − (c + d)` in sponge mode, `t − d` in compression mode `[READ, 2025/954 eq. 27
and §7.1: "ℓ = t − (c + d) = r − d", "all results … hold for the compression mode by setting
c = 0"]`. 1792 claims to double it.

**Which modes we actually deploy — read at source, and it corrects a note.** `[OURS]`
`breadstuffs/circuit/src/plonky3_prover.rs:71-72`, `stark_zk.rs:79-80`,
`circuit-prove/src/gpu_backend.rs:2987-2989`:

```rust
type TestHash     = PaddingFreeSponge<Perm16, 16, 8, 8>;      // leaves: WIDTH 16, RATE 8, OUT 8  → c = 8
type TestCompress = TruncatedPermutation<Perm16, 2, 8, 16>;   // internal nodes: 2×8 → 8        → c = 0, d = 8
```

and the pinned `p3-symmetric` (`~/.cargo/git/checkouts/plonky3-7d8a3b21a665a86f/82cfad7/symmetric/src/compression.rs`):
`compress` is `self.inner_permutation.permute(pre)` then `post[..CHUNK]` — **`Trunc₈(P(x))`
with no feed-forward.** minidregg agrees: `Selvage/HashFamily.lean:6` — *"the Merkle role —
an ordered 2-to-1 compression"*. ⚠ **So `hash-verdict.md` item 6 — *"our Merkle tree is
sponge-mode … Compression-mode literature findings do not reach us"* — is true of the
leaves and false of every internal node.** VERDICTS §1/§5h do not state a mode, so nothing
in VERDICTS is contradicted; the note line should be corrected to *"leaves sponge (rate 8),
internal nodes 2-to-1 truncated permutation"*. `poseidon2-audit-verdict.md`'s table already
has the right shape (its "Merkle compress" row).

**What 1792 means at OUR parameters, derived from the abstract plus GKR25** `[DERIVED]` —
the paper's `E_c` is read here as GKR25's `t − (c + d)` analogue; **that identification is
unverified until the PDF is read** and is the single thing to check first:

| deployed object | `c` | `d` (output constraints) | GKR25 linear window `t−(c+d)` `[READ, 2025/954 eq. 27, §7.1]` | 1792's stated window `2E_c` | vs `R_P = 13` |
|---|---|---|---|---|---|
| **leaf sponge** `PaddingFreeSponge<16,8,8>` | 8 | 8 (`⌈248/31⌉`, GKR25's own `c = d = ⌈log_p 2^{2κ}⌉` rule) | **0** | **0** | *nothing to linearize* — same shape as "GSR identically vacuous at k=8" |
| **Merkle node** `TruncatedPermutation<2,8,16>` | **0** | 8 | **8** — GKR25 `[READ, §5.1]`: *"In compression mode, we get t − (c + d) ≤ t − 1 by artificially setting c = 0"* | **up to 16** | **≥ 13 — would absorb the whole internal layer, and 3 rounds to spare** |

> ⚑ So the abstract's headline reproduces, at our width, exactly the §5h structural fact —
> `R_P = 13` fits inside the attacker's linearizable window — **but through the Gröbner
> route, on the deployed Merkle node, where GSR's symmetric DoF count gave `t − 2k = 0` at
> k=8 and stopped.** VERDICTS §5h *"the instances GSR breaks are not the instances that
> carry our security claim"* was stated for GSR's k=1,2 on the sponge; **the Merkle node is
> a different instance, GKR25's linear model already linearizes 8 of its 13 partial rounds,
> and 1792 is the paper that claims to double that.** ⚠ Two things keep this from being a
> finding rather than a question: (a) what remains after linearization is **all 8 full rounds
> at α=7** (GKR25's model has no free-first-round trick for Poseidon2 — *"all results can be
> extended to Poseidon by using r_f − 1, since the first full round of Poseidon can be skipped
> for free"* `[READ, §7]` — the converse being that Poseidon2 keeps it), and every published
> α=7 number we hold says that residual is enormous (GSR's CICO-1 with only *three* full
> rounds unreached cost 2^27 with *one* variable; here there are eight and up to sixteen
> variables); (b) GKR25's cost model is stated for `p ≥ 2^64` and its Figure 5 never visits a
> 31-bit prime, where *"the maximum degree could be achieved"* `[READ, §5.1]`. **No one has
> published a cost at `(p ≈ 2³¹, t=16, α=7, c=0, d=8, R_P=13)`.**

**What it would cost us to re-derive.** Not runnable from the abstract. When the PDF lands:
(i) confirm what `E_c` is and whether the `2E_c` construction survives `p ≈ 2³¹` (GKR25 §5.1
`[READ]`: *"recent versions of Poseidon (including Poseidon2) have been introduced for much
smaller values of p … In these cases, the maximum degree could be achieved … adding more
rounds does not (necessarily) increase the degree"* — so the small-prime saturation regime is
where our instance lives and where GKR's own Figure 5, at `p ∈ {2^64, 2^96, 2^128, 2^256}`,
never looked); (ii) plug `t=16, α=7, c∈{0,8}, d=8, R_F=8, R_P=13` into their cost formula and
GKR25's eq. (7.1) with `ω=2`, and compare to the 2^124 bar. That is a ~60-line extension of
`notes/gsr-scripts/gsr_calc.py`'s shape (which reproduced GSR's Table 1 5/5 before being
pointed at us — the same guard applies: reproduce 1792's table first). ⚠ **Not done in this
lane; the PDF was still syncing.** Filed as the one computation this delta names.

**Sentence at risk, exactly:** VERDICTS §5h — *"the sponge's ~124-bit claim — which lives at
CICO-k for k at the capacity, where GSR gives nothing (no gain by k=3; identically vacuous at
k=8)."* True for GSR; **1792's compression-mode room at d=8 is not zero.** If our tree only
ever runs the permutation in sponge mode, the sentence needs "(and the compression mode is
not deployed)" appended and nothing else changes; if any 2-to-1 compression use exists, the
`R_P 13 → 20` repair priced in §5h (+5.0%) is the same repair this line would ask for.

### 1.3 eprint 2026/1760 — Midpoint Reset, and the Initiative's pause

`[READ, abstract page https://eprint.iacr.org/2026/1760; received 2026-08-21, approved
08-22; Sunghyeon Jo, Georgia Tech / QED Audit]`: *"an explicit compression collision for all
28 rounds of the KoalaBear Poseidon instance"* with `(t, α, R_F, R_P) = (16, 3, 8, 20)`, *"in
the setting where the round constants are fixed before the MDS linear layer is chosen"*;
*"the result exposes an adaptive correlation between fixed round constants and a subsequently
chosen linear layer that matrix-only checks do not capture"*; submitted to the Initiative
*"on 31 July 2026"*. Reproduction repo `ainta/poseidon1-collision-verifier` `[READ, README
via gh api]`: verification pinned to `khovratovich/poseidon-tools@60075da7`, *"contains no
alternative Poseidon implementation"*; both 15-element inputs give the same full 16-coordinate
output; and — the sentence that matters for the rules — *"The official `verify_mds_matrix`
routine checks Poseidon-specific subspace criteria, but not the classical MDS requirement that
every square minor be nonzero"*, so the repo checks all 601,080,389 minors independently and
reports `ALL_NONEMPTY_SQUARE_MINORS_NONZERO`.

**The rule it exploits is the challenge's own.** `[READ, poseidon-initiative.info/home]`:
*"the MDS matrix is arbitrary but satisfying 'no-invariant-subspace-trail' conditions"* (the
Plonky3 circulant given as an example). So the solver may pick `M` after seeing the constants.
This is a **specification result about the bounty**, not a cryptanalytic result about Poseidon
with a fixed public matrix: our `M_E`, `M_I` are pinned upstream of any constants
`[OURS, gsr-poseidon-2026-1692.md §2a]` and no adaptive choice exists. **Nothing in our tree is
touched.**

Two things it does change in how we write:
- `hash-landscape.md` §3's graveyard row *"Poseidon / Poseidon2 — no full-round break"* is
  now true only with the qualifier *"for a fixed, constants-independent matrix"*. A full-round
  Poseidon collision exists in print; it is a rules artefact. Say both.
- `[INFERRED]` The pause. `hash-verdict.md` and `hash-landscape.md` §3 record *"paused as of
  2026-08-01, unexplained."* 1760 was *"submitted … on 31 July 2026"*; the pause is dated
  *"1 AUG 2026 AoE"*. Adjacent dates, and a rules-valid full-round collision is exactly the
  kind of submission that pauses a prize while the rules are rewritten. **This is a
  correlation read off two dates, not a statement by the Initiative** — the Initiative page
  says nothing, and no kagi hit connects them. Recorded as the leading candidate, not as fact.
- It is a fourth instance of the pattern hash-landscape §3 already names — *"the recurring
  wound is the LINEAR LAYER"* — with a new axis: **constants-then-matrix ordering**. Our gate
  (`weft-c-spec.md` structure/quotient/subfield/minpoly-first) does not have an item for
  "who fixes what first"; it should, at zero cost, for any primitive we author.

### 1.4 What 2026/306 and GSR together already gave — unchanged

`poseidon2-audit-verdict.md` (+286 bits vs 2026/306), `gsr-poseidon-2026-1692.md` (3-round
ceiling, CICO-1 practical on 18/21, sponge claim untouched), `gsr-cheaplunch-composability.md`
(skip reaches, does not compose): **no source in the window contradicts any of them.** The
CheapLunch `M_E` skip at `t=16, k=1` remains an open problem in print with no new taker.

---

## 2. Target 2 — Gröbner / FreeLunch / Resolution line since Aug 15

### 2.1 Corpus

eprint ids 1692–1861 (classic listing, 260 entries in 1600–1899 range; title regex over the
AO/GB vocabulary) → in-window AO-relevant: **1760, 1792, 1842**; adjacent but not AO: 1838
(Fenzi, FS on generated R1CS — no hash named `[READ, abstract]`), 1843 (APEX — ARX/Long-Trail,
not AO `[READ, abstract]`), 1848 (Beyne et al., quasidifferential WKR — block ciphers). kagi
`eprint 2026 Gröbner basis attack Griffin Anemoi Arion Rescue-Prime ideal degree new results`
→ only pre-window items (2024/347, 2025/259, 2025/814, 2024/250) plus the Arion news item.
**No new attack on Griffin, Anemoi, Arion, Rescue-Prime, XHash in the window.** The last
moves in that line are the ones `hash-landscape.md` §3 already carries (2025/259, 2026/1281,
CheapLunch 2025/2040).

### 2.2 ⚑ eprint 2026/1842 — Arion, ToSC 2026(3): a `D_I`-based security argument, in print

`[READ, abstract page + IACR news item 29448, 2026-09-01]`. Authors Campa, Roy (Innsbruck),
Steiner (independent), Trevisani (TU Wien). Verbatim:

> *"To the best of our knowledge, Arion is the first hash function whose security analysis is
> explicitly based on the algebraic invariant of the underlying ideal — the quotient ring
> dimension. In particular, we explicitly determine the dimension of the quotient ring
> associated with the CICO problem induced by the hashing modes. Furthermore, our analysis of
> the CICO-t problem applies to any t ≥ 1 and covers both the Sponge and feed-forward
> constructions."*

and the efficiency claim: *"Arion is frequently the best-performing design in the Plonk
setting and remains highly competitive, often ranking second, in both R1CS and AIR. … Arion is
the only construction based on high-degree power maps that achieves performance comparable to
Poseidon/Poseidon2."* Parameter sets: *"prime fields commonly used in zero-knowledge proof
applications, including the scalar fields of the BLS12-381 and BN254"* — **no 31-bit prime is
named in the abstract.**

**Relationship to what we hold.**
- `decidable-by-design.md` §1f `[OURS]`: the decidable half of the Gröbner leg is `D_I` = the
  quotient-ring dimension; the argued half is the exponent `ω′` and the min-over-models; Perrin's
  slide *"security arguments based on D_I are the future!"* `[READ there]`. **1842 is that
  future, shipped**: a designer choosing `D_I` as the stated basis of the security claim. It
  does not close the argued half — a `D_I` for *their* model is a per-model upper bound, and the
  same note's §5 point 3 (*"a design can make its best-known model's D_I exceed the bar; it
  cannot certify no better model exists"*) applies to Arion verbatim. ⚠ And 2025/259 §5
  `[READ there]` computed Griffin's/Arion's ideal degree in closed form *and still broke them*
  because the exponent moved — so "security based on `D_I`" is exactly as strong as `ω′`, which
  1842's abstract does not state. **Read the PDF for the exponent they assume before quoting
  any number.**
- `decidable-by-design.md` §5's *"unwritten"* claim is about the **decidability ledger** (5 of
  7 classes decided, the two argued ones with structural causes). 1842 does not write that
  ledger; it writes one leg's analysis `D_I`-first. The claim stands, and 1842 becomes the
  nearest published neighbour to cite next to it.
- `hash-landscape.md` §3 graveyard: *"Arion — 2025/259: 2^53–2^57, 'almost all parameter
  variants' — BROKEN."* 1842 is by the original Arion authors plus Campa; whether it re-parameterizes
  or re-argues is **not decidable from the abstract**. Until read: the row stays, with
  *"ToSC 2026 version 2026/1842 pending read"* appended. arXiv 2303.04639 (the 2023 Arion)
  last updated 2023-05-28 `[READ, arXiv API]` — 1842 is a new manuscript, not a revision push.

**Cost to re-derive**: nothing to run until the PDF is read; then `dbd_ideal_degree.py`
(`notes/decidable-scripts/`) is the shape for checking their `D_I` on a toy instance.

### 2.3 Not new, but unread in paperbin: eprint 2026/1271 (June)

`~/paperbin/ao-hash-boosting-2026-1271.pdf` — Andreeva, Bhattacharyya, Roy, Trevisani, USENIX
Security 2026, *"Boosting Efficiency and Security in AO Hashing"* — **0 mentions in
notes/ docs/ forcodex/** (`grep -rn 1271`). `[READ, p.1]`: PA/PAX permutation-based compression
modes with *"optimal collision and preimage resistance"* (vs sponge), PAX indifferentiable;
*"unifies … Jive and Trunc, as used in … Anemoi and POSEIDON2"*; up to 2× native and up to 60%
in Plonky2 over sponge at 128-bit collision. Pre-window (June) — **not a delta** — but it is the
mode-level result the CR/RO-split lane (VERDICTS §5j, "the live knob is leaf RATE") would want
to have read, and `hash-verdict.md` item 6 (*"mode is free … Compression-mode literature
findings do not reach us"*) is exactly the sentence it bears on. Flagged for that lane; not
pursued here.

---

## 3. Target 3 — Binary-field / char-2 hashes

### 3.1 The only in-window char-2 item: Lumora (eprint 2026/1653)

`[READ, mirror PDF, full text]`. Samanta, Grenouilloux, Gong, Li (Waterloo / Bergen).
*"a family of arithmetization-oriented, permutation-based wide-block ciphers … Each instance
of Lumora follows a unified AES-like SPN structure defined over the binary extension field
F_{2^n} for n ∈ {16, 32, 64}"*, keyed by single-key Even–Mansour, for R1CS / FAEST-EM
signatures. Not a hash. But its **permutation** is the object Twill's legs are about:

| | Lumora(512,32) `[READ]` | Twill `[OURS, weft-c-spec.md §1, §5a]` | Mark-32 `[READ 2024/633 via weft-c-spec §0.3]` |
|---|---|---|---|
| field | GF(2³²), `x³²+x²²+x²+x+1` | GF(2³²) Fan–Paar tower | GF(2³²) tower |
| S-box | `S(x) = L(x⁻¹) + a_n`, `L` a linearized permutation; *"algebraic degree n−1"*, DP `2^{-n+2}`, LC `2^{-7}` at n=16 (Nyberg) | lane-wise `x⁻¹` + `B`/`B⁻¹` linearized layer | `x⁻¹` + `B`/`B⁻¹` |
| state | 16 cells (4×4), 512 bits | 24 lanes, 768 bits | 24 lanes, 768 bits |
| linear layer | MDS MixColumns + ShiftRows (`s_j ← s_{13j mod 16}`), *"full diffusion within two rounds"* | `cosetPack`, branch 8 exact | systematic-RS MDS, branch 25 |
| statistical bound | *"at least 25 active Sboxes over any four rounds"* → 4-round trail `≤ 2^{-25(n-2)} = 2^{-750}` vs target `2^{-16n} = 2^{-512}` | 4-step minimum active ≥ 17 (generic 16) | — |
| algebraic | GB of the 16-variable model *"directly forms a Gröbner basis"*, FreeLunch-shaped with degree `q−2`; cost `(2^n−2)^{ω(16R_n−1)+1}` *"exceeds the target threshold 2^{16n} when R_n ≥ 3"*; integral reaches 4 rounds at `O(2^{5n+2})` | leg 7 asserted 6 → corrected 13 steps | Table 1: 3 rounds asserted |
| rounds shipped | **10** (n=32); 12 (n=16); 8 (n=64) — *"we therefore use four rounds as a conservative lower bound for the security analysis"* | 26 S-box layers (13 Vision rounds) | 8 Vision rounds = 16 layers |
| inversions per state-bit `[DERIVED]` | `16·10/512 = 0.3125` | `24·26/768 = 0.8125` | `384/768 = 0.5` |

**What this is and is not for Twill.** It is the first published analysis of an `x⁻¹`-SPN on
GF(2³²) besides Mark-32 — same field, same S-box family, an MDS layer, a wide-trail count and
a FreeLunch/GB estimate in one document. It provisions **2.5× the attacked reach** (4 → 10)
and lands **2.6× lighter per bit than Twill and 1.6× lighter than Mark-32** `[DERIVED above]`.
It is **not** a refutation of Twill's `R=26`: Twill's binding leg is a *hash* CICO with an
outward-corrected prior (`weft-c-spec.md` §2e), while Lumora's target is a keyed permutation
against the full-codebook bound `2^{-16n}` and its GB argument stops at *"R_n ≥ 3 suffices"*
without the exponent question `decidable-by-design.md` §1f raises. ⚠ Their FreeLunch claim is
a *designer's* per-model statement, which the same note says can block but never bless. **A
data point for the ×2.1 prior, not a bound.** No action; recorded for the day the char-2 slot
exists.

⚠ Lumora cites Vision and Mark-32 lineage `[READ, §"Comparison with Related Work"]` but
**does not analyze Mark-32's MDS, its round count, or the Marvellous minimum-10 floor**;
`[M32-flag]`/`[M32-floor]` have no outside witness in the window.

### 3.2 Vision Mark-32, Grøstl-in-Binius, Poseidon2b — nothing new

- kagi `"Vision Mark-32" cryptanalysis binary tower hash attack rounds` (42 results) → the
  paper, the Irreducible FPGA post, cryptography.academy summaries, dblp. **No third-party
  analysis.** The standing line *"none found, and nobody has looked"* `[OURS, VERDICTS §5f]`
  holds.
- kagi `binary field hash Binius Grøstl "binary tower" new design 2026` → Binius-era items only
  (2023/1784, Springer chapter, Rechberger's SPRING-2026 survey slides). **∅ new.**
- kagi `Poseidon2b … cryptanalysis 2026` → 2025/1893 (the design) and 2026/306 (Feb). **∅
  new since Aug.**
- **Adjacent, systems-side, one line only** (the systems lane owns it): Plonky3 v0.7.0 merged
  *"characteristic-agnostic groundwork for binary fields (#2000)"* and *"additive NTT and the
  Encoder abstraction (#2003)"* `[READ, PR bodies via gh api]` — *"Phase 0/Phase 2 of a staged
  plan to add characteristic-2 (binary tower) field support to Plonky3"*, Cantor basis of the
  tower included. **No binary-field hash AIR is in either PR.** Relevant to VERDICTS §5f/§IV-h
  *"the char-2 hash slot does not exist"* only as a trend: the substrate the slot would need is
  being built upstream, and the hash it would run is not.

---

## 4. Target 4 — New AO hash proposals and attacks since Aug 15

| design | in-window source | status |
|---|---|---|
| **Arion (ToSC)** | 2026/1842 (§2.2) | new manuscript by the designers; `D_I`-first analysis; parameters pending read |
| **Lumora** | 2026/1653 (§3.1) | new char-2 AO *cipher* family; Waterloo/Bergen |
| Skyscraper (v1/v2), Monolith, Tip5 | kagi `Skyscraper OR Monolith OR Tip5 hash cryptanalysis attack eprint 2026 …` (51 results, mostly noise: a Netflix special, Jeddah Tower) → only ToSC items already in hash-landscape §3 (2025/102 Bak, the Tip5/Monolith collision paper) | **∅ new** |
| Poseidon-π / Rescue-XLIX / Kintsugi / "lookup-based" | 0 in-window titles; `Poseidon-π` appears only inside 2026/1271's benchmark `[READ]` | **∅ new** |
| Anemoi/Griffin/Rescue variants | §2.1 | **∅ new** |
| APEX (2026/1843) | abstract `[READ]`: ARX, Long Trail Strategy, large-state S-boxes | **not AO** — excluded |

**One graveyard-table edit is warranted** (hash-landscape §3): the Poseidon row gains
*"full-round collision with attacker-chosen MDS: 2026/1760 (rules artefact)"*; the Arion row
gains *"ToSC 2026 version 2026/1842 pending read"*.

---

## 5. Target 5 — EF L1 decision aftermath: new *analysis* of Poseidon's margin?

**None found that is analysis rather than announcement.**

- kagi `Poseidon security margin post-mortem analysis after Ethereum abandons Poseidon
  "hash-friendly SNARKs" …` (5 results) → postquantum.com, incrypted, cryptoslate, crypto.news,
  ainvest (*"Poseidon Wasn't Broken. It Was Outcompeted"*) — **all trade press re-quoting the
  same Drake post** `[READ, snippets]`; no numbers not already in `hash-landscape.md` §3.
- kagi `Khovratovich OR "Poseidon initiative" retrospective OR "lessons learned" …` → the
  SPRING-2026 deck we already hold (`~/paperbin/grey-poseidon-initiative-state-of-art-2026.txt`),
  `khovratovich/poseidon-tools`, a ZK podcast episode (leanSig). **No retrospective document.**
- scry `hackernews.items` since 08-13 with `poseidon` in `search_text_lc` → 2 rows: an empty
  item and *"Why Ethereum Walked Away from Poseidon"* → a ProjectZKM **tweet** (not fetched;
  a tweet is a tweet).
- The Initiative page has not been edited since the pause `[READ, §1.1]`; the deck's claimed
  *"$90,000 award fund for published attack papers"* (postquantum.com snippet) has no
  published outcome in the window.
- **The one analysis-adjacent fact is 1760 (§1.3)**: a rules-valid full-round collision
  submitted the day before the pause. If a post-mortem ever appears, that is where it starts.
- `demirelo/poseidon` (*"Concrete-Complexity Cryptanalysis of the 2026 Poseidon1/KoalaBear
  Challenge Suite"*, last push 2026-06-17 `[READ, README]`) — pre-window, reduced-round
  witnesses only (`RF=4/RP=5`), explicitly *"does not claim a funded full-round RF=6 bounty
  solve"*. Not a delta; noted because its README independently states the Initiative's
  admissible-MDS rule (*"The challenge admits any MDS matrix satisfying the
  no-invariant-subspace-trail conditions"*), the rule 1760 walked through.

The audit-verdict residual `[OURS, poseidon2-audit-verdict.md]` — *"Poseidon's Fiat–Shamir …
security … 'largely unexplored'"* — got one adjacent paper: Fenzi 2026/1838 (FS on generated
R1CS; Spartan/Aurora variants; mitigation = derive the first challenge from the generated
statement). `[READ, abstract]` names no hash function; it is the KRS25 class, which
`hash-verdict.md` item 2 already places outside our GKR-free stack. Systems/soundness lane's.

---

## 6. Corpus + instrument ledger

| absence claim | corpus | instrument |
|---|---|---|
| no designer/industry response to 2026/1692 | eprint 2026 ids 1692–1861 (classic listing, 260 entries); GitHub Plonky3, HorizenLabs/poseidon2, stwo, plonky2, sp1, risc0, openvm; poseidon-initiative.info; ethresear.ch via kagi + scry forums.posts | author-name regex over titles/authors; `gh api … commits?path=poseidon2&since=2026-08-15`, `issues?since=2026-08-01`, `search/commits q=repo:X+poseidon+committer-date:>2026-08-15`; WebFetch ×2; kagi ×3 |
| no eprint cites 2026/1692 except (probably) 1792 | mirror ids 1650–1730 (first 3 pages, pdftotext); classic listing titles | `grep -c '2026/1692'` over `mirror-txt/*.txt` (first 3 pages for 1650–1730, full text for 1731–1792); **1760 cites it, nothing else does**; ⚠ ids 1793–1861 not on the mirror at close (§7.4) |
| no new Griffin/Anemoi/Arion/Rescue/XHash attack | eprint 1692–1861 titles; kagi | title regex; kagi `eprint 2026 Gröbner basis attack Griffin Anemoi Arion Rescue-Prime ideal degree new results` |
| no new Vision Mark-32 / Grøstl / Poseidon2b analysis | kagi ×3; eprint titles | queries quoted in §3.2 |
| no new Skyscraper/Monolith/Tip5 attack | kagi; eprint titles | query quoted in §4 |
| no arXiv AO-hash paper since 08-10 | scry `academic.catalog` | `hasToken(lower(abstract),'poseidon') OR hasAllTokens(lower(abstract),['arithmetization','oriented']) OR (hash ∧ cryptanalysis ∧ field)`, `published_at ≥ 2026-08-10` → 0 rows; ⚠ **coverage extent `built_at` 2026-08-13…08-27** — absence is meaningful only inside that window |
| no Poseidon post-mortem analysis | kagi ×2; scry hackernews.items (fresh to 09-04) | queries quoted in §5 |
| no 3MI follow-up published | eprint titles/authors 1692–1861; kagi `"3MI Labs" OR "Tomer Ashur" Poseidon second paper …` | the only hit was a repost of 2026/1254 |

⚠ **An instrument that does NOT work for this window**: the STAP Zoo (`stap-zoo.com`, cited
by Lumora as tracking *"subsequent security developments"*) — its news stops at **June 2024**
and its Poseidon/Poseidon2 cryptanalysis list ends at ACISP 2024 `[READ, WebFetch 09-04]`;
Vision Mark-32, Monolith, Tip5 carry *"no cryptanalysis references"*. Stale; not evidence of
absence for anything in 2026.

Kagi budget used: 19 of 25. Scry: 5 queries (2 malformed-column retries). eprint abstract
pages fetched: 1792, 1760, 1842, 1838 (4 of ≤ 40, spaced). **No PDF was downloaded from
eprint.iacr.org**; all full texts came from the local mirror or paperbin.

---

## 7. PDF reads — 1760 and 1792 (mirror); 1842 abstract-only

Session note: the lane was killed by a session limit and resumed; §0–§6 above are as written
before the PDFs landed and are not re-derived here. 1760 landed 19:33, 1792 landed 20:01;
**1842 had not landed** (the sync hit the archive throttle at 20:27, per the coordinator) and
is carried at abstract level only (§2.2). Full texts: `pdftotext` of the mirror PDFs into the
session scratchpad (`p1760.txt`, 638 lines; `p1792.txt` with `-layout`, 2,408 lines).

### 7.1 eprint 2026/1760 — read in full

**Mechanism, in the paper's words** `[READ, abstract + §1]`: two executions tracked as midpoint
`m_r` and half-difference `d_r`; *"In each two-round block, one prescribed image of the linear
layer cancels the midpoint against the next round constant, so the following odd cubic S-box
receives opposite states and resets the midpoint to zero. Two additional images are reused
throughout the permutation to return the half-difference to the same one-dimensional
subspace."* The prescribed images `M·u_r = −c^{(r+1)}` determine `M`; *"For the concrete
28-round instance, the resulting source vectors are linearly independent. Hence the prescribed
images determine a unique linear layer."* Image budget `L + 2 ≤ t`, with `L = 14, t = 16` —
*"the direct construction uses a basis of the state space."*

**Scope — this is a rules result, confirmed at source** `[READ, §1, §6]`: *"The Poseidon
Cryptanalysis Initiative considers … a collision challenge in which the round constants are
fixed while the attacker may provide an MDS matrix satisfying the prescribed linear-layer
checks. The stated rules did not explicitly prohibit choosing the matrix as a function of
those constants."* And the general point: *"MDS tests constrain diffusion through the minors
of M, while the subspace-trail tests of [8] constrain persistent subspace behavior of M and
its powers. Neither class of test constrains these joint matrix–constant relations. The
attack therefore identifies the parameter-selection order as an additional part of the
security analysis."* Its proposed fix: *"derive the complete parameter set non-adaptively,
for example from a common seed or by binding the round constants to a canonical encoding of
the matrix."* **Nothing here applies to a matrix fixed independently of the constants** —
i.e. to every deployed instance we hold. The matrix passes `verify_mds_matrix(M,p)=True` at
the pinned `poseidon-tools` commit and all square minors are nonzero (two exact
implementations, Dodgson condensation and Laplace) `[READ, §5]`.

**Timeline and the pause** `[READ, §6 "Relation to recent attacks", Acknowledgments]`: *"The
collision reported here was submitted to the Poseidon Cryptanalysis Initiative on 31 July
2026, before the public appearance of Slipway [10] and the attack of Bhati, Tariq, and Ashur
[3]. The works were developed independently."* and *"We thank the Ethereum Foundation Poseidon
Group … for reviewing the submitted collision."* So the Initiative **received and reviewed** a
rules-valid full-round collision on 31 July; the Collision Prize was paused **1 August AoE**
`[READ, poseidon-initiative.info]`. The paper does not connect the two and the Initiative has
published nothing. `[INFERRED]` stays as written in §1.3: the leading candidate explanation
for the "unexplained" pause, not a fact.

**It is the citer of 2026/1692.** Reference [3] is GSR; the paper positions itself as
*"complementary … [GSR] keeps the linear layer fixed and restricts selected partial-round
S-box inputs … Midpoint reset uses the opposite degree of freedom."* That resolves §1.1's
*"Cited by 1"*: **1760, not 1792** (1792's bibliography has Ashur–Buschman–Mahzoun ACISP'24 but
not 1692 — `grep 1692 p1792.txt → ∅`).

**Bearing**: none on any deployed verdict; two writing edits (hash-landscape §3 graveyard
qualifier; the pause line) as in §1.3; one zero-cost gate item — *fix the selection order
(constants before matrix, or both from one seed) and say so* — for any primitive we author.

### 7.2 ⚑ eprint 2026/1792 — read in full, and the identification in §1.2 is confirmed at source

> ⚠ **Corrected 2026-09-04 by the computation this section asked for**
> (`nst-1792-at-our-node.md`, `gsr-scripts/nst_1792.py`, Table C.1 58/58 and C.2
> 21/21 reproduced). Two readings below are wrong and are kept as written:
> (i) Table C.1's entries `2E_c+1` are the model's *trail floor*, at which the cost
> is already ≥ 2^128 in 55/58 cells (≥ 2^164.9 for every t ≥ 8) — "six full rounds
> alone sit below 2^128" does not follow; (ii) "t=10, p≈2^64: E_c=2 → 9" is a
> column misalignment (row a's first entry is under t=12). At our node the cheapest
> model is 2^511.9 at ω=2, R_P=20 changes nothing at the floor, and the
> "independent argument for R_P 13→20" does not survive. The structural
> identification (trail covers all 13 partial rounds) stands.

**`E_c` is exactly what §1.2 assumed** `[READ, §4.1 p.24]`: *"we take `min{c, d} = d` without
loss of generality. Then `E_c = r − min{c, d} = r − d = t − (c + d)`. In compression mode, one
has `E_c = t − min{c, d} = t − d`."* And the construction `[READ, §1 contribution 2]`: *"our
construction extends a linear subspace trail of length about `⌊E_c/s⌋` to a nonlinear subspace
trail of length `2⌊E_c/s⌋`. … In particular, when `s = 1`, the length is extended from `E_c` to
`2E_c`."* Poseidon2 has `s = 1`.

**At our deployed objects** `[DERIVED from the two quotes + §1.2's source reads]`:

| object | `E_c` | nonlinear trail `2E_c` | `R_P = 13` | consequence in 1792's model |
|---|---|---|---|---|
| leaf sponge `PaddingFreeSponge<16,8,8>` (`c = d = 8`) | `16 − 16 = 0` | 0 | — | nothing linearized; unchanged |
| **Merkle node `TruncatedPermutation<2,8,16>` (`c = 0, d = 8`)** | **`16 − 8 = 8`** | **16** | **13 < 16** | **the entire internal layer is absorbed, with 3 rounds of trail to spare** |

**What their tables say about "all partial rounds absorbed"** `[READ, Tables C.1, C.2; §4.2]`.
Their round number is *"the minimum number of internal partial rounds required for the
corresponding algebraic solving complexity to reach or exceed 2^128"*, at fixed `r_F = 6`, no
margin, cost model `C_GB(d_MAC, ω=2)` / `C_FGLM(d_I, ω=3)`. Every α=7 entry is **`2E_c + 1`**:
sponge `t=24, c=d=1`: `E_c=22 → 45/45`; `t=4`: `E_c=2 → 5/5`; compression `t=22, d=1`:
`E_c=21 → 43`; `t=24, d=1`: `E_c=23 → 47` (Table C.2, *"exceeds the recommendation with the
security margin"* — designers' 43, with margin 47). ⚑ **Read what `2E_c + 1` means: in their
model the trail is free, and six full rounds at α=7 plus ZERO un-absorbed partial rounds sit
BELOW 2^128 — the 2^128 line is crossed by the first partial round the trail cannot reach.**
(The α=3 rows need more: `t=10, p≈2^64`: `E_c=2 → 9`.) So on the deployed Merkle node, in
1792's model, **security rests on the 8 full rounds alone**, which is exactly the shape §5h
already recorded for GSR — *"our safety on that half now rests entirely on the §4b
obstruction"* — now arriving by the Gröbner route with no DoF obstruction at all.

**What is NOT decided, stated exactly.** Their tables never visit our point: `r_F = 8` (not
6), `p ≈ 2^31` (their smallest is `2^64`; at `p−2` saturation they *"estimate their degree as
p − 2"* `[READ, p.24]` — a cap that helps the attacker), and `d = 8` with `c = 0` (their
compression rows have `d ∈ {1, 4}`). Two more full rounds at α=7 is a lot of degree
(`7^8 ≈ 2^22.5` per coordinate, still below `p − 2`), and GSR's own numbers at *three*
unreached full rounds and one variable were `2^27.4`; with eight full rounds and up to eight
residual variables the Macaulay-bound cost is plausibly far past `2^124` — **but that is a
guess, and this lane does not ship guesses as numbers.**

> **THE COMPUTATION, named and priced.** Extend `notes/gsr-scripts/gsr_calc.py`'s shape with
> 1792's §4.2 cost model (`C_GB` on the Macaulay bound at `ω=2`, `C_FGLM` on `D_I` at `ω=3`,
> both stated in their §2.4/§4.1), **reproduce Table C.1's `t=16` column for rows a–f
> first** (the same guard that reproduced GSR's Table 1 5/5 before pointing it at us), then
> evaluate `(p = 2013265921, t=16, α=7, c=0, d=8, r_F=8, R_P=13)` against `2^124`. ~60–100
> lines, no dependencies, under a minute. **Until it runs, VERDICTS §5h's *"the instances GSR
> breaks are not the instances that carry our security claim"* is true of GSR and
> unestablished for 1792 on the Merkle node.**

**Bearing on the repair already priced.** §5h's fix `R_P 13 → 20` (+5.0%) puts `R_P = 20 >
2E_c = 16` — **four partial rounds beyond the nonlinear trail** on the Merkle node, which in
1792's model is where the `2^128` line is crossed with room to spare; `R_P = 15` (the
containment) stays *inside* the trail (`15 < 16`). ⚑ **So 1792 is a second, independent
argument for going straight to 20 rather than 15**, on a different object (the Merkle node)
and by a different route (GB with nonlinear subspaces) than GSR's.

**The bounty instance, for the record** `[READ, §3.3 "A concrete instance"]`: KoalaBear
`t=16, α=3`, CICO-2: `E_c = 16 − 2 − 2 = 12`, nonlinear trail length 24 **> the bounty's
`R_P = 20`** — *"This instance is not a complete attack, but an explicit nonlinear subspace
trail for the internal partial rounds"*, with verification code in their repository. That is
the Poseidon1/KoalaBear Initiative instance (§1.3), fully absorbed by a trail, in print.

**Neptune and the rest**: SitM models are Neptune-only (*"inverting the external rounds of
Poseidon causes a degree explosion"*); *"input subspaces are avoided by the initial linear
mixing layer of Poseidon2"* — consistent with our `M_E`-skip composability finding (VERDICTS
§5h, `gsr-cheaplunch-composability.md`) and with nothing new claimed against it.

### 7.3 eprint 2026/1842 — abstract only

Not landed; §2.2 stands as written from the abstract page. The parameter table, the assumed
exponent on `D_I`, and the response to 2025/259 remain **unread**.

### 7.4 Citation grep, final state

Mirror ids 1731–1792 full text (`pdftotext`, no `-layout`), `grep -c '2026/1692'`: **only
1760 cites it** (its ref. [3]). 1792 does not. Ids 1793–1861 were not on the mirror when this
lane closed.
