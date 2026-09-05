# Lova, Neo/SuperNeo implementations, degree-D RMFE — three reviewer claims read at source

2026-09-04. Literature lane for the joint-algebra question (`swarm/ASTRA-ALGEBRA-PROMPT.md`). An external
reviewer made three claims our corpus did not hold. Sources: Lova = `IACR-eprint-mirror/2024/1964.pdf`
(pdftotext, pages cited); RMFE = `IACR-eprint-mirror/2023/173.pdf`; Neo v2 = `~/paperbin/…2026-242-v2026-08.txt`
(Aug-13 revision); eprint abstract page for 2026/242 (one fetch). Instruments: `gh api` (repo metadata,
READMEs, trees, code search), scry `github.documents`, kagi ×3 (q1 "Neo lattice folding scheme implementation
github Setty", q2 "SuperNeo folding github rust", q3 "Nightstream lattice zkVM SuperNeo benchmark …"),
script `notes/galois-scripts/rmfe_toy.py` (brute force, reproduced below). No commits; VERDICTS untouched.

Verdict in three lines: (1) **Lova is exactly what the reviewer said** — unstructured SIS, q = 2^64 literally,
Rust — but it folds *Ajtai openings + a subset-sum sketch*, not R1CS/CCS, with t = 330 ternary challenge
columns, 16–47 MB per fold and 700–3,000 s per fold; its verifier is ≥ 7.4·10⁶ constraints/fold, i.e. the
**Merkle-wrap magnitude, not the 4–50× band**. (2) **Neo/SuperNeo has three independent research
implementations** (Nightstream ★30 Lean+Rust; moven0831 Rust PoC; a Swift/Metal one) — "no implementation"
is dead; "no published constraint count for its own recursive verifier" **survives** (a Nightstream test would
print it; nobody has). eprint 2026/242 was **revised today (3rd revision, CRYPTO 2026)**. (3) The reviewer's
RMFE toy is correct and is the paper's own (2,3;2) example; RMFE packs at **rate 0.28 (D=2) / 0.11 (D=3)** at
our r ≈ 129 — better than *one lane per extension element* by ×36, **worse than one lane per base element**
by ×3.6, which is what our sumcheck already uses. Trap verdict stands; one seam sentence softens.

## 1. Lova (eprint 2024/1964, Fenzi–Knabenhans–Nguyen–Pham, ASIACRYPT 2024)

**Modulus [READ].** "we are able to choose the lattice modulus to be a hardware-friendly power-of-two (q = 2^64
in our evaluation), which eschews modular arithmetic altogether" (p.3); "We choose q = 2^64 for the lattice
modulus" (§4.1 p.18). Literally 2^64, not a prime near it; the code's `Ring` type is generic and the parameter
notebook sweeps q ∈ {2^32, 2^64, 2^128}.

**Commitment [READ].** Unstructured Ajtai: A ∈ Z_q^{n×m}, As ≡ t (mod q), binding by SIS (p.3–4, Def 1 p.10);
knowledge soundness under SIS_{n,m,q,(2kt+1)β} (Lemma 6 p.16). No ring, no NTT, "matrix-matrix multiplication
with bounded-norm entries" (p.3).

**Relation [READ] — not R1CS, not CCS.** Eq. (1) p.7: R_{q,β,t} = {(A,(T,D),S) : AS ≡ T (mod q) ∧ D = SᵀS ∧
∀i D_ii ≤ β²} — Ajtai openings of t columns carrying their own Gram matrix as an exact-ℓ2-norm certificate.
Folding = RoK (R_{q,β,t})² → R_{q,β,2t} (Fig. 1 p.12: prover sends the cross blocks S₂ᵀS₁) then R_{q,β,2t} →
R_{q,β,t} (Fig. 2 p.14: decompose S̃ = G⁻¹(S) in balanced base b, send T̃ = AS̃, D̃ = S̃ᵀS̃; challenge
C ← {−1,0,1}^{2kt×t}; output S′ = S̃C; verifier checks GᵀD̃G = D, T̃G ≡ T, outputs (T̃C, CᵀD̃C)). p.17:
"unlike in Nova [KST22], we cannot easily modify our construction to support (relaxed) R1CS relations … the norm
of the (additional cross-term) folded witness now depends on the magnitude of entries in the R1CS matrices …
We leave a construction of a lattice-based folding scheme for R1CS-type relations as future work." NP-hardness
via subset sum only, as a "sketch" (Eq. 3 p.18: D = SᵀS − Sᵀ1, D_ii = 0 ⇒ binary). Neo v2 p.4 reads it the
same way: "Lova [37] avoids this issue but at the cost of only supporting the subset sum relation, not CCS."

**Challenge set and what it needs [READ].** Ternary, uniform. The extractor (coordinate-wise special soundness
with the [BBC+18] heavy-row argument, Lemma 5 p.14–16) needs, per coordinate j, two accepting transcripts
differing only in row j with *some* entry difference equal to ±1 — never ±2: "for δ = ±2, it is unclear whether
the extracted witness is short, or even if it is well-defined, e.g. for even moduli q" (p.6). ⚑ So Lova never
inverts 2 and never needs an exceptional set: this is how it lives at Lenstra constant 2. Price: soundness
"roughly (2/3)^t" per column (p.6); Lemma 5 needs ε > 4·2^{t(δ+2/3)}/3^t, extractor time O(λkt/ε); the exact
step adds (2/|C|)^t = (2/3)^t from a DLSZ identity test on the Gram matrix *over ℤ* (p.16–17, footnote 3 p.8:
ternary "is what allows us to have soundness in this step"). Parameters p.18: κ_KS = Q(κ_PIT + κ_rS + κ_SIS);
λ = 128, Q = 2^64 ⇒ **t = 330**, κ_SIS ≤ 2^−193. One fold's challenge is a 2kt×t ternary matrix: the verifier
"needs to sample ⌈3.22·kt²⌉ bits" (p.20) — [DERIVED] 871,200 trits ≈ 1.4 Mbit per fold.

**Norm growth [READ].** None in honest execution (decompose-and-fold); perfect completeness iff
t ≤ β/(2k·⌊b/2⌋·√m) (Lemma 4 p.13); chosen β = (4t)²·m, b = ⌊√β⌉, k = 4 (p.18). Extraction is *exact*
(no slack), so "the number of folding steps is independent of the instantiated lattice parameters" (p.3) —
no norm wall at all, versus our additive budget `b₀ + T·ρB` (VERDICTS §3c, safe to T = 2⁴⁷−2).

**Verifier cost per fold [READ p.20].** Checks T̃G ≡ T and GᵀD̃G = D: n·2t and (2t)² linear constraints;
T′ = T̃C and D′ = CᵀD̃C: n·2t and (2k)² + (2kt)² quadratic constraints ("very sparse … some variables are
ternary … may be exploited to significantly reduce the overhead"). [DERIVED] at t = 330, k = 4:
(2t)² = 435,600; (2kt)² = 6,969,600; + 1,320·n ⇒ **≥ 7.4·10⁶ Z_{2^64}-constraints per fold before the n terms.**
n (commitment rows) is not printed; the code sets it by binary search against `lattice-estimator` (util.rs
comment; the notebook's exploratory point is h = 1,023 at m = 2^16, q = 2^64).

**Sizes and times [READ Table 2 p.20].** Per fold step, m = 2^17 / 2^18 / 2^19: IVC-type proof 16.62–19.18 MB,
PCD-type 41.62–47.36 MB; prover **702–3,244 s** (AWS m5.8xlarge, 32 vCPU, p.19). No verifier time reported.
Neo v2 p.4 [READ]: "Lova also incurs extreme overheads, reporting a prover time of ≈3,000 seconds for a subset
sum instance of length 2^19 [37, Table 2], compared to 500 ms for Nova"; p.12: "several orders of magnitude
slower". The accumulator carries T ∈ Z_q^{n×t} plus the t×t Gram matrix D with entries ≤ β².

**Code [READ p.19 fn.6 + gh api].** `https://github.com/lattirust/lova`: Rust 98 KB + Jupyter 285 KB, ★2,
0 forks, created and last pushed **2025-04-22** ("Split off lova"); `src/{prover,verifier,util}.rs`, criterion
bench at 2^17–2^19, `inner_security_parameter = 330` hard-coded (util.rs:113), depends on `lattirust` and a
`lattice_estimator` crate. Second party: cardano-foundation/bls `lattice-prover` (Rust, ★6, pushed 2026-08-31)
has a Lova design doc and says "No code here yet" [READ]. Kagi not needed (URL in the paper); code search
`"eprint.iacr.org/2024/1964"` → 15 files, one implementation (lattirust).

**Bearing on our tree.** Claim 1 is true as stated and materially incomplete. (a) VERDICTS §3c "hash commitments
do not fold; PQ lattice fold 4–50×": the first half is confirmed by one more instance; the second half is the
*dual-mode, structured-MSIS* derived price (`nebula-vega-lessons.md` §1c: 4–7·10³ R_q rows ≈ 0.4–5·10⁶
base-mult-equiv). Lova's measured *unstructured* fold verifier is ≥ 7.4·10⁶ base constraints — [DERIVED, count
only] 1.5–18× above that band, ≈ 740× Nova's 10⁴ gates, 0.78× the Merkle wrap's 9.5·10⁶ constraint-equivalents.
The honest conversion is by constraint count; no clock exists on either side (Lova reports prover seconds and
no verifier time; ours are permutation counts). The ordering should read **DL 1× < dual-mode PQ ~4–50×
[DERIVED] < Lova unstructured PQ ~10²–10³× [READ, count] ≈ Merkle wrap ~10³×**, and "4–50×" must be scoped
"structured MSIS fold". (b) `galois-ring-stack.md` §2's absence "no lattice PCS over a power-of-two modulus is
published" **survives as worded**: Lova has no evaluation claim and no opening protocol — it is not a PCS, and
that note's mirror sweep listed 1964 among its 13 hits and excluded it correctly. (c) What the same note got
*under*-stated: §2 "Escapes [INFERRED, ours, unverified]. Repetition: κ ≈ 100–128 parallel challenges" — Lova is
the published instance, at **t = 330** (ternary CWSS gives (2/3)^t, not 2^−t), with the price visible above;
and §3's "1/2 per fold over Z_{2^k}" is right for one exceptional-set challenge but the CWSS route needs no
exceptional set. (d) Lova's exact-norm proof is modulus-free (DLSZ over ℤ on SᵀS): it is the ℓ2 analogue of
the "Z/2^64 has lattice norms" remark in §3 and would transfer to `AccRbrFold`'s Gram-free budget only by
adding a t×t witness-side matrix — a shape change, unpriced.

**Sentences at risk.** `docs/VERDICTS.md` §3c line ~308 "DL fold 1× < PQ fold ~4–50× < Merkle wrap ~10³×"
(scope PQ to structured; add the unstructured data point); `docs/VERDICTS.md` §7.2 blockquote "every lattice
PCS/fold/opening loses its challenge space (1/2 knowledge error per fold)" (single-challenge; repetition route
published, priced); `notes/galois-ring-stack.md` §2 "Escapes … unverified" and §3 "1/2 over Z_{2^k}" and §7
"(S2) … ×κ ≈ 100 repetitions"; same ordering duplicated in `forcodex/02-LANDSCAPE.md:903`,
`forcodex/03-MEASUREMENTS.md:946`, `notes/nebula-vega-lessons.md` §1c.

## 2. Neo/SuperNeo (eprint 2026/242) — implementations

**The paper moved today [READ, eprint page].** "History: 2026-09-04: last of 3 revisions; 2026-02-13: received";
"A minor revision of an IACR publication in CRYPTO 2026"; Note: "Updates to support folding CCS over extension
fields, minor typo and bug fixes, and improved error bounds. This work subsumes 2025/294". No "github",
"implement" or code URL anywhere on the page. `~/paperbin` holds revision 2 (Aug 13); revision 3 not fetched
(mirror-sync rule) — whether the Note text changed between rev 2 and 3 is unknown.

**Implementations found [READ, gh api 2026-09-04].**
1. **LFDT-Nightstream/Nightstream** — "Lattice zkVM (post-quantum zkVM)". Lean 17.0 MB + Rust 6.1 MB, ★30,
   8 forks, created 2025-08-17, pushed 2026-09-04 (default-branch HEAD 2026-07-11, wasm-vm merge). README:
   "SuperNeo folding pipeline Π_CCS → Π_RLC → Π_DEC (`neo-reductions`, optimized + paper-exact engines)",
   "HyperNova-style recursive IVC layer", Goldilocks + degree-2 extension, Ajtai MSIS, Poseidon2-only
   transcript, "F′ recursive-step shell … R1CS compiler", Spartan2 decider; "Research software … Not
   production-ready"; "No independent audit or formal verification of the Rust implementation". Wiki
   parameters: κ = 18, λ = 125 target, effective-λ floor 96 bits for the s = 2 engine. `formal/superneo-lean`:
   132 `.lean` files, "Lean is the mathematical source of truth", checks are `#guard`/`example` identities
   (Thm 4/5, Def 7/8, Π_DEC) behind a "theorem import wall"; GitHub code search (default branch, word `sorry`,
   that path, `.lean`) → 0 files; 122 files contain `theorem` — an index, not a kernel check; not read.
   **Measurements: none recorded.** Perf tests exist — `fibonacci_bits_perf_snapshot` and
   `fibonacci_decider_r1cs_shape_snapshot` ("R1CS shape the full-history audit circuit hands the decider") —
   but are `--ignored` and no output is committed in README, `wiki/protocol/parameters.md`,
   `wiki/development/profiling.md`, `wiki/architecture/decider.md`, `wiki/roadmap.md`, or any tree filename.
2. **moven0831/superneo** — "Rust implementation of SuperNeo … proof of concept", ★0, created 2026-05-30,
   pushed 05-31; README claims all eight milestones incl. IVC, BaseFold/FRI + Spartan-style compression, "a
   circuit builder that expresses the fold verifier as constraints", a demo that "prints timings", Criterion
   benches (`ring_mul, ajtai_commit, fold_step, compress`) — no number printed in the README.
3. **Numi2/SuperNeo-NuMetal** — Swift/Metal, ★1, pushed 2026-06-30, Goldilocks/Φ81(d = 54) profile, "not an
   independently audited production SNARK".
4. coset-io/baby-lattice-folding (Rust ★9, educational); privacy-ethereum/sonobe README "SuperNeo (WIP)"
   PR #265; dcSpark/Nightstream-readonly (archived mirror); idrees2516/latticezkvm (kagi hit, `gh api` 404).

**Instruments for the absence half.** Scry `github.documents hasToken(content_text,'SuperNeo')` → 1 row
(Nightstream README; scry's GitHub coverage is thin). Kagi q1/q2/q3 → no page reporting a measured SuperNeo
prover time or a verifier-circuit constraint count (icme.io "LatticeBlindFold" blog mentions SuperNeo, not
read). GitHub code search `"eprint.iacr.org/2026/242"` → 9 files (sonobe, midnight, blogs, manifests).

**Bearing on our tree.** `notes/neo-verdict.md`'s "Neo cannot be scored — no implementation, no evaluation, no
benchmark, and sharper: no constraint count for its own recursive verifier" splits: **"no implementation" is
false** (and was already false on 2026-08-14 — Nightstream dates from 2025-08-17; that sentence carried no
instrument line, which is the failure class `the-absence-problem.md` names). "No evaluation/benchmark" stays
true *of the paper* (rev 2 p.4 quotes only others' numbers; rev 3's Note lists no evaluation). **"No
published constraint count for its own recursive verifier" holds** — neither the paper nor any repo README/wiki
states one — but it is now *measurable from a public tree* (`cargo test -p neo-fold-clean --release --test
perf_fibonacci_bits -- --ignored fibonacci_decider_r1cs_shape_snapshot`), which is a cheaper probe than the
sage-estimator one the verdict named. §3c "Neo's configuration is killed twice by the dual-mode" is untouched
(it is about ring-native absorb rows, not about whether code exists).

**Sentences at risk.** `notes/neo-verdict.md` §"What the lane settled" — "No implementation, no evaluation, no
benchmark"; `swarm/ASTRA-ALGEBRA-PROMPT.md:120` "unscoreable (no implementation, no verifier constraint count)";
`notes/neo-superneo-read.md` §0(b) "No implementation section" (true of the paper; scope it); `SLVG_THOUGHT.md`
§IV-b table row "machine-checked compilation layer … nobody" is *not* contradicted by Nightstream's Lean track
until someone reads whether it states soundness or only computes identities.

## 3. Degree-D RMFE (eprint 2023/173, Escudero–Hong–Liu–Xing–Yuan)

**Definition [READ Def 3 p.11].** Galois rings GR(p^k,d) and GR(p^k,rd); additive homomorphisms
ϕ: GR(p^k,d)^n → GR(p^k,rd), ψ: GR(p^k,rd) → GR(p^k,d)^n with ψ(ϕ(a₁)·ϕ(a₂)···ϕ(a_D)) = a₁⋆a₂⋆···⋆a_D
(⋆ = lane-wise product) — an (n, r; D)-RMFE over GR(p^k,d). Lemma 1: ϕ, ψ are Z_{p^k}-linear; Prop 2: ϕ
injective, ψ surjective; Lemma 2: WLOG ϕ(1) = 1, then ψ∘ϕ = id and degree-D ⇒ degree-D′ for all D′ ≤ D
(p.11–12). p.5: "unlike CRT-based techniques it is not possible to multiply more than two values before
'decoding' … encode → multiply → decode → repeat". Note the reviewer's phrase "without requiring a ring
embedding": ϕ *is* an embedding into a ring extension; what RMFE avoids is a *splitting* (CRT) — p.4 "for MPC
and ZKPs, the quotient polynomial has to be irreducible … packing elements using CRT-based techniques is not
possible. To address this complication, … RMFEs".

**Rates over Z_{2^ℓ} [READ].** Cor 1 p.17: p ≥ n ⇒ (n, D(n−1)+1; D) by polynomial evaluation (over Z_2 this
caps n ≤ 2). Ex. 2 p.18, D = 2: (2,3), (3,5), (2m, 6m−3) m ≤ 9 → (8,21), (10,27), (18,51); (2m, 6m+9) m ≤ 14 →
(28,93); (2m, 6m+21) m ≤ 18 → **(36,129)**; (3m, 10m−5) m ≤ 33 → (99,325); (132,455), (159,565), (192,695).
Cor 3 p.19: asymptotic k/n → 4.92 (rate 0.203). Ex. 3 p.20, D ≥ 2: (3, 1+2t; t) ⇒ (3,7;3);
(3m, 7(3m+4); 3) m ≤ 150 → (450, 3178); (3m, 7(3m+10); 3) m ≤ 172 → (516, 3682). Cor 5 / Remark 1 p.21:
k/n ≈ D(1+2D)/3 asymptotically, i.e. rate 3/(D(2D+1)): **0.30 (D=2), 0.143 (D=3), 0.083 (D=4), 0.029 (D=7)**.
[DERIVED from Ex. 3's formula] small D = 3 instances near our r: (12,112;3) rate 0.107, (15,133;3) rate 0.113.

**Cost [READ + DERIVED].** The paper gives no operation counts (grep "complexity" → only §5 MPC
communication). ϕ and ψ are Z_{p^k}-linear: a k×n and an n×k matrix over Z_{2^ℓ}. For (36,129;2): 4,644
words each way; one packed GR(2^64,129) product is 129² = 16,641 u64 mults (schoolbook) for 36 lane products
= 462 per lane, versus 1 native u64 mult per lane.

**The reviewer's toy [READ + script].** S = R[u]/(u³+u+1): u³+u+1 has no root mod 2 ⇒ irreducible over F₂ ⇒
S = GR(2^k, 3). φ(a,b) = a + (b−a)u is the unique linear polynomial with f(0) = a, f(1) = b; ψ = (f(0), f(1)).
A product of two linear polynomials has degree 2 < 3, so no reduction occurs — degree 2 holds; brute force over
Z/16, all 16⁴ pairs: **True**. Degree 3: u³ ≡ −u−1 so ψ(u·u·u) = (−1, −2) ≠ (0,1) = (0,1)⋆(0,1)⋆(0,1);
1,279/2,000 random triples fail (`rmfe_toy.py`). It is exactly Cor 1 with p = 2, n = 2, D = 2 (k = 3) = Ex. 2's
(2,3;2), the paper's "simple example … ratio r/((r−1)D+1), which is optimal" (p.5) — the classical
polynomial-evaluation RMFE, not the function-field construction; D = 3 needs k = 4 (GR(2^k,4), rate 1/2). Both
halves of the reviewer's claim check.

**Bearing on our tree [INFERRED].** The question is whether the ML accumulator can ride in the sumcheck's
challenge ring GR(2^64, r), r = 107–131 (`galois-ring-stack.md` §1), at better than one lane per element.
Three ways to hold a Z/2^64 lane against that ring:
(i) *base-ring witness, extension challenges* — what §1 priced: 1 word/lane, r mults per lane per
challenge-weighting, products of witnesses native (the sumcheck prover forms ∏ w_j(x) over lanes *before* it
weights by GR challenges; the verifier's MLE evaluations at extension points are GR-linear in base values);
(ii) *constant embedding* into GR — r words/lane, r² mults: the "witness blown up r×" of §2's S2 escape;
(iii) *RMFE* (36,129;2) — 3.6 words/lane, 462 mults/lane, at most D = 2 factors before a ψ-decode; D = 3
(15,133;3): 8.9 words/lane; at the deployed constraint degree 7 (§1's α = 7 S-box) the asymptotic rate 0.029
means 35 words/lane. So RMFE beats (ii) by ×36 and **loses to (i) by ×3.6 (D=2) / ×8.9 (D=3) in both bytes
and multiplications per lane** — and (i) is what the note already uses. Quoted rate: **36 lanes per
GR(2^64,129) element (0.279), 15 per GR(2^64,133) element at D = 3 (0.113)** — better than one lane per
*extension* element, never better than one lane per *base* element. It does not touch the 1/64 law: soundness
is still bought by the residue field, and an RMFE-shaped challenge set {ϕ(ρ) : ρ ∈ {0,1}^n} has pairwise-unit
differences only for ρ ≠ ρ′ mod 2 [DERIVED: Galois-ring non-units are exactly the multiples of 2; ϕ is
injective mod 2], i.e. 2^n ≤ 2^36 ≪ 2^129 elements — worse than the ring's own exceptional set. Where it
*does* bear is the S2 seam: when the witness must live in the extension ring for the commitment/fold challenge
space (X^N+1 ≡ (X+1)^N mod 2 — no CRT slots, the situation p.4 names), the linear parts (commit, fold) can use
rate-1 coefficient packing *if* an evaluation homomorphism in Neo's Thm-5 sense exists over GR (unverified),
and any in-ring degree-≤D check (a LatticeFold-style range proof w(w−1)(w+1) = 0 is D = 3) can use RMFE at
rate 0.11 instead of 1/r ≈ 0.008: §2's "witness blown up r×" becomes "×3.6 (D=2) / ×8.9 (D=3) on the nonlinear
part". That is a ×12–36 improvement on one leg of a candidate the note killed on three independent legs (1/64
challenge law, Lenstra constant 2, T-function hashes); **"TRAP as one algebra" stands**, and Lova (§1) is the
published route around S2 with no extension at all. The paper's own reading agrees (p.22): "finding direct
applications of our novel degree-D RMFEs for D > 2 to these settings is not trivial since … degree-2
computation seems to be enough for many use-cases." `notes/inert-cyclotomic-tower.md` does not exist yet
(ls 2026-09-04); for that lane the transferable fact is: over an inert cyclotomic the lane-wise packing tool
available is RMFE at the rates above, and rate 1 needs a splitting.

**Sentences at risk.** `notes/galois-ring-stack.md` §2 "Extension: run the commitment over
GR(2^k, r)[X]/(X^N+1) … witness blown up r×" and §7 "(S2) … ×κ ≈ 100 repetitions or ×r witness" (add the
RMFE rate for the nonlinear part); §1, §6 "ML accumulator" row and VERDICTS §7.2's Galois-ring blockquote:
**no sentence moves** — RMFE never improves on a base-ring witness.

## Absence claims — corpus + instrument

- Lova implementations: paper fn.6 URL; `gh api repos/lattirust/lova`; code search `"eprint.iacr.org/2024/1964"`
  (15 files, 1 implementation). No kagi (not needed).
- Neo/SuperNeo measurements: eprint page (1 fetch, rev 3 dated today, not downloaded); `gh api` READMEs/wikis/
  trees of Nightstream, moven0831/superneo, Numi2; GitHub repo search ×5 phrasings, code search ×5; scry
  `github.documents` (1 row); kagi q1–q3. Nightstream's perf outputs are not committed; the constraint count is
  runnable, not published.
- RMFE in our corpus before today: `grep -rli 'RMFE\|multiplication-friendly' notes/ docs/ forcodex/ swarm/` → ∅
  (the paperbin holds `bootstrapping-with-rmfe-fhe-2025-350.pdf`, unread by any note).
- Kagi total 3 of 12. Not verified: rev-3 diff of 2026/242; Nightstream's Lean statements (index only);
  Lova's concrete n and any verifier time (unreported).
