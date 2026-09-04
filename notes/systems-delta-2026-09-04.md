# Systems delta, 2026-08-15 → 2026-09-04 — what moved in deployed/announced provers and zkML

2026-09-04. Systems-landscape lane. **Diffed against**: `SLVG_THOUGHT.md` §IV/IV-b/IV-c,
`notes/zkml-landscape.md`, `notes/attestable-calibration.md`, `notes/fast-systems-recon.md`,
`notes/spain-celer-verdicts.md`, `docs/the-position.md`, `notes/binaryspartan-read.md`,
`notes/binaryspartan-position.md`, `notes/catgrad-seam.md`, `docs/RESEARCH-STANCE.md`,
`notes/hash-landscape.md`, `forcodex/01b-STEERS-RECOVERED.md` §27, `docs/VERDICTS.md` §7.0.
A delta already in those files is not a delta; several candidates below were checked and
dropped on that rule (Poseidon Initiative pause, eprint 2026/1692, 2026/1760, Flock's repo,
Irreducible's shutdown, ZK-DeepSeek).

Provenance legend: **[READ]** quoted from source at URL/date · **[DERIVED]** my arithmetic
from named inputs · **[INFERRED]** my reconstruction · **[OURS]** measured/proved in our tree,
cited by note · **[TWEET]** a social post, screenshot, or a news relay of one — not a paper,
spec, or repo.

Instruments: kagi (19 queries, §9), page fetches (curl), `gh api` authenticated as emberian,
scry (hackernews.items answered; academic.catalog answered but thin — §9), ethresear.ch's
Discourse search JSON. Every absence claim names corpus + instrument in §9.

## 0. Summary

| # | target | what changed since 08-15 | bears on | verdict-changing? |
|---|---|---|---|---|
| 1 | Attestable | Nothing new: launch was **08-11** ($20M seed), two blog posts, numbers unchanged, no paper, no code | `attestable-calibration.md`, `zkml-landscape.md` §2/§9 | **no** |
| 2 | EF hash decision | Still no EF-institutional writeup (ethresear.ch, blog, eprint, EIP: none). **But leanVM v0.10 (09-03) IS the artifact**: "full rewrite with binary fields and BLAKE2s", F_{2^192}, WHIR, Flock's BLAKE2s, 128-bit RBR Johnson, spec PDF with Theorem B.7 | `01b-STEERS` §27, `hash-landscape.md` §"EF pivot", `RESEARCH-STANCE.md` | **no** on Poseidon2-stays (our reason is recursion cost, §2.4); **yes** on provenance: the "tweet-only" label can be retired |
| 3 | Binary-field systems | **BinarySpartan revised 4× on eprint, last 09-03: BLAKE3 872k, SHA-256 401k, Keccak 287k (2.1×/1.8×/1.8× the v1 we deep-read); still no artifact.** Binius64: recursion landed, Ligerito→WHIR rename, inner-rate study. Flock: recursion tower productionized | `binaryspartan-read.md` §0 (numbers stale), `RESEARCH-STANCE.md` "12.4× off" (now ~22.7×) | **numbers yes, stance no** (§3.1) |
| 4 | zkML systems | DeepProve dormant since 05-31 and still custom-licensed; ezkl dormant since 02-20; Expander since 07-20; zkGPT code exists (anonymous MIT repo, 2025); no new proof-of-inference product, no proof-of-training paper found | `zkml-landscape.md` §1/§2/§5 | **no** (one correction: zkGPT "unreleased" → an MIT artifact exists, GPT-2 only) |
| 5 | zkVMs | **Plonky3 v0.7.0 (09-04)**: `p3-binary-field` tower (no PCS yet), `p3-multi-stark` fractional LogUp-GKR, ring-switching in `p3-sumcheck`, STIR/WHIR crates, DSFS transcript, `p3-security` fixed-point round budget for recursive verifiers + legacy ethSTARK conjectured bound. **Jolt**: HyperKZG deleted, Akita lattice-PCS path 1.76–2.70× over Dory. SP1: minor releases + cuPQC post. RISC Zero: no main commits since 07-20 | `fast-systems-recon.md` ("Plonky3 has no GKR" — now false), `lookup-ram-verdicts.md`, `num-queries-pin.md`, `two-regime-calculator.md`, `zkml-landscape.md` §5 ("Jolt is hash-based" was wrong) | **one line** (§5.1) |
| 6 | catgrad / catena | catgrad: 0 commits, 0 issues since 06-10. catena: bf16 native (08-17), `catena-gpu` (HIP) crate, SafeRuntime; still no LICENSE file; zero ZK code; `gate` README says the catgrad ZK backend is future work | `catgrad-seam.md` (verdict stands; §6) | **no** |
| 7 | Plonky3 #1982 | **MERGED 2026-08-17** (`f67b0ea2`), contained in `p3-fri-v0.7.0` | `VERDICTS.md` §7.0 ("STILL OPEN / CHANGES_REQUESTED") | **yes — housekeeping** (§7) |

---

## 1. Attestable

**What changed [READ]**: nothing since our calibration. Facts pinned this pass:

- **Launch date 2026-08-11** — Calcalist, `calcalistech.com/ctechnews/article/h1ddvrd8mg`,
  `datePublished 2026-08-11T17:42Z`: *"raised $20 million in Seed funding led by TLV Partners
  and Altimeter Capital … founded in 2025 by three mathematicians: CEO Yogev Bar-On, CTO Shahar
  Papini and VP of R&D Shahar Samocha. [Papini] previously worked at StarkWare and later at
  … Safe Superintelligence."* The LinkedIn launch posts decode (snowflake ID → ms) to
  2026-08-11 16:59–19:57 UTC [DERIVED from post IDs 7492987995407618048 etc.]. So the
  company came out of stealth *during* our campaign, two days before the calibration lane.
- **Blog index** (`attestable.com/resources`, fetched 09-04) lists exactly two posts, "Proving
  LLMs at Scale" and "From Verifiability to Model-Weight Security"; the featured card carries
  the date *"August 17, 2026"* [READ]. Whether that is a publish or an update date the page
  does not say; the LinkedIn relay "they just published the first results" is 08-12 [TWEET].
- **"Proving LLMs at Scale", re-read 09-04** [READ, `attestable.com/blog/proving-llms-scale`]:
  *"All benchmarked on a single H100, with context size 4K and batch size 4"*; proof size
  *"4.35 to 7.92 MiB"*; verification *"157 to 648 milliseconds"*; *"100 bits of security"*;
  *"up to 16K tokens in the context window"*; Gemma 4 31B *"53 tokens per second for a
  batch-one 16K sequence. At batch four, it reaches 77 tokens per second"*; *"we use floating
  points for almost all of the operations during inference. Our only current limitation is
  dynamically quantizing the linear operations to 8-bit integers."* Identical to what
  `zkml-landscape.md` §2 and `attestable-calibration.md` carry. No proof system, field, hash,
  or regime named; no paper; no code (kagi q1, q2, q9; §9).
- Corporate site is `attestable.com` (the brief's `attestable.ai` does not resolve to them).

**Bears on**: `attestable-calibration.md` — every standing unknown (regime, architecture,
whether "ZK" means hiding) is still unknown. The 4K-context/batch-4 benchmark condition
versus the 16K/batch-1 Gemma figure is the same baseline ambiguity the calibration note
already flags.

**Verdict-changing?** No.

## 2. Ethereum Foundation hash decision

### 2.1 Still no institutional writeup — absence, with instruments

- ethresear.ch Discourse search JSON, `q=poseidon after:2026-08-14` → 6 topics, none from the
  EF on the decision: 25730 (08-16, "Ethereum lessons from a live end-to-end PQ proof-native
  protocol", a Parano1d testnet post), 25865 (08-31, "Poseidon2b is secure!"), 25889, 25894,
  25831 (unrelated). `q=leanVM after:2026-08-14` → 25746 (08-18, "Formally Verified Security
  for PQ-DAS / leanDA") and 25730. `q=blake2s after:2026-08-01` → ∅.
- kagi q3, q4, q8 → only news relays of the 08-13 X thread (postquantum.com, cryptotimes,
  coinmarketcap, bankless, crypto.news, dailycoin, incrypted, kucoin, binance square). No
  blog.ethereum.org, no EIP, no eprint. Bankless states it outright [READ, relay]: *"No formal
  EF blog post or EIP has followed yet, so for now this is Drake's own framing of an internal
  research shift rather than a finalized protocol update."*
- Timeline as relayed [TWEET via Bankless/ainewscrypto]: *"a strawmap timeline a production
  leanVM will arrive in 2027 and consensus, data, and execution layer deployments in 2028"*;
  claimed throughput *"about 1 million hash calls proven per second on a laptop"*.

### 2.2 The artifact that exists: leanVM v0.10, 2026-09-03

**[READ, `github.com/leanEthereum/leanVM`, release v0.10 published 2026-09-03T17:28Z]**
Release body, in full: *"Full rewrite with binary fields and blake2s."* README at v0.10:
*"Minimal hash-based zkVM, for a Post-Quantum Ethereum … leanVM was originally designed over
the KoalaBear prime and Poseidon, still available in the branch koalabear; it is being
rewritten over binary fields and BLAKE2s."*

- **Security** [READ]: *"128-bit (LDR Johnson, no proximity gaps conjecture)"*.
- **Snark machinery** [READ]: *"Binary field of 192 bits (tower of degree 3 over the 64 bit
  field) · PCS: WHIR (aka Ligerito) · Proving BLAKE2s by Flock · RingSwitching, M3
  arithmetisation, (and more) by Binius / Binius64"*.
- **Parameters** [READ, `crates/pcs/src/whir_config.rs` @ v0.10]: `SECURITY_BITS = 128`
  round-by-round; `LOG_INV_RATE_0 = 1` (rate 1/2, CLI-selectable 1..4);
  `QUERY_GRINDING_BITS = 17` *"ground after the level commitment and before its query positions
  are sampled, so the query count only needs to close the remaining SECURITY_BITS − 17 bits"*;
  `INITIAL_FOLDING_FACTOR = 6`, `SUBSEQUENT_FOLDING_FACTOR = 4`, `RESIDUAL_MAX_LOG = 5`; the
  file is *"Ported from bolt-rs (bcc-research), … CREDIT succinctlabs/flock"*.
- **Spec PDF** (`releases/download/doc-latest/leanVM.pdf`, 811 KB, fetched 09-04): Annex B
  carries *Theorem B.7 (RBR soundness)* built on *Theorem B.9 (MCA up to the Johnson bound;
  [BSCH+25, Thm 4.6])*, with *Theorem B.8 (MCA in the unique-decoding regime)* recorded *"only
  for comparison, we don't need it in the List-Decoding Regime"* [READ, pdftotext lines
  3056–3175]. This is the citable soundness statement for the EF's binary-field zkVM.
- **Benchmarks** [READ, README, Mac M4 Max]: 900-XMSS aggregation 0.818 s (1,100 sig/s,
  proof 296 KiB, 9.0 GiB peak); 2→1 recursion over 900-XMSS leaves 0.394 s; Flock BLAKE2s
  batch of 2^18 compressions: prove 540.5 ms = 485,033 compressions/s, with the phase split
  *zerocheck 40.3% · pcs opening 29.1% · commit 16.6% · witness-gen 10.6% · lincheck 3.4%*.
- **Repo mechanics** [READ, `gh api`]: the `koalabear` branch head is 2026-09-03T16:57Z and the
  rewrite landed as one restructure commit `699236d1` at 17:22Z (*"vendor/ dies, the repo
  becomes 8 clean workspace crates"*); v0.9→v0.10 is 716 commits / 300 files. `crates/flock`
  is a vendored, credited port of `succinctlabs/flock` specialised to BLAKE2s.

### 2.3 Poseidon cryptanalysis, since 08-15

- Initiative page (`poseidon-initiative.info`, fetched 09-04) [READ]: Phase 2 *"shall
  conclude in December 2026"*; Collision Prize *"PAUSED STARTING 1 AUG 2026 AoE"*; q=3
  ($32K) *"Claimed on April 6th 2026"*. **Already in `hash-landscape.md` line 602** — not a
  delta.
- eprint **2026/1760** (received 08-21, Sunghyeon Jo): full-round KoalaBear Poseidon collision
  *"in the setting where the round constants are fixed before the MDS linear layer is chosen"*
  — an adaptive-MDS (weak-instance) result, submitted to the Initiative 07-31. **Already
  triaged in `notes/eprint-delta-2026-09-04.md`** as a design-process item. Not re-read here.
- ethresear.ch 25865 "Poseidon2b is secure!" (08-31, ignotusnemo) [READ]: a production
  Poseidon2b instance (GF(2^128), t=4, x^7, RF=8, RP=58) with an executable audit against the
  Skipping-Class paper; argues the wide-state round-skipping does not reach t=4. A single
  operator's instance, not an EF statement; relevant to `hash-landscape.md`'s Poseidon2b
  thread only as one more data point that binary-field Poseidon variants are being defended
  case-by-case rather than adopted.

### 2.4 Bears on / verdict

- `01b-STEERS` §27's *"the trigger was a tweet, not a paper … do not let that provenance get
  laundered"*: the provenance is now **a tweet plus a shipped v0.10 with a spec PDF**. The
  decision itself remains uncited by the EF; the *consequence* is code.
- `RESEARCH-STANCE.md` / `SLVG_THOUGHT` §IV: our Poseidon2-stays reason is the measured
  in-circuit 30.6–210× and *recursion cost is verifier cost*. leanVM's own numbers do not
  refute that; they change the *substrate* (binary field, GF(2) R1CS via Flock, WHIR) — the
  route `docs/BINARY-POSITION.md` already classifies. **Not verdict-changing**; it is the
  strongest available evidence that the EF's chosen substrate for the hash-friendly route is
  *Flock-style GF(2) R1CS + WHIR over F_{2^192}*, not a prime-field AIR with a cheap hash.
- One number to carry: leanVM's Flock phase split (**zerocheck 40%, PCS opening 29%, commit
  17%**) is the binary-field analogue of our "is the prover hash-bound?" question — there, the
  sumcheck side is the larger half and the commitment is not. Same shape as
  `fast-systems-recon.md`'s Ceno finding.

## 3. Binary-field systems

### 3.1 BinarySpartan (eprint 2026/1656) — REVISED, still no artifact

**[READ, abstract page fetched 09-04]** History: *"2026-09-03: last of 4 revisions · 2026-08-11:
received."* Current abstract: *"BinarySpartan proves BLAKE3 at 872,000 hashes/second, SHA-256
at 401,000 hashes/second, and Keccak-f at 287,000 permutations/second, including witness
generation … At comparable security, BinarySpartan is 16.3–37.8× faster than Plonky3,
6.3–15.7× faster than Binius64, and 4.0× faster than Hashcaster, which only supports Keccak.
On all three hash functions, BinarySpartan's peak throughput matches or exceeds that of Flock,
the prior state-of-the-art system."*

| | v1 (08-11), what `binaryspartan-read.md` read | v4 (09-03) abstract | ratio [DERIVED] |
|---|---|---|---|
| BLAKE3 h/s | 410,166 | 872,000 | 2.13× |
| SHA-256 h/s | 218,735 | 401,000 | 1.83× |
| Keccak-f perm/s | 163,375 | 287,000 | 1.76× |

- **We hold v1**: the mirror's `2026/1656.pdf` (283,092 bytes, 08-16) and
  `~/paperbin/2026-1656-binaryspartan-setty.pdf` (same size) — `pdftotext` of page 1 reads
  *"219,000 hashes/second"* [OURS]. The revised PDF was **not read** (rule: no eprint PDF
  pulls; the mirror holds ids, not revisions — whether it re-syncs revisions is unknown).
  Microsoft Research's publication page quotes an intermediate *547,000 / 255,000* [READ,
  kagi q6 snippet], so at least three distinct headline sets exist.
- **Artifact**: abstract page contains zero GitHub URLs [READ]; `gh api
  search/repositories?q=binaryspartan` → 0; `q="binary spartan"` → 0 (09-04). The
  `binaryspartan-read.md` §0 finding *"no artifact"* stands for v4 as far as the abstract shows.
- **Bears on**: every comparison in `binaryspartan-read.md` §0/§1 and
  `binaryspartan-position.md` that uses the v1 rates; `RESEARCH-STANCE.md`'s *"12.4× off their
  SHA-256 throughput"* [DERIVED there from 218,735] becomes **~22.7×** against 401,000 —
  *if* the comparison were the point, which `SLVG_THOUGHT` §IV-b says it is not.
- **Verdict-changing?** Numbers yes (stale by ~2×), stance no. The v4 security paragraph
  (UD regime, no grinding, ≤2^28 coefficients) may also have moved; unverifiable without the
  PDF. Flagged in §8.

### 3.2 Binius64 (`binius-zk/binius64`; `IrreducibleOSS/binius64` redirects there)

100+ commits 08-15→09-03, no tags, no releases [READ, `gh api`]. Items with our-tree bearing:

- **Recursion is real now** — PR #2352 (merged 08-27) [READ]: *"`crates/recursion` stopped one
  step short of recursion … Nothing ever proved that circuit."* Adds `RecursiveCircuit`
  build/witness split; *"`build` needs only the shape, never a proof"*; depth-2 measured.
- **Inner-proof rate study** — PR #2405 (08-31) [READ]: at 96 bits, *"232 queries at rate
  1/2 and 116 at rate 1/8"*; recursive-verifier rows for a 4-word inner proof 873,998 (rate
  1/2) → **736,679 (rate 1/8, −15.7%)**, worse again at 1/16 (+6.4%); at 64 words rate 1/4
  gives −30.4%. The *"every caller passes [rate] 1"* admission: an unoptimized free parameter
  on the dominant recursion term. Same trade our `blowup-drop.md` §7 measured in permutations
  (prover 15.19× fewer vs verifier 2.28× more) — their optimum sits at 1/8, ours at 1/64.
- **Ligerito → WHIR rename** — PR #2372 (08-27): *"Pure rename — no parameter, no query
  count, no transcript byte changes."* Naming now matches leanVM ("WHIR (aka Ligerito)").
- **SHA-256 at 364 AND constraints/block** (#2400, 08-31); **Flock credited in README**
  (#2413, 08-31) as *"A binary field STARK protocol that builds on Binius64 and contributed
  significant algorithmic and codegen-level optimizations"*; the verifier hash crate
  (`crates/hash`) is *"sequential and reference-driven"* with **SHA-256 as `StdDigest`** and a
  BLAKE3 suite — the Merkle hash is a standard hash, as `fast-systems-recon.md` assumed.
- ZK: *"Require a cryptographic RNG where the ZK mask's entropy enters"* (#2431, 09-01) —
  hiding is being hardened, relevant to `impl-readiness.md`'s hiding survey.

### 3.3 Flock (`succinctlabs/flock`, Apache-2.0, 87★)

Known public since 06-25 (`binaryspartan-position.md` line 1016 lists it at 72★). Since 08-15:
100+ commits; **recursion tower productionization** (09-03/04: *"the driver — one call from
chain statement to converged root"*, *"the standalone root verifier (M2)"*, *"the root bundle
on the wire + the VK fingerprint (M3)"*), *"capacity-free ring switching"* docs (09-04).
README bench table is dated **2026-07-17** (Threadripper 7970X, 32T: SHA-256 305.3k/s, BLAKE3
629.8k/s at batch 2^18) with the note *"encoders have shrunk substantially since this table
was measured (2026-08-14 zk.golf-derived fused adders), so current numbers run higher —
regenerate before quoting"* [READ]. No newer published number.

### 3.4 No delta

Hashcaster (`morgana-proofs/hashcaster`) last push 07-01. ProveKit v1.0.1 (09-02) is a Noir
toolchain bump only [READ, release body]. `IrreducibleOSS/binius` archived 2025-09-09;
Irreducible shut down 2025-11-12 — both already in `binaryspartan-position.md` /
`docs/HARDWARE.md`.

## 4. zkML systems

- **DeepProve** [READ, `gh api`]: last push **2026-05-31**; 0 commits since 08-15; `LICENSE`
  still the custom *"LEGALLY BINDING AGREEMENT BETWEEN LAGRANGE LABS"* (`spdx NOASSERTION`).
  The 06-03 press release *"Lagrange Labs Open-Sources DeepProve"* (kagi q15) is therefore
  source-available, not OSI — `zkml-landscape.md` §1 stands. Lagrange blog index shows no
  Aug/Sep 2026 post (fetched; 3.8 KB page, JS-rendered — weak absence).
- **ezkl**: last push 02-20, v23.0.5. **Expander**: 07-20. **Ceno**: 3 GPU commits
  (08-25/26, *"overlap replay with shard proving"*). **jolt-atlas**: 3 commits (trig tables).
- **zkGPT**: `zkml-landscape.md` §2 says *"unreleased"*. There is `security-Anonymous/zkGPT`
  (MIT, created 2025-06-22, last push 2025-08-27, 14★) whose README reads *"This is the
  implementation of zkGPT, which is a SNARK for LLM inference … Current implementation only
  supports GPT-2"* [READ]. Pre-window, but a correction to our record: an artifact exists,
  anonymous, GPT-2 only. OpenLLM (eprint 2026/1578, same group) already in
  `spain-celer-verdicts.md`.
- **Attestable**: §1. **New proof-of-inference products / Kimi-DeepSeek-scale claims**:
  kagi q10, q18 → only 2026 explainer blogs, NanoZK (2603.18046, known), ZK-DeepSeek
  (2511.19902, known in `moe-router-binding.md`), and the Hollow-LLM attack (known). Nothing
  dated after 08-15.
- **Proof of training**: kagi q11 → zkPoT (2024/162), ZKBoost (2026/202, Feb), Optimum
  Vicinity (2025/053). Nothing after 08-15.
- scry `academic.catalog` since 08-15 with ZK×{inference, training, zkml, snark×neural,
  verifiable×inference×llm} tokens → **1 row, unrelated** (§9 for the coverage caveat).

**Verdict-changing?** No. `the-position.md` and `spain-celer-verdicts.md` are untouched by
anything found.

## 5. zkVMs — real-time, recursion, Merkle hash

### 5.1 Plonky3 v0.7.0 (released 2026-09-04) — the largest upstream delta

42 commits 08-15→09-04 (26 Nashtare, 11 tcoratger, 1 each kilic / pucedoteth / latifkasuli /
jdodinh / The-Ashwin-Karthikeyan) [READ, `gh api`]. Workspace now includes `binary-dft
binary-field multi-stark stir whir zk-codes sumcheck security lookup monolith poseidon1
sha256-air`. Items with bearing:

- **`p3-binary-field`** (#2001, 08-30) [READ]: *"the Wiedemann tower GF(2) ⊂ GF(4) ⊂ … ⊂
  GF(2^128) … Phase 1 of a staged plan; it delivers field arithmetic, extension structure,
  serialization, and a Fiat-Shamir challenger … **No PCS, DFT, or `p3-multi-stark`
  integration yet**."* Then **`p3-binary-dft`** additive NTT + `Encoder` (#2003, 08-31) and
  **ring switching in `p3-sumcheck`** (#2006, 09-03): *"Construction 3.1 [DP24] … generic over
  `F: Field, EF: ExtensionField<F>` … nothing in the construction is characteristic-2
  specific … Discharging `t'(r') = s'` against a commitment to `t'` is the caller's
  business."* Also GF(2^128) vector-native mul (#2016, 09-04).
  → Bears on `docs/BINARY-POSITION.md` (*"no char-2 AIR, no constraint evaluator, no
  witness-gen"*) and `notes/ring-switching-connectors.md`: upstream now has an independent
  ring-switching implementation to cross-check our connectors against, in the same
  MSB-first indexing convention the PR flags as *"self-consistent and wrong"* if inverted.
- **`p3-multi-stark` fractional LogUp-GKR** (#1974, kilic, 08-19) [READ]: *"the fractional
  logup GKR prover and verifier, together with lookup planning and packed fraction-table
  materialization … Exclusive lookup interactions are not supported yet."*
  → **`fast-systems-recon.md`'s line "Plonky3 has no GKR (zero hits) … build, not adopt" is
  now false at v0.7.0.** Not a verdict, but the sentence should be dated.
- **`p3-security`**: const-fn fixed-point round budget *"for protocols that grade proof
  soundness inside a recursive verifier"* (#1984, 08-17); OOD-point-count fix that had
  *"overstated security by a fraction of a bit"* (#2007, 09-03); and a **"legacy conjectured
  FRI soundness bound as specified in the ethSTARK paper"** (#2018, 09-03) — upstream now
  labels the CBR-shaped column *legacy*, matching `two-regime-calculator.md`'s posture.
  → Bears on `num-queries-pin.md` / VERDICTS §7.0's *"num_queries pin in the recursion
  verifier"*: a mechanised in-circuit budget is exactly the object that pin needs.
- **`p3-challenger` typed Fiat-Shamir transcript (DSFS / IETF draft)** (#1603, 09-04);
  **projective monomial-basis sumcheck (eprint 2026/762)** (#1900, 08-21) — already in
  `speedup-ledger.md` as ~10%; **STIR** crate with height-bucketed shared domains (#1990,
  #2005) and **WHIR** HVZK budget fixes (#1995).
- **`plonky3-recursion`**: 58 commits, all Robin Salen (Nashtare): 0.7.0 migration
  (09-04), `RecursionLayerProfile` *"the verifier-owned recursion-layer shape"* (08-28), the
  challenger's Poseidon permutation table split from the Merkle one with sponge-chain binding
  tests (08-27), and a hardening pass rejecting malformed proofs instead of panicking (08-25).
  README still: *"hasn't been audited yet."*

### 5.2 Jolt (a16z), 69 commits

- **HyperKZG deleted** (#1795, 08-25) [READ]: *"Dory is the only PCS the prover and verifier
  actually instantiate. ~3,300 lines removed."*
- **Akita** — `LayerZero-Labs/akita`, *"a high-performance, modular lattice polynomial
  commitment scheme with transparent setup and post-quantum security"* [READ, kagi q14] — is
  now a first-class Jolt prover path (#1732, 08-26) [READ]: sha2-chain on M4 Max, *"Akita is
  1.76× to 2.70× faster and uses less peak RSS at every measured scale"* (2^20: 3.84 s Dory vs
  1.42 s Akita; 2^28: 314 s vs 146 s, *"about 1.84 million trace cycles/s"*); *"single
  observations rather than confidence intervals."* `specs/lattice-claims.md`: *"Akita is a
  lattice PCS with no commitment homomorphism"* — the RLC-at-opening trick is unavailable,
  hence a native grouped opening. Already known to us as the zk-`compile_error!` scheme
  (`sis-lattice-verdict.md`); the delta is that it is now the faster production path.
  → `zkml-landscape.md` §5 *"Jolt is hash-based"* was wrong (Dory is pairing-based); Jolt's
  PQ story is now lattice, not hash.
- In-circuit hash rows [READ, commit subjects]: BLAKE3 **648 rows/compression** (08-17),
  SHA-256 **2,300 rows/block** (08-17), Keccak **3,087 rows** (09-02) — comparable in kind to
  the `RESEARCH-STANCE.md` cells/compression column, different unit (rows of a lookup-heavy
  VM trace vs AIR cells); not directly comparable, recorded for the next hash-landscape pass.
- Also: a *"Lean generator for virtual instruction expansions"* (#1825) and z3 forall-proofs —
  Jolt is growing a formal leg; `formalization-frontier.md` did not list it.

### 5.3 SP1, OpenVM, RISC Zero

- **SP1** v6.4.0 (08-12), v6.5.0 (08-26: mTLS, dalek Edwards), v6.6.0 (09-02: bounded guest
  output capture) — no proof-system change [READ, release bodies]. Blog 09-03 *"SP1 Integrates
  NVIDIA cuPQC"* [READ, `blog.succinct.xyz/sp1-nvidia-cupqc/`]: cuPQC *"exposes cryptographic
  primitives such as hash functions, Merkle tree operations, and field arithmetic as GPU
  primitives within a CUDA kernel … provided as device functions rather than opaque,
  standalone kernels"*; motivation is portability across NVIDIA generations and widening
  Prover Network participation (*"Historically, SP1's kernels were hand-optimized for specific
  GPUs"*). **No benchmark number in the post**; no hash or field change. Same blog's VEIL
  (ZK wrapper, ~3% prover / 22% verifier / 12% proof size) is dated **2026-05-01** and already
  in `speedup-ledger.md` / `nebula-vega-lessons.md` (eprint 2026/683) — not a delta.
- **OpenVM** v2.0.2 (08-14, one day before the window): *"parallel witness-generation pipeline,
  enabling sub-four-second SNARK proving"* on the Halo2 GPU wrapper [READ].
- **RISC Zero**: `risc0/risc0` main last commit **2026-07-20**; last release v3.0.6 (07-17);
  a `release-5.0` branch exists with `v5.0.0-rc.1` from 2026-01-15 and no GA. Activity has
  moved to `boundless-xyz/*` (steel 08-31, boundless 08-26). The X bio *"@RiscZero is joining
  Boundless to help power The Signal"* is undated [TWEET]. Blog index had no Aug/Sep post
  (11 KB, JS-rendered — weak absence).
- **Merkle-hash choices, current**: SP1 Hypercube Poseidon2/KoalaBear, OpenVM
  Poseidon2/BabyBear, RISC Zero Poseidon2/BabyBear (all as `fast-systems-recon.md` holds);
  **leanVM: BLAKE2s** (new, §2.2); Binius64: SHA-256/BLAKE3 (§3.2); Jolt: none (Dory/Akita).
  Twist & Shout in Jolt is unchanged since the 2025-08-18 upgrade [READ, README].

**Verdict-changing?** One sentence in `fast-systems-recon.md` (GKR) and one in
`zkml-landscape.md` §5 (Jolt) are now wrong as written; no VERDICTS §7 item moves.

## 6. hellas-ai/catgrad and catena

- **catgrad** [READ, `gh api`]: `pushed_at 2026-06-10`; commits since 08-12: **0**; issues
  updated since 08-12: **0**; not archived; 13 open issues. `catgrad-seam.md`'s "dormancy is an
  asset for a proving target" reading is unchanged.
- **catena-lang**: 9 commits since 08-15 — *"Bf16 native (#167)"* 08-17; *"Add minimal catena
  gpu (#172)"*, *"launch and scheduling (#173)"*, *"naive matmul (#174)"* 08-26→09-01 (a
  `catena-gpu` crate, HIP dialect in the README example); *"IPC and SafeRuntime using
  parent/child split (#168)"*; *"Allow multiple programs loaded per runtime (#171)"*. Repo
  `license: null` still (manifests say MIT OR Apache-2.0); 25 open issues; #48 (catgrad ops
  test suite), #125 (SmolLM2), #147 (static resource usage proofs) all still open, last
  touched 06-26 / 07-22 / 08-05. `gh` code search `repo:hellas-ai/catena-lang zk` → **0**;
  `proof` → 16 hits, all docs about static resource proofs.
- **What catena is** (the brief asked) [READ, README]: *"a deterministic array programming
  language: programs produce bitwise identical results on all platforms … a key technical
  component enabling the Hellas Network, a decentralised platform for trustless AI compute:
  Determinism enables verifiability."* Programs are hexpr open-hypergraph terms; `Runtime::
  new(GpuDialect::Hip)`. Exactly the determinism→replay story `catgrad-seam.md` recorded.
- **`hellas-ai/gate`** (Apache-2.0, created 2025-06-10, pushed 09-04) README [READ]: *"Once
  catgrad ZK backend is implemented, we can support verifying responses — check request was
  serviced correctly without quantization, context injection, tampered weights"* under
  *"# future"*. Confirms the ZK backend is still unwritten on their side.

**Bears on**: `catgrad-seam.md` "RESOLVED" verdict (fork catgrad, track catena's op
vocabulary). Catena's native bf16 removes the *"bf16 added and removed from the runtime ABI in
one week"* churn caveat; `catena-gpu`'s naive matmul is the first tensor kernel there.
**Verdict-changing?** No.

## 7. Plonky3 PR #1982 and plonky3-recursion

**[READ, `gh api repos/Plonky3/Plonky3/pulls/1982`]** `state: closed, merged: true, merged_at:
2026-08-17T08:48:31Z`, merge commit `f67b0ea2` (*"coset_dft bit reverse in two_adic_pcs
(#1982)"*), author The-Ashwin-Karthikeyan, reviews by Nashtare: APPROVED 08-13 07:46,
CHANGES_REQUESTED 08-13 08:04, **APPROVED 08-17 07:19**. Files touched:
`fri/src/two_adic_pcs.rs` only. `compare/f67b0ea2...p3-fri-v0.7.0` → `ahead_by 28, behind_by
0` — **the fix is inside the v0.7.0 release**.

- **Bears on**: `docs/VERDICTS.md` §7.0 (*"PR #1982 is the same change and is STILL OPEN /
  CHANGES_REQUESTED (checked 08-14), so we carry it with the provenance recorded"*) and
  `notes/blowup-drop.md` §"PR #1982" / item 4 (*"If upstream merges it, drop the delta from
  `vendor/plonky3-fri-82cfad73`"*). The stated condition is now met.
- **Verdict-changing?** **Yes, as housekeeping**: §7.0's provenance sentence is stale, and the
  vendored delta can be retired on the next upstream sync to ≥ `f67b0ea2` (v0.7.0). The
  measured trade (prover 15.19× fewer permutations, verifier 2.28× more, config flip NOT
  landed) is unaffected. Not done here (no implementation-tree edits; no VERDICTS edits).

## 8. What I could NOT verify

- The **revised BinarySpartan PDF** (v4, 09-03): security paragraph, artifact URL, parameter
  changes. Only the abstract page was read.
- The **Drake thread itself** (x.com does not serve without JS); all thread quotes are relays
  and are labelled [TWEET].
- **RISC Zero's and Lagrange's blogs** for Aug/Sep posts — JS-rendered indices, absence weak.
- Whether the mirror's `2026/1656.pdf` will ever pick up revisions (it holds v1).
- catena's `Bf16 native` and `catena-gpu` PR bodies are empty; scope inferred from titles.

## 9. Instrument log and absence lines

**kagi (19 of ≤25)**: q1 `attestable.ai blog` · q2 `Attestable zero-knowledge proof LLM
inference 2026` · q3 `Ethereum Foundation Poseidon abandon SHA BLAKE lean Ethereum hash
function decision` · q4 `ethresear.ch lean Ethereum binary fields blake2s hash function
Poseidon` · q5 `Poseidon Cryptanalysis Initiative results 2026` · q6 `BinarySpartan Setty
Spartan binary fields github implementation` · q7 `leanVM binary fields blake2s rewrite Flock`
· q8 `Justin Drake "Goodbye, Poseidon"` · q9 `Attestable AI Yogev Bar-On zero-knowledge
announcement` · q10 `verifiable inference zero-knowledge proof product launch September 2026`
· q11 `proof of training zero-knowledge 2026` · q12 `SP1 Hypercube real-time proving Succinct
2026` · q13 `RISC Zero R0VM 2026 release Boundless` · q14 `Akita lattice polynomial commitment
scheme Jolt` · q15 `DeepProve Lagrange zkML August 2026` · q16 `zkGPT Xuanming Liu code
release verifiable LLM inference` · q17 `Irreducible Binius64 recursion announcement 2026` ·
q18 `zero-knowledge proof DeepSeek Kimi inference proof 2026` · q19 `RISC Zero joining
Boundless The Signal ZK consensus client 2026`. Raw results in the scratchpad `kagi-sd-*.txt`.

**Absence claims**:
- *No EF-institutional writeup of the hash decision* — corpus: ethresear.ch (Discourse
  search JSON, 4 queries, §2.1), kagi q3/q4/q8 (24 results, all relays), Bankless's own
  statement; instrument dates 09-04.
- *No BinarySpartan code artifact* — corpus: GitHub (`gh api search/repositories`,
  `binaryspartan` → 0, `"binary spartan"` → 0), eprint 2026/1656 abstract page (0 GitHub
  URLs), kagi q6 (eprint + MSR page only).
- *No new Attestable post/paper/code since 08-17* — corpus: `attestable.com/resources` (2
  posts), kagi q1/q2/q9, scry `academic.catalog` (below), GitHub search `attestable zk`
  (unrelated hits only).
- *No new proof-of-inference product or proof-of-training paper after 08-15* — corpus: kagi
  q10/q11/q18; scry `academic.catalog` since 08-15 with token sets {zero,knowledge}×title,
  {zero,knowledge,inference}, {zero,knowledge,training,model}, {zkml}, {snark,neural},
  {verifiable,inference,llm} → 1 unrelated row. ⚠ Coverage caveat, measured: the relation's
  declared extent is `built_at` **2026-08-13 → 2026-08-27** (18,426 rows with `published_at ≥
  08-01`; `max(published_at)` is a 2299 sentinel), so **anything posted after 08-27 is absent
  by construction**. This absence covers 08-15→08-27 only, and weakly.
- *HN*: scry `hackernews.items` stories since 08-15 matching poseidon/attestable/zkvm/
  zero-knowledge/zkml/binius/"proof of inference" → 3 rows, max 1 upvote ("Why Ethereum
  Walked Away from Poseidon" → an X post, 08-17; an EFF age-verification piece; a SaaS teaser).
  Nothing on HN carried any of this.
- *RISC Zero main quiet* — corpus: `gh api repos/risc0/risc0/commits` (last 07-20), releases
  (v3.0.6 07-17), org listing (only `risc0` pushed in window, 08-28, on a non-main ref).
