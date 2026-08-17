# The landscape — every direction explored, and its verdict

Reconstructed from the session transcripts, not from the notes corpus — so it
includes **the directions that were explored and closed before anything was
written down.** For each: what was asked, what came back, and where the
artifact is now.

## Scale, so you can calibrate

**369 top-level research/build lanes** across seven parent sessions,
2026-08-10 → 08-16, plus each lane's own sub-lanes (many report "all four lanes
are in", so the true count is materially higher — I did not enumerate the
second tier). Distribution:

| session | lanes | what it mostly was |
|---|---|---|
| `ca67a4c1` | 121 | the wide literature sweep — FHE, lattices, hardware, ring hashes, Attestable recon |
| `1b80977b` | 78 | PCS theorem extraction, zkVM reconnaissance, the build turn |
| `c352a91d` | 53 | grey literature, the prime paper, audit corpus, first implementation lanes |
| `5ba0dbe2` | 38 | binary fields, the BabyBear→KoalaBear census, the measurement fixes |
| `e68bba8f` | 38 | the hash decision, char-2 vacuity, the hbox rig, ingredient inventory |
| `3e64269c` | 33 | the zkML format pillar (this is where the campaign starts) |
| `b3c7abd2` | 8 | the current session — vacuity repair, sumcheck batching, this handoff |

⚠ **Sessions overlap heavily** because ember pruned context repeatedly and the
harness forked. The same lane can appear in several transcripts. The table
above counts each lane once, against the session that spawned it.

---

# Pillar 1 — Proof system

## 1.1 Field choice

**Asked** (ember, 08-13 11:22): *"we're only using babybear because plonky3
already was"* — is that right?

**Explored**: BabyBear · KoalaBear · Goldilocks · Mersenne31 · the 127·2ⁿ+1
family · p61 = 2⁶¹−2⁵⁴+1 · binary towers · the BFV RNS limbs as a proof field.

**Found**:
- The prime family is **127·2ⁿ+1**; KoalaBear is n=24, p61 is n=54. Prime
  members {2,12,18,24,54,72,114}. The row is **Riesel 1994, Table 5, h=127** —
  i.e. the "family law" was already in a 1994 number-theory table. Maximal
  3-adic inertia iff n ≡ 0 or 2 (mod 6).
- **KoalaBear measured ≈1.05× on the leaf prover, not the 3.36× the case was
  built on.** All three factors failed, one of them by *inverting*. See
  `docs/VERDICTS.md` §1b — that section is the single densest thing in the repo.
- **Goldilocks**: the relayed "NoCap/Ceno/Neo choice" claim was "one-third
  right, one-third stale, one-third mislabeled." Its pre-crypto history is
  older than the ZK literature: **Mikko Tommila's `apfloat` 1.10, May 1996**,
  three years before Solinas.
- **SP1 moved BabyBear → KoalaBear** and never published a reason; the only
  rationale anywhere is one sentence in a crate README, and the substantive
  "why" is in a Plonky3 PR.
- Two-adicity is the axis that matters and it is **consumed by FRI, not by
  sumcheck** — which is why the field question and the "are we still an
  FRI system?" question are entangled.

⚑ **And a number that circulated and does not reproduce.** The KoalaBear-as-RNS-limb
result was recovered from a transcript as **"77 candidate towers"**. The
re-derivation found **479** in the honest search space — and, worse,
**33 different unstated companion-exponent windows hit exactly 77.**
`notes/koalabear-limb.md:69-84` says plainly: **"Do not quote 77 without the
window."** The substance survived; the number was an artifact of an unstated
parameter. ⟨inference⟩ This is the sharpest small instance of the campaign's
characteristic error — a figure that is *reproducible-looking* because many
wrong windows produce it.

**Artifacts**: `docs/VERDICTS.md` §1b · `notes/field-choice-verdict.md` ·
`notes/koalabear-limb.md`, `notes/koalabear-limb-verdict.md` ·
`notes/koalabear-migration.md` · `minidregg/Theory/CyclotomicInertia.lean` (the
family law, with a 67-digit counterexample) · the BabyBear→KoalaBear flag-day
census, split across four sweeps (450 files / 4,216 literals / **50
independent modulus declarations** in `breadstuffs/metatheory`; minidregg has
**1**).

⚠ **A live disagreement, and it is the sharpest one in this handoff.** A
decision memo published as a claude.ai artifact on 08-13 recommends
**"KoalaBear everywhere"** (v4, `d671d644-…`, see `07-ARTIFACTS.md`).
`docs/VERDICTS.md` §1b, written later the same day, says **"KoalaBear is NOT
recommended on this evidence."** VERDICTS is current truth and the memo is
history — but the memo's *reasoning* (two-adicity 27 vs 24 is a property FRI
consumes and sumcheck does not; `3 | p−1` forcing a degree-7 S-box) is not
refuted by VERDICTS, only outweighed. **If the system moves off FRI, the memo
becomes live again.** Do not treat it as dead.

## 1.2 The prime hunt, and the paper that grew out of it

**Asked** (ember, 08-13 14:50): *"if we do a lil bit of number theory work up
front on the representation we can achieve a boon that nobody had thought to
find? a rock nobody turned over?"*

**Explored**: an exhaustive scan of `2^a − 2^b + 1` for a ∈ [96,130]
(**exactly 117 primes, exactly 93 with 2-adicity ≥ 20** — reproduced
independently); prior use of p61 = 2287828610704211969; whether tabulating
NTT-friendly primes *by 2-adicity* is novel; whether the joint FHE-modulus /
proof-field optimization had been posed.

**Found — and this is a case study in the campaign's characteristic error**:
- **"Nobody has posed the joint optimization" — FALSIFIED.** HELIOPOLIS
  (2023/1949 §6.2) derives a genuine two-sided feasibility region. What is
  *actually* absent is the **search**, not the posing.
- **"p61 appears exactly once in the public record (a 2014 Lisp comment)" —
  FALSE.** It is in the published number-theory literature with four
  independent listings, including a textbook table. A narrowed claim ("no prior
  *deployed* use") survives.
- Tabulating NTT primes by 2-adicity is **known and old**, named and standard
  in three independent literatures. It is not a proof-system idea.
- Bloemen's published scan **omits k=2** (Φ₆(2²)=13) — a real, small correction
  we can make.

**Artifacts**: `paper/DRAFT.md` + `paper/CLAIM-LEDGER.md` (title recommendation
*"Choosing the Modulus Together"*) · `paper/scripts/` · the red-team pass that
forced two claims to change before submission.

⟨inference⟩ **The pattern to inherit**: every "nobody has done X" claim this
campaign made against the eprint cache was wrong at least once, and the
refutation was usually *already in `~/paperbin`*. See `05-ERROR-CLASSES.md`.

## 1.3 Hash choice

**Asked** (ember, 08-14 16:47): *"why **are** we using poseidon2, are we stuck
with it?"*

**Explored**: Poseidon2 · Poseidon2b (binary-field variant) · a hypothetical
Poseidon3 · Monolith-31 · RPO-M31 / XHash-M31 · Skyscraper · Rescue · Griffin ·
Anemoi · Reinforced Concrete · Tip5 · Arion · Keccak/SHA-256/BLAKE3 ·
Keccacheck · SWIFFTX · Chaghri/Vision (extension-field AO hashes) ·
a **ring-native** hash of our own design.

**Found**:
- **Poseidon2 stays — but now for a measured reason, not an inherited one.**
  In-circuit it wins 30.6×–210×; natively it loses 5.82×; the crossover from
  our own shares is 2.0–4.5× against a measured 30.6×.
- ⚑ **The reason we had it at all: Plonky3 handed it to us.** Nobody had
  written that down until the design stopped being treated as fixed.
- **Poseidon3 does not exist.** Both mirror mentions are name collisions.
- **Poseidon2b is real** (GKK+25, by the actual Poseidon designers) and its
  2^106 figure is about the *binary* variant — a fact that killed a
  round-skipping panic before it cost anything.
- **Monolith-31 does not exist for our field**, and where it does it is **21×
  more expensive in-circuit** than Poseidon2-KoalaBear at equal degree.
- The **invariant-subfield attack** is a named published class whose standard
  dismissal is explicitly conditioned on *"q is prime"* — a condition an
  extension-field design breaks. That closed the τ=4 extension-field S-box
  direction.
- Binary fields collapse the *proving* advantage of algebraic hashes but **not
  the verifier/recursion advantage** — proving converges, verification does not,
  and recursion cost *is* verifier cost.

**Artifacts**: `notes/hash-landscape.md` (1,036 lines) + `notes/hash-verdict.md` ·
`minidregg/Selvage/HashFamily.lean` · `notes/poseidon2-audit-verdict.md` ·
`notes/ring-hash-design.md` (1,077 lines), `notes/ring-hash-cryptanalysis.md`,
`notes/ring-hash-tau-verdict.md`, `notes/ring-hash-build-verdict.md`,
`notes/ring-hash-scripts/` · a decision memo as a claude.ai artifact
(`1167978c-…`, `07-ARTIFACTS.md`).

## 1.4 The ring-native arithmetization-friendly hash

⚑ **The campaign's most original construction, and it survived cryptanalysis.**

**Asked**: ember, twice — *"ring-native arithmetization friendly hash is
important"* (08-13 14:50) and *"also what's up with that ring hash we were
working on?"* (08-13 19:42, recovering it after it had gone silent).

**The idea**: `End_{Z_q}(R_q) ≅ R_q ⋊ Gal` — the ring's own automorphisms are
free constraint terms, and eprint 2026/1127's own Definition 9 already carries
σ₅ and σ₋₁ as native terms, used only for constant checks. Those two generate
the full slot-permutation group of their own ring. So the paper's §D open
problem is **substantially an arithmetization gap, not a design gap.**

**Cryptanalysis verdict**: *"the direction SURVIVES — no feasible break found
on the reference instance"*, against three controls at τ=1 and τ=2.
**τ=2 leads**: the challenge space kills τ=1, integral cryptanalysis punishes
τ=4. `docs/VERDICTS.md` §7.4 lists it as open with **one named experiment that
settles it.**

**The competing option was priced and lost**: the "delegation escape" —
delegate the hash rather than build a ring-native one — measured against
σ-Poseidon at **302,141 R_q constraints** and gadget-Feistel at **92,257**,
versus **2,417,127** today. See `04-DEAD-ENDS.md`.

**Artifacts**: `notes/ring-hash-design.md`, `notes/ring-hash-scripts/`, and
⚑ **`~/src/ring-ro-hash/design_*.py`, which is NOT a git repository** —
see `07-ARTIFACTS.md`.

## 1.5 Polynomial commitment schemes

**Asked**: what can we actually build on, and what is provable about it?

**Read at theorem level** (each lane extracted exact statements, page-pinned):
BaseFold family · WHIR · STIR · DeepFold · UltraFold · SwitchFold · Ligerito ·
Jagged PCS · Zinc / Zinc+ / Relaxed Mod-PCS · Galois-ring BaseFold ·
tensor-code / linear-code multilinear PCS · the whole Ligero/Brakedown descent ·
a SoK on hash-based PCS (Skatharoudis, 2026).

**Found**:
- ⚑ **The brief's premise was wrong in a way that shrank the job.**
  `openAt : … → (Fin m → F) → Op` is the **KZG/homomorphic** shape. **No
  hash-based multilinear PCS has it** — the commitment is a Merkle vector
  commitment to a codeword, which is our existing `OpeningScheme`, unchanged.
  That prediction was made and then held.
- **Jagged PCS has no cryptographic content** — which is precisely why it is
  tractable. A convenience layer on top of a PCS that does the security work.
- **Ligerito**: exploratory formalization found the errata are **display-only**;
  the *general-code* bound sits where our proximity gap is proved
  unconditionally, while the *headline RS* bound is the expensive one — so the
  sequencing inverts from what a dismissal would have assumed.

**Artifacts**: `notes/multilinear-pcs-landscape.md` (1,692 lines) +
`notes/multilinear-pcs-verdict.md` · `notes/ligerito-exploration.md` ·
`minidregg/Selvage/LigeritoInterleaved.lean` · `docs/SELVAGE.md` §4.2, §5.2
(corrected in place).

## 1.6 Soundness accounting

**Explored**: the three regimes (unique-decoding / Johnson / capacity), the
withdrawal of the capacity regime, grinding, `num_queries`, `max_log_arity`,
extension degree, proximity gaps, correlated agreement, sponge
indifferentiability, Fiat–Shamir in the ROM.

**Found** — the parts that are not obvious from `VERDICTS.md`:
- **"Conjectured 130" is capacity-shaped — the regime `ethereum/soundcalc`
  deleted in Nov 2025.** 57 of the 130-vs-73 headroom is a *withdrawal*, not a
  knob. **Never quote 130.**
- ⚑ **A real soundness hole was found and pinned**: `num_queries` was read off
  the inner proof and never checked. The falsifier proved it: with the pin
  disarmed, **a one-query proof verified.** 16 → 34 bits at UDR.
  ⚠ **The pin does not reach breadstuffs yet** — `breadstuffs/Cargo.toml:370-373`
  pins an older rev; it needs a push (outward-facing, so left for ember).
- ⚑ **A second hole found by the same mechanism and deliberately left open and
  unquantified**: `max_log_arity` is unpinned; the partition is attacker-chosen
  and `log_arity = 0` is unrejected.
- ⚑ **Our own hardening commit un-parallelised the grind.** `find_map_any` →
  `find_map_first` was correct for determinism and destroyed the parallel
  scaling (1 thread 20,766 batches; 12 threads 20,766 — **scale 1.00**). Fixed
  08-14 with a windowed parallel min at all five sites: **10.6× mean / 11.8×
  p99 critical path, +12.6% total work, byte-identical witnesses.**
- **A `sorry` was found in a theorem's *statement*** — caught only by the
  `#guard_msgs`-pinned `#print axioms` on `sorryAx`. First time seen in the
  wild.

**Artifacts**: `docs/VERDICTS.md` §2 · `notes/grind-fix.md`, `notes/grind-phase.md` ·
`notes/num-queries-pin.md` · `notes/two-regime-calculator.md` ·
`minidregg/Assurance/TwoRegimeQueryBudget.lean` (**regime in the type**; the
withdrawn capacity regime is *unrepresentable*) · `~/dev/plonky3-recursion`
commit `52e1fab`.

## 1.7 Recursion and the tower

**Asked** (ember, 08-14 17:14): should the leaf and the recursion layer be
*different proof systems*?

**Found**:
- **SP1 and OpenVM both keep one proof system across layers**, changing
  parameters plus a hash-field swap. The deciding quantity is **`K = wrap/leaf`:
  ours is 26.9, theirs is < 1.**
  > ***Our problem is not the proof system. It is that the leaf is too small.***
- ⚑ **A measured identity, twice, with no shared code path**: the child's
  **native verify** permutations = **38,168**; the leaf wrap's **in-circuit**
  `poseidon2_perm` ops = **38,168**. *A wrap's biggest table IS its child's
  verifier, row for row.* So verifier cost and prover cost are the same
  quantity at different layers.
- ⚑ **The in-circuit Poseidon2 share is 36.45%, not the ~75% every "the tower
  is where this pays" claim rested on.**
- ⚑ **The blowup trade is net ≈65× WORSE per turn** once the tower is counted —
  every grid we had priced one layer of five.
- **Arbitrary-length extendability is priced at ×27.9 per turn**, paid whether
  or not a chain is ever extended. That was ember's suspicion and it was right.

**Artifacts**: `notes/recursion-tower-profile.md` ·
`notes/leaf-vs-recursion.md`, `docs/LEAF-VS-RECURSION.md` ·
`breadstuffs/circuit-prove/tests/recursion_tower_profile.rs`,
`.../leaf_vs_recursion_sweep.rs` · `docs/VERDICTS.md` §4c.

## 1.8 Lookups and RAM

**Explored**: LogUp · LogUp-GKR · logup* (2025/946) · Lasso · Twist & Shout ·
Shout one-hot · cq / Caulk / Caulk+ / Baloo / Flookup / µ-seek · Deep Thought
(2024/325) · Celer (2026/1453) · SP1 Hypercube's memory argument · OpenVM /
SWIRL · Ceno · RISC Zero · Nexus · ring-native lookups over Z_{2^k}.

**Found**:
- ⚑ **Two structural facts kill most of the table-efficiency literature for
  us before any detail**: our table is 2^16 rows and *public*, so the verifier
  can evaluate its MLE directly; and m ≈ 2^28 ≫ n, so sublinear-in-n is
  worthless.
- The "43m/10m" constants everyone quotes trace to **LogUp-GKR §3.3 Eq. (5)**,
  not to Celer, and **43 is not derived in Celer at all.**
- **~502 trace cells per general RAM touch in SP1** against 39–44 for the
  instruction itself. This number is the empirical backbone of `docs/SYSTEM.md`'s
  thesis — *we did not arrive at a faster prover, we arrived at a different
  statement.*
- **Deep Thought has no implementation and no benchmarks** — every number in it
  is an analytic operation count. Nobody has transplanted it to a hash-based or
  lattice commitment. Clean negative.

**Artifacts**: `notes/lookup-ram-verdicts.md` · `docs/SYSTEM.md` ·
`minidregg/Selvage/BinaryLookup.lean` (proves the one-hot equality vector *is*
the χ vector of the address bits, not merely "boolean + sums to one").

## 1.9 Binary fields and the char-2 cone

**Trigger**: the Ethereum Foundation's public pivot on 08-14 (`01b` §27).

**Found**:
- ⚑ **13 of 18 keystones are field-agnostic.** The multiplicative dependency
  is concentrated in **exactly one Lean structure** (`Selvage.FoldingData`,
  carrying `two_ne : (2:F) ≠ 0`) and **one deployed sampler**
  (`BaseFoldBcsQuerySampling`). Both are single, named, replaceable objects,
  and the char-2 replacement for the first **already existed on disk**
  (`AdditiveFriTower`).
- **The char-2 vacuity census found exactly one trap tree-wide**, and it was
  latent rather than live. Both traps closed 08-14.
- `grep -rn 'IsPrimitiveRoot\|rootsOfUnity\|primitiveRoot\|nthRoots'` over
  minidregg → **0 hits, tree-wide.** Four distinct domain constructions, none
  multiplicative.
- ⚑ **BinarySpartan: two lanes searched soundly and drew the wrong conclusion.**
  `notes/binaryspartan-position.md` and `notes/neo-superneo-read.md` both say it
  could not be verified to exist (five independent instruments, all ∅).
  **`docs/BINARY-POSITION.md` corrects this: it EXISTS** — ember holds its title
  page and abstract from the eprint *review queue*, plus an EF slide with its
  benchmark table. It is awaiting publication, so **by construction it is in no
  mirror and no author listing.** `docs/VERDICTS.md` is silent, so there is no
  tiebreak from the file that normally wins. **The rule that came out of it:**
  *absence from a published corpus is evidence about the corpus, never about
  reality, and a paper described as unpublished is not evidence at all.*
  What survives from the search either way: the name traces to **Irreducible's
  Binius64 blueprint §1.2, "Why Not Binary Spartan?" — a rejected strawman.**
  Irreducible considered this design and rejected it; Setty built it and it is
  the fastest scheme in the EF client-side benchmark.

**Artifacts**: `docs/BINARY-POSITION.md` · `notes/binaryspartan-position.md`
(1,203 lines) · `notes/neo-superneo-read.md`, `notes/neo-verdict.md` ·
`notes/char2-vacuity-census.md` · `notes/basefold-additive.md` ·
`minidregg/Selvage/AdditiveBaseFold.lean` (838 lines, 13 axiom pins) ·
`notes/ring-switching-connectors.md`.

## 1.10 Reconnaissance on the fast systems

**Asked** (ember, implicitly, throughout): why *are* they fast?

**Read at source, at HEAD**: SP1 / SP1 Hypercube / SLOP · OpenVM + SWIRL ·
`openvm-stark-backend` · Ceno + gkr-backend · Expander (Polyhedra) · RISC Zero ·
Nexus · Jolt (+ Akita) · Binius64 · leanMultisig · ezkl · Stwo.

**Found**:
- **SP1 Hypercube targets 100 bits, not 128** — one named constant.
- Its production FRI/BaseFold parameters are derived in the **unique-decoding**
  regime: *no proximity-gap conjecture.* Four of five production systems refuse
  the capacity conjecture; **we are the outlier.**
- **Binius64 commits no end-to-end prover profile.** Everything quantitative
  lives in PR and commit messages.
- **Expander's `benchmark_results.json` is 0 bytes.**
- `~/src/leanMultisig` is a **dead personal fork**, 8 commits, empty scaffolding
  — a wrong-repo hazard now recorded.
- **NVIDIA shipped `clmad`** (carryless multiply-accumulate, SM80+, CUDA 13.3),
  measured 4.1–12.9× on B200 for sumcheck vs bitsliced, and cites Binius
  explicitly. ⚑ Found by the hardware sweep and **it never reached a note.**

**Artifacts**: `notes/fast-systems-recon.md` · `notes/prover-floor.md` +
a claude.ai artifact (`ea569fc8-…`) + `paper/scripts/prover_floor.py`.

---

# Pillar 2 — vFHE

## 2.1 The two directions

Ember's framing, 08-13 12:09: **stark-in-fhe and fhe-in-stark achieve
different constructional outcomes** and both are wanted. That split survived
into `docs/SYSTEM.md` and `docs/COMPOSITIONS.md`.

## 2.2 What we actually deploy, measured rather than assumed

Three separate lanes had to correct the brief on ground truth:
- **Deployed depth is 2** (measured, 40/40) — not the 1–3 that was assumed.
- **The secret is CBD(20)** (variance 10, support ±20) — **not ternary**,
  which is what every noise formula in the literature and in our own briefs
  assumed. `vendor/fhe-dregg/src/bfv/keys/secret_key.rs:43`. This is the single
  most load-bearing parameter in every noise bound and it was wrong in the
  brief.
- **`t = 2²⁰` binds any BFV polynomial nonlinearity to degree ≤ 2 regardless
  of levels.** Encrypted attention at depth ≤ 3 is refuted, three independent
  ways, two of which the lane computed rather than found.
- **Exactly two parameter sets exist in the whole tree**, from one source of
  truth (`fhegg-core/src/params.rs:10-15`).

## 2.3 Directions explored under vFHE

| direction | verdict | where |
|---|---|---|
| Transciphering | **dead** — 269 bits of noise against a 109-bit modulus | `04-DEAD-ENDS.md` |
| Bootstrapping | **dead** — depth 13–17 crossover against our 2 | `04-DEAD-ENDS.md` |
| Amortized / batched bootstrapping | **does not apply to BFV**; the one method that uses BFV internally says in its own footnote it becomes impractical at exactly our 20-bit precision | `notes/fhe-scout-verdicts.md` |
| Scheme switching | **hazardous** — a working CPA-D proof of concept | `docs/VERDICTS.md` §3 |
| NTRU-based FHE | **all 11 parameter sets across 6 papers sit above the Ducas–van Woerden fatigue point**; 5 of 6 apply the wrong test | `04-DEAD-ENDS.md` |
| GBFV | measured directly in Fheanor at our parameters | `notes/fhe-core-theory.md` |
| Coefficient-encoded matmul | ✅ **built and measured** — 12 bits/matmul with split-sign, depth 2 after, 466 µs at 512×31 | `fhegg-fhe/src/bfv_coeff_matmul.rs`, `notes/coeff-matmul-landed.md` |
| Single joint prime (H1/H2) | **net loss at 109 bits, wins at 61**; the deciding variable is the 64-bit machine word | `notes/h2-verdict.md`, `phase0/h2-rns-vs-single-prime/` |
| The KPZ encoding fix | ⚑ **NO-OP** — already in force; the "fix" had nothing to fix | `notes/kpz-noop-and-the-model-gap.md` |
| PIR for the embedding table | ⚑ **LIVE, not closed** — "PIR rotation keys cost **2.01 MB at our parameters** (12 keys × 0.33 MB at N=4096; the literature's **857 MB** horror is N=2^16). **The field's rotation-phobia does not transfer to us.**" Un-promoted to VERDICTS, so neither confirmed nor closed. | `notes/fhe-scout-verdicts.md:28-30` |
| Circuit privacy / sanitization | **smudging does NOT give circuit privacy**, and the literature says so in as many words (2025/275) | `notes/fhe-core-theory.md` |
| RLWE worst-case reductions vs our deployment | a √n hides in a convention gap between two normalizations | `notes/fhe-core-theory.md` |
| Post-quantum status of our parameters | ⚑ **OPEN and unfavourable.** `docs/VERDICTS.md` §7.8: it is a *classical*-line set nobody ships; Apple ships N=4096 at **83 bits** for `.quantum128`, and N=8192 / 148 bits when it wants log t ≈ 20. ⚠ **A sharper pair of figures exists only in a transcript and never reached the notes** — lane `a0cbd2ee` ("2024-26 attacks and parameters") concluded *"~125.1 bits — about 3 bits short — and `log q = 109` is 3 bits over the current recommended maximum of 106… we are sitting on the 2018 table's number."* **Not in any file.** The nearest recorded numbers are deployed **98.1 core-SVP / 119.9 MATZOV / 130.5 HE-standard** (`notes/koalabear-limb.md:145-152`) — a ~32-bit spread that is **the model, not the parameters.** | `docs/VERDICTS.md` §7.8 · transcript only |

## 2.4 ⚑ Cross-limb binding — the pillar's real finding

**Exhibited in Lean, 08-14.** It was **two holes under one name**:

- **Hole A — provenance.** The checked system is `∀ i, ∃ source`; the honest
  one is `∃ source, ∀ i`. A quantifier swap, invisible to every completeness
  test. The exhibit takes limbs from *different* ciphertexts, satisfies every
  per-limb equation, and reconstructs to a value **no honest pair can
  produce** — a wrong *answer*, not merely an unbound proof.
- **Hole B — expressibility.** `⌊t·x/Q⌉` reads the CRT reconstruction, so there
  is no per-limb equation to bind at all.
- ⚑ **The obvious fix is a tautology.** "A CRT-consistency relation over the
  limbs" can never refuse: the CRT map is a bijection and the forgery is itself
  CRT-consistent.
- ⚑ **Why nobody had exhibited it**: every Lean BFV carrier in the tree makes
  the attack *unrepresentable* — and one file said so in its own residual list.
  **Documented ≠ detected, in our own tree.**
- **The fix is a layout decision and the free one exists**: interleave the
  limbs into one row and the row *is* the shared opening. +0 felts, +0
  permutations.

**Artifacts**: `breadstuffs/metatheory/Bfv/CrossLimb.lean` (`5b653ba5d`) ·
`notes/cross-limb-binding.md`, `notes/cross-limb-verdict.md` ·
`metatheory/Bfv/Ring.lean` (the noise model lifted to the ring).

## 2.5 The applied vFHE literature

Read in depth: Laminate (2025/2285) · packed sumcheck over small
characteristic (2025/719) · Zama's matvecmul (2026/027) · Dinocchio (2026/159) ·
Rinocchio · HELIOPOLIS · the whole "proofs over rings" line (LaBRADOR,
Greyhound, LaZer, SLAP, LatticeFold/+, Neo/SuperNeo, Cyclo, Symphony).

⚑ **The one structural move that dominates**: *make the FHE modulus and the
proof field the same object.* Two papers do it from opposite ends. That is what
made the joint-prime question (H1/H2) worth asking at all.

⚑ **And a clean negative that took several lanes to establish**: **nobody has a
ring-native RO-like hash.** Every lattice proof system either drops to a
coefficient-field/byte hash and eats the conversion, or is non-recursive so the
hash is never arithmetized. That absence is what the ring-hash pillar (§1.4)
aims at.

---

# Pillar 3 — zkML

## 3.1 Numeric format — where the campaign started

**Asked** (ember, 08-12 13:37): Attestable quantises matmuls to int8; *"we
don't need to accept the limitations, we can do actual floating point stuff."*

**Explored**: bf16 exact tables · MXFP4 / MXINT8 / NVFP4 microscaling ·
block floating point generally · IEEE-754 in-circuit · fixed point · int8 ·
Ozaki-scheme limb splitting · unary lookup tables.

**Found**:
- ⚑ **The bf16 4× thesis measured at 1.4×.** A clean negative, and the honest
  number. `docs/PHASE0-RESULT.md`.
- ⚑ **MXFP4 within-block exactness holds; NVFP4 preserves exactness but
  destroys the power-of-two-scale shift argument** — so our arithmetization is
  MXFP4-specific, not "block-float-generic."
- ⚑ **Measured on gpt-oss: 100% of 1,382,400 sampled reduction rows fit a
  width-8 exponent window** (max observed spread = 8, in exactly 2 rows). So
  the cheap ~1,050-constraint alignment path is not the common case — it is the
  **only** case, covering 100% of the 78.9% of per-token FLOPs that are MXFP4.
- **Block-float / shared-exponent structure inside a ZK proof system is
  essentially unwritten.** eprint searches for `microscaling`, `bfloat16 FP8`
  return literally zero. One arXiv paper (2606.05433) names the mechanism once.
  ⚠ That is a *scoped* absence, and the scoping matters — see `05-ERROR-CLASSES.md`.

**Artifacts**: `docs/PHASE0-RESULT.md` · `docs/mx-formats.md` ·
`docs/bf16-exact-arithmetization.md` · `phase0/` · `notes/float-in-zk-three-regimes.md`.

## 3.2 Nonlinearity — where the cost actually is

**Found**, and it redirected the whole pillar:
- **The nonlinear part dominates and it is not close.** Measured across three
  systems: **DeepProve 67–75%, zkGPT ~59%, zkLLM ~34% from softmax alone.**
  **Matmul lands at 5–7%.**
- Consequently: *the lever you asked me to examine is the wrong one.* Several
  lanes independently reached this and said so.
- **Requantization is not eliminated by the good systems — it is promoted to a
  first-class protocol they pay for on every operator** (OpenLLM).
- **ZIP (CCS'25) is the only IEEE-754 system and needs 37 hours for an
  11M-parameter 4-layer mini-BERT.** ⚑ **Transcript-only** — lane `a4e77a94`
  ("Transformer ZK softmax/layernorm survey", session `3e64269c`). This figure
  is **in no file in the repo**; ZIP appears three times in the notes and none
  of those carries it. Re-source before publishing.
- **Spain (OSDI'26)** is the best 2026 float system and **loses to quantized** —
  by their own Figure 4, on the same workload (GPT-2, seq=32): prover 750 s vs
  zkGPT's 64 s (**11.7×**), verifier 78 s vs 5.8 s, proof 1.6 MB vs 88 KB. Their
  §8, unprompted: *"Spain's prover isn't the fastest in the literature; that
  honor belongs to zkGPT."*

**Artifacts**: `notes/zkml-landscape.md` · `notes/spain-celer-verdicts.md` ·
`notes/ml-to-crypto-mappings.md` · `docs/PHASES-AND-TENSOR.md`.

## 3.3 MoE and scale

**Asked** (ember, 08-13 17:21): *"kimi k3 is a 2.4T moe model with many active
parameters, so we need to keep that in mind."*

**Found**:
- ⚑ **Router binding must be ZERO-KNOWLEDGE** — expert selections recover
  **91% of tokens.** That was not in the brief and it changes the protocol.
- **Ties are a property of the scoring function**: sigmoid-scored routers are
  *structurally* tied (only **26 distinct bf16 values in [0.9,1.0) for 256
  experts**); raw-logit ~4%; DeepSeek-V4's Sqrt(Softplus) never saturates.
- **V4's early-block hash routing makes selection a public function of the
  token id — so binding is free there.**
- ⚑ **A retraction worth reading**: *"MoE router binding — zero papers across
  7,090 swept, verified absence twice"* was **wrong**, and both refuting papers
  **were already in `~/paperbin`, pulled and correctly named on the same day
  the absence was declared.**

**Artifacts**: `notes/moe-router-binding.md` + `notes/moe-router-binding-cost.py`.

## 3.4 The matmul contraction, and verifiable training

Landed work, not survey:
- **`foldl → Finset.sum` bridge**, built in two *named* steps so the discard
  point is a line you can point at. ⚑ The load-bearing property is
  **associativity, not commutativity** — IEEE-754 addition *is* commutative and
  is *not* associative; and step 2 has **no counterexample at all**, because
  `Finset.sum` over `Fin k` cannot be written without commutativity, so its
  refutation is a *type error*.
- **Measured**: `[2,1024]·[1024,128]` gives a **51-field-element / 408-byte
  transcript** against the AIR route's **314,000 gates ≈ 27 MB descriptor** —
  but **the sumcheck is 5% of the prover**; the lever is the partial evaluation.
  ⚠ And the 408 bytes omits two multilinear openings that do not exist yet.
- **Rank-1 gradient check**: proved over any `CommRing`, `≤ (mᵢ+mⱼ)/|F|`, no
  rank hypothesis — so *every other rank-1 matrix* is refused by theorem, not
  by testing. **7×10⁴× cheaper than the circuit at 4096×4096.**
  ⚠ **The honest half**: it removes the n² *proof*, not the n² *commitment* —
  and once the proof is 10⁴× cheaper, **the commitment IS the step.**
- **Low-rank updates**: break-even rank is `d/2` = 2048, so **the commitment is
  never the reason to stop**; the constraint that actually binds is **steps** —
  T = 128 at d=4096, r=16.
  ⚑ And the natural `d×r` layout costs **2.0× more permutations** than
  transposing, for *identical felts* — invisible in a felt count.

**Artifacts**: `minidregg/Theory/ZkmlMatmulSum.lean` ·
`minidregg/Selvage/Rank1GradientCheck.lean` (545 lines) ·
`minidregg/Assurance/ZkmlLowRankUpdate.lean` (758 lines) ·
`notes/contraction-sumcheck.md`, `notes/rank1-gradient-check.md`,
`notes/low-rank-updates.md` · `docs/DARK-TRAINING.md`.

## 3.5 catgrad — the compiler seam

**Asked** (ember, the origin steer): can we ship zk attestability for catgrad?

**Found**: catgrad is real (MIT, 31 stars, 4 contributors, active), and
`catena-lang` is its compiler workspace. The seam verdict: **the pillar lives
in minidregg** — op vocabulary in `Theory/` (candidate-independent,
mechanically enforced), per-op semantics in `Selvage/`, emission in
`Compiler/`, engine = the Selvage sumcheck prover. The breadstuffs interim
should be dropped.

⚑ **Tripwire held**: no constraint was written in Rust. Nothing in
`~/src/catgrad-spike` was touched. All arithmetization is Lean-authored.

**Artifacts**: `notes/catgrad-seam.md` · `notes/zkml-integration-architecture.md` ·
`minidregg/Theory/Zkml*.lean` · `phase0/v0_to_v1.py` · `notes/zkml-build-log.md`.

## 3.6 The weight-commitment registry — built, then rejected

Shipped `zkml-research/registry/` (`registry_tool.py`, `MANIFEST-FORMAT.md`,
`COMMITMENTS.md`, 8 manifests, gates, run logs). Ember, immediately:

> *"bruv you just built a complete toy registry for a commitment that is
> irrelevant to all possible proof systems and patted yourself on the back"*

**The objection is exact**: a SHA-256 manifest commits to weights in a way no
prover can open inside a circuit. `docs/VERDICTS.md` §5 records the correct
object: **Poseidon2 over the field-element encoding, at a leaf granularity the
circuit opens, in the layout the prover reads.** Nobody has built that.

⚠ Also found while building it: **`deepseek-ai/DeepSeek-V4` returns HTTP 404
with credentials** — it does not exist on HuggingFace — yet two notes still
cited it as a *measured* Tier-1 exemplar.

---

# Pillar 4 — Hardware

**Asked** (ember, repeatedly): *"AWS F2 fpga i remind you, and also dreams of
custom ASICs"*; *"we should also definitely be thinking about our own TPUs
code."*

**Explored**: Zama HPU (the open SystemVerilog FHE processor) · DARPA DPRIVE ·
the FHE ASIC line (F1, CraterLake, BTS, ARK, SHARP, Trinity) · Intel HERACLES ·
ZK prover silicon · MORPH / MoMA (AI-ASIC-for-ZK) · NVIDIA `clmad` · AWS F2 ·
wgpu / GPU kernels.

**Found**:
- ⚑ **Exactly zero of the academic FHE ASIC designs have ever been
  fabricated.** Every number they report is from a cycle-accurate simulator.
  Exactly one DPRIVE chip became real silicon (Intel HERACLES), at the very end
  of the program.
- **Zama's HPU is real, open, and complete** — 553 `.sv` files, 162,770 LOC
  under `hw/`, a full processor rather than a kernel. Three shipped build
  configs. An "audit-sample instruction" was studied at ISA level and is
  feasible.
- ⚑ **The Amdahl ceiling for tensor silicon is 1.26× at the deployed point.**
  GEMM-shaped work is only the two LDE rows — **20.8% of prove** — and **MLE
  folding is under 0.1%.** Trace height does not rescue it.
- **CROSS's BAT transfers to BabyBear with zero modification** (31 bits ⇒ K=4,
  exactly CROSS's K), bit-exact four ways, **3.05× over three-limb Montgomery
  on hardware with no INT8 unit.** ⚠ **But BAT needs one operand preknown** —
  free for NTT twiddles, *not* free for an MLE fold or a sumcheck round.
- ⚑ **Four-step NTT does not survive to LDE sizes**: the extra-multiply factor
  grows as √N/log N — 341× at N=2^12, **3277× at N=2^20.**
- ⚑ **Drop MoMA and MORPH from the tensor thread**: MoMA does not use tensor
  cores at all; MORPH's GEMM is base *conversion* for 256–753-bit moduli.
- ✅ **The GPU fusion thesis holds and compounds** — 2.7–7.1× at 2^20–2^22 on
  memory traffic alone. ⚑ **Structural finding: two wgpu devices cannot share a
  buffer, so fusion was unreachable by construction** until the arena
  consolidation landed (9 device sites → 1).

**Artifacts**: `docs/HARDWARE.md` · `notes/hpu-seam-study.md` ·
`notes/ntt-as-gemm.md` · `notes/wgpu-fusion.md` · `notes/arena-consolidation.md` ·
`breadstuffs/fhegg-fhe/src/gpu_arena.rs`, `.../bin/ntt_four_step_bench.rs`.

⚑ **Not recorded anywhere until now**: NVIDIA's `clmad` instruction (CUDA 13.3,
SM80+, 4.1–12.9× on B200 for sumcheck vs bitsliced, citing Binius). The
hardware sweep found it and no note carries it.

---

# Pillar 5 — Audit economics

**Origin**: ember's recognition that Attestable's "random sampling" is the
technique we already used on the Mina bridge.

**Explored**: commit-then-audit sampling · beacon grinding (2025/1974,
"Taming Iterative Grinding Attacks on Blockchain Beacons") · the RAND SL1–SL5
framework · TEE/attestation as a competing primitive · the published ZK
audit-bug corpus.

**Found**:
- ✅ **The commit-then-audit theorem is LANDED and, as far as we can establish,
  the first machine-checked one anywhere.**
  `minidregg/Selvage/AuditSampling.lean`, 1,173 lines, sorry-free, **20 axiom
  pins**, all clean. It carries the **fail-open wound class as a theorem**.
- ⚑ **Deployed attestation gives a signed statement about *platform state*, not
  about *computation*.** Exactly one deployed system (Apple PCC) binds model
  weights into its attestation — and deliberately declines to publish them, so
  the binding is a commitment nobody outside Apple can open. **Nothing deployed
  binds "this output came from this model."**
- A **93-artifact, ~1.4 GB audit corpus** was assembled (59 audit PDFs, 29 blog
  texts, the zkbugs dataset with 139 bugs, the 0xPARC tracker). The single
  largest bug class is **Fiat–Shamir transcript ordering** — a public claim not
  absorbed before challenge derivation.
- **The beacon leg is open**: we hold the grinding mechanism and no beacon
  model. `ε_beacon` and `ε_chk` are both uninstantiated.

**Artifacts**: `minidregg/Selvage/AuditSampling.lean` ·
`notes/audit-theorem-statement.md`, `notes/audit-sampling-prior-art.md` ·
`notes/attestable-calibration.md` · `~/paperbin/attestable/` (22 files) ·
`~/paperbin/audit-*` (93 artifacts).

⚑ **The Attestable recon deserves its own line.** Five lanes established the
team, funding, lineage, Vitalik's public comment verbatim, and located,
mirrored and **transcribed a 54-minute founder interview** with whisper
large-v3-turbo. The CEO states the overhead range himself and **it matches our
independent derivation.** That is a calibration point we own and nobody else
has written down.

---

# Pillar 6 — Formalization landscape

**Asked**: what does the formal-methods world already hold, and where are we
actually unique?

**Found**:
- ⚑ **Nobody has machine-checked FRI soundness or the Reed–Solomon proximity
  gap / correlated agreement in the list-decoding (Johnson) regime.** But far
  more exists than expected: ArkLib has the Johnson bound and Guruswami–Sudan.
- **ArkLib's composition theorems are `sorry`.** That is the gap we sit in:
  we hold the **compilation layer** — between "an interactive protocol is
  round-by-round sound" and "a deployed non-interactive verifier accepts only
  true things" — and nobody else has both legs.
- **The Verified-zkEVM effort (ArkLib + CompPoly) is the only serious binary-
  field formalization**, and it is in Lean 4. Everyone else is prime-field.
- ⚑ **StarkWare + Avigad's `formal-proofs` (arXiv 2606.04311) verifies the
  LogUp protocol inside the S-two AIR** — which retracted our framing of our own
  LogUp work as "narrow but unclaimed."
- **CatCrypt** (Spitters, eprint 2026/604) — 172 game-based constructions in
  Lean 4, including FHE-adjacent material.
- ⚑ **`~/dev/minidregg/Selvage` is a 48,522-line, 96-file, zero-`sorry`
  zero-`axiom` Lean formalization of exactly the technique the literature says
  you should adopt** (WARP-style hash-based accumulation with WHIR's
  constrained-RS claim object). A survey lane found that out about *us*.
- **The carrier census / vacuity-detection methodology has a name in two
  literatures**, and its deductive-verification version was published **four
  months ago** (FMCAD 2025) — so the area is live, not closed. This is the
  finding that produced ember's "vacuity-checking is tacit behavior" correction.

**Artifacts**: `notes/formalization-frontier.md` · `notes/avigad-stwo-verdict.md` ·
`notes/vacuity-prior-art.md` · `notes/ingredient-inventory.md` (1,077 lines —
minidregg surveyed as a *library of composable primitives*: 473 files, 16,097
declarations, a name-blinded body-hash twin detector, an island detector) ·
`docs/INGREDIENTS.md`.

---

# Directions that were explored and then simply stopped

Not closed by a number — **stalled**, which is a different thing. Ember swept
for these on 08-13 16:34 and the sweep is worth reproducing, because the *shape*
of the stalls is diagnostic: work dies here when it is (a) small-but-formal
(no lane feels "worth" a 200-line change), (b) deployment glue falling between
pillars, or (c) **gated on something whose gate silently cleared and nobody
re-checked.**

**Gates that cleared without anyone noticing**
- Phase 0′ — the MXFP4 alignment-window *constraint* harness. Gated on the
  Spain/Celer reads; both landed days earlier. The data side is answered
  (width-8 covers 100%); the constraint-count harness was never dispatched.
- The Celer grand-product spike, gated on a re-pricing that landed.

**High-value, fully specified, never dispatched**
- ✅ *The two-regime security calculator* — this one later landed
  (`Assurance/TwoRegimeQueryBudget.lean`).
- **The sponge re-aim: extraction-friendly indifferentiability.** Vanilla
  indifferentiability does not close [FS-ROM] for knowledge soundness; the
  re-aim "gets the first and the closure." Never became a card. ⚑ *Arguably
  Selvage's deepest open formal item.*
- **Verified table contents** — queued since the first week, cheap, zero motion.
- **Chiesa–Orrù Corollary 1 plug** — FRI into the state-restoration framework,
  where our assets are the scarce half.

**Deployment glue for the audit theorem** (the theorem landed; its deployment
did not)
- **The beacon assembly** — `pqvrf` + fhegg's threshold ceremonies = the G=1
  threshold VUF that makes ε_beacon → 0. Nobody has checked `pqvrf`'s state.
- **The inference ledger** — the audit game's Merkle ledger as a minidregg
  Hyperdocument instantiation. The registry covers weights; nobody designed the
  per-turn ledger.
- AuditSampling's own ten named residuals.

**Small-but-formal batch**
`Ext5` (Ext6 buys zero bits by their own lemma) · the hardware rate spreadsheet
(hours of work, "prices everything else", never done) · the `fhegg-rtl`
word-level BitVec layer verdict · G3 ring noise lift · G4 CPA-D/determinism
hinge.

**Zero motion since first mention**
- ⚑ **`zkQMC`** — "proving randomized computations via quasi-[Monte Carlo]",
  described in-window as *"the mine's genuine surprise"*, **truncated
  mid-sentence by the safety classifier and never picked back up.** No note, no
  lane, no artifact. See `01b-STEERS-RECOVERED.md` §16.
- **The vacuity-methodology blog post** for `~/dev/dregg-site` — ember named
  the venue explicitly; the page was never written.
- **The Twist/Shout one-hot expert-select lane** and **the S-two carrier
  census** — both died to credit exhaustion mid-write-up and were never re-run.
