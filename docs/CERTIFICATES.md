# CERTIFICATES: an algebra of content-bound claims that does not name a prover

2026-11-05. Tags: [READ] seen at the cited file:line; [MEASURED] I ran it; [CLAIM] asserted
elsewhere, not checked; [INFERRED] my derivation. Companions: `docs/PROOF-SYSTEM-SPACE.md`,
`notes/selvage-foundations-critique-2026-11-05.md`, `notes/proof-system-codex-synthesis.md`.

Ember's ask: *"certificates that a substring matches at a particular location, properties on the
form, everything else all like that"*, composed across proof systems. PROGRAM-2026-11-05 F6 says
the receipt should not name a prover. This doc defines the objects, the composition laws, the
three instantiations, what Dregg2 already proves, and the Lean statements to add, each with its
vacuity falsifier.

---

## 0. Three findings first, because they change the design

1. **The existing DFA soundness theorem does not mention the word.** [READ]
   `Dregg2/Crypto/Dfa.lean:169-177`: `Statement` holds `δ, q₀, accept`. It holds no input, no
   record index and no commitment. `dfa_verify_sound` (`:200-205`) concludes
   `∃ trace, DfaAccepts δ q₀ accept trace`. For a **complement** automaton (the absence use case)
   that conclusion holds for nearly every automaton and every proof. It is close to `True`. The
   chain "accepted proof ⇒ this record avoids P" is not in the theorem. It lives in prose and in
   the circuit's public-input wiring. Codex found this independently
   (`notes/proof-system-codex-synthesis.md` §A6). It calls the result a zero-work "splice"
   falsifier: an accepting run over a benign word satisfies the statement for any record. **Every
   certificate below therefore takes the content commitment as part of its statement.** This is
   law zero.
2. **For a public position and pattern, "substring P at position i" needs no proof system.** It
   needs only a vector-commitment opening. Over a byte-leaf Merkle tree with salted leaves it
   costs `⌈|P|/leaf⌉` authentication paths, about `log₂ n` compressions each. For a 32-byte
   pattern in a 1 MiB record with 64-byte leaves that is two paths of 14 compressions
   [INFERRED]. A proof system becomes necessary only when the position is hidden ("P occurs
   *somewhere*"), the pattern is a language (regex, grammar), the claim is a negation (absence),
   or the claim quantifies over a corpus. The algebra keeps the two tiers separate, so a receipt
   never pays for a STARK it does not need.
3. **Today the binding weak link is about 2^15.5, not 2^124.** [READ]
   `AttestedAutomatonWeld8.lean` header: the descriptor carries eight root lanes, but
   `DescriptorIR2.MapOp.holdsAt` reads `(m.root 0)` only. `weld_completion_lanes_free` exhibits
   satisfying assignments that differ on lanes 1-7. The weld is also unrouted: no `EmitByName`
   entry and no by-name artifact. `AttestedQuery.server_cannot_omit` (`:358`) takes
   `Poseidon2SpongeCR`, which `Storage.DeployedFloorRefuted` refutes at the deployed one-felt
   hash. The dossier (`whatember/sources/01-...md` §5 step 3) says the weld binds "all 8 lanes";
   that is false as of the file's own header. `MMR.lean` is honest: its residual is the
   per-instance `MRootColl` at the pair `mrootFind` names, over an abstract `hash : List ℤ → ℤ`.
   Its bit security is the instantiation's: about 128 for the Rust `Blake3Mmr`
   (`dregg-query/src/mmr.rs:59-64`), and about 15.5 if instantiated at the one-felt
   `poseidon2Hash` [INFERRED].

---

## 1. The objects (proof-system independent)

Alphabet `Σ = UInt8`, or tokens `Fin V`; the algebra is alphabet-generic. A **content scheme** is
the only cryptographic primitive the certificates name.

```lean
/-- A content commitment with COMPUTATIONAL binding, stated as an adversary advantage,
    replacing Selvage's perfect `OpeningScheme.PositionBinding` (Commitment.lean:113),
    which no compressing scheme can inhabit (pigeonhole). -/
structure ContentScheme (Σ Digest Op : Type) where
  commit    : List Σ → Digest
  openAt    : List Σ → ℕ → Op
  verifyOpen : Digest → ℕ → Σ → Op → Bool
  verifyLen : Digest → ℕ → Op → Bool            -- the committed length is part of the root
  complete  : ∀ w i (h : i < w.length), verifyOpen (commit w) i w[i] (openAt w i)
  /-- binding game: an oracle adversary making ≤ q hash queries outputs (d, i, v, o, v', o')
      with both openings verifying and v ≠ v'; `bindAdv q` bounds its success. -/
  bindAdv   : ℕ → ℝ≥0
```

The statements are relations on `(digest, public data)` and witnesses `w : List Σ`:

| object | relation `R(x, w)` | notes |
|---|---|---|
| **SubstringAt** `x = (c, i, P)` | `commit w = c ∧ i + ∣P∣ ≤ ∣w∣ ∧ ∀ j < ∣P∣, w[i+j] = P[j]` | tier 1 if `i` and `P` are public: openings suffice |
| **OccursIn** `x = (c, P)` | `∃ i, SubstringAt (c,i,P) w` | `i` hidden: needs a proof, or reveals `i` |
| **MatchesAt** `x = (c, i, j, r)` | `commit w = c ∧ derives (w.slice i j) r` | regex `r : PredRE` on a span |
| **FormOK** `x = (c, G)` | `commit w = c ∧ w ∈ G.language` | CFG membership (JSON schema, chat framing) |
| **Framed** `x = (c, T)` | `commit w = c ∧ ∃ d, w = render T d ∧ guardedSafe T d` | guarded template (`HandlebarsGuarded.lean:66-80`) |
| **Absent** `x = (c, P)` | `commit w = c ∧ ∀ i, ¬ SubstringAt' w i P` | P a pattern or a regex |
| **AllRecords** `x = (R, N, φ)` | `mroot L = R ∧ ∣L∣ = N ∧ ∀ k < N, ∃ w_k, L[k] = commit w_k ∧ φ(w_k)` | corpus level; Count=0 is `φ = Absent` |
| **Produced** `x = (m, c_in, c_out)` | `∃ out, IsModelOutput(weights m, prompt c_in, out) ∧ commit out = c_out` | the model-identity weld; supplied by an inference prover |

A **certificate** for `R` under scheme `S` is a verifier `V : x → π → Bool` with knowledge
soundness: there is an extractor `E` from the adversary's query log such that
`Pr[V x π ∧ ¬ R(x, E(log))] ≤ ε_V(q)`. This is FlashProve's `VerifiableInference.Sound` shape
(`lean/VerifiableInference/Statements.lean:84-99`: straight-line extractor from the query log,
error a function of query count). It is also Selvage's RBR→FS output shape
(`Selvage/FiatShamir.lean:512`, error `(t+k)ε`). Adopting that shape lets FlashProve's theorem
plug in as the `Produced` certificate with no restatement.

---

## 2. Composition laws

Each law is a theorem schema. **The ε accounting is the content.** A law that drops the binding
term is the bug class that §0.3 found deployed.

**L0 (statement binds content).** Every certificate's statement contains `c`, and its relation
contains `commit w = c`. This is a well-formedness rule, not a theorem. `Dfa.Statement` violates
it today (§0.1).

**L1 (conjunction over one commitment).**
`Cert_S(c, φ₁; ε₁) ∧ Cert_S(c, φ₂; ε₂) ⇒ Cert_S(c, φ₁ ∧ φ₂; ε₁ + ε₂ + bindAdv)`.
The two extractors may return different words `w₁ ≠ w₂` with `commit w₁ = commit w₂ = c`. Binding
is exactly what forces `w₁ = w₂`. This is where `zkOracle_sound` (`ZkOracle.lean:90`) is too weak
for this use: it conjoins three independent discharges and never relates their words.

**L2 (aggregation over an MMR).**
`(∀ k < N, Cert_S(L[k], φ; ε)) ∧ MMRopen(R, N, L) ⇒ AllRecords(R, N, φ)`, with error
`N·ε + bindAdv_MMR + bindAdv_S` (union bound). With recursion
(`RecursiveAggregation.light_client_verifies_whole_history`, `:221`) the `N·ε` term becomes
`ε_engine`. That term is the `EngineSound` hypothesis (`:121`), which is named but not
discharged (§5).

**L3 (absence via complement).**
`Absent(w, P) ⟺ derives w (neg (any* · P · any*)) = true`. **The pattern must be padded:**
`neg P` accepts `xPx` (whole-word complement), and that is not absence. Codex flagged this (§A6).
The proved pieces are `derives_neg` and `correctness` (`Deriv/Correctness.lean:103, 267`),
`der_finite` (`Deriv/Finiteness.lean:347`) and `tableDfa_faithful` (`Deriv/TableDfa.lean:133`).
Count=0 over a corpus is L2 applied to L3.

**L4 (weld to model identity).**
`Produced(m, c_in, c_out; ε_inf) ∧ Cert_S(c_out, φ; ε_c) ∧ Bridge(c_out ≡ c'_out) ⇒`
`∃ out, IsModelOutput(m, c_in, out) ∧ φ(out)`, with error `ε_inf + ε_c + ε_bridge`. When the
inference prover and the certificate prover commit with different schemes, `Bridge` is a
certificate that one byte string opens both. It costs one in-circuit hash of the window under the
other scheme.

**L5 (transport along a scheme morphism).** A map of content schemes `S → S'` that is computable
in the certificate prover carries certificates over, adding `bindAdv_S + bindAdv_S'`. This is how
a receipt avoids naming a prover: the receipt names a **content scheme**, and each prover
supplies a morphism into it.

**L6 (tier collapse).** If `i` and `P` are public, `SubstringAt` is discharged by openings alone,
with `ε = bindAdv_S`. No proof system is involved. Hiding of the rest of `w` needs salted leaves
at the granularity of the pattern, or a ZK opening.

---

## 3. Three instantiations

### 3a. Poseidon2-8 over BabyBear (ours)

- **Scheme.** `content_commitment = hash_bytes_8` gives `[BabyBear; 8]`
  (`zkoracle-prove/src/attestation.rs:84-86`), 248 bits of digest and about 124-bit generic
  collision resistance [INFERRED, birthday]. MMR: `Blake3Mmr` in Rust; abstract `hash` in Lean.
- **Tier 2 provers.** DFA routing (`DfaRoutingGeneralEmit.lean`), Dyck/CFG replay
  (`DyckStackEmit.lean`, `CfgCompact.lean`), the weld (`AttestedAutomatonWeld8.lean`). All are
  Lean-emitted IR-v2 descriptors.
- **What blocks L1 here.** The weld's denotation reads lane 0 only (§0.3). Until `MapOp.holdsAt`
  reads all eight lanes, `bindAdv` is about 2^-15.5 (chosen-pair collision on one felt) or
  2^-30.9 (fixed-target second preimage) [INFERRED; codex §A6 reached the same numbers]. That is
  roughly 108 bits short of the digest the Rust side computes.
- **Cost of a tier-2 absence certificate per record** [INFERRED]: one DFA AIR row per byte
  (states plus a one-hot byte or a table lookup), plus a Poseidon2-8 sponge over the bytes,
  `⌈n/32⌉` permutations at 4 bytes per felt and rate 8. At 352 committed felts per permutation,
  or 141 narrowed (`COMPOSITIONS.md` C3), the **hash dominates the DFA** by about 4-11× per byte.
  That is the same "commit the boundary" lesson.

### 3b. Blake2s Merkle over M31 (Stwo)

- **Scheme.** A Blake2s Merkle root over the raw bytes, kept separate from any trace commitment
  so that it is a content scheme and not a proof artifact. Binding is about 128 bits.
- **Tier 2.** A Stwo AIR proving `Blake2s-Merkle(w) = c` (Stwo ships a Blake2s AIR [CLAIM]) plus
  the DFA run. Stwo's soundness at SASH parameters is "100 bits under the FRI conjecture" [READ,
  SASH note]. In our accounting that is a capacity-shaped figure, so `ε_V` here must be quoted at
  Johnson or UD: blowup 2 and 100 queries give about 100 × 0.5 × 1 = 50 Johnson bits, and
  `100·log₂(4/3) ≈ 41.5` UD bits [INFERRED, queries_for() in the search script]. **Any receipt
  built on Stwo at SASH's parameters inherits that.**
- **Bridge to 3a.** Prove `hash_bytes_8(w)` inside Stwo, or Blake2s inside our AIR, over the same
  `w`. That is about `n/64` compressions; in-circuit cost is the unmeasured `blake2s-m31` row of
  `INCIRCUIT_CELLS` in `notes/construction-search/space.py`.

### 3c. FlashProve's commitment

- **There is no content commitment to bind to.** [READ, helper digest of
  `docs/format/FORMAT.md:3185-3187` and `docs/format/10-proof-file.md:70-111`] The proof file
  holds no tokens. Tokens are bound only through Fiat-Shamir: the first chain's first query
  absorbs the raw request-file words (T+2 u32) and a 177-word statement containing
  `TK(request words)`. TK is a 256-bit digest under FlashProve's second hash K, built on the
  BLAKE2b compression function with a nonstandard counter word. `result-v1` prints `r, e` and
  "no token and no digest of tokens".
- **So instantiate `c_out := TK(window)`.** It is recomputable from the window by anyone. For
  `Produced` we take FlashProve's `sound_of_verify_at`
  (`lean/Johnson/Goal/Skeleton/SoundOfVerifyAt.lean:69-74`) as the certificate, with error
  `soundnessErrorInQueries t 1 ≈ q/2^124 + 2^-101`. **Caveat [READ, LIMITS/THEOREM]: K's
  properties are not assumed by that theorem; it is treated as a fixed function.** A
  certificate whose binding rests on K's collision resistance therefore adds an assumption
  FlashProve does not make.
- **The hiding caveat that decides the use case.** [READ, `docs/what-is-not-hidden.md:55`]
  *"A proof file is as sensitive as its request. Anyone who has it and the public files can test
  any guess at the whole request."* A ZK certificate over a FlashProve output therefore hides
  nothing from anyone who also holds the FlashProve proof. **Certificates over FlashProve
  outputs are meaningful in two settings:** (i) the verifier sees the window, and the
  certificate adds a machine-checked *property* (grammar, absence), not privacy; or (ii) the
  inference proof goes only to an auditor and the public sees only the certificate plus
  `TK(window)`.
- **Bridge cost** [INFERRED]: a 1026-word window is 4,104 bytes, about 33 BLAKE2b compressions of
  128 bytes. In a binary-field R1CS at roughly 14-30k constraints per compression (BLAKE3/SHA-256
  rows of 2026/1656 §4) that is about 0.5-1M constraints. This is small, and it is the U2 design
  point of `PROOF-SYSTEM-SPACE.md`.

---

## 4. What is already proved in Dregg2, and what is new

| piece | status [READ] | in the algebra |
|---|---|---|
| `derives_neg`, `correctness` | proved, `Deriv/Correctness.lean:103, 267` | L3 core |
| `der_finite` | proved, `Deriv/Finiteness.lean:347` | the complement table exists |
| `tableDfa_faithful` | proved, `Deriv/TableDfa.lean:133`; **premise**: the table agrees with `derives` on every word | L3; the premise is a per-table decision, needs `SymbolicEquivalence` to discharge |
| `dfa_bridge`, `dfa_verify_sound` | proved; **statement lacks the word** (§0.1) | must be restated (P8) |
| `cfg_bridge`, `compact_sound`, `compact_to_chain` | proved, `Cfg.lean:83`, `CfgCompact.lean:81, 90` | FormOK core; also lacks `c` |
| `guarded_render_mem_language`, `slot_confinement` | proved | Framed |
| `mroot_binds_or_collides`, `server_cannot_omit_position`, `range_complete` | proved, honest per-instance residual | L2 |
| `answer_complete`, `server_cannot_omit` (sorted index) | proved under `Poseidon2SpongeCR`, refuted at deployed hash | L2 (needs regrounding like MMR's) |
| `light_client_verifies_whole_history`, `light_client_position_non_omission` | proved under `EngineSound` (named hypothesis). Its inhabitant `real_engine_sound` (`RecursiveAggregation.lean:716`) has since been paired with refusals (`realVerify_discriminates` `:648`, `engineSound_is_a_real_boundary`), so the old "accept-all" vacuity (`LEAF-VS-RECURSION.md` corrections) is repaired at the verifier. The file itself says the **hash portal is not established** (`zero_portal_chainBound_is_free` `:672`: every hash is constant-zero there) | L2 with recursion: `ε_engine` is undischarged, and the hash leg of its witness is still free |
| `root8_binds_automaton_or_collides` | proved over `mapRoot8`; **denotation lane 0, unrouted** | L1 at Poseidon2-8, blocked |
| `zkOracle_sound` | proved; conjunction of independent discharges | weaker than L1 |

**New in this doc:** the `ContentScheme` with computational binding; L0 as a rule; L1 with the
`bindAdv` term; the padded complement in L3; L4 against FlashProve's `Sound`; L5 morphisms; L6
tier collapse; the TK bridge.

---

## 5. Lean statements to add (proposals), each with its vacuity falsifier

Each statement should land with its falsifier as a `#guard`/`decide` theorem in the same file,
and `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}.

**P1 `ContentScheme`** (as §1).
*Falsifier:* `bindAdv` must not be identically 0 for a compressing instance. Build the toy scheme
`commit w := (w.sum % 2)` over `Fin 2` and prove a concrete equivocation exists. This shows the
game is not trivially won by the honest structure, unlike `idealCommitment`
(`Selvage/Commitment.lean:220-228`).

**P2 `SubstringAt`, `OccursIn`, `Absent`** as relations. *Falsifier:* `decide` on a 6-byte
instance with `SubstringAt` true at `i = 2` and false at `i = 1`, so a verifier that ignores `i`
is caught.

**P3 tier-1 soundness**
```lean
theorem substringAt_of_openings (S : ContentScheme Σ D Op) (c : D) (i : ℕ) (P : List Σ)
    (os : Fin P.length → Op) (hv : ∀ j, S.verifyOpen c (i + j) (P.get j) (os j) = true) :
    -- with probability ≥ 1 - bindAdv q over the adversary producing (c, os):
    ∀ w, S.commit w = c → i + P.length ≤ w.length → SubstringAt S c i P w ∨ BindBreak S c
```
*Falsifier:* drop one `hv` index and exhibit an accepting tuple with `SubstringAt` false.

**P4 padded complement**
```lean
theorem absent_iff_padded_complement (w : List Value) (r : PredRE) :
    (∀ i j, ¬ derives (w.slice i j) r) ↔ derives w (.neg (.star .any ++ r ++ .star .any)) = true
theorem whole_word_complement_is_not_absence :
    ∃ w r, derives w (.neg r) = true ∧ ∃ i j, derives (w.slice i j) r = true
```
*Falsifier:* the second theorem is the falsifier. It pins the trap as a regression.

**P5 conjunction over one commitment (L1)**
```lean
theorem cert_and (S : ContentScheme Σ D Op) {V₁ V₂} (h₁ : Sound S V₁ φ₁ ε₁) (h₂ : Sound S V₂ φ₂ ε₂) :
    Sound S (fun x π => V₁ x π.1 && V₂ x π.2) (fun w => φ₁ w ∧ φ₂ w)
      (fun q => ε₁ q + ε₂ q + S.bindAdv q)
```
*Falsifier:* on the toy scheme of P1, words `w₁ ∈ φ₁ \ φ₂` and `w₂ ∈ φ₂ \ φ₁` with
`commit w₁ = commit w₂` make both certificates sound and the conjunction false at
`ε₁ = ε₂ = 0`. This proves the `bindAdv` term is necessary rather than decorative.

**P6 content-bound DFA statement** (repairing §0.1)
```lean
structure BoundStatement (State Sym D : Type) extends Dfa.Statement State Sym where
  c : D
theorem dfa_bound_sound ... (haccept : K.verify stmt π = true) :
    ∃ w, S.commit w = stmt.c ∧ ∃ trace, DfaAccepts stmt.δ stmt.q₀ stmt.accept trace ∧ trace.word = w
```
*Falsifier:* a `DfaVerifierKernel` instance whose `verify` ignores the word (the splice) must
satisfy the OLD `dfa_verify_sound` and fail the NEW one. That is an exhibited separation.

**P7 `AllRecords` over `Digest8`** (lift `MMR.lean` from `List ℤ → ℤ` to `List D → D` with
`D := Fin 8 → BabyBear`). *Falsifier:* the one-felt instance with the `rfl` collision from
`DeployedFloorRegrounded` refutes `AllRecords`-soundness at `D := BabyBear`. That records why the
lift is needed.

**P8 weld to FlashProve** (L4). Hypothesis: FlashProve's `VerifiableInference.Sound … ε`
restated over `TK(window)`. Conclusion: `∃ out, IsModelOutput … ∧ φ out`. *Falsifier:* a
certificate about `w' ≠ window` is refused because `TK w' ≠ TK window` unless K collides. This
names exactly the K-collision assumption FlashProve does not make.

**P9 weld denotation** (the deployed blocker): `MapOp.holdsAt` over all eight lanes, then re-prove
`root8_binds_automaton_or_collides` with the collision disjunct at `Digest8`. *Falsifier:*
`weld_completion_lanes_free` must become **false**: it should no longer be provable that two
different lane vectors satisfy the descriptor.

---

## 6. ZK Email (ePrint 2026/1284) and Reef (2023/1886): what is theirs

[READ, the PDF] ZK Email proves regex matches by **path verification over ε-free NFAs**
(Thompson construction via `regex_automata`). The relation `R_regex` (eq. 2) checks
`p₀ = q₀ ∧ p_k ∈ F ∧ ∀i (p_{i−1}, a_i, p_i) ∈ δ ∧ c_i = Cap(a_i, p_{i−1})`. Prover cost is linear
in the **captured path length** and independent of the email size. It is integrated with DKIM
RSA-SHA256 verification and an arbitrary-length SHA-256 with partial precomputation, written in
Circom and Noir for Groth16 and UltraHonk, and reports 3.8 s client proving and about 200 ms
verification on an M4 Pro.

**Honest comparison:**
- **Ahead of us.** It has a real-world authenticity anchor (DKIM): our analogue is DECO/zkTLS in
  `ZkOracle.lean`, which is a model. It has capture groups and selective reveal, a shipped and
  deployed system, and measured client-side costs. Its "linear in path, independent of
  document" is a statement-shape lever we do not have: our DFA AIR runs over the whole record.
- **Behind or different.** It has no complement and no absence. Its knowledge soundness is a
  paper sketch (Appendix F) with no machine check. Groth16 needs a trusted setup and is not PQ.
  It has no corpus aggregation and no grammar (CFG) certificates.
- **Not ours to claim.** Absence over a committed document is **Reef** (Angel et al., ePrint
  2023/1886): "a committed document matches **or does not match** a regular expression", with
  skipping automata, on Nova/Spartan. **We must not claim "first ZK regex absence".** What may be
  ours, pending a search of Reef's follow-ups: machine-checked complement compilation
  (`tableDfa_faithful`); CFG parse certificates in the same algebra; corpus-level non-omission
  composed with absence (L2∘L3); and the algebra's explicit `bindAdv` accounting.

---

## 7. What to build first (one sentence each)

1. **P9 + P6.** Without them, every tier-2 certificate in this repo binds about 15.5 bits or
   binds no word at all. Cost: one IR-v2 `MapOp` change plus re-emit, under a flag day already
   priced in the weld header.
2. **P4.** It is a pure-Lean afternoon and prevents the whole-word trap from reaching a receipt.
3. **L6 as a receipt format** (`substring-at/v1`: digest, `i`, `P`, salted-leaf openings). It
   ships without any prover and is the cheapest demonstrable governance receipt.
4. **P8 against a real FlashProve proof**, verifier-side only. It needs the two shipped
   full-size proofs and the window; no recursion.
