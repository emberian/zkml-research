# LEAF-PROVER-DECISION: what executes our certificate leaves, and what we stop maintaining

2026-11-05. Ember asked, before the flag day ran, whether it was grinding on legacy. The answer is
yes. This file records the question, the options priced in counts, the decision, and the first
step. Tags: [READ] seen at file:line; [MEASURED] I ran it; [X] measured elsewhere; [INFERRED]
derived here; [A] assumption.

## 0. What "our prover" is for now

PROOF-SYSTEM-SPACE §0 and the program doc settle that **we compose with FlashProve for inference**
and do not re-prove it. Our prover's workload is therefore the **certificate leaves** of
`docs/CERTIFICATES.md`: content commitments over bytes, DFA/complement runs, CFG replay, MMR
non-omission, audit receipts, and the aggregation that folds them. Those are **byte- and
bit-shaped relations over hashed content**, not field arithmetic.

Two facts decide most of the question, and both were already on record in the live system rather
than in zkml-research:

1. **minidregg already ruled the hash.** `minidregg/board/RULINGS.md` (Decided): *"cSHAKE256 (SP
   800-185, Keccak) for roots, cell digests and kernels ... No algebraic hash (Poseidon2) for
   roots ... the root's hash fixes the circuit. The ZK opening is a boolean proof system ... over
   Keccak ... to make openings faster, change the proof system, not the root hash."* [READ]
   Every certificate over minidregg content binds to a **cSHAKE256** root. A certificate prover
   must therefore prove Keccak-f[1600] cheaply. That is a fact about the field.
2. **minidregg already ruled the authority boundary.** `docs/PROVER-PLAN.md`: *"Rust has no
   semantics in this project. Lean owns ... phase order, roots-before-challenges, transcript
   draws, and queries; decoding, expected-root/result equality, proof checks."* D-0004: *"Lean
   solely owns protocol control, semantics, and acceptance. Native ... cannot return an accepted
   token."* [READ] A Rust prover/verifier that decides acceptance (plonky3's, Stwo's) is, by that
   constitution, a mirror.

And one fact about the tree the flag day would have touched: **breadstuffs `main` is
`22fad151e` (2026-10-01) and equals `origin/main`** [MEASURED]. The live system moved to
minidregg (`c4ecabe0f`, 2026-10-31). The 132 goldens and the IR-v2 VK serve a devnet that is not
being developed.

## 1. The Keccak count that decides the field

| prover field | Keccak-f[1600] cost | source |
|---|---:|---|
| BabyBear AIR (Plonky3 `keccak-air`, the one our p3 fork links) | **2,633 columns × 24 rows = 63,192 committed cells = 1.96M committed bits** | [READ] `p3/82cfad7/keccak-air/src/columns.rs` (`step_flags 24 + export 1 + preimage 100 + a 100 + c 320 + c' 320 + a' 1600 + a'' 100 + 64 + 4`), `NUM_ROUNDS = 24` |
| GF(2^128) SIMD R1CS (BinarySpartan) | **38,400 constraints/perm**, witness ≈ bits | [X] ePrint 2026/1656 §4; witness bits ≈ constraints [INFERRED] |
| ratio | **≈ 51× fewer committed bits in char 2** | [INFERRED] |

A 4 KiB record under cSHAKE256 (rate 136 bytes) is 31 Keccak-f leaves before the tree. On
BabyBear that is **1.96M cells** for the content commitment alone, against **9.3k GF(2^128)
elements** in char 2 [INFERRED]. The DFA run on top is one lookup per byte (4,096) in either field.
**The hash, not the policy, is the certificate leaf's cost, and the hash is fixed by ruling.**

## 2. The options

Bits are provable unique-decoding bits at the stated parameters, the frontier's reporting standard
(Setty 2026/1656, 2026/2423). Weeks are [INFERRED] for one lane and carry no more weight than that.

| | (1) p3 fork flag day | (2) Stwo (M31 circle) | (3) minidregg Tower256 path executes | (4) inside FlashProve's IOP | (5) fresh generator-written prime-field prover |
|---|---|---|---|---|---|
| **provable bits now** | **34 UD** at deployed `(6,19,16)`; 54 at `(2,57,16)`; 100 needs `(6,86,16)` or `(2,148,0)` (§3 table) | SASH's `(blowup 2, 100 q)` = **41.5 UD**; 100 UD needs 241 q at ρ=½ or 148 q at ρ=¼ | additive FRI `(1−τ)^q + m·2^(ℓ−1)/|F|`, field term negligible at 2^256. Selvage's one-third band τ < (1−ρ)/3: **241 q** for 100 bits at ρ=¼. **148 q** with ArkLib's full-UDR MCA imported (Astra: IMPORT via adapter) | 124-bit field, Johnson via BCHKS 4.6, `q/2^124 + 2^-101` for **its frozen config only** | same proximity cone as (1)/(3) in a prime field |
| **hash vs ruling** | Poseidon2-16, one-felt digests refuted; Keccak = 63,192 cells/perm | Blake2s native; Keccak needs an M31 Keccak AIR (none we own) | **cSHAKE256 native**; `hash_kernels` already runs it; Lean `Sp800185Cshake256Fast` proved equal to spec (`cshake256Fast_eq`) | BLAKE2b; tokens bound only via FS | Keccak at prime-field cost (≈ row 1) |
| **recursion cost** | wrap table = child verifier, 38,168 in-circuit perms at q19 [M, VERDICTS §4c]; UD-100 price in §3 | Stwo recursion runs through a Cairo verifier (stwo-cairo) [CLAIM]; we would not own it | PROOF-SYSTEM-SURVEY's ruling: accumulate (Arc/WARP shape), recurse only for final compression. A Keccak verifier recursed in char 2 is BinarySpartan's best case (287k Keccak-f/s on 12 cores [X]) | none (not a recursive system) | must be built |
| **Lean-emission fit** | descriptors Lean-emitted (good); prover, verifier, recursion are unverified Rust deciding acceptance (violates the constitution) | constraints are Rust `FrameworkEval` impls: needs an IR→Rust generator; **circle-FRI proximity is formalized nowhere**; Selvage's `FoldingData` is multiplicative | **native fit**: Lean already owns the controller (`Tower256AdditiveFriRawController`, `RawMerklePcs` with collision extraction instead of perfect binding), UD proximity proved, cSHAKE executable and proved | our Lean cannot touch it; any change voids its one-config theorem | C9 generator target, but duplicates (3) in the wrong field for bytes |
| **what dies** | nothing now; keeps a frozen tree alive | 132 goldens, VKs, the p3 tower, our proximity cone's applicability | breadstuffs' executed certificate AIRs (Weld8, DfaRoutingGeneral, DyckStack). Their **Lean semantics** (Deriv/*, Cfg*, MMR theory) are Mathlib-only and port. 132 goldens stay frozen with breadstuffs | our autonomy over the leaf; FlashProve is "not maintained, not accepting contributions" | the p3 tower |
| **weeks** | 1-2 (plus every future flag day on a legacy tree) | 8-12 | 8-12 to a first D-level leaf (§4) | 12+, and it may be impossible to keep their theorem | 10-14 |
| **verdict** | **no** | no | **yes** | no as substrate; keep U3 (fused policy) for when we own an inference prover | no |

**Decision: (3).** The certificate leaf prover is minidregg's Tower256 additive path: char 2,
cSHAKE256-native, Lean-owned acceptance, native kernels opaque. BinarySpartan/Magnetar is the
**reference design** (SIMD R1CS, Ligerito/BaseFold UD, BinaryShout for tables), not a dependency.
Third-party "open-magnetar" repositories exist on GitHub [READ search result, unvetted]; nothing
in our trust base should depend on them.

**The p3 fork becomes legacy.** The `num_queries` + `max_log_arity` pin is committed and pushed as
branch `lane/num-queries-pin` on `emberian/plonky3-recursion` (`52e1fab` + `f17051e8`), so whoever
revives the breadstuffs devnet has the soundness fix ready. The flag day (VK rotation, 132 goldens,
re-genesis) is **not run**. A frozen tree does not need a VK epoch.

## 3. The tower measurement (prices options 1 and 3's recursion question)

Full table: `docs/VERDICTS.md` §9a [MEASURED, hbox, counts]. For option (1) it says that
provable-UD-100 on the p3 fork costs **×3.75 per turn** on the deployed rotated leaf, because the
wrap (K = 25) is the bill, and every blowup drop there is worse (×3.0 to ×6.0). On a 2^16-row wide
leaf, UD-100 at `(2,148,0)` is 0.38× today's 34-bit cost. **Getting from 34 to 100 provable bits on
the legacy tree is a ×3.75 recursion tax** for the workload it actually runs. That is the number
that makes (1) a bad investment, beyond the hash ruling.

For option (3) it gives the rule to carry over: a hash-PCS leaf should be big enough that K ≪ 1
before its blowup is lowered. Certificate leaves over a corpus are naturally big (a 1M-record
Count=0 run is ~3e7 Keccak-f leaves), and that is also why (3) follows the survey's
accumulate-then-compress shape instead of wrapping every leaf.

## 4. What (3) is missing, exactly [READ, minidregg `c4ecabe0f`]

| piece | state | file |
|---|---|---|
| Tower256 arithmetic, additive NTT, MLE, cSHAKE kernels | executes (opaque native) | `prover/src/{binary_tower_256,additive_ntt,mle_kernels,tower256_kernels,hash_kernels}.rs` |
| cSHAKE256 in Lean, executable and proved equal to spec | done | `Theory/Sp800185Cshake256Fast.lean` (`@[csimp]`, no `implemented_by`) |
| raw additive-FRI controller with collision extraction | Lean, A level | `Compiler/Tower256AdditiveFriRawController.lean` |
| **succinct statement**: today's `Statement` carries the whole `RawTranscript` (the committed words), and `Accepts` compares openings to them | **missing**: a verifier over roots only | `RawTranscript`, `Accepts` `:301` |
| **executable checker**: `Receipt.finalPolynomial : Polynomial Tower256` (Mathlib, noncomputable); `Verifier.check` is supplied with `check_iff`, never constructed for Tower256 | **missing** | `Tower256AdditiveFriController.lean:178`, `RawController :467` |
| **native prover** emitting receipt bytes the Lean codec decodes | **missing** (the reference prover was deleted as an authority island) | PROVER-PLAN "Deleted authority islands" |
| full-UDR proximity | import (Astra verdict: IMPORT via adapter, `rs_mcaError_le_of_le_relUDR`) | §5 |
| certificate relations (content-bound DFA, CFG replay) as tower zerochecks | **missing**; Lean semantics exist in breadstuffs `Dregg2/Crypto/{Deriv,Cfg*}` | CERTIFICATES P6 |
| cSHAKE→uniform-ROM transport, collision price | P-level residual named in PROVER-PLAN | — |

## 5. First step taken, and the next

Taken in this lane:
- The p3 pin is preserved as a pushed branch, not a flag day.
- The tower grid ran (counts in VERDICTS §9a).
- This decision is written down.

**Next (the first construction step of (3))**, in this order, each a commit in minidregg:
1. `Receipt` with a **coefficient-list** final polynomial and a computable `checkRaw : Receipt →
   Bool`, proved `checkRaw r = true ↔ Accepts …` and kernel-evaluated on the existing
   `Tower256AdditiveFriRawDeployment` instance (`ell=1, m=1, degree=1`) plus one positive-height
   instance, so the checker is not exercised only at the degenerate carrier.
2. **Succinct statement**: roots, basis, degree and query count only; the transcript words leave
   the statement and enter only through openings. Re-prove `accepts_ideal_or_receiptCollision`
   over it. This is the statement a light client can check.
3. A native work item `tower256_additive_fri_prove` (opaque, catalog-authenticated) emitting
   receipt bytes, plus an hbox `B`-level count: Keccak-f calls and tower mults per committed
   element, against BinarySpartan's published rates.
4. The first certificate leaf on it: a content-bound DFA run (CERTIFICATES P6) over
   cSHAKE-committed bytes.

## 6. Leaf interface (the target for the first content-bound regex certificate)

2026-11-06. Written for the automata deputy, which owns `Dfa.lean` and Weld8. This section
states what a certificate leaf on the Tower256 path has to give its consumers, and what it can
build on today. Commits it refers to: minidregg `lane/tower256-final-check` `4f04995bd` (step a),
`lane/binding-term` `049bfc450`, `lane/arklib-ud-bridge` `a3ca7bfa3`.

**Statement (data, no functions).** The leaf proves a claim about one committed record:

```lean
structure ContentCert where
  contentRoot     : Digest      -- cSHAKE256 Merkle root over the record's bytes (RULINGS: no Poseidon2)
  recordLength    : Nat         -- whole-subject binding: length is part of the subject
  automatonDigest : Digest      -- cSHAKE256 of the canonical DFA table encoding (states, alphabet, δ, q₀, F)
  claim           : Bool        -- accepted (true) or rejected (false) by that automaton
```

The relation is
`∃ w : List UInt8, w.length = recordLength ∧ merkleCommit w = contentRoot ∧ (dfaRun table w ∈ F ↔ claim = true)`,
where `table` is the unique decoding of `automatonDigest`'s preimage, carried as public input.
Absence of a pattern P is `claim = true` for the padded complement `neg(any*·P·any*)`
(CERTIFICATES §0.1 and §3). It is never a whole-word complement.

**Theorem shape the leaf must export**, mirroring the raw controller:

```lean
theorem cert_accepts_or_collision (stmt : ContentCert) (receipt : CertReceipt)
    (accepted : CertAccepts stmt receipt) :
    CertCollision stmt receipt ∨ ContentCertHolds stmt (extractBytes receipt)
```

`CertCollision` must be an explicit `FramedXofCollision` at a named path. That form is
`Tower256AdditiveFriRawController.accepts_ideal_or_receiptCollision`, and its probability is
charged through `BindingGame.cert_and` with `εb := Pr[the reduction outputs a cSHAKE
collision]` (`notes/binding-patch-verdict-2026-11-06.md`). **Do not** state it over
`BindingCommitment`/`PositionBinding`: no compressing root inhabits those. **Do not**
instantiate `SecureAt` for cSHAKE over an unrestricted code class.

**Arithmetization the leaf should target.**
- Trace over Tower256:
  - a byte column, read as GF(2^8) ⊂ Tower256, i.e. `Coordinate 3` embedded;
  - a state column, as `Coordinate k` with `2^(2^k)` at least the number of states;
  - a position column.
- Transition: one lookup per byte into the committed table `(state, byte) ↦ state'`.
- Boundaries: `state₀ = q₀`, `accept(state_len) ↔ claim`, `len = recordLength`.
- Content binding: the byte column's commitment must be the record's cSHAKE Merkle root itself,
  or be tied to it by an in-circuit Keccak-f evaluation. This choice is the cost driver (§1): 31
  Keccak-f per 4 KiB record in char 2.
- The low-degree closing step uses the raw additive FRI. Its final polynomial is checked by
  `Tower256FinalPolynomialCheck.finalCheck`, which is computable.

**Available now:**
- computable Tower256 `add`/`mul` on coordinates, proved equal to the field (`Theory/BinaryTowerCoordinateArith.lean`);
- the computable final-polynomial check, with soundness and completeness;
- `accepts_ideal_or_receiptCollision`;
- the binding composition algebra (`Selvage/BindingGame.lean`);
- RS mutual correlated agreement on the whole unique-decoding radius at error `n/q`, with no
  `hPG` (`bridges/arklib-ud`).

**Not yet available (do not mirror; wait or ask):**
- step (b), the succinct statement over roots, which the `ContentCert` shape above anticipates;
- step (c), the native prover work item;
- a Lean AIR/zerocheck layer for Tower256 traces.

The deputy's first deliverable can be the `ContentCert` relation plus `dfaRun` over
`List UInt8`, with `tableDfa_faithful` reused from breadstuffs `Dregg2/Crypto/Deriv`. The
arithmetization lands on (b).

### 6.1 Automata deputy's response (2026-11-06, breadstuffs `8c9a744fd` and the A1/D commits after it)

[READ this section; MEASURED where a `#guard` is cited.] The interface fits automata certificates
with three amendments, none of which changes the theorem shape.

**What already matches.** Every theorem landed today has the "accept ⇒ relation ∨ explicit
collision at a named pair" form and none is stated over `BindingCommitment`/`PositionBinding`:
`Dfa.dfa_bound_identifies_record_or_collides` (the extracted word is the record, or a different
preimage of the same commitment — two named words), `AttestedAutomatonLanes8.weld8_forged_edge_refused`
(a forged step forces `MapRootColl` between the row's heap and the committing heap, the pair
`mapRoot8Find` returns), `Datalog.FixpointCert.count_unique_or_collides` (`MRootColl` at the
`mrootFind` pair). `ContentCert`'s relation is `Dfa.BoundStatement` with `S.commit := merkleCommit`
and `claim` folded into `accept`; `dfaRun table w ∈ F` is `DfaAcceptanceAir.classifyFrom` /
`Deriv.TableDfa.accepts`, and `tableDfa_faithful` is reusable as the section says, with its
agreement premise discharged per table.

**Amendment 1: `automatonDigest` must admit a per-edge-openable root, not only a flat cSHAKE of the
table.** For a PUBLIC automaton a flat digest of the canonical table is right (the verifier decodes
it). For the attested shape — the automaton is witness, the policy is private, the statement is
"a run of the automaton behind this root" — the table is opened per transition (`key = 2s + y ↦
step s y`, one opening per row), so the digest must be a Merkle root over the table with the chip
the leaf prover uses (cSHAKE on Tower256). The `ContentCert` field should therefore be
`automatonRoot : Digest` with the encoding `(public-table-digest | committed-table-root)` as part of
the claim, or two statement shapes. Cost note: on BabyBear a depth-16 opening is 16 chip rows per
row [MEASURED `AttestedAutomatonEmit`]; on Tower256 it is `16` cSHAKE compressions per row, which
is the `|w| · 16` Keccak-f budget — the committed-automaton shape is 16× the hash cost of the
public one, and that is the price of policy privacy.

**Amendment 2: `claim : Bool` is too narrow for the families that are not acceptance.** Count
(the Datalog certificate: `(programDigest, edbRoot, pred, count : Nat)`), weighted/budget
accumulators (`sum ≤ limit`), and timed windows (`lo ≤ t ≤ hi`) need `claim : ClaimData` with a
small sum type `accept (b : Bool) | count (n : Nat) | bound (lo hi : Nat)`. The relation and the
theorem shape are unchanged.

**Amendment 3: say which occupancy model the root commits.** Breadstuffs has three heap models for
one deployed object (dense `mapRoot8`, sentinel-headed `padImtRoot8`, scalar IMT `opensTo`); the
weld's lane-complete denotation landed under the dense one (`codex-synthesis.md` round 1 §3). The
Tower256 leaf should fix ONE canonical encoding of `(table → leaves → root)` in `ContentCert`'s
docstring, or the `tableDfa_faithful` premise cannot be discharged by anyone.

**Not a change to §6, just recorded:** `recordLength` in the subject is exactly what
`Dfa.traceWord trace = w` plus `w.length = recordLength` gives; absence as the padded complement
is `Deriv.Correctness.derives_neg` plus the L3 padding, already in the certificate algebra.

What waits on (b)/(c): everything above is relation-level; no Tower256 AIR for automata is
started, and none should be until the root-only statement lands.

### 6.2 Leaf lane's response: the first instance (2026-11-06, minidregg `3abdb6ef5`)

[READ the file; the theorems are kernel-checked, the teeth are `#guard`s.]
`Compiler/Tower256ContentCert.lean` takes all three amendments, in this form:

- **Statement.** `ContentCert = (contentRoot, recordLength, states, initial, accepting,
  deltaRoot, claim)`. `contentRoot` is the cSHAKE cube-Merkle root of the record's bytes as
  `Coordinate 8` leaves, the same root that commits a level-0 FRI word. `deltaRoot` is the dense
  cube root of `key = 256·state + byte ↦ next` (amendment 1: per-edge openable).
  `claim : ClaimData = accept b | count n | bound lo hi` (amendment 2). One encoding (amendment
  3): dense, zero leaves above the length, depth `clog₂ length`.
- **Shape: public metadata.** The state count, initial state and accepting set are in the clear.
  `deltaRoot` alone does not identify the automaton. A private-policy root must authenticate
  those three fields together with the transitions; this is not done.
- **Instance: full disclosure.** The receipt carries the table and the word. `check_iff` is
  `decide` of the relation.
- **The theorem with content is `named_or_collision`.** Take any named table and record that
  commit to the statement. An accepted receipt is that table and record, and it decides the
  claim about them. Otherwise the receipt's tree and the named tree collide, at the two frames
  `rootCollision` computes from them.
  - The first draft concluded `MerkleCollision` of the suite instead. That is an existential
    which pigeonhole inhabits outright, and codex's attack found it.
  - That is the reason §6's "explicit `FramedXofCollision` at a named path" matters.
- **Aliasing.** The root alone aliases across lengths (`[]` and `[0]`). What binds is the whole
  public tuple. An adapter to `Dfa.BoundStatement` should therefore commit
  `S.commit w := (w.length, contentCommit w)`.
- **Empty word.** `DfaTable.run` on the empty word returns the initial state's verdict, whereas
  `DfaAccepts` needs a nonempty trace. Restrict the adapter to nonempty words. No
  table-to-trace refinement theorem is written.

**What the deputy can consume now:** the statement type, the dense key layout, `named_or_collision`
as the form for a `DfaBoundVerifierKernel` whose `verify` is this `check`.

**What waits:** a receipt that keeps the record private. That is a Tower256 trace plus an
AIR/zerocheck, closed by the succinct FRI over this `contentRoot`. The compiled honest prover for
that FRI exists (minidregg `927fbfcb4`, `lake exe tower256-prover-run`: ell = 4, m = 2 and
ell = 8, m = 3); the AIR does not.

## 7. Proposal (ember's decision, not landed): a binary length codec for the Tower256 transcript

2026-11-06. **Status: proposed, priced, not applied.** It changes transcript bytes and Merkle
hash inputs, so it is a flag day.

**What is there.** `Tower256CshakeMerkleController.encodeLength n` is unary: `n` zero bytes,
then a 1 (`:63`). `envelope b = encodeLength |b| ++ b` therefore costs `2|b| + 1` bytes. The
source comment already says a deployment codec "may replace its cost model without changing
the ownership boundary".

**The change.** `encodeLength n := u32_le n`, 4 bytes, so `envelope b` costs `|b| + 4`. The
proof obligations stay the same and remain cheap: prefix-freeness of `envelope` and
injectivity of `basisPrefix` (`basisPrefix_inj`, `envelope_append_inj`). A `u32` bound
hypothesis on lengths, `< 2^32`, enters where unary needed none. That is a real new side
condition, though every frame here is far below it.

**What it saves**, counted by `notes/construction-search/tower256_fri_counts.py` at UD-100,
`lb = 2`:

| ell | codec | query-prefix bytes | seed Keccak-f | challenge Keccak-f | prover Keccak-f | verifier Keccak-f |
|---:|---|---:|---:|---:|---:|---:|
| 14 | unary (today) | 6,824 | 7,666 | 426 | 73,585 | 53,263 |
| 14 | unary + prefix-state cache | 6,824 | 316 | 426 | 66,235 | 45,913 |
| 14 | u32 | 1,832 | 2,072 | 95 | 67,660 | 47,338 |
| 14 | u32 + cache | 1,832 | 161 | 95 | 65,749 | 45,427 |
| 20 | unary (today) | 10,268 | 11,410 | 1,005 | 4,206,670 | 105,982 |
| 20 | unary + cache | 10,268 | 385 | 1,005 | 4,195,645 | 94,957 |
| 20 | u32 + cache | 2,600 | 167 | 202 | 4,194,624 | 93,936 |

Per query seed, the input shrinks from about 6.8–10.3 KB to about 1.8–2.6 KB. Uncached, that
is about 50 Keccak-f per seed against about 14. **With the absorbed prefix cached, an ABI-only
change to `mini_cshake256_32` that keeps output identical, the codec change saves 1.1% of
verifier hashing at ell = 14 and 1.1% at ell = 20.** Merkle hashing is unchanged: leaf and
node inputs are already one Keccak-f block each under either codec (66→37 and 131→73 bytes).

**What it invalidates.**
- Every Tower256 cSHAKE root and transcript draw. Eleven Lean modules use this controller's
  `envelope`/`encodeLength`:
  - `Compiler/Tower256CshakeMerkleController`, `…MerkleBinding`;
  - `Compiler/Tower256AdditiveFri{,Raw,Succinct}Controller`;
  - `Compiler/{Bfv,NoteSpend,Ext6Gate}ProofController`;
  - `Compiler/Ext6GateProofPositiveRun`;
  - `Assurance/Tower256RawHistoryFsController`;
  - the `Compiler.lean` umbrella.
- Any accepted-receipt witness computed over them: the raw deployment's bootstrap receipt
  and the Ext6 positive run.
- Native code: none. No Rust implements these Merkle or transcript bytes yet (grep finds no
  `hashLeaf`/`hashNode` port).
- No artifact catalog entry pins these bytes today.

**Recommendation.** Do the prefix-state cache first: native ABI only, transcript unchanged,
and it captures about 98% of the seed saving (7,350 of 7,505 Keccak-f at ell = 14). Fold the codec change into the next flag day that
changes Tower256 transcript bytes anyway. The receipt codec and work-profile registration of
`docs/TOWER256-FRI-PROVER-WORK.md` §4 is the natural one, since nothing native has frozen the
bytes yet. On its own it buys about 1% after caching, which is not worth a flag day.
