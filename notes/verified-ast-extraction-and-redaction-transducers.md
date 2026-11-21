# Verified Unambiguous LL(1) AST Extraction and Deterministic Secret-Redaction Byte Transducers

**Date:** 2026-11-21
**Status:** Kernel-verified in Lean 4.35.0 (`0 sorry`, `0` custom axioms, `0 native_decide`, `0 #guard`, `20` `#guard_msgs`-pinned `#print axioms` checks) and executed in Rust (`--release`, bit-exact conformance on Lean-authored JSON vectors + multi-KB throughput benchmarks).

## 1. Executive Summary & Architectural Verdict

Boolean formal-language gating (`w ∈ L(G)` in [CfgCompact.lean](file:///Users/ember/dev/breadstuffs/metatheory/Dregg2/Crypto/CfgCompact.lean#L97-L115)) and pure substring rejection (`AbsentPlain` in [ContentCertificate.lean](file:///Users/ember/dev/minidregg/Selvage/ContentCertificate.lean#L211-L246)) leave two concrete production failure modes when gating LLM agent tool calls and chain-of-thought (CoT) transcripts:

1. **Ambiguous Parse-Tree Splice (`[REFUTED: boolean CFG membership or non-LL(1) pushdown replay as sufficient for tool-call AST authorization]`):** Knowing `w ∈ L(G)`—or replaying a prover-chosen leftmost rule sequence `rs` without grammar-level determinacy—does not bind the *extracted command AST*. In [VerifiedAstTransducer.lean](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L1257-L1269), `ambigMiniJsonCfg_splice_attack` exhibits a single 73-byte duplicate-key JSON payload `{"tool":"read_status","tool":"wipe_prod","target":"db_main","amount":1}` in `L(G)` admitting two valid pushdown certificates that synthesize distinct `MiniValue` tool ASTs (`"read_status"` vs `"wipe_prod"`).
2. **Whole-Transcript Rejection vs Canonical Sanitization:** Rejecting any raw transcript containing a secret aborts benign agent turns whenever CoT reasoning quotes an environment variable or API token before invoking a safe tool. What a production policy gate requires is a **deterministic byte-stream redaction transducer** (`w_clean = redactBytes rules w_raw`) that provably scrubs all target secret prefixes into `Regex.paddedComplement`, preserves clean code/prose byte-for-byte (`w_clean = w_raw`), and feeds `w_clean` into an **LL(1)-certified AST extractor** under `cSHAKE256` content commitments.

We close both gaps end-to-end across `Theory/`, `Compiler/`, and `prover/`:

| Artifact | Tier / Role | Core Verified / Executed Deliverable |
|---|---|---|
| [VerifiedAstTransducer.lean](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L1-L1970) | `Theory/` (`Mathlib.*` only) | `AttrCfg`, `AttrReplay`, `execAttrReplay_iff`, `ll1Deterministic`, `attrReplay_unique_of_ll1`, 139-rule `miniJsonCfg` (`ll1Deterministic = true`), `ambigMiniJsonCfg_splice_attack`, `redactBytes`, `SafeReplacement`, `redactBytes_deterministic`, `redactBytes_scrubs_all`, `redactBytes_preserves_clean`, `redactBytes_idempotent`, `redactBytes_unsafe_repl_falsifier` (`[DERIVED]`, `[EXECUTED]`) |
| [PolicyAstTransducerEmit.lean](file:///Users/ember/dev/minidregg/Compiler/PolicyAstTransducerEmit.lean#L1-L507) | `Compiler/` (`Selvage` + `Tower256ContentCert`) | `absentW_iff_padded_complement`, `redactBytes_scrubs_padded_complement`, `verifyRewriteAndExtract`, `verifyRewriteAndExtract_complete`, `rewrite_and_extract_sound_or_collision` over SP 800-185 `cSHAKE256` (`contentCommit`), soundness teeth, and `#eval` emission of [policy_transducer_conformance.json](file:///Users/ember/dev/minidregg/prover/testdata/policy_transducer_conformance.json) (`10,163` B) (`[DERIVED]`, `[EXECUTED]`) |
| [policy_transducer.rs](file:///Users/ember/dev/minidregg/prover/src/policy_transducer.rs#L1-L1970) | Rust native prover/verifier | `content_commit` (256-leaf + zero-subtree cached `cSHAKE256` cube-Merkle), `CompiledByteLl1Parser` (`O(1)` 257-slot dispatch + zero-clone in-place value stack + unbounded `ExactNat`), `CompiledRedactor` + `O(N)` `StreamingRedactor`, `prove_mini_rewrite_and_extract`, `verify_rewrite_and_extract` (`[EXECUTED]`) |
| [policy_transducer_conformance.rs](file:///Users/ember/dev/minidregg/prover/tests/policy_transducer_conformance.rs#L1-L710) | Rust conformance & bench | Bit-exact Lean JSON conformance (roots, rule indices, ASTs, splice vectors), 6 adversarial forgery/overflow/alias teeth, 1-byte through 128-byte chunk-split streaming stress, and `4 KiB`–`256 KiB` `--release` throughput benchmarks (`[EXECUTED]`) |
| [build_and_verify.sh](file:///Users/ember/dev/zkml-research/research/real_systems_wave_2026_11_21/formal_transducer/build_and_verify.sh#L1-L231) | Reproducible verifier | Overlay Lean 4.35.0 kernel check + import-boundary enforcement + `--release` Rust conformance & benchmark suite (`[EXECUTED]`) |

---

## 2. Verified Unambiguous LL(1) Parse-to-AST Extraction

### 2.1 S-Attributed Pushdown Replay & Compute-Then-Certify LL(1) Uniqueness

In [VerifiedAstTransducer.lean](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L45-L169), `AttrCfg T NT SemOp Val` pairs a context-free rule list (`lhs → rhs`, semantic operator `op : SemOp`) with terminal interpretation `termVal : T → Val` and bottom-up operator evaluation `evalOp : SemOp → List Val → Val`. The inductive relation `AttrStackReplay` ([lines 112–137](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L112-L137)) interleaves symbol matching/expansion with explicit deferred `.reduce op k` stack frames:
- **CFG Language Tie-Back (`[DERIVED]`):** `attrReplay_mem_language` ([lines 164–169](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L164-L169)) proves every accepted `AttrReplay g rs w ast` witnesses `w ∈ g.toCfg.language` in Mathlib's `ContextFreeGrammar` ([SOURCE: Mathlib.Computability.ContextFreeGrammar]).
- **Executable Equivalence (`[DERIVED]`):** `execAttrReplay` ([lines 173–215](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L173-L215)) is written via structural recursion (`execNoRules` + `execStepUntilRule`) without `WellFounded.fix`, avoiding `Acc.rec` proof-term blowup during kernel `by decide`. `execAttrReplay_iff` ([lines 350–355](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L350-L355)) proves `execAttrReplay g rs w = some ast ↔ AttrReplay g rs w ast`.
- **LL(1) Determinacy & Uniqueness (`[DERIVED]`):** `ll1Deterministic : AttrCfg T NT SemOp Val → Bool` ([lines 572–575](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L572-L575)) computes `(nullNTs, firstTab, followTab)` via strict early-stopping fixed-point passes (`computeLl1Tables`, [lines 488–535](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L488-L535)) and certifies inductive closure (`none ∈ FOLLOW(initial)`, `NULLABLE`, `FIRST`, and `FOLLOW` suffix closure) plus pairwise disjointness of `rulePredict(r) = FIRST(rhs) ∪ (if NULLABLE(rhs) then FOLLOW(lhs) else ∅)` across same-LHS rules (`checkLl1Tables`, [lines 560–569](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L560-L569)). Theorem `attrReplay_unique_of_ll1` ([lines 832–856](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L832-L856)) proves via the stack invariant `FollowSafe` ([lines 605–664](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L605-L664)) that for any `g` with `ll1Deterministic g = true`:
  $$\mathrm{AttrReplay}\;g\;rs_1\;w\;ast_1 \;\wedge\; \mathrm{AttrReplay}\;g\;rs_2\;w\;ast_2 \;\Longrightarrow\; ast_1 = ast_2 \;\wedge\; rs_1 = rs_2.$$

### 2.2 Production `Mini` JSON Tool-Call Grammar vs Duplicate-Key Splice Attack

- **Canonical `miniJsonCfg` (`[DERIVED]`, `[EXECUTED]`):** Defined over raw `UInt8` bytes with 13 nonterminals and 139 rules ([lines 1005–1055](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L1005-L1055)), supporting arbitrary RFC 8259 whitespace, JSON string escape decoding (`\"`, `\\`, `\/`, `\n`, `\r`, `\t`), canonical non-leading-zero arbitrary-precision decimal naturals (`0 | [1-9][0-9]*`), left-factored single tool frames `{"tool":"...","target":"...","amount":N}`, CoT+tool frames `{"cot":"...","tool":"...","target":"...","amount":N}`, and recursive batch arrays `[...]`. Kernel `by decide` theorems prove `miniJsonCfg_is_ll1` ([line 1058](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L1058)), `miniJsonCfg_extracts_escaped_tool` ([lines 1072–1075](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L1072-L1075)), `miniJsonCfg_extracts_batch` ([lines 1097–1100](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L1097-L1100)), and leading-zero rejection `miniJsonCfg_rejects_leading_zero` ([lines 1106–1107](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L1106-L1107)).
- **Constructive Ambiguous Splice Attack (`[DERIVED]`, `[EXECUTED]`):** `ambigMiniJsonCfg` ([lines 1196–1218](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L1196-L1218)) models lax RFC 8259 duplicate-key JSON objects (`firstWins` vs `lastWins` on duplicate `"tool"` keys). Theorem `ambigMiniJsonCfg_splice_attack` ([lines 1257–1269](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L1257-L1269)) kernel-proves `ll1Deterministic ambigMiniJsonCfg = false`, exhibits `ambigBenignCert` (`"read_status"`) and `ambigDestructiveCert` (`"wipe_prod"`) replaying on identical `ambigSplicePayload`, proves `ambigBenignAst ≠ ambigDestructiveAst`, and confirms `ll1Parse miniJsonCfg ambigSplicePayload = none`.

---

## 3. Deterministic Secret-Redaction Transducer & `cSHAKE256` `RewriteCert`

### 3.1 Multi-Pattern Longest-Match Byte Sanitizer & Boundary Algebra

In [VerifiedAstTransducer.lean](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L1461-L1647), each `RedactRule Sym` specifies `(name, pat, bodyPred, repl)`: a non-empty trigger prefix `pat` followed by a greedy continuation predicate `bodyPred : Sym → Bool` (`ruleMatchLen`). At each cursor offset, `pickLongestMatch` selects the longest matching rule (breaking ties by first-listed priority) and advances by `len ≥ 1`, emitting `repl`.

To prevent replacement boundaries from synthesizing a forbidden pattern (e.g., deleting `"ab"` inside `"aabb"` leaves `"ab"`), `SafeReplacement P repl` ([lines 1316–1324](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L1316-L1324)) checks `repl ≠ []`, `AbsentW repl P`, and for every split `P = p₁ ++ p₂` (`0 < |p₁| < |P|`), `¬(p₂ <+: repl) ∧ ¬(repl <+: p₂) ∧ ¬(p₁ <:+ repl)`:
- **Splitting & Scrubbing (`[DERIVED]`):** `absentW_append_repl` ([lines 1351–1458](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L1351-L1458)) proves `AbsentW u P → AbsentW v P → AbsentW (u ++ repl ++ v) P`. `redactBytes_scrubs_all` ([lines 1811–1818](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L1811-L1818)) proves that under `allRulesSafe rules = true`, every `rt.pat` (`rt ∈ rules`) is universally absent from `redactBytes rules w`.
- **Determinism, Clean Preservation, Idempotence & Falsifier (`[DERIVED]`, `[EXECUTED]`):** `redactBytes_deterministic` ([lines 1714–1734](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L1714-L1734), pure `[propext]`), `redactBytes_preserves_clean` ([lines 1821–1864](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L1821-L1864)), `redactBytes_idempotent` ([lines 1878–1883](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L1878-L1883)), `defaultSecretRules_allSafe` (`sk-`, `Bearer `, `-----BEGIN `, `{{`, `ghp_`, [line 1908](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L1908)), and falsifier tooth `redactBytes_unsafe_repl_falsifier` ([lines 1934–1939](file:///Users/ember/dev/minidregg/Theory/VerifiedAstTransducer.lean#L1934-L1939)).
- **Scope Note on Greedy Continuation (`[DERIVED]`):** `redactBytes_scrubs_all` guarantees absence of every trigger prefix `rt.pat` (`AbsentPlain _ rt.pat`). If two distinct secret tokens are concatenated without any delimiter so an earlier rule's `bodyPred` consumes the trigger prefix of the second (e.g. `"sk-Bearer eyJ..."` where `isApiKeyBodyByte` consumes `"Bearer"` and stops at `' '`), `"sk-"` and `"Bearer "` are both scrubbed, leaving `" eyJ..."`. Requiring disjoint delimiter characters or including whitespace-free token prefixes in `rules` closes body-tail spillover (`[OPEN]` for entropy-based secret detectors).

### 3.2 `Selvage` Padded-Complement & `Tower256` `cSHAKE256` `RewriteCert` Bridge

In [PolicyAstTransducerEmit.lean](file:///Users/ember/dev/minidregg/Compiler/PolicyAstTransducerEmit.lean#L59-L226):
- **Regex Padded-Complement Bridge (`[DERIVED]`):** `redactBytes_scrubs_padded_complement` ([lines 75–86](file:///Users/ember/dev/minidregg/Compiler/PolicyAstTransducerEmit.lean#L75-L86)) bridges `AbsentW` directly to `Selvage.AbsentPlain`, `MatchesRegex _ (Regex.paddedComplement (Regex.literal rt.pat))`, and `Regex.derives _ (Regex.paddedComplement _) = true`.
- **Closing the Dense-Column Trailing-Zero Root Alias (`[DERIVED]`, `[EXECUTED]`):** `Tower256ContentCert.contentCommit` ([SOURCE: Compiler/Tower256ContentCert.lean:607-623]) pads payloads of length `n` to `2^(Nat.clog 2 n)` zero leaves, so `"xab"` (`len = 3, depth = 2`) and `"xab\0"` (`len = 4, depth = 2`) share an identical 32-byte `cSHAKE256` root (verified at `#eval` in [PolicyAstTransducerEmit.lean](file:///Users/ember/dev/minidregg/Compiler/PolicyAstTransducerEmit.lean#L480) and Rust Tooth D in [policy_transducer_conformance.rs](file:///Users/ember/dev/minidregg/prover/tests/policy_transducer_conformance.rs#L384-L400)). `RewriteCertStmt` ([lines 100–106](file:///Users/ember/dev/minidregg/Compiler/PolicyAstTransducerEmit.lean#L100-L106)) binds both `(rawLength, rawRoot)` and `(cleanLength, cleanRoot)` alongside `claimedAst`.
- **Capstone Theorem `rewrite_and_extract_sound_or_collision` (`[DERIVED]`):** Proved at [lines 186–225](file:///Users/ember/dev/minidregg/Compiler/PolicyAstTransducerEmit.lean#L186-L225). Whenever `verifyRewriteAndExtract g rules stmt wit = true`, for *any* raw/clean byte records `(wRaw, wClean)` matching `stmt`'s `(length, contentCommit)` pairs, **either**:
  1. `wClean = redactBytes rules wRaw` and `RedactsTo rules wRaw wClean`,
  2. every `rt ∈ rules` satisfies `AbsentPlain wClean rt.pat` and `MatchesRegex wClean (Regex.paddedComplement (Regex.literal rt.pat))`,
  3. clean inputs satisfy `(∀ r ∈ rules, AbsentPlain wRaw r.pat) → wClean = wRaw`,
  4. `AttrReplay g wit.ruleSeq wClean stmt.claimedAst` and `wClean ∈ g.toCfg.language`, and
  5. **Unique AST & Parse:** `∀ rs' ast', AttrReplay g rs' wClean ast' → ast' = stmt.claimedAst ∧ rs' = wit.ruleSeq`,
  **or** an explicit SP 800-185 `cSHAKE256` `DenseCollision` (`FramedXofCollision cshakeC`) is constructively extracted.

---

## 4. Adversarial Audit Hardening & `[EXECUTED]` Benchmarks

An adversarial helper audit (`transducer-neon-audit`) reviewed both Lean modules and the Rust engine prior to final verification:
1. **Lean Soundness & Non-Vacuity (`[EXECUTED]`):** Confirmed all 20 `#guard_msgs`-pinned `#print axioms` checks use only standard Lean axioms (`[propext, Classical.choice, Quot.sound]`; `[propext]` on `redactBytes_deterministic`), zero `sorry`/`axiom`/`native_decide`/`#guard`, and inhabited premises across `e2eVec1_verified`–`e2eVec3_verified`.
2. **Rust Hardening Applied (`[EXECUTED]`):** (a) Replaced fixed-width `u64` AST naturals with canonical base-$10^9$ `ExactNat` ([policy_transducer.rs](file:///Users/ember/dev/minidregg/prover/src/policy_transducer.rs#L820-L914)) so JSON integers $\ge 2^{64}$ match Lean `Nat` identically without overflow or $\bmod\;2^{64}$ wraparound (tested at $2^{64}$ in Tooth E, [policy_transducer_conformance.rs](file:///Users/ember/dev/minidregg/prover/tests/policy_transducer_conformance.rs#L402-L434)); (b) auto-computed `(0u8..=255).any(body_pred)` inside `CompiledRedactor::new` so callers cannot misconfigure continuation flags; (c) upgraded `StreamingRedactor` with `StreamRuleState::Growing { scanned_len }` ([lines 1698–1860](file:///Users/ember/dev/minidregg/prover/src/policy_transducer.rs#L1698-L1860)) for $O(N)$ incremental continuation scanning across 1-byte chunks; and (d) added zero-clone in-place reverse-accumulator stack reductions (`eval_mini_op_in_place`, [lines 1084–1255](file:///Users/ember/dev/minidregg/prover/src/policy_transducer.rs#L1084-L1255)) for linear-time batch/string AST synthesis.

### 4.1 Reproducible Verification & `--release` Throughput (`[EXECUTED]`)

Command:
```sh
bash /Users/ember/dev/zkml-research/research/real_systems_wave_2026_11_21/formal_transducer/build_and_verify.sh
```
- **Lean 4.35.0 Kernel Output (`[EXECUTED]`):** `scripts/check-import-boundary.sh` passed; `Theory.VerifiedAstTransducer` verified in `40.02s` (`rc=0`, `0` warnings, `12` axiom pins); `Compiler.PolicyAstTransducerEmit` verified in `30.61s` (`rc=0`, `0` warnings, `8` axiom pins), emitting `policy_transducer_conformance.json` (`10,163` B).
- **Rust `--release` Conformance & Multi-KB Throughput (`[EXECUTED]`, `4 passed; 0 failed` in `18.22s`, plus `sumcheck_conformance` `5 passed; 0 failed`):**

| Transcript Workload | Raw / Clean Bytes | Replay Rules | Batch `redact` | `64 B` `StreamingRedactor` | Compiled `ll1_ast` (`cert`) | Pushdown `replay` | Full `2× cSHAKE256` `RewriteCert` (prove+verify) |
|---|---:|---:|---:|---:|---:|---:|---:|
| `4 KiB` dirty (CoT secrets + JSON batch) | `3,908` / `3,363` B | `3,157` | `532.0 MB/s` | `360.7 MB/s` | `34.8 MB/s` (`33.8 MB/s`) | `40.8 MB/s` | `14.26 ms` (`0.27 MB/s`) |
| `16 KiB` dirty (CoT secrets + JSON batch) | `16,306` / `14,022` B | `13,158` | `483.4 MB/s` | `365.9 MB/s` | `31.6 MB/s` (`29.5 MB/s`) | `38.6 MB/s` | `64.16 ms` (`0.25 MB/s`) |
| `64 KiB` dirty (CoT secrets + JSON batch) | `65,466` / `56,228` B | `52,788` | `300.9 MB/s` | `257.9 MB/s` | `23.8 MB/s` (`21.4 MB/s`) | `33.0 MB/s` | `305.75 ms` (`0.21 MB/s`) |
| `64 KiB` clean (zero-mangling check) | `65,325` / `65,325` B | `61,339` | `482.0 MB/s` | `372.1 MB/s` | `31.0 MB/s` (`33.7 MB/s`) | `41.0 MB/s` | `259.84 ms` (`0.25 MB/s`) |
| `256 KiB` dirty (CoT secrets + JSON batch) | `262,083` / `225,067` B | `211,393` | `435.6 MB/s` | `372.9 MB/s` | `25.9 MB/s` (`23.8 MB/s`) | `34.9 MB/s` | `1093.30 ms` (`0.24 MB/s`) |

*(Note: Full `RewriteCert` prove+verify hashes $4\times$ `cSHAKE256` cube-Merkle trees—prover + verifier on `w_raw` and `w_clean`—over pure scalar Rust Keccak-f[1600]; the redaction + LL(1) AST extraction + replay pipeline itself runs at `24–532 MB/s`, i.e., `< 0.2 ms` on a `4 KiB` agent turn.)*

---

## 5. Metered Search Ledger & Proposed Maintainer Folds

- **Metered Search Queries:** `0` `scry.py` queries, `0` `kagi.py` queries, `0` `eprint.iacr.org` fetches (all constructions derived directly from local `minidregg` and `breadstuffs` companions).
- **Proposed Maintainer Folds (unmodified per ownership rules):**
  1. `minidregg/Theory.lean`: add `import Theory.VerifiedAstTransducer`.
  2. `minidregg/Compiler.lean`: add `import Compiler.PolicyAstTransducerEmit`.
  3. `zkml-research/docs/VERDICTS.md`: fold `attrReplay_unique_of_ll1` + `rewrite_and_extract_sound_or_collision` under the content-certificate / formal-language gating lane, recording that boolean CFG membership is superseded by LL(1)-certified AST extraction composed with `SafeReplacement` byte-stream sanitization.
