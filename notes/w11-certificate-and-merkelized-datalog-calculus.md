# Wave 11 Lane 4 · Certificate composition over a Merkelized Datalog EDB

[DERIVED] For a finite ground stratified program and a sorted EDB with boundary sentinels, a signed literal holds exactly when it has an accepted certificate whose openings agree with the committed leaves. The forward construction works for any hash. In the reverse direction, acceptance of a false literal on a sorted tree identifies a submitted claim with a mismatched opening and entails a hash collision. This formulation applies to fixed-width digests. A separate verifier checks the DFA run, canonical tokens and Datalog authorization for one opened turn.

[EXECUTED] The Lean kernel checked the literal Rust-generated certificate and the signed model answer for **each of the 51 toy atoms**. The two checkers agreed on all 58 fixture verdicts, including the malformed openings. The computed root is **839753907**. The reproduction command and measured SHA3 workload appear below.

## Certificate rules and proof boundaries

[SOURCE] Lean references below are theorem statements and proofs in `minidregg/Assurance/CertificateAndDatalogCalculus.lean`. Rust references are implementations in `minidregg/prover/src/datalog_and_cert_calculus.rs`. Test references are assertions in `minidregg/prover/tests/cert_and_datalog_calculus.rs`. The fixture is `minidregg/prover/testdata/cert_datalog_conformance.json`, under `toy`.

| Rule | What the checker establishes | Evidence |
|---|---|---|
| Membership | A positive EDB atom opens its **encoded key and salt** at an in-range position. The top-down sibling list has exactly the committed depth. | [SOURCE] Lean:390 `checkClaim`, Lean:338 `merkle_position_binding`, Rust:905 `recompute_root`, Rust:1113 `verify_cert`. |
| Rule | The positive IDB head equals the instantiated rule head. Every positive and negative body literal has a claim of the required sign and **strictly smaller** rank. Min-rank lookup in Rust implements Lean’s existential lookup, independent of certificate order. | [SOURCE] Lean:390 `checkClaim`, Lean:412 `hasLit_iff`, Rust:1113 `verify_cert`. |
| Gap | A negative EDB claim opens positions **i and i+1**, both at exact depth, against one root. Their keys strictly bracket the query key. Either endpoint can be a sentinel. Global sortedness lets these two local openings establish absence. | [SOURCE] Lean:439 `claims_sound`, Rust:957 `from_leaves`, tests:385 `toy_tamper_falsifiers`. |
| Unfounded set | A negative IDB claim belongs to an all-IDB set U. For **every** rule instance headed in U, some positive body atom belongs to U or has a lower-ranked negative claim, or some negative body atom has a lower-ranked positive claim. The proof descends in a finite positive derivation inside U. A head with no defining instance is legitimately false. | [SOURCE] Lean:390 `checkClaim`, Lean:439 `claims_sound`, Rust:378 `match_head`, Rust:1218 blocker test, tests:470 `unf_checks_every_matching_head_instance`. |

[DERIVED] The verifier checks every supplied claim and requires the signed query to occur. An authenticated pair of nonconsecutive leaves cannot establish absence. A root alone also gives no certificate of global ordering. Rust’s checked builder establishes the order at construction. A verifier receiving an external root relies on the authority that supplied the EDB commitment. Lean exposes an ordering violation as a separate soundness outcome.

[SOURCE] Lean completeness uses the query and the ground rules’ heads and bodies, least positive derivation depths, lower strata for negation, and classical choice of rule and opening witnesses. Endpoints and strictly interior atom encodings suffice to construct honest gaps. Sortedness enters the sound direction. Rust uses first provenance, stratum-local rounds, and a query-directed certificate. Different ranks and claim orders can satisfy the identical strict dependency test. Its toy rank width is 4, as recorded in `toy.rankWidth`. Lean’s `width` belongs to its own canonical construction. See Lean:539 `derivN_mono`, Lean:667 `genClaim_check`, Lean:774 `datalog_cert_complete`, Rust:713 `solve` and Rust:1388 `generate_cert`.

[DERIVED] For a SHA3 instantiation of the bounded-key theorem, take the ordered key domain between the two sentinels, inclusive. Unrestricted byte vectors have elements above `ff`. The policy’s valid atoms have encodable predicate IDs and fixed arities, so their keys are interior and the encoding is injective. The generic Lean semantics defines EDB membership by encoded-key equality. An alternative encoding that aliases two atoms would give those atoms shared membership. The concrete SHA3 verifier bounds gap endpoints and the checked builder bounds every fact key. See Lean:793 `datalog_cert_sound_and_complete`, Rust:851 `Sha3Hasher`, Rust:957 `from_leaves` and Rust:1113 `verify_cert`.

[SOURCE] For Rust variables, head matching enumerates all relevant ground instances when every body variable occurs in the head. Constants and repeated variables constrain matches. Several defining rules can match one atom. A predicate with any non-head-covering defining rule causes `Unf` to reject before enumeration. The policy’s group join in `can` and recursive delegation in `trusted` have body-only variables. Positive instances still carry explicit substitutions. The generator uses the solver’s first positive derivation and can fail when a required negative subcertificate is unavailable. See Rust:268 `Program::new`, Rust:1113 `verify_cert`, Rust:1307 `neg_inner`, and tests:718 `policy_sha3_certs_and_falsifiers`.

## Composition and premise audit

- [SOURCE] `Judg` quantifies over the commitment and certificate before sampling uniform coins from a finite **nonempty** space. It bounds acceptance with a bad extracted witness outside the stated collision event. `cert_conj_shared_commit` uses a union bound, so the sub-verifiers may share coins. Two distinct extracted witnesses opening the same commitment give the two explicit preimages in `CollisionWitness`. `exact_opening_judg` supplies an inhabited zero-error premise. See Lean:42, 57, 66 and 131.
- [SOURCE] `cert_transducer_pushforward` preserves the budget for a deterministic function and a proved relation implication. The committed object remains the input witness. `det_run_pushforward` gives the corresponding unique-run rule. `nondet_transducer_pushforward_fails` and `independent_commits_allow_split_witness` exhibit the failure of their respective relaxed rules. `cert_implication_weaken` and `cert_union_or` cover implication and a fixed tagged branch. See Lean:85, 93, 99, 105, 114 and 137.
- [SOURCE] `audit_miss_prob`, `audit_miss_le` and `cert_sampled_audit` use a fixed opening and k independent uniform draws **with replacement** from N positions. With D defective positions the exact miss probability is `((N−D)/N)^k`. A defect fraction at least δ gives the upper bound `(1−δ)^k` for meaningful fractions in [0,1]. The audit checks the extracted word’s commitment. `audit_two_draws` evaluates the one-defect, four-position, two-draw case to 9/16. See Lean:148, 158, 175 and 212.
- [SOURCE] `cert_bpe_byte_weld` transfers DFA acceptance to the bytes denoted by canonical tokens using `decode (encode w) = w`. `cert_opened_byte_turn` checks one salted opening, its DFA acceptance, its canonical tokens, the policy query read from that word and a positive Datalog certificate at the policy EDB root. The deterministic judgment has error budget zero outside the named opening-collision and ordering exceptions. See Lean:198 and 510.
- [SOURCE] The model theorems are `SM_fix`, `SM_isStratModel`, `stratModel_unique` and `stratModel_least`. Leastness is relative to closures reading negative literals from the stratified model. `unstratified_negation_no_model` handles the self-negation falsifier. `mkPath_length`, `recompute_mkPath`, `merkle_position_binding`, `checked_opening_or_collision` and `claims_sound` connect honest paths and mismatches to model truth. See Lean:252, 260, 263, 273, 281, 321, 326, 338, 427 and 439.
- [SOURCE] The signed keystones are `datalog_cert_sound`, `genClaim_check`, `genClaim_faithful`, `datalog_cert_complete` and `datalog_cert_sound_and_complete`. `toy_sorted` and `toy_signed_iff` instantiate the actual sortedness, endpoint and interior-key premises over `Fin 51`. `toy_root`, `toy_accepts`, `toy_cyclic_rejected` and `toy_nonadjacent_gap_falsifier` pin positive witnesses and failures. See Lean:491, 667, 768, 774, 793, 836, 841, 847, 869, 876 and 896.

[REFUTED: original turn authorization interpretation] The previous honest-turn fixture used bytes naming user 42 with valid authorization for user 5. Equal byte-root labels and a recomputed transcript establish neither identity equality nor a byte-to-query relation by themselves. The verifier now runs the context’s deterministic request parser and requires the resulting pair to equal the pair in `allowed(user,tool)`. The demo parser accepts canonical unsigned decimal fields in `user <id> calls tool <id>: ` and leaves the remainder as payload. An authenticated session principal, request freshness and a particular caller-expected turn are application inputs beyond this judgment. See Rust:1883 `TurnContext`, Rust:1911 `text_request_ids`, Rust:1993 `verify_composed_turn`, tests:952 `composed_turn_accepts_honest`.

[SOURCE] Rust recomputes the salted byte digest, compares all three subcertificate roots, checks each DFA transition, checks BPE decoding and canonical re-encoding, and verifies the positive policy query at the context’s EDB root **and depth**. The public transcript digest covers the byte root, EDB root and depth, user, tool, DFA and BPE table digests, and hashes of trace, tokens and encoded claims. The verifier context selects the policy and parsing function externally. See Rust:1688 `commit_turn_bytes`, Rust:1933 `turn_transcript` and Rust:1993 `verify_composed_turn`.

[OPEN] The Lean result is for the mathematical checker. The Rust parser, SHA3 implementation, solver, wire decoder and BPE implementation have executable coverage here. A refinement proof for those implementations and a computational hiding or collision-resistance reduction remain open.

[DERIVED] The BPE round-trip premise has a concrete interpretation in this builder. Each merge token stores the concatenation of its two operands’ byte expansions. Replacing an adjacent pair with its merge token preserves the decoded word and shortens the sequence. The initial singleton tokens decode to the input, so every completed encoding decodes to those bytes. Re-encoding detects an alternative token sequence that decodes to the same word. See Rust:1762 `BpeTable`, Rust:1816 `encode`, Rust:1837 `decode` and tests:1010 `composed_turn_rejects_tokens_of_different_bytes`.

## Disclosure to the verifier

[SOURCE] Sorting uses **plaintext encoded keys**. For the SHA3 backend a key is a one-byte predicate tag below 255 followed by fixed-width big-endian u64 arguments. Bottom is empty, top is `ff`. The leaf preimage has a leaf domain tag, a 32-byte salt, the little-endian u32 key length and the key. Internal nodes have a separate domain tag and two ordered 32-byte digests. The salt derivation hashes its own domain, the master, the little-endian u64 position, the little-endian u32 key length and the key. See Rust:851 `Sha3Hasher` and Rust:881 `sha3_leaf_salt`.

| Observable | Information available |
|---|---|
| Public EDB commitment | [DERIVED] Root and depth d disclose capacity. With the minimal builder and n distinct encoded facts, `2^(d−1) < n+2 ≤ 2^d`. This lower bound depends on minimal padding. Repeated identical roots link snapshots. |
| Membership | [DERIVED] The claim gives the fact, salt, position j and d sibling digests. With the checked layout and bottom at zero, exactly j−1 facts precede it. |
| Gap | [DERIVED] The claim gives the absent query, **both** neighboring plaintext keys, both salts, indices i and i+1, both paths and the open interval containing no fact. Exactly i facts precede the query. A right-hand top sentinel identifies the first top position and hence the exact fact count. A bottom-to-top gap identifies an empty EDB. |
| Rule and unfounded set | [DERIVED] The recipient sees all signed atoms, ranks, chosen rule IDs and substitutions, all listed members of U, and all auxiliary support and blocker claims in the certificate. The public program lets the recipient reconstruct matching rule bodies. |
| Repeated proofs | [DERIVED] Openings at the same root can be combined. Equal paths, positions and shared subtree digests reveal overlap. Reusing a master can link unchanged position/key pairs across snapshots. |
| Composed turn | [SOURCE] The certificate explicitly carries bytes and salt, user/tool, byte and EDB commitments, DFA trace, token IDs, table digests, policy claims and transcript. A recipient of the full certificate reads the payload directly. See Rust:1870 `ComposedByteTurnCert`. |

[HYPOTHESIS] Concealing unopened keys from a root or sibling digest requires unpredictable secret salts and a suitable hiding assumption for the domain-separated hash constructions. Opened neighbors and order information remain observable under that assumption. The fixture publishes its deterministic master `[0x5A; 32]` and its turn salt. Its timings carry no empirical hiding claim. See tests:674 `MASTER` and tests:916 `prove`.

## Reproduction

[EXECUTED] From the research repository, this command rebuilt the Lean module into the local overlay, replayed the JSON with Lean, and ran the two scoped Cargo targets. The script invokes the tracked-tree import-boundary checker and separately scans the owned target’s imports, tokens, line count and guarded axiom prints. It elaborates the source on every run with warnings promoted to errors. The overlay contains the generated parity proof and the Cargo logs.

```sh
cd /Users/ember/dev/zkml-research
bash research/wave11_frontier_upgrades_2026_11_22/formal_calculus/build_and_verify.sh
```

[EXECUTED] The Rust portion runs the following commands. The benchmark is part of the integration target. The fixture was regenerated once during editing with `CARGO_TARGET_DIR=/tmp/target-w11-calculus CERT_DATALOG_REGEN=1 cargo test --release --locked --test cert_and_datalog_calculus conformance_json_is_reproducible` from the prover directory. The verification script unsets that regeneration switch.

```sh
cd /Users/ember/dev/minidregg/prover
export CARGO_TARGET_DIR=/tmp/target-w11-calculus
cargo test --locked --release --lib datalog_and_cert_calculus
cargo test --locked --release --test cert_and_datalog_calculus -- --nocapture --test-threads=1
```

[EXECUTED] The final run on 2026-11-22 exited 0. The target has 945 lines and seven message-guarded axiom prints. Its six direct imports are Mathlib modules. The ATLAS scan found zero forbidden tokens in executable source, and Lean and Cargo emitted zero warnings. The pins report only `propext`, `Classical.choice` and `Quot.sound` across the pinned proofs. The lane uses the default Lean linters. Selected output from the command above follows.

```text
ATLAS: 945 lines, 7 axiom pins, imports and forbidden tokens checked
Lean/JSON: root 839753907; 16 paths; 58 matching verdicts; 51 signed model answers proved
test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 77 filtered out; finished in 0.00s
test result: ok. 20 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.37s
PASS: Lean overlay, conformance parity and both release test targets
```

[EXECUTED] The 58 cases comprise seven hand fixtures and one generated certificate per toy atom. The 51 model proofs each use the actual fixture, an exact-depth verifier judgment and its agreement with the reference leaves. The true IDBs were 20, 21, 22, 30, 32 and 41. The unit test independently checks 32 subsets of five rules, two EDB states and four signed query answers per state against Boolean truth conditions. The integration tests also exercise both sentinels, surplus siblings, equal ranks, a positive cycle, blocked versus unblocked alternative rules, repeated head variables, a non-head-covering predicate, inconsistent model/program inputs and relabeled turn components. See Rust:2055 `all_signed_queries_in_small_stratified_programs`, tests:269 `conformance_json_is_reproducible`, tests:385 `toy_tamper_falsifiers` and tests:470 `unf_checks_every_matching_head_instance`.

## 100,000-fact SHA3 measurement

[EXECUTED] On an Apple M2 Max, Darwin 27.2.0 arm64, the release run committed 100,000 distinct synthetic EDB facts in **123.3 ms** and solved the policy in **126.4 ms**. The padded tree had depth 17 and 131,072 leaves. The solver recorded maximum round 7, 88 trusted tuples, 130,226 can tuples, 117,374 allowed tuples and 20,274 alert tuples. Input generation preceded both timers. The benchmark seeds SplitMix with `0xC0FFEE`. Compiler identity came from `rustc --version` (`1.98.0-nightly (8b6558a02 2026-06-20)`), and host identity from `uname -mrs` and `sysctl -n machdep.cpu.brand_string`. See tests:615 `BIG`, tests:641 `synthetic_policy_edb` and tests:798 `bench_policy_100k_sha3_edb`.

[EXECUTED] All timings below are milliseconds as printed by that same invocation. Generation and first verification are single observations. The verify and decode-plus-verify columns are arithmetic means over 200 iterations each. Full output is retained by the verifier in `formal_calculus/build/rust-integration.log`.

| Signed query (user, resource) | Claims | Encoded bytes | Generate | First verify | Mean verify | Mean decode + verify |
|---|---:|---:|---:|---:|---:|---:|
| allowed(3270, 561), group membership | 5 | 2,578 | 0.044 | 0.0254 | 0.0188 | 0.0266 |
| ¬alert(16770, 47), allowed request | 5 | 2,010 | 0.035 | 0.0165 | 0.0175 | 0.0174 |
| ¬allowed(12113, 484), revoked user | 2 | 680 | 0.011 | 0.0052 | 0.0049 | 0.0051 |
| alert(10398, 1861), revoked request | 4 | 1,352 | 0.014 | 0.0100 | 0.0097 | 0.0105 |
| allowed(10966, 1976), delegation chain | 16 | 5,920 | 0.071 | 0.0437 | 0.0566 | 0.0548 |

[EXECUTED] Generating ¬can returned `NonHeadCovering` in 0.021 ms. The separate opened-turn fixture used 52 bytes, 38 canonical tokens and four Datalog claims (712 encoded claim bytes). It took 0.066 ms to produce and 0.060 ms to verify. These are measurements of disclosed, native certificates on this machine.

[EXECUTED] Research instruments used in this audit — Kagi: 0, Scry: 0, eprint downloads: 0.
