# Proof-library decisions: source checks, 2026-11-06

## 9. ArkLib: contribute the missing adapter, then retire duplicated proofs

**Question:** Should we contribute on #627, and replace Selvage's FS/Depth proofs with ArkLib?

**Options:** maintain both proof stacks; offer our existing stack upstream; or contribute the missing Merkle adapter and consume upstream's general theorems.

**Recommendation [INFERRED]:** Choose the third. Offer a small native-API blueprint on [#627](https://github.com/Verified-zkEVM/ArkLib/issues/627), crediting its existing author and asking where the native successor should live. The first deliverable should adapt VCVio's extraction theorem—the guarantee that accepted openings agree with data recoverable from the commitment-phase query log. Follow it with the interactive commitment compiler, then compose with Fiat–Shamir. Do not offer a supposedly complete BCS compiler: neither our accumulator instance nor a Merkle adapter establishes that theorem. This run posts nothing.

Finish the existing bridge and retire precisely the FS/Depth theorems it derives. Keep only uncovered generality and the bridge; do not keep two maintained proofs for reassurance. The approximately 2,600-line deletion is an intended outcome, not a present eligibility test. Require equality of the actual games and extractor, preservation of error bounds, and migrated consumers before removing a proof.

**Evidence:** [READ] `notes/arklib-upstream/{GROUNDING.md,CORRECTIONS-2026-11-06.md}` correctly retract the earlier absence claim. I also read `ArkLib/Interaction/Oracle/Security/StateRestorationGame.lean:102` in `/Users/ember/src/ArkLib-fork`: `stateRestoration_knowledge_soundness` runs the verifier and proves the `(Q + rounds.length) * error` bound. Live [PR #1277](https://github.com/Verified-zkEVM/ArkLib/pull/1277), fetched November 6, remains open, not merged; it covers actual single-salt verification with private-coin adversaries. Its companion stack must not be described as already released.

[READ] `CONTRIBUTING.md:14–25` asks for discussion before substantial implementation; `docs/design/05-roadmap.md:191–198` names the unstarted Merkle adapter and says to reuse VCVio's game. The live issue and all five comments concern an existing legacy-layer proposal; acknowledge that work rather than taking over its scope. [READ] The bridge at minidregg commit `681b3c7d9`, `bridges/arklib-ud/SelvageArkLib/StateRestoration.lean`, proves preservation and local boundedness for finite prover-message types. Its lane transcript (`cv show --frozen 78fef112-a52f-425f-8503-f3fa24ff087c --agent ab9a7605 --last 14`) leaves cached-oracle coupling, extractor equality, full game correspondence and infinite-alphabet closure unfinished. These are genuine remaining obligations.

**What would change my mind:** A maintainer already owns the adapter; coordinate a review/client contribution instead. A real consumer needs infinite message alphabets and the proposed finite-support reduction fails; retain that portion. The existing `Q=0` example is nonvacuous but does not test adaptive query accounting (`ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean:143–160`); add a repeated/fresh-query client as a bridge acceptance condition, not as an accusation that the upstream theorem is false.

**Cost or risk of being wrong:** Import and API churn, and a subtle mismatch between games. A pinned optional bridge bounds dependency exposure; premature deletion could silently weaken statements. Publishing a focused blueprint costs little and avoids building the wrong abstraction.

## 12. Tower256: integrate work 9104 and finish the binary framing now

**Question:** Should the Tower256 work-profile and binary length-codec flag day proceed?

**Options:** freeze unary framing; defer all changes; or integrate the registered work profile and version the binary framing before the native prover interface becomes established.

**Recommendation [INFERRED]:** Choose the third. The work profile is already implemented on the lane branch: integrate it as a new artifact, and make bounded `u32` little-endian framing part of this development cut. Keep the prefix-state cache. Do not sell this as a large speedup; the reason to finish framing now is a smaller, conventional, explicitly bounded interface before downstream adoption. Today's approval of shape changes removes the old permission question.

Use a length type restricted below `2^32`, or a checked encoder which refuses overflow; silently truncating `Nat` destroys injectivity. Prove envelope prefix-freeness, `basisPrefix` injectivity and decoder round trips for the new domain. Assign a new suite/transcript version and artifact/codec pins; regenerate roots, draws and honest receipts and require rejection under the wrong version. Receipt compression and transcript framing are separate changes and need separate checks. Native work remains opaque: only Lean's decoder and checker can accept its reply.

**Evidence:** [READ] The requested `minidregg/docs/TOWER256-FRI-PROVER-WORK.md` is absent from the main working checkout, but present at commit `107697663` on `lane/tower256-prover-exe`; I read it with `git show`. Section 5 records work `9104`, request codec `9011`, response codec `9013`, a new catalog `[9101,9104]`, and unchanged original v1 catalog. `Compiler/Tower256FriNativeDeployment.lean:acceptResponse_iff` connects accepted bytes to `SuccinctAccepts`. Its source still says the Rust prover is unwritten; compiled Lean examples are not that native kernel.

[READ] The same note §2 records the prefix cache and compact pair openings already implemented, superseding the older “cache first” task in `zkml-research/docs/LEAF-PROVER-DECISION.md:278–332`. [MEASURED] Re-evaluation of that note's **older cost model**, saved in [TOWER-COUNTS.json](TOWER-COUNTS.json), gives `ell=14`: seed permutations 7,666 → 316 with caching → 161 with binary framing; query-prefix bytes 6,824 → 1,832. After caching, its verifier total falls 45,913 → 45,427 (about 1.1%). This is neither a runtime measurement nor an updated total for the newly compressed receipt.

**What would change my mind:** A deployed consumer already depends on these exact bytes, or the bounded framing proof materially delays a working verifier. Then ship the cached unary version with an explicit version, and change framing in the next scheduled cut. No such deployed dependency is established by the sources read.

**Cost or risk of being wrong:** New identities invalidate old fixtures and receipts. Overflow or ambiguous mixed-version parsing is more serious than the modest saving. Keep the pre-change decoder only as an explicitly selected historical format, never an automatic fallback after new-format verification fails.


## Reproducing the count measurement

[MEASURED] The script below loads the same functions and parameters as the executed
importlib-based check. Its output is the `rows` array in `TOWER-COUNTS.json`;
it does not inspect the current Lean receipt implementation or run a prover.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 - <<'PYCOUNT'
import runpy, json
m = runpy.run_path("notes/construction-search/tower256_fri_counts.py")
rows = []
for ell in (14, 20):
    for unary, cache, label in ((True, False, "unary"),
                                (True, True, "unary+cache"),
                                (False, True, "u32+cache")):
        c = m["counts"](ell, 2, ell-4, m["q_for"](2), unary=unary, cache=cache)
        rows.append(dict(codec=label, **{k: c[k] for k in
            ("ell", "seed_kf", "challenge_kf", "query_prefix_bytes",
             "prover_kf", "verifier_kf")}))
print(json.dumps(rows, indent=2))
PYCOUNT
```
