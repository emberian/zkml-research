# Wave 8b — the open turn waist (D2) and IConfluent tier relaxation (D5) in `obend`

Lane `w8b-obend-turn-waist`. Brief: board #171. This lands `MASTER_REVIVAL_ALIGNMENT.md`
§2.1.3 (open registered effect waist), §2.4.1 (Tier 0/1 relaxation) and decisions `D2`/`D5`. The
code is in `obend` worktree branch `revival-open-turn-waist` at commit **`9a30f557`**, not pushed.
Paths below are relative to `lean/`.

## 1. The open turn waist (`Obend/Vault/Replay.lean`)

- [EXECUTED] `Turn` now has 28 closed constructors plus one open arm, `ext (tag) (op : Json)`
  (`:150`). The `filled` arm, which nothing outside `Replay` built, is now the first registered
  extension, `fillExt` (`:925`), in `LawfulTurnRegistry.core` (`:949`). `turnOf` decodes old
  `"turn":"fill"` records to it, so existing logs replay unchanged (`fill_replays`, `:1224`).
- [EXECUTED] `LawfulTurnExt` (`:824`) carries a tag, `Op`, codec, step and footprint. Its laws are
  proof fields: `roundtrip` (decode after encode is the identity); `conserves` (`Conserves`,
  `:809`, keeps journal, grants, outstanding, landed and minted); `frame` (pages outside the
  footprint are unchanged).
- [EXECUTED] `LawfulTurnRegistry` (`:836`) requires unique tags, the shape of [SOURCE] `minidregg/
  Effects/Revival/Engine.lean:274` `LawfulRegistry`. `stepTurn w t (R := .core)` (`:955`) gains one
  arm, `.ext tag op => stepExt R w tag op` (`:886`); no domain arm was added.
- Proved [EXECUTED] (all in the remote build):
  - `ext_replays` (`:1181`): a registered record replays as `e.step w x`;
    `stepTurn_core_registry_free` (`:1190`): registration never changes a core turn.
  - `stepTurns_ext_conserves` (`:1205`): conservation along any trace of registered records
    (the multi-turn invariant); `stepExt_conserves` (`:904`).
  - `stepExt_unregistered_refused` (`:896`), with its premise inhabited by
    `unregistered_tag_refused_empty`; `dropping_obligations_not_conserving` (falsifier).
  - `outstanding_kept` and `landed_kept` (`:1820`, `:1853`), now for every registry.
- [EXECUTED] `#tooth` (`:1242`, `:1245`); both report "rejected stored proof". Mutating `stepExt`
  to drop obligations rejects `stepExt_conserves`. Mutating `LawfulTurnRegistry.find?` to `head?`
  rejects `find?_eq_none`, so `stepExt_unregistered_refused` fails.

## 2. IConfluent pushout relaxation (`Obend/Consensus/Finality.lean`)

- [EXECUTED] New definitions: `JoinSemilattice` (`:264`), `IConfluent` (`:271`), `PushoutWitness`
  (`:276`). A witness says the operation is `s ↦ join s δ`, with `I δ` and `I` I-confluent.
  `TurnOp` (`:284`) holds `apply`, `cells` and `pushout : Option PushoutWitness`.
- [EXECUTED] `turnCommitTier` changed in place (`:306`) to `max op.floor (joinTier cells)`. The
  floor is `speculative` with a witness and `quorum_final` without. New: `admitAtTier` (`:310`)
  and `Operation.confluentWrite` (minimum tier `speculative`). `turnCommitTier_admits_stateWrite`
  is replaced by `turnCommitTier_admits_write` (`:330`).
- Policy names [SOURCE] (`CONSENSUS_BLOCKLACE_AND_SETTLEMENT_AUDIT.md:175-176`):
  `speculative` = `LocalOptimistic`, `attested` = `EquivocationBounded`, `quorum_final` = `Byzantine`.
- Proved [EXECUTED]:
  - `admitAtTier_sound` (`:343`): admitted below `quorum_final` implies a witness.
  - `admitAtGate` (`:722`), `admitAtGate_unwitnessed_sound` (`:733`) and `admitAtGate_sound`
    (`:753`): an admitted write is witnessed, or the gate's `FinCert` checks and
    `Finalized P sent` holds (`n - f` votes).
  - `confluent_diamond` (`:362`), `applyWitnessed_perm` and `applyWitnessed_keeps`: replicas
    converge in any order and keep `I`.
  - `PushoutWitness.idempotent` and `balanceDebit_no_pushout` (`:440`): a debit `b ↦ b - k`,
    `k > 0`, has no witness in **any** semilattice.
  - `nonconfluent_debit_refused_below_byzantine` (`:450`): the debit is refused at `speculative`
    and at `attested`.
- [EXECUTED] `#tooth` (`:462`, `:765`): `TurnOp.floor := speculative` rejects
  `turnCommitTier_unwitnessed`; `admitAtGate` without the `FinCert` check rejects its soundness.
- [EXECUTED] `docMerge_tombstones_join` (`:405`, private): `Doc.Graph.merge`'s tombstones are the
  `pointwiseOr` join. `killsWithin_iconfluent` and `tombstoneOp` give a witnessed Doc tombstoning.
  `decide`-checked examples: tombstoning admitted at Tier 0; `sampleDebit` refused at Tier 0;
  `sampleDebit` admitted at a gate whose 3-of-4 `FinCert` checks, refused there without it.

## 3. A trap found, and the fix

- [EXECUTED] `Obend/Doc/Graph.lean:84` declares a global
  `instance : DecidableEq ByteArray := decByteArray`, whose body downstream kernels cannot reduce.
  A public import of `Doc.Merge` broke two `decide` checks: the existing `advanceSimplexGate`
  example (Finality §7) and `tests/metasystem/DeosSimplexOutboxSeamTest.lean:632/635` (stuck at
  `Doc.decByteArray`). Fix: Finality imports `Doc.Merge` **privately** and erases the instance
  locally (`attribute [-instance]`, `:56`). [HYPOTHESIS] The instance shadows core's for every
  importer of `Doc.Graph`; retiring it is a separate scar-removal lane.

## 4. Verification

- [EXECUTED] All builds ran remotely on `bb2` in `~/.cache/obb-worktrees/w8b-waist`, under
  `SWARM_MEM_MAX=12G timeout --kill-after=10s 600s lake build …`; 0 macOS builds. Targets:
  `Finality`, `Replay`, `Vault.Cli`, `FFI.Bridge`, `Vault.Escrow`, `UnifiedDeos`,
  `IrreversibleOutbox`, `Main`, `Apps.SovereignDrex`, `Teeth.Extracted.{Apps,Core}Teeth`, and the
  11 `metasystem.*` tests that import Replay or Finality. Result: "Build completed successfully
  (540 jobs)", with 0 new warnings in the touched modules. Remote scratch removed afterwards.
- [EXECUTED] `lake build Obend` (tier 1): the only failure is
  `Obend.Hardware.OpenHypergraphQuotient` (`:670-674`). A Python import walk shows its closure
  contains no Finality, Replay or Doc module, so the failure is not this change's. [OPEN] Its
  owner should fix it.
- [EXECUTED] `obb lint --strict --strict-expose --strict-harnesses`: 510 findings before and after,
  0 new. The only finding on a touched file is the existing `lean/monolithic-module` on `Replay`.
  `@[expose]`: 7 in Finality, 1 in Replay. 0 `sorry`, 0 custom `axiom`, 0 `native_decide`.
- [EXECUTED] `tests/m4/*` (in no Lake lib) follows the new API; it still fails on unrelated stale
  names (`State`, `castVote`, `EpistemicFrame…`). `obb pipeline|apex|harness` absent in this `obb`.

## 5. Open

- [OPEN] No `JoinSemilattice` instance for `Vault.Merge` (only Doc tombstones, `maxNat`). Not done:
  Tier-1 signer thresholds `(signers, k)`, `Slot.Budget` leases, binding `TurnOp` to `Replay.Turn`.
- [OPEN] `Conserves` forbids journal edits outright; a supply-preserving relaxation is future work.
  Metered search queries: 0.
