# BaseFold work-capacity event: the exact event, the bridge, the price, the charge

Lane note for ranked next-proof queue item 1 of
`minidregg/docs/FORMAL_STATUS_AND_NEXT_PROOFS.md` ("Close the exact BaseFold
work-capacity event. Prove the deterministic bridge from no capacity collision
to the replay-compatible terminal-fresh run, then price it on the existing
fixed work ledger. Do not substitute pairwise capacity distinctness for
rooted-path uniqueness.").

File created: `/Users/ember/dev/minidregg/Selvage/BaseFoldBcsCapacityEvent.lean`
(1379 lines, imports `Selvage.BaseFoldBcsRunSchedule` and
`Selvage.BaseFoldBcsStrictRomLedger`; nothing else touched).  Elaborates with
`lake env lean` at 0 errors / 0 warnings; 12 `#guard_msgs`-pinned
`#print axioms` (all `[propext, Classical.choice, Quot.sound]`);
`scripts/check-import-boundary.sh` OK; no `sorry`, no `axiom`.  Not committed.

## Ground truth consumed (quoted binders)

`Selvage/BaseFoldBcsRunSchedule.lean:1432`

```lean
def PaddedEagerTerminalFreshRun {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (coins : Fin (paddedTranscriptPrimitiveWork statement receipt) →
      Rate × Cap) : Prop :=
  ∀ (round : Fin (m + queryCount)) (state : WorkHybridState Rate Cap),
    paddedWorkHybridStateNat statement receipt verdict coins round
        (Nat.le_of_lt round.isLt) = .ok state →
      TerminalPrimitiveFreshTo
        (lastRateCoin ((state.remaining.take
          (paddedRoundPrimitiveWork statement receipt round)).map Prod.fst))
        state.core.ro state.core.primitive (0, 0) []
        (paddedPublicMessageSchedule statement receipt round)
        ((state.remaining.take
          (paddedRoundPrimitiveWork statement receipt round)).map Prod.fst)
        ((state.remaining.take
          (paddedRoundPrimitiveWork statement receipt round)).map Prod.snd)
```

`Selvage/SpongeIndiff.lean:872`

```lean
theorem capBad_le (qc : ℕ) (S : Finset Cap) (hS : S.card ≤ qc + 1) :
    uniformProb (Fin qc → Cap) (CapBad S)
      ≤ 2 * (qc : ℝ) ^ 2 / (Fintype.card Cap : ℝ)
-- with  CapBad S c := (∃ i j : Fin qc, i < j ∧ c i = c j) ∨ ∃ i, c i ∈ S
```

The consumer of the event is `paddedEagerDeferredRun_terminalFresh_agreement`
(RunSchedule), which needs `PaddedFullMessageRoutingSafe` (proved by
`paddedFullMessageRoutingSafe` for `queryCount ≤ BabyBearExt4.modulus`) and
`PaddedEagerTerminalFreshRun`.  The existing ledger charged into is
`BaseFoldBcsStrictRomLedger.strictRomSamplingError work queryCount =
romError work + queryCount / modulus`.

## The exact event (NOT pairwise distinctness)

Walk level, generic `Rate Cap` (`namespace Minidregg.Selvage`):

```lean
noncomputable def CapacityPathCollision (iv : Rate × Cap)
    (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (state : Rate × Cap) (seen : List Rate) :
    List Rate → List Rate → List Cap → Prop
  | [], _, _ => False
  | _ :: _, [], _ => False
  | _ :: _, _, [] => False
  | block :: message, rateCoin :: rateCoins,
      capacityCoin :: capacityCoins =>
      let nextPrefix := seen ++ [block]
      let key : Rate × Cap := (state.1 + block, state.2)
      match primitive.lookup key with
      | some edgeValue =>
          let roReply := ro.respond nextPrefix edgeValue.1
          CapacityPathCollision iv roReply.2 primitive edgeValue nextPrefix
            message rateCoins capacityCoins
      | none =>
          capacityCoin ∈ capsOf primitive iv ∨
            let roReply := ro.respond nextPrefix rateCoin
            let programmed : Rate × Cap := (roReply.1, capacityCoin)
            let primitiveReply := primitive.respond key programmed
            CapacityPathCollision iv roReply.2 primitiveReply.2
              primitiveReply.1 nextPrefix message rateCoins capacityCoins
```

Replayed edges consume their coin without programming and cannot collide;
a freshly programmed edge collides iff its capacity coin is already in the
landed `capsOf` of the table *reachable at that moment* (IV, inputs,
outputs).  Run level (`namespace Minidregg.Selvage.BaseFoldBcsCapacityEvent`):

```lean
def PaddedCapacityCollisionRun {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (coins : Fin (paddedTranscriptPrimitiveWork statement receipt) →
      Rate × Cap) : Prop :=
  ∃ (round : Fin (m + queryCount)) (state : WorkHybridState Rate Cap),
    paddedWorkHybridStateNat statement receipt verdict coins round
        (Nat.le_of_lt round.isLt) = .ok state ∧
      CapacityPathCollision (0, 0) state.core.ro state.core.primitive (0, 0) []
        (paddedPublicMessageSchedule statement receipt round)
        ((state.remaining.take
          (paddedRoundPrimitiveWork statement receipt round)).map Prod.fst)
        ((state.remaining.take
          (paddedRoundPrimitiveWork statement receipt round)).map Prod.snd)
```

Rate/capacity split: `paddedRateCoins`, `paddedCapacityCoins`
(`fun i => (coins i).1` / `.2`) and the lossless
`splitWorkCoins : (Fin W → α × β) ≃ ((Fin W → α) × (Fin W → β))`.

## The invariant the bridge runs through

- `UniquePaths primitive iv` — the LANDED rooted-path uniqueness of
  `SpongeIndiff` (every rooted capacity has one path), preserved per fresh
  edge by the landed `uniquePaths_respond_freshOut` exactly when the
  programmed capacity misses `capsOf` (this is what `¬CapacityPathCollision`
  supplies).
- `TableRooted iv ro primitive admissible`: every table entry is the edge
  `(node.1 + block, node.2)` of some rooted prefix `path` (`walkFrom
  primitive iv path = some node`) with `ro.lookup (path ++ [block]) = some
  entry.2.1`, and `path ++ [block]` admissible.  Admissibility during a
  round is `WalkAdmissible issued seen μ := issued μ ∨ μ <+: seen`; between
  rounds `issued := PaddedIssuedBefore statement receipt round` (a prefix of a
  message of some round `j < round`).
- `CapsConsumed iv primitive consumed`: every capacity in `capsOf` is the
  IV's or a consumed coordinate (`PaddedConsumedCap coins bound c := ∃ i <
  bound, (coins i).2 = c`).  This one needs NO freshness and is threaded
  through collisions too; it is what makes the transport to `CapBad` exact.

Why uniqueness (not distinctness) is the load-bearing thing: at a replayed
edge the entry's rooted prefix must be *the* current prefix, and at the
terminal step a present edge would have to be rooted at the current full
message, which is either a proper prefix of the current walk (length
contradiction) or a prefix of an earlier message (contradicts
`PaddedFullMessageRoutingSafe`).  Both use `hU state.2 (seen, state.1)
(path, node.1)` — the unique rooted path to capacity `state.2`.

## Statements proved (all pinned)

Walk level:

```lean
theorem terminalPrimitiveFreshTo_of_noCollision (iv : Rate × Cap)
    (issued : List Rate → Prop) (terminalRate : Rate) :
    ∀ (message rateCoins : List Rate) (capacityCoins : List Cap)
      (ro : Oracle (List Rate) Rate) (primitive : Oracle (Rate × Cap) (Rate × Cap))
      (state : Rate × Cap) (seen : List Rate),
      message ≠ [] → rateCoins.length = message.length →
      capacityCoins.length = message.length →
      lastRateCoin rateCoins = terminalRate →
      UniquePaths primitive iv →
      TableRooted iv ro primitive (WalkAdmissible issued seen) →
      walkFrom primitive iv seen = some state →
      ¬ issued (seen ++ message) →
      ¬ CapacityPathCollision iv ro primitive state seen message rateCoins capacityCoins →
      TerminalPrimitiveFreshTo terminalRate ro primitive state seen message
          rateCoins capacityCoins ∧
        ∀ result, programPrefixes ro primitive state seen message rateCoins
              capacityCoins = some result →
            UniquePaths result.primitive iv ∧
              TableRooted iv result.ro result.primitive
                (WalkAdmissible issued (seen ++ message))
theorem capacityPathCollision_index  -- collision ⇒ ∃ k, caps[k] = iv.2 ∨ consumed caps[k] ∨ ∃ j < k, caps[j] = caps[k]
theorem programPrefixes_capsConsumed -- CapsConsumed preserved with consumed ∨ (∈ capacityCoins), no freshness premise
theorem workHybridStep_constr_program -- a successful adapter step exposes its programConstruction result tables
```

Run level:

```lean
theorem paddedEagerTerminalFreshRun_of_noCapacityCollision
    (hsafe : PaddedFullMessageRoutingSafe statement receipt)
    (hnocol : ¬ PaddedCapacityCollisionRun statement receipt verdict coins) :
    PaddedEagerTerminalFreshRun statement receipt verdict coins
theorem paddedCapacityCollisionRun_capBad (hcol : PaddedCapacityCollisionRun …) :
    CapBad {(0 : Cap)} (paddedCapacityCoins statement receipt coins)
theorem paddedCapacityCollisionRun_le :
    uniformProb (Fin (paddedTranscriptPrimitiveWork statement receipt) → Rate × Cap)
        (PaddedCapacityCollisionRun statement receipt verdict)
      ≤ 2 * (paddedTranscriptPrimitiveWork statement receipt : Real) ^ 2 /
          (Fintype.card Cap : Real)
theorem paddedEagerDeferredRun_disagreement_le (hsafe) :
    uniformProb _ (fun coins => ¬ ∃ eager deferred, workHybridRun … coins = .ok eager ∧
        deferredWorkRun … (paddedSegmentReindex … coins) = .ok deferred ∧
        eager.core.ans = deferred.core.ans) ≤ 2 * W^2 / |Cap|
theorem paddedConstructionDistinguisher_rom_rejection_capacity_bound (hrom) :
    |realProb … - idealProb …| + Pr[QuerySeedRejection] + Pr[PaddedCapacityCollisionRun …]
      ≤ strictRomSamplingCapacityError (paddedTranscriptPrimitiveWork statement receipt) queryCount
-- strictRomSamplingCapacityError work queryCount :=
--   strictRomSamplingError work queryCount + paddedCapacityError work
-- paddedCapacityError work := 2 * work^2 / |Cap|
```

Supporting run bookkeeping: `paddedWorkHybridStateNat_ok_shape` (transcript
length and static remaining suffix, read off the landed classification),
`paddedRound_data`, `paddedRound_bridge` (one round: terminal-fresh +
invariants into the next state), `paddedWorkHybridStateNat_rooted`,
`paddedWorkHybridStateNat_capsConsumed`, `segment_mem`, `segment_getElem`.

## ATLAS fields per keystone

**`terminalPrimitiveFreshTo_of_noCollision` / `CapacityPathCollision`** (over
`ZMod 2 × Fin 3`, IV `(0,0)`, message `[1,0]`, rate coins `[1,0]`):
- witness: `CapacityEventExample.no_collision_fresh_capacities` — capacity
  coins `[1,2]` do not collide (computed through the handler laws), and
  `terminalFresh_fresh_capacities` obtains `TerminalPrimitiveFreshTo
  (lastRateCoin [1,0]) … [1,0] [1,0] [1,2]` THROUGH the bridge from empty
  tables (non-vacuous instantiation).
- falsifier: `collision_zero_capacity` — capacity coins `[0,2]` collide (first
  fresh edge gets the IV capacity), and `not_terminalFresh_zero_capacity` —
  terminal freshness FAILS: the collision closes the cycle `(1,0) ↦ (1,0)`, so
  the terminal edge of `[1,0]` is already present.  The no-collision
  hypothesis is a constraint, and it is exactly a rooted-path phenomenon.
- premise inhabitation: `uniquePaths_empty`, empty `TableRooted`, `walkFrom
  … [] = some iv` (rfl), `¬ issued` for `issued := fun _ => False`.

**`paddedEagerTerminalFreshRun_of_noCapacityCollision`**:
- premise inhabitation: `hsafe` by the landed `paddedFullMessageRoutingSafe`
  (`queryCount ≤ modulus`); `hnocol` by
  `paddedCapacityCollisionRun_avoidable : 2·W² < |Cap| → ∃ coins, ¬ PaddedCapacityCollisionRun …`
  (via `uniformProb_congr`/`uniformProb_const` and the price; for every
  statement/receipt in that regime).
- teeth: `paddedCapacityCollisionRun_zero : 0 < m + queryCount →
  PaddedCapacityCollisionRun statement receipt verdict (fun _ => (0,0))` —
  the all-zero work vector suffers the event at round 0 (its first fresh edge
  receives the IV capacity), for every statement/receipt.  The run-level
  falsifier of terminal freshness is the walk-level one above at round 0
  (identical predicate on empty tables); a concrete BabyBear-digest receipt
  evaluation was not attempted (classical `Oracle.lookup` on function-typed
  digests does not evaluate).

**`paddedCapacityCollisionRun_capBad` / `_le`**: witness/teeth inherit from
`capBad_pair`, `capBad_two_prob`, `capBad_two_pos` in SpongeIndiff (bound
attained at q = 2); the transport is monotone (`uniformProb_mono`) then the
split equivalence and `uniformProb_prod_le` (rate coordinate conditioned
out), then `capBad_le W {0}` with `|{0}| = 1 ≤ W + 1`.

## The ledger term and its size

Charged term: `paddedCapacityError W = 2·W²/|Cap|` with `|Cap| = p⁸`,
`p = 2013265921` (`BaseFoldPoseidon2Rom.capacity_card`), `W =
paddedTranscriptPrimitiveWork statement receipt = transcriptPrimitiveWork +
(m + queryCount)`.  Numerically `p⁸ ≈ 2^247.3`: at `W = 2^20` the term is
≈ `2^-206`; at `W = 2^30` ≈ `2^-186`.  The bound is the pessimistic constant
from `capBad_le` (birthday `W(W−1)/2 + W·1`, rounded up to `2W²`).

⚠ Read the ledger exactly.  `romError W = 2·W²/p⁸ + W²/p¹⁶` (the *named,
unproved* ideal-permutation target's error expression) already contains the
same `2·W²/p⁸` summand.  `strictRomSamplingCapacityError` adds my term ON TOP
of `romError`, by union bound, because `hrom` is still an open premise and the
two events live on different sample spaces (permutation space vs. work
space).  When queue item 2 realizes the RP/RF switch through THIS event, the
honest ledger should identify the summands rather than pay twice; that is a
decision for item 2, not a claim made here.

## What is proved vs. named obligation

Everything in the file is proved; no obligation was left in a docstring.
Deviations from the queue's wording, made for honesty:

1. The bridge needs `PaddedFullMessageRoutingSafe` in addition to
   `¬PaddedCapacityCollisionRun` (queue: "from no capacity collision").  It is
   genuinely needed: with a repeated or prefix-nested message the terminal
   edge is legitimately present.  It is already proved for the padded
   schedule, so the composed statement is unconditional modulo
   `queryCount ≤ modulus`.
2. The event is the rooted-path collision *at the reachable table*; pairwise
   `CapBad {0}` is only the pricing superset (`_capBad`).  The gap between the
   two (coins of replayed edges, coins of tables that were never reached) is
   deliberately NOT priced tighter.
3. The coupling probability statement (`paddedEagerDeferredRun_disagreement_le`)
   is hybrid-to-hybrid on the work space; it is not the ROM advantage.

## What queue item 2 now needs

- RP/RF and deployed-Poseidon2 switches: realize `romConstructionTarget`
  (`SpongeIndiffWorkGame Rate Cap (0,0)`) with the work-space bad event
  being exactly `PaddedCapacityCollisionRun` (or its generic walk form
  `CapacityPathCollision`), and identify the `2·W²/p⁸` summand of `romError`
  with `paddedCapacityError` so the ledger does not double count; the
  `W²/p¹⁶` term is the permutation/function switch on the full state.
- The generic (adaptive, non-fixed-schedule) version of the bridge: this file
  is for the fixed padded receipt schedule (all queries are `.constr`, no
  public `fwd/inv`); `TableRooted` would need the simulator-programmed edges
  of `simFwdRO`/`simInv` if item 2 reuses it for the adaptive game
  (`SpongeIndiffRunInvariant` already covers `UniquePaths` there).
- Bind Ext4, root, path and whole-receipt codecs to the proved field/Merkle
  semantics (unchanged from the row).
