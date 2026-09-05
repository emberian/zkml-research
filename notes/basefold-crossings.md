# BaseFold cryptographic crossings: the capacity summand identified, the deployed Poseidon2 boundary, and the receipt bytes bound to acceptance

Lane note for ranked next-proof queue item 2 of
`minidregg/docs/FORMAL_STATUS_AND_NEXT_PROOFS.md` ("Complete the BaseFold
cryptographic crossings. Add RP/RF and deployed Poseidon2 boundaries with
every term visible; bind Ext4, root, path, and whole-receipt codecs to the
proved field/Merkle semantics."), taking item 1's warning as the first job:
"`romError W` already contains the summand `2W²/p⁸`; my ledger adds the
same-shaped term by union bound ... Queue item 2 must identify the summands
... not pay twice."

Files created (nothing else touched; not committed; NOT added to
`Selvage.lean`, the coordinator root):

| file | lines | imports | status |
|---|---|---|---|
| `/Users/ember/dev/minidregg/Selvage/BaseFoldBcsCrossings.lean` | 953 | `Selvage.BaseFoldBcsCapacityEvent` | `lake env lean` 0 errors / 0 warnings; 14 pinned `#print axioms` |
| `/Users/ember/dev/minidregg/Selvage/BaseFoldBcsReceiptCodec.lean` | 578 | `Selvage.BaseFoldBcsByteCodec` | 0 / 0; 12 pins |
| `/Users/ember/dev/minidregg/Selvage/BaseFoldBcsDeferredIdeal.lean` | 339 | `Selvage.BaseFoldBcsCrossings`, `Selvage.SpongeIndiffOffBadRun`, `Selvage.LightClientGrinding` | 0 / 0; 6 pins |

All pins are `[propext, Classical.choice, Quot.sound]` except
`decodeNat_encodeNat_append` (`[propext, Quot.sound]`).  No `sorry`, no
`axiom`, no `#guard`.  `scripts/check-import-boundary.sh` OK.  One targeted
`lake build Selvage.BaseFoldBcsCrossings` was run (its only import was
already built) so the third file could import it; `pgrep -f "lake build"`
was empty each time.

## 1. The identification (the first job)

**Same quantity, as real numbers — proved.**

```lean
def switchError (work : Nat) : Real :=
  (work : Real) ^ 2 / ((modulus ^ 16 : Nat) : Real)

theorem capacity_summand_identified (work : Nat) :
    paddedCapacityError work =
      2 * (work : Real) ^ 2 / ((modulus ^ 8 : Nat) : Real)

theorem romError_eq_switch_add_capacity (work : Nat) :
    BaseFoldPoseidon2Rom.romError work =
      switchError work + paddedCapacityError work

theorem switchError_lt_paddedCapacityError (work : Nat) (hwork : 0 < work) :
    switchError work < paddedCapacityError work       -- teeth: distinct summands
theorem paddedCapacityError_pos (work : Nat) (hwork : 0 < work) :
    0 < paddedCapacityError work                       -- witness: not the zero term
```

**Not the same event, and which one the ledger keeps.**  `romError` is the
error expression *inside* the still-open `romConstructionTarget` (`hrom`), a
proposition about the ideal-permutation real world versus the lazy-RO ideal
world (perm space vs. ideal coin space).  Item 1's event lives on the eager
hybrid's work space `Fin W → Rate × Cap`.  An assumed `hrom` is opaque: no
theorem can identify a summand of an assumption with a proved event.  So the
honest move is to decompose the *padded class* of `hrom` into hops on
explicit sample spaces and let item 1's event BE the capacity hop.  The
ledger keeps `paddedCapacityError` (proved, item 1) and `switchError`
(named), and no longer carries `romError` as an opaque premise for the
padded receipt class.  The double payment is exhibited as a theorem:

```lean
def crossingsError (gap : Nat → Real) (work queryCount : Nat) : Real :=
  gap work + switchError work + paddedCapacityError work +
    (queryCount : Real) / (modulus : Real)

theorem crossingsError_zero_gap (work queryCount : Nat) :
    crossingsError (fun _ => 0) work queryCount = strictRomSamplingError work queryCount

theorem strictRomSamplingCapacityError_double_counts (work queryCount : Nat) :
    strictRomSamplingCapacityError work queryCount =
      crossingsError (fun _ => 0) work queryCount + paddedCapacityError work
```

Item 1's charged ledger = the honest ledger + exactly one extra capacity
term.

## 2. The hop chain, and what is proved vs. named

```
real (uniform Equiv.Perm)              [RP-RF-switch]         ≤ switchError W          NAMED
  ≈ total function (uniform function)  [RF-lazy-sampling]     exact                    NAMED
  = lazy function (work space)         [RF-lazy-eager]        off ¬collision, pointwise NAMED
  ≈ eager hybrid (work space)          item 1                 off ¬collision           PROVED
  ≈ deferred ideal (work space)        [DEFERRED-ideal-exact] exact                    PROVED (file 3)
  = idealRun (ideal coin space)
```

Worlds for the padded receipt distinguisher `D := paddedConstructionDistinguisher statement receipt verdict`
(all on `WorkCoins statement receipt := Fin (paddedTranscriptPrimitiveWork statement receipt) → Rate × Cap`
except the first two): `eagerAccept/eagerProb` (= `workHybridAccept`),
`deferredAccept/deferredProb` (= `deferredWorkAccept`), `lazyAccept/lazyProb`
(NEW `lazyFunctionRun`: constructions through the landed `lazyAbsorb`, one
work pair per block, replays consume nothing, inverse queries fail closed),
`functionProb` (NEW: uniform TOTAL function on `Rate × Cap`, inverse queries
fail closed), and

```lean
theorem paddedRealProb_eq_perm_functionAccept :
    realProb D (0, 0) = uniformProb (Equiv.Perm (Rate × Cap)) fun π => functionAccept (⇑π) D (0, 0)
```
(the landed real world IS the function world restricted to permutations; the
padded schedule is construction-only, `paddedConstructionDistinguisher_constructionOnly`).

**Proved, generic:** `uniformProb_abs_sub_le_of_agree_off_bad :
(∀ c, ¬ bad c → (left c ↔ right c)) → |P left − P right| ≤ P bad`.

**Proved, the eager/deferred hop through item 1:**

```lean
theorem eagerProb_sub_deferredProb_abs_le (hsafe : PaddedFullMessageRoutingSafe statement receipt) :
    |eagerProb statement receipt verdict - deferredProb statement receipt verdict|
      ≤ paddedCapacityError (paddedTranscriptPrimitiveWork statement receipt)
```

**Named hypotheses** (`def : Prop`, the tree's `[COMMIT-CR]`/`[FOLD-msis]`
shape; never axioms, never asserted; ATLAS fields in each docstring):

```lean
def PaddedRpRfSwitch statement receipt verdict : Prop :=                       -- [RP-RF-switch]
  |realProb D (0, 0) - functionProb D (0, 0)| ≤ switchError (paddedTranscriptPrimitiveWork statement receipt)
def PaddedLazyFunctionSampling statement receipt verdict : Prop :=             -- [RF-lazy-sampling]
  functionProb D (0, 0) = lazyProb statement receipt verdict
def PaddedLazyEagerAgreeOffCollision statement receipt verdict : Prop :=       -- [RF-lazy-eager]
  ∀ coins, ¬ PaddedCapacityCollisionRun statement receipt verdict coins →
    (lazyAccept statement receipt verdict coins ↔ eagerAccept statement receipt verdict coins)
def PaddedDeferredIdealExact statement receipt verdict : Prop :=               -- [DEFERRED-ideal-exact], PROVED in file 3
  deferredProb statement receipt verdict = idealProb D (0, 0)
def Poseidon2PermutationIdeal (gap : Nat → Real) : Prop :=                     -- [POSEIDON2-perm-ideal]
  ∀ {m queryCount} (statement : Statement m) (receipt : Receipt m queryCount) verdict,
    |deployedIndicator statement receipt verdict - realProb D (0, 0)|
      ≤ gap (paddedTranscriptPrimitiveWork statement receipt)
```

where `deployedAccept := functionAccept BaseFoldPoseidon2Rom.permutePair D (0,0)`
(the source-derived width-16 Poseidon2 at the generic sponge interface, zero
IV, deterministic) and `deployedIndicator := uniformProb Unit (fun _ => deployedAccept …)`
(`deployedIndicator_eq : = if deployedAccept then 1 else 0`).

ATLAS for the named ones:
- `[RP-RF-switch]`: witness `paddedRpRfSwitch_zero_rounds` (satisfiable, zero-round slice);
  teeth `RpRfSwitchToy.switch_is_load_bearing : realProb ≠ functionProb` at
  `ZMod 2 × Fin 1` with two one-block constructions (`realProb = 0`, `functionProb > 0`),
  so no zero switching term can hold in general.
- `[RF-lazy-eager]`: needs the converse of item 1's `TableRooted` (every RO
  entry is the programmed edge of a rooted prefix) threaded through
  `paddedRound_bridge`; with it a fresh primitive edge always sits at a fresh
  RO prefix, so the programmed rate IS the work rate coin.  Teeth are item
  1's `CapacityEventExample.collision_zero_capacity` (on the event the
  worlds may differ, hence conditional).  Not built here.
- `[RF-lazy-sampling]`: a pushforward along adaptively selected fresh keys
  (`uniformProb_pushforward_le` in `Selvage/Depth.lean` is the counting
  kernel).  Not built here.
- `[POSEIDON2-perm-ideal]`: witness `poseidon2PermutationIdeal_one` (`gap := 1`,
  the vacuous floor); teeth = any structural distinguisher for deployed
  Poseidon2 (cryptanalysis, not a Lean fact — stated, not claimed).

**Proved: the capacity event paid ONCE across two hops, and the padded class
of `hrom` derived through item 1's event:**

```lean
theorem lazyProb_sub_deferredProb_abs_le (hsafe) (hagree : PaddedLazyEagerAgreeOffCollision …) :
    |lazyProb … - deferredProb …| ≤ paddedCapacityError (paddedTranscriptPrimitiveWork statement receipt)

theorem paddedRomBound_of_crossings (hsafe) (hswitch) (hsampling) (hagree) (hdeferred) :
    |realProb D (0, 0) - idealProb D (0, 0)|
      ≤ BaseFoldPoseidon2Rom.romError (paddedTranscriptPrimitiveWork statement receipt)
-- file 3: paddedRomBound_of_three_crossings drops hdeferred.
```

## 3. The deployed ledger, every term visible

```lean
theorem deployed_rom_rejection_ledger (gap) (hgap : Poseidon2PermutationIdeal gap) … :
    |deployedIndicator statement receipt verdict - idealProb D (0, 0)| +
      uniformProb (Fin queryCount → Digest) QuerySeedRejection
      ≤ crossingsError gap (paddedTranscriptPrimitiveWork statement receipt) queryCount

theorem deployedPaddedAcceptedRawLedger … (same raw-IOR hypotheses as strictPaddedAcceptedRawRomLedger;
    hrom replaced by hgap hswitch hsampling hagree hdeferred) :
    uniformProb ((Fin m → E) × AcceptedSeedFamily queryCount) (raw accepted-seed false accept) +
      |deployedIndicator … - idealProb D (0, 0)| +
      uniformProb (Fin queryCount → Digest) QuerySeedRejection
      ≤ (m : Real) * (3 / Fintype.card E) + (1 - tau) ^ queryCount
          + uniformProb (…) (FriRawAdaptiveEquivocates …)
          + crossingsError gap (paddedTranscriptPrimitiveWork statement receipt) queryCount
```

i.e. `deployedError = algebraic m·3/|E| + miss (1−τ)^q + retained Merkle
equivocation + Poseidon2 gap + switch W²/p¹⁶ + capacity 2W²/p⁸ (once) + q/p`.

## 4. `[DEFERRED-ideal-exact]` closed (file 3)

```lean
theorem paddedIdealRun_ans (hsafe) :
    (idealRun D (0, 0) coins).ans = List.ofFn (idealRateTrace coins)   -- idealRateTrace coins r := .rate (coins r).1
theorem paddedIdealProb_eq (hsafe) : idealProb D (0, 0) = uniformProb (Fin (m + queryCount) → Rate) (rateVerdict verdict)
theorem paddedDeferredProb_eq (hsafe) : deferredProb … = uniformProb (Fin (m + queryCount) → Rate) (rateVerdict verdict)
theorem paddedDeferredIdealExact (hsafe) : PaddedDeferredIdealExact statement receipt verdict
def paddedOffBadWitness (hsafe) :
    PrefixHybridIdealOffBadWitness Rate Cap (work := paddedTranscriptPrimitiveWork statement receipt) D (0, 0)
  -- bad := PaddedCapacityCollisionRun; deferredAccept := reindexed deferred run;
  -- agree_off_bad := item 1's bridge; deferred_probability_exact := this module.
```

The ideal side is the same induction as the landed
`paddedDeferredStateNat_head_semantics`, on `idealStateNat`
(`SpongeIndiffOffBadRun`); the probability identity is
`uniformProb_comp_injective` along the injective segment-head map
(`paddedSegmentHead_injective`) plus `splitWorkCoins`/`uniformProb_prod_snd`.
The tree's own off-bad interface (`SpongeIndiffWorkStream`) is thereby
inhabited for every padded receipt distinguisher.

## 5. Codec binding (file 2)

A `FramedCodec α` (encode + parser + framing law
`parse (encode a ++ suffix) = some (a, suffix)`), with `prod`, `iso`, `vec`,
a strict `decode`, and `toLawful : LawfulCodec α`.  Built ONLY from the
landed word/rate codecs plus a base-128 varint for path lengths
(`decodeNat_encodeNat_append`).

```lean
def ext4Codec : LawfulCodec E             def rootCodec : LawfulCodec Digest
def pathCodec : LawfulCodec (List Digest) def openingCodec : LawfulCodec Opening
def roundMessageCodec : LawfulCodec RoundMessage
def statementCodec (m) : LawfulCodec (Statement m)
def receiptCodec (m queryCount) : LawfulCodec (Receipt m queryCount)

-- Ext4 bound to the proved field semantics
theorem encodeRate_extBlock (value : E) :
    encodeRate (extBlock value) = ext4Framed.encode value ++ encodeFields (List.ofFn fun _ : Fin 4 => (0 : F))
theorem ext4_decode_eq_rateChallenge (value : E) :
    ext4Framed.decode (ext4Framed.encode value) = some (rateChallenge (extBlock value))
theorem ext4_noncanonical_word_refused :
    ext4Framed.decode (encodeNatLE4 modulus ++ encodeFields [0, 0, 0]) = none        -- falsifier

-- root bound to the landed lawful rate codec
theorem digestFramed_decode_eq_decodeRate (bytes) : digestFramed.decode bytes = decodeRate bytes
theorem root_trailing_refused (root) (byte) : digestFramed.decode (digestFramed.encode root ++ [byte]) = none

-- path bound to the proved Merkle semantics
theorem merkle_path_bytes_verify_iff (root index value path) :
    (∃ decoded, pathFramed.decode (pathFramed.encode path) = some decoded ∧
        (BinaryMerkle.openingScheme hashSuite k).verifyOpen root index value decoded) ↔
      (BinaryMerkle.openingScheme hashSuite k).verifyOpen root index value path
theorem merkle_path_extra_sibling_refused (hpath : path.length = k) :
    ¬ (BinaryMerkle.openingScheme hashSuite k).verifyOpen root index value (path ++ [sibling])  -- recompute fails closed
theorem path_length_tamper_refused (path) :
    pathFramed.decode (encodeNat (path.length + 1) ++ encodeRates path) = none

-- whole receipt bound to acceptance
def AcceptsBytes T st hmell statement queryCount bytes : Prop :=
  ∃ receipt, (receiptFramed m queryCount).decode bytes = some receipt ∧ Accepts T st hmell statement receipt
theorem bcs_accept_bytes_iff (receipt) :
    AcceptsBytes T st hmell statement queryCount ((receiptFramed m queryCount).encode receipt) ↔
      Accepts T st hmell statement receipt
theorem acceptsBytes_trailing_refused (hsuffix : suffix ≠ []) :
    ¬ AcceptsBytes … ((receiptFramed m queryCount).encode receipt ++ suffix)
theorem tamperTerminalRoot_bytes_ne (hne : root ≠ receipt.terminalRoot) :
    encode (tamperTerminalRoot receipt root) ≠ encode receipt
theorem acceptsBytes_terminalRoot_tamper_refused (hne : root ≠ receipt.terminalRoot)
    (haccept : Accepts T st hmell statement receipt) :
    ¬ AcceptsBytes … ((receiptFramed m queryCount).encode (tamperTerminalRoot receipt root))
```

The terminal-root tamper is refused by `RootsExact` (the root at index `m`
must equal `st.rootAt receipt.challenge m`); the trailing-byte tamper by
strict framing.  Not claimed: native realization of these decoders, that
this layout is the production wire format, anything about hash security.

## 6. What closed vs. what is named (summary)

Closed: the numeric identification and the double-count exhibit; the
eager/deferred probability hop through item 1; capacity paid once across
the lazy/eager/deferred hops given the pointwise named hypothesis; the
padded class of `hrom` derived from the three named hops; the deployed
ledger in one expression with the raw-IOR terms; `[DEFERRED-ideal-exact]`
and the landed off-bad witness; all codecs, their field/Merkle bindings,
`bcs_accept_bytes_iff`, and byte-level falsifiers.

Named (docstring obligations with ATLAS fields, `def : Prop`):
`[RP-RF-switch]` (`PaddedRpRfSwitch`), `[RF-lazy-sampling]`
(`PaddedLazyFunctionSampling`), `[RF-lazy-eager]`
(`PaddedLazyEagerAgreeOffCollision`), `[POSEIDON2-perm-ideal]`
(`Poseidon2PermutationIdeal gap`, its number cryptanalytic).

Honesty items: the RP/RF switch's proper error is the `W²/p¹⁶` term, not
the capacity term — the brief's phrasing conflated them; the capacity term
is the RF→ideal (simulator) hop, and this note keeps them apart.  The
deployed world's "probability" is an indicator (a fixed function has no
randomness), which is exactly why `[POSEIDON2-perm-ideal]` is a heuristic
assumption about a fixed object.

## 7. For the coordinator

- Add `import Selvage.BaseFoldBcsCrossings`, `import Selvage.BaseFoldBcsReceiptCodec`,
  `import Selvage.BaseFoldBcsDeferredIdeal` to `Selvage.lean` (not done: coordinator root).
- The row's "current coupling is conditional on `PaddedEagerLastRateRun`" can
  now read: conditional on `¬PaddedCapacityCollisionRun` + routing safety
  (item 1), priced once, with the RP/RF and lazy-sampling hops named and the
  deferred/ideal hop proved.
