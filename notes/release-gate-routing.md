# Release-gate routing — the routing lemma, the binding control, and what the Stage-0 receipt binds

**2026-09-06. Lane on `/Users/ember/dev/minidregg` branch `main`. ONE new file, untracked, nothing
else touched; not committed, no stash, no `add -A`; `pgrep -f "lake build"` empty before every lake
command of mine; the umbrella never invoked.**

| file | lines | what |
|---|---|---|
| `Assurance/ReleaseGateRouting.lean` | 543 | §1 routing lemma, §2 binding control, §3 the tree (kernel gate shape; Stage-0 receipt as bound evidence), §4 eighteen `#guard_msgs`-pinned axiom footprints |

Elaboration: `lake env lean Assurance/ReleaseGateRouting.lean` — zero diagnostics (no warnings, no
sorry, every pin matches). `scripts/check-import-boundary.sh` OK, `scripts/check-proof-hygiene.sh`
PASS (my untracked file scanned separately with the same awk: no bare `#print axioms`, no `axiom`).
Targeted `lake build Assurance.ReleaseGateRouting`: `✔ [3048/3048] Built Assurance.ReleaseGateRouting (4.7s)`, `Build completed successfully`, olean at `.lake/build/lib/lean/Assurance/ReleaseGateRouting.olean` (nothing upstream rebuilt; `pgrep -f "lake build"` empty before it).
`Assurance.lean` (the coordinator roots) NOT edited — wiring the module into the root is the
coordinator's move.

## 0. The wound, in one paragraph

A host homomorphically computes any function of a private state `s`; a release service reveals one
designated output bit of any resulting ciphertext. "Put private bit 37 into the designated position",
submit, read; `n` submissions read all of `s`. The encryption held throughout. What failed is the
GATE: it accepted a predicate with no evidence that the predicate was the AUTHORIZED transition. The
fix is a gate whose acceptance certifies "this output came from the authorized relation" — a proof
binding a descriptor, which is exactly the tree's Stage-0 receipt. Both halves are theorems.

## 1. The routing lemma (§1, generic)

```lean
abbrev PredicateGate (S : Type) := (S → Bool) → Bool
def Determines (gate : PredicateGate S) : Prop :=
  ∀ s t : S, (∀ f, gate f = true → f s = f t) → s = t
def Separates (gate : PredicateGate S) : Prop :=
  ∀ s t : S, s ≠ t → ∃ f, gate f = true ∧ f s ≠ f t

theorem determines_iff_separates (gate : PredicateGate S) : Determines gate ↔ Separates gate
theorem routing_of_projections {n} (gate : PredicateGate (Fin n → Bool))
    (h : ∀ i, gate (proj n i) = true) : Determines gate
theorem routing_of_accept_all {n} (gate : PredicateGate (Fin n → Bool))
    (h : ∀ f, gate f = true) : Determines gate
theorem hostReconstruct_exact {n} (s : Fin n → Bool) : hostReconstruct n (fun f => f s) = s   -- rfl
theorem single_predicate_not_determining {n} (hn : 2 ≤ n) (gate) (f₀)
    (hsingle : ∀ f, gate f = true → f = f₀) : ¬ Determines gate                         -- pigeonhole
theorem single_gate_two_states_one_bit :
    singleGate (proj 2 0) (proj 2 0) = true ∧ (![true, true] : Fin 2 → Bool) ≠ ![true, false] ∧
    proj 2 0 ![true, true] = proj 2 0 ![true, false] ∧ ¬ Determines (singleGate (proj 2 0)) ∧
    Determines (fun _ => true : PredicateGate (Fin 2 → Bool))
```

`releasedView_eq_iff` makes `Determines` literally "the released view is injective in the state".
The sharp form is the iff: released bits determine `s` ⟺ the accepted class separates points;
projections separate (`funext`), so an all-accepting gate — or one accepting merely the `n`
projections — leaks everything; `hostReconstruct` is the attack as a program (one `rfl`).

ATLAS fields — **satisfiable**: `accept_all_gate_exists n` (a gate accepting every projection
exists and `Determines` fires on it). **teeth**: `single_predicate_not_determining` — a gate
accepting ≤ 1 predicate cannot determine a state of ≥ 2 bits (`Fintype.exists_ne_map_eq_of_card_lt`,
`2 < 2^n`); pinned at `n = 2` with both poles on one carrier. **premise-inhabitation**: `Fin n → Bool`
inhabited; `singleGate` inhabits the ≤ 1 hypothesis.

## 2. The binding control (§2)

```lean
abbrev AuthorizedRelation (S O : Type) := S → S → O → Prop
def BindingGate {E S O} (R : AuthorizedRelation S O) (stateOf : E → S) (outOf : E → O)
    (gate : E → Bool) : Prop := ∀ e, gate e = true → ∃ s', R (stateOf e) s' (outOf e)
def PublicOnly {S O Pub} (R) (π : S → Pub) (h : Pub → O) : Prop := ∀ s s' o, R s s' o → o = h (π s)

theorem routing_refused (hbind : BindingGate R stateOf outOf gate) (hpub : PublicOnly R π h)
    (e : E) (hne : outOf e ≠ h (π (stateOf e))) : gate e = false
theorem binding_release_public_only (hbind) (hpub) (e e' : E) (he : gate e = true)
    (he' : gate e' = true) (hπ : π (stateOf e) = π (stateOf e')) : outOf e = outOf e'
```

`binding_release_public_only` is the gate-level twin of `Kernel/PrivateTurn`'s
`privateTurn_public_indistinguishable`: there the public VIEW is blind to the witness, here the
RELEASE is. It is precisely the routing lemma's premise failing — the accepted class does not
separate privately-differing states.

Concrete (`TwoBit`, carrier `Fin 2 → Bool`, coordinate 0 designated, coordinate 1 private,
`R s s' o := s' = s ∧ o = s 0`, `gate e := decide (e.out = e.state 0)`): **premise-inhabitation**
`gate_binding : BindingGate R …`, `R_publicOnly`; **satisfiable** `honest_accepted` (`⟨![false,true],
false⟩` accepted); **teeth** `routed_refused` — "output := s 1" at `![false, true]` refused through the
generic lemma with the side condition `decide`d; `private_bit_not_released` — `![false,true]` and
`![false,false]` both accepted with the SAME output while differing at coordinate 1.

## 3. The tree (§3)

### (i) Kernel — `Kernel/PrivateEscrowSettlement`

```lean
theorem acceptable_pins_named_relation (b : EvidenceBinding) (h : b.Acceptable) :
    b.pins.proofSuiteId ≠ ⟨0⟩ ∨
      (b.mode = .sharedMpc ∧ b.pins = .zero ∧ b.protocolId ≠ ⟨0⟩ ∧ b.federationId ≠ ⟨0⟩)
theorem settlement_is_binding_gate :
    BindingGate (E := Settlement Source M portal authState) (fun (fill : Fill M portal authState) _ o => o = fill.base)
      (fun st => st.fill) (fun st => st.sealed.claim.releasedBase) (fun _ => true)
theorem settlement_release_public_only (st₁ st₂ : Settlement Source M portal authState)
    (h : st₁.fill.base = st₂.fill.base) : st₁.sealed.claim.releasedBase = st₂.sealed.claim.releasedBase
```

`EvidenceBinding.Acceptable` is the kernel's binding-shaped gate: acceptance pins a NAMED relation
(a nonzero suite id, or declared MPC with nonzero protocol/federation and zero pins); the kernel's
own routing refusal is `note_or_bfv_zero_suite_not_acceptable`. `Settlement` is a `BindingGate` by
TYPE — `claimBound.releaseExact` forces `releasedBase = fill.base` — and the generic lemma applied
to the REAL kernel type gives: two settlements over fills of equal base release equal base, whatever
their sealed private computations. Premise-inhabitation of `Settlement` is the tree's
`PrivateEscrowSettlementJoin.Witness.settlement_nonempty` (cited, not imported).

### (ii) Stage 0 — `Compiler/CommittedTerminalFiatShamir`

```lean
noncomputable abbrev stage0Reduction := gateReduction S.commit evmAddDescriptor (bitCorner 13) _
theorem stage0_relation_is_descriptor (rt y : Fin 4131 → BabyBear) :
    stage0Reduction.R () rt y () ↔ (y = rt ∧ descriptorHolds evmAddDescriptor (traceOf y))   -- Iff.rfl
theorem stage0_statement_carries_word (rc : FsReceipt (Fin 4131 → BabyBear) 4131 13) :
    (rc.output …).stmt.y = rc.word ∧ (rc.output …).stmt.x = rc.root                            -- rfl

structure Stage0Evidence where (X Y Z : ℕ) (word : Fin 4131 → BabyBear)
def stage0IdealGate (e) : Bool := decide (e.X < 2^256) && decide (e.Y < 2^256) && decide (e.Z < 2^256)
  && decide (∀ i : Fin 48, traceOf e.word i.1 = encodeBoundary e.X e.Y e.Z i)
  && decide (descriptorHolds evmAddDescriptor (traceOf e.word))
def stage0Relation : AuthorizedRelation (ℕ × ℕ) ℕ := fun xy xy' z => xy' = xy ∧ z = (xy.1 + xy.2) % 2^256

theorem stage0_released_output_forced (X Y Z) (hX hY hZ : _ < 2^256) (wv : ℕ → BabyBear)
    (hpin : ∀ i : Fin 48, wv i.1 = encodeBoundary X Y Z i) (hd : descriptorHolds evmAddDescriptor wv) :
    Z = (X + Y) % 2 ^ 256        -- evmAddDescriptor_means_semantics + fragment_run_eq_iff
theorem stage0IdealGate_binding : BindingGate stage0Relation (fun e => (e.X, e.Y)) Stage0Evidence.Z stage0IdealGate
theorem stage0_routing_refused (e) (hne : e.Z ≠ (e.X + e.Y) % 2 ^ 256) : stage0IdealGate e = false
theorem stage0_forged_z_refused (word) : stage0IdealGate ⟨1, 2, 4, word⟩ = false
theorem stage0_honest_accepted (X Y) (hX hY) :
    stage0IdealGate ⟨X, Y, (X + Y) % 2 ^ 256, wordOf (evmAddCandidate X Y)⟩ = true
theorem stage0_deployed_gate_accepts_honest (X Y) (hX hY) :
    ∃ r, fsCheck S.commit evmAddDescriptor (bitCorner 13) _ O (fsProve … O (S.commit w) w) = .ok r  -- w := wordOf (evmAddCandidate X Y)
theorem stage0Receipt_is_bound_evidence :
    (∀ rc r, fsCheck S.commit evmAddDescriptor (bitCorner 13) _ O rc = .ok r →
        fiatShamir stage0Reduction 0 O (rc.output …) = some ((), fun _ => ())) ∧
    FsStraightlineKnowledgeSoundness stage0Reduction Set.univ
      (fun _s t _δ => ((t : ℝ) + (13 + 1)) * (0 + (4148 - 1 : ℕ) / 2013265921^6 + 13 * (1 / 2013265921^6)))
```

**Exactly what the Stage-0 receipt binds.** The relation, definitionally (`Iff.rfl`): the root IS
the word (`S = idealCommitment`) and `evmAddDescriptor` holds on the word. Through the descriptor,
the released `Z` is FORCED to be `(X + Y) mod 2^256` for the public `(X, Y)` the statement names —
no assignment of the 4,083 non-public wires routes anything else into the output limbs
(`stage0_released_output_forced`; `stage0_forged_z_refused` at the compiled exhibit's own `Z = 4`).
The deployed `fsCheck` at the cSHAKE oracle accepts only what the tree's `fiatShamir` accepts, and
`fiatShamir` accepts a statement outside that relation with probability ≤ `(t + 14) · 4160/p^6`
(`< 2^-173` per `(t+14)`, `stage0Price_value`) against a `t`-query adversary in the lazily-sampled ROM.
So: BOUND = the descriptor (the authorized transition) + the full word, public prefix included,
up to the FS price, under the ROM (`[FS-ROM]` for the cSHAKE realizing it).

**What it does NOT do.** It does not hide: the entire 4,131-wire word is the FS statement's implicit
instance (`stage0_statement_carries_word`, `rfl`), read in full by `gateVerify`, hashed by the
oracle (`encodeRoot` — the root IS the word). At Stage 0 there is no private half at all. It does
not certify currency: nothing in `R s s' o` says `s` is the current state.

ATLAS fields — **satisfiable**: `stage0_honest_accepted` (ideal gate) and
`stage0_deployed_gate_accepts_honest` (deployed gate, `fsProve_complete` at Stage 0 — the evidence
type is inhabited by an ACCEPTED receipt, not just data). **teeth**: `stage0_routing_refused`,
`stage0_forged_z_refused`. **premise-inhabitation**: `S : BindingCommitment` is `idealCommitment`
(binding proved, no axiom); `hpin`/`hd` inhabited by `evmAddCandidate_pins`/`evmAddCandidate_holds`.

## 4. Residuals named

* `[RELEASE-hiding]` — the receipt binds, it does not hide. Bound AND hiding needs the word out of the
  statement (`[CT-merkle-profile]`/`[FS-BCS]`: a root hashed, binding load-bearing under
  `[COMMIT-CR]`) plus a hiding argument (`Assurance/PrivateTurn` masked openings; `[ZK-RBR-game]`).
* `[RELEASE-continuity]` — a bound gate does not prevent replaying a stale but valid state; a gate
  that is a function of the evidence alone accepts the replay as it accepted the original. The tree's
  continuity objects, by name, not imported: `Kernel/DurableDataIntent.StableNullifier`,
  `Kernel/DurableCommitProtocol.Intent.nullifiersFreshCheck` (in `preflight`),
  `Kernel/PrivateEscrowSettlement.Settlement.installed_rekey_nullifier_not_fresh` and
  `Claim.computationNullifier`, `Kernel/State.UKey.nullifier`.
* Prompt named `Kernel/PrivateTurn`'s docstring as carrying "Clear/Shielded/Dark" — that vocabulary is
  not in the tree (`grep -rn Shielded Kernel/` empty); the file's actual model is `Pub × Priv` +
  `publicView`, cited as such.

## 5. Pins (all `#guard_msgs (whitespace := lax) in #print axioms …`, all matching)

`determines_iff_separates`, `single_predicate_not_determining`, `single_gate_two_states_one_bit`,
`settlement_release_public_only`, `stage0_relation_is_descriptor`, `stage0_released_output_forced`,
`stage0IdealGate_binding`, `stage0_routing_refused`, `stage0_forged_z_refused`, `stage0_honest_accepted`,
`stage0_deployed_gate_accepts_honest`, `stage0Receipt_is_bound_evidence` — `[propext, Classical.choice,
Quot.sound]`; `routing_refused`, `TwoBit.routed_refused`, `TwoBit.private_bit_not_released` —
`[propext]`; `routing_of_projections` — `[Quot.sound]`; `binding_release_public_only`,
`acceptable_pins_named_relation` — no axioms. No `sorryAx` anywhere.

One proof-engineering note worth keeping: on `stage0_honest_accepted` a `show`/`exact`/`simp only`
against the concrete `Stage0Evidence` literal sends the unifier into lazy delta on
`decide (descriptorHolds evmAddDescriptor (traceOf (wordOf (evmAddCandidate X Y))))` and it unfolds
the 3,298-gate `fillAux` (max recursion). `unfold` + syntactic `rw [decide_eq_true …]` + `rfl` is
the shape that works; the file says so in a comment at the site.
