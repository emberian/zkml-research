/-
# Selvage.BaseFoldBcsCapacityEvent — the exact capacity event closes the eager coupling

`BaseFoldBcsRunSchedule` couples the eager prefix-programmed run of the padded
BaseFold schedule with the deferred ideal run under the structural event
`PaddedEagerTerminalFreshRun`: every reached construction may replay shared
proper-prefix edges but must find its own terminal primitive edge absent.
That event was left unpriced.

This module prices it.  The work vector is split into its rate and capacity
coordinates; the exact capacity event is the rooted-path collision
`CapacityPathCollision` — while a construction walks its message from the IV,
a freshly programmed edge receives a capacity coin that the primitive table
already mentions (the IV, an input, or an output); and the deterministic
bridge proves that absence of this event, together with the already proved
prefix-free routing, yields `PaddedEagerTerminalFreshRun`.  The bridge runs
through the landed `UniquePaths` invariant of `Selvage.SpongeIndiff` and a
table-rooting invariant (`TableRooted`): every table edge is the edge of a
rooted prefix whose RO value is the edge's rate, and that prefix belongs to
an already issued public message or to the current walk.

Pairwise capacity distinctness is NOT the event.  It is only the pricing
witness: the exact event implies `CapBad {iv.2}` on the capacity coordinate
(`paddedCapacityCollisionRun_capBad`), so the landed `capBad_le` transports
to `2·W²/|Cap|` at the padded receipt work `W`.  That term is then charged
into the existing strict ROM/sampling ledger.

Covered scope: the eager/deferred coupling's bad event on the exact work
space of one fixed padded receipt.  Not covered: the random-permutation /
random-function switch, deployed Poseidon2 idealisation, and receipt/path
codecs (queue item 2).
-/

import Selvage.BaseFoldBcsRunSchedule
import Selvage.BaseFoldBcsStrictRomLedger

namespace Minidregg.Selvage

/-! ## The exact rooted-path capacity event along one construction walk -/

section CapacityWalk

variable {Rate Cap : Type} [AddCommGroup Rate] [DecidableEq Rate]

/-- The exact rooted-path capacity collision along one construction walk.
Replayed proper-prefix edges consume their coins without programming and
cannot collide.  A freshly programmed edge collides exactly when its
capacity coin is already mentioned by the primitive table — the IV, an
input, or an output (`capsOf`).  Malformed coin lists never collide; the
padded run always supplies exactly one pair per block. -/
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

/-- Every primitive-table entry is the edge of a rooted prefix whose lazy RO
value is the entry's rate, and that prefix is admissible.  Together with
`UniquePaths` this pins each table edge to ONE public message prefix. -/
def TableRooted (iv : Rate × Cap) (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (admissible : List Rate → Prop) : Prop :=
  ∀ entry ∈ primitive.log,
    ∃ (path : List Rate) (block : Rate) (node : Rate × Cap),
      walkFrom primitive iv path = some node ∧
        entry.1 = (node.1 + block, node.2) ∧
        ro.lookup (path ++ [block]) = some entry.2.1 ∧
        admissible (path ++ [block])

/-- Prefixes admissible during a walk: an already issued message prefix, or
a prefix of the part of the current message walked so far. -/
def WalkAdmissible (issued : List Rate → Prop) (seen : List Rate)
    (μ : List Rate) : Prop :=
  issued μ ∨ μ <+: seen

/-- Every capacity the table mentions is the IV's or an already consumed
capacity coordinate. -/
def CapsConsumed (iv : Rate × Cap)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (consumed : Cap → Prop) : Prop :=
  ∀ c ∈ capsOf primitive iv, c = iv.2 ∨ consumed c

omit [DecidableEq Rate] in
theorem tableRooted_mono {iv : Rate × Cap} {ro : Oracle (List Rate) Rate}
    {primitive : Oracle (Rate × Cap) (Rate × Cap)}
    {admissible admissible' : List Rate → Prop}
    (himp : ∀ μ, admissible μ → admissible' μ)
    (hrooted : TableRooted iv ro primitive admissible) :
    TableRooted iv ro primitive admissible' := by
  intro entry hentry
  obtain ⟨path, block, node, hwalk, hkey, hro, hadm⟩ := hrooted entry hentry
  exact ⟨path, block, node, hwalk, hkey, hro, himp _ hadm⟩

omit [AddCommGroup Rate] [DecidableEq Rate] in
theorem walkAdmissible_mono {issued : List Rate → Prop}
    {seen seen' : List Rate} (hle : seen <+: seen') (μ : List Rate)
    (h : WalkAdmissible issued seen μ) : WalkAdmissible issued seen' μ :=
  h.imp_right fun hμ => hμ.trans hle

omit [AddCommGroup Rate] [DecidableEq Rate] in
theorem capsConsumed_mono {iv : Rate × Cap}
    {primitive : Oracle (Rate × Cap) (Rate × Cap)}
    {consumed consumed' : Cap → Prop}
    (himp : ∀ c, consumed c → consumed' c)
    (hcons : CapsConsumed iv primitive consumed) :
    CapsConsumed iv primitive consumed' := by
  intro c hc
  exact (hcons c hc).imp_right (himp c)

omit [DecidableEq Rate] in
/-- Extending a successful walk by one recorded edge. -/
theorem walkFrom_snoc {primitive : Oracle (Rate × Cap) (Rate × Cap)}
    {iv node next : Rate × Cap} {path : List Rate} {block : Rate}
    (hpath : walkFrom primitive iv path = some node)
    (hlookup : primitive.lookup (node.1 + block, node.2) = some next) :
    walkFrom primitive iv (path ++ [block]) = some next := by
  rw [walkFrom_append, hpath]
  show walkFrom primitive node [block] = some next
  rw [walkFrom_cons, hlookup]
  rfl

omit [DecidableEq Rate] in
/-- A rooted node's capacity is mentioned by the table. -/
theorem rooted_cap_mem {primitive : Oracle (Rate × Cap) (Rate × Cap)}
    {iv node : Rate × Cap} {path : List Rate}
    (hpath : walkFrom primitive iv path = some node) :
    node.2 ∈ capsOf primitive iv :=
  isPath_cap_mem (p := (path, node.1)) (c := node.2) (by exact hpath)

omit [DecidableEq Rate] in
/-- One fresh programming step preserves table rooting: old entries keep
their rooted prefixes through the handler frame laws, and the new entry is
rooted at the current node by the current block. -/
theorem tableRooted_respond (iv : Rate × Cap) {ro : Oracle (List Rate) Rate}
    {primitive : Oracle (Rate × Cap) (Rate × Cap)}
    {admissible : List Rate → Prop}
    (hrooted : TableRooted iv ro primitive admissible)
    {node : Rate × Cap} {path : List Rate}
    (hnode : walkFrom primitive iv path = some node)
    (block rateCoin : Rate) (capacityCoin : Cap)
    (hedge : primitive.lookup (node.1 + block, node.2) = none)
    (hadm : admissible (path ++ [block])) :
    TableRooted iv (ro.respond (path ++ [block]) rateCoin).2
      (primitive.respond (node.1 + block, node.2)
        ((ro.respond (path ++ [block]) rateCoin).1, capacityCoin)).2
      admissible := by
  intro entry hentry
  rw [Oracle.respond_fresh_log hedge] at hentry
  rcases List.mem_append.mp hentry with hold | hnew
  · obtain ⟨path', block', node', hwalk, hkey, hro, hadm'⟩ :=
      hrooted entry hold
    exact ⟨path', block', node', walkFrom_respond _ _ hwalk, hkey,
      Oracle.lookup_respond_some hro _ _, hadm'⟩
  · rw [List.mem_singleton] at hnew
    subst hnew
    exact ⟨path, block, node, walkFrom_respond _ _ hnode, rfl,
      Oracle.lookup_respond_self ro _ rateCoin, hadm⟩

omit [AddCommGroup Rate] [DecidableEq Rate] in
/-- One fresh programming step at a rooted key adds exactly the programmed
capacity to the consumed footprint. -/
theorem capsConsumed_respond (iv : Rate × Cap)
    {primitive : Oracle (Rate × Cap) (Rate × Cap)} {consumed : Cap → Prop}
    (hcons : CapsConsumed iv primitive consumed) {key value : Rate × Cap}
    (hkey : key.2 = iv.2 ∨ consumed key.2)
    (hedge : primitive.lookup key = none) :
    CapsConsumed iv (primitive.respond key value).2
      (fun c => consumed c ∨ c = value.2) := by
  intro c hc
  unfold capsOf at hc
  rw [Oracle.respond_fresh_log hedge] at hc
  simp only [List.map_append, List.map_cons, List.map_nil, List.mem_cons,
    List.mem_append, List.mem_nil_iff, or_false] at hc
  rcases hc with hiv | (hin | hkeyc) | (hout | hval)
  · exact Or.inl hiv
  · exact (hcons c (List.mem_cons_of_mem _ (List.mem_append_left _ hin))).imp_right
      Or.inl
  · subst hkeyc
    exact hkey.imp_right Or.inl
  · exact (hcons c (List.mem_cons_of_mem _ (List.mem_append_right _ hout))).imp_right
      Or.inl
  · exact Or.inr (Or.inr hval)

/-- **Consumed-coordinate invariant along a walk.**  Whatever a successful
construction programs, every capacity its final table mentions is the IV's,
a previously consumed capacity, or one of this walk's capacity coins.  No
freshness premise: this holds through collisions too. -/
theorem programPrefixes_capsConsumed (iv : Rate × Cap) :
    ∀ (message rateCoins : List Rate) (capacityCoins : List Cap)
      (ro : Oracle (List Rate) Rate)
      (primitive : Oracle (Rate × Cap) (Rate × Cap))
      (state : Rate × Cap) (seen : List Rate) (consumed : Cap → Prop)
      (result : PrefixProgramState Rate Cap),
      CapsConsumed iv primitive consumed →
      walkFrom primitive iv seen = some state →
      programPrefixes ro primitive state seen message rateCoins capacityCoins =
        some result →
      CapsConsumed iv result.primitive
        (fun c => consumed c ∨ c ∈ capacityCoins) := by
  intro message
  induction message with
  | nil =>
      intro rateCoins capacityCoins ro primitive state seen consumed result
        hcons _ hrun
      cases rateCoins <;> cases capacityCoins <;>
        simp [programPrefixes] at hrun
      subst result
      exact capsConsumed_mono (fun c hc => Or.inl hc) hcons
  | cons block rest ih =>
      intro rateCoins capacityCoins ro primitive state seen consumed result
        hcons hstate hrun
      cases rateCoins with
      | nil => simp [programPrefixes] at hrun
      | cons rateCoin rateCoins =>
          cases capacityCoins with
          | nil => simp [programPrefixes] at hrun
          | cons capacityCoin capacityCoins =>
              simp only [programPrefixes] at hrun
              cases hedge : primitive.lookup (state.1 + block, state.2) with
              | some edgeValue =>
                  rw [hedge] at hrun
                  simp only at hrun
                  by_cases hagree :
                      edgeValue.1 =
                        (ro.respond (seen ++ [block]) edgeValue.1).1
                  · rw [if_pos hagree] at hrun
                    have htail := ih rateCoins capacityCoins
                      (ro.respond (seen ++ [block]) edgeValue.1).2 primitive
                      edgeValue (seen ++ [block]) consumed result hcons
                      (walkFrom_snoc hstate hedge) hrun
                    refine capsConsumed_mono (fun c hc => ?_) htail
                    exact hc.imp_right (List.mem_cons_of_mem _)
                  · rw [if_neg hagree] at hrun
                    contradiction
              | none =>
                  rw [hedge] at hrun
                  have htailRun :
                      programPrefixes (ro.respond (seen ++ [block]) rateCoin).2
                        (primitive.respond (state.1 + block, state.2)
                          ((ro.respond (seen ++ [block]) rateCoin).1,
                            capacityCoin)).2
                        (primitive.respond (state.1 + block, state.2)
                          ((ro.respond (seen ++ [block]) rateCoin).1,
                            capacityCoin)).1
                        (seen ++ [block]) rest rateCoins capacityCoins =
                          some result := by
                    simpa using hrun
                  have hcons' := capsConsumed_respond iv hcons
                    (key := (state.1 + block, state.2))
                    (value := ((ro.respond (seen ++ [block]) rateCoin).1,
                      capacityCoin))
                    (hcons state.2 (rooted_cap_mem hstate)) hedge
                  have hstate' := walkFrom_snoc
                    (walkFrom_respond (state.1 + block, state.2)
                      ((ro.respond (seen ++ [block]) rateCoin).1, capacityCoin)
                      hstate)
                    (Oracle.lookup_respond_self primitive
                      (state.1 + block, state.2)
                      ((ro.respond (seen ++ [block]) rateCoin).1, capacityCoin))
                  have htail := ih rateCoins capacityCoins
                    (ro.respond (seen ++ [block]) rateCoin).2
                    (primitive.respond (state.1 + block, state.2)
                      ((ro.respond (seen ++ [block]) rateCoin).1,
                        capacityCoin)).2
                    (primitive.respond (state.1 + block, state.2)
                      ((ro.respond (seen ++ [block]) rateCoin).1,
                        capacityCoin)).1
                    (seen ++ [block]) _ result hcons' hstate' htailRun
                  refine capsConsumed_mono (fun c hc => ?_) htail
                  rcases hc with (hc | hc) | hc
                  · exact Or.inl hc
                  · exact Or.inr (hc ▸ List.mem_cons_self ..)
                  · exact Or.inr (List.mem_cons_of_mem _ hc)

omit [DecidableEq Rate] in
/-- **The exact event names its coordinate.**  A rooted-path collision along
a walk exhibits the colliding capacity coin's position: it equals the IV's
capacity, an already consumed capacity, or an earlier coin of the same
walk.  This is the deterministic half of the transport to `CapBad`. -/
theorem capacityPathCollision_index (iv : Rate × Cap) :
    ∀ (message rateCoins : List Rate) (capacityCoins : List Cap)
      (ro : Oracle (List Rate) Rate)
      (primitive : Oracle (Rate × Cap) (Rate × Cap))
      (state : Rate × Cap) (seen : List Rate) (consumed : Cap → Prop),
      CapsConsumed iv primitive consumed →
      walkFrom primitive iv seen = some state →
      CapacityPathCollision iv ro primitive state seen message rateCoins
        capacityCoins →
      ∃ k, ∃ hk : k < capacityCoins.length,
        capacityCoins[k] = iv.2 ∨ consumed capacityCoins[k] ∨
          ∃ j, ∃ hj : j < k, capacityCoins[j]'(by omega) = capacityCoins[k] := by
  intro message
  induction message with
  | nil =>
      intro rateCoins capacityCoins ro primitive state seen consumed _ _ hcol
      simp [CapacityPathCollision] at hcol
  | cons block rest ih =>
      intro rateCoins capacityCoins ro primitive state seen consumed hcons
        hstate hcol
      cases rateCoins with
      | nil => simp [CapacityPathCollision] at hcol
      | cons rateCoin rateCoins =>
          cases capacityCoins with
          | nil => simp [CapacityPathCollision] at hcol
          | cons capacityCoin capacityCoins =>
              simp only [CapacityPathCollision] at hcol
              cases hedge : primitive.lookup (state.1 + block, state.2) with
              | some edgeValue =>
                  rw [hedge] at hcol
                  simp only at hcol
                  obtain ⟨k, hk, hcase⟩ := ih rateCoins capacityCoins
                    (ro.respond (seen ++ [block]) edgeValue.1).2 primitive
                    edgeValue (seen ++ [block]) consumed hcons
                    (walkFrom_snoc hstate hedge) hcol
                  refine ⟨k + 1, by simp; omega, ?_⟩
                  simp only [List.getElem_cons_succ]
                  rcases hcase with h | h | ⟨j, hj, hjk⟩
                  · exact Or.inl h
                  · exact Or.inr (Or.inl h)
                  · exact Or.inr (Or.inr ⟨j + 1, by omega, by
                      simpa [List.getElem_cons_succ] using hjk⟩)
              | none =>
                  rw [hedge] at hcol
                  simp only at hcol
                  rcases hcol with hhit | htail
                  · refine ⟨0, by simp, ?_⟩
                    simp only [List.getElem_cons_zero]
                    rcases hcons capacityCoin hhit with h | h
                    · exact Or.inl h
                    · exact Or.inr (Or.inl h)
                  · have hcons' := capsConsumed_respond iv hcons
                      (key := (state.1 + block, state.2))
                      (value := ((ro.respond (seen ++ [block]) rateCoin).1,
                        capacityCoin))
                      (hcons state.2 (rooted_cap_mem hstate)) hedge
                    have hstate' := walkFrom_snoc
                      (walkFrom_respond (state.1 + block, state.2)
                        ((ro.respond (seen ++ [block]) rateCoin).1,
                          capacityCoin) hstate)
                      (Oracle.lookup_respond_self primitive
                        (state.1 + block, state.2)
                        ((ro.respond (seen ++ [block]) rateCoin).1,
                          capacityCoin))
                    obtain ⟨k, hk, hcase⟩ := ih rateCoins capacityCoins
                      (ro.respond (seen ++ [block]) rateCoin).2
                      (primitive.respond (state.1 + block, state.2)
                        ((ro.respond (seen ++ [block]) rateCoin).1,
                          capacityCoin)).2
                      (primitive.respond (state.1 + block, state.2)
                        ((ro.respond (seen ++ [block]) rateCoin).1,
                          capacityCoin)).1
                      (seen ++ [block]) _ hcons' hstate' htail
                    refine ⟨k + 1, by simp; omega, ?_⟩
                    simp only [List.getElem_cons_succ]
                    rcases hcase with h | (h | h) | ⟨j, hj, hjk⟩
                    · exact Or.inl h
                    · exact Or.inr (Or.inl h)
                    · exact Or.inr (Or.inr ⟨0, by omega, by
                        simpa [List.getElem_cons_zero] using h.symm⟩)
                    · exact Or.inr (Or.inr ⟨j + 1, by omega, by
                        simpa [List.getElem_cons_succ] using hjk⟩)

/-- **The deterministic bridge, one walk.**  Under unique rooted paths, a
rooted table, a rooted current node, a full message that no admissible
prefix equals, and NO rooted-path capacity collision, the walk is
replay-compatible terminal-fresh for its last rate coin; moreover any
successful programming of it preserves unique paths and table rooting with
the walked message now admissible. -/
theorem terminalPrimitiveFreshTo_of_noCollision (iv : Rate × Cap)
    (issued : List Rate → Prop) (terminalRate : Rate) :
    ∀ (message rateCoins : List Rate) (capacityCoins : List Cap)
      (ro : Oracle (List Rate) Rate)
      (primitive : Oracle (Rate × Cap) (Rate × Cap))
      (state : Rate × Cap) (seen : List Rate),
      message ≠ [] →
      rateCoins.length = message.length →
      capacityCoins.length = message.length →
      lastRateCoin rateCoins = terminalRate →
      UniquePaths primitive iv →
      TableRooted iv ro primitive (WalkAdmissible issued seen) →
      walkFrom primitive iv seen = some state →
      ¬ issued (seen ++ message) →
      ¬ CapacityPathCollision iv ro primitive state seen message rateCoins
        capacityCoins →
      TerminalPrimitiveFreshTo terminalRate ro primitive state seen message
          rateCoins capacityCoins ∧
        ∀ result,
          programPrefixes ro primitive state seen message rateCoins
              capacityCoins = some result →
            UniquePaths result.primitive iv ∧
              TableRooted iv result.ro result.primitive
                (WalkAdmissible issued (seen ++ message)) := by
  intro message
  induction message with
  | nil =>
      intro _ _ _ _ _ _ hnonempty
      exact absurd rfl hnonempty
  | cons block rest ih =>
      intro rateCoins capacityCoins ro primitive state seen _ hrates hcaps
        hlast hU hrooted hstate hnot hcol
      cases rateCoins with
      | nil => simp at hrates
      | cons rateCoin rateCoins =>
          cases capacityCoins with
          | nil => simp at hcaps
          | cons capacityCoin capacityCoins =>
              have hrates' : rateCoins.length = rest.length := by
                simpa using hrates
              have hcaps' : capacityCoins.length = rest.length := by
                simpa using hcaps
              have hstateCap : state.2 ∈ capsOf primitive iv :=
                rooted_cap_mem hstate
              cases hedge : primitive.lookup (state.1 + block, state.2) with
              | some edgeValue =>
                  -- The replayed edge is rooted; uniqueness pins its prefix.
                  obtain ⟨path, b, node, hwalk, hkey, hro, hadm⟩ :=
                    hrooted _ (Oracle.lookup_mem hedge)
                  simp only [Prod.mk.injEq] at hkey
                  obtain ⟨hkeyRate, hkeyCap⟩ := hkey
                  have hpaths := hU state.2 (seen, state.1) (path, node.1)
                    (by exact hstate)
                    (by
                      show walkFrom primitive iv path = some (node.1, state.2)
                      rw [hkeyCap]
                      exact hwalk)
                  simp only [Prod.mk.injEq] at hpaths
                  obtain ⟨hpath, hrate⟩ := hpaths
                  subst hpath
                  have hb : b = block := by
                    rw [hrate] at hkeyRate
                    exact (add_left_cancel hkeyRate).symm
                  subst b
                  have hroHit : ro.lookup (seen ++ [block]) = some edgeValue.1 :=
                    hro
                  have hreply : ro.respond (seen ++ [block]) edgeValue.1 =
                      (edgeValue.1, ro) :=
                    Oracle.respond_hit hroHit _
                  cases rest with
                  | nil =>
                      exfalso
                      rcases hadm with hissued | hprefix
                      · exact hnot hissued
                      · have := hprefix.length_le
                        simp at this
                  | cons next rest =>
                      have hcol' : ¬ CapacityPathCollision iv ro primitive
                          edgeValue (seen ++ [block]) (next :: rest) rateCoins
                          capacityCoins := by
                        intro h
                        apply hcol
                        simp only [CapacityPathCollision, hedge, hreply]
                        exact h
                      have hnot' : ¬ issued ((seen ++ [block]) ++ next :: rest) := by
                        rw [List.append_assoc, List.singleton_append]
                        exact hnot
                      have hlast' : lastRateCoin rateCoins = terminalRate := by
                        cases rateCoins with
                        | nil => simp at hrates'
                        | cons r rs => simpa [lastRateCoin] using hlast
                      have hih := ih rateCoins capacityCoins ro primitive
                        edgeValue (seen ++ [block]) (by simp) hrates' hcaps'
                        hlast' hU
                        (tableRooted_mono
                          (walkAdmissible_mono (List.prefix_append seen [block]))
                          hrooted)
                        (walkFrom_snoc hstate hedge) hnot' hcol'
                      refine ⟨?_, ?_⟩
                      · simp only [TerminalPrimitiveFreshTo, List.isEmpty_cons,
                          Bool.false_eq_true, ↓reduceIte, hedge, hreply]
                        exact ⟨by trivial, hih.1⟩
                      · intro result hrun
                        simp only [programPrefixes, hedge, hreply,
                          ↓reduceIte] at hrun
                        have := hih.2 result hrun
                        rwa [List.append_assoc, List.singleton_append] at this
              | none =>
                  -- A fresh edge: the capacity coin must miss the table.
                  have hcol' : ¬ (capacityCoin ∈ capsOf primitive iv ∨
                      CapacityPathCollision iv
                        (ro.respond (seen ++ [block]) rateCoin).2
                        (primitive.respond (state.1 + block, state.2)
                          ((ro.respond (seen ++ [block]) rateCoin).1,
                            capacityCoin)).2
                        (primitive.respond (state.1 + block, state.2)
                          ((ro.respond (seen ++ [block]) rateCoin).1,
                            capacityCoin)).1
                        (seen ++ [block]) rest rateCoins capacityCoins) := by
                    intro h
                    apply hcol
                    simp only [CapacityPathCollision, hedge]
                    exact h
                  obtain ⟨hcapFresh, hcolTail⟩ := not_or.mp hcol'
                  have hcapNe : capacityCoin ≠ state.2 := fun h =>
                    hcapFresh (h ▸ hstateCap)
                  have hU' : UniquePaths
                      (primitive.respond (state.1 + block, state.2)
                        ((ro.respond (seen ++ [block]) rateCoin).1,
                          capacityCoin)).2 iv :=
                    uniquePaths_respond_freshOut hU hedge hcapFresh hcapNe
                  have hstate' := walkFrom_snoc
                    (walkFrom_respond (state.1 + block, state.2)
                      ((ro.respond (seen ++ [block]) rateCoin).1, capacityCoin)
                      hstate)
                    (Oracle.lookup_respond_self primitive
                      (state.1 + block, state.2)
                      ((ro.respond (seen ++ [block]) rateCoin).1, capacityCoin))
                  have hrooted' : TableRooted iv
                      (ro.respond (seen ++ [block]) rateCoin).2
                      (primitive.respond (state.1 + block, state.2)
                        ((ro.respond (seen ++ [block]) rateCoin).1,
                          capacityCoin)).2
                      (WalkAdmissible issued (seen ++ [block])) :=
                    tableRooted_respond iv
                      (tableRooted_mono
                        (walkAdmissible_mono (List.prefix_append seen [block]))
                        hrooted)
                      hstate block rateCoin capacityCoin hedge
                      (Or.inr List.prefix_rfl)
                  cases rest with
                  | nil =>
                      have hratesNil : rateCoins = [] :=
                        List.eq_nil_of_length_eq_zero hrates'
                      have hcapsNil : capacityCoins = [] :=
                        List.eq_nil_of_length_eq_zero hcaps'
                      subst hratesNil
                      subst hcapsNil
                      refine ⟨?_, ?_⟩
                      · simp only [TerminalPrimitiveFreshTo, List.isEmpty_nil,
                          ↓reduceIte, true_and]
                        exact ⟨by simpa [lastRateCoin] using hlast, hedge⟩
                      · intro result hrun
                        simp only [programPrefixes, hedge, Option.some.injEq]
                          at hrun
                        subst hrun
                        exact ⟨hU', hrooted'⟩
                  | cons next rest =>
                      have hnot' : ¬ issued ((seen ++ [block]) ++ next :: rest) := by
                        rw [List.append_assoc, List.singleton_append]
                        exact hnot
                      have hlast' : lastRateCoin rateCoins = terminalRate := by
                        cases rateCoins with
                        | nil => simp at hrates'
                        | cons r rs => simpa [lastRateCoin] using hlast
                      have hih := ih rateCoins capacityCoins
                        (ro.respond (seen ++ [block]) rateCoin).2
                        (primitive.respond (state.1 + block, state.2)
                          ((ro.respond (seen ++ [block]) rateCoin).1,
                            capacityCoin)).2
                        (primitive.respond (state.1 + block, state.2)
                          ((ro.respond (seen ++ [block]) rateCoin).1,
                            capacityCoin)).1
                        (seen ++ [block]) (by simp) hrates' hcaps' hlast' hU'
                        hrooted' hstate' hnot' hcolTail
                      refine ⟨?_, ?_⟩
                      · simp only [TerminalPrimitiveFreshTo, List.isEmpty_cons,
                          Bool.false_eq_true, ↓reduceIte, hedge]
                        exact hih.1
                      · intro result hrun
                        simp only [programPrefixes, hedge] at hrun
                        have := hih.2 result hrun
                        rwa [List.append_assoc, List.singleton_append] at this

/-- A successful construction step of the fixed work adapter exposes the
`programConstruction` result whose tables it installs. -/
theorem workHybridStep_constr_program {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (state next : WorkHybridState Rate Cap) (j : Fin q)
    (x : Rate) (xs : List Rate)
    (hquery : D.move state.core.ans = .constr x xs)
    (hstep : workHybridStep D iv state j = .ok next) :
    ∃ result,
      programConstruction iv state.core.ro state.core.primitive (x :: xs)
          ((state.remaining.take (xs.length + 1)).map Prod.fst)
          ((state.remaining.take (xs.length + 1)).map Prod.snd) =
            some result ∧
        next.core.ro = result.ro ∧ next.core.primitive = result.primitive := by
  unfold workHybridStep at hstep
  dsimp only at hstep
  rw [hquery] at hstep
  simp only [SpQuery.primitiveCalls] at hstep
  split at hstep
  · simp only [SpQuery.prefixCoins] at hstep
    split at hstep
    · rename_i coreNext hcore
      injection hstep with hnext
      subst next
      unfold prefixHybridStep at hcore
      rw [hquery] at hcore
      dsimp only at hcore
      split at hcore
      · split at hcore
        · rename_i result hprogram
          injection hcore with hcoreEq
          subst hcoreEq
          exact ⟨result, hprogram, rfl, rfl⟩
        · contradiction
      · contradiction
    · contradiction
  · contradiction

end CapacityWalk

/-! ## Witness and falsifier for the walk-level bridge (ATLAS fields) -/

namespace CapacityEventExample

def iv : ZMod 2 × Fin 3 := (0, 0)

/-- **Falsifier**: with the first capacity coin equal to the IV capacity, the
walk of `[1, 0]` collides at its first fresh edge … -/
theorem collision_zero_capacity :
    CapacityPathCollision iv Oracle.empty Oracle.empty iv [] [1, 0] [1, 0]
      [0, 2] := by
  simp only [CapacityPathCollision, Oracle.lookup_empty]
  left
  simp [capsOf, Oracle.empty, iv]

/-- … and terminal freshness FAILS: the collided capacity closes a cycle
`(1,0) ↦ (1,0)`, so the terminal edge of `[1, 0]` is already present.  The
no-collision hypothesis of the bridge is therefore a constraint. -/
theorem not_terminalFresh_zero_capacity :
    ¬ TerminalPrimitiveFreshTo (lastRateCoin [1, 0]) Oracle.empty
      Oracle.empty iv [] [1, 0] [1, 0] [0, 2] := by
  intro h
  have hro1 : ((Oracle.empty : Oracle (List (ZMod 2)) (ZMod 2)).respond
      [1] 1).1 = 1 :=
    Oracle.respond_fresh_fst (Oracle.lookup_empty _) _
  have hp1 : ((Oracle.empty : Oracle (ZMod 2 × Fin 3) (ZMod 2 × Fin 3)).respond
      (1, 0) (1, 0)).1 = (1, 0) :=
    Oracle.respond_fresh_fst (Oracle.lookup_empty _) _
  have hp1' : ((Oracle.empty : Oracle (ZMod 2 × Fin 3) (ZMod 2 × Fin 3)).respond
      (1, 0) (1, 0)).2.lookup (1, 0) = some (1, 0) := by
    rw [Oracle.lookup_respond_self, hp1]
  simp only [TerminalPrimitiveFreshTo, Oracle.lookup_empty, iv, zero_add,
    List.nil_append, List.isEmpty_cons, List.isEmpty_nil, Bool.false_eq_true,
    ↓reduceIte, hro1, hp1, add_zero, hp1'] at h
  simp at h

/-- **Witness**: distinct nonzero capacities `[1, 2]` on the same walk do not
collide. -/
theorem no_collision_fresh_capacities :
    ¬ CapacityPathCollision iv Oracle.empty Oracle.empty iv [] [1, 0] [1, 0]
      [1, 2] := by
  intro h
  have hro1 : ((Oracle.empty : Oracle (List (ZMod 2)) (ZMod 2)).respond
      [1] 1).1 = 1 :=
    Oracle.respond_fresh_fst (Oracle.lookup_empty _) _
  have hp1 : ((Oracle.empty : Oracle (ZMod 2 × Fin 3) (ZMod 2 × Fin 3)).respond
      (1, 0) (1, 1)).1 = (1, 1) :=
    Oracle.respond_fresh_fst (Oracle.lookup_empty _) _
  have hlk : ((Oracle.empty : Oracle (ZMod 2 × Fin 3) (ZMod 2 × Fin 3)).respond
      (1, 0) (1, 1)).2.lookup (1, 1) = none := by
    rw [Oracle.lookup_respond_ne _ (by decide) _]
    exact Oracle.lookup_empty _
  simp only [CapacityPathCollision, Oracle.lookup_empty, iv, zero_add,
    List.nil_append, hro1, hp1, add_zero, hlk] at h
  rcases h with h | h
  · simp [capsOf, Oracle.empty] at h
  · rcases h with h | h
    · unfold capsOf at h
      rw [Oracle.respond_fresh_log (Oracle.lookup_empty _)] at h
      simp [Oracle.empty] at h
    · exact h

/-- The bridge is non-vacuous: the witness walk is terminal-fresh for its
last rate coin `0`, obtained THROUGH the bridge from empty tables. -/
theorem terminalFresh_fresh_capacities :
    TerminalPrimitiveFreshTo (lastRateCoin [1, 0]) Oracle.empty
      Oracle.empty iv [] [1, 0] [1, 0] [1, 2] :=
  (terminalPrimitiveFreshTo_of_noCollision iv (fun _ => False)
    (lastRateCoin [1, 0]) [1, 0] [1, 0] [1, 2] Oracle.empty Oracle.empty iv []
    (by simp) rfl rfl rfl (uniquePaths_empty iv)
    (fun _ h => absurd h List.not_mem_nil) rfl (fun h => h)
    no_collision_fresh_capacities).1

end CapacityEventExample

/-! ## Work-vector segments: index bookkeeping for the coordinate transport -/

section Segments

variable {α β : Type}

/-- Lossless rate/capacity split of a fixed work vector. -/
def splitWorkCoins (work : Nat) :
    (Fin work → α × β) ≃ ((Fin work → α) × (Fin work → β)) where
  toFun coins := (fun i => (coins i).1, fun i => (coins i).2)
  invFun parts := fun i => (parts.1 i, parts.2 i)
  left_inv coins := by
    funext i
    rfl
  right_inv parts := by
    rcases parts with ⟨rates, caps⟩
    rfl

/-- A member of the capacity segment starting at work index `p` of length
`n` is the capacity of a work coin with index in `[p, p + n)`. -/
theorem segment_mem {work : Nat} (coins : Fin work → α × β) {p n : Nat} {c : β}
    (hmem : c ∈ (((List.ofFn coins).drop p).take n).map Prod.snd) :
    ∃ i : Fin work, p ≤ (i : Nat) ∧ (i : Nat) < p + n ∧ (coins i).2 = c := by
  obtain ⟨a, ha, hac⟩ := List.mem_map.mp hmem
  obtain ⟨k, hk, hka⟩ := List.mem_iff_getElem.mp ha
  have hk' := hk
  simp only [List.length_take, List.length_drop, List.length_ofFn] at hk'
  refine ⟨⟨p + k, by omega⟩, by simp, by simp; omega, ?_⟩
  rw [← hac, ← hka]
  simp [List.getElem_take, List.getElem_drop, List.getElem_ofFn]

/-- Position `k` of the capacity segment starting at work index `p` is the
capacity of work coin `p + k`. -/
theorem segment_getElem {work : Nat} (coins : Fin work → α × β) {p n k : Nat}
    (hk : k < ((((List.ofFn coins).drop p).take n).map Prod.snd).length) :
    ∃ i : Fin work, (i : Nat) = p + k ∧
      ((((List.ofFn coins).drop p).take n).map Prod.snd)[k] = (coins i).2 := by
  have hk' := hk
  simp only [List.length_map, List.length_take, List.length_drop,
    List.length_ofFn] at hk'
  refine ⟨⟨p + k, by omega⟩, rfl, ?_⟩
  simp [List.getElem_take, List.getElem_drop, List.getElem_ofFn]

end Segments

end Minidregg.Selvage

/-! ## The exact event on the padded BaseFold work vector -/

namespace Minidregg.Selvage.BaseFoldBcsCapacityEvent

open Minidregg.Selvage
open Minidregg.Selvage.BaseFoldBcsFiatShamir
open Minidregg.Selvage.BaseFoldBcsPadding
open Minidregg.Selvage.BaseFoldBcsRunSchedule
open Minidregg.Selvage.BaseFoldBcsStrictRomLedger

set_option autoImplicit false

noncomputable section

/-- The rate coordinate of the padded work vector. -/
def paddedRateCoins {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (coins : Fin (paddedTranscriptPrimitiveWork statement receipt) →
      Rate × Cap) :
    Fin (paddedTranscriptPrimitiveWork statement receipt) → Rate :=
  fun i => (coins i).1

/-- The capacity coordinate of the padded work vector. -/
def paddedCapacityCoins {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (coins : Fin (paddedTranscriptPrimitiveWork statement receipt) →
      Rate × Cap) :
    Fin (paddedTranscriptPrimitiveWork statement receipt) → Cap :=
  fun i => (coins i).2

/-- Public messages issued strictly before numeric round `round`. -/
def PaddedIssuedBefore {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (round : Nat) (μ : List Rate) : Prop :=
  ∃ j : Fin (m + queryCount), (j : Nat) < round ∧
    μ <+: paddedPublicMessageSchedule statement receipt j

/-- Capacity coordinates consumed strictly before work index `bound`. -/
def PaddedConsumedCap {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (coins : Fin (paddedTranscriptPrimitiveWork statement receipt) →
      Rate × Cap)
    (bound : Nat) (c : Cap) : Prop :=
  ∃ i : Fin (paddedTranscriptPrimitiveWork statement receipt),
    (i : Nat) < bound ∧ (coins i).2 = c

/-- **The exact run-level capacity event.**  Some reached eager round's
construction walk suffers a rooted-path capacity collision on its actual
work segment.  This is NOT pairwise distinctness of capacity coins: coins
of replayed edges never count, and only the table reachable at that moment
is consulted. -/
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

/-! ### Deterministic run bookkeeping -/

/-- Every reached eager prefix has the static transcript length and the
static unconsumed work suffix (read off the landed classification). -/
theorem paddedWorkHybridStateNat_ok_shape {m queryCount round : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (coins : Fin (paddedTranscriptPrimitiveWork statement receipt) →
      Rate × Cap)
    (hround : round ≤ m + queryCount) {state : WorkHybridState Rate Cap}
    (hstate : paddedWorkHybridStateNat statement receipt verdict coins round
      hround = .ok state) :
    state.core.ans.length = round ∧
      state.remaining = (List.ofFn coins).drop
        (paddedWorkPrefix statement receipt round) := by
  rcases paddedWorkHybridStateNat_classify statement receipt verdict coins
      hround with ⟨state', hstate', hans, _, hremaining⟩ | herror
  · rw [hstate] at hstate'
    injection hstate' with h
    subst h
    exact ⟨hans, hremaining⟩
  · rw [hstate] at herror
    cases herror

/-- Static data of one eager construction round at a reached state: the
selected query, its message, its exact primitive cost, and sufficiency of
the remaining work. -/
theorem paddedRound_data {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (coins : Fin (paddedTranscriptPrimitiveWork statement receipt) →
      Rate × Cap)
    (round : Fin (m + queryCount)) (state : WorkHybridState Rate Cap)
    (hans : state.core.ans.length = round)
    (hremaining : state.remaining =
      (List.ofFn coins).drop (paddedWorkPrefix statement receipt round)) :
    ∃ x xs,
      (paddedConstructionDistinguisher statement receipt verdict).move
          state.core.ans = .constr x xs ∧
        paddedPublicMessageSchedule statement receipt round = x :: xs ∧
        xs.length + 1 = paddedRoundPrimitiveWork statement receipt round ∧
        xs.length + 1 ≤ state.remaining.length := by
  obtain ⟨x, xs, hquery, hmessage⟩ :=
    paddedConstructionQuerySchedule_is_constr statement receipt round
  have hsize : xs.length + 1 =
      paddedRoundPrimitiveWork statement receipt round := by
    simp [paddedRoundPrimitiveWork, hquery]
  refine ⟨x, xs, ?_, hmessage, hsize, ?_⟩
  · rw [paddedConstructionDistinguisher_move_at_length statement receipt
      verdict state.core.ans (by omega)]
    calc
      paddedConstructionQuerySchedule statement receipt
          ⟨state.core.ans.length, by omega⟩ =
          paddedConstructionQuerySchedule statement receipt round := by
        apply congrArg (paddedConstructionQuerySchedule statement receipt)
        exact Fin.ext hans
      _ = .constr x xs := hquery
  · have hsize' : xs.length + 1 =
        paddedRoundPrimitiveWork statement receipt ⟨round, round.isLt⟩ := by
      convert hsize using 1
    rw [hremaining, List.length_drop, List.length_ofFn, hsize']
    have hprefixLe :=
      paddedWorkPrefix_le_final statement receipt (round + 1)
    have hprefixStep :=
      paddedWorkPrefix_succ statement receipt round round.isLt
    omega

/-- **One eager round, bridged.**  At a rooted, path-unique state whose
current walk has no rooted-path capacity collision, the round is
replay-compatible terminal-fresh for its segment-last rate coin, and every
successful step preserves path uniqueness and table rooting with the round's
message now issued. -/
theorem paddedRound_bridge {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (coins : Fin (paddedTranscriptPrimitiveWork statement receipt) →
      Rate × Cap)
    (hsafe : PaddedFullMessageRoutingSafe statement receipt)
    (round : Fin (m + queryCount)) (state : WorkHybridState Rate Cap)
    (hans : state.core.ans.length = round)
    (hremaining : state.remaining =
      (List.ofFn coins).drop (paddedWorkPrefix statement receipt round))
    (hU : UniquePaths state.core.primitive (0, 0))
    (hrooted : TableRooted (0, 0) state.core.ro state.core.primitive
      (PaddedIssuedBefore statement receipt round))
    (hnocol : ¬ CapacityPathCollision (0, 0) state.core.ro
      state.core.primitive (0, 0) []
      (paddedPublicMessageSchedule statement receipt round)
      ((state.remaining.take
        (paddedRoundPrimitiveWork statement receipt round)).map Prod.fst)
      ((state.remaining.take
        (paddedRoundPrimitiveWork statement receipt round)).map Prod.snd)) :
    TerminalPrimitiveFreshTo
        (lastRateCoin ((state.remaining.take
          (paddedRoundPrimitiveWork statement receipt round)).map Prod.fst))
        state.core.ro state.core.primitive (0, 0) []
        (paddedPublicMessageSchedule statement receipt round)
        ((state.remaining.take
          (paddedRoundPrimitiveWork statement receipt round)).map Prod.fst)
        ((state.remaining.take
          (paddedRoundPrimitiveWork statement receipt round)).map Prod.snd) ∧
      ∀ next,
        workHybridStep
            (paddedConstructionDistinguisher statement receipt verdict)
            (0, 0) state round = .ok next →
          UniquePaths next.core.primitive (0, 0) ∧
            TableRooted (0, 0) next.core.ro next.core.primitive
              (PaddedIssuedBefore statement receipt ((round : Nat) + 1)) := by
  obtain ⟨x, xs, hmove, hmessage, hsize, henough⟩ :=
    paddedRound_data statement receipt verdict coins round state hans
      hremaining
  have hlen : (state.remaining.take (xs.length + 1)).length =
      xs.length + 1 := by
    rw [List.length_take]
    omega
  have hnot : ¬ PaddedIssuedBefore statement receipt round (x :: xs) := by
    rintro ⟨j, hj, hprefix⟩
    have hne : round ≠ j := by
      intro h
      subst h
      exact lt_irrefl _ hj
    apply hsafe round j hne
    rw [hmessage]
    exact hprefix
  rw [hmessage, ← hsize] at hnocol ⊢
  have hwalk := terminalPrimitiveFreshTo_of_noCollision (0, 0)
    (PaddedIssuedBefore statement receipt round)
    (lastRateCoin ((state.remaining.take (xs.length + 1)).map Prod.fst))
    (x :: xs)
    ((state.remaining.take (xs.length + 1)).map Prod.fst)
    ((state.remaining.take (xs.length + 1)).map Prod.snd)
    state.core.ro state.core.primitive (0, 0) [] (by simp)
    (by rw [List.length_map, hlen, List.length_cons])
    (by rw [List.length_map, hlen, List.length_cons]) rfl hU
    (tableRooted_mono (fun _ h => Or.inl h) hrooted) rfl hnot hnocol
  refine ⟨hwalk.1, ?_⟩
  intro next hstep
  obtain ⟨result, hprogram, hro, hprim⟩ :=
    workHybridStep_constr_program _ _ state next round x xs hmove hstep
  have hrun : programPrefixes state.core.ro state.core.primitive (0, 0) []
      (x :: xs)
      ((state.remaining.take (xs.length + 1)).map Prod.fst)
      ((state.remaining.take (xs.length + 1)).map Prod.snd) = some result := by
    simpa [programConstruction] using hprogram
  obtain ⟨hU', hrooted'⟩ := hwalk.2 result hrun
  rw [hro, hprim]
  refine ⟨hU', tableRooted_mono (fun μ h => ?_) hrooted'⟩
  rcases h with ⟨j, hj, hprefix⟩ | hprefix
  · exact ⟨j, by omega, hprefix⟩
  · refine ⟨round, by simp, ?_⟩
    rw [hmessage]
    simpa using hprefix

/-- **The run invariant.**  Under prefix-free routing and absence of the
exact capacity event, every reached eager prefix has a path-unique primitive
table rooted at the messages issued so far. -/
theorem paddedWorkHybridStateNat_rooted {m queryCount round : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (coins : Fin (paddedTranscriptPrimitiveWork statement receipt) →
      Rate × Cap)
    (hsafe : PaddedFullMessageRoutingSafe statement receipt)
    (hnocol : ¬ PaddedCapacityCollisionRun statement receipt verdict coins)
    (hround : round ≤ m + queryCount) {state : WorkHybridState Rate Cap}
    (hstate : paddedWorkHybridStateNat statement receipt verdict coins round
      hround = .ok state) :
    UniquePaths state.core.primitive (0, 0) ∧
      TableRooted (0, 0) state.core.ro state.core.primitive
        (PaddedIssuedBefore statement receipt round) := by
  induction round generalizing state with
  | zero =>
      simp only [paddedWorkHybridStateNat] at hstate
      injection hstate with hstateEq
      subst hstateEq
      refine ⟨uniquePaths_empty _, ?_⟩
      intro entry hentry
      simp [WorkHybridState.initial, PrefixHybridState.empty, Oracle.empty]
        at hentry
  | succ round ih =>
      have hprev : round ≤ m + queryCount :=
        Nat.le_trans (Nat.le_succ round) hround
      unfold paddedWorkHybridStateNat at hstate
      cases hprevRun : paddedWorkHybridStateNat statement receipt verdict coins
          round hprev with
      | error error =>
          rw [hprevRun] at hstate
          contradiction
      | ok previous =>
          rw [hprevRun] at hstate
          have hstep : workHybridStep
              (paddedConstructionDistinguisher statement receipt verdict)
              (0, 0) previous ⟨round, Nat.lt_of_succ_le hround⟩ =
                .ok state := by
            simpa using hstate
          obtain ⟨hU, hrooted⟩ := ih hprev hprevRun
          obtain ⟨hans, hremaining⟩ :=
            paddedWorkHybridStateNat_ok_shape statement receipt verdict coins
              hprev hprevRun
          exact (paddedRound_bridge statement receipt verdict coins hsafe
            ⟨round, Nat.lt_of_succ_le hround⟩ previous hans hremaining hU
            hrooted (fun h => hnocol
              ⟨⟨round, Nat.lt_of_succ_le hround⟩, previous, hprevRun, h⟩)).2
            state hstep

/-- ⭐ **The deterministic bridge.**  No rooted-path capacity collision on the
exact work vector, plus the proved prefix-free routing, gives the
replay-compatible terminal-fresh run — the event the eager/deferred coupling
consumes. -/
theorem paddedEagerTerminalFreshRun_of_noCapacityCollision {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (coins : Fin (paddedTranscriptPrimitiveWork statement receipt) →
      Rate × Cap)
    (hsafe : PaddedFullMessageRoutingSafe statement receipt)
    (hnocol : ¬ PaddedCapacityCollisionRun statement receipt verdict coins) :
    PaddedEagerTerminalFreshRun statement receipt verdict coins := by
  intro round state hstate
  obtain ⟨hU, hrooted⟩ := paddedWorkHybridStateNat_rooted statement receipt
    verdict coins hsafe hnocol (Nat.le_of_lt round.isLt) hstate
  obtain ⟨hans, hremaining⟩ := paddedWorkHybridStateNat_ok_shape statement
    receipt verdict coins (Nat.le_of_lt round.isLt) hstate
  exact (paddedRound_bridge statement receipt verdict coins hsafe round state
    hans hremaining hU hrooted (fun h => hnocol ⟨round, state, hstate, h⟩)).1

/-! ### Transport to the priced pairwise event -/

/-- The consumed-coordinate run invariant: every capacity a reached table
mentions is the IV's or the capacity of an already consumed work coin.  No
freshness premise. -/
theorem paddedWorkHybridStateNat_capsConsumed {m queryCount round : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (coins : Fin (paddedTranscriptPrimitiveWork statement receipt) →
      Rate × Cap)
    (hround : round ≤ m + queryCount) {state : WorkHybridState Rate Cap}
    (hstate : paddedWorkHybridStateNat statement receipt verdict coins round
      hround = .ok state) :
    CapsConsumed (0, 0) state.core.primitive
      (PaddedConsumedCap statement receipt coins
        (paddedWorkPrefix statement receipt round)) := by
  induction round generalizing state with
  | zero =>
      simp only [paddedWorkHybridStateNat] at hstate
      injection hstate with hstateEq
      subst hstateEq
      intro c hc
      left
      simpa [capsOf, WorkHybridState.initial, PrefixHybridState.empty,
        Oracle.empty] using hc
  | succ round ih =>
      have hprev : round ≤ m + queryCount :=
        Nat.le_trans (Nat.le_succ round) hround
      unfold paddedWorkHybridStateNat at hstate
      cases hprevRun : paddedWorkHybridStateNat statement receipt verdict coins
          round hprev with
      | error error =>
          rw [hprevRun] at hstate
          contradiction
      | ok previous =>
          rw [hprevRun] at hstate
          have hstep : workHybridStep
              (paddedConstructionDistinguisher statement receipt verdict)
              (0, 0) previous ⟨round, Nat.lt_of_succ_le hround⟩ =
                .ok state := by
            simpa using hstate
          have hcons := ih hprev hprevRun
          obtain ⟨hans, hremaining⟩ :=
            paddedWorkHybridStateNat_ok_shape statement receipt verdict coins
              hprev hprevRun
          obtain ⟨x, xs, hmove, hmessage, hsize, henough⟩ :=
            paddedRound_data statement receipt verdict coins
              ⟨round, Nat.lt_of_succ_le hround⟩ previous hans hremaining
          obtain ⟨result, hprogram, hro, hprim⟩ :=
            workHybridStep_constr_program _ _ previous state
              ⟨round, Nat.lt_of_succ_le hround⟩ x xs hmove hstep
          have hrun : programPrefixes previous.core.ro previous.core.primitive
              (0, 0) [] (x :: xs)
              ((previous.remaining.take (xs.length + 1)).map Prod.fst)
              ((previous.remaining.take (xs.length + 1)).map Prod.snd) =
                some result := by
            simpa [programConstruction] using hprogram
          have hcons' := programPrefixes_capsConsumed (0, 0) (x :: xs) _ _
            previous.core.ro previous.core.primitive (0, 0) [] _ result hcons
            rfl hrun
          rw [hprim]
          refine capsConsumed_mono (fun c hc => ?_) hcons'
          rw [paddedWorkPrefix_succ statement receipt round
            (Nat.lt_of_succ_le hround), ← hsize]
          rcases hc with ⟨i, hi, hci⟩ | hmem
          · exact ⟨i, by omega, hci⟩
          · rw [hremaining] at hmem
            obtain ⟨i, _, hhi, hci⟩ := segment_mem coins hmem
            exact ⟨i, by omega, hci⟩

/-- **Exact event ⊆ priced event.**  A rooted-path capacity collision on the
work vector is a pairwise capacity collision or a hit of the IV capacity —
the landed `CapBad` at avoid set `{0}` on the capacity coordinate. -/
theorem paddedCapacityCollisionRun_capBad {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (coins : Fin (paddedTranscriptPrimitiveWork statement receipt) →
      Rate × Cap)
    (hcol : PaddedCapacityCollisionRun statement receipt verdict coins) :
    CapBad {(0 : Cap)} (paddedCapacityCoins statement receipt coins) := by
  obtain ⟨round, state, hstate, hwalk⟩ := hcol
  have hcons := paddedWorkHybridStateNat_capsConsumed statement receipt
    verdict coins (Nat.le_of_lt round.isLt) hstate
  obtain ⟨_, hremaining⟩ := paddedWorkHybridStateNat_ok_shape statement
    receipt verdict coins (Nat.le_of_lt round.isLt) hstate
  rw [hremaining] at hwalk
  obtain ⟨k, hk, hcase⟩ := capacityPathCollision_index (0, 0) _ _ _ _ _ _ _ _
    hcons rfl hwalk
  obtain ⟨i, hi, hik⟩ := segment_getElem coins hk
  rcases hcase with hzero | ⟨i', hi', hci'⟩ | ⟨j, hj, hjk⟩
  · refine Or.inr ⟨i, ?_⟩
    rw [Finset.mem_singleton]
    show (coins i).2 = 0
    rw [← hik]
    exact hzero
  · refine Or.inl ⟨i', i, Fin.lt_def.mpr (by omega), ?_⟩
    show (coins i').2 = (coins i).2
    rw [hci', hik]
  · obtain ⟨i'', hi'', hjk'⟩ := segment_getElem coins (Nat.lt_trans hj hk)
    refine Or.inl ⟨i'', i, Fin.lt_def.mpr (by omega), ?_⟩
    show (coins i'').2 = (coins i).2
    rw [← hjk', ← hik]
    exact hjk

/-- ⭐ **The capacity event, priced on the exact work space** through the
landed `capBad_le`: at padded receipt work `W`, at most `2·W²/|Cap|`. -/
theorem paddedCapacityCollisionRun_le {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool) :
    uniformProb (Fin (paddedTranscriptPrimitiveWork statement receipt) →
        Rate × Cap)
        (PaddedCapacityCollisionRun statement receipt verdict)
      ≤ 2 * (paddedTranscriptPrimitiveWork statement receipt : Real) ^ 2 /
          (Fintype.card Cap : Real) := by
  refine le_trans (uniformProb_mono fun coins hcol =>
    paddedCapacityCollisionRun_capBad statement receipt verdict coins hcol) ?_
  calc
    uniformProb (Fin (paddedTranscriptPrimitiveWork statement receipt) →
        Rate × Cap)
        (fun coins => CapBad {(0 : Cap)}
          (paddedCapacityCoins statement receipt coins))
      = uniformProb
          ((Fin (paddedTranscriptPrimitiveWork statement receipt) → Rate) ×
            (Fin (paddedTranscriptPrimitiveWork statement receipt) → Cap))
          (fun parts => CapBad {(0 : Cap)} parts.2) :=
        uniformProb_equiv
          (splitWorkCoins (paddedTranscriptPrimitiveWork statement receipt))
          (fun parts => CapBad {(0 : Cap)} parts.2)
    _ ≤ 2 * (paddedTranscriptPrimitiveWork statement receipt : Real) ^ 2 /
          (Fintype.card Cap : Real) :=
        uniformProb_prod_le (by positivity) fun _ =>
          capBad_le (paddedTranscriptPrimitiveWork statement receipt)
            {(0 : Cap)} (by simp)

/-- ⭐ **The eager/deferred coupling, priced.**  Under prefix-free routing,
the eager and reindexed deferred runs fail to agree with probability at most
the capacity term.  This is the first probability statement on the coupling;
it is still a hybrid-to-hybrid statement, not the RP/RF switch. -/
theorem paddedEagerDeferredRun_disagreement_le {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (hsafe : PaddedFullMessageRoutingSafe statement receipt) :
    uniformProb (Fin (paddedTranscriptPrimitiveWork statement receipt) →
        Rate × Cap)
        (fun coins => ¬ ∃ eager deferred,
          workHybridRun
              (paddedConstructionDistinguisher statement receipt verdict)
              (0, 0) coins = .ok eager ∧
            deferredWorkRun
              (paddedConstructionDistinguisher statement receipt verdict)
              (0, 0) (paddedSegmentReindex statement receipt coins) =
                .ok deferred ∧
            eager.core.ans = deferred.core.ans)
      ≤ 2 * (paddedTranscriptPrimitiveWork statement receipt : Real) ^ 2 /
          (Fintype.card Cap : Real) := by
  refine le_trans (uniformProb_mono fun coins hdisagree => ?_)
    (paddedCapacityCollisionRun_le statement receipt verdict)
  by_contra hnocol
  exact hdisagree (paddedEagerDeferredRun_terminalFresh_agreement statement
    receipt verdict coins hsafe
    (paddedEagerTerminalFreshRun_of_noCapacityCollision statement receipt
      verdict coins hsafe hnocol))

/-! ### Premise inhabitation and run-level teeth -/

/-- **Premise inhabitation.**  Whenever the capacity term is below one, some
work vector avoids the exact event; the bridge's hypothesis is satisfiable
for every statement and receipt in that regime. -/
theorem paddedCapacityCollisionRun_avoidable {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (hsmall : 2 * (paddedTranscriptPrimitiveWork statement receipt : Real) ^ 2
      < (Fintype.card Cap : Real)) :
    ∃ coins : Fin (paddedTranscriptPrimitiveWork statement receipt) →
        Rate × Cap,
      ¬ PaddedCapacityCollisionRun statement receipt verdict coins := by
  by_contra hall
  have hall' : ∀ coins : Fin (paddedTranscriptPrimitiveWork statement receipt) →
      Rate × Cap, PaddedCapacityCollisionRun statement receipt verdict coins :=
    fun coins => Classical.by_contradiction fun h => hall ⟨coins, h⟩
  have hone : uniformProb
      (Fin (paddedTranscriptPrimitiveWork statement receipt) → Rate × Cap)
      (PaddedCapacityCollisionRun statement receipt verdict) = 1 := by
    rw [uniformProb_congr (q := fun _ => True)
      (fun coins => ⟨fun _ => trivial, fun _ => hall' coins⟩),
      uniformProb_const, if_pos trivial]
  have hle := paddedCapacityCollisionRun_le statement receipt verdict
  rw [hone] at hle
  have hcard : (0 : Real) < (Fintype.card Cap : Real) := by
    exact_mod_cast Fintype.card_pos
  rw [le_div_iff₀ hcard, one_mul] at hle
  linarith

/-- The collision at a first fresh edge whose capacity coin is the IV's. -/
theorem capacityPathCollision_head_iv {Rate' Cap' : Type} [AddCommGroup Rate']
    (iv : Rate' × Cap') (ro : Oracle (List Rate') Rate') (x r : Rate')
    (xs rateCoins : List Rate') (capacityCoins : List Cap') :
    CapacityPathCollision iv ro Oracle.empty iv [] (x :: xs)
      (r :: rateCoins) (iv.2 :: capacityCoins) := by
  simp only [CapacityPathCollision, Oracle.lookup_empty]
  exact Or.inl (iv_cap_mem _ _)

/-- **Run-level teeth.**  The all-zero work vector suffers the exact event
at round zero of every nonempty padded schedule: its first fresh edge
receives the IV capacity.  The event is not vacuous. -/
theorem paddedCapacityCollisionRun_zero {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (hrounds : 0 < m + queryCount) :
    PaddedCapacityCollisionRun statement receipt verdict
      (fun _ => ((0 : Rate), (0 : Cap))) := by
  refine ⟨⟨0, hrounds⟩, WorkHybridState.initial _, rfl, ?_⟩
  obtain ⟨x, xs, hquery, hmessage⟩ :=
    paddedConstructionQuerySchedule_is_constr statement receipt ⟨0, hrounds⟩
  have hsize : paddedRoundPrimitiveWork statement receipt ⟨0, hrounds⟩ =
      xs.length + 1 := by
    simp [paddedRoundPrimitiveWork, hquery]
  have hW : xs.length + 1 ≤ paddedTranscriptPrimitiveWork statement receipt := by
    have h1 := paddedWorkPrefix_le_final statement receipt 1
    have h2 := paddedWorkPrefix_succ statement receipt 0 hrounds
    rw [paddedWorkPrefix_zero, hsize] at h2
    simp only [Nat.zero_add] at h2
    omega
  have hrem : (WorkHybridState.initial
      (fun _ : Fin (paddedTranscriptPrimitiveWork statement receipt) =>
        ((0 : Rate), (0 : Cap)))).remaining.take (xs.length + 1) =
      List.replicate (xs.length + 1) ((0 : Rate), (0 : Cap)) := by
    simp [WorkHybridState.initial, List.ofFn_const, List.take_replicate,
      Nat.min_eq_left hW]
  rw [hmessage, hsize, hrem, List.map_replicate, List.map_replicate,
    List.replicate_succ]
  exact capacityPathCollision_head_iv (0, 0) _ x _ xs _ _

/-! ### The ledger charge -/

/-- The exact capacity term at work `W`: the pessimistic `2·W²/|Cap|` of the
landed `capBad_le`, with `|Cap| = p⁸` for BabyBear `p`
(`BaseFoldPoseidon2Rom.capacity_card`). -/
def paddedCapacityError (work : Nat) : Real :=
  2 * (work : Real) ^ 2 / (Fintype.card Cap : Real)

/-- The strict ROM/sampling ledger with the capacity event charged. -/
def strictRomSamplingCapacityError (work queryCount : Nat) : Real :=
  strictRomSamplingError work queryCount + paddedCapacityError work

theorem paddedCapacityCollisionRun_le_error {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool) :
    uniformProb (Fin (paddedTranscriptPrimitiveWork statement receipt) →
        Rate × Cap)
        (PaddedCapacityCollisionRun statement receipt verdict)
      ≤ paddedCapacityError (paddedTranscriptPrimitiveWork statement receipt) :=
  paddedCapacityCollisionRun_le statement receipt verdict

/-- Arithmetic composition rule: the capacity term joins the strict ledger by
addition, without renaming or dropping either existing term. -/
theorem add_capacity_le_strictCapacityLedger {work queryCount : Nat}
    {romAdvantage rejection collision : Real}
    (romAndRejection :
      romAdvantage + rejection ≤ strictRomSamplingError work queryCount)
    (hcollision : collision ≤ paddedCapacityError work) :
    romAdvantage + rejection + collision ≤
      strictRomSamplingCapacityError work queryCount := by
  unfold strictRomSamplingCapacityError
  linarith

/-- ⭐ **The charged ledger.**  Sponge-game advantage, fail-closed rejection,
and the exact capacity event of the eager/deferred coupling, each on its
honest sample space, combined only by addition at the padded receipt work.
`hrom` remains the explicitly open ideal-permutation premise. -/
theorem paddedConstructionDistinguisher_rom_rejection_capacity_bound
    {m queryCount : Nat}
    (hrom : BaseFoldPoseidon2Rom.romConstructionTarget)
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool) :
    |realProb
          (paddedConstructionDistinguisher statement receipt verdict) (0, 0) -
        idealProb
          (paddedConstructionDistinguisher statement receipt verdict) (0, 0)| +
        uniformProb (Fin queryCount → BaseFoldPoseidon2.Digest)
          BaseFoldBcsQuerySampling.QuerySeedRejection +
        uniformProb (Fin (paddedTranscriptPrimitiveWork statement receipt) →
            Rate × Cap)
          (PaddedCapacityCollisionRun statement receipt verdict)
      ≤ strictRomSamplingCapacityError
          (paddedTranscriptPrimitiveWork statement receipt) queryCount :=
  add_capacity_le_strictCapacityLedger
    (paddedConstructionDistinguisher_rom_and_rejection_bound hrom statement
      receipt verdict)
    (paddedCapacityCollisionRun_le statement receipt verdict)

#check @CapacityPathCollision
#check @TableRooted
#check @terminalPrimitiveFreshTo_of_noCollision
#check @capacityPathCollision_index
#check @programPrefixes_capsConsumed
#check @PaddedCapacityCollisionRun
#check @paddedEagerTerminalFreshRun_of_noCapacityCollision
#check @paddedCapacityCollisionRun_capBad
#check @paddedCapacityCollisionRun_le
#check @paddedEagerDeferredRun_disagreement_le
#check @paddedCapacityCollisionRun_avoidable
#check @paddedCapacityCollisionRun_zero
#check @strictRomSamplingCapacityError
#check @paddedConstructionDistinguisher_rom_rejection_capacity_bound

/-- info: 'Minidregg.Selvage.terminalPrimitiveFreshTo_of_noCollision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms terminalPrimitiveFreshTo_of_noCollision
/-- info: 'Minidregg.Selvage.capacityPathCollision_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms capacityPathCollision_index
/-- info: 'Minidregg.Selvage.programPrefixes_capsConsumed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms programPrefixes_capsConsumed
/-- info: 'Minidregg.Selvage.CapacityEventExample.not_terminalFresh_zero_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CapacityEventExample.not_terminalFresh_zero_capacity
/-- info: 'Minidregg.Selvage.CapacityEventExample.terminalFresh_fresh_capacities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CapacityEventExample.terminalFresh_fresh_capacities
/-- info: 'Minidregg.Selvage.BaseFoldBcsCapacityEvent.paddedEagerTerminalFreshRun_of_noCapacityCollision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paddedEagerTerminalFreshRun_of_noCapacityCollision
/-- info: 'Minidregg.Selvage.BaseFoldBcsCapacityEvent.paddedCapacityCollisionRun_capBad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paddedCapacityCollisionRun_capBad
/-- info: 'Minidregg.Selvage.BaseFoldBcsCapacityEvent.paddedCapacityCollisionRun_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paddedCapacityCollisionRun_le
/-- info: 'Minidregg.Selvage.BaseFoldBcsCapacityEvent.paddedEagerDeferredRun_disagreement_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paddedEagerDeferredRun_disagreement_le
/-- info: 'Minidregg.Selvage.BaseFoldBcsCapacityEvent.paddedCapacityCollisionRun_avoidable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paddedCapacityCollisionRun_avoidable
/-- info: 'Minidregg.Selvage.BaseFoldBcsCapacityEvent.paddedCapacityCollisionRun_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paddedCapacityCollisionRun_zero
/-- info: 'Minidregg.Selvage.BaseFoldBcsCapacityEvent.paddedConstructionDistinguisher_rom_rejection_capacity_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paddedConstructionDistinguisher_rom_rejection_capacity_bound

end

end Minidregg.Selvage.BaseFoldBcsCapacityEvent
