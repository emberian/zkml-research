/-
# `Obend.Lower.Pancake.CondSClk` — Path-Sensitive Static Clock Synthesis (`SClk`)

Upgrades `orb-compiler`'s static clock synthesis (`SClk`) for Cross-Tree Gate `G6`:
1. **Path-Sensitive Branching (`SClk.cond`)**: Synthesizes tight `Nat.max clk1 clk2`
   clock bounds across conditional branches, refining the true branch under
   `P s ∧ guard s = true` and the false branch under `P s ∧ guard s = false`.
2. **Clock-Consuming Bounded Loops (`SClk.loop`)**: Generalizes `While` clock
   synthesis from `0`-clock bodies to arbitrary clock-consuming bodies (`m * (1 + clkBody)`).
3. **Intra-Module Verified Calls (`SClk.call`)**: Accounts for `1 + clkCallee` ticks
   across `s.code` lookups and caller local-frame restoration.
4. **Entry-Preconditioned Leaves (`EntryWF` / `PostWF`)**: Eliminates the vacuous
   universal `∀ s` quantification over empty-locals / unmapped-memory states.
-/
import PanSemV435


namespace OrbPancakeV435

set_option autoImplicit false

/-! ## 1. Entry & Postcondition Envelopes (`EntryWF`, `PostWF`) -/

/-- Entry-state well-formedness: combines machine structural validity (`StateWF`)
    with the stage's domain/local entry precondition `P`. -/
def EntryWF {θ : Type} (P : PanState θ → Prop) (s0 : PanState θ) : Prop :=
  StateWF s0 ∧ P s0

/-- Exit-state well-formedness: combines preserved machine structural validity (`StateWF`)
    with the stage's result/state postcondition `Q`. -/
def PostWF {θ : Type} (Q : PanResult → PanState θ → Prop) (r : PanResult) (s1 : PanState θ) : Prop :=
  StateWF s1 ∧ Q r s1

/-! ## 2. Pure AST Path-Sensitive Clock Synthesis (`synthStmtClk`) -/

/-- Pure syntactic clock-bound synthesis for loop-free `PStmt` trees:
    * `skip`, `assign`, `store`, `storeByte`, `ret`, `annot`, `extCall` -> `0` ticks
    * `tick` -> `1` tick
    * `dec` -> continuation's clock bound
    * `seq c1 c2` -> `c1_clk + c2_clk`
    * `ite cond c1 c2` -> **`Nat.max c1_clk c2_clk`** (path-sensitive tight max)
    * `while_` / `call` / `decCall` -> `none` without external loop/callee annotation
      (handled by `SClk.loop` and `SClk.call` below). -/
def synthStmtClk : PStmt → Option Nat
  | .skip                => some 0
  | .tick                => some 1
  | .dec _ _ _ body      => synthStmtClk body
  | .assign _ _ _        => some 0
  | .store _ _           => some 0
  | .storeByte _ _       => some 0
  | .ret _               => some 0
  | .annot _ _           => some 0
  | .extCall _ _ _ _ _   => some 0
  | .break_              => some 0
  | .continue_           => some 0
  | .seq c1 c2 =>
    match synthStmtClk c1, synthStmtClk c2 with
    | some k1, some k2 => some (k1 + k2)
    | _, _             => none
  | .ite _ c1 c2 =>
    match synthStmtClk c1, synthStmtClk c2 with
    | some k1, some k2 => some (max k1 k2)
    | _, _             => none
  | .while_ _ _          => none
  | .call _ _ _          => none
  | .decCall _ _ _ _ _   => none
termination_by structural s => s

@[simp] theorem synthStmtClk_skip : synthStmtClk .skip = some 0 := rfl
@[simp] theorem synthStmtClk_tick : synthStmtClk .tick = some 1 := rfl
@[simp] theorem synthStmtClk_assign (vk : VarKind) (v : String) (e : PExp) :
    synthStmtClk (.assign vk v e) = some 0 := rfl
@[simp] theorem synthStmtClk_ret (e : PExp) : synthStmtClk (.ret e) = some 0 := rfl
@[simp] theorem synthStmtClk_dec (v : String) (sh : Shape) (e : PExp) (body : PStmt) :
    synthStmtClk (.dec v sh e body) = synthStmtClk body := rfl

@[simp] theorem synthStmtClk_ite (e : PExp) (c1 c2 : PStmt) (k1 k2 : Nat)
    (h1 : synthStmtClk c1 = some k1) (h2 : synthStmtClk c2 = some k2) :
    synthStmtClk (.ite e c1 c2) = some (max k1 k2) := by
  simp [synthStmtClk, h1, h2]

@[simp] theorem synthStmtClk_seq (c1 c2 : PStmt) (k1 k2 : Nat)
    (h1 : synthStmtClk c1 = some k1) (h2 : synthStmtClk c2 = some k2) :
    synthStmtClk (.seq c1 c2) = some (k1 + k2) := by
  simp [synthStmtClk, h1, h2]

/-- Synthesized `synthStmtClk` on a conditional is strictly tighter than additive sum whenever
    both arms consume non-zero clock (`max k1 k2 < k1 + k2` for `k1 > 0, k2 > 0`). -/
theorem cond_clk_lt_additive {k1 k2 : Nat} (h1 : 0 < k1) (h2 : 0 < k2) :
    max k1 k2 < k1 + k2 := by
  omega

/-! ## 3. Annotated Path-Sensitive Clocked-Stage Derivation (`SClk`) -/

/-- Path-sensitive clocked stage (`SClk θ P stmt clk Q`):
    Indexed by entry precondition `P`, concrete Pancake statement `stmt : PStmt`,
    synthesized static clock budget `clk : Nat`, and relational postcondition
    `Q : PanState θ → PanResult → PanState θ → Prop`. -/
inductive SClk (θ : Type) :
    (PanState θ → Prop) → PStmt → Nat → (PanState θ → PanResult → PanState θ → Prop) → Type where
  | skip (P : PanState θ → Prop) :
      SClk θ P .skip 0 (fun s0 r s1 => r = .normal ∧ s1 = s0)
  | tick (P : PanState θ → Prop) :
      SClk θ P .tick 1 (fun s0 r s1 => r = .normal ∧ s1 = dec_clock s0)
  | assign {P : PanState θ → Prop} (vk : VarKind) (v : String) (src : PExp)
      (f : PanState θ → PanVal)
      (heval : ∀ s, EntryWF P s → eval s src = some (f s))
      (hvalid : ∀ s, EntryWF P s → is_valid_value s vk v (f s) = true) :
      SClk θ P (.assign vk v src) 0 (fun s0 r s1 => r = .normal ∧ s1 = set_kvar vk v (f s0) s0)
  | store {P : PanState θ → Prop} (dst src : PExp)
      (addr : PanState θ → Word) (val : PanState θ → PanVal)
      (mNext : PanState θ → (Word → Word))
      (hdst : ∀ s, EntryWF P s → eval s dst = some (.word (addr s)))
      (hsrc : ∀ s, EntryWF P s → eval s src = some (val s))
      (hmem : ∀ s, EntryWF P s → mem_stores (addr s) (flatten (val s)) s.memaddrs s.memory = some (mNext s)) :
      SClk θ P (.store dst src) 0 (fun s0 r s1 => r = .normal ∧ s1 = { s0 with memory := mNext s0 })
  | storeByte {P : PanState θ → Prop} (dst src : PExp)
      (addr w : PanState θ → Word)
      (hdst : ∀ s, EntryWF P s → eval s dst = some (.word (addr s)))
      (hsrc : ∀ s, EntryWF P s → eval s src = some (.word (w s)))
      (hdom : ∀ s, EntryWF P s → s.memaddrs (byte_align (addr s)) = true) :
      SClk θ P (.storeByte dst src) 0 (fun s0 r s1 =>
        r = .normal ∧
        s1 = { s0 with
          memory := UPDATE (byte_align (addr s0))
            (set_byte (addr s0) (BitVec.setWidth 8 (w s0)) (s0.memory (byte_align (addr s0))) s0.be)
            s0.memory })
  | ret {P : PanState θ → Prop} (e : PExp) (f : PanState θ → PanVal)
      (heval : ∀ s, EntryWF P s → eval s e = some (f s))
      (hsz : ∀ s, EntryWF P s → size_of_shape (shape_of (f s)) ≤ 32) :
      SClk θ P (.ret e) 0 (fun s0 r s1 => r = .ret (f s0) ∧ s1 = empty_locals s0)
  | dec {P Pc : PanState θ → Prop} {bodyStmt : PStmt} {clk : Nat}
      {Qc : PanState θ → PanResult → PanState θ → Prop}
      (v : String) (sh : Shape) (e : PExp) (f : PanState θ → PanVal)
      (heval : ∀ s, EntryWF P s → eval s e = some (f s))
      (hsh : ∀ s, EntryWF P s → shape_of (f s) = sh)
      (hlink : ∀ s, EntryWF P s → Pc { s with locals := FUPDATE s.locals (v, f s) })
      (body : SClk θ Pc bodyStmt clk Qc) :
      SClk θ P (.dec v sh e bodyStmt) clk (fun s0 r s1 =>
        ∃ smid, Qc { s0 with locals := FUPDATE s0.locals (v, f s0) } r smid ∧
          s1 = { smid with locals := res_var smid.locals (v, s0.locals v) })
  | seq {P1 P2 : PanState θ → Prop} {c1 c2 : PStmt} {clk1 clk2 : Nat}
      {Q1 Q2 : PanState θ → PanResult → PanState θ → Prop}
      (s1 : SClk θ P1 c1 clk1 Q1) (s2 : SClk θ P2 c2 clk2 Q2)
      (hlink : ∀ s0 smid, EntryWF P1 s0 → StateWF smid → Q1 s0 .normal smid → P2 smid) :
      SClk θ P1 (.seq c1 c2) (clk1 + clk2) (fun s0 r s2_st =>
        (∃ smid, Q1 s0 .normal smid ∧ Q2 smid r s2_st) ∨
        (r ≠ .normal ∧ Q1 s0 r s2_st))
  | cond {P : PanState θ → Prop} {c1 c2 : PStmt} {clk1 clk2 : Nat}
      {Q1 Q2 : PanState θ → PanResult → PanState θ → Prop}
      (e : PExp) (guard : PanState θ → Bool)
      (hguard : ∀ s, EntryWF P s → ∃ w : Word, eval s e = some (.word w) ∧ (w != 0#64) = guard s)
      (thenBranch : SClk θ (fun s => P s ∧ guard s = true) c1 clk1 Q1)
      (elseBranch : SClk θ (fun s => P s ∧ guard s = false) c2 clk2 Q2) :
      SClk θ P (.ite e c1 c2) (max clk1 clk2) (fun s0 r s1 =>
        if guard s0 then Q1 s0 r s1 else Q2 s0 r s1)
  | loop {bodyStmt : PStmt} {clkBody : Nat}
      {Qbody : PanState θ → PanResult → PanState θ → Prop}
      (I : Nat → PanState θ → Prop)
      (condE : PExp) (m : Nat)
      (hguard : ∀ n s, n ≤ m → EntryWF (I n) s →
        ∃ w : Word, eval s condE = some (.word w) ∧ (w != 0#64) = decide (n ≠ 0))
      (body : SClk θ (fun s => ∃ n, n < m ∧ I (n + 1) s) bodyStmt clkBody Qbody)
      (hstep : ∀ n s0 s1 r, n < m → EntryWF (I (n + 1)) s0 →
        StateWF s1 → Qbody (dec_clock s0) r s1 → r = .normal ∧ I n s1)
      (hdec : ∀ n (s0 : PanState θ), n < m → I (n + 1) s0 → I (n + 1) (dec_clock s0)) :
      SClk θ (I m) (.while_ condE bodyStmt) (m * (1 + clkBody)) (fun _ r s1 => r = .normal ∧ I 0 s1)
  | call {P Pcallee : PanState θ → Prop} {calleeBody : PStmt} {clkCallee : Nat}
      {Qcallee : PanState θ → PanResult → PanState θ → Prop}
      (vk : VarKind) (retVar fname : String) (args : List PExp)
      (params : List (String × Shape))
      (argVals : PanState θ → List PanVal)
      (retValOf : PanState θ → PanVal)
      (callee : SClk θ Pcallee calleeBody clkCallee Qcallee)
      (hargs : ∀ s, EntryWF P s → evalList s args = some (argVals s))
      (hcode : ∀ s, EntryWF P s → s.code fname = some (params, calleeBody))
      (hshapes : ∀ s, EntryWF P s → shapesMatch params (argVals s) = true)
      (hcalleeP : ∀ s, EntryWF P s →
        Pcallee { dec_clock s with locals := mkCalleeLocals params (argVals s) })
      (hcalleeRet : ∀ s r sc, EntryWF P s →
        Qcallee { dec_clock s with locals := mkCalleeLocals params (argVals s) } r sc →
        r = .ret (retValOf s))
      (hvalid : ∀ s, EntryWF P s → is_valid_value s vk retVar (retValOf s) = true) :
      SClk θ P (.call (some (vk, retVar)) fname args) (1 + clkCallee) (fun s0 r s1 =>
        ∃ sc, Qcallee { dec_clock s0 with locals := mkCalleeLocals params (argVals s0) }
                (.ret (retValOf s0)) sc ∧
              r = .normal ∧
              s1 = set_kvar vk retVar (retValOf s0) { sc with locals := s0.locals })
  | conseq {P P' : PanState θ → Prop} {stmt : PStmt} {clk clk' : Nat}
      {Q Q' : PanState θ → PanResult → PanState θ → Prop}
      (inner : SClk θ P stmt clk Q)
      (hP : ∀ s0, EntryWF P' s0 → P s0)
      (hclk : clk ≤ clk')
      (hQ : ∀ s0 r s1, EntryWF P' s0 → StateWF s1 → Q s0 r s1 → Q' s0 r s1) :
      SClk θ P' stmt clk' Q'

/-- Extract the synthesized static clock bound `clk : Nat` carried by an `SClk` derivation. -/
def SClk.clkBound {θ : Type} {P : PanState θ → Prop} {stmt : PStmt} {clk : Nat}
    {Q : PanState θ → PanResult → PanState θ → Prop} (_ : SClk θ P stmt clk Q) : Nat :=
  clk

/-- `SClk.cond` synthesizes `max clk1 clk2` as its exact `clkBound`. -/
theorem sclk_cond_clkBound {θ : Type} {P : PanState θ → Prop} {c1 c2 : PStmt} {clk1 clk2 : Nat}
    {Q1 Q2 : PanState θ → PanResult → PanState θ → Prop}
    (e : PExp) (guard : PanState θ → Bool)
    (hg : ∀ s, EntryWF P s → ∃ w : Word, eval s e = some (.word w) ∧ (w != 0#64) = guard s)
    (st1 : SClk θ (fun s => P s ∧ guard s = true) c1 clk1 Q1)
    (st2 : SClk θ (fun s => P s ∧ guard s = false) c2 clk2 Q2) :
    (SClk.cond e guard hg st1 st2).clkBound = max st1.clkBound st2.clkBound := rfl


/--
info: 'OrbPancakeV435.cond_clk_lt_additive' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms cond_clk_lt_additive

/--
info: 'OrbPancakeV435.sclk_cond_clkBound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms sclk_cond_clkBound

end OrbPancakeV435

