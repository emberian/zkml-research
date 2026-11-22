/-
# `Obend.Lower.Pancake.PanSem` — HOL4-Faithful CakeML Pancake Operational Semantics

Implements the Lean 4.35 (`Init`-only, `0` Mathlib, `LAW-M1`) port and upgrade of
the CakeML Pancake operational semantics (`panLang` / `panSem`, CakeML `ed31510b3`,
`'a := 64`), closing the operational-semantics foundation of Cross-Tree Gate `G6`:

1. **Structural Fuel-Clocked Operational Semantics (`eval`, `evaluate`)**:
   - Models `PExp`, `PStmt`, `PFun`, `PanVal`, `PanState`, and `PanResult` (`normal`,
     `ret`, `break_`, `continue_`, `TimeOut`, `Error`, `finalFFI`).
   - Covers `skip`, `dec`, `assign` (enforcing HOL4's `is_valid_value` bound-and-shape
     invariant), `store`, `storeByte`, `seq` (with `fix_clock`), `ite`, `while_`
     (with `dec_clock` + `fix_clock`), `break_`, `continue_`, intra-module `call`
     and `decCall` (over `s.code`), `extCall` (`call_FFI` + `read_bytearray` /
     `write_bytearray`), `ret` (`size_of_shape ≤ 32`), `tick`, and `annot`.
   - Defined via nested structural recursion (`evaluateStep` / `evaluateFuel`,
     `0 WellFounded.fix`, `0 Classical.choice`), enabling instantaneous kernel
     WHNF reduction while proving exact HOL4 `evaluate` unfolding equations.
2. **HOL4 Kernel Row Contracts & `ServeSpec` Wire Alignment**:
   - Proves 64-bit word, signed/unsigned comparison (`Less` vs `Lower`), bit-slice,
     and finite-map contracts plus `ServeSpec` (`List UInt8 ↔ List (BitVec 8)`)
     wire serialization agreement.
-/


namespace OrbPancakeV435

set_option autoImplicit false

/-! ## 1. Finite Maps, Machine Words & HOL4 Byte/Alignment Substrate -/

/-- 64-bit machine word (`'a := 64` target in CakeML Pancake). -/
abbrev Word := BitVec 64

/-- 8-bit machine byte (`word8`). -/
abbrev Byte := BitVec 8

/-- Computable lookup-function model of HOL4 finite maps `α |-> β` (`FLOOKUP`). -/
abbrev FMap (α β : Type) := α → Option β

/-- `FEMPTY`: empty finite map (`FLOOKUP_EMPTY`). -/
def FEMPTY {α β : Type} : FMap α β := fun _ => none

/-- `f |+ (k, v)`: finite map point update (`FLOOKUP_UPDATE`). -/
def FUPDATE {α β : Type} [DecidableEq α] (f : FMap α β) (kv : α × β) : FMap α β :=
  fun x => if x = kv.1 then some kv.2 else f x

/-- `f \\ k`: finite map domain subtraction (`DOMSUB_FLOOKUP_THM`). -/
def DOMSUB {α β : Type} [DecidableEq α] (f : FMap α β) (k : α) : FMap α β :=
  fun x => if x = k then none else f x

/-- `f |++ kvs`: left-fold bulk update where later keys win (`FUPDATE_LIST_THM`). -/
def FUPDATE_LIST {α β : Type} [DecidableEq α] (f : FMap α β) (kvs : List (α × β)) : FMap α β :=
  kvs.foldl FUPDATE f

/-- `(a =+ b) f`: HOL4 `combin$UPDATE` function point override. -/
def UPDATE {α β : Type} [DecidableEq α] (a : α) (b : β) (f : α → β) : α → β :=
  fun c => if a = c then b else f c

/-- HOL4 `(h '' l) w` (`word_slice_def`): inclusive bit slice `l ≤ i ≤ h`. -/
def word_slice (h l : Nat) (w : Word) : Word :=
  BitVec.ofNat 64 (((w.toNat >>> l) % 2 ^ (h + 1 - l)) <<< l)

/-- HOL4 `word_slice_alt h l w`: half-open bit slice `l ≤ i < h`. -/
def word_slice_alt (h l : Nat) (w : Word) : Word :=
  BitVec.ofNat 64 (((w.toNat >>> l) % 2 ^ (h - l)) <<< l)

/-- HOL4 `byte$byte_index` (`'a := 64`, `d = 8`): bit offset of byte at address `a`. -/
def byte_index (a : Word) (is_bigendian : Bool) : Nat :=
  let d := 8
  if is_bigendian then 8 * ((d - 1) - (a.toNat % d)) else 8 * (a.toNat % d)

/-- HOL4 `byte$get_byte`: extract byte selected by low 3 bits of `a` from word `w`. -/
def get_byte (a w : Word) (is_bigendian : Bool) : Byte :=
  BitVec.setWidth 8 (w >>> byte_index a is_bigendian)

/-- HOL4 `byte$set_byte`: overwrite byte selected by low 3 bits of `a` inside word `w`. -/
def set_byte (a : Word) (b : Byte) (w : Word) (is_bigendian : Bool) : Word :=
  let i := byte_index a is_bigendian
  word_slice_alt 64 (i + 8) w ||| ((BitVec.setWidth 64 b <<< i) ||| word_slice_alt i 0 w)

/-- HOL4 `alignment$align`: clear low `p` bits (`word_slice 63 p w`). -/
def align (p : Nat) (w : Word) : Word :=
  word_slice 63 p w

/-- HOL4 `alignment$byte_align` (`'a := 64`): 8-byte word alignment (`align 3 w`). -/
def byte_align (w : Word) : Word :=
  align 3 w

/-- HOL4 `panSem$mem_load_byte`: aligned word lookup + byte extraction. -/
def mem_load_byte (m : Word → Word) (dm : Word → Bool) (be : Bool) (w : Word) : Option Byte :=
  if dm (byte_align w) then some (get_byte w (m (byte_align w)) be) else none

/-- HOL4 `panSem$mem_store_byte`: aligned word byte-overwrite if mapped in `dm`. -/
def mem_store_byte (m : Word → Word) (dm : Word → Bool) (be : Bool) (w : Word) (b : Byte) :
    Option (Word → Word) :=
  if dm (byte_align w) then
    some (UPDATE (byte_align w) (set_byte w b (m (byte_align w)) be) m)
  else
    none

/-- HOL4 `misc$read_bytearray`: read `n` consecutive bytes starting at `a`. -/
def read_bytearray {α : Type} (a : Word) : Nat → (Word → Option α) → Option (List α)
  | 0, _ => some []
  | n + 1, gb =>
    match gb a with
    | none => none
    | some b =>
      match read_bytearray (a + 1#64) n gb with
      | none => none
      | some bs => some (b :: bs)
termination_by structural n => n

/-- HOL4 `panSem$write_bytearray`: right-to-left byte write; unmapped byte drops writes (`NONE => m`). -/
def write_bytearray (a : Word) : List Byte → (Word → Word) → (Word → Bool) → Bool → (Word → Word)
  | [], m, _, _ => m
  | b :: bs, m, dm, be =>
    match mem_store_byte (write_bytearray (a + 1#64) bs m dm be) dm be a b with
    | none => m
    | some m' => m'
termination_by structural bs => bs

/-! ## 2. Pancake AST (`Shape`, `Binop`, `Panop`, `Cmp`, `Shift`, `PExp`, `PStmt`, `PFun`) -/

/-- Variable scope kind (`panLang$varkind`). -/
inductive VarKind where
  | Local
  | Global
  deriving DecidableEq, Repr, Inhabited

/-- Value layout shape (`panLang$shape`). -/
inductive Shape where
  | One
  | Comb (fields : List Shape)
  deriving Repr, Inhabited

mutual
def Shape.beq : Shape → Shape → Bool
  | .One, .One => true
  | .Comb xs, .Comb ys => Shape.beqList xs ys
  | _, _ => false
termination_by structural s => s

def Shape.beqList : List Shape → List Shape → Bool
  | [], [] => true
  | x :: xs, y :: ys => Shape.beq x y && Shape.beqList xs ys
  | _, _ => false
termination_by structural xs => xs
end

instance : BEq Shape := ⟨Shape.beq⟩

mutual
theorem Shape.beq_iff_eq : ∀ (a b : Shape), (Shape.beq a b = true) ↔ a = b
  | .One, .One => by simp [Shape.beq]
  | .One, .Comb _ => by simp [Shape.beq]
  | .Comb _, .One => by simp [Shape.beq]
  | .Comb xs, .Comb ys => by
    simp only [Shape.beq, Shape.Comb.injEq]
    exact Shape.beqList_iff_eq xs ys
termination_by structural a => a

theorem Shape.beqList_iff_eq : ∀ (xs ys : List Shape), (Shape.beqList xs ys = true) ↔ xs = ys
  | [], [] => by simp [Shape.beqList]
  | [], _ :: _ => by simp [Shape.beqList]
  | _ :: _, [] => by simp [Shape.beqList]
  | x :: xs, y :: ys => by
    simp only [Shape.beqList, Bool.and_eq_true, List.cons.injEq]
    rw [Shape.beq_iff_eq x y, Shape.beqList_iff_eq xs ys]
termination_by structural xs => xs
end

instance : LawfulBEq Shape where
  eq_of_beq {a b} h := (Shape.beq_iff_eq a b).mp h
  rfl {a} := (Shape.beq_iff_eq a a).mpr rfl

instance : DecidableEq Shape := fun a b =>
  if h : Shape.beq a b = true then isTrue ((Shape.beq_iff_eq a b).mp h)
  else isFalse (fun heq => h ((Shape.beq_iff_eq a b).mpr heq))

mutual
/-- Word count of a `Shape` (`panLang$size_of_shape`). -/
def size_of_shape : Shape → Nat
  | .One => 1
  | .Comb shs => size_of_shapes shs
termination_by structural s => s

def size_of_shapes : List Shape → Nat
  | [] => 0
  | s :: ss => size_of_shape s + size_of_shapes ss
termination_by structural ss => ss
end

/-- Word ALU binary operators (`asm$binop`). -/
inductive Binop where
  | Add
  | Sub
  | And
  | Or
  | Xor
  deriving DecidableEq, Repr, Inhabited

/-- Extra Pancake word operators (`panLang$panop`). -/
inductive Panop where
  | Mul
  deriving DecidableEq, Repr, Inhabited

/-- All 8 HOL4 `asm$cmp` word comparators (`Less`/`NotLess` signed, `Lower`/`NotLower` unsigned). -/
inductive Cmp where
  | Equal
  | Lower
  | Less
  | Test
  | NotEqual
  | NotLower
  | NotLess
  | NotTest
  deriving DecidableEq, Repr, Inhabited

/-- All 4 HOL4 `ast$shift` operators. -/
inductive Shift where
  | Lsl
  | Lsr
  | Asr
  | Ror
  deriving DecidableEq, Repr, Inhabited

/-- Pancake expressions (`panLang$exp`). -/
inductive PExp where
  | const (w : Word)
  | var (vk : VarKind) (name : String)
  | rstruct (fields : List PExp)
  | rfield (idx : Nat) (target : PExp)
  | load (sh : Shape) (addr : PExp)
  | loadByte (addr : PExp)
  | binop (op : Binop) (args : List PExp)
  | panop (op : Panop) (args : List PExp)
  | cmp (c : Cmp) (lhs rhs : PExp)
  | shift (sh : Shift) (arg : PExp) (amount : Nat)
  | baseAddr
  | topAddr
  | bytesInWord
  deriving Repr, Inhabited

/-- Convenience constructor for local variable reference. -/
def PExp.lvar (name : String) : PExp := .var .Local name

/-- Pancake statements / programs (`panLang$prog`), including `call` and `decCall`. -/
inductive PStmt where
  | skip
  | dec (v : String) (sh : Shape) (e : PExp) (body : PStmt)
  | assign (vk : VarKind) (v : String) (src : PExp)
  | store (dst src : PExp)
  | storeByte (dst src : PExp)
  | seq (c1 c2 : PStmt)
  | ite (cond : PExp) (thenBranch elseBranch : PStmt)
  | while_ (cond : PExp) (body : PStmt)
  | break_
  | continue_
  | call (retTarget : Option (VarKind × String)) (fname : String) (args : List PExp)
  | decCall (v : String) (sh : Shape) (fname : String) (args : List PExp) (cont : PStmt)
  | extCall (ffiName : String) (confPtr confLen arrPtr arrLen : PExp)
  | ret (e : PExp)
  | tick
  | annot (tag text : String)
  deriving Repr, Inhabited

/-- Convenience constructor for local assignment. -/
abbrev PStmt.lassign (v : String) (src : PExp) : PStmt := .assign .Local v src

/-- Top-level Pancake function declaration (`PFun`). -/
structure PFun where
  name     : String
  params   : List (String × Shape) := []
  body     : PStmt
  exported : Bool := false
  deriving Repr, Inhabited

/-! ## 3. Semantic Values, FFI State, Machine State & Outcomes (`PanVal`, `PanState`, `PanResult`) -/

/-- Runtime values (`panSem$v`): 64-bit words and anonymous tuple/record structs. -/
inductive PanVal where
  | word (w : Word)
  | rstruct (fields : List PanVal)
  deriving Repr, Inhabited

mutual
def PanVal.beq : PanVal → PanVal → Bool
  | .word w1, .word w2 => w1 == w2
  | .rstruct xs, .rstruct ys => PanVal.beqList xs ys
  | _, _ => false
termination_by structural v => v

def PanVal.beqList : List PanVal → List PanVal → Bool
  | [], [] => true
  | x :: xs, y :: ys => PanVal.beq x y && PanVal.beqList xs ys
  | _, _ => false
termination_by structural xs => xs
end

instance : BEq PanVal := ⟨PanVal.beq⟩

mutual
theorem PanVal.beq_iff_eq : ∀ (a b : PanVal), (PanVal.beq a b = true) ↔ a = b
  | .word w1, .word w2 => by simp [PanVal.beq]
  | .word _, .rstruct _ => by simp [PanVal.beq]
  | .rstruct _, .word _ => by simp [PanVal.beq]
  | .rstruct xs, .rstruct ys => by
    simp only [PanVal.beq, PanVal.rstruct.injEq]
    exact PanVal.beqList_iff_eq xs ys
termination_by structural a => a

theorem PanVal.beqList_iff_eq : ∀ (xs ys : List PanVal), (PanVal.beqList xs ys = true) ↔ xs = ys
  | [], [] => by simp [PanVal.beqList]
  | [], _ :: _ => by simp [PanVal.beqList]
  | _ :: _, [] => by simp [PanVal.beqList]
  | x :: xs, y :: ys => by
    simp only [PanVal.beqList, Bool.and_eq_true, List.cons.injEq]
    rw [PanVal.beq_iff_eq x y, PanVal.beqList_iff_eq xs ys]
termination_by structural xs => xs
end

instance : LawfulBEq PanVal where
  eq_of_beq {a b} h := (PanVal.beq_iff_eq a b).mp h
  rfl {a} := (PanVal.beq_iff_eq a a).mpr rfl

instance : DecidableEq PanVal := fun a b =>
  if h : PanVal.beq a b = true then isTrue ((PanVal.beq_iff_eq a b).mp h)
  else isFalse (fun heq => h ((PanVal.beq_iff_eq a b).mpr heq))

mutual
/-- Runtime shape of a `PanVal` (`panSem$shape_of`). -/
def shape_of : PanVal → Shape
  | .word _ => .One
  | .rstruct vs => .Comb (shapes_of vs)
termination_by structural v => v

def shapes_of : List PanVal → List Shape
  | [] => []
  | v :: vs => shape_of v :: shapes_of vs
termination_by structural vs => vs
end

mutual
/-- Flatten a `PanVal` into sequential 64-bit words (`panSem$flatten`). -/
def flatten : PanVal → List Word
  | .word w => [w]
  | .rstruct vs => flatten_list vs
termination_by structural v => v

def flatten_list : List PanVal → List Word
  | [] => []
  | v :: vs => flatten v ++ flatten_list vs
termination_by structural vs => vs
end

/-- HOL4 `ffi$ffi_outcome`. -/
inductive FFIOutcome where
  | FFI_failed
  | FFI_diverged
  deriving DecidableEq, Repr, Inhabited

/-- HOL4 `ffi$oracle_result`. -/
inductive OracleResult (θ : Type) where
  | Oracle_return (ffi' : θ) (bytes' : List Byte)
  | Oracle_final (outcome : FFIOutcome)
  deriving DecidableEq, Repr

/-- HOL4 `ffi$io_event`. -/
structure IOEvent where
  name  : String
  conf  : List Byte
  inout : List (Byte × Byte)
  deriving DecidableEq, Repr, Inhabited

/-- HOL4 `ffi$final_event`. -/
structure FinalEvent where
  name    : String
  conf    : List Byte
  bytes   : List Byte
  outcome : FFIOutcome
  deriving DecidableEq, Repr, Inhabited

/-- HOL4 `ffi$ffi_state`. -/
structure FFIState (θ : Type) where
  oracle    : String → θ → List Byte → List Byte → OracleResult θ
  ffi_state : θ
  io_events : List IOEvent

/-- HOL4 `ffi$ffi_result`. -/
inductive FFIResult (θ : Type) where
  | FFI_return (st' : FFIState θ) (bytes' : List Byte)
  | FFI_final (ev : FinalEvent)

/-- HOL4 `ffi$call_FFI`: empty FFI name is a no-op; length mismatch yields `FFI_failed`. -/
def call_FFI {θ : Type} (st : FFIState θ) (name : String) (conf bytes : List Byte) : FFIResult θ :=
  if name != "" then
    match st.oracle name st.ffi_state conf bytes with
    | .Oracle_return ffi' bytes' =>
      if bytes'.length == bytes.length then
        .FFI_return
          { st with
            ffi_state := ffi'
            io_events := st.io_events ++ [{ name := name, conf := conf, inout := List.zip bytes bytes' }] }
          bytes'
      else
        .FFI_final { name := name, conf := conf, bytes := bytes, outcome := .FFI_failed }
    | .Oracle_final outcome =>
      .FFI_final { name := name, conf := conf, bytes := bytes, outcome := outcome }
  else
    .FFI_return st bytes

/-- HOL4 `panSem$state` (`'a := 64`). -/
structure PanState (θ : Type) where
  locals    : FMap String PanVal
  globals   : FMap String PanVal
  code      : FMap String (List (String × Shape) × PStmt)
  memory    : Word → Word
  memaddrs  : Word → Bool
  clock     : Nat
  be        : Bool
  ffi       : FFIState θ
  base_addr : Word
  top_addr  : Word

/-- Unified operational result (`Option panSem$result` flattened cleanly so `normal` = `NONE`,
    `TimeOut` = `SOME TimeOut`, `Error` = `SOME Error`, `ret v` = `SOME (Return v)`). -/
inductive PanResult where
  | normal
  | ret (v : PanVal)
  | break_
  | continue_
  | TimeOut
  | Error
  | finalFFI (ev : FinalEvent)
  deriving DecidableEq, Repr, Inhabited

export PanResult (TimeOut Error)

/-! ## 4. Expression & Statement Operational Semantics (`eval`, `evaluate`) -/

/-- HOL4 `asm$word_cmp`: signed `Less`/`NotLess` (`BitVec.slt`), unsigned `Lower`/`NotLower` (`BitVec.ult`). -/
def word_cmp : Cmp → Word → Word → Bool
  | .Equal,    w1, w2 => w1 == w2
  | .Less,     w1, w2 => BitVec.slt w1 w2
  | .Lower,    w1, w2 => BitVec.ult w1 w2
  | .Test,     w1, w2 => (w1 &&& w2) == 0#64
  | .NotEqual, w1, w2 => w1 != w2
  | .NotLess,  w1, w2 => !(BitVec.slt w1 w2)
  | .NotLower, w1, w2 => !(BitVec.ult w1 w2)
  | .NotTest,  w1, w2 => (w1 &&& w2) != 0#64

/-- HOL4 `wordLang$word_op`: `Sub` is strictly binary; `Add`/`And`/`Or`/`Xor` fold right. -/
def word_op : Binop → List Word → Option Word
  | .Add, ws       => some (ws.foldr (· + ·) 0#64)
  | .Sub, [w1, w2] => some (w1 - w2)
  | .Sub, _        => none
  | .And, ws       => some (ws.foldr (· &&& ·) (~~~ 0#64))
  | .Or,  ws       => some (ws.foldr (· ||| ·) 0#64)
  | .Xor, ws       => some (ws.foldr (· ^^^ ·) 0#64)

/-- HOL4 `panSem$pan_op`: `Mul` is strictly binary. -/
def pan_op : Panop → List Word → Option Word
  | .Mul, [w1, w2] => some (w1 * w2)
  | .Mul, _        => none

/-- HOL4 `wordLang$word_sh`: shift amounts `n ≥ 64` (with `n ≠ 0`) fail with `none`. -/
def word_sh (sh : Shift) (w : Word) (n : Nat) : Option Word :=
  if n != 0 && decide (n ≥ 64) then none
  else
    match sh with
    | .Lsl => some (w <<< n)
    | .Lsr => some (w >>> n)
    | .Asr => some (BitVec.sshiftRight w n)
    | .Ror => some (BitVec.rotateRight w n)

/-- Extract words from a list of `PanVal`s if all elements are `.word` (`EVERY is_word`). -/
def extractWords : List PanVal → Option (List Word)
  | [] => some []
  | .word w :: vs =>
    match extractWords vs with
    | some ws => some (w :: ws)
    | none => none
  | .rstruct _ :: _ => none
termination_by structural vs => vs

mutual
/-- HOL4 `panSem$mem_load`: load structured or word value from mapped word addresses. -/
def mem_load : Shape → Word → (Word → Bool) → (Word → Word) → Option PanVal
  | .One, addr, dm, m =>
    if dm addr then some (.word (m addr)) else none
  | .Comb shs, addr, dm, m =>
    match mem_load_fields shs addr dm m with
    | some vs => some (.rstruct vs)
    | none => none
termination_by structural sh => sh

def mem_load_fields : List Shape → Word → (Word → Bool) → (Word → Word) → Option (List PanVal)
  | [], _, _, _ => some []
  | sh :: shs, addr, dm, m =>
    match mem_load sh addr dm m with
    | none => none
    | some v =>
      let nextAddr := addr + BitVec.ofNat 64 (8 * size_of_shape sh)
      match mem_load_fields shs nextAddr dm m with
      | none => none
      | some vs => some (v :: vs)
termination_by structural shs => shs
end

/-- HOL4 `panSem$mem_store`: single-word store if `addr` is mapped in `dm`. -/
def mem_store (addr w : Word) (dm : Word → Bool) (m : Word → Word) : Option (Word → Word) :=
  if dm addr then some (UPDATE addr w m) else none

/-- HOL4 `panSem$mem_stores`: sequential multi-word store (`addr`, `addr + 8`, ...). -/
def mem_stores (a : Word) : List Word → (Word → Bool) → (Word → Word) → Option (Word → Word)
  | [], _, m => some m
  | w :: ws, dm, m =>
    match mem_store a w dm m with
    | none => none
    | some m' => mem_stores (a + 8#64) ws dm m'
termination_by structural ws => ws

/-- HOL4 `panSem$lookup_kvar`. -/
def lookup_kvar {θ : Type} (vk : VarKind) (v : String) (s : PanState θ) : Option PanVal :=
  match vk with
  | .Local  => s.locals v
  | .Global => s.globals v

/-- HOL4 `panSem$set_var`. -/
def set_var {θ : Type} (v : String) (val : PanVal) (s : PanState θ) : PanState θ :=
  { s with locals := FUPDATE s.locals (v, val) }

/-- HOL4 `panSem$set_global`. -/
def set_global {θ : Type} (v : String) (val : PanVal) (s : PanState θ) : PanState θ :=
  { s with globals := FUPDATE s.globals (v, val) }

/-- HOL4 `panSem$set_kvar`. -/
def set_kvar {θ : Type} (vk : VarKind) (v : String) (val : PanVal) (s : PanState θ) : PanState θ :=
  match vk with
  | .Local  => set_var v val s
  | .Global => set_global v val s

/-- HOL4 `panSem$is_valid_value`: target variable MUST already be bound with matching shape. -/
def is_valid_value {θ : Type} (s : PanState θ) (vk : VarKind) (v : String) (val : PanVal) : Bool :=
  match lookup_kvar vk v s with
  | none   => false
  | some w => shape_of val == shape_of w

/-- HOL4 `panSem$res_var`: restore shadowed variable (`none => DOMSUB`, `some v => FUPDATE`). -/
def res_var {α β : Type} [DecidableEq α] (lc : FMap α β) (kv : α × Option β) : FMap α β :=
  match kv.2 with
  | none   => DOMSUB lc kv.1
  | some v => FUPDATE lc (kv.1, v)

/-- HOL4 `panSem$empty_locals`. -/
def empty_locals {θ : Type} (s : PanState θ) : PanState θ :=
  { s with locals := FEMPTY }

/-- HOL4 `panSem$dec_clock`. -/
def dec_clock {θ : Type} (s : PanState θ) : PanState θ :=
  { s with clock := s.clock - 1 }

/-- HOL4 `panSem$fix_clock`: clamp returned clock to `min old_s.clock new_s.clock`. -/
def fix_clock {θ : Type} (old_s : PanState θ) (res : PanResult × PanState θ) :
    PanResult × PanState θ :=
  (res.1, { res.2 with clock := if old_s.clock < res.2.clock then old_s.clock else res.2.clock })

@[simp] theorem dec_clock_clock {θ : Type} (s : PanState θ) :
    (dec_clock s).clock = s.clock - 1 := rfl

theorem fix_clock_clock {θ : Type} (s : PanState θ) (r : PanResult × PanState θ) :
    (fix_clock s r).2.clock = if s.clock < r.2.clock then s.clock else r.2.clock := rfl

theorem fix_clock_le {θ : Type} (s : PanState θ) (r : PanResult × PanState θ) :
    (fix_clock s r).2.clock ≤ s.clock := by
  simp only [fix_clock_clock]
  split <;> omega

mutual
/-- HOL4 `panSem$eval`: total structural expression evaluator. -/
def eval {θ : Type} (s : PanState θ) : PExp → Option PanVal
  | .const w => some (.word w)
  | .var .Local v => s.locals v
  | .var .Global v => s.globals v
  | .rstruct es =>
    match evalList s es with
    | some vs => some (.rstruct vs)
    | none => none
  | .rfield idx target =>
    match eval s target with
    | some (.rstruct vs) => vs[idx]?
    | _ => none
  | .load sh addr =>
    match eval s addr with
    | some (.word w) => mem_load sh w s.memaddrs s.memory
    | _ => none
  | .loadByte addr =>
    match eval s addr with
    | some (.word w) =>
      match mem_load_byte s.memory s.memaddrs s.be w with
      | some b => some (.word (BitVec.setWidth 64 b))
      | none => none
    | _ => none
  | .binop op es =>
    match evalList s es with
    | some vs =>
      match extractWords vs with
      | some ws => (word_op op ws).map .word
      | none => none
    | none => none
  | .panop op es =>
    match evalList s es with
    | some vs =>
      match extractWords vs with
      | some ws => (pan_op op ws).map .word
      | none => none
    | none => none
  | .cmp c e1 e2 =>
    match eval s e1, eval s e2 with
    | some (.word w1), some (.word w2) =>
      some (.word (if word_cmp c w1 w2 then 1#64 else 0#64))
    | _, _ => none
  | .shift sh e n =>
    match eval s e with
    | some (.word w) => (word_sh sh w n).map .word
    | _ => none
  | .baseAddr => some (.word s.base_addr)
  | .topAddr => some (.word s.top_addr)
  | .bytesInWord => some (.word 8#64)
termination_by structural e => e

def evalList {θ : Type} (s : PanState θ) : List PExp → Option (List PanVal)
  | [] => some []
  | e :: es =>
    match eval s e, evalList s es with
    | some v, some vs => some (v :: vs)
    | _, _ => none
termination_by structural es => es
end

/-- Check that every parameter's declared shape matches its argument's runtime shape. -/
def shapesMatch : List (String × Shape) → List PanVal → Bool
  | [], [] => true
  | (_, sh) :: ps, v :: vs => (shape_of v == sh) && shapesMatch ps vs
  | _, _ => false
termination_by structural ps => ps

/-- Build callee local environment once `shapesMatch params argVals = true`. -/
def mkCalleeLocals (params : List (String × Shape)) (argVals : List PanVal) : FMap String PanVal :=
  FUPDATE_LIST FEMPTY (List.zip (params.map Prod.fst) argVals)

/-- Single clock-layer structural statement evaluator (`termination_by structural stmt`). -/
def evaluateStep {θ : Type}
    (stepLower : PStmt → PanState θ → PanResult × PanState θ)
    (stmt : PStmt) (s : PanState θ) : PanResult × PanState θ :=
  match stmt with
  | .skip => (.normal, s)
  | .dec v sh e body =>
    match eval s e with
    | none => (.Error, s)
    | some val =>
      if sh == shape_of val then
        let r := evaluateStep stepLower body { s with locals := FUPDATE s.locals (v, val) }
        (r.1, { r.2 with locals := res_var r.2.locals (v, s.locals v) })
      else
        (.Error, s)
  | .assign vk v src =>
    match eval s src with
    | none => (.Error, s)
    | some val =>
      if is_valid_value s vk v val then
        (.normal, set_kvar vk v val s)
      else
        (.Error, s)
  | .store dst src =>
    match eval s dst, eval s src with
    | some (.word addr), some val =>
      match mem_stores addr (flatten val) s.memaddrs s.memory with
      | none => (.Error, s)
      | some m' => (.normal, { s with memory := m' })
    | _, _ => (.Error, s)
  | .storeByte dst src =>
    match eval s dst, eval s src with
    | some (.word addr), some (.word w) =>
      match mem_store_byte s.memory s.memaddrs s.be addr (BitVec.setWidth 8 w) with
      | none => (.Error, s)
      | some m' => (.normal, { s with memory := m' })
    | _, _ => (.Error, s)
  | .seq c1 c2 =>
    let r1 := fix_clock s (evaluateStep stepLower c1 s)
    if r1.1 == .normal then
      evaluateStep stepLower c2 r1.2
    else
      r1
  | .ite cond c1 c2 =>
    match eval s cond with
    | some (.word w) =>
      if w != 0#64 then evaluateStep stepLower c1 s else evaluateStep stepLower c2 s
    | _ => (.Error, s)
  | .break_ => (.break_, s)
  | .continue_ => (.continue_, s)
  | .while_ cond body =>
    match eval s cond with
    | some (.word w) =>
      if w != 0#64 then
        if s.clock == 0 then
          (.TimeOut, empty_locals s)
        else
          let r1 := fix_clock (dec_clock s) (stepLower body (dec_clock s))
          match r1.1 with
          | .normal    => stepLower (.while_ cond body) r1.2
          | .continue_ => stepLower (.while_ cond body) r1.2
          | .break_    => (.normal, r1.2)
          | other      => (other, r1.2)
      else
        (.normal, s)
    | _ => (.Error, s)
  | .call retTarget fname args =>
    match evalList s args, s.code fname with
    | some argVals, some (params, calleeBody) =>
      if shapesMatch params argVals then
        if s.clock == 0 then
          (.TimeOut, empty_locals s)
        else
          let calleeSt := { dec_clock s with locals := mkCalleeLocals params argVals }
          let r1 := fix_clock (dec_clock s) (stepLower calleeBody calleeSt)
          match r1.1 with
          | .ret retVal =>
            match retTarget with
            | none => (.ret retVal, empty_locals r1.2)
            | some (vk, v) =>
              if is_valid_value s vk v retVal then
                (.normal, set_kvar vk v retVal { r1.2 with locals := s.locals })
              else
                (.Error, r1.2)
          | .TimeOut       => (.TimeOut, empty_locals r1.2)
          | .finalFFI ev   => (.finalFFI ev, empty_locals r1.2)
          | .Error         => (.Error, r1.2)
          | .normal        => (.Error, r1.2)
          | .break_        => (.Error, r1.2)
          | .continue_     => (.Error, r1.2)
      else
        (.Error, s)
    | _, _ => (.Error, s)
  | .decCall v sh fname args cont =>
    match evalList s args, s.code fname with
    | some argVals, some (params, calleeBody) =>
      if shapesMatch params argVals then
        if s.clock == 0 then
          (.TimeOut, empty_locals s)
        else
          let calleeSt := { dec_clock s with locals := mkCalleeLocals params argVals }
          let r1 := fix_clock (dec_clock s) (stepLower calleeBody calleeSt)
          match r1.1 with
          | .ret retVal =>
            if sh == shape_of retVal then
              let contSt := { r1.2 with locals := FUPDATE s.locals (v, retVal) }
              let r2 := stepLower cont contSt
              (r2.1, { r2.2 with locals := res_var r2.2.locals (v, s.locals v) })
            else
              (.Error, r1.2)
          | .TimeOut       => (.TimeOut, empty_locals r1.2)
          | .finalFFI ev   => (.finalFFI ev, empty_locals r1.2)
          | .Error         => (.Error, r1.2)
          | .normal        => (.Error, r1.2)
          | .break_        => (.Error, r1.2)
          | .continue_     => (.Error, r1.2)
      else
        (.Error, s)
    | _, _ => (.Error, s)
  | .ret e =>
    match eval s e with
    | none => (.Error, s)
    | some val =>
      if decide (size_of_shape (shape_of val) ≤ 32) then
        (.ret val, empty_locals s)
      else
        (.Error, s)
  | .tick =>
    if s.clock == 0 then
      (.TimeOut, empty_locals s)
    else
      (.normal, dec_clock s)
  | .annot _ _ => (.normal, s)
  | .extCall ffiName ptr1 len1 ptr2 len2 =>
    match eval s ptr1, eval s len1, eval s ptr2, eval s len2 with
    | some (.word ad1), some (.word sz1), some (.word ad2), some (.word sz2) =>
      match read_bytearray ad1 sz1.toNat (mem_load_byte s.memory s.memaddrs s.be),
            read_bytearray ad2 sz2.toNat (mem_load_byte s.memory s.memaddrs s.be) with
      | some confBytes, some arrBytes =>
        match call_FFI s.ffi ffiName confBytes arrBytes with
        | .FFI_return newFFI newBytes =>
          let nmem := write_bytearray ad2 newBytes s.memory s.memaddrs s.be
          (.normal, { s with ffi := newFFI, memory := nmem })
        | .FFI_final ev =>
          (.finalFFI ev, empty_locals s)
      | _, _ => (.Error, s)
    | _, _, _, _ => (.Error, s)
termination_by structural stmt

/-- Outer clock-fuel tower (`termination_by structural f => f`). -/
def evaluateFuel {θ : Type} : Nat → PStmt → PanState θ → PanResult × PanState θ
  | 0, stmt, s => evaluateStep (fun _ s' => (.TimeOut, empty_locals s')) stmt s
  | fuel + 1, stmt, s => evaluateStep (evaluateFuel fuel) stmt s
termination_by structural f => f

/-- HOL4 `panSem$evaluate`: clocked big-step operational semantics (`0 WellFounded.fix`). -/
def evaluate {θ : Type} (stmt : PStmt) (s : PanState θ) : PanResult × PanState θ :=
  evaluateFuel s.clock stmt s

/-! ## 5. Fuel Independence, Unfolding Equations, Clock Monotonicity & `StateWF` -/

private theorem evaluateStep_congr {θ : Type}
    (step1 step2 : PStmt → PanState θ → PanResult × PanState θ)
    (B : Nat)
    (hstep : ∀ p (st : PanState θ), st.clock < B → step1 p st = step2 p st) :
    ∀ (stmt : PStmt) (s : PanState θ), s.clock ≤ B →
      evaluateStep step1 stmt s = evaluateStep step2 stmt s := by
  intro stmt
  induction stmt with
  | skip | assign _ _ _ | store _ _ | storeByte _ _ | break_ | continue_
  | ret _ | tick | annot _ _ | extCall _ _ _ _ _ =>
    intro _ _; rfl
  | dec v sh e body ih =>
    intro s hs
    simp only [evaluateStep]
    cases he : eval s e with
    | none => rfl
    | some val =>
      dsimp only
      split
      · rw [ih { s with locals := FUPDATE s.locals (v, val) } hs]
      · rfl
  | seq c1 c2 ih1 ih2 =>
    intro s hs
    simp only [evaluateStep]
    rw [ih1 s hs]
    have hfc : (fix_clock s (evaluateStep step2 c1 s)).2.clock ≤ B :=
      Nat.le_trans (fix_clock_le s _) hs
    split
    · exact ih2 _ hfc
    · rfl
  | ite cond c1 c2 ih1 ih2 =>
    intro s hs
    simp only [evaluateStep]
    cases he : eval s cond with
    | none => rfl
    | some val =>
      cases val with
      | rstruct _ => rfl
      | word w =>
        dsimp only
        split
        · exact ih1 s hs
        · exact ih2 s hs
  | while_ cond body _ =>
    intro s hs
    simp only [evaluateStep]
    cases he : eval s cond with
    | none => rfl
    | some val =>
      cases val with
      | rstruct _ => rfl
      | word w =>
        dsimp only
        split
        · split
          · rfl
          · rename_i hclk
            have hpos : 0 < s.clock := by
              cases hsc : s.clock with
              | zero => simp [hsc] at hclk
              | succ _ => omega
            have h1 : step1 body (dec_clock s) = step2 body (dec_clock s) :=
              hstep body (dec_clock s) (by simp [dec_clock]; omega)
            rw [h1]
            have h2 : (fix_clock (dec_clock s) (step2 body (dec_clock s))).2.clock < B :=
              Nat.lt_of_le_of_lt (fix_clock_le (dec_clock s) _) (by simp [dec_clock]; omega)
            cases hr1 : (fix_clock (dec_clock s) (step2 body (dec_clock s))).1 <;> dsimp only <;>
              first | rfl | exact hstep (.while_ cond body) _ h2
        · rfl
  | call retTarget fname args =>
    intro s hs
    simp only [evaluateStep]
    cases ha : evalList s args with
    | none => rfl
    | some argVals =>
      cases hc : s.code fname with
      | none => rfl
      | some entry =>
        obtain ⟨params, calleeBody⟩ := entry
        dsimp only
        split
        · split
          · rfl
          · rename_i hclk
            have hpos : 0 < s.clock := by
              cases hsc : s.clock with
              | zero => simp [hsc] at hclk
              | succ _ => omega
            let calleeSt := { dec_clock s with locals := mkCalleeLocals params argVals }
            have h1 : step1 calleeBody calleeSt = step2 calleeBody calleeSt :=
              hstep calleeBody calleeSt (by simp [calleeSt, dec_clock]; omega)
            rw [h1]
        · rfl
  | decCall v sh fname args cont _ =>
    intro s hs
    simp only [evaluateStep]
    cases ha : evalList s args with
    | none => rfl
    | some argVals =>
      cases hc : s.code fname with
      | none => rfl
      | some entry =>
        obtain ⟨params, calleeBody⟩ := entry
        dsimp only
        split
        · split
          · rfl
          · rename_i hclk
            have hpos : 0 < s.clock := by
              cases hsc : s.clock with
              | zero => simp [hsc] at hclk
              | succ _ => omega
            let calleeSt := { dec_clock s with locals := mkCalleeLocals params argVals }
            have h1 : step1 calleeBody calleeSt = step2 calleeBody calleeSt :=
              hstep calleeBody calleeSt (by simp [calleeSt, dec_clock]; omega)
            rw [h1]
            have hfc : (fix_clock (dec_clock s) (step2 calleeBody calleeSt)).2.clock < B :=
              Nat.lt_of_le_of_lt (fix_clock_le (dec_clock s) _) (by simp [dec_clock]; omega)
            cases hr1 : (fix_clock (dec_clock s) (step2 calleeBody calleeSt)).1 with
            | ret retVal =>
              dsimp only
              split
              · let contSt := { (fix_clock (dec_clock s) (step2 calleeBody calleeSt)).2 with
                                locals := FUPDATE s.locals (v, retVal) }
                rw [hstep cont contSt hfc]
              · rfl
            | _ => rfl
        · rfl

private theorem evaluateFuel_eq {θ : Type} (f1 : Nat) :
    ∀ (f2 : Nat) (stmt : PStmt) (s : PanState θ),
      s.clock ≤ f1 → s.clock ≤ f2 →
      evaluateFuel f1 stmt s = evaluateFuel f2 stmt s := by
  induction f1 with
  | zero =>
    intro f2 stmt s h1 _
    cases f2 with
    | zero => rfl
    | succ k =>
      exact evaluateStep_congr _ _ 0 (fun _ _ hlt => absurd hlt (Nat.not_lt_zero _)) stmt s h1
  | succ k1 ih =>
    intro f2 stmt s h1 h2
    cases f2 with
    | zero =>
      exact (evaluateStep_congr _ _ 0 (fun _ _ hlt => absurd hlt (Nat.not_lt_zero _)) stmt s h2).symm
    | succ k2 =>
      exact evaluateStep_congr (evaluateFuel k1) (evaluateFuel k2)
        (if k1 ≤ k2 then k1 + 1 else k2 + 1)
        (fun p st hlt => ih k2 p st (by split at hlt <;> omega) (by split at hlt <;> omega))
        stmt s (by split <;> omega)

/-- Master unfolding identity: `evaluate` is a fixed point of `evaluateStep`. -/
theorem evaluate_eq_step {θ : Type} (stmt : PStmt) (s : PanState θ) :
    evaluate stmt s = evaluateStep evaluate stmt s := by
  unfold evaluate
  cases hclk : s.clock with
  | zero =>
    exact evaluateStep_congr _ _ 0 (fun _ _ hlt => absurd hlt (Nat.not_lt_zero _)) stmt s (by omega)
  | succ k =>
    exact evaluateStep_congr (evaluateFuel k) (fun p st => evaluateFuel st.clock p st) (k + 1)
      (fun p st hlt => evaluateFuel_eq k st.clock p st (by omega) (Nat.le_refl _))
      stmt s (by omega)

private def PreservesConfig {θ : Type} (s0 s1 : PanState θ) : Prop :=
  s1.clock ≤ s0.clock ∧
  s1.memaddrs = s0.memaddrs ∧
  s1.code = s0.code ∧
  s1.be = s0.be ∧
  s1.base_addr = s0.base_addr ∧
  s1.top_addr = s0.top_addr

private theorem PreservesConfig.refl {θ : Type} (s : PanState θ) : PreservesConfig s s :=
  ⟨Nat.le_refl _, rfl, rfl, rfl, rfl, rfl⟩

private theorem PreservesConfig.trans {θ : Type} {s0 s1 s2 : PanState θ}
    (h1 : PreservesConfig s0 s1) (h2 : PreservesConfig s1 s2) : PreservesConfig s0 s2 :=
  ⟨Nat.le_trans h2.1 h1.1,
   h2.2.1.trans h1.2.1,
   h2.2.2.1.trans h1.2.2.1,
   h2.2.2.2.1.trans h1.2.2.2.1,
   h2.2.2.2.2.1.trans h1.2.2.2.2.1,
   h2.2.2.2.2.2.trans h1.2.2.2.2.2⟩

private theorem PreservesConfig.fix_clock_of {θ : Type} (s0 : PanState θ) (r : PanResult × PanState θ)
    (h : PreservesConfig s0 r.2) : PreservesConfig s0 (fix_clock s0 r).2 :=
  ⟨fix_clock_le s0 r, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem evaluateStep_clock_and_config {θ : Type}
    (stepLower : PStmt → PanState θ → PanResult × PanState θ)
    (hLower : ∀ p (st : PanState θ), PreservesConfig st (stepLower p st).2) :
    ∀ (stmt : PStmt) (s : PanState θ), PreservesConfig s (evaluateStep stepLower stmt s).2 := by
  intro stmt
  induction stmt with
  | skip | break_ | continue_ | annot _ _ =>
    intro s; exact PreservesConfig.refl s
  | tick =>
    intro s; simp only [evaluateStep]
    split
    · exact ⟨Nat.le_refl _, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨by simp [dec_clock], rfl, rfl, rfl, rfl, rfl⟩
  | ret e =>
    intro s; simp only [evaluateStep]
    cases he : eval s e with
    | none => exact PreservesConfig.refl s
    | some _ => dsimp only; split <;> exact ⟨Nat.le_refl _, rfl, rfl, rfl, rfl, rfl⟩
  | dec v sh e body ih =>
    intro s; simp only [evaluateStep]
    cases he : eval s e with
    | none => exact PreservesConfig.refl s
    | some val =>
      dsimp only; split
      · have h := ih { s with locals := FUPDATE s.locals (v, val) }
        exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
      · exact PreservesConfig.refl s
  | assign vk v src =>
    intro s; simp only [evaluateStep]
    cases he : eval s src with
    | none => exact PreservesConfig.refl s
    | some _ =>
      dsimp only; split
      · cases vk <;> exact ⟨Nat.le_refl _, rfl, rfl, rfl, rfl, rfl⟩
      · exact PreservesConfig.refl s
  | store dst src =>
    intro s; simp only [evaluateStep]
    cases hd : eval s dst with
    | none => exact PreservesConfig.refl s
    | some dv =>
      cases dv with
      | rstruct _ => exact PreservesConfig.refl s
      | word addr =>
        cases hs : eval s src with
        | none => exact PreservesConfig.refl s
        | some sv =>
          dsimp only
          cases mem_stores addr (flatten sv) s.memaddrs s.memory <;>
            exact ⟨Nat.le_refl _, rfl, rfl, rfl, rfl, rfl⟩
  | storeByte dst src =>
    intro s; simp only [evaluateStep]
    cases hd : eval s dst with
    | none => exact PreservesConfig.refl s
    | some dv =>
      cases dv with
      | rstruct _ => exact PreservesConfig.refl s
      | word addr =>
        cases hs : eval s src with
        | none => exact PreservesConfig.refl s
        | some sv =>
          cases sv with
          | rstruct _ => exact PreservesConfig.refl s
          | word w =>
            dsimp only
            cases mem_store_byte s.memory s.memaddrs s.be addr (BitVec.setWidth 8 w) <;>
              exact ⟨Nat.le_refl _, rfl, rfl, rfl, rfl, rfl⟩
  | seq c1 c2 ih1 ih2 =>
    intro s; simp only [evaluateStep]
    have hfc := PreservesConfig.fix_clock_of s _ (ih1 s)
    split
    · exact hfc.trans (ih2 _)
    · exact hfc
  | ite cond c1 c2 ih1 ih2 =>
    intro s; simp only [evaluateStep]
    cases hc : eval s cond with
    | none => exact PreservesConfig.refl s
    | some val =>
      cases val with
      | rstruct _ => exact PreservesConfig.refl s
      | word _ => dsimp only; split; exact ih1 s; exact ih2 s
  | while_ cond body _ =>
    intro s; simp only [evaluateStep]
    cases hc : eval s cond with
    | none => exact PreservesConfig.refl s
    | some val =>
      cases val with
      | rstruct _ => exact PreservesConfig.refl s
      | word _ =>
        dsimp only; split
        · split
          · exact ⟨Nat.le_refl _, rfl, rfl, rfl, rfl, rfl⟩
          · have hdec : PreservesConfig s (dec_clock s) :=
              ⟨by simp [dec_clock], rfl, rfl, rfl, rfl, rfl⟩
            have hfc := hdec.trans (PreservesConfig.fix_clock_of (dec_clock s) _ (hLower body (dec_clock s)))
            cases hr1 : (fix_clock (dec_clock s) (stepLower body (dec_clock s))).1 <;> dsimp only <;>
              first | exact hfc | exact hfc.trans (hLower (.while_ cond body) _)
        · exact PreservesConfig.refl s
  | call retTarget fname args =>
    intro s; simp only [evaluateStep]
    cases ha : evalList s args with
    | none => exact PreservesConfig.refl s
    | some argVals =>
      cases hc : s.code fname with
      | none => exact PreservesConfig.refl s
      | some entry =>
        obtain ⟨params, calleeBody⟩ := entry
        dsimp only; split
        · split
          · exact ⟨Nat.le_refl _, rfl, rfl, rfl, rfl, rfl⟩
          · let calleeSt := { dec_clock s with locals := mkCalleeLocals params argVals }
            have hcal : PreservesConfig s calleeSt :=
              ⟨by simp [calleeSt, dec_clock], rfl, rfl, rfl, rfl, rfl⟩
            have hfc := hcal.trans
              (PreservesConfig.fix_clock_of (dec_clock s) _
                (by
                  have h := hLower calleeBody calleeSt
                  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩))
            cases hr1 : (fix_clock (dec_clock s) (stepLower calleeBody calleeSt)).1 with
            | ret retVal =>
              dsimp only
              cases retTarget with
              | none => exact ⟨hfc.1, hfc.2.1, hfc.2.2.1, hfc.2.2.2.1, hfc.2.2.2.2.1, hfc.2.2.2.2.2⟩
              | some vk_v =>
                obtain ⟨vk, v⟩ := vk_v
                dsimp only; split
                · cases vk <;> exact ⟨hfc.1, hfc.2.1, hfc.2.2.1, hfc.2.2.2.1, hfc.2.2.2.2.1, hfc.2.2.2.2.2⟩
                · exact hfc
            | TimeOut | finalFFI _ =>
              exact ⟨hfc.1, hfc.2.1, hfc.2.2.1, hfc.2.2.2.1, hfc.2.2.2.2.1, hfc.2.2.2.2.2⟩
            | _ => exact hfc
        · exact PreservesConfig.refl s
  | decCall v sh fname args cont _ =>
    intro s; simp only [evaluateStep]
    cases ha : evalList s args with
    | none => exact PreservesConfig.refl s
    | some argVals =>
      cases hc : s.code fname with
      | none => exact PreservesConfig.refl s
      | some entry =>
        obtain ⟨params, calleeBody⟩ := entry
        dsimp only; split
        · split
          · exact ⟨Nat.le_refl _, rfl, rfl, rfl, rfl, rfl⟩
          · let calleeSt := { dec_clock s with locals := mkCalleeLocals params argVals }
            have hcal : PreservesConfig s calleeSt :=
              ⟨by simp [calleeSt, dec_clock], rfl, rfl, rfl, rfl, rfl⟩
            have hfc := hcal.trans
              (PreservesConfig.fix_clock_of (dec_clock s) _
                (by
                  have h := hLower calleeBody calleeSt
                  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩))
            cases hr1 : (fix_clock (dec_clock s) (stepLower calleeBody calleeSt)).1 with
            | ret retVal =>
              dsimp only; split
              · let contSt := { (fix_clock (dec_clock s) (stepLower calleeBody calleeSt)).2 with
                                locals := FUPDATE s.locals (v, retVal) }
                have hc2 : PreservesConfig s contSt :=
                  ⟨hfc.1, hfc.2.1, hfc.2.2.1, hfc.2.2.2.1, hfc.2.2.2.2.1, hfc.2.2.2.2.2⟩
                have hcont := hc2.trans (hLower cont contSt)
                exact ⟨hcont.1, hcont.2.1, hcont.2.2.1, hcont.2.2.2.1, hcont.2.2.2.2.1, hcont.2.2.2.2.2⟩
              · exact hfc
            | TimeOut | finalFFI _ =>
              exact ⟨hfc.1, hfc.2.1, hfc.2.2.1, hfc.2.2.2.1, hfc.2.2.2.2.1, hfc.2.2.2.2.2⟩
            | _ => exact hfc
        · exact PreservesConfig.refl s
  | extCall ffiName ptr1 len1 ptr2 len2 =>
    intro s; simp only [evaluateStep]
    cases h1 : eval s ptr1 with
    | none => exact PreservesConfig.refl s
    | some v1 =>
      cases v1 with
      | rstruct _ => exact PreservesConfig.refl s
      | word ad1 =>
        cases h2 : eval s len1 with
        | none => exact PreservesConfig.refl s
        | some v2 =>
          cases v2 with
          | rstruct _ => exact PreservesConfig.refl s
          | word sz1 =>
            cases h3 : eval s ptr2 with
            | none => exact PreservesConfig.refl s
            | some v3 =>
              cases v3 with
              | rstruct _ => exact PreservesConfig.refl s
              | word ad2 =>
                cases h4 : eval s len2 with
                | none => exact PreservesConfig.refl s
                | some v4 =>
                  cases v4 with
                  | rstruct _ => exact PreservesConfig.refl s
                  | word sz2 =>
                    dsimp only
                    cases hr1 : read_bytearray ad1 sz1.toNat (mem_load_byte s.memory s.memaddrs s.be) with
                    | none => exact PreservesConfig.refl s
                    | some confBytes =>
                      cases hr2 : read_bytearray ad2 sz2.toNat (mem_load_byte s.memory s.memaddrs s.be) with
                      | none => exact PreservesConfig.refl s
                      | some arrBytes =>
                        dsimp only
                        cases call_FFI s.ffi ffiName confBytes arrBytes <;>
                          exact ⟨Nat.le_refl _, rfl, rfl, rfl, rfl, rfl⟩

private theorem evaluateFuel_clock_and_config {θ : Type} (fuel : Nat) :
    ∀ (stmt : PStmt) (s : PanState θ),
      PreservesConfig s (evaluateFuel fuel stmt s).2 := by
  induction fuel with
  | zero =>
    intro stmt s
    exact evaluateStep_clock_and_config _ (fun _ _ => ⟨Nat.le_refl _, rfl, rfl, rfl, rfl, rfl⟩) stmt s
  | succ f ih =>
    intro stmt s
    exact evaluateStep_clock_and_config _ ih stmt s

/-- Fundamental HOL4 `panSemProps$evaluate_clock`: `evaluate` never increases `s.clock`
    and preserves read-only configuration (`memaddrs`, `code`, `be`, `base_addr`, `top_addr`). -/
theorem evaluate_clock_and_config {θ : Type} (stmt : PStmt) (s : PanState θ) :
    (evaluate stmt s).2.clock ≤ s.clock ∧
    (evaluate stmt s).2.memaddrs = s.memaddrs ∧
    (evaluate stmt s).2.code = s.code ∧
    (evaluate stmt s).2.be = s.be ∧
    (evaluate stmt s).2.base_addr = s.base_addr ∧
    (evaluate stmt s).2.top_addr = s.top_addr :=
  evaluateFuel_clock_and_config s.clock stmt s

theorem evaluate_clock_le {θ : Type} (stmt : PStmt) (s : PanState θ) :
    (evaluate stmt s).2.clock ≤ s.clock :=
  (evaluate_clock_and_config stmt s).1

/-- Because `evaluate` never increases `s1.clock`, `fix_clock s0 (evaluate stmt s1)` is an identity whenever `s1.clock ≤ s0.clock`. -/
theorem fix_clock_evaluate_of_clock_le {θ : Type} (s0 s1 : PanState θ) (stmt : PStmt)
    (hclk : s1.clock ≤ s0.clock) :
    fix_clock s0 (evaluate stmt s1) = evaluate stmt s1 := by
  have hle := evaluate_clock_le stmt s1
  cases hev : evaluate stmt s1 with
  | mk r s2 =>
    rw [hev] at hle
    dsimp only at hle
    simp only [fix_clock]
    have hnotlt : ¬ (s0.clock < s2.clock) := by omega
    simp [hnotlt]

@[simp] theorem fix_clock_evaluate {θ : Type} (s : PanState θ) (stmt : PStmt) :
    fix_clock s (evaluate stmt s) = evaluate stmt s :=
  fix_clock_evaluate_of_clock_le s s stmt (Nat.le_refl _)

/-- Structural well-formedness of a `PanState`: arena bounds `base_addr ≤ top_addr` and
    every registered function in `s.code` has pairwise-distinct parameter names (`Nodup`). -/
def StateWF {θ : Type} (s : PanState θ) : Prop :=
  s.base_addr.toNat ≤ s.top_addr.toNat ∧
  ∀ fname params body, s.code fname = some (params, body) → (params.map Prod.fst).Nodup

theorem evaluate_preserves_stateWF {θ : Type} (stmt : PStmt) (s : PanState θ)
    (hwf : StateWF s) : StateWF (evaluate stmt s).2 := by
  have hc := evaluate_clock_and_config stmt s
  refine ⟨?_, ?_⟩
  · rw [hc.2.2.2.2.1, hc.2.2.2.2.2]; exact hwf.1
  · rw [hc.2.2.1]; exact hwf.2

/-! ## 6. Exported Unfolding Equations for `eval` and `evaluate` -/

@[simp] theorem eval_const {θ : Type} (s : PanState θ) (w : Word) :
    eval s (.const w) = some (.word w) := rfl

@[simp] theorem eval_lvar {θ : Type} (s : PanState θ) (v : String) :
    eval s (.lvar v) = s.locals v := rfl

@[simp] theorem eval_var_local {θ : Type} (s : PanState θ) (v : String) :
    eval s (.var .Local v) = s.locals v := rfl

@[simp] theorem eval_rstruct {θ : Type} (s : PanState θ) (es : List PExp) :
    eval s (.rstruct es) = (evalList s es).map .rstruct := by
  simp only [eval]
  cases evalList s es <;> rfl

@[simp] theorem eval_rfield {θ : Type} (s : PanState θ) (idx : Nat) (e : PExp) :
    eval s (.rfield idx e) =
      match eval s e with
      | some (.rstruct vs) => vs[idx]?
      | _ => none := rfl

@[simp] theorem eval_loadByte {θ : Type} (s : PanState θ) (addr : PExp) :
    eval s (.loadByte addr) =
      match eval s addr with
      | some (.word w) => (mem_load_byte s.memory s.memaddrs s.be w).map (fun b => .word (BitVec.setWidth 64 b))
      | _ => none := by
  simp only [eval]
  cases ha : eval s addr with
  | none => rfl
  | some v =>
    cases v with
    | rstruct _ => rfl
    | word w => dsimp only; cases mem_load_byte s.memory s.memaddrs s.be w <;> rfl

@[simp] theorem eval_cmp {θ : Type} (s : PanState θ) (c : Cmp) (e1 e2 : PExp) :
    eval s (.cmp c e1 e2) =
      match eval s e1, eval s e2 with
      | some (.word w1), some (.word w2) =>
        some (.word (if word_cmp c w1 w2 then 1#64 else 0#64))
      | _, _ => none := rfl

@[simp] theorem eval_binop2 {θ : Type} (s : PanState θ) (op : Binop) (e1 e2 : PExp) :
    eval s (.binop op [e1, e2]) =
      match eval s e1, eval s e2 with
      | some (.word w1), some (.word w2) => (word_op op [w1, w2]).map .word
      | _, _ => none := by
  simp only [eval, evalList]
  cases eval s e1 with
  | none => rfl
  | some v1 =>
    cases eval s e2 with
    | none => cases v1 <;> rfl
    | some v2 =>
      cases v1 <;> cases v2 <;> rfl

@[simp] theorem eval_panop2 {θ : Type} (s : PanState θ) (op : Panop) (e1 e2 : PExp) :
    eval s (.panop op [e1, e2]) =
      match eval s e1, eval s e2 with
      | some (.word w1), some (.word w2) => (pan_op op [w1, w2]).map .word
      | _, _ => none := by
  simp only [eval, evalList]
  cases eval s e1 with
  | none => rfl
  | some v1 =>
    cases eval s e2 with
    | none => cases v1 <;> rfl
    | some v2 =>
      cases v1 <;> cases v2 <;> rfl

@[simp] theorem evalList_nil {θ : Type} (s : PanState θ) :
    evalList s [] = some [] := rfl

@[simp] theorem evalList_cons {θ : Type} (s : PanState θ) (e : PExp) (es : List PExp) :
    evalList s (e :: es) =
      match eval s e, evalList s es with
      | some v, some vs => some (v :: vs)
      | _, _ => none := rfl

theorem evaluate_skip {θ : Type} (s : PanState θ) :
    evaluate .skip s = (.normal, s) :=
  evaluate_eq_step .skip s

theorem evaluate_tick {θ : Type} (s : PanState θ) :
    evaluate .tick s =
      (if s.clock == 0 then (.TimeOut, empty_locals s) else (.normal, dec_clock s)) :=
  evaluate_eq_step .tick s

theorem evaluate_dec {θ : Type} (v : String) (sh : Shape) (e : PExp) (body : PStmt) (s : PanState θ) :
    evaluate (.dec v sh e body) s =
      match eval s e with
      | none => (.Error, s)
      | some val =>
        if sh == shape_of val then
          let r := evaluate body { s with locals := FUPDATE s.locals (v, val) }
          (r.1, { r.2 with locals := res_var r.2.locals (v, s.locals v) })
        else
          (.Error, s) := by
  rw [evaluate_eq_step]
  simp only [evaluateStep]
  cases he : eval s e with
  | none => rfl
  | some val =>
    dsimp only
    split
    · rw [← evaluate_eq_step]
    · rfl

theorem evaluate_assign {θ : Type} (vk : VarKind) (v : String) (src : PExp) (s : PanState θ) :
    evaluate (.assign vk v src) s =
      match eval s src with
      | none => (.Error, s)
      | some val =>
        if is_valid_value s vk v val then (.normal, set_kvar vk v val s) else (.Error, s) :=
  evaluate_eq_step (.assign vk v src) s

theorem evaluate_store {θ : Type} (dst src : PExp) (s : PanState θ) :
    evaluate (.store dst src) s =
      match eval s dst, eval s src with
      | some (.word addr), some val =>
        match mem_stores addr (flatten val) s.memaddrs s.memory with
        | none => (.Error, s)
        | some m' => (.normal, { s with memory := m' })
      | _, _ => (.Error, s) :=
  evaluate_eq_step (.store dst src) s

theorem evaluate_storeByte {θ : Type} (dst src : PExp) (s : PanState θ) :
    evaluate (.storeByte dst src) s =
      match eval s dst, eval s src with
      | some (.word addr), some (.word w) =>
        match mem_store_byte s.memory s.memaddrs s.be addr (BitVec.setWidth 8 w) with
        | none => (.Error, s)
        | some m' => (.normal, { s with memory := m' })
      | _, _ => (.Error, s) :=
  evaluate_eq_step (.storeByte dst src) s

theorem evaluate_seq {θ : Type} (c1 c2 : PStmt) (s : PanState θ) :
    evaluate (.seq c1 c2) s =
      let r1 := evaluate c1 s
      if r1.1 == .normal then evaluate c2 r1.2 else r1 := by
  rw [evaluate_eq_step]
  simp only [evaluateStep, ← evaluate_eq_step, fix_clock_evaluate]

theorem evaluate_ite {θ : Type} (cond : PExp) (c1 c2 : PStmt) (s : PanState θ) :
    evaluate (.ite cond c1 c2) s =
      match eval s cond with
      | some (.word w) => if w != 0#64 then evaluate c1 s else evaluate c2 s
      | _ => (.Error, s) := by
  rw [evaluate_eq_step]
  simp only [evaluateStep]
  cases hc : eval s cond with
  | none => rfl
  | some val =>
    cases val with
    | rstruct _ => rfl
    | word w => dsimp only; split <;> rw [← evaluate_eq_step]

theorem evaluate_while {θ : Type} (cond : PExp) (body : PStmt) (s : PanState θ) :
    evaluate (.while_ cond body) s =
      match eval s cond with
      | some (.word w) =>
        if w != 0#64 then
          if s.clock == 0 then
            (.TimeOut, empty_locals s)
          else
            let r1 := evaluate body (dec_clock s)
            match r1.1 with
            | .normal    => evaluate (.while_ cond body) r1.2
            | .continue_ => evaluate (.while_ cond body) r1.2
            | .break_    => (.normal, r1.2)
            | other      => (other, r1.2)
        else
          (.normal, s)
      | _ => (.Error, s) := by
  conv => lhs; rw [evaluate_eq_step]
  simp only [evaluateStep]
  cases hc : eval s cond with
  | none => rfl
  | some val =>
    cases val with
    | rstruct _ => rfl
    | word w =>
      dsimp only
      split
      · split
        · rfl
        · rw [fix_clock_evaluate]
      · rfl

theorem evaluate_call {θ : Type} (retTarget : Option (VarKind × String)) (fname : String)
    (args : List PExp) (s : PanState θ) :
    evaluate (.call retTarget fname args) s =
      match evalList s args, s.code fname with
      | some argVals, some (params, calleeBody) =>
        if shapesMatch params argVals then
          if s.clock == 0 then
            (.TimeOut, empty_locals s)
          else
            let calleeSt := { dec_clock s with locals := mkCalleeLocals params argVals }
            let r1 := evaluate calleeBody calleeSt
            match r1.1 with
            | .ret retVal =>
              match retTarget with
              | none => (.ret retVal, empty_locals r1.2)
              | some (vk, v) =>
                if is_valid_value s vk v retVal then
                  (.normal, set_kvar vk v retVal { r1.2 with locals := s.locals })
                else
                  (.Error, r1.2)
            | .TimeOut       => (.TimeOut, empty_locals r1.2)
            | .finalFFI ev   => (.finalFFI ev, empty_locals r1.2)
            | .Error         => (.Error, r1.2)
            | .normal        => (.Error, r1.2)
            | .break_        => (.Error, r1.2)
            | .continue_     => (.Error, r1.2)
        else
          (.Error, s)
      | _, _ => (.Error, s) := by
  conv => lhs; rw [evaluate_eq_step]
  simp only [evaluateStep]
  cases ha : evalList s args with
  | none => rfl
  | some argVals =>
    cases hc : s.code fname with
    | none => rfl
    | some entry =>
      obtain ⟨params, calleeBody⟩ := entry
      dsimp only
      split
      · split
        · rfl
        · rw [fix_clock_evaluate_of_clock_le (dec_clock s) { dec_clock s with locals := mkCalleeLocals params argVals } calleeBody (Nat.le_refl _)]
      · rfl

theorem evaluate_ret {θ : Type} (e : PExp) (s : PanState θ) :
    evaluate (.ret e) s =
      match eval s e with
      | none => (.Error, s)
      | some val =>
        if decide (size_of_shape (shape_of val) ≤ 32) then (.ret val, empty_locals s) else (.Error, s) :=
  evaluate_eq_step (.ret e) s

/-! ## 7. HOL4 Kernel Row Contracts & Helper Equations -/

@[simp] theorem shape_of_word (w : Word) : shape_of (.word w) = .One := rfl

@[simp] theorem size_of_shape_one : size_of_shape .One = 1 := rfl

@[simp] theorem flatten_word (w : Word) : flatten (.word w) = [w] := rfl

theorem is_valid_value_local {θ : Type} (s : PanState θ) (v : String) (val : PanVal) :
    is_valid_value s .Local v val =
      match s.locals v with
      | none => false
      | some old => shape_of val == shape_of old := rfl

theorem mem_store_byte_eq {m : Word → Word} {dm : Word → Bool} {be : Bool} {w : Word} {b : Byte}
    (hdom : dm (byte_align w) = true) :
    mem_store_byte m dm be w b =
      some (UPDATE (byte_align w) (set_byte w b (m (byte_align w)) be) m) := by
  simp [mem_store_byte, hdom]

theorem mem_load_byte_after_store_same {m : Word → Word} {dm : Word → Bool} {be : Bool}
    {w : Word} {b : Byte} (hdom : dm (byte_align w) = true) :
    mem_load_byte (UPDATE (byte_align w) (set_byte w b (m (byte_align w)) be) m) dm be w = some b := by
  simp only [mem_load_byte, hdom, ite_true, UPDATE, set_byte, get_byte]
  apply congrArg some
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hbi : byte_index w be ≤ 56 := by
    simp only [byte_index]
    have : w.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
    split <;> omega
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, word_slice_alt, BitVec.getLsbD_ofNat,
    Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  have h1 : ¬ (byte_index w be + 8 ≤ byte_index w be + i) := by omega
  have h3 : byte_index w be + i < 64 := by omega
  have h4 : byte_index w be + i - byte_index w be = i := by omega
  have h5 : ¬ (byte_index w be + i < byte_index w be) := by omega
  simp [h1, h3, h4, h5, hi]
  omega

theorem contract_word_carrier (a b : Word) (k : Nat) :
    a.toNat < 18446744073709551616 ∧
    (a.toNat = b.toNat → a = b) ∧
    (BitVec.ofNat 64 k).toNat = k % 18446744073709551616 :=
  ⟨a.isLt, BitVec.eq_of_toNat_eq, BitVec.toNat_ofNat k 64⟩

theorem contract_word_add (a b : Word) :
    (a + b).toNat = (a.toNat + b.toNat) % 18446744073709551616 := by
  simp [BitVec.toNat_add]

theorem contract_word_sub (a b : Word) : (a - b) + b = a :=
  BitVec.sub_add_cancel a b

theorem contract_word_mul (a b : Word) :
    (a * b).toNat = (a.toNat * b.toNat) % 18446744073709551616 := by
  simp [BitVec.toNat_mul]

theorem contract_word_lo (a b : Word) :
    (BitVec.ult a b = true) = (a.toNat < b.toNat) := by
  simp [BitVec.ult]

theorem contract_word_lt (a b : Word) :
    (BitVec.slt a b = true) =
      (BitVec.ult (a + 9223372036854775808#64) (b + 9223372036854775808#64) = true) := by
  have hc : (9223372036854775808#64 : Word).toNat = 9223372036854775808 := rfl
  have ha : a.toNat < 18446744073709551616 := a.isLt
  have hb : b.toNat < 18446744073709551616 := b.isLt
  have e1 : (2 : Nat) ^ (64 - 1) = 9223372036854775808 := rfl
  rw [BitVec.slt_eq_ult, BitVec.msb_eq_decide, BitVec.msb_eq_decide]
  unfold BitVec.ult
  rw [BitVec.toNat_add, BitVec.toNat_add, hc, e1]
  apply propext
  by_cases h1 : 9223372036854775808 ≤ a.toNat <;>
    by_cases h2 : 9223372036854775808 ≤ b.toNat <;>
    by_cases h3 : a.toNat < b.toNat <;>
    simp [h1, h2, h3] <;> omega

theorem contract_word_slice (h l i : Nat) (w : Word) :
    (BitVec.getLsbD (word_slice h l w) i = true) =
      (l ≤ i ∧ i ≤ h ∧ BitVec.getLsbD w i = true) := by
  apply propext
  rw [word_slice, BitVec.getLsbD_ofNat]
  simp only [Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    Bool.and_eq_true, decide_eq_true_eq, ge_iff_le]
  rw [BitVec.getLsbD]
  constructor
  · rintro ⟨_, hli, hlt, hb⟩
    exact ⟨hli, by omega, by rwa [Nat.add_sub_cancel' hli] at hb⟩
  · rintro ⟨hli, hih, hb⟩
    refine ⟨?_, hli, by omega, by rwa [Nat.add_sub_cancel' hli]⟩
    if hn : i < 64 then exact hn
    else
      have : w.toNat < 2 ^ i :=
        Nat.lt_of_lt_of_le w.isLt (Nat.pow_le_pow_right (by decide) (by omega))
      rw [Nat.testBit_lt_two_pow this] at hb; simp at hb

theorem contract_fmap {α β : Type} [DecidableEq α]
    (f : FMap α β) (k x : α) (v : β) (h : α × β) (l : List (α × β)) :
    (FEMPTY : FMap α β) x = none ∧
    FUPDATE f (k, v) x = (if x = k then some v else f x) ∧
    DOMSUB f k x = (if x = k then none else f x) ∧
    FUPDATE_LIST f [] = f ∧
    FUPDATE_LIST f (h :: l) = FUPDATE_LIST (FUPDATE f h) l :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem contract_update {α β : Type} [DecidableEq α] (a c : α) (b : β) (f : α → β) :
    UPDATE a b f a = b ∧ (a ≠ c → UPDATE a b f c = f c) :=
  ⟨by simp [UPDATE], fun h => by simp [UPDATE, h]⟩

/-! ## 8. Shared `ServeSpec` Wire Alignment -/

namespace ServeSpec

abbrev Bytes := List UInt8

def toBitVec8s (bs : Bytes) : List Byte := bs.map UInt8.toBitVec

def ofBitVec8s (bs : List Byte) : Bytes := bs.map UInt8.ofBitVec

theorem ofBitVec8s_toBitVec8s (bs : Bytes) : ofBitVec8s (toBitVec8s bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b tl ih =>
    unfold toBitVec8s ofBitVec8s at ih ⊢
    simp only [List.map_cons, UInt8.ofBitVec_toBitVec, ih]

structure Response where
  status  : Nat
  reason  : Bytes
  headers : List (Bytes × Bytes)
  body    : Bytes
  deriving Repr, DecidableEq

def crlf   : Bytes := [13, 10]
def http11 : Bytes := [72, 84, 84, 80, 47, 49, 46, 49]
def clName : Bytes := [67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104]

def natToDec (n : Nat) : Bytes := (Nat.repr n).toUTF8.toList

def headerLine (nv : Bytes × Bytes) : Bytes := nv.1 ++ [58, 32] ++ nv.2

def renderHeaders : List (Bytes × Bytes) → Bytes
  | []     => []
  | [h]    => headerLine h
  | h :: t => headerLine h ++ crlf ++ renderHeaders t
termination_by structural hs => hs

def serialize (r : Response) : Bytes :=
  let statusLn := http11 ++ [32] ++ natToDec r.status ++ [32] ++ r.reason
  let allHdrs  := r.headers ++ [(clName, natToDec r.body.length)]
  statusLn ++ crlf ++ renderHeaders allHdrs ++ crlf ++ crlf ++ r.body

end ServeSpec


-- `#guard_msgs`-pinned axiom audit for `PanSemV435`.
/--
info: 'OrbPancakeV435.evaluate_eq_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms evaluate_eq_step

/--
info: 'OrbPancakeV435.mem_load_byte_after_store_same' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms mem_load_byte_after_store_same

end OrbPancakeV435

