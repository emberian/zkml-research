/-!
Keccak-f[1600], SHAKE256 and cSHAKE256 (FIPS 202, NIST SP 800-185), pure Lean.
Lanes are indexed `x + 5*y`; bytes are absorbed little-endian into lanes.
The unrolled round was generated mechanically from the rho/pi tables and is checked by vectors.
-/
namespace Mir.Crypto
namespace Keccak

def RC : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
  0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
  0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

@[inline] def rotl (x : UInt64) (n : UInt64) : UInt64 := (x <<< n) ||| (x >>> (64 - n))

/-! The round below is unrolled. rho offsets per lane `x + 5*y`:
`0 1 62 28 27 36 44 6 55 20 3 10 43 25 39 41 45 15 21 8 18 2 61 56 14`; pi sends lane
`(x, y)` to `(y, 2x + 3y mod 5)`. -/

/-- Keccak-f[1600] state: 25 unboxed lanes, lane `x + 5*y` is `a{x+5y}`. -/
structure State where
  a0 : UInt64
  a1 : UInt64
  a2 : UInt64
  a3 : UInt64
  a4 : UInt64
  a5 : UInt64
  a6 : UInt64
  a7 : UInt64
  a8 : UInt64
  a9 : UInt64
  a10 : UInt64
  a11 : UInt64
  a12 : UInt64
  a13 : UInt64
  a14 : UInt64
  a15 : UInt64
  a16 : UInt64
  a17 : UInt64
  a18 : UInt64
  a19 : UInt64
  a20 : UInt64
  a21 : UInt64
  a22 : UInt64
  a23 : UInt64
  a24 : UInt64

def State.zero : State := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- One round of Keccak-f[1600] (theta, rho, pi, chi, iota). -/
@[inline] def round (s : State) (rc : UInt64) : State :=
  let c0 := s.a0 ^^^ s.a5 ^^^ s.a10 ^^^ s.a15 ^^^ s.a20
  let c1 := s.a1 ^^^ s.a6 ^^^ s.a11 ^^^ s.a16 ^^^ s.a21
  let c2 := s.a2 ^^^ s.a7 ^^^ s.a12 ^^^ s.a17 ^^^ s.a22
  let c3 := s.a3 ^^^ s.a8 ^^^ s.a13 ^^^ s.a18 ^^^ s.a23
  let c4 := s.a4 ^^^ s.a9 ^^^ s.a14 ^^^ s.a19 ^^^ s.a24
  let d0 := c4 ^^^ rotl c1 1
  let d1 := c0 ^^^ rotl c2 1
  let d2 := c1 ^^^ rotl c3 1
  let d3 := c2 ^^^ rotl c4 1
  let d4 := c3 ^^^ rotl c0 1
  let b0 := (s.a0 ^^^ d0)
  let b1 := rotl (s.a6 ^^^ d1) 44
  let b2 := rotl (s.a12 ^^^ d2) 43
  let b3 := rotl (s.a18 ^^^ d3) 21
  let b4 := rotl (s.a24 ^^^ d4) 14
  let b5 := rotl (s.a3 ^^^ d3) 28
  let b6 := rotl (s.a9 ^^^ d4) 20
  let b7 := rotl (s.a10 ^^^ d0) 3
  let b8 := rotl (s.a16 ^^^ d1) 45
  let b9 := rotl (s.a22 ^^^ d2) 61
  let b10 := rotl (s.a1 ^^^ d1) 1
  let b11 := rotl (s.a7 ^^^ d2) 6
  let b12 := rotl (s.a13 ^^^ d3) 25
  let b13 := rotl (s.a19 ^^^ d4) 8
  let b14 := rotl (s.a20 ^^^ d0) 18
  let b15 := rotl (s.a4 ^^^ d4) 27
  let b16 := rotl (s.a5 ^^^ d0) 36
  let b17 := rotl (s.a11 ^^^ d1) 10
  let b18 := rotl (s.a17 ^^^ d2) 15
  let b19 := rotl (s.a23 ^^^ d3) 56
  let b20 := rotl (s.a2 ^^^ d2) 62
  let b21 := rotl (s.a8 ^^^ d3) 55
  let b22 := rotl (s.a14 ^^^ d4) 39
  let b23 := rotl (s.a15 ^^^ d0) 41
  let b24 := rotl (s.a21 ^^^ d1) 2
  ⟨(b0 ^^^ ((~~~ b1) &&& b2)) ^^^ rc,
   b1 ^^^ ((~~~ b2) &&& b3),
   b2 ^^^ ((~~~ b3) &&& b4),
   b3 ^^^ ((~~~ b4) &&& b0),
   b4 ^^^ ((~~~ b0) &&& b1),
   b5 ^^^ ((~~~ b6) &&& b7),
   b6 ^^^ ((~~~ b7) &&& b8),
   b7 ^^^ ((~~~ b8) &&& b9),
   b8 ^^^ ((~~~ b9) &&& b5),
   b9 ^^^ ((~~~ b5) &&& b6),
   b10 ^^^ ((~~~ b11) &&& b12),
   b11 ^^^ ((~~~ b12) &&& b13),
   b12 ^^^ ((~~~ b13) &&& b14),
   b13 ^^^ ((~~~ b14) &&& b10),
   b14 ^^^ ((~~~ b10) &&& b11),
   b15 ^^^ ((~~~ b16) &&& b17),
   b16 ^^^ ((~~~ b17) &&& b18),
   b17 ^^^ ((~~~ b18) &&& b19),
   b18 ^^^ ((~~~ b19) &&& b15),
   b19 ^^^ ((~~~ b15) &&& b16),
   b20 ^^^ ((~~~ b21) &&& b22),
   b21 ^^^ ((~~~ b22) &&& b23),
   b22 ^^^ ((~~~ b23) &&& b24),
   b23 ^^^ ((~~~ b24) &&& b20),
   b24 ^^^ ((~~~ b20) &&& b21)⟩

def State.get (s : State) (i : Nat) : UInt64 :=
  match i with
  | 0 => s.a0
  | 1 => s.a1
  | 2 => s.a2
  | 3 => s.a3
  | 4 => s.a4
  | 5 => s.a5
  | 6 => s.a6
  | 7 => s.a7
  | 8 => s.a8
  | 9 => s.a9
  | 10 => s.a10
  | 11 => s.a11
  | 12 => s.a12
  | 13 => s.a13
  | 14 => s.a14
  | 15 => s.a15
  | 16 => s.a16
  | 17 => s.a17
  | 18 => s.a18
  | 19 => s.a19
  | 20 => s.a20
  | 21 => s.a21
  | 22 => s.a22
  | 23 => s.a23
  | 24 => s.a24
  | _ => 0

/-- XOR `v` into lane `i`. -/
def State.xorLane (s : State) (i : Nat) (v : UInt64) : State :=
  match i with
  | 0 => { s with a0 := s.a0 ^^^ v }
  | 1 => { s with a1 := s.a1 ^^^ v }
  | 2 => { s with a2 := s.a2 ^^^ v }
  | 3 => { s with a3 := s.a3 ^^^ v }
  | 4 => { s with a4 := s.a4 ^^^ v }
  | 5 => { s with a5 := s.a5 ^^^ v }
  | 6 => { s with a6 := s.a6 ^^^ v }
  | 7 => { s with a7 := s.a7 ^^^ v }
  | 8 => { s with a8 := s.a8 ^^^ v }
  | 9 => { s with a9 := s.a9 ^^^ v }
  | 10 => { s with a10 := s.a10 ^^^ v }
  | 11 => { s with a11 := s.a11 ^^^ v }
  | 12 => { s with a12 := s.a12 ^^^ v }
  | 13 => { s with a13 := s.a13 ^^^ v }
  | 14 => { s with a14 := s.a14 ^^^ v }
  | 15 => { s with a15 := s.a15 ^^^ v }
  | 16 => { s with a16 := s.a16 ^^^ v }
  | 17 => { s with a17 := s.a17 ^^^ v }
  | 18 => { s with a18 := s.a18 ^^^ v }
  | 19 => { s with a19 := s.a19 ^^^ v }
  | 20 => { s with a20 := s.a20 ^^^ v }
  | 21 => { s with a21 := s.a21 ^^^ v }
  | 22 => { s with a22 := s.a22 ^^^ v }
  | 23 => { s with a23 := s.a23 ^^^ v }
  | 24 => { s with a24 := s.a24 ^^^ v }
  | _ => s

/-- Keccak-f[1600]: 24 rounds. -/
def permute (s : State) : State := Id.run do
  let mut s := s
  for r in [0:24] do
    s := round s RC[r]!
  return s

/-- Sponge with rate `rate` bytes (a multiple of 8, at most 200). `dsByte` is the first padding
byte (domain-separation bits followed by the first pad bit); the last block byte gets `0x80`. -/
def sponge (rate : Nat) (input : ByteArray) (dsByte : UInt8) (outBytes : Nat) : ByteArray :=
  Id.run do
  let len := input.size
  let total := (len / rate + 1) * rate
  let mut m := ByteArray.emptyWithCapacity total
  m := m ++ input
  m := m.push dsByte
  for _ in [0:total - len - 1] do
    m := m.push 0
  m := m.set! (total - 1) (m.get! (total - 1) ||| 0x80)
  let mut a := State.zero
  let lanes := rate / 8
  for blk in [0:total / rate] do
    let off := blk * rate
    for i in [0:lanes] do
      let o := off + 8 * i
      let mut v : UInt64 := 0
      for j in [0:8] do
        v := v ||| ((m.get! (o + j)).toUInt64 <<< (8 * j).toUInt64)
      a := a.xorLane i v
    a := permute a
  let mut out := ByteArray.emptyWithCapacity outBytes
  let mut produced := 0
  while produced < outBytes do
    for i in [0:lanes] do
      let v := a.get i
      for j in [0:8] do
        if produced < outBytes then
          out := out.push (v >>> (8 * j).toUInt64).toUInt8
          produced := produced + 1
    if produced < outBytes then
      a := permute a
  return out

/-- Big-endian minimal bytes of `x` (at least one byte). -/
def natBytesBE (x : Nat) : ByteArray := Id.run do
  let mut n := 1
  while 256 ^ n ≤ x do
    n := n + 1
  let mut out := ByteArray.emptyWithCapacity n
  for i in [0:n] do
    out := out.push (x / 256 ^ (n - 1 - i) % 256).toUInt8
  return out

/-- SP 800-185 2.3.1 `left_encode`. -/
def leftEncode (x : Nat) : ByteArray :=
  let bs := natBytesBE x
  (ByteArray.empty.push bs.size.toUInt8) ++ bs

/-- SP 800-185 2.3.1 `right_encode`. -/
def rightEncode (x : Nat) : ByteArray :=
  let bs := natBytesBE x
  bs.push bs.size.toUInt8

/-- SP 800-185 2.3.2 `encode_string` (bit length prefix). -/
def encodeString (s : ByteArray) : ByteArray := leftEncode (8 * s.size) ++ s

/-- SP 800-185 2.3.3 `bytepad`. -/
def bytepad (x : ByteArray) (w : Nat) : ByteArray := Id.run do
  let mut z := leftEncode w ++ x
  while z.size % w != 0 do
    z := z.push 0
  return z

def rate256 : Nat := 136

end Keccak

/-- SHAKE256 (FIPS 202) with `outBytes` bytes of output. -/
def shake256 (x : ByteArray) (outBytes : Nat) : ByteArray :=
  Keccak.sponge Keccak.rate256 x 0x1f outBytes

/-- cSHAKE256 (SP 800-185 3.3): `n` is the function-name string, `s` the customization
string. With both empty this is SHAKE256. -/
def cshake256 (x : ByteArray) (outBytes : Nat) (n s : ByteArray) : ByteArray :=
  if n.size == 0 && s.size == 0 then shake256 x outBytes
  else
    let pre := Keccak.bytepad (Keccak.encodeString n ++ Keccak.encodeString s) Keccak.rate256
    Keccak.sponge Keccak.rate256 (pre ++ x) 0x04 outBytes

end Mir.Crypto
