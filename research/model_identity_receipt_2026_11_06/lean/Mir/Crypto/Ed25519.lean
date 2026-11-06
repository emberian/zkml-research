import Mir.Crypto.Sha512
/-!
Ed25519 signature verification (RFC 8032 5.1.7), cofactorless: accepts iff
`[S]B = R + [k]A` with `k = SHA-512(R || A || M) mod L`.
Strict: rejects non-canonical point encodings (y ≥ p, or x = 0 with sign bit 1),
points not on the curve, and `S ≥ L`. Field and scalar arithmetic over `Nat`.
-/
namespace Mir.Crypto
namespace Ed25519

def p : Nat := 2 ^ 255 - 19
def L : Nat := 2 ^ 252 + 27742317777372353535851937790883648493

/-- Modular exponentiation by squaring. -/
def powMod (b e m : Nat) : Nat := Id.run do
  let mut r := 1 % m
  let mut b := b % m
  let mut e := e
  while e > 0 do
    if e % 2 == 1 then r := r * b % m
    b := b * b % m
    e := e / 2
  return r

def inv (x : Nat) : Nat := powMod x (p - 2) p

/-- d = -121665/121666 mod p. -/
def d : Nat := (p - 121665) * inv 121666 % p
def d2 : Nat := 2 * d % p
/-- sqrt(-1) = 2^((p-1)/4) mod p. -/
def sqrtM1 : Nat := powMod 2 ((p - 1) / 4) p

@[inline] def fadd (a b : Nat) : Nat := (a + b) % p
@[inline] def fsub (a b : Nat) : Nat := (a + p - b) % p
@[inline] def fmul (a b : Nat) : Nat := a * b % p

/-- Extended homogeneous coordinates (X : Y : Z : T), x = X/Z, y = Y/Z, xy = T/Z. -/
structure Point where
  X : Nat
  Y : Nat
  Z : Nat
  T : Nat

def identity : Point := ⟨0, 1, 1, 0⟩

/-- RFC 8032 5.1.4 addition (complete for Ed25519; also used for doubling). -/
def add (P Q : Point) : Point :=
  let a := fmul (fsub P.Y P.X) (fsub Q.Y Q.X)
  let b := fmul (fadd P.Y P.X) (fadd Q.Y Q.X)
  let c := fmul (fmul P.T d2) Q.T
  let dd := fmul (2 * P.Z % p) Q.Z
  let e := fsub b a
  let f := fsub dd c
  let g := fadd dd c
  let h := fadd b a
  ⟨fmul e f, fmul g h, fmul f g, fmul e h⟩

/-- Scalar multiplication, MSB-first double-and-add. -/
def scalarMul (k : Nat) (P : Point) : Point := Id.run do
  let mut r := identity
  let nb := Nat.log2 k + 1
  for i in [0:nb] do
    r := add r r
    if (k >>> (nb - 1 - i)) % 2 == 1 then
      r := add r P
  return r

/-- Projective equality. -/
def eq (P Q : Point) : Bool :=
  fmul P.X Q.Z == fmul Q.X P.Z && fmul P.Y Q.Z == fmul Q.Y P.Z

/-- Little-endian bytes to Nat. -/
def leNat (b : ByteArray) : Nat := Id.run do
  let mut x := 0
  for i in [0:b.size] do
    x := x + (b.get! i).toNat <<< (8 * i)
  return x

/-- Recover x from y and sign bit (RFC 8032 5.1.3 steps 2-4). -/
def recoverX (y : Nat) (sign : Nat) : Option Nat :=
  let y2 := fmul y y
  let u := fsub y2 1
  let v := fadd (fmul d y2) 1
  let v3 := fmul (fmul v v) v
  let v7 := fmul (fmul v3 v3) v
  let x := fmul (fmul u v3) (powMod (fmul u v7) ((p - 5) / 8) p)
  let vx2 := fmul v (fmul x x)
  let x? : Option Nat :=
    if vx2 == u then some x
    else if vx2 == (p - u) % p then some (fmul x sqrtM1)
    else none
  match x? with
  | none => none
  | some x =>
    if x == 0 && sign == 1 then none
    else if x % 2 != sign then some (p - x)
    else some x

/-- Strict decoding of a 32-byte point encoding (RFC 8032 5.1.3). -/
def decodePoint (b : ByteArray) : Option Point :=
  if b.size != 32 then none else
  let n := leNat b
  let sign := n >>> 255
  let y := n % 2 ^ 255
  if y ≥ p then none else
  match recoverX y sign with
  | none => none
  | some x => some ⟨x, y, 1, fmul x y⟩

/-- Base point: y = 4/5, x even. -/
def B : Point :=
  let y := fmul 4 (inv 5)
  match recoverX y 0 with
  | some x => ⟨x, y, 1, fmul x y⟩
  | none => identity

end Ed25519

open Ed25519 in
/-- Ed25519 verification (RFC 8032 5.1.7, cofactorless, strict). A public key of small order (8A = identity, the
identity among them) is refused: with A = R = identity and S = 0 every message would verify (second cross-model
attack, notes/attack-2.md). -/
def ed25519Verify (pk : ByteArray) (msg : ByteArray) (sig : ByteArray) : Bool :=
  if pk.size != 32 || sig.size != 64 then false else
  let rBytes := sig.extract 0 32
  let s := leNat (sig.extract 32 64)
  if s ≥ L then false else
  match decodePoint pk, decodePoint rBytes with
  | some A, some R =>
    if eq (scalarMul 8 A) identity then false else
    let k := leNat (sha512 (rBytes ++ pk ++ msg)) % L
    eq (scalarMul s B) (add R (scalarMul k A))
  | _, _ => false

end Mir.Crypto
