/-!
Hex encoding helpers: lowercase output; decoding accepts lowercase only.
-/
namespace Mir.Crypto

private def hexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)

/-- Lowercase hex encoding. -/
def toHex (b : ByteArray) : String := Id.run do
  let mut s := ""
  for i in [0:b.size] do
    let x := b.get! i
    s := (s.push (hexDigit (x >>> 4))).push (hexDigit (x &&& 0x0f))
  return s

private def hexVal? (c : Char) : Option UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87).toUInt8
  else none

/-- Decode a lowercase hex string of even length. -/
def ofHex? (s : String) : Option ByteArray := Id.run do
  let cs := s.toList.toArray
  if cs.size % 2 != 0 then return none
  let mut out := ByteArray.emptyWithCapacity (cs.size / 2)
  for i in [0:cs.size / 2] do
    match hexVal? cs[2*i]!, hexVal? cs[2*i+1]! with
    | some hi, some lo => out := out.push ((hi <<< 4) ||| lo)
    | _, _ => return none
  return some out

end Mir.Crypto
