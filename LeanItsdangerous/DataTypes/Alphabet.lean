import LeanItsdangerous.DataTypes.Bytes

/-!
# The URL-safe base64 alphabet

`A-Z a-z 0-9 - _`, the alphabet of `base64.urlsafe_base64Encode`, as a pair of
arithmetic maps between a 6-bit index and its byte. Defining them by
arithmetic rather than by table lookup is what lets `decide` check
`decChar (encChar i) = some i` for all 64 indices at once, and `omega` reason
about the indices.

`isAlphabet` is upstream's `_base64_alphabet`: the 64 characters plus `=`. A
signer separator must avoid all of them.
-/

namespace LeanItsdangerous

/-- The byte for 6-bit index `n % 64`. -/
def encChar (n : Nat) : UInt8 :=
  let i := n % 64
  if i < 26 then UInt8.ofNat (65 + i)
  else if i < 52 then UInt8.ofNat (71 + i)
  else if i < 62 then UInt8.ofNat (i - 4)
  else if i = 62 then 45 else 95

/-- The 6-bit index of a base64url byte, or `none` for any other byte
(including the padding `=`). -/
def decChar (c : UInt8) : Option Nat :=
  let n := c.toNat
  if 65 ≤ n ∧ n ≤ 90 then some (n - 65)
  else if 97 ≤ n ∧ n ≤ 122 then some (n - 71)
  else if 48 ≤ n ∧ n ≤ 57 then some (n + 4)
  else if n = 45 then some 62
  else if n = 95 then some 63
  else none

/-- Upstream's `_base64_alphabet`: ASCII letters, digits, and `-_=`. -/
def isAlphabet (c : UInt8) : Bool := (decChar c).isSome || c == 61

end LeanItsdangerous
