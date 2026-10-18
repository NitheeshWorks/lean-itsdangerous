import LeanItsdangerous.DataTypes.Alphabet

/-!
# base64url without padding, integer bytes, splitting

* `b64encode` / `b64decode`: upstream's `base64_encode` (URL-safe alphabet,
  `=` padding stripped) and `base64_decode` (padding re-added before
  decoding). Groups of three bytes become four characters; a trailing one or
  two bytes become two or three characters.
* `intToBytes` / `bytesToInt`: upstream's `int_to_bytes` (big-endian,
  leading zero bytes stripped) and `bytes_to_int` (at most eight bytes).
* `splitFirst` / `rsplit`: `bytes.rsplit(sep, 1)`, by searching the
  reversed string for the reversed separator.
-/

namespace LeanItsdangerous

/-! ## base64url -/

/-- Three bytes to four characters. -/
def enc3 (a b c : UInt8) : Bytes :=
  [encChar (a.toNat / 4), encChar (a.toNat % 4 * 16 + b.toNat / 16),
   encChar (b.toNat % 16 * 4 + c.toNat / 64), encChar (c.toNat % 64)]

/-- Two trailing bytes to three characters. -/
def enc2 (a b : UInt8) : Bytes :=
  [encChar (a.toNat / 4), encChar (a.toNat % 4 * 16 + b.toNat / 16), encChar (b.toNat % 16 * 4)]

/-- One trailing byte to two characters. -/
def enc1 (a : UInt8) : Bytes :=
  [encChar (a.toNat / 4), encChar (a.toNat % 4 * 16)]

/-- `base64_encode`: URL-safe base64 with the `=` padding removed. -/
def b64encode : Bytes → Bytes
  | a :: b :: c :: rest => enc3 a b c ++ b64encode rest
  | [a, b] => enc2 a b
  | [a] => enc1 a
  | [] => []

/-- Four characters to three bytes. -/
def dec4 (w x y z : UInt8) : Option Bytes := do
  let a ← decChar w
  let b ← decChar x
  let c ← decChar y
  let d ← decChar z
  pure [UInt8.ofNat (a * 4 + b / 16), UInt8.ofNat (b % 16 * 16 + c / 4), UInt8.ofNat (c % 4 * 64 + d)]

/-- Three trailing characters to two bytes (the low two bits are dropped, as
Python's decoder does). -/
def dec3 (w x y : UInt8) : Option Bytes := do
  let a ← decChar w
  let b ← decChar x
  let c ← decChar y
  pure [UInt8.ofNat (a * 4 + b / 16), UInt8.ofNat (b % 16 * 16 + c / 4)]

/-- Two trailing characters to one byte. -/
def dec2 (w x : UInt8) : Option Bytes := do
  let a ← decChar w
  let b ← decChar x
  pure [UInt8.ofNat (a * 4 + b / 16)]

/-- `base64_decode` of unpadded URL-safe base64. A length of `1 mod 4`, or
a byte outside the alphabet, is invalid. -/
def b64decode : Bytes → Option Bytes
  | w :: x :: y :: z :: rest => do
    let q ← dec4 w x y z
    let r ← b64decode rest
    pure (q ++ r)
  | [w, x, y] => dec3 w x y
  | [w, x] => dec2 w x
  | [_] => none
  | [] => some []

/-- Upstream accepts `=` padding on input and strips it before decoding
(it re-pads to a multiple of four); so do we. -/
def stripPadding (s : Bytes) : Bytes := (s.reverse.dropWhile (· == 61)).reverse

/-- `base64_decode` as upstream exposes it: tolerant of trailing `=`. -/
def base64Decode (s : Bytes) : Option Bytes := b64decode (stripPadding s)

/-! ## Integers as bytes -/

/-- Minimal big-endian bytes of a natural number (`0` is the empty string). -/
def natToBytes (n : Nat) : Bytes :=
  if _h : n = 0 then [] else natToBytes (n / 256) ++ [UInt8.ofNat (n % 256)]
termination_by n
decreasing_by omega

/-- `int_to_bytes` of a 64-bit unsigned integer. -/
def intToBytes (n : UInt64) : Bytes := natToBytes n.toNat

/-- Big-endian value of a byte string. -/
def bytesToNat (bs : Bytes) : Nat := bs.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- `bytes_to_int`: at most eight bytes, else invalid (upstream's
`struct.error`). -/
def bytesToInt (bs : Bytes) : Option UInt64 :=
  if bs.length ≤ 8 then some (UInt64.ofNat (bytesToNat bs)) else none

/-! ## Splitting -/

/-- Split at the first occurrence of `pat`: `some (before, after)`. -/
def splitFirst (pat : Bytes) : Bytes → Option (Bytes × Bytes)
  | [] => if pat.isPrefixOf [] then some ([], []) else none
  | x :: xs =>
    if pat.isPrefixOf (x :: xs) then some ([], (x :: xs).drop pat.length)
    else (splitFirst pat xs).map fun p => (x :: p.1, p.2)

/-- `s.rsplit(sep, 1)`, or `none` if `sep` does not occur. -/
def rsplit (sep s : Bytes) : Option (Bytes × Bytes) :=
  (splitFirst sep.reverse s.reverse).map fun p => (p.2.reverse, p.1.reverse)

end LeanItsdangerous
