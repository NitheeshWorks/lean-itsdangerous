/-!
# Bytes

Upstream works on Python `bytes` and accepts `str` wherever it accepts bytes,
encoding text as UTF-8 (`want_bytes`). Here the byte string is a `List UInt8`:
it is what the round-trip and splitting proofs induct on. Text enters through
`Bytes.ofString`, the analogue of `want_bytes`.
-/

namespace LeanItsdangerous

/-- A byte string. A list rather than a `ByteArray` because every proof in
this library is an induction over it. -/
abbrev Bytes := List UInt8

/-- UTF-8 encoding of a string: upstream's `want_bytes(s)`. -/
def Bytes.ofString (s : String) : Bytes := s.toUTF8.toList

/-- UTF-8 decoding, failing on invalid UTF-8. -/
def Bytes.toString? (b : Bytes) : Option String := String.fromUTF8? ⟨b.toArray⟩

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Lower-case hexadecimal rendering, two digits per byte. -/
def Bytes.toHex (b : Bytes) : String :=
  String.ofList (b.flatMap fun x => [hexDigit (x.toNat / 16), hexDigit (x.toNat % 16)])

/-- Python's `repr` of a `bytes` value (`b'...'`), as upstream interpolates
it into error messages. Printable ASCII is kept; quote and backslash are
escaped; everything else is `\xNN`. -/
def Bytes.pyRepr (b : Bytes) : String :=
  let body := b.flatMap fun x =>
    let n := x.toNat
    if n = 39 then ['\\', '\''] else if n = 92 then ['\\', '\\']
    else if n = 10 then ['\\', 'n'] else if n = 13 then ['\\', 'r']
    else if n = 9 then ['\\', 't']
    else if 32 ≤ n ∧ n < 127 then [Char.ofNat n]
    else ['\\', 'x', hexDigit (n / 16), hexDigit (n % 16)]
  "b'" ++ String.ofList body ++ "'"

instance : ToString Bytes := ⟨Bytes.pyRepr⟩

end LeanItsdangerous
