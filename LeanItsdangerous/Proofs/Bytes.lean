import LeanItsdangerous.DataTypes.Bytes

/-!
# Proofs: the UTF-8 encoder

`Bytes.ofString` is written by structural recursion so the kernel can
evaluate it on a literal (a separator is checked by `decide`). This proves it
is nonetheless the same function as Lean core's `String.toUTF8`, for every
string. Proof contributed by the review of the STYLE.md pass.
-/

namespace LeanItsdangerous

/-- One code point: `utf8Char` is core's `String.utf8EncodeChar`. -/
theorem utf8Char_eq (c : Char) : utf8Char c = String.utf8EncodeChar c := by
  have hc : c.toNat < 0x110000 := by
    have := c.valid; unfold Char.toNat; rcases this with h | h <;> omega
  unfold utf8Char String.utf8EncodeChar
  simp only [Char.toNat] at *
  generalize c.val.toNat = n at *
  by_cases h1 : n < 0x80
  · simp [h1, show n ≤ 127 by omega]
  by_cases h2 : n < 0x800
  · simp only [h1, h2, ite_false, ite_true, show ¬ n ≤ 127 by omega, show n ≤ 2047 by omega]
    rw [show n / 64 % 32 + 192 = 0xC0 + n / 64 by omega, show n % 64 + 128 = 0x80 + n % 64 by omega]
  by_cases h3 : n < 0x10000
  · simp only [h1, h2, h3, ite_false, ite_true, show ¬ n ≤ 127 by omega, show ¬ n ≤ 2047 by omega, show n ≤ 65535 by omega]
    rw [show n / 4096 % 16 + 224 = 0xE0 + n / 4096 by omega, show n / 64 % 64 + 128 = 0x80 + n / 64 % 64 by omega,
      show n % 64 + 128 = 0x80 + n % 64 by omega]
  · simp only [h1, h2, h3, ite_false, show ¬ n ≤ 127 by omega, show ¬ n ≤ 2047 by omega, show ¬ n ≤ 65535 by omega]
    rw [show n / 262144 % 8 + 240 = 0xF0 + n / 262144 by omega, show n / 4096 % 64 + 128 = 0x80 + n / 4096 % 64 by omega,
      show n / 64 % 64 + 128 = 0x80 + n / 64 % 64 by omega, show n % 64 + 128 = 0x80 + n % 64 by omega]

/-- A list of code points: core's encoder, as a byte list. -/
theorem utf8Encode_toList (l : List Char) : l.utf8Encode.data.toList = l.flatMap utf8Char := by
  induction l with
  | nil => simp [List.utf8Encode_nil]
  | cons c l ih =>
    rw [List.utf8Encode_cons, List.utf8Encode_singleton, ByteArray.data_append, Array.toList_append, ih,
      List.flatMap_cons, utf8Char_eq, List.data_toByteArray]

/-- `Bytes.ofString` is UTF-8 exactly as Lean core encodes it (`String.toUTF8`),
for every string. -/
theorem Bytes.ofString_eq_toUTF8 (s : String) : Bytes.ofString s = s.toUTF8.data.toList := by
  unfold Bytes.ofString String.toUTF8
  conv => rhs; rw [← String.ofList_toList (s := s)]
  rw [String.toByteArray_ofList, utf8Encode_toList]

end LeanItsdangerous
