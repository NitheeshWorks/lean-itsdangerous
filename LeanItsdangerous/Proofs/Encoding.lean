import LeanItsdangerous.RepoImpl.Signer

/-!
# Proofs: base64url, integer bytes, splitting

The round trips (`b64decode_b64encode`, `bytesToInt_intToBytes`,
`decodeTimestamp_encodeTimestamp`), the facts about the encoder's output the
signer proofs need (alphabet only, length a function of input length,
injective), and the two directions of `rsplit`.
-/

namespace LeanItsdangerous

/-! ## The alphabet -/

theorem decChar_encChar_fin : ∀ i : Fin 64, decChar (encChar i.val) = some i.val := by decide

theorem isAlphabet_encChar_fin : ∀ i : Fin 64, isAlphabet (encChar i.val) = true := by decide

theorem encChar_mod (n : Nat) : encChar n = encChar (n % 64) := by
  simp [encChar]

theorem decChar_encChar (n : Nat) : decChar (encChar n) = some (n % 64) := by
  rw [encChar_mod]; exact decChar_encChar_fin ⟨n % 64, Nat.mod_lt _ (by decide)⟩

theorem isAlphabet_encChar (n : Nat) : isAlphabet (encChar n) = true := by
  rw [encChar_mod]; exact isAlphabet_encChar_fin ⟨n % 64, Nat.mod_lt _ (by decide)⟩

theorem encChar_ne_eq (n : Nat) : encChar n ≠ 61 := by
  intro h
  have := decChar_encChar n
  rw [h, show decChar 61 = none by decide] at this
  cases this

/-! ## base64url round trip -/

private theorem ofNat_eq {a : UInt8} {x : Nat} (h : x = a.toNat) : UInt8.ofNat x = a := by
  subst h; exact UInt8.ofNat_toNat

theorem b64decode_b64encode (bs : Bytes) : b64decode (b64encode bs) = some bs := by
  induction bs using b64encode.induct with
  | case1 a b c rest ih =>
    have ha := a.toNat_lt; have hb := b.toNat_lt; have hc := c.toNat_lt
    simp only [b64encode, enc3, List.cons_append, List.nil_append, b64decode, dec4,
      decChar_encChar, ih, Option.bind_eq_bind, Option.pure_def, Option.bind_some]
    simp only [Option.some.injEq, List.cons.injEq]
    refine ⟨ofNat_eq ?_, ofNat_eq ?_, ofNat_eq ?_, trivial⟩ <;> omega
  | case2 a b =>
    have ha := a.toNat_lt; have hb := b.toNat_lt
    simp only [b64encode, enc2, b64decode, dec3, decChar_encChar, Option.bind_eq_bind,
      Option.pure_def, Option.bind_some]
    simp only [Option.some.injEq, List.cons.injEq]
    refine ⟨ofNat_eq ?_, ofNat_eq ?_, trivial⟩ <;> omega
  | case3 a =>
    have ha := a.toNat_lt
    simp only [b64encode, enc1, b64decode, dec2, decChar_encChar, Option.bind_eq_bind,
      Option.pure_def, Option.bind_some]
    simp only [Option.some.injEq, List.cons.injEq]
    refine ⟨ofNat_eq ?_, trivial⟩; omega
  | case4 => rfl

/-- Every byte of an encoding is in the base64url alphabet. -/
theorem isAlphabet_of_mem_b64encode {bs : Bytes} {c : UInt8} (h : c ∈ b64encode bs) :
    isAlphabet c = true := by
  induction bs using b64encode.induct with
  | case1 a b d rest ih =>
    simp only [b64encode, enc3, List.cons_append, List.nil_append, List.mem_cons] at h
    rcases h with h | h | h | h | h <;> first | (subst h; exact isAlphabet_encChar _) | exact ih h
  | case2 a b =>
    simp only [b64encode, enc2, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h <;> (subst h; exact isAlphabet_encChar _)
  | case3 a =>
    simp only [b64encode, enc1, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h <;> (subst h; exact isAlphabet_encChar _)
  | case4 => simp [b64encode] at h

/-- No `=` in an encoding. -/
theorem ne_eq_of_mem_b64encode {bs : Bytes} {c : UInt8} (h : c ∈ b64encode bs) : c ≠ 61 := by
  induction bs using b64encode.induct with
  | case1 a b d rest ih =>
    simp only [b64encode, enc3, List.cons_append, List.nil_append, List.mem_cons] at h
    rcases h with h | h | h | h | h <;> first | (subst h; exact encChar_ne_eq _) | exact ih h
  | case2 a b =>
    simp only [b64encode, enc2, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h <;> (subst h; exact encChar_ne_eq _)
  | case3 a =>
    simp only [b64encode, enc1, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h <;> (subst h; exact encChar_ne_eq _)
  | case4 => simp [b64encode] at h

/-- The encoding's length depends only on the input's: `⌈4n/3⌉`. -/
theorem length_b64encode (bs : Bytes) : (b64encode bs).length = (4 * bs.length + 2) / 3 := by
  induction bs using b64encode.induct with
  | case1 a b c rest ih => simp [b64encode, enc3, ih]; omega
  | case2 a b => simp [b64encode, enc2]
  | case3 a => simp [b64encode, enc1]
  | case4 => rfl

theorem b64encode_injective {a b : Bytes} (h : b64encode a = b64encode b) : a = b := by
  have := b64decode_b64encode a
  rw [h, b64decode_b64encode] at this
  exact (Option.some.inj this).symm

theorem stripPadding_of_no_eq {s : Bytes} (h : ∀ c ∈ s, c ≠ 61) : stripPadding s = s := by
  unfold stripPadding
  cases hr : s.reverse with
  | nil => simp_all
  | cons x xs =>
    have hx : x ≠ 61 := h x (by rw [← List.mem_reverse, hr]; simp)
    rw [List.dropWhile_cons_of_neg (by simpa using hx), ← hr, List.reverse_reverse]

theorem base64Decode_b64encode (bs : Bytes) : base64Decode (b64encode bs) = some bs := by
  unfold base64Decode
  rw [stripPadding_of_no_eq (fun _ h => ne_eq_of_mem_b64encode h), b64decode_b64encode]

/-! ## Integers as bytes -/

theorem bytesToNat_append_single (bs : Bytes) (b : UInt8) :
    bytesToNat (bs ++ [b]) = bytesToNat bs * 256 + b.toNat := by
  simp [bytesToNat, List.foldl_append]

theorem bytesToNat_natToBytes (n : Nat) : bytesToNat (natToBytes n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [natToBytes]
    split
    · subst_vars; rfl
    · rw [bytesToNat_append_single, ih _ (by omega)]
      simp [UInt8.toNat_ofNat']; omega

theorem length_natToBytes_le (k n : Nat) (h : n < 256 ^ k) : (natToBytes n).length ≤ k := by
  induction k generalizing n with
  | zero => simp at h; subst h; simp [natToBytes]
  | succ k ih =>
    rw [natToBytes]
    split
    · simp
    · simp only [List.length_append, List.length_singleton]
      have : n / 256 < 256 ^ k := by rw [Nat.pow_succ] at h; omega
      have := ih _ this; omega

theorem bytesToInt_intToBytes (n : UInt64) : bytesToInt (intToBytes n) = some n := by
  have hlen : (intToBytes n).length ≤ 8 := length_natToBytes_le 8 _ n.toNat_lt
  unfold intToBytes at hlen
  simp only [bytesToInt, intToBytes, hlen, ite_true, bytesToNat_natToBytes, UInt64.ofNat_toNat]

/-- The timestamp encode/decode round trip. -/
theorem decodeTimestamp_encodeTimestamp (ts : UInt64) :
    TimestampSigner.decodeTimestamp (TimestampSigner.encodeTimestamp ts) = some ts := by
  simp [TimestampSigner.decodeTimestamp, TimestampSigner.encodeTimestamp,
    base64Decode_b64encode, bytesToInt_intToBytes]

/-! ## Splitting -/

theorem splitFirst_sound {pat l a b : Bytes} (h : splitFirst pat l = some (a, b)) :
    l = a ++ pat ++ b := by
  induction l generalizing a b with
  | nil =>
    simp only [splitFirst] at h
    split at h
    · rename_i hp
      have := (List.isPrefixOf_iff_prefix.mp hp)
      simp at h this; obtain ⟨rfl, rfl⟩ := h; simp [this]
    · simp at h
  | cons x xs ih =>
    simp only [splitFirst] at h
    split at h
    · rename_i hp
      obtain ⟨t, ht⟩ := List.isPrefixOf_iff_prefix.mp hp
      simp at h; obtain ⟨rfl, rfl⟩ := h
      rw [← ht]; simp
    · simp only [Option.map_eq_some_iff, Prod.exists] at h
      obtain ⟨a', b', h', he⟩ := h
      simp at he; obtain ⟨rfl, rfl⟩ := he
      rw [ih h']; simp

theorem splitFirst_append {p : UInt8} {ps pre rest : Bytes} (hp : p ∉ pre) :
    splitFirst (p :: ps) (pre ++ (p :: ps) ++ rest) = some (pre, rest) := by
  induction pre with
  | nil =>
    have h : (p :: ps).isPrefixOf ((p :: ps) ++ rest) = true :=
      List.isPrefixOf_iff_prefix.mpr ⟨rest, rfl⟩
    simp only [List.nil_append] at h ⊢
    simp only [List.cons_append] at h ⊢
    simp [splitFirst, h]
  | cons y ys ih =>
    have hy : y ≠ p := fun h => hp (h ▸ List.mem_cons_self)
    have hp' : p ∉ ys := fun h => hp (List.mem_cons_of_mem _ h)
    have h : ((p :: ps).isPrefixOf (y :: (ys ++ (p :: ps) ++ rest))) = false := by
      simp [List.isPrefixOf, Ne.symm hy]
    simp only [List.cons_append] at h ⊢
    simp only [splitFirst, h, Bool.false_eq_true, ite_false]
    have := ih hp'
    rw [this]; rfl

theorem rsplit_sound {sep l a b : Bytes} (h : rsplit sep l = some (a, b)) : l = a ++ sep ++ b := by
  simp only [rsplit, Option.map_eq_some_iff, Prod.exists] at h
  obtain ⟨x, y, h', he⟩ := h
  simp at he; obtain ⟨rfl, rfl⟩ := he
  have := splitFirst_sound h'
  have := congrArg List.reverse this
  simpa using this

/-- `rsplit` recovers the last field when that field contains no byte of the
separator. -/
theorem rsplit_append {sep v s : Bytes} (hsep : sep ≠ []) (hs : ∀ c ∈ s, c ∉ sep) :
    rsplit sep (v ++ sep ++ s) = some (v, s) := by
  unfold rsplit
  obtain ⟨p, ps, hrev⟩ : ∃ p ps, sep.reverse = p :: ps := by
    cases h : sep.reverse with
    | nil => simp at h; exact absurd h hsep
    | cons p ps => exact ⟨p, ps, rfl⟩
  have hpmem : p ∈ sep := by rw [← List.mem_reverse, hrev]; exact List.mem_cons_self
  have hp : p ∉ s.reverse := fun h => hs p (List.mem_reverse.mp h) hpmem
  have : (v ++ sep ++ s).reverse = s.reverse ++ (p :: ps) ++ v.reverse := by
    simp [List.reverse_append, hrev]
  rw [this, hrev, splitFirst_append hp]
  simp

/-- Base64url output never contains a byte of a valid separator. -/
theorem not_mem_sep_of_mem_b64encode {sep bs : Bytes} (hsep : ValidSep sep) :
    ∀ c ∈ b64encode bs, c ∉ sep := by
  intro c hc hcs
  have h1 := isAlphabet_of_mem_b64encode hc
  have h2 := hsep.2 c hcs
  rw [h1] at h2; exact absurd h2 (by decide)

end LeanItsdangerous
