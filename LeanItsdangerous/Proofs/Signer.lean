import LeanItsdangerous.Proofs.Encoding

/-!
# Proofs: Signer

* `unsignImpl_signWith` (key rotation): a value signed by *any* key in the list
  unsigns to itself.
* `unsignImpl_sign`: the special case of the signing (newest) key.
* `unsignImpl_sound`: an `ok v` from `unsign` means the input is `v` signed by
  some key in the list. This is the refinement `APIs/` returns.
* `unsignImpl_ok_iff`: the two together, as a characterisation.
* `unsignImpl_tampered_value`, `unsignImpl_tampered`, `unsignImpl_tampered_single`: what
  tampering can achieve. A successful one-byte tamper either returns the
  original value or exhibits an explicit collision of the signing algorithm;
  no collision resistance is assumed.
-/

namespace LeanItsdangerous.Signer

theorem secretKey_mem (s : Signer) : s.secretKey ∈ s.secretKeys := List.getLast_mem _

theorem signatureFor_not_mem_sep (s : Signer) (k v : Bytes) :
    ∀ c ∈ s.signatureFor k v, c ∉ s.sep :=
  not_mem_sep_of_mem_base64Encode s.h_sep

theorem rsplit_signWith (s : Signer) (k v : Bytes) :
    rsplit s.sep (s.signWith k v) = some (v, s.signatureFor k v) :=
  rsplit_append s.h_sep.1 (s.signatureFor_not_mem_sep k v)

theorem verifySignature_iff (s : Signer) (v sig : Bytes) :
    s.verifySignature v sig = true ↔ ∃ k ∈ s.secretKeys, s.signatureFor k v = sig := by
  simp [verifySignature, List.any_eq_true, ctEq_iff]

/-- Key rotation: verification succeeds if any key in the list signed the
value. -/
theorem unsignImpl_signWith (s : Signer) {k : Bytes} (hk : k ∈ s.secretKeys) (v : Bytes) :
    s.unsignImpl (s.signWith k v) = .ok v := by
  have hv : s.verifySignature v (s.signatureFor k v) = true :=
    (s.verifySignature_iff _ _).mpr ⟨k, hk, rfl⟩
  simp [unsignImpl, rsplit_signWith, hv]

/-- Unsigning with the same signer returns the original value. -/
theorem unsignImpl_sign (s : Signer) (v : Bytes) : s.unsignImpl (s.sign v) = .ok v :=
  s.unsignImpl_signWith s.secretKey_mem v

/-- Soundness: `unsign` succeeds only on a value signed by a key in the list. -/
theorem unsignImpl_sound {s : Signer} {input v : Bytes} (h : s.unsignImpl input = .ok v) :
    ∃ k ∈ s.secretKeys, s.signWith k v = input := by
  unfold unsignImpl at h
  split at h
  · cases h
  · rename_i value sig hsplit
    split at h
    · rename_i hv
      cases h
      obtain ⟨k, hk, hsig⟩ := (s.verifySignature_iff _ _).mp hv
      refine ⟨k, hk, ?_⟩
      rw [rsplit_sound hsplit, signWith, hsig]
    · cases h

/-- The characterisation of `unsign`. -/
theorem unsignImpl_ok_iff (s : Signer) (input v : Bytes) :
    s.unsignImpl input = .ok v ↔ ∃ k ∈ s.secretKeys, s.signWith k v = input := by
  constructor
  · exact unsignImpl_sound
  · rintro ⟨k, hk, rfl⟩; exact s.unsignImpl_signWith hk v

/-- `validate` is `unsign` succeeding. -/
theorem validate_iff (s : Signer) (input : Bytes) :
    s.validate input = true ↔ ∃ v, ∃ k ∈ s.secretKeys, s.signWith k v = input := by
  unfold validate
  constructor
  · intro h
    split at h
    · rename_i v hv; exact ⟨v, unsignImpl_sound hv⟩
    · cases h
  · rintro ⟨v, hv⟩
    rw [(s.unsignImpl_ok_iff input v).mpr hv]

theorem signatureFor_inj {s : Signer} {k₁ k₂ v₁ v₂ : Bytes}
    (h : s.signatureFor k₁ v₁ = s.signatureFor k₂ v₂) :
    s.rawSignature k₁ v₁ = s.rawSignature k₂ v₂ := base64Encode_injective h

/-- Tampering with the value: putting any value `v'` in front of `v`'s
signature makes `unsign` fail, unless that is an explicit collision of the
signing algorithm (`v'` has the same raw signature under some listed key). -/
theorem unsignImpl_tampered_value (s : Signer) (k v v' : Bytes) :
    (∃ e, s.unsignImpl (v' ++ s.sep ++ s.signatureFor k v) = .error e) ∨
      ∃ k' ∈ s.secretKeys, s.rawSignature k' v' = s.rawSignature k v := by
  cases h : s.unsignImpl (v' ++ s.sep ++ s.signatureFor k v) with
  | error e => exact Or.inl ⟨e, rfl⟩
  | ok r =>
    right
    obtain ⟨k', hk', heq⟩ := unsignImpl_sound h
    unfold signWith at heq
    have hsplit := rsplit_signWith s k' r
    unfold signWith at hsplit
    rw [heq, rsplit_append s.h_sep.1 (s.signatureFor_not_mem_sep k v)] at hsplit
    simp only [Option.some.injEq, Prod.mk.injEq] at hsplit
    obtain ⟨rfl, hsig⟩ := hsplit
    exact ⟨k', hk', signatureFor_inj hsig.symm⟩

private theorem exists_getElem?_ne {α : Type} {l₁ l₂ : List α} (h : l₁ ≠ l₂)
    (hl : l₁.length = l₂.length) : ∃ j < l₁.length, l₁[j]? ≠ l₂[j]? := by
  have : ¬ ∀ j, l₁[j]? = l₂[j]? := fun hall => h (List.ext_getElem? hall)
  rw [Classical.not_forall] at this
  obtain ⟨j, hj⟩ := this
  refine ⟨j, ?_, hj⟩
  apply Classical.byContradiction; intro hlt
  apply hj
  rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- Tampering with one byte. If changing any single byte of a signed string
(in the value, the separator or the signature) makes `unsign` succeed, then
either it returns the original value `v`, or it exhibits an explicit
collision of the signing algorithm: a different value `r` whose raw signature
under some listed key equals `v`'s under the signing key. No collision
resistance is assumed: a forgery by one-byte change *is* an HMAC collision.
The one hypothesis, `hlen`, is that raw signatures have a fixed length, which
`rawSignature_length_hmac` discharges for HMAC. -/
theorem unsignImpl_tampered (s : Signer) {k : Bytes} (v : Bytes) (i : Nat) (b : UInt8)
    (hlen : ∃ n, ∀ k' ∈ s.secretKeys, ∀ v', (s.rawSignature k' v').length = n)
    (hk : k ∈ s.secretKeys)
    (r : Bytes) (hr : s.unsignImpl ((s.signWith k v).set i b) = .ok r) :
    r = v ∨ ∃ k' ∈ s.secretKeys, r ≠ v ∧ s.rawSignature k' r = s.rawSignature k v := by
  obtain ⟨n, hn⟩ := hlen
  obtain ⟨k', hk', heq⟩ := unsignImpl_sound hr
  apply Classical.byContradiction
  intro hno
  have hrv : r ≠ v := fun h => hno (Or.inl h)
  have hraw : s.rawSignature k' r ≠ s.rawSignature k v :=
    fun h => hno (Or.inr ⟨k', hk', hrv, h⟩)
  -- The two signed strings, as value ++ (sep ++ signature).
  have hlenEq : (s.signWith k' r).length = (s.signWith k v).length := by
    rw [heq, List.length_set]
  have hsigLen : (s.signatureFor k' r).length = (s.signatureFor k v).length := by
    simp only [signatureFor, length_base64Encode, hn k' hk', hn k hk]
  have hvLen : r.length = v.length := by
    simp only [signWith, List.length_append] at hlenEq; omega
  have hsigNe : s.signatureFor k' r ≠ s.signatureFor k v :=
    fun h => hraw (signatureFor_inj h)
  -- Off position `i`, the tampered string agrees with the original.
  have hoff : ∀ j, j ≠ i → (s.signWith k' r)[j]? = (s.signWith k v)[j]? := by
    intro j hj; rw [heq, List.getElem?_set]; simp [Ne.symm hj]
  -- The values differ somewhere, so at `i`, inside the value.
  obtain ⟨j, hj, hjne⟩ := exists_getElem?_ne hrv hvLen
  have hji : j = i := by
    apply Classical.byContradiction; intro hji
    apply hjne
    have := hoff j hji
    simp only [signWith, List.append_assoc] at this
    rwa [List.getElem?_append_left hj, List.getElem?_append_left (hvLen ▸ hj)] at this
  -- The signatures differ somewhere, so at `i`, inside the signature.
  obtain ⟨j', hj', hj'ne⟩ := exists_getElem?_ne hsigNe hsigLen
  have hJi : r.length + s.sep.length + j' = i := by
    apply Classical.byContradiction; intro hJi
    apply hj'ne
    have := hoff _ hJi
    simp only [signWith] at this
    rw [List.getElem?_append_right (by simp), List.getElem?_append_right (by simp; omega)] at this
    simpa [hvLen] using this
  omega

/-- With a single secret key, changing any one byte (to a different byte, at
a position inside the string) makes `unsign` fail, unless the algorithm has
an explicit collision: a value `v' ≠ v` with the same raw signature as `v`. -/
theorem unsignImpl_tampered_single (s : Signer) {k : Bytes} (hkeys : s.secretKeys = [k]) (v : Bytes)
    (i : Nat) (hi : i < (s.signWith k v).length) (b : UInt8) (hb : (s.signWith k v)[i]? ≠ some b)
    (hlen : ∃ n, ∀ v', (s.rawSignature k v').length = n) :
    (∃ e, s.unsignImpl ((s.signWith k v).set i b) = .error e) ∨
      ∃ v', v' ≠ v ∧ s.rawSignature k v' = s.rawSignature k v := by
  cases h : s.unsignImpl ((s.signWith k v).set i b) with
  | error e => exact Or.inl ⟨e, rfl⟩
  | ok r =>
    have hk : k ∈ s.secretKeys := by simp [hkeys]
    obtain ⟨n, hn⟩ := hlen
    rcases s.unsignImpl_tampered v i b
        ⟨n, fun k' hk' v' => by simp [hkeys] at hk'; subst hk'; exact hn v'⟩ hk r h with hrv | hcol
    · exfalso
      subst hrv
      obtain ⟨k', hk', heq⟩ := unsignImpl_sound h
      simp [hkeys] at hk'; subst hk'
      have := congrArg (·[i]?) heq
      simp only [List.getElem?_set_self hi] at this
      exact hb this
    · obtain ⟨k', hk', hne, hraw⟩ := hcol
      simp [hkeys] at hk'; subst hk'
      exact Or.inr ⟨r, hne, hraw⟩

/-- For the HMAC algorithm, raw signatures have the digest's fixed length:
`unsignImpl_tampered`'s length hypothesis holds. -/
theorem rawSignature_length_hmac (s : Signer) (H : Hash) (h : s.algorithm = hmacAlgorithm H)
    (k v : Bytes) : (s.rawSignature k v).length = H.digestSize := by
  simp [rawSignature, h, hmacAlgorithm, length_hmac]

end LeanItsdangerous.Signer
