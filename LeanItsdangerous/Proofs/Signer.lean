import LeanItsdangerous.Proofs.Encoding

/-!
# Proofs: Signer

* `unsign_signWith` (key rotation): a value signed by *any* key in the list
  unsigns to itself.
* `unsign_sign`: the special case of the signing (newest) key.
* `unsign_sound`: an `ok v` from `unsign` means the input is `v` signed by
  some key in the list. This is the refinement `APIs/` returns.
* `unsign_ok_iff`: the two together, as a characterisation.
* `unsign_tampered_value`, `unsign_tampered`, `unsign_tampered_single`: what
  tampering can and cannot achieve, under explicit hypotheses about the
  signing algorithm (HMAC is trusted, so its collision resistance is a
  hypothesis, never a theorem).
-/

namespace LeanItsdangerous.Signer

theorem secretKey_mem (s : Signer) : s.secretKey ∈ s.secretKeys := List.getLast_mem _

theorem signatureFor_not_mem_sep (s : Signer) (k v : Bytes) :
    ∀ c ∈ s.signatureFor k v, c ∉ s.sep :=
  not_mem_sep_of_mem_b64encode s.h_sep

theorem rsplit_signWith (s : Signer) (k v : Bytes) :
    rsplit s.sep (s.signWith k v) = some (v, s.signatureFor k v) :=
  rsplit_append s.h_sep.1 (s.signatureFor_not_mem_sep k v)

theorem verifySignature_iff (s : Signer) (v sig : Bytes) :
    s.verifySignature v sig = true ↔ ∃ k ∈ s.secretKeys, s.signatureFor k v = sig := by
  simp [verifySignature, List.any_eq_true]

/-- Key rotation: verification succeeds if any key in the list signed the
value. -/
theorem unsign_signWith (s : Signer) {k : Bytes} (hk : k ∈ s.secretKeys) (v : Bytes) :
    s.unsignImpl (s.signWith k v) = .ok v := by
  have hv : s.verifySignature v (s.signatureFor k v) = true :=
    (s.verifySignature_iff _ _).mpr ⟨k, hk, rfl⟩
  simp [unsignImpl, rsplit_signWith, hv]

/-- Unsigning with the same signer returns the original value. -/
theorem unsign_sign (s : Signer) (v : Bytes) : s.unsignImpl (s.sign v) = .ok v :=
  s.unsign_signWith s.secretKey_mem v

/-- Soundness: `unsign` succeeds only on a value signed by a key in the list. -/
theorem unsign_sound {s : Signer} {input v : Bytes} (h : s.unsignImpl input = .ok v) :
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
theorem unsign_ok_iff (s : Signer) (input v : Bytes) :
    s.unsignImpl input = .ok v ↔ ∃ k ∈ s.secretKeys, s.signWith k v = input := by
  constructor
  · exact unsign_sound
  · rintro ⟨k, hk, rfl⟩; exact s.unsign_signWith hk v

/-- `validate` is `unsign` succeeding. -/
theorem validate_iff (s : Signer) (input : Bytes) :
    s.validate input = true ↔ ∃ v, ∃ k ∈ s.secretKeys, s.signWith k v = input := by
  unfold validate
  constructor
  · intro h
    split at h
    · rename_i v hv; exact ⟨v, unsign_sound hv⟩
    · cases h
  · rintro ⟨v, hv⟩
    rw [(s.unsign_ok_iff input v).mpr hv]

theorem signatureFor_inj {s : Signer} {k₁ k₂ v₁ v₂ : Bytes}
    (h : s.signatureFor k₁ v₁ = s.signatureFor k₂ v₂) :
    s.rawSignature k₁ v₁ = s.rawSignature k₂ v₂ := b64encode_injective h

/-- Tampering with the value: replacing the value of a signed string by any
other value `v'` makes `unsign` fail, provided the signing algorithm's output
on `v'` under every accepted key differs from its output on `v` under the
signing key (the HMAC-outputs-differ hypothesis). -/
theorem unsign_tampered_value (s : Signer) (k v v' : Bytes)
    (hdiff : ∀ k' ∈ s.secretKeys, s.rawSignature k' v' ≠ s.rawSignature k v) :
    ∃ e, s.unsignImpl (v' ++ s.sep ++ s.signatureFor k v) = .error e := by
  cases h : s.unsignImpl (v' ++ s.sep ++ s.signatureFor k v) with
  | error e => exact ⟨e, rfl⟩
  | ok r =>
    exfalso
    obtain ⟨k', hk', heq⟩ := unsign_sound h
    unfold signWith at heq
    have hsplit := rsplit_signWith s k' r
    unfold signWith at hsplit
    rw [heq, rsplit_append s.h_sep.1 (s.signatureFor_not_mem_sep k v)] at hsplit
    simp only [Option.some.injEq, Prod.mk.injEq] at hsplit
    obtain ⟨rfl, hsig⟩ := hsplit
    exact hdiff k' hk' (signatureFor_inj hsig.symm)

private theorem exists_getElem?_ne {α : Type} {l₁ l₂ : List α} (h : l₁ ≠ l₂)
    (hl : l₁.length = l₂.length) : ∃ j < l₁.length, l₁[j]? ≠ l₂[j]? := by
  have : ¬ ∀ j, l₁[j]? = l₂[j]? := fun hall => h (List.ext_getElem? hall)
  rw [Classical.not_forall] at this
  obtain ⟨j, hj⟩ := this
  refine ⟨j, ?_, hj⟩
  apply Classical.byContradiction; intro hlt
  apply hj
  rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- Tampering with one byte. Changing any single byte of a signed string, in
the value, the separator or the signature, can never make `unsign` return a
*different* value. Hypotheses, both about the trusted algorithm: every raw
signature under an accepted key has the same length (`hlen`, which
`rawSignature_length_hmac` discharges for HMAC), and signatures of different
values differ (`hdiff`, the HMAC-outputs-differ hypothesis). -/
theorem unsign_tampered (s : Signer) {k : Bytes} (v : Bytes) (i : Nat) (b : UInt8)
    (hlen : ∃ n, ∀ k' ∈ s.secretKeys, ∀ v', (s.rawSignature k' v').length = n)
    (hk : k ∈ s.secretKeys)
    (hdiff : ∀ k' ∈ s.secretKeys, ∀ v', v' ≠ v → s.rawSignature k' v' ≠ s.rawSignature k v)
    (r : Bytes) (hr : s.unsignImpl ((s.signWith k v).set i b) = .ok r) : r = v := by
  obtain ⟨n, hn⟩ := hlen
  obtain ⟨k', hk', heq⟩ := unsign_sound hr
  apply Classical.byContradiction; intro hrv
  -- The two signed strings, as value ++ (sep ++ signature).
  have hlenEq : (s.signWith k' r).length = (s.signWith k v).length := by
    rw [heq, List.length_set]
  have hsigLen : (s.signatureFor k' r).length = (s.signatureFor k v).length := by
    simp only [signatureFor, length_b64encode, hn k' hk', hn k hk]
  have hvLen : r.length = v.length := by
    simp only [signWith, List.length_append] at hlenEq; omega
  have hsigNe : s.signatureFor k' r ≠ s.signatureFor k v :=
    fun h => hdiff k' hk' r hrv (signatureFor_inj h)
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
a position inside the string) makes `unsign` fail. -/
theorem unsign_tampered_single (s : Signer) {k : Bytes} (hkeys : s.secretKeys = [k]) (v : Bytes)
    (i : Nat) (hi : i < (s.signWith k v).length) (b : UInt8) (hb : (s.signWith k v)[i]? ≠ some b)
    (hlen : ∃ n, ∀ v', (s.rawSignature k v').length = n)
    (hdiff : ∀ v', v' ≠ v → s.rawSignature k v' ≠ s.rawSignature k v) :
    ∃ e, s.unsignImpl ((s.signWith k v).set i b) = .error e := by
  cases h : s.unsignImpl ((s.signWith k v).set i b) with
  | error e => exact ⟨e, rfl⟩
  | ok r =>
    exfalso
    have hk : k ∈ s.secretKeys := by simp [hkeys]
    obtain ⟨n, hn⟩ := hlen
    have hrv := s.unsign_tampered v i b ⟨n, fun k' hk' v' => by simp [hkeys] at hk'; subst hk'; exact hn v'⟩ hk
      (fun k' hk' v' hv' => by simp [hkeys] at hk'; subst hk'; exact hdiff v' hv') r h
    subst hrv
    obtain ⟨k', hk', heq⟩ := unsign_sound h
    simp [hkeys] at hk'; subst hk'
    have := congrArg (·[i]?) heq
    simp only [List.getElem?_set_self hi] at this
    exact hb this

/-- For the HMAC algorithm, raw signatures have the digest's fixed length:
`unsign_tampered`'s length hypothesis holds. -/
theorem rawSignature_length_hmac (s : Signer) (H : Hash) (h : s.algorithm = hmacAlgorithm H)
    (k v : Bytes) : (s.rawSignature k v).length = H.digestSize := by
  simp [rawSignature, h, hmacAlgorithm, length_hmac]

end LeanItsdangerous.Signer
