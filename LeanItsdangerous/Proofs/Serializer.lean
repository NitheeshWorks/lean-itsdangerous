import LeanItsdangerous.Proofs.Timed
import LeanItsdangerous.Specifications.Serializer

/-!
# Proofs: serializers

* `urlSafeCodec_roundTrip`: the URL-safe payload wrapping preserves a codec
  round trip.
* `loads_dumps` (plain and timed): `loads (dumps x) = x` for a round-tripping
  codec, with any salt, and for the timed serializer within `max_age`.
* `loads_signWith`: key rotation through the serializer.
* `loads_sound` (plain and timed): what an `ok` result means; the refinement
  `APIs/` returns.
-/

namespace LeanItsdangerous

theorem b64encode_ne_dot_cons (bs t : Bytes) : b64encode bs ≠ 46 :: t := by
  intro h
  have := isAlphabet_of_mem_b64encode (c := 46) (bs := bs) (by rw [h]; exact List.mem_cons_self)
  exact absurd this (by decide)

/-- The URL-safe wrapping preserves a codec round trip. -/
theorem urlSafeCodec_roundTrip {α : Type} (c : Codec α) (h : c.RoundTrip) :
    (urlSafeCodec c).RoundTrip := by
  intro x
  simp only [urlSafeCodec]
  split
  · rename_i t ht; exact absurd ht (b64encode_ne_dot_cons _ _)
  · rw [base64Decode_b64encode]; exact h x

namespace Serializer

variable {α : Type}

theorem makeSigner_mem_unsigners (s : Serializer α) (salt : Option Bytes) :
    s.makeSigner salt ∈ s.unsigners salt := List.mem_cons_self

theorem makeSigner_secretKeys (s : Serializer α) (salt : Option Bytes) :
    (s.makeSigner salt).secretKeys = s.secretKeys := rfl

theorem loadPayload_ok_iff (s : Serializer α) (p : Bytes) (x : α) :
    s.loadPayload p = .ok x ↔ s.codec.loads p = .ok x := by
  unfold loadPayload
  split <;> rename_i h <;> simp [h]

/-- Key rotation through the serializer: a payload signed by the main signer
with any of the secret keys loads. -/
theorem loads_signWith (s : Serializer α) (hc : s.codec.RoundTrip) (salt : Option Bytes)
    {k : Bytes} (hk : k ∈ s.secretKeys) (x : α) :
    s.loadsImpl ((s.makeSigner salt).signWith k (s.dumpPayload x)) salt = .ok x := by
  have hu := (s.makeSigner salt).unsign_signWith (k := k) hk (s.dumpPayload x)
  simp only [loadsImpl, unsigners, loadsWith, hu]
  exact (s.loadPayload_ok_iff _ _).mpr (hc x)

/-- `loads (dumps x) = x`, with any salt, for a round-tripping codec. -/
theorem loads_dumps (s : Serializer α) (hc : s.codec.RoundTrip) (x : α) (salt : Option Bytes) :
    s.loadsImpl (s.dumps x salt) salt = .ok x :=
  s.loads_signWith hc salt (Signer.secretKey_mem _) x

theorem loadsWith_sound (s : Serializer α) (input : Bytes) :
    ∀ (us : List Signer) (last : Option BadSignature) (x : α),
      s.loadsWith input us last = .ok x →
      ∃ u ∈ us, ∃ k ∈ u.secretKeys, ∃ p, u.signWith k p = input ∧ s.codec.loads p = .ok x
  | [], _, x, h => by simp [loadsWith] at h
  | u :: us, last, x, h => by
    simp only [loadsWith] at h
    split at h
    · rename_i p hp
      obtain ⟨k, hk, hs⟩ := Signer.unsign_sound hp
      exact ⟨u, List.mem_cons_self, k, hk, p, hs, (s.loadPayload_ok_iff _ _).mp h⟩
    · obtain ⟨u', hu', rest⟩ := s.loadsWith_sound input us _ x h
      exact ⟨u', List.mem_cons_of_mem _ hu', rest⟩

/-- Soundness of `loads`. -/
theorem loads_sound {s : Serializer α} {input : Bytes} {salt : Option Bytes} {x : α}
    (h : s.loadsImpl input salt = .ok x) : s.SignedBy salt input x :=
  s.loadsWith_sound input _ _ x h

/-- `loads_unsafe (dumps x) = (true, x)`. -/
theorem loadsUnsafe_dumps (s : Serializer α) (hc : s.codec.RoundTrip) (x : α)
    (salt : Option Bytes) : s.loadsUnsafe (s.dumps x salt) salt = .ok (true, some x) := by
  simp [loadsUnsafe, s.loads_dumps hc]

end Serializer

namespace TimedSerializer

variable {α : Type}

theorem loads_signWith (s : TimedSerializer α) (hc : s.toSerializer.codec.RoundTrip)
    (salt : Option Bytes) {k : Bytes} (hk : k ∈ s.toSerializer.secretKeys)
    {maxAge : Option Nat} {now ts : UInt64} (hage : TimestampSigner.AgeOk maxAge now ts) (x : α) :
    s.loadsImpl ((s.makeSigner salt).signWith k ts (s.toSerializer.dumpPayload x)) maxAge now salt
      = .ok (x, ts) := by
  simp only [loadsImpl, Serializer.unsigners, loadsWith]
  have := (s.makeSigner salt).unsign_signWith (k := k) hk hage (s.toSerializer.dumpPayload x)
  simp only [makeSigner] at this ⊢
  rw [this]
  have hl : s.toSerializer.loadPayload (s.toSerializer.dumpPayload x) = .ok x :=
    (Serializer.loadPayload_ok_iff _ _ _).mpr (hc x)
  simp [Except.map, hl]

/-- `loads (dumps x at ts) at now = (x, ts)` within `max_age`. -/
theorem loads_dumps (s : TimedSerializer α) (hc : s.toSerializer.codec.RoundTrip) (x : α)
    (salt : Option Bytes) {maxAge : Option Nat} {now ts : UInt64}
    (hage : TimestampSigner.AgeOk maxAge now ts) :
    s.loadsImpl (s.dumps ts x salt) maxAge now salt = .ok (x, ts) :=
  s.loads_signWith hc salt (Signer.secretKey_mem _) hage x

theorem loadsWith_sound (s : TimedSerializer α) (maxAge : Option Nat) (now : UInt64)
    (input : Bytes) :
    ∀ (us : List Signer) (last : Option BadData) (r : α × UInt64),
      s.loadsWith maxAge now input us last = .ok r →
      ∃ u ∈ us, ∃ p, (TimestampSigner.mk u).SignedBy input p r.2 ∧
        TimestampSigner.AgeOk maxAge now r.2 ∧ s.toSerializer.codec.loads p = .ok r.1
  | [], _, r, h => by simp [loadsWith] at h
  | u :: us, last, r, h => by
    simp only [loadsWith] at h
    split at h
    · rename_i p ts hp
      obtain ⟨hsig, hage⟩ := TimestampSigner.unsign_sound hp
      cases hl : s.toSerializer.loadPayload p with
      | error e => rw [hl] at h; cases h
      | ok x =>
        rw [hl] at h; cases h
        exact ⟨u, List.mem_cons_self, p, hsig, hage, (Serializer.loadPayload_ok_iff _ _ _).mp hl⟩
    · split at h
      · cases h
      · split at h
        · obtain ⟨u', hu', rest⟩ := s.loadsWith_sound maxAge now input us _ r h
          exact ⟨u', List.mem_cons_of_mem _ hu', rest⟩
        · cases h

/-- Soundness of timed `loads`. -/
theorem loads_sound {s : TimedSerializer α} {input : Bytes} {maxAge : Option Nat} {now : UInt64}
    {salt : Option Bytes} {r : α × UInt64} (h : s.loadsImpl input maxAge now salt = .ok r) :
    s.SignedBy salt maxAge now input r.1 r.2 :=
  s.loadsWith_sound maxAge now input _ _ r h

end TimedSerializer

end LeanItsdangerous
