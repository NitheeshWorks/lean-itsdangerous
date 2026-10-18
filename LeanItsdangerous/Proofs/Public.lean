import LeanItsdangerous.APIs.Signer

/-!
# The headline theorems, about the public functions

Each is an equation or an `↔` about what users call (`sign`, `unsign`,
`dumps`, `loads`, `validate`), and each is a short corollary of the
implementation lemma in `Proofs/Signer.lean`, `Proofs/Timed.lean` or
`Proofs/Serializer.lean`. `Except.val` forgets the proof a refined result
carries.

What the refinements say is not repeated here: `Signer.unsign`,
`TimestampSigner.unsign`, `Serializer.loads` and `TimedSerializer.loads`
return their soundness in their types.
-/

namespace LeanItsdangerous

namespace Signer

/-- Unsigning what a signer signed returns the value. -/
theorem unsign_sign (s : Signer) (v : Bytes) : (s.unsign (s.sign v)).val = .ok v := by
  rw [unsign_val, unsignImpl_sign]

/-- The plan's name for the round trip, as lean-starlette cites it. -/
theorem session_sign_verify (s : Signer) (v : Bytes) : (s.unsign (s.sign v)).val = .ok v :=
  s.unsign_sign v

/-- Key rotation: a value signed with any key in the list unsigns. -/
theorem unsign_signWith (s : Signer) {k : Bytes} (hk : k ∈ s.secretKeys) (v : Bytes) :
    (s.unsign (s.signWith k v)).val = .ok v := by
  rw [unsign_val, unsignImpl_signWith _ hk]

/-- What a successful `unsign` means, exactly: the input is the value signed
with one of the keys. -/
theorem unsign_eq_ok_iff (s : Signer) (signedValue v : Bytes) :
    (s.unsign signedValue).val = .ok v ↔ ∃ k ∈ s.secretKeys, s.signWith k v = signedValue := by
  rw [unsign_val, unsignImpl_ok_iff]

/-- A one-byte change that still unsigns returns the original value, or
exhibits a collision of the signing algorithm. -/
theorem unsign_tampered (s : Signer) {k : Bytes} (hk : k ∈ s.secretKeys) (v : Bytes) (i : Nat)
    (b : UInt8) (hlen : ∃ n, ∀ k' ∈ s.secretKeys, ∀ v', (s.rawSignature k' v').length = n)
    (r : Bytes) (hr : (s.unsign ((s.signWith k v).set i b)).val = .ok r) :
    r = v ∨ ∃ k' ∈ s.secretKeys, r ≠ v ∧ s.rawSignature k' r = s.rawSignature k v := by
  rw [unsign_val] at hr; exact s.unsignImpl_tampered v i b hlen hk r hr

/-- With one key, a one-byte change fails to unsign, or exhibits a collision. -/
theorem unsign_tampered_single (s : Signer) {k : Bytes} (hkeys : s.secretKeys = [k]) (v : Bytes)
    (i : Nat) (hi : i < (s.signWith k v).length) (b : UInt8) (hb : (s.signWith k v)[i]? ≠ some b)
    (hlen : ∃ n, ∀ v', (s.rawSignature k v').length = n) :
    (∃ e, (s.unsign ((s.signWith k v).set i b)).val = .error e) ∨
      ∃ v', v' ≠ v ∧ s.rawSignature k v' = s.rawSignature k v := by
  rw [unsign_val]; exact s.unsignImpl_tampered_single hkeys v i hi b hb hlen

/-- Swapping the value under a signature fails to unsign, or exhibits a
collision. -/
theorem unsign_tampered_value (s : Signer) (k v v' : Bytes) :
    (∃ e, (s.unsign (v' ++ s.sep ++ s.signatureFor k v)).val = .error e) ∨
      ∃ k' ∈ s.secretKeys, s.rawSignature k' v' = s.rawSignature k v := by
  rw [unsign_val]; exact s.unsignImpl_tampered_value k v v'

end Signer

namespace TimestampSigner

/-- Signed at `ts`, unsigned at `now` within `max_age`: the value and `ts`
come back. -/
theorem unsign_sign (t : TimestampSigner) {maxAge : Option Nat} {now ts : UInt64}
    (hage : AgeOk maxAge now ts) (v : Bytes) :
    (t.unsign (t.sign v ts) maxAge now).val = .ok (v, ts) := by
  rw [unsign_val, unsignImpl_sign _ hage]

/-- Key rotation for timestamped signatures. -/
theorem unsign_signWith (t : TimestampSigner) {k : Bytes} (hk : k ∈ t.toSigner.secretKeys)
    {maxAge : Option Nat} {now ts : UInt64} (hage : AgeOk maxAge now ts) (v : Bytes) :
    (t.unsign (t.signWith k v ts) maxAge now).val = .ok (v, ts) := by
  rw [unsign_val, unsignImpl_signWith _ hk hage]

/-- Raising `max_age` never rejects what a smaller one accepted. -/
theorem unsign_maxAge_mono (t : TimestampSigner) {m m' : Nat} (hm : m ≤ m') {now : UInt64}
    {signedValue : Bytes} {r : Bytes × UInt64}
    (h : (t.unsign signedValue (some m) now).val = .ok r) :
    (t.unsign signedValue (some m') now).val = .ok r := by
  rw [unsign_val] at h ⊢; exact t.unsignImpl_maxAge_mono hm now signedValue r h

/-- A signature older than `max_age` raises `SignatureExpired` with the
value and the signing time. -/
theorem unsign_expired (t : TimestampSigner) {k : Bytes} (hk : k ∈ t.toSigner.secretKeys)
    {m : Nat} {now ts : UInt64} (hold : ts.toNat + m < now.toNat) (v : Bytes) :
    ∃ msg, (t.unsign (t.signWith k v ts) (some m) now).val =
      .error (.signatureExpired msg (some v) (some ⟨ts.toNat⟩)) := by
  rw [unsign_val]; exact t.unsignImpl_expired hk hold v

end TimestampSigner

/-- `loads (dumps x) = x`, for any salt and any lawful payload codec. -/
theorem Serializer.loads_dumps {α : Type} (s : Serializer α) (hc : s.codec.Lawful) (x : α)
    (salt : Option Bytes) : (s.loads (s.dumps x salt) salt).val = .ok x := by
  rw [loads_val, loadsImpl_dumps _ hc]

/-- The timed `loads (dumps x at ts)` within `max_age` returns `x` and `ts`. -/
theorem TimedSerializer.loads_dumps {α : Type} (s : TimedSerializer α)
    (hc : s.toSerializer.codec.Lawful) (x : α) (salt : Option Bytes) {maxAge : Option Nat}
    {now ts : UInt64} (hage : TimestampSigner.AgeOk maxAge now ts) :
    (s.loads (s.dumps x ts salt) maxAge now salt).val = .ok (x, ts) := by
  rw [loads_val, loadsImpl_dumps _ hc x salt hage]

end LeanItsdangerous
