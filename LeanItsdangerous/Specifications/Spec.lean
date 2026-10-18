import LeanItsdangerous.APIs.Signer

/-!
# Specifications: the headline properties

Each is a `Prop` about the public functions (`sign`, `unsign`, `dumps`,
`loads`, `validate`) or about the codec theory, with no proof attached.
`Proofs/Verified.lean` has one slot per property, filled by the theorem of
`Proofs/Public.lean` or `Proofs/Codec.lean` that proves it.

HMAC is trusted, not proved, and nothing here assumes it is collision
resistant. The tampering properties conclude that a successful forgery
*exhibits* a collision; their one hypothesis about the algorithm is a fixed
signature length, which `Signer.rawSignature_length_hmac` discharges for
HMAC.
-/

namespace LeanItsdangerous.Spec

/-! ## The codec theory -/

/-- The codec law is closed under `andThen`. -/
def LawfulAndThen : Prop :=
  ∀ (α : Type) (inner : Codec α) (outer : Codec Bytes),
    inner.Lawful → outer.Lawful → (inner.andThen outer).Lawful

/-- base64url, the integer bytes and the timestamp are lawful codecs. -/
def EncodingsLawful : Prop :=
  base64Codec.Lawful ∧ intCodec.Lawful ∧ timestampCodec.Lawful

/-- The URL-safe wrapping preserves the codec law. -/
def UrlSafeLawful : Prop := ∀ (α : Type) (c : Codec α), c.Lawful → (urlSafeCodec c).Lawful

/-- `base64_decode(base64_encode(b)) == b`. -/
def Base64RoundTrip : Prop := ∀ b : Bytes, base64Decode (base64Encode b) = some b

/-! ## Signer -/

/-- `unsign(sign(v)) == v`. -/
def UnsignSign : Prop := ∀ (s : Signer) (v : Bytes), (s.unsign (s.sign v)).val = .ok v

/-- Key rotation: a value signed with any key in the list unsigns. -/
def KeyRotation : Prop :=
  ∀ (s : Signer) (k : Bytes), k ∈ s.secretKeys → ∀ v, (s.unsign (s.signWith k v)).val = .ok v

/-- `unsign` succeeds exactly on values signed with a listed key. -/
def UnsignEqOkIff : Prop :=
  ∀ (s : Signer) (signedValue v : Bytes),
    (s.unsign signedValue).val = .ok v ↔ ∃ k ∈ s.secretKeys, s.signWith k v = signedValue

/-- Swapping the value under a signature fails, or exhibits a collision. -/
def UnsignTamperedValue : Prop :=
  ∀ (s : Signer) (k v v' : Bytes),
    (∃ e, (s.unsign (v' ++ s.sep ++ s.signatureFor k v)).val = .error e) ∨
      ∃ k' ∈ s.secretKeys, s.rawSignature k' v' = s.rawSignature k v

/-- A one-byte change that still unsigns returns the original value, or
exhibits a collision. -/
def UnsignTampered : Prop :=
  ∀ (s : Signer) (k : Bytes), k ∈ s.secretKeys → ∀ (v : Bytes) (i : Nat) (b : UInt8),
    (∃ n, ∀ k' ∈ s.secretKeys, ∀ v', (s.rawSignature k' v').length = n) →
    ∀ r, (s.unsign ((s.signWith k v).set i b)).val = .ok r →
      r = v ∨ ∃ k' ∈ s.secretKeys, r ≠ v ∧ s.rawSignature k' r = s.rawSignature k v

/-- With one key, a one-byte change fails to unsign, or exhibits a collision. -/
def UnsignTamperedSingle : Prop :=
  ∀ (s : Signer) (k : Bytes), s.secretKeys = [k] → ∀ (v : Bytes) (i : Nat),
    i < (s.signWith k v).length → ∀ b : UInt8, (s.signWith k v)[i]? ≠ some b →
    (∃ n, ∀ v', (s.rawSignature k v').length = n) →
    (∃ e, (s.unsign ((s.signWith k v).set i b)).val = .error e) ∨
      ∃ v', v' ≠ v ∧ s.rawSignature k v' = s.rawSignature k v

/-- The signature comparison is equality. -/
def CtEqIff : Prop := ∀ a b : Bytes, ctEq a b = true ↔ a = b

/-! ## TimestampSigner -/

/-- Signed at `ts` by any listed key, unsigned within `max_age`: value and
`ts` back. -/
def TimestampUnsignSign : Prop :=
  ∀ (t : TimestampSigner) (k : Bytes), k ∈ t.toSigner.secretKeys →
    ∀ (maxAge : Option Nat) (now ts : UInt64), TimestampSigner.AgeOk maxAge now ts →
    ∀ v, (t.unsign (t.signWith k v ts) maxAge now).val = .ok (v, ts)

/-- `max_age` monotonicity. -/
def MaxAgeMono : Prop :=
  ∀ (t : TimestampSigner) (m m' : Nat), m ≤ m' → ∀ (now : UInt64) (signedValue : Bytes)
    (r : Bytes × UInt64), (t.unsign signedValue (some m) now).val = .ok r →
    (t.unsign signedValue (some m') now).val = .ok r

/-- Older than `max_age` raises `SignatureExpired` with the signing date. -/
def MaxAgeExpired : Prop :=
  ∀ (t : TimestampSigner) (k : Bytes), k ∈ t.toSigner.secretKeys →
    ∀ (m : Nat) (now ts : UInt64), ts.toNat + m < now.toNat → ∀ v,
    ∃ msg, (t.unsign (t.signWith k v ts) (some m) now).val =
      .error (.signatureExpired msg (some v) (some ts.toNat))

/-! ## Serializers -/

/-- `loads(dumps(x)) == x` for a lawful payload codec. -/
def LoadsDumps : Prop :=
  ∀ (α : Type) (s : Serializer α), s.codec.Lawful → ∀ (x : α) (salt : Option Bytes),
    (s.loads (s.dumps x salt) salt).val = .ok x

/-- The timed `loads(dumps(x))` within `max_age`. -/
def TimedLoadsDumps : Prop :=
  ∀ (α : Type) (s : TimedSerializer α), s.toSerializer.codec.Lawful →
    ∀ (x : α) (salt : Option Bytes) (maxAge : Option Nat) (now ts : UInt64),
    TimestampSigner.AgeOk maxAge now ts → (s.loads (s.dumps x ts salt) maxAge now salt).val = .ok (x, ts)

end LeanItsdangerous.Spec
