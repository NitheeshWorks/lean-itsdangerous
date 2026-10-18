import LeanItsdangerous.Specifications.Serializer

/-!
# Specifications: the headline properties

Each is a `Prop` about the implementation in `RepoImpl/`, with no proof
attached. `Proofs/Verified.lean` has one slot per property, filled by the
theorem of `Proofs/` that proves it.

HMAC is trusted, not proved, and nothing here assumes it is collision
resistant. The tampering properties instead conclude that a successful forgery
*exhibits* a collision (a different value with the same raw signature); their
one hypothesis about the algorithm is a fixed signature length (`hlen`),
which `Signer.rawSignature_length_hmac` discharges for HMAC.
-/

namespace LeanItsdangerous.Spec

/-! ## Encoding -/

/-- `base64_decode(base64_encode(b)) == b`. -/
def B64RoundTrip : Prop := ∀ bs : Bytes, b64decode (b64encode bs) = some bs

/-- The same, through the padding-tolerant entry point upstream exposes. -/
def Base64DecodeRoundTrip : Prop := ∀ bs : Bytes, base64Decode (b64encode bs) = some bs

/-- `bytes_to_int(int_to_bytes(n)) == n` for 64-bit `n`. -/
def IntBytesRoundTrip : Prop := ∀ n : UInt64, bytesToInt (intToBytes n) = some n

/-- The timestamp encoding round trip. -/
def TimestampRoundTrip : Prop :=
  ∀ ts : UInt64, TimestampSigner.decodeTimestamp (TimestampSigner.encodeTimestamp ts) = some ts

/-- Base64url output never contains a byte of a valid separator, which is
why `unsign` can find the signature. -/
def B64AvoidsSep : Prop := ∀ sep bs : Bytes, ValidSep sep → ∀ c ∈ b64encode bs, c ∉ sep

/-! ## Signer -/

/-- `unsign(sign(v)) == v`. -/
def UnsignSign : Prop := ∀ (s : Signer) (v : Bytes), s.unsignImpl (s.sign v) = .ok v

/-- Key rotation: a value signed by any key in the list unsigns. -/
def KeyRotation : Prop :=
  ∀ (s : Signer) (k : Bytes), k ∈ s.secretKeys → ∀ v, s.unsignImpl (s.signWith k v) = .ok v

/-- An `ok v` from `unsign` means some key in the list signed `v`. -/
def UnsignSound : Prop :=
  ∀ (s : Signer) (input v : Bytes), s.unsignImpl input = .ok v →
    ∃ k ∈ s.secretKeys, s.signWith k v = input

/-- Replacing the value under a signature makes `unsign` fail, or exhibits
an explicit collision of the signing algorithm. -/
def UnsignTamperedValue : Prop :=
  ∀ (s : Signer) (k v v' : Bytes),
    (∃ e, s.unsignImpl (v' ++ s.sep ++ s.signatureFor k v) = .error e) ∨
      ∃ k' ∈ s.secretKeys, s.rawSignature k' v' = s.rawSignature k v

/-- Changing one byte of a signed string: a successful `unsign` returns the
original value, or exhibits an explicit collision of the signing algorithm
(a different value with the same raw signature). No collision resistance is
assumed; only that raw signatures have a fixed length. -/
def UnsignTampered : Prop :=
  ∀ (s : Signer) (k v : Bytes) (i : Nat) (b : UInt8),
    (∃ n, ∀ k' ∈ s.secretKeys, ∀ v', (s.rawSignature k' v').length = n) →
    k ∈ s.secretKeys →
    ∀ r, s.unsignImpl ((s.signWith k v).set i b) = .ok r →
      r = v ∨ ∃ k' ∈ s.secretKeys, r ≠ v ∧ s.rawSignature k' r = s.rawSignature k v

/-- With one key, changing any one byte makes `unsign` fail, or exhibits an
explicit collision. -/
def UnsignTamperedSingle : Prop :=
  ∀ (s : Signer) (k : Bytes), s.secretKeys = [k] → ∀ (v : Bytes) (i : Nat),
    i < (s.signWith k v).length → ∀ b : UInt8, (s.signWith k v)[i]? ≠ some b →
    (∃ n, ∀ v', (s.rawSignature k v').length = n) →
    (∃ e, s.unsignImpl ((s.signWith k v).set i b) = .error e) ∨
      ∃ v', v' ≠ v ∧ s.rawSignature k v' = s.rawSignature k v

/-- The comparison `unsign` uses is equality. -/
def CtEqIsEq : Prop := ∀ a b : Bytes, ctEq a b = true ↔ a = b

/-! ## TimestampSigner -/

/-- Signed at `ts` by any key, unsigned within `max_age`: value and `ts` back. -/
def TimestampKeyRotation : Prop :=
  ∀ (t : TimestampSigner) (k : Bytes), k ∈ t.toSigner.secretKeys →
    ∀ (maxAge : Option Nat) (now ts : UInt64), TimestampSigner.AgeOk maxAge now ts →
    ∀ v, t.unsignImpl maxAge now (t.signWith k ts v) = .ok (v, ts)

/-- An `ok` result is signed by a key in the list and within `max_age`. -/
def TimestampUnsignSound : Prop :=
  ∀ (t : TimestampSigner) (maxAge : Option Nat) (now : UInt64) (input : Bytes)
    (r : Bytes × UInt64), t.unsignImpl maxAge now input = .ok r →
    t.SignedBy input r.1 r.2 ∧ TimestampSigner.AgeOk maxAge now r.2

/-- `max_age` monotonicity. -/
def MaxAgeMono : Prop :=
  ∀ (t : TimestampSigner) (m m' : Nat), m ≤ m' → ∀ (now : UInt64) (input : Bytes)
    (r : Bytes × UInt64), t.unsignImpl (some m) now input = .ok r →
    t.unsignImpl (some m') now input = .ok r

/-- Older than `max_age` raises `SignatureExpired` with the signing date. -/
def MaxAgeExpired : Prop :=
  ∀ (t : TimestampSigner) (k : Bytes), k ∈ t.toSigner.secretKeys →
    ∀ (m : Nat) (now ts : UInt64), ts.toNat + m < now.toNat → ∀ v,
    ∃ msg, t.unsignImpl (some m) now (t.signWith k ts v) =
      .error (.signatureExpired msg (some v) (some ts.toNat))

/-! ## Serializers -/

/-- The URL-safe payload wrapping preserves a codec round trip. -/
def UrlSafeRoundTrip : Prop := ∀ (α : Type) (c : Codec α), c.RoundTrip → (urlSafeCodec c).RoundTrip

/-- `loads(dumps(x)) == x`. -/
def LoadsDumps : Prop :=
  ∀ (α : Type) (s : Serializer α), s.codec.RoundTrip → ∀ (x : α) (salt : Option Bytes),
    s.loadsImpl (s.dumps x salt) salt = .ok x

/-- An `ok x` from `loads` is a signed payload that loads to `x`. -/
def LoadsSound : Prop :=
  ∀ (α : Type) (s : Serializer α) (input : Bytes) (salt : Option Bytes) (x : α),
    s.loadsImpl input salt = .ok x → s.SignedBy salt input x

/-- The timed `loads(dumps(x))` within `max_age`. -/
def TimedLoadsDumps : Prop :=
  ∀ (α : Type) (s : TimedSerializer α), s.toSerializer.codec.RoundTrip →
    ∀ (x : α) (salt : Option Bytes) (maxAge : Option Nat) (now ts : UInt64),
    TimestampSigner.AgeOk maxAge now ts → s.loadsImpl (s.dumps ts x salt) maxAge now salt = .ok (x, ts)

/-- An `ok` from timed `loads` is a signed, fresh payload that loads. -/
def TimedLoadsSound : Prop :=
  ∀ (α : Type) (s : TimedSerializer α) (input : Bytes) (maxAge : Option Nat) (now : UInt64)
    (salt : Option Bytes) (r : α × UInt64), s.loadsImpl input maxAge now salt = .ok r →
    s.SignedBy salt maxAge now input r.1 r.2

end LeanItsdangerous.Spec
