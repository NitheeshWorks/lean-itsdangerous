import LeanItsdangerous.Proofs.Serializer
import LeanItsdangerous.Specifications.Spec

/-!
# The harness: one `Verified<Layer>` structure per layer

Each `Verified<Layer>` has a field per headline property of
`Specifications/Spec.lean` for that layer, and `theVerified<Layer>` fills
every field with the theorem that proves it. A specification with no proof is
a compile error the moment it needs a field here: you cannot construct the
value without every proof in hand. If a stated specification turned out
false, its slot's type would flip to a refutation rather than being dropped,
so this file stays an honest map of what is verified.

Not here, because tested rather than proved: the bit-level correctness of
SHA-1, SHA-256, SHA-512 and HMAC (FIPS 180-4 and RFC 2202/4231 vectors in
`tests/Props.lean`). No proof assumes HMAC is collision resistant: the
tampering slots conclude that a successful forgery exhibits a collision.
-/

namespace LeanItsdangerous

/-- base64url and the integer/timestamp encodings. -/
structure VerifiedEncoding where
  b64RoundTrip : Spec.B64RoundTrip
  base64DecodeRoundTrip : Spec.Base64DecodeRoundTrip
  intBytesRoundTrip : Spec.IntBytesRoundTrip
  timestampRoundTrip : Spec.TimestampRoundTrip
  b64AvoidsSep : Spec.B64AvoidsSep

theorem theVerifiedEncoding : VerifiedEncoding := {
  b64RoundTrip := b64decode_b64encode,
  base64DecodeRoundTrip := base64Decode_b64encode,
  intBytesRoundTrip := bytesToInt_intToBytes,
  timestampRoundTrip := decodeTimestamp_encodeTimestamp,
  b64AvoidsSep _ _ h := not_mem_sep_of_mem_b64encode h }

/-- `Signer`: round trip, key rotation, soundness, tampering. -/
structure VerifiedSigner where
  unsignSign : Spec.UnsignSign
  keyRotation : Spec.KeyRotation
  unsignSound : Spec.UnsignSound
  unsignTamperedValue : Spec.UnsignTamperedValue
  unsignTampered : Spec.UnsignTampered
  unsignTamperedSingle : Spec.UnsignTamperedSingle
  ctEqIsEq : Spec.CtEqIsEq

theorem theVerifiedSigner : VerifiedSigner := {
  unsignSign := Signer.unsign_sign,
  keyRotation s _ hk v := s.unsign_signWith hk v,
  unsignSound _ _ _ h := Signer.unsign_sound h,
  unsignTamperedValue := Signer.unsign_tampered_value,
  unsignTampered s _ v i b hlen hk r hr := s.unsign_tampered v i b hlen hk r hr,
  unsignTamperedSingle s _ hkeys v i hi b hb hlen :=
    s.unsign_tampered_single hkeys v i hi b hb hlen,
  ctEqIsEq := ctEq_iff }

/-- `TimestampSigner`: round trip with rotation, soundness, `max_age`. -/
structure VerifiedTimestampSigner where
  keyRotation : Spec.TimestampKeyRotation
  unsignSound : Spec.TimestampUnsignSound
  maxAgeMono : Spec.MaxAgeMono
  maxAgeExpired : Spec.MaxAgeExpired

theorem theVerifiedTimestampSigner : VerifiedTimestampSigner := {
  keyRotation t _ hk _ _ _ hage v := t.unsign_signWith hk hage v,
  unsignSound _ _ _ _ _ h := TimestampSigner.unsign_sound h,
  maxAgeMono t _ _ hm now input r h := t.unsign_maxAge_mono hm now input r h,
  maxAgeExpired t _ hk _ _ _ hold v := t.unsign_expired hk hold v }

/-- Serializers: round trips and soundness. -/
structure VerifiedSerializer where
  urlSafeRoundTrip : Spec.UrlSafeRoundTrip
  loadsDumps : Spec.LoadsDumps
  loadsSound : Spec.LoadsSound
  timedLoadsDumps : Spec.TimedLoadsDumps
  timedLoadsSound : Spec.TimedLoadsSound

theorem theVerifiedSerializer : VerifiedSerializer := {
  urlSafeRoundTrip _ c h := urlSafeCodec_roundTrip c h,
  loadsDumps _ s hc x salt := s.loads_dumps hc x salt,
  loadsSound _ _ _ _ _ h := Serializer.loads_sound h,
  timedLoadsDumps _ s hc x salt _ _ _ hage := s.loads_dumps hc x salt hage,
  timedLoadsSound _ _ _ _ _ _ _ h := TimedSerializer.loads_sound h }

end LeanItsdangerous
