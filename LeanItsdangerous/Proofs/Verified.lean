import LeanItsdangerous.Proofs.Public
import LeanItsdangerous.Proofs.Bytes
import LeanItsdangerous.Specifications.Spec

/-!
# The harness: one `Verified<Layer>` structure per layer

Each `Verified<Layer>` has a field per headline property of
`Specifications/Spec.lean` for that layer, and `theVerified<Layer>` fills
every field with the theorem that proves it. A specification with no proof is
a compile error the moment it needs a field here. If a stated specification
turned out false, its slot's type would flip to a refutation rather than
being dropped, so this file stays an honest map of what is verified.

Not here, because tested rather than proved: the bit-level correctness of
SHA-1, SHA-256, SHA-512 and HMAC (FIPS 180-4 and RFC 2202/4231 vectors in
`tests/Props.lean`). No proof assumes HMAC is collision resistant: the
tampering slots conclude that a successful forgery exhibits a collision.

Not here, because it is the type: the soundness of `unsign` and `loads`,
which their refined return types carry.
-/

namespace LeanItsdangerous

/-- The codec theory and the encodings built from it. -/
structure VerifiedCodec : Prop where
  lawfulAndThen : Spec.LawfulAndThen
  encodingsLawful : Spec.EncodingsLawful
  urlSafeLawful : Spec.UrlSafeLawful
  base64RoundTrip : Spec.Base64RoundTrip
  ofStringEqToUTF8 : Spec.OfStringEqToUTF8

theorem theVerifiedCodec : VerifiedCodec where
  lawfulAndThen _ _ _ hi ho := hi.andThen ho
  encodingsLawful := ⟨base64Codec_lawful, intCodec_lawful, timestampCodec_lawful⟩
  urlSafeLawful _ _ h := urlSafeCodec_lawful h
  base64RoundTrip := base64Decode_base64Encode
  ofStringEqToUTF8 := Bytes.ofString_eq_toUTF8

/-- `Signer`: round trip, key rotation, characterisation, tampering. -/
structure VerifiedSigner : Prop where
  unsignSign : Spec.UnsignSign
  keyRotation : Spec.KeyRotation
  unsignEqOkIff : Spec.UnsignEqOkIff
  unsignTamperedValue : Spec.UnsignTamperedValue
  unsignTampered : Spec.UnsignTampered
  unsignTamperedSingle : Spec.UnsignTamperedSingle
  ctEqIff : Spec.CtEqIff

theorem theVerifiedSigner : VerifiedSigner where
  unsignSign := Signer.unsign_sign
  keyRotation s _ hk v := s.unsign_signWith hk v
  unsignEqOkIff := Signer.unsign_eq_ok_iff
  unsignTamperedValue := Signer.unsign_tampered_value
  unsignTampered s _ hk v i b hlen r hr := s.unsign_tampered hk v i b hlen r hr
  unsignTamperedSingle s _ hkeys v i hi b hb hlen := s.unsign_tampered_single hkeys v i hi b hb hlen
  ctEqIff := ctEq_iff

/-- `TimestampSigner`: round trip with rotation, `max_age`. -/
structure VerifiedTimestampSigner : Prop where
  unsignSign : Spec.TimestampUnsignSign
  maxAgeMono : Spec.MaxAgeMono
  maxAgeExpired : Spec.MaxAgeExpired

theorem theVerifiedTimestampSigner : VerifiedTimestampSigner where
  unsignSign t _ hk _ _ _ hage v := t.unsign_signWith hk hage v
  maxAgeMono t _ _ hm _ _ _ h := t.unsign_maxAge_mono hm h
  maxAgeExpired t _ hk _ _ _ hold v := t.unsign_expired hk hold v

/-- Serializers: round trips. -/
structure VerifiedSerializer : Prop where
  loadsDumps : Spec.LoadsDumps
  timedLoadsDumps : Spec.TimedLoadsDumps

theorem theVerifiedSerializer : VerifiedSerializer where
  loadsDumps _ s hc x salt := s.loads_dumps hc x salt
  timedLoadsDumps _ s hc x salt _ _ _ hage := s.loads_dumps hc x salt hage

end LeanItsdangerous
