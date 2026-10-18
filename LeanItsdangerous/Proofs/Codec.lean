import LeanItsdangerous.Proofs.Encoding
import LeanItsdangerous.RepoImpl.Serializer

/-!
# Proofs: the codec law, once, and its instances

`Codec.Lawful.andThen` is the one round-trip proof; every encoding in a token
is built from two base codecs (`base64Codec`, `intCodec`) and that
combinator, so its round trip is an instance:

* `timestampCodec_lawful` gives `decodeTimestamp_encodeTimestamp`;
* `urlSafeCodec_lawful` gives the URL-safe serializers' payload round trip.
-/

namespace LeanItsdangerous

theorem Codec.Lawful.andThen {α : Type} {inner : Codec α} {outer : Codec Bytes}
    (hi : inner.Lawful) (ho : outer.Lawful) : (inner.andThen outer).Lawful := by
  intro a
  show (outer.loads (outer.dumps (inner.dumps a)) >>= inner.loads) = _
  rw [ho]; exact hi a

theorem bytesCodec_lawful : (inferInstance : Codec Bytes).Lawful := fun _ => rfl

theorem base64Codec_lawful : base64Codec.Lawful := by
  intro a
  show (match base64Decode (base64Encode a) with | some b => Except.ok b | none => Except.error _) = _
  rw [base64Decode_base64Encode]

theorem intCodec_lawful : intCodec.Lawful := by
  intro a
  show (match bytesToInt (intToBytes a) with | some n => Except.ok n | none => Except.error _) = _
  rw [bytesToInt_intToBytes]

theorem timestampCodec_lawful : timestampCodec.Lawful :=
  intCodec_lawful.andThen base64Codec_lawful

/-- The timestamp encode/decode round trip. -/
theorem decodeTimestamp_encodeTimestamp (ts : UInt64) :
    TimestampSigner.decodeTimestamp (TimestampSigner.encodeTimestamp ts) = some ts := by
  simp only [TimestampSigner.decodeTimestamp, TimestampSigner.encodeTimestamp,
    timestampCodec_lawful ts]; rfl

theorem base64Encode_ne_dot_cons (bs t : Bytes) : base64Encode bs ≠ 46 :: t := by
  intro h
  have := isAlphabet_of_mem_base64Encode (c := 46) (bs := bs) (by rw [h]; exact List.mem_cons_self)
  exact absurd this (by decide)

theorem urlSafeBase64_lawful : urlSafeBase64.Lawful := by
  intro a
  show urlSafeLoads (base64Encode a) = _
  unfold urlSafeLoads
  split
  · rename_i t ht; exact absurd ht (base64Encode_ne_dot_cons _ _)
  · rw [base64Decode_base64Encode]

/-- The URL-safe wrapping preserves the codec law. -/
theorem urlSafeCodec_lawful {α : Type} {c : Codec α} (h : c.Lawful) : (urlSafeCodec c).Lawful :=
  h.andThen urlSafeBase64_lawful

end LeanItsdangerous
