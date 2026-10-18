import LeanItsdangerous.DataTypes.Bytes

/-!
# Codecs

A codec is an encoder to bytes and a decoder that may fail with a message:
the shape of upstream's `serializer` objects (`dumps`/`loads`), and of every
encoding inside a signed token (base64url, the integer timestamp, the
URL-safe payload). It is a class, so a serializer finds the payload codec by
type, as upstream's default `json` is found by default.

A codec is **lawful** when decoding inverts encoding. The law is proved once
for the combinator `Codec.andThen` (`Proofs/Codec.lean`), and each encoding in
this library is an instance. The tokens are delimited by a separator rather
than self-delimiting, so the law is the whole-buffer form; the separator
split is proved separately (`rsplit_append`).
-/

namespace LeanItsdangerous

/-- An encoder/decoder pair. -/
class Codec (α : Type) where
  dumps : α → Bytes
  loads : Bytes → Except String α

/-- The codec law: `loads (dumps a) = .ok a`. -/
def Codec.Lawful {α : Type} (c : Codec α) : Prop := ∀ a, c.loads (c.dumps a) = .ok a

/-- Encode with `inner`, then encode those bytes with `outer`; decode in the
reverse order. -/
@[instance_reducible] def Codec.andThen {α : Type} (inner : Codec α) (outer : Codec Bytes) : Codec α where
  dumps a := outer.dumps (inner.dumps a)
  loads b := outer.loads b >>= inner.loads

/-- Bytes as their own payload (upstream with a `bytes` serializer). -/
instance : Codec Bytes := ⟨id, .ok⟩

/-- UTF-8 text as the payload: for JSON (or any text) the caller has already
rendered. It is the default instance, as `json` is upstream's default
serializer, so `URLSafeSerializer.new "secret-key"` needs no type ascription.
A `Json` codec comes from lean-json. -/
@[default_instance] instance : Codec String where
  dumps := Bytes.ofString
  loads b := match b.toString? with
    | some s => .ok s
    | none => .error "invalid utf-8"

/-- The payload codec the URL-safe serializers use by default: upstream's
`_CompactJSON` (no spaces), where the plain serializers use `json.dumps`'s
default separators. Without a specific instance it is the type's `Codec`. -/
class CompactCodec (α : Type) where
  codec : Codec α

instance (priority := low) {α : Type} [c : Codec α] : CompactCodec α := ⟨c⟩

/-- Text payloads are the same either way; the default instance, as for
`Codec`. -/
@[default_instance] instance : CompactCodec String := ⟨inferInstance⟩

end LeanItsdangerous
