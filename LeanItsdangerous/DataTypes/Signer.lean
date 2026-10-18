import LeanItsdangerous.DataTypes.Alphabet
import LeanItsdangerous.DataTypes.Errors
import LeanItsdangerous.DataTypes.Hash

/-!
# Signer and serializer configuration

The constructor checks upstream performs (`ValueError` on a separator that may
occur inside a signature; `IndexError` on signing with an empty key list) are
invariant fields here: a `Signer` value cannot hold a bad separator or an
empty key list.
-/

namespace LeanItsdangerous

/-- A usable separator: non-empty, and no byte of it is in upstream's
`_base64_alphabet`. Upstream rejects a separator only when it is a substring
of the alphabet; this is stricter for multi-byte separators that mix alphabet
and non-alphabet bytes (recorded as a deviation). It is exactly what makes the
split in `unsign` provably recover the signature. -/
def ValidSep (sep : Bytes) : Prop := sep ≠ [] ∧ ∀ c ∈ sep, isAlphabet c = false

instance (sep : Bytes) : Decidable (ValidSep sep) := by
  unfold ValidSep; exact inferInstance

/-- Everything about a signer except its keys and salt: what upstream's
`signer_kwargs` and `fallback_signers` entries configure. -/
structure SignerConfig where
  /-- `sep`, default `b"."`. -/
  sep : Bytes
  h_sep : ValidSep sep
  /-- `key_derivation`, default `django-concat`. -/
  keyDerivation : KeyDerivation
  /-- `digest_method`, default SHA-1. Used by key derivation, and by the
  default HMAC algorithm. -/
  digest : Hash
  /-- `algorithm`, default `HMACAlgorithm(digest_method)`. -/
  algorithm : SigningAlgorithm

/-- Upstream's `Signer`: a configuration plus the secret keys (oldest to
newest; the newest signs) and the salt. -/
structure Signer extends SignerConfig where
  /-- `secret_keys`, oldest first. -/
  secretKeys : List Bytes
  h_keys : secretKeys ≠ []
  /-- `salt`, default `b"itsdangerous.Signer"`. -/
  salt : Bytes

/-- Upstream's `TimestampSigner`: a `Signer` whose `sign` appends a timestamp
and whose `unsign` can check its age. -/
structure TimestampSigner where
  toSigner : Signer

/-- The `serializer` object upstream passes to a `Serializer`: a pair of
`dumps`/`loads`. Kept abstract so the JSON codec (lean-json) can be plugged
in by the caller. `loads` reports failure as a message, which becomes the
`original_error` of a `BadPayload`. -/
structure Codec (α : Type) where
  dumps : α → Bytes
  loads : Bytes → Except String α

/-- Upstream's `Serializer`. `salt = none` means the signer's own default
(`b"itsdangerous.Signer"`), as upstream's `salt=None` does. -/
structure Serializer (α : Type) where
  secretKeys : List Bytes
  h_keys : secretKeys ≠ []
  /-- default `some b"itsdangerous"` -/
  salt : Option Bytes
  codec : Codec α
  /-- the `signer_kwargs` of the main signer -/
  signer : SignerConfig
  /-- `fallback_signers`: each one is tried with each secret key after the
  main signer fails. -/
  fallbacks : List SignerConfig

/-- Upstream's `TimedSerializer`: a `Serializer` that signs with a
`TimestampSigner`. -/
structure TimedSerializer (α : Type) where
  toSerializer : Serializer α

end LeanItsdangerous

namespace LeanItsdangerous

/-- Upstream's default separator `b"."`. -/
def defaultSep : Bytes := [46]

theorem defaultSep_valid : ValidSep defaultSep := by decide

end LeanItsdangerous
