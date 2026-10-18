import LeanItsdangerous.DataTypes.Bytes

/-!
# Hash functions, signing algorithms, key derivation

Upstream passes a `hashlib` constructor as `digest_method` and a
`SigningAlgorithm` object as `algorithm`. Here both are plain structures of
functions. A `Hash` carries its fixed output length as an invariant
(`h_len`), which the tampering theorem uses: every signature under a given
digest has the same length.
-/

namespace LeanItsdangerous

/-- A hash function with a fixed block size and output size, as HMAC needs. -/
structure Hash where
  name : String
  /-- Block size in bytes (64 for SHA-1/SHA-256, 128 for SHA-512). -/
  blockSize : Nat
  /-- Output size in bytes. -/
  digestSize : Nat
  digest : Bytes → Bytes
  /-- Every output has exactly `digestSize` bytes. -/
  h_len : ∀ m, (digest m).length = digestSize

/-- Upstream's `SigningAlgorithm`: computes the raw signature of a value under
an (already derived) key. Verification compares signatures for equality. -/
structure SigningAlgorithm where
  name : String
  getSignature : (key : Bytes) → (value : Bytes) → Bytes

/-- Upstream's `key_derivation` strings. An unknown string raises `TypeError`
upstream at the first `derive_key`; here it is unrepresentable. -/
inductive KeyDerivation where
  /-- `digest(salt + secret_key)` -/
  | concat
  /-- `digest(salt + b"signer" + secret_key)`, the default. -/
  | djangoConcat
  /-- `HMAC(secret_key, salt)` -/
  | hmac
  /-- the secret key itself -/
  | none
  deriving Repr, DecidableEq, Inhabited

end LeanItsdangerous
