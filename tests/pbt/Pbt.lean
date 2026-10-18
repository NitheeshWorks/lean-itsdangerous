import LeanItsdangerous
import Plausible

/-!
# Plausible properties

Each `example` here is a randomised check, run at build time by the
`plausible` tactic: properties that are tested rather than proved (HMAC
behaviour), and restatements of theorems as smoke tests of the definitions
they are about.
-/

namespace Pbt

open LeanItsdangerous

/-- HMAC-SHA256 has a fixed output length. -/
example : ∀ (k m : List UInt8), (hmac sha256 k m).length = 32 := by plausible

/-- HMAC-SHA1 has no collision on sampled pairs (a smoke test; it cannot test a for-all). -/
example : ∀ (k m₁ m₂ : List UInt8), m₁ ≠ m₂ → hmac sha1 k m₁ ≠ hmac sha1 k m₂ := by plausible

/-- base64url round trip (proved as `b64decode_b64encode`). -/
example : ∀ (m : List UInt8), b64decode (b64encode m) = some m := by plausible

/-- Encoded length is `⌈4n/3⌉` (proved as `length_b64encode`). -/
example : ∀ (m : List UInt8), (b64encode m).length = (4 * m.length + 2) / 3 := by plausible

/-- Signing and unsigning with the default signer (proved as `unsign_sign`). -/
example : ∀ (k v : List UInt8),
    ((Signer.ofKey k).unsignImpl ((Signer.ofKey k).sign v)).toOption = some v := by plausible

/-- A different key does not verify. -/
example : ∀ (k₁ k₂ v : List UInt8), k₁ ≠ k₂ →
    (Signer.ofKey k₂).validate ((Signer.ofKey k₁).sign v) = false := by plausible

/-- Timestamp round trip (proved as `decodeTimestamp_encodeTimestamp`). -/
example : ∀ (n : Nat),
    TimestampSigner.decodeTimestamp (TimestampSigner.encodeTimestamp (UInt64.ofNat n)) =
      some (UInt64.ofNat n) := by plausible

end Pbt
