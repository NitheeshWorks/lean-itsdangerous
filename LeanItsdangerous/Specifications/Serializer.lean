import LeanItsdangerous.RepoImpl.Serializer
import LeanItsdangerous.Specifications.Timed

/-!
# Specifications: codecs and serializer results
-/

namespace LeanItsdangerous

/-- A codec whose `loads` inverts `dumps`: the hypothesis every serializer
round trip needs of the caller's payload format. -/
def Codec.RoundTrip {α : Type} (c : Codec α) : Prop := ∀ x, c.loads (c.dumps x) = .ok x

/-- `input` is a payload `p` signed by one of the serializer's unsigners
(with one of its keys), and the payload loads to `x`. -/
def Serializer.SignedBy {α : Type} (s : Serializer α) (salt : Option Bytes) (input : Bytes)
    (x : α) : Prop :=
  ∃ u ∈ s.unsigners salt, ∃ k ∈ u.secretKeys, ∃ p, u.signWith k p = input ∧ s.codec.loads p = .ok x

/-- The timed analogue: a payload signed at `ts` by one of the unsigners,
loading to `x`, with `ts` within the age bound. -/
def TimedSerializer.SignedBy {α : Type} (s : TimedSerializer α) (salt : Option Bytes)
    (maxAge : Option Nat) (now : UInt64) (input : Bytes) (x : α) (ts : UInt64) : Prop :=
  ∃ u ∈ s.toSerializer.unsigners salt, ∃ p, (TimestampSigner.mk u).SignedBy input p ts ∧
    TimestampSigner.AgeOk maxAge now ts ∧ s.toSerializer.codec.loads p = .ok x

end LeanItsdangerous
