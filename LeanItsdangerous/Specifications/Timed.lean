import LeanItsdangerous.RepoImpl.Signer

/-!
# Specifications: the predicates the timestamp results are refined by
-/

namespace LeanItsdangerous.TimestampSigner

/-- The age condition `unsign` enforces: with `max_age = m`, the timestamp
is not in the future and at most `m` seconds old. -/
def AgeOk (maxAge : Option Nat) (now ts : UInt64) : Prop :=
  ∀ m, maxAge = some m → ts.toNat ≤ now.toNat ∧ now.toNat - ts.toNat ≤ m

instance (maxAge : Option Nat) (now ts : UInt64) : Decidable (AgeOk maxAge now ts) :=
  match maxAge with
  | none => isTrue (fun _ h => by cases h)
  | some m =>
    if h : ts.toNat ≤ now.toNat ∧ now.toNat - ts.toNat ≤ m then
      isTrue (fun m' hm => by cases hm; exact h)
    else isFalse (fun hall => h (hall m rfl))

/-- `input` is `value ++ sep ++ tsb`, signed by a key in the list, where
`tsb` is an encoding of the timestamp `ts`. (Not necessarily *the* canonical
encoding: like upstream, a timestamp with leading zero bytes or `=` padding is
accepted, so this is the strongest statement that holds.) -/
def SignedBy (t : TimestampSigner) (input value : Bytes) (ts : UInt64) : Prop :=
  ∃ k ∈ t.toSigner.secretKeys, ∃ tsb, decodeTimestamp tsb = some ts ∧
    t.toSigner.signWith k (value ++ t.toSigner.sep ++ tsb) = input

end LeanItsdangerous.TimestampSigner
