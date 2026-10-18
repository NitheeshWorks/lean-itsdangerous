import LeanItsdangerous.Proofs.Signer
import LeanItsdangerous.Proofs.Codec
import LeanItsdangerous.Specifications.Timed

/-!
# Proofs: TimestampSigner

* `unsignImpl_signWith` / `unsignImpl_sign`: sign at `ts`, unsign at `now` within
  `max_age`, get back the value and `ts`; for any key in the list.
* `unsignImpl_sound`: an `ok` result is a value signed by a key in the list,
  within the age bound.
* `unsignImpl_maxAge_mono`, `unsignImpl_none_of_some`: raising `max_age` (or dropping
  it) never turns a success into a failure.
* `unsignImpl_expired`, `unsignImpl_future`: a too-old or future timestamp raises
  `SignatureExpired` with the signing date.
-/

namespace LeanItsdangerous.TimestampSigner

theorem checkAge_eq_none_iff (maxAge : Option Nat) (now : UInt64) (value : Bytes) (ts : UInt64) :
    checkAge maxAge now value ts = none ↔ AgeOk maxAge now ts := by
  unfold checkAge AgeOk
  cases maxAge with
  | none => simp
  | some m =>
    simp only [Option.some.injEq, forall_eq']
    constructor
    · intro h
      by_cases h1 : (now.toNat : Int) - ts.toNat > m
      · simp [h1] at h
      · by_cases h2 : (now.toNat : Int) - ts.toNat < 0
        · simp [h1, h2] at h
        · omega
    · intro h
      have h1 : ¬ ((now.toNat : Int) - ts.toNat > m) := by omega
      have h2 : ¬ ((now.toNat : Int) - ts.toNat < 0) := by omega
      simp [h1, h2]

theorem encodeTimestamp_not_mem_sep (t : TimestampSigner) (ts : UInt64) :
    ∀ c ∈ encodeTimestamp ts, c ∉ t.toSigner.sep :=
  not_mem_sep_of_mem_base64Encode t.toSigner.h_sep

theorem unsignCore_signWith (t : TimestampSigner) {k : Bytes} (hk : k ∈ t.toSigner.secretKeys)
    (ts : UInt64) (v : Bytes) : t.unsignCore (t.signWith k v ts) = .ok (v, ts) := by
  simp only [unsignCore, signWith, t.toSigner.unsignImpl_signWith hk,
    rsplit_append t.toSigner.h_sep.1 (t.encodeTimestamp_not_mem_sep ts),
    decodeTimestamp_encodeTimestamp]

/-- Key rotation for timestamp signatures: signed by any key in the list at
`ts`, unsigned at `now` within `max_age`, the value and timestamp come back. -/
theorem unsignImpl_signWith (t : TimestampSigner) {k : Bytes} (hk : k ∈ t.toSigner.secretKeys)
    {maxAge : Option Nat} {now ts : UInt64} (hage : AgeOk maxAge now ts) (v : Bytes) :
    t.unsignImpl maxAge now (t.signWith k v ts) = .ok (v, ts) := by
  simp only [unsignImpl, t.unsignCore_signWith hk, (checkAge_eq_none_iff _ _ _ _).mpr hage]

theorem sign_eq_signWith (t : TimestampSigner) (ts : UInt64) (v : Bytes) :
    t.sign v ts = t.signWith t.toSigner.secretKey v ts := rfl

/-- The timestamp round trip through the signer. -/
theorem unsignImpl_sign (t : TimestampSigner) {maxAge : Option Nat} {now ts : UInt64}
    (hage : AgeOk maxAge now ts) (v : Bytes) :
    t.unsignImpl maxAge now (t.sign v ts) = .ok (v, ts) :=
  t.unsignImpl_signWith t.toSigner.secretKey_mem hage v

theorem unsignImpl_ok_iff (t : TimestampSigner) (maxAge : Option Nat) (now : UInt64)
    (input : Bytes) (r : Bytes × UInt64) :
    t.unsignImpl maxAge now input = .ok r ↔
      t.unsignCore input = .ok r ∧ AgeOk maxAge now r.2 := by
  unfold unsignImpl
  rw [← checkAge_eq_none_iff _ _ r.1]
  constructor
  · intro h
    split at h
    · cases h
    · rename_i value ts hc
      split at h
      · cases h
      · rename_i hn; cases h; exact ⟨hc, hn⟩
  · rintro ⟨hc, hn⟩
    rw [hc]; simp only; rw [hn]

theorem unsignCore_sound {t : TimestampSigner} {input : Bytes} {r : Bytes × UInt64}
    (h : t.unsignCore input = .ok r) : t.SignedBy input r.1 r.2 := by
  cases hu : t.toSigner.unsignImpl input with
  | error e =>
    simp only [unsignCore, hu] at h
    split at h
    · cases h
    · split at h
      · split at h <;> cases h
      · cases h
  | ok w =>
    simp only [unsignCore, hu] at h
    split at h
    · cases h
    · rename_i value tsb hsplit
      split at h
      · cases h
      · rename_i ts hts
        cases h
        obtain ⟨k, hk, hw⟩ := Signer.unsignImpl_sound hu
        refine ⟨k, hk, tsb, hts, ?_⟩
        rw [← rsplit_sound hsplit, hw]

/-- Soundness: an `ok (v, ts)` from `unsign` is `v` signed by a key in the
list at `ts`, and `ts` passes the age check. -/
theorem unsignImpl_sound {t : TimestampSigner} {maxAge : Option Nat} {now : UInt64} {input : Bytes}
    {r : Bytes × UInt64} (h : t.unsignImpl maxAge now input = .ok r) :
    t.SignedBy input r.1 r.2 ∧ AgeOk maxAge now r.2 := by
  obtain ⟨hc, ha⟩ := (t.unsignImpl_ok_iff _ _ _ _).mp h
  exact ⟨unsignCore_sound hc, ha⟩

/-- `max_age` monotonicity: a signature accepted with `max_age = m` is
accepted, with the same result, with any `m' ≥ m`. -/
theorem unsignImpl_maxAge_mono (t : TimestampSigner) {m m' : Nat} (hm : m ≤ m') (now : UInt64)
    (input : Bytes) (r : Bytes × UInt64) (h : t.unsignImpl (some m) now input = .ok r) :
    t.unsignImpl (some m') now input = .ok r := by
  obtain ⟨hc, ha⟩ := (t.unsignImpl_ok_iff _ _ _ _).mp h
  refine (t.unsignImpl_ok_iff _ _ _ _).mpr ⟨hc, ?_⟩
  intro m'' hm''
  cases hm''
  have := ha m rfl
  omega

/-- No `max_age` is the weakest check. -/
theorem unsignImpl_none_of_some (t : TimestampSigner) {m : Nat} (now now' : UInt64) (input : Bytes)
    (r : Bytes × UInt64) (h : t.unsignImpl (some m) now input = .ok r) :
    t.unsignImpl none now' input = .ok r := by
  obtain ⟨hc, _⟩ := (t.unsignImpl_ok_iff _ _ _ _).mp h
  exact (t.unsignImpl_ok_iff _ _ _ _).mpr ⟨hc, fun _ h => by cases h⟩

/-- A signature older than `max_age` raises `SignatureExpired`, carrying the
value and the signing time. -/
theorem unsignImpl_expired (t : TimestampSigner) {k : Bytes} (hk : k ∈ t.toSigner.secretKeys)
    {m : Nat} {now ts : UInt64} (hold : ts.toNat + m < now.toNat) (v : Bytes) :
    ∃ msg, t.unsignImpl (some m) now (t.signWith k v ts) =
      .error (.signatureExpired msg (some v) (some ts.toNat)) := by
  unfold unsignImpl
  rw [t.unsignCore_signWith hk]
  have h1 : (now.toNat : Int) - ts.toNat > m := by omega
  simp [checkAge, h1]

/-- A signature from the future raises `SignatureExpired` whenever an age is
checked. -/
theorem unsignImpl_future (t : TimestampSigner) {k : Bytes} (hk : k ∈ t.toSigner.secretKeys)
    {m : Nat} {now ts : UInt64} (hfut : now.toNat < ts.toNat) (v : Bytes) :
    ∃ msg, t.unsignImpl (some m) now (t.signWith k v ts) =
      .error (.signatureExpired msg (some v) (some ts.toNat)) := by
  unfold unsignImpl
  rw [t.unsignCore_signWith hk]
  have h1 : ¬ ((now.toNat : Int) - ts.toNat > m) := by omega
  have h2 : (now.toNat : Int) - ts.toNat < 0 := by omega
  simp [checkAge, h1, h2]

end LeanItsdangerous.TimestampSigner
