import LeanItsdangerous.DataTypes.Signer
import LeanItsdangerous.RepoImpl.Hash
import LeanItsdangerous.RepoImpl.Encoding

/-!
# Signer and TimestampSigner

Executable transcriptions of `itsdangerous/signer.py` and the
`TimestampSigner` half of `itsdangerous/timed.py`. The functions here return
plain results; `APIs/` wraps them in refinements using the theorems in
`Proofs/`.

Time is an input: upstream's `get_timestamp()` reads the wall clock, here the
caller passes `now` (seconds since the epoch), which keeps every function
pure.
-/

namespace LeanItsdangerous

/-- Upstream's largest timestamp `datetime.fromtimestamp(ts, tz=utc)`
accepts: 9999-12-31T23:59:59Z. Larger ones raise inside
`timestamp_to_datetime`, which upstream reports as `Malformed timestamp`. -/
def maxDatetimeTs : Nat := 253402300799

namespace Signer

/-- `derive_key(secret_key)`. -/
def deriveKey (s : Signer) (secretKey : Bytes) : Bytes :=
  match s.keyDerivation with
  | .concat => s.digest.digest (s.salt ++ secretKey)
  | .djangoConcat => s.digest.digest (s.salt ++ Bytes.ofString "signer" ++ secretKey)
  | .hmac => hmac s.digest secretKey s.salt
  | .none => secretKey

/-- The raw signature of `value` under one secret key. -/
def rawSignature (s : Signer) (secretKey value : Bytes) : Bytes :=
  s.algorithm.getSignature (s.deriveKey secretKey) value

/-- `get_signature`, for a chosen secret key: base64url of the raw signature. -/
def signatureFor (s : Signer) (secretKey value : Bytes) : Bytes :=
  b64encode (s.rawSignature secretKey value)

/-- `secret_key`: the newest (last) key, which signs. -/
def secretKey (s : Signer) : Bytes := s.secretKeys.getLast s.h_keys

/-- `get_signature(value)`, with the signing key. -/
def getSignature (s : Signer) (value : Bytes) : Bytes := s.signatureFor s.secretKey value

/-- Signing with a chosen key: `value + sep + signature`. -/
def signWith (s : Signer) (secretKey value : Bytes) : Bytes :=
  value ++ s.sep ++ s.signatureFor secretKey value

/-- `sign(value)`, with the newest key. -/
def sign (s : Signer) (value : Bytes) : Bytes := s.signWith s.secretKey value

/-- `verify_signature(value, sig)`: does any secret key produce exactly
`sig`? Upstream decodes `sig` and compares raw bytes; comparing the canonical
encoding instead is the same on every signature upstream produces, and
rejects the non-canonical spellings Python's lenient decoder would accept. -/
def verifySignature (s : Signer) (value sig : Bytes) : Bool :=
  s.secretKeys.reverse.any fun k => s.signatureFor k value == sig

/-- `unsign(signed_value)`. The public `Signer.unsign` (`APIs/`) is this,
refined with a proof of what an `ok` result means. -/
def unsignImpl (s : Signer) (signed : Bytes) : Except BadSignature Bytes :=
  match rsplit s.sep signed with
  | none => .error ⟨s!"No {s.sep} found in value", none⟩
  | some (value, sig) =>
    if s.verifySignature value sig then .ok value
    else .error ⟨s!"Signature {sig} does not match", some value⟩

/-- `validate(signed_value)`. -/
def validate (s : Signer) (signed : Bytes) : Bool :=
  match s.unsignImpl signed with
  | .ok _ => true
  | .error _ => false

end Signer

namespace TimestampSigner

/-- The encoded timestamp: `base64_encode(int_to_bytes(ts))`. -/
def encodeTimestamp (ts : UInt64) : Bytes := b64encode (intToBytes ts)

/-- The inverse: `bytes_to_int(base64_decode(ts_bytes))`. -/
def decodeTimestamp (b : Bytes) : Option UInt64 := (base64Decode b).bind bytesToInt

/-- `sign(value)` at time `now`: `value + sep + timestamp + sep + signature`. -/
def sign (t : TimestampSigner) (now : UInt64) (value : Bytes) : Bytes :=
  t.toSigner.sign (value ++ t.toSigner.sep ++ encodeTimestamp now)

/-- Signing with a chosen key, for the key rotation theorem. -/
def signWith (t : TimestampSigner) (secretKey : Bytes) (now : UInt64) (value : Bytes) : Bytes :=
  t.toSigner.signWith secretKey (value ++ t.toSigner.sep ++ encodeTimestamp now)

/-- The age check: `age = now - ts`; expired if `age > max_age` or `age < 0`.
`none` on success, else the error. -/
def checkAge (maxAge : Option Nat) (now : UInt64) (value : Bytes) (ts : UInt64) :
    Option BadData :=
  match maxAge with
  | none => none
  | some m =>
    let age : Int := (now.toNat : Int) - ts.toNat
    if age > m then
      some (.signatureExpired s!"Signature age {age} > {m} seconds" (some value) (some ts.toNat))
    else if age < 0 then
      some (.signatureExpired s!"Signature age {age} < 0 seconds" (some value) (some ts.toNat))
    else none

/-- Everything `unsign(signed_value, return_timestamp=True)` checks except
the age: the signature, then the timestamp's presence and form. The order of
the checks, and which error each failure produces, follows upstream exactly.
Independent of the current time. -/
def unsignCore (t : TimestampSigner) (signed : Bytes) : Except BadData (Bytes × UInt64) :=
  let s := t.toSigner
  let (result, sigError) : Bytes × Option BadSignature :=
    match s.unsignImpl signed with
    | .ok v => (v, none)
    | .error e => (e.payload.getD [], some e)
  match rsplit s.sep result with
  | none =>
    match sigError with
    | some e => .error e.toBadData
    | none => .error (.badTimeSignature "timestamp missing" (some result) none)
  | some (value, tsBytes) =>
    let tsInt := decodeTimestamp tsBytes
    match sigError with
    | some e =>
      match tsInt with
      | some ts =>
        if ts.toNat > maxDatetimeTs then
          .error (.badTimeSignature "Malformed timestamp" (some value) none)
        else .error (.badTimeSignature e.message (some value) (some ts.toNat))
      | none => .error (.badTimeSignature e.message (some value) none)
    | none =>
      match tsInt with
      | none => .error (.badTimeSignature "Malformed timestamp" (some value) none)
      | some ts => .ok (value, ts)

/-- `unsign(signed_value, max_age, return_timestamp=True)` at time `now`:
the value and its timestamp. Upstream checks the age last, after the
signature and the timestamp have been accepted; so does this. -/
def unsignImpl (t : TimestampSigner) (maxAge : Option Nat) (now : UInt64) (signed : Bytes) :
    Except BadData (Bytes × UInt64) :=
  match t.unsignCore signed with
  | .error e => .error e
  | .ok (value, ts) =>
    match checkAge maxAge now value ts with
    | some e => .error e
    | none => .ok (value, ts)

/-- `validate(signed_value, max_age)`. -/
def validate (t : TimestampSigner) (maxAge : Option Nat) (now : UInt64) (signed : Bytes) : Bool :=
  match t.unsignImpl maxAge now signed with
  | .ok _ => true
  | .error _ => false

end TimestampSigner

end LeanItsdangerous
