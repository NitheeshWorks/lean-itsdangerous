import LeanItsdangerous
open LeanItsdangerous

/-!
# Exceptions

Translates itsdangerous `docs/exceptions.rst` ("Exceptions"): `BadData`,
`BadSignature`, `BadTimeSignature`, `SignatureExpired`, `BadHeader`,
`BadPayload`.

Upstream raises; here the decoders return `Except`, and the hierarchy is the
inductive `BadData` with the `isinstance` tests as predicates
(`isBadSignature`, `isBadTimeSignature`, `isSignatureExpired`,
`isBadPayload`). The attributes are `message` (`str(e)`), `payload`,
`dateSigned` (seconds since the epoch).
-/

namespace Examples.Exceptions

def signer := Signer.new "secret-key"
def timed := TimestampSigner.new "secret-key"
def serializer := Serializer.new "secret-key"

/-- `BadSignature`: no separator. -/
def noSeparator := signer.unsign "no separator here"
#eval match noSeparator with
  | .error e => e.message | .ok _ => "accepted"
-- No b'.' found in value

/-- `BadTimeSignature`: a plain signature has no timestamp. -/
def timestampMissing := timed.unsign (signer.sign "value") (now := 1700000000)
#eval match timestampMissing with
  | .error e => s!"{e.isBadTimeSignature} {e.message} {e.dateSigned}" | .ok _ => "accepted"
-- true timestamp missing none

/-- `SignatureExpired` is a `BadTimeSignature` and a `BadSignature`, and
carries the payload and the signing date. -/
def expired := timed.unsign (timed.sign "value" 1700000000) (maxAge := 5) (now := 1700000015)
#eval match expired with
  | .error e => s!"{e.isSignatureExpired} {e.isBadTimeSignature} {e.isBadSignature} {e.payload} {e.dateSigned}"
  | .ok _ => "accepted"
-- true true true some b'value' some 1700000000

/-- `BadPayload`: a valid signature over a payload that does not load. Here
the payload is not UTF-8, so the `String` codec rejects it. -/
def badPayload := serializer.loads (serializer.makeSigner.sign [0xff, 0xfe])
#eval match badPayload with
  | .error e => s!"{e.isBadPayload} {e.message}" | .ok _ => "accepted"
-- true Could not load the payload because an exception occurred on unserializing the data.

/-- A separator that may occur in a signature is upstream's `ValueError`:
as a literal it does not compile (`Signer.new "k" (sep := "-")` fails its
`by decide`), and at run time `checkSeparator` reports it. -/
def badSeparator := checkSeparator "-"
#eval match badSeparator with
  | .error m => m | .ok _ => "accepted"

end Examples.Exceptions
