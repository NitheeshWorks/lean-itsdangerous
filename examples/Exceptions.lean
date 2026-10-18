import LeanItsdangerous
open LeanItsdangerous

/-!
# Exceptions

Port of itsdangerous `docs/exceptions.rst` ("Exceptions"). The page
documents the exception classes and their attributes (from
`src/itsdangerous/exc.py`) and has no code block of its own, so this file
shows each documented attribute on the error upstream raises:
`BadSignature.payload`, `BadTimeSignature.date_signed`,
`SignatureExpired.date_signed`, `BadPayload.original_error`.

Upstream raises; here the decoders return `Except`, the hierarchy is the
inductive `BadData`, and `isinstance` is `isBadSignature`,
`isBadTimeSignature`, `isSignatureExpired`, `isBadPayload`.
-/

namespace Examples.Exceptions

def signer := Signer.new "secret-key"
def timed := TimestampSigner.new "secret-key"

/-- `BadSignature.payload`: the value that failed the check. -/
def badSignature := signer.unsign "my string.AAAAAAAAAAAAAAAAAAAAAAAAAAA"
#eval match badSignature with
  | .error e => s!"{e.message}; payload = {e.payload}" | .ok _ => "accepted"
-- Signature b'AAAAAAAAAAAAAAAAAAAAAAAAAAA' does not match; payload = (some b'my string')

/-- `BadTimeSignature.date_signed` is `None` when there is no timestamp. -/
def timestampMissing := timed.unsign (signer.sign "value") (now := 1700000000)
#eval match timestampMissing with
  | .error e => s!"{e.isBadTimeSignature} {e.message} {repr e.dateSigned}" | .ok _ => "accepted"
-- true timestamp missing none

/-- `SignatureExpired` is a `BadTimeSignature` and a `BadSignature`;
`date_signed` is when it was signed. -/
def expired := timed.unsign (timed.sign "value" 1700000000) (maxAge := 5) (now := 1700000015)
#eval match expired with
  | .error e => s!"{e.isSignatureExpired} {e.isBadTimeSignature} {e.isBadSignature} {e.dateSigned}"
  | .ok _ => "accepted"
-- true true true (some 2023-11-14 22:13:20+00:00)

/-- `BadPayload.original_error`: a valid signature over a payload that does
not load (here, not UTF-8). -/
def serializer := Serializer.new "secret-key"
def badPayload := serializer.loads (serializer.makeSigner.sign [0xff, 0xfe])
#eval match badPayload with
  | .error (.badPayload m e) => s!"{m} original_error = {e}" | _ => "accepted"
-- Could not load the payload because an exception occurred on unserializing the data. original_error = (some invalid utf-8)

end Examples.Exceptions
