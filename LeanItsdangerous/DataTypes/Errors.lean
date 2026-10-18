import LeanItsdangerous.DataTypes.Bytes
import LeanItsdangerous.DataTypes.DateTime

/-!
# The exception hierarchy

Upstream (`itsdangerous/exc.py`) has

```
BadData
├── BadSignature            (payload)
│   ├── BadTimeSignature    (payload, date_signed)
│   │   └── SignatureExpired
│   └── BadHeader           (payload, header, original_error)
└── BadPayload              (original_error)
```

Lean has no subclassing, so the hierarchy is one inductive with a
constructor per class, and the `isinstance` checks are the Boolean
predicates `isBadSignature` and `isBadTimeSignature`. `Signer.unsign` can
only raise `BadSignature` itself, so it gets the narrower structure
`BadSignature`, which embeds into `BadData`.

`date_signed` is upstream's aware UTC `datetime`; here a `DateTime`, which
prints as Python prints a `datetime`.
-/

namespace LeanItsdangerous

/-- Every error this library raises. -/
inductive BadData where
  /-- Plain `BadData`, e.g. invalid base64 from `base64_decode`. -/
  | badData (message : String)
  /-- `BadSignature`: the signature did not match. -/
  | badSignature (message : String) (payload : Option Bytes)
  /-- `BadTimeSignature`: a time-based signature is invalid. -/
  | badTimeSignature (message : String) (payload : Option Bytes) (dateSigned : Option DateTime)
  /-- `SignatureExpired`: the timestamp is older than `max_age` (or in the future). -/
  | signatureExpired (message : String) (payload : Option Bytes) (dateSigned : Option DateTime)
  /-- `BadHeader`: a signed header is invalid. Kept for the hierarchy; no
  current upstream code path raises it. -/
  | badHeader (message : String) (payload : Option Bytes) (header : Option Bytes)
      (originalError : Option String)
  /-- `BadPayload`: the payload could not be loaded. -/
  | badPayload (message : String) (originalError : Option String)
  deriving DecidableEq, Inhabited

namespace BadData

/-- `str(exc)`. -/
def message : BadData → String
  | badData m | badSignature m _ | badTimeSignature m _ _ | signatureExpired m _ _
  | badHeader m _ _ _ | badPayload m _ => m

/-- The `payload` attribute, for the `BadSignature` family. -/
def payload : BadData → Option Bytes
  | badSignature _ p | badTimeSignature _ p _ | signatureExpired _ p _ | badHeader _ p _ _ => p
  | _ => none

/-- The `date_signed` attribute, for the `BadTimeSignature` family. -/
def dateSigned : BadData → Option DateTime
  | badTimeSignature _ _ d | signatureExpired _ _ d => d
  | _ => none

/-- The upstream class name. -/
def className : BadData → String
  | badData .. => "BadData" | badSignature .. => "BadSignature"
  | badTimeSignature .. => "BadTimeSignature" | signatureExpired .. => "SignatureExpired"
  | badHeader .. => "BadHeader" | badPayload .. => "BadPayload"

/-- As the last line of upstream's traceback: `SignatureExpired: Signature age 15 > 5 seconds`. -/
instance : ToString BadData := ⟨fun e => s!"{e.className}: {e.message}"⟩
instance : Repr BadData := ⟨fun e _ => .text (toString e)⟩

/-- `isinstance(e, BadSignature)`. -/
def isBadSignature : BadData → Bool
  | badSignature .. | badTimeSignature .. | signatureExpired .. | badHeader .. => true
  | _ => false

/-- `isinstance(e, BadTimeSignature)`. -/
def isBadTimeSignature : BadData → Bool
  | badTimeSignature .. | signatureExpired .. => true
  | _ => false

/-- `isinstance(e, SignatureExpired)`. -/
def isSignatureExpired : BadData → Bool
  | signatureExpired .. => true
  | _ => false

/-- `isinstance(e, BadPayload)`. -/
def isBadPayload : BadData → Bool
  | badPayload .. => true
  | _ => false

end BadData

/-- The error `Signer.unsign` raises: a `BadSignature` and nothing else. -/
structure BadSignature where
  message : String
  payload : Option Bytes
  deriving DecidableEq, Inhabited

/-- As the last line of upstream's traceback: `BadSignature: Signature ... does not match`. -/
instance : ToString BadSignature := ⟨fun e => s!"BadSignature: {e.message}"⟩
instance : Repr BadSignature := ⟨fun e _ => .text (toString e)⟩

/-- `BadSignature` is a `BadData`. -/
def BadSignature.toBadData (e : BadSignature) : BadData := .badSignature e.message e.payload

instance : Coe BadSignature BadData := ⟨BadSignature.toBadData⟩

end LeanItsdangerous
