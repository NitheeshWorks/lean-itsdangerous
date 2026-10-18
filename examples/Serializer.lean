import LeanItsdangerous
open LeanItsdangerous

/-!
# Serialization Interface

Translates itsdangerous `docs/serializer.rst` ("Serialization Interface",
"Responding to Failure", "Fallback Signers").

Upstream's default serializer is Python's `json`; here the payload type picks
its codec, and the default is `String`: JSON text as `json.dumps` writes it.
lean-json's `Json` plugs in the same way (lean-starlette does this).
-/

namespace Examples.Serializer

/-! ## dumps and loads

```python
from itsdangerous.serializer import Serializer
s = Serializer("secret-key")
s.dumps([1, 2, 3, 4])           # '[1, 2, 3, 4].r7R9RhGgDPvvWl3iNzLuIIfELmo'
s.loads('[1, 2, 3, 4].r7R9RhGgDPvvWl3iNzLuIIfELmo')   # [1, 2, 3, 4]
```
-/

def s := Serializer.new "secret-key"

def token := s.dumps "[1, 2, 3, 4]"
#eval token                    -- b'[1, 2, 3, 4].r7R9RhGgDPvvWl3iNzLuIIfELmo'

def loaded := s.loads "[1, 2, 3, 4].r7R9RhGgDPvvWl3iNzLuIIfELmo"
#eval loaded                   -- Except.ok "[1, 2, 3, 4]"

/-! ## Responding to failure

```python
s = URLSafeSerializer("secret-key")
decoded_payload = None
try:
    decoded_payload = s.loads(data)
except BadSignature as e:
    if e.payload is not None:
        try:
            decoded_payload = s.load_payload(e.payload)
        except BadData:
            pass
sig_okay, payload = s.loads_unsafe(data)
```
-/

def u := URLSafeSerializer.new "secret-key"

/-- A token whose last signature character was changed. -/
def data : Bytes := "eyJpZCI6NX0.Miy6DmCsMs_TuHx_Rl2OXEaAyKA"

/-- The payload is still available, decoded but unsafe. -/
def decodedPayload : Option String :=
  match u.loads data with
  | .ok v => some v
  | .error e =>
    if e.isBadSignature then
      match e.payload with
      | some p => (u.loadPayload p).toOption
      | none => none
    else none
#eval decodedPayload           -- some "{\"id\":5}"

/-- Or, without inspecting the exception: `(signature_valid, payload)`. -/
def unsafeResult := u.loadsUnsafe data
#eval unsafeResult             -- Except.ok (false, some "{\"id\":5}")

/-! ## Fallback signers

```python
s = Serializer(
    "secret-key",
    signer_kwargs={"digest_method": hashlib.sha512},
    fallback_signers=[{"digest_method": hashlib.sha1}]
)
```
Signs with SHA-512, but still accepts tokens signed with SHA-1.
-/

def upgraded := Serializer.new "secret-key"
  (signerKwargs := { digestMethod := sha512 })
  (fallbackSigners := [{ digestMethod := sha1 }])

def newToken := upgraded.dumps "[1, 2, 3, 4]"
#eval newToken                 -- SHA-512 signature

def oldTokenLoads := upgraded.loads token
#eval oldTokenLoads            -- Except.ok "[1, 2, 3, 4]"

end Examples.Serializer
