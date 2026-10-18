import ItsdangerousJson
open LeanItsdangerous LeanJson

/-!
# Serialization Interface

Port of itsdangerous `docs/serializer.rst` ("Serialization Interface",
"Responding to Failure", "Fallback Signers"), block by block, with real JSON
values (lean-json's `json%`).
-/

namespace Examples.Serializer

/-! Block 1:
```python
from itsdangerous.serializer import Serializer
s = Serializer("secret-key")
s.dumps([1, 2, 3, 4])
b'[1, 2, 3, 4].r7R9RhGgDPvvWl3iNzLuIIfELmo'
```
-/

def s := Serializer.new "secret-key"
def token := s.dumps (json% [1, 2, 3, 4])
#eval token                     -- b'[1, 2, 3, 4].r7R9RhGgDPvvWl3iNzLuIIfELmo'

/-! Block 2:
```python
s.loads('[1, 2, 3, 4].r7R9RhGgDPvvWl3iNzLuIIfELmo')
[1, 2, 3, 4]
```
-/

def loaded := s.loads "[1, 2, 3, 4].r7R9RhGgDPvvWl3iNzLuIIfELmo"
#eval loaded                    -- Except.ok json% [1, 2, 3, 4]

/-! Block 3 ("Responding to Failure"). The page leaves `data` undefined;
here it is a token whose signature was changed.
```python
from itsdangerous.serializer import Serializer
from itsdangerous.exc import BadSignature, BadData

s = URLSafeSerializer("secret-key")
decoded_payload = None

try:
    decoded_payload = s.loads(data)
    # This payload is decoded and safe
except BadSignature as e:
    if e.payload is not None:
        try:
            decoded_payload = s.load_payload(e.payload)
        except BadData:
            pass
        # This payload is decoded but unsafe because someone
        # tampered with the signature.
```
-/

def u := URLSafeSerializer.new "secret-key"
def data : Bytes := "eyJpZCI6NX0.Miy6DmCsMs_TuHx_Rl2OXEaAyKA"

def decodedPayload : Option Json :=
  match u.loads data with
  | .ok v => some v               -- decoded and safe
  | .error e =>
    if e.isBadSignature then
      match e.payload with
      | some p => (u.loadPayload p).toOption   -- decoded but unsafe
      | none => none
    else none
#eval decodedPayload            -- some json% {"id": 5}

/-! Block 4:
```python
sig_okay, payload = s.loads_unsafe(data)
```
-/

def unsafeResult := u.loadsUnsafe data
#eval unsafeResult              -- Except.ok (false, some json% {"id": 5})

/-! Block 5 ("Fallback Signers"). The page omits the secret key; it is
`"secret-key"` here.
```python
s = Serializer(
    signer_kwargs={"digest_method": hashlib.sha512},
    fallback_signers=[{"digest_method": hashlib.sha1}]
)
```
Signs with SHA-512, still accepts SHA-1 tokens such as block 1's.
-/

def upgraded := Serializer.new "secret-key"
  (signerKwargs := { digestMethod := sha512 })
  (fallbackSigners := [{ digestMethod := sha1 }])
def newToken := upgraded.dumps (json% [1, 2, 3, 4])
#eval newToken
def oldTokenLoads := upgraded.loads token
#eval oldTokenLoads             -- Except.ok json% [1, 2, 3, 4]

end Examples.Serializer
