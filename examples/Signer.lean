import LeanItsdangerous
open LeanItsdangerous

/-!
# Signing Interface

Translates itsdangerous `docs/signer.rst` ("Signing Interface").

```python
from itsdangerous import Signer
s = Signer("secret-key")
s.sign("my string")                                  # b'my string.wh6tMHxLgJqB6oY1uT73iMlyrOA'
s.unsign(b"my string.wh6tMHxLgJqB6oY1uT73iMlyrOA")   # b'my string'
s.unsign(b"different string.wh6tMHxLgJqB6oY1uT73iMlyrOA")   # BadSignature
```
-/

namespace Examples.Signer

def s := Signer.new "secret-key"

/-- The signature is appended to the string, separated by a dot. -/
def signed := s.sign "my string"
#eval signed                    -- b'my string.wh6tMHxLgJqB6oY1uT73iMlyrOA'

/-- To validate the string, use `unsign`. -/
def unsigned := s.unsign "my string.wh6tMHxLgJqB6oY1uT73iMlyrOA"
#eval unsigned                  -- Except.ok b'my string'

/-- If the value is changed, the signature no longer matches. -/
def tampered := s.unsign "different string.wh6tMHxLgJqB6oY1uT73iMlyrOA"
#eval match tampered with
  | .ok _ => "accepted"
  | .error e => s!"BadSignature: {e.message}"
-- BadSignature: Signature b'wh6tMHxLgJqB6oY1uT73iMlyrOA' does not match

-- Text is encoded as UTF-8 implicitly, as upstream does.
#eval s.sign "mañana" == s.sign (Bytes.ofString "mañana")   -- true

/-- The signing algorithms: `NoneAlgorithm` and `HMACAlgorithm`. -/
def unsignedSigner := Signer.new "secret-key" (algorithm := some noneAlgorithm)
#eval unsignedSigner.sign "my string"       -- b'my string.'
def sha256Signer := Signer.new "secret-key" (digestMethod := sha256)
#eval sha256Signer.sign "my string"

end Examples.Signer
