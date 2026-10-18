import LeanItsdangerous
open LeanItsdangerous

/-!
# Signing Interface

Port of itsdangerous `docs/signer.rst` ("Signing Interface"), block by block.
-/

namespace Examples.Signer

/-! Block 1:
```python
from itsdangerous import Signer
s = Signer("secret-key")
s.sign("my string")
b'my string.wh6tMHxLgJqB6oY1uT73iMlyrOA'
```
-/

def s := Signer.new "secret-key"
def signed := s.sign "my string"
#eval signed                    -- b'my string.wh6tMHxLgJqB6oY1uT73iMlyrOA'

/-! Block 2:
```python
s.unsign(b"my string.wh6tMHxLgJqB6oY1uT73iMlyrOA")
b'my string'
```
-/

def unsigned := s.unsign "my string.wh6tMHxLgJqB6oY1uT73iMlyrOA"
#eval unsigned                  -- Except.ok b'my string'

/-! Block 3:
```python
s.unsign(b"different string.wh6tMHxLgJqB6oY1uT73iMlyrOA")
Traceback (most recent call last):
  ...
BadSignature: Signature does not match
```
-/

def tampered := s.unsign "different string.wh6tMHxLgJqB6oY1uT73iMlyrOA"
#eval tampered
-- Except.error BadSignature: Signature b'wh6tMHxLgJqB6oY1uT73iMlyrOA' does not match

end Examples.Signer
