import ItsdangerousJson
open LeanItsdangerous LeanJson

/-!
# General Concepts

Port of itsdangerous `docs/concepts.rst` ("The Secret Key", "The Salt",
"Key Rotation"), block by block.
-/

namespace Examples.Concepts

/-! Block 1 ("The Secret Key"):
```python
import os
from itsdangerous.serializer import Serializer
SECRET_KEY = os.environ.get("SECRET_KEY")
s = Serializer(SECRET_KEY)
```
-/

def fromEnvironment : IO (Serializer Json) := do
  let some secretKey ← IO.getEnv "SECRET_KEY"
    | throw (IO.userError "SECRET_KEY is not set")
  return Serializer.new secretKey

/-! Block 2 ("The Salt"):
```python
from itsdangerous.url_safe import URLSafeSerializer

s1 = URLSafeSerializer("secret-key", salt="activate")
s1.dumps(42)
'NDI.MHQqszw6Wc81wOBQszCrEE_RlzY'

s2 = URLSafeSerializer("secret-key", salt="upgrade")
s2.dumps(42)
'NDI.c0MpsD6gzpilOAeUPra3NShPXsE'
```
-/

def s1 := URLSafeSerializer.new "secret-key" (salt := "activate")
def activate := s1.dumps (json% 42)
#eval activate                  -- b'NDI.MHQqszw6Wc81wOBQszCrEE_RlzY'

def s2 := URLSafeSerializer.new "secret-key" (salt := "upgrade")
def upgrade := s2.dumps (json% 42)
#eval upgrade                   -- b'NDI.c0MpsD6gzpilOAeUPra3NShPXsE'

/-! Block 3:
```python
s2.loads(s1.dumps(42))
Traceback (most recent call last):
  ...
BadSignature: Signature does not match
```
-/

def crossSalt := s2.loads (s1.dumps (json% 42))
#eval crossSalt
-- Except.error BadSignature: Signature b'MHQqszw6Wc81wOBQszCrEE_RlzY' does not match

/-! Block 4:
```python
s2.loads(s2.dumps(42))
42
```
-/

def sameSalt := s2.loads (s2.dumps (json% 42))
#eval sameSalt                  -- Except.ok json% 42

/-! Block 5 ("Key Rotation"):
```python
SECRET_KEYS = ["2b9cd98e", "169d7886", "b6af09f5"]

# sign some data with the latest key
s = Serializer(SECRET_KEYS)
t = s.dumps({"id": 42})

# rotate a new key in and the oldest key out
SECRET_KEYS.append("cf9b3588")
del SECRET_KEYS[0]

s = Serializer(SECRET_KEYS)
s.loads(t)  # valid even though it was signed with a previous key
```
-/

def secretKeys := ["2b9cd98e", "169d7886", "b6af09f5"]
def t := (Serializer.new secretKeys).dumps (json% {"id": 42})
#eval t                         -- b'{"id": 42}.vPnMXi_7YWhvSPnrl9Bcf1-2I44'

def rotatedKeys := (secretKeys ++ ["cf9b3588"]).drop 1
def stillValid := (Serializer.new rotatedKeys).loads t
#eval stillValid                -- Except.ok json% {"id": 42}

end Examples.Concepts
