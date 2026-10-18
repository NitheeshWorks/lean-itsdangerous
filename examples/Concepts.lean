import LeanItsdangerous
open LeanItsdangerous

/-!
# General Concepts: the salt and key rotation

Translates itsdangerous `docs/concepts.rst` ("The Salt", "Key Rotation").
-/

namespace Examples.Concepts

/-! ## The salt

```python
s1 = URLSafeSerializer("secret-key", salt="activate")
s1.dumps(42)                    # 'NDI.MHQqszw6Wc81wOBQszCrEE_RlzY'
s2 = URLSafeSerializer("secret-key", salt="upgrade")
s2.dumps(42)                    # 'NDI.c0MpsD6gzpilOAeUPra3NShPXsE'
s2.loads(s1.dumps(42))          # BadSignature: Signature does not match
s2.loads(s2.dumps(42))          # 42
```
-/

def s1 := URLSafeSerializer.new "secret-key" (salt := "activate")
def s2 := URLSafeSerializer.new "secret-key" (salt := "upgrade")

def activate := s1.dumps "42"
def upgrade := s2.dumps "42"
#eval activate                 -- b'NDI.MHQqszw6Wc81wOBQszCrEE_RlzY'
#eval upgrade                  -- b'NDI.c0MpsD6gzpilOAeUPra3NShPXsE'

def crossSalt := s2.loads activate
#eval match crossSalt with
  | .error e => s!"BadSignature: {e.message}"
  | .ok _ => "accepted"
-- BadSignature: Signature b'MHQqszw6Wc81wOBQszCrEE_RlzY' does not match

#eval s2.loads upgrade         -- Except.ok "42"

/-! ## Key rotation

```python
SECRET_KEYS = ["2b9cd98e", "169d7886", "b6af09f5"]
s = Serializer(SECRET_KEYS)     # sign with the latest key
t = s.dumps({"id": 42})
SECRET_KEYS.append("cf9b3588")  # rotate a new key in, the oldest out
del SECRET_KEYS[0]
s = Serializer(SECRET_KEYS)
s.loads(t)                      # still valid
```
-/

def before := Serializer.new ["2b9cd98e", "169d7886", "b6af09f5"]
def t := before.dumps "{\"id\": 42}"
#eval t                        -- b'{"id": 42}.vPnMXi_7YWhvSPnrl9Bcf1-2I44'

def after := Serializer.new ["169d7886", "b6af09f5", "cf9b3588"]
def stillValid := after.loads t
#eval stillValid               -- Except.ok "{\"id\": 42}"
def rotated := after.dumps "{\"id\": 42}"
#eval rotated                  -- b'{"id": 42}.jGrDf14fqQmBTQeF9-Fg799Qixw'

end Examples.Concepts
