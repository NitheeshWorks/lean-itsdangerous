import ItsdangerousJson
open LeanItsdangerous LeanJson

/-!
# A Simple Example

Port of itsdangerous `README.md` ("A Simple Example"), the one code block:

```python
from itsdangerous import URLSafeSerializer
auth_s = URLSafeSerializer("secret key", "auth")
token = auth_s.dumps({"id": 5, "name": "itsdangerous"})

print(token)
# eyJpZCI6NSwibmFtZSI6Iml0c2Rhbmdlcm91cyJ9.6YP6T0BaO67XP--9UzTrmurXSmg

data = auth_s.loads(token)
print(data["name"])
# itsdangerous
```
-/

namespace Examples.Quickstart

def authS := URLSafeSerializer.new "secret key" "auth"
def token := authS.dumps (json% {"id": 5, "name": "itsdangerous"})
#eval token
-- b'eyJpZCI6NSwibmFtZSI6Iml0c2Rhbmdlcm91cyJ9.6YP6T0BaO67XP--9UzTrmurXSmg'

def data := authS.loads token
def name := match data with
  | .ok d => d.val.getObjVal? "name" >>= Json.getStr?
  | .error _ => none
#eval name                      -- some "itsdangerous"

def main : IO Unit := do
  IO.println token.decode       -- eyJpZCI6NSwibmFtZSI6Iml0c2Rhbmdlcm91cyJ9.6YP6T0BaO67XP--9UzTrmurXSmg
  IO.println (name.getD "")     -- itsdangerous

end Examples.Quickstart
