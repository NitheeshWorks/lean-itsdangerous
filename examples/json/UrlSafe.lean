import ItsdangerousJson
open LeanItsdangerous LeanJson

/-!
# URL Safe Serialization

Port of itsdangerous `docs/url_safe.rst` ("URL Safe Serialization"), the one
code block:

```python
from itsdangerous.url_safe import URLSafeSerializer
s = URLSafeSerializer("secret-key")
s.dumps([1, 2, 3, 4])
'WzEsMiwzLDRd.wSPHqC0gR7VUqivlSukJ0IeTDgo'
s.loads("WzEsMiwzLDRd.wSPHqC0gR7VUqivlSukJ0IeTDgo")
[1, 2, 3, 4]
```
-/

namespace Examples.UrlSafe

def s := URLSafeSerializer.new "secret-key"
def token := s.dumps (json% [1, 2, 3, 4])
#eval token                     -- b'WzEsMiwzLDRd.wSPHqC0gR7VUqivlSukJ0IeTDgo'
def loaded := s.loads "WzEsMiwzLDRd.wSPHqC0gR7VUqivlSukJ0IeTDgo"
#eval loaded                    -- Except.ok json% [1, 2, 3, 4]

end Examples.UrlSafe
