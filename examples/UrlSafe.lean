import LeanItsdangerous
open LeanItsdangerous

/-!
# URL Safe Serialization

Translates itsdangerous `docs/url_safe.rst` ("URL Safe Serialization").

```python
from itsdangerous.url_safe import URLSafeSerializer
s = URLSafeSerializer("secret-key")
s.dumps([1, 2, 3, 4])           # 'WzEsMiwzLDRd.wSPHqC0gR7VUqivlSukJ0IeTDgo'
s.loads("WzEsMiwzLDRd.wSPHqC0gR7VUqivlSukJ0IeTDgo")   # [1, 2, 3, 4]
```

The URL-safe serializers write compact JSON (`[1,2,3,4]`); upstream also
zlib-compresses long payloads, which is not supported here (see
CONTRIBUTING.md, deviations).
-/

namespace Examples.UrlSafe

def s := URLSafeSerializer.new "secret-key"

def token := s.dumps "[1,2,3,4]"
#eval token                    -- b'WzEsMiwzLDRd.wSPHqC0gR7VUqivlSukJ0IeTDgo'

def loaded := s.loads "WzEsMiwzLDRd.wSPHqC0gR7VUqivlSukJ0IeTDgo"
#eval loaded                   -- Except.ok "[1,2,3,4]"

/-- `URLSafeTimedSerializer`: the same, with a timestamp. -/
def timed := URLSafeTimedSerializer.new "secret-key"
def timedToken := timed.dumps "{\"a\":1}" 1700000000
#eval timedToken               -- b'eyJhIjoxfQ.ZVPxAA.qIAQK7X87cwO6blIj4letDtfsCI'
#eval timed.loads timedToken (maxAge := 3600) (now := 1700000060)

end Examples.UrlSafe
