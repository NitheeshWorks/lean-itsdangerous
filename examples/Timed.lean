import LeanItsdangerous
open LeanItsdangerous

/-!
# Signing With Timestamps

Port of itsdangerous `docs/timed.rst` ("Signing With Timestamps"), block by
block. Upstream reads the clock inside `sign` and `unsign`; here the time is
the last argument, fixed so the output is reproducible: signed at `t0`,
checked 15 seconds later, as the page's traceback shows.
-/

namespace Examples.Timed

/-! Block 1:
```python
from itsdangerous import TimestampSigner
s = TimestampSigner('secret-key')
string = s.sign('foo')
```
-/

def s := TimestampSigner.new "secret-key"
def t0 : UInt64 := 1700000000
def string := s.sign "foo" t0
#eval string                    -- b'foo.ZVPxAA.IsOrIGtLkuP2keI23m0UgRvxgdY'

/-! Block 2:
```python
s.unsign(string, max_age=5)
Traceback (most recent call last):
  ...
itsdangerous.exc.SignatureExpired: Signature age 15 > 5 seconds
```
-/

def expired := s.unsign string (maxAge := 5) (now := t0 + 15)
#eval expired                   -- Except.error SignatureExpired: Signature age 15 > 5 seconds

-- The exception's `date_signed`, a `datetime` as upstream gives it:
#eval match expired with
  | .error e => repr e.dateSigned | .ok _ => "accepted"
-- some datetime.datetime(2023, 11, 14, 22, 13, 20, tzinfo=datetime.timezone.utc)

end Examples.Timed
