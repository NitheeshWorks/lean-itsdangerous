import LeanItsdangerous
open LeanItsdangerous

/-!
# Signing With Timestamps

Translates itsdangerous `docs/timed.rst` ("Signing With Timestamps").

```python
from itsdangerous import TimestampSigner
s = TimestampSigner('secret-key')
string = s.sign('foo')
s.unsign(string, max_age=5)
# itsdangerous.exc.SignatureExpired: Signature age 15 > 5 seconds
```

Upstream reads the clock inside `sign` and `unsign`; here the time is the
last argument (`getTimestamp` reads the clock, see `main`). The example
fixes it so its output is reproducible: signed at `t0`, checked 15 seconds
later.
-/

namespace Examples.Timed

def s := TimestampSigner.new "secret-key"
def t0 : UInt64 := 1700000000

def string := s.sign "foo" t0
#eval string                   -- b'foo.ZVPxAA.IsOrIGtLkuP2keI23m0UgRvxgdY'

/-- Fifteen seconds later, with `max_age=5`. -/
def tooOld := s.unsign string (maxAge := 5) (now := t0 + 15)
#eval match tooOld with
  | .error e => s!"SignatureExpired: {e.message} (signed at {e.dateSigned})"
  | .ok _ => "accepted"
-- SignatureExpired: Signature age 15 > 5 seconds (signed at some 1700000000)

/-- Three seconds later it is accepted; the timestamp comes back too
(`return_timestamp=True`). -/
def fresh := s.unsign string (maxAge := 5) (now := t0 + 3)
#eval fresh                    -- Except.ok (b'foo', 1700000000)

/-- `TimedSerializer` is the serializer counterpart. -/
def ts := TimedSerializer.new "secret-key"
def timedToken := ts.dumps "[1, 2, 3, 4]" t0
#eval timedToken               -- b'[1, 2, 3, 4].ZVPxAA.ntr3GKq8MmJ7zD3OC1BOs7aq6VA'

/-- With the real clock. -/
def main : IO Unit := do
  let now ← getTimestamp
  let token := s.sign "foo" now
  IO.println (repr (s.unsign token (maxAge := 5) now)).pretty

end Examples.Timed
