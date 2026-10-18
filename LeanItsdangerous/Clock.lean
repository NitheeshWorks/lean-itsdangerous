import Std.Time

/-!
# Clock: the one effectful module

Upstream's `TimestampSigner.get_timestamp()` reads `time.time()`. Everything
else in this library is pure and takes the time as an argument `now`; this
module is the one place that reads the wall clock, so a program can write

```lean
let now ← getTimestamp
let token := signer.sign "value" now
```
-/

namespace LeanItsdangerous

/-- Seconds since the Unix epoch, now: upstream's `get_timestamp()`. -/
def getTimestamp : IO UInt64 := do
  let t ← Std.Time.Timestamp.now
  return UInt64.ofNat t.toSecondsSinceUnixEpoch.toInt.toNat

end LeanItsdangerous
