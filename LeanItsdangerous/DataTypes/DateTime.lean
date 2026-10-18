/-!
# DateTime

Upstream's `date_signed` is an aware UTC `datetime`. Here it is a UTC
instant in whole seconds since the Unix epoch, rendered as Python renders a
`datetime`: `str` gives `2023-11-14 22:13:20+00:00`, `repr` gives
`datetime.datetime(2023, 11, 14, 22, 13, 20, tzinfo=datetime.timezone.utc)`.
The calendar fields come from the days-to-civil algorithm (proleptic
Gregorian), in plain `Nat` arithmetic.
-/

namespace LeanItsdangerous

/-- A UTC instant, in seconds since the Unix epoch. -/
structure DateTime where
  timestamp : Nat
  deriving DecidableEq, Inhabited

namespace DateTime

/-- `(year, month, day)` of the instant. -/
def date (d : DateTime) : Nat × Nat × Nat :=
  let z := d.timestamp / 86400 + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let day := doy - (153 * mp + 2) / 5 + 1
  let month := if mp < 10 then mp + 3 else mp - 9
  let year := yoe + era * 400 + (if month ≤ 2 then 1 else 0)
  (year, month, day)

def year (d : DateTime) : Nat := d.date.1
def month (d : DateTime) : Nat := d.date.2.1
def day (d : DateTime) : Nat := d.date.2.2
def hour (d : DateTime) : Nat := d.timestamp % 86400 / 3600
def minute (d : DateTime) : Nat := d.timestamp % 3600 / 60
def second (d : DateTime) : Nat := d.timestamp % 60

private def pad (w n : Nat) : String :=
  let s := toString n
  String.ofList (List.replicate (w - s.length) '0') ++ s

/-- Python's `str(datetime)`: `2023-11-14 22:13:20+00:00`. -/
def isoformat (d : DateTime) : String :=
  s!"{pad 4 d.year}-{pad 2 d.month}-{pad 2 d.day} {pad 2 d.hour}:{pad 2 d.minute}:{pad 2 d.second}+00:00"

instance : ToString DateTime := ⟨isoformat⟩

/-- Python's `repr(datetime)`, which omits a zero second. -/
instance : Repr DateTime where
  reprPrec d _ :=
    let sec := if d.second = 0 then "" else s!", {d.second}"
    .text s!"datetime.datetime({d.year}, {d.month}, {d.day}, {d.hour}, {d.minute}{sec}, tzinfo=datetime.timezone.utc)"

end DateTime

end LeanItsdangerous
