import LeanItsdangerous
open LeanItsdangerous

/-! The itsdangerous README's example, translated. -/

def authS : URLSafeSerializer String := .new "secret key" "auth"
def token : Bytes := authS.dumps "{\"id\":5,\"name\":\"itsdangerous\"}"
#eval token
-- b'eyJpZCI6NSwibmFtZSI6Iml0c2Rhbmdlcm91cyJ9.6YP6T0BaO67XP--9UzTrmurXSmg'
#eval (authS.loads token).val

/-! Signer -/
def s := Signer.new "secret-key"
#eval s.sign "my string"
#eval (s.unsign "my string.wh6tMHxLgJqB6oY1uT73iMlyrOA").val

/-! TimestampSigner with max_age -/
def ts := TimestampSigner.new "secret-key"
def stamped := ts.sign "foo" 1700000000
#eval (ts.unsign stamped (maxAge := some 5) (now := 1700000003)).val
#eval match (ts.unsign stamped (maxAge := some 5) (now := 1700000010)).val with
  | .error e => e.message | .ok _ => "ok"

/-! Key rotation and a custom separator -/
def rotated := Signer.new ["old key", "new key"] (sep := "|")
#eval rotated.sign "v"

def main : IO Unit := do
  let now ← getTimestamp
  let u : URLSafeTimedSerializer String := .new "secret-key" (salt := "activate")
  let t := u.dumps "{\"user\":42}" now
  IO.println (repr ((u.loads t (maxAge := some 3600) now).val)).pretty
