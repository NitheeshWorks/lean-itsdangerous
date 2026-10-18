import LeanItsdangerous

/-!
# Conformance cases

Each case re-expresses one upstream test (https://github.com/pallets/itsdangerous,
`tests/test_itsdangerous/`) in Lean and names it, so `docs/traceability.toml`
can point at both. The upstream suite is the behavioural specification; no
upstream code is copied.

Upstream runs its signer suite twice (`TestSigner`, and `TestTimestampSigner`
inheriting it) and its serializer suite four times (`Serializer`,
`TimedSerializer`, `URLSafeSerializer`, `URLSafeTimedSerializer`); so do we,
through the small `SignerUnderTest` / `SerializerUnderTest` records. Upstream
freezes time with `freezegun`; here `now` is a parameter.

The payload codec stands in for upstream's default `json`: values are given
as their compact JSON text, `dumps` is UTF-8 encoding and `loads` accepts
only well-formed JSON (a small recogniser below), so a truncated payload
raises `BadPayload` exactly as `json.loads` would. The real JSON codec comes
from lean-json, plugged in by lean-starlette.

Run with `lake exe conformance`.
-/

open LeanItsdangerous

instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

structure Case where
  /-- Upstream test this mirrors, e.g. `tests/test_itsdangerous/test_signer.py::TestSigner::test_signer`. -/
  upstream : String
  name : String
  run : IO Bool

def b (s : String) : Bytes := Bytes.ofString s

def ensure (cond : Bool) (msg : String) : IO Bool := do
  unless cond do IO.println s!"      {msg}"
  return cond

/-! ## A JSON recogniser for the test codec -/

namespace J

def ws : Bytes → Bytes
  | c :: cs => if c == 32 || c == 10 || c == 13 || c == 9 then ws cs else c :: cs
  | [] => []

def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57

def str : Bytes → Option Bytes
  | 34 :: cs => some cs
  | 92 :: _ :: cs => str cs
  | c :: cs => if c < 32 then none else str cs
  | [] => none

def num (cs : Bytes) : Option Bytes :=
  let cs := match cs with | 45 :: r => r | r => r
  let d := cs.takeWhile isDigit
  if d.isEmpty then none else
  let cs := cs.drop d.length
  let cs := match cs with
    | 46 :: r => let f := r.takeWhile isDigit; if f.isEmpty then none else some (r.drop f.length)
    | r => some r
  cs

def lit (w : String) (cs : Bytes) : Option Bytes :=
  let w := b w
  if w.isPrefixOf cs then some (cs.drop w.length) else none

mutual
def value : Nat → Bytes → Option Bytes
  | 0, _ => none
  | n + 1, cs =>
    match ws cs with
    | 34 :: r => str r
    | 91 :: r => match ws r with
      | 93 :: r' => some r'
      | _ => elems n r
    | 123 :: r => match ws r with
      | 125 :: r' => some r'
      | _ => members n r
    | 116 :: _ => lit "true" (ws cs)
    | 102 :: _ => lit "false" (ws cs)
    | 110 :: _ => lit "null" (ws cs)
    | r => num r
def elems : Nat → Bytes → Option Bytes
  | 0, _ => none
  | n + 1, cs => do
    let r ← value n cs
    match ws r with
    | 44 :: r' => elems n r'
    | 93 :: r' => some r'
    | _ => none
def members : Nat → Bytes → Option Bytes
  | 0, _ => none
  | n + 1, cs => do
    let r ← match ws cs with | 34 :: r => str r | _ => none
    let r ← match ws r with | 58 :: r => some r | _ => none
    let r ← value n r
    match ws r with
    | 44 :: r' => members n r'
    | 125 :: r' => some r'
    | _ => none
end

def valid (bs : Bytes) : Bool :=
  match value (bs.length + 1) bs with
  | some rest => (ws rest).isEmpty
  | none => false

end J

/-- The stand-in for upstream's `json` serializer: JSON text in, JSON text out. -/
@[instance_reducible] def jsonText : Codec String where
  dumps s := b s
  loads bs :=
    if J.valid bs then
      match bs.toString? with
      | some s => .ok s
      | none => .error "invalid utf-8"
    else .error "Expecting value"

/-! ## Signer suite (`TestSigner`, `TestTimestampSigner`) -/

/-- Upstream's frozen time, 2011-06-24T00:09:05Z. -/
def frozen : UInt64 := 1308874145

structure SignerUnderTest where
  sign : Bytes → Bytes
  unsign : Bytes → Except BadData Bytes
  sep : Bytes

def SignerUnderTest.validate (s : SignerUnderTest) (x : Bytes) : Bool :=
  match s.unsign x with | .ok _ => true | .error _ => false

def plainSUT (s : Signer) : SignerUnderTest where
  sign := s.sign
  unsign x := match s.unsign x with
    | .ok v => .ok v.val
    | .error e => .error e.toBadData
  sep := s.sep

def timedSUT (s : Signer) : SignerUnderTest where
  sign v := (TimestampSigner.mk s).sign v frozen
  unsign x := match (TimestampSigner.mk s).unsign x none frozen with
    | .ok r => .ok r.val.1
    | .error e => .error e
  sep := s.sep

/-- Replace the first occurrence of `pat` by `rep` (`bytes.replace(.., 1)`). -/
def replace1 (pat rep : Bytes) : Bytes → Bytes
  | [] => []
  | c :: cs => if pat.isPrefixOf (c :: cs) then rep ++ (c :: cs).drop pat.length
    else c :: replace1 pat rep cs

def isBadSig : Except BadData Bytes → Bool
  | .error e => e.isBadSignature
  | .ok _ => false

/-- `_ReverseAlgorithm` from upstream's test: `(key + value)[::-1]`. -/
def reverseAlgorithm : SigningAlgorithm := ⟨"reverse", fun k v => (k ++ v).reverse⟩

def signerSuite (cls : String) (mk : Signer → SignerUnderTest) : List Case :=
  let file := "tests/test_itsdangerous/" ++ (if cls == "TestSigner" then "test_signer.py" else "test_timed.py")
  let up (t : String) := s!"{file}::{cls}::{t}"
  let dflt := mk (Signer.new "secret-key")
  [ ⟨up "test_signer", s!"{cls}: sign then validate and unsign", do
      let signed := dflt.sign (b "my string")
      ensure (dflt.validate signed && dflt.unsign signed == .ok (b "my string")) "round trip failed"⟩,
    ⟨up "test_no_separator", s!"{cls}: separator replaced", do
      let signed := replace1 dflt.sep (b "*") (dflt.sign (b "my string"))
      ensure (!dflt.validate signed && isBadSig (dflt.unsign signed)) "accepted"⟩,
    ⟨up "test_broken_signature", s!"{cls}: truncated signature, payload kept", do
      let signed := dflt.sign (b "b")
      let bad := signed.dropLast
      match dflt.unsign bad with
      | .error e => ensure (e.isBadSignature && e.payload == some (b "b")) s!"payload {repr e}"
      | .ok _ => ensure false "accepted"⟩,
    ⟨up "test_changed_value", s!"{cls}: value changed", do
      let signed := replace1 (b "my") (b "other") (dflt.sign (b "my string"))
      ensure (!dflt.validate signed && isBadSig (dflt.unsign signed)) "accepted"⟩,
    ⟨up "test_invalid_separator", s!"{cls}: separator '-' rejected", do
      -- A literal is rejected at compile time (`by decide` fails); at run time:
      match checkSeparator (b "-") with
      | .error m => ensure (!decide (ValidSep (b "-")) && (m.splitOn "separator cannot be used").length > 1) m
      | .ok _ => ensure false "accepted"⟩,
    ⟨up "test_key_derivation", s!"{cls}: concat, django-concat, hmac, none", do
      let ok := [KeyDerivation.concat, .djangoConcat, .hmac, .none].all fun kd =>
        let s := mk (Signer.new "secret-key" (keyDerivation := kd))
        s.unsign (s.sign (b "value")) == .ok (b "value")
      ensure ok "a key derivation failed"⟩,
    ⟨up "test_digest_method", s!"{cls}: another digest (SHA-256 for md5)", do
      let s := mk (Signer.new "secret-key" (digestMethod := sha256))
      ensure (s.unsign (s.sign (b "value")) == .ok (b "value")) "round trip failed"⟩,
    ⟨up "test_algorithm", s!"{cls}: default, None, HMAC, reverse algorithms", do
      let ok := [none, some noneAlgorithm, some (hmacAlgorithm sha1), some reverseAlgorithm].all fun a =>
        let s := mk (Signer.new "secret-key" (algorithm := a))
        s.unsign (s.sign (b "value")) == .ok (b "value")
      ensure ok "an algorithm failed"⟩,
    ⟨up "test_secret_keys", s!"{cls}: key rotation", do
      let s1 := mk (Signer.new "a")
      let s2 := mk (Signer.new ["a", "b"])
      let signed := s1.sign (b "my string")
      ensure (s2.validate signed && s2.unsign signed == .ok (b "my string")) "rotation failed"⟩ ]

def tsSigner : TimestampSigner := TimestampSigner.new "secret-key"

def timedSignerCases : List Case :=
  let up (t : String) := s!"tests/test_itsdangerous/test_timed.py::TestTimestampSigner::{t}"
  [ ⟨up "test_max_age", "TestTimestampSigner: max_age boundary and expiry", do
      let signed := tsSigner.sign (b "value") frozen
      let ok1 := match tsSigner.unsign signed (some 10) (frozen + 1) with
        | .ok r => r.val.1 == b "value" | .error _ => false
      let ok2 := match tsSigner.unsign signed (some 10) (frozen + 11) with
        | .error e => e.isSignatureExpired && e.dateSigned == some frozen.toNat | .ok _ => false
      ensure (ok1 && ok2) "max_age"⟩,
    ⟨up "test_return_timestamp", "TestTimestampSigner: timestamp returned", do
      match tsSigner.unsign (tsSigner.sign (b "value") frozen) none frozen with
      | .ok r => ensure (r.val == (b "value", frozen)) "wrong result"
      | .error e => ensure false e.message⟩,
    ⟨up "test_timestamp_missing", "TestTimestampSigner: plain signature has no timestamp", do
      let signed := (Signer.new "secret-key").sign (b "value")
      match tsSigner.unsign signed none frozen with
      | .error e => ensure (e.isBadTimeSignature && (e.message.splitOn "missing").length > 1 &&
          e.dateSigned == none) e.message
      | .ok _ => ensure false "accepted"⟩,
    ⟨up "test_malformed_timestamp", "TestTimestampSigner: malformed timestamp", do
      let signed := (Signer.new "secret-key").sign (b "value.____________")
      match tsSigner.unsign signed none frozen with
      | .error e => ensure (e.isBadTimeSignature && (e.message.splitOn "Malformed").length > 1 &&
          e.dateSigned == none) e.message
      | .ok _ => ensure false "accepted"⟩,
    ⟨up "test_malformed_future_timestamp", "TestTimestampSigner: timestamp beyond datetime range", do
      match tsSigner.unsign (b "value.TgPVoaGhoQ.AGBfQ6G6cr07byTRt0zAdPljHOY") none frozen with
      | .error e => ensure (e.isBadTimeSignature && (e.message.splitOn "Malformed").length > 1 &&
          e.dateSigned == none) e.message
      | .ok _ => ensure false "accepted"⟩,
    ⟨up "test_future_age", "TestTimestampSigner: signed in the future", do
      match tsSigner.unsign (tsSigner.sign (b "value") frozen) (some 10) 44496000 with
      | .error e => ensure (e.isSignatureExpired && e.dateSigned.isSome) e.message
      | .ok _ => ensure false "accepted"⟩,
    ⟨up "test_sig_error_date_signed", "TestTimestampSigner: bad signature still reports the date", do
      let signed := replace1 (b "my") (b "other") (tsSigner.sign (b "my string") frozen)
      match tsSigner.unsign signed none frozen with
      | .error e => ensure (e.isBadTimeSignature && e.dateSigned.isSome) e.message
      | .ok _ => ensure false "accepted"⟩ ]

/-! ## Serializer suite (`TestSerializer` and its three subclasses) -/

structure SerializerUnderTest where
  dumps : String → Option Bytes → Bytes
  loads : Bytes → Option Bytes → Except BadData String
  loadsUnsafe : Bytes → Except BadData (Bool × Option String)
  loadPayload : Bytes → Except BadData String
  /-- `make_signer().sign` -/
  sign : Bytes → Bytes

def plainSer (s : Serializer String) : SerializerUnderTest where
  dumps x salt := s.dumps x salt
  loads x salt := (s.loads x salt).map Subtype.val
  loadsUnsafe x := s.loadsUnsafe x
  loadPayload := s.loadPayload
  sign := (s.makeSigner).sign

def timedSer (s : TimedSerializer String) : SerializerUnderTest where
  dumps x salt := s.dumps x frozen salt
  loads x salt := (s.loads x none frozen salt).map (·.val.1)
  loadsUnsafe x := s.loadsUnsafe x none frozen
  loadPayload := s.toSerializer.loadPayload
  sign v := (s.makeSigner).sign v frozen

def isBadSigS : Except BadData String → Bool
  | .error e => e.isBadSignature
  | .ok _ => false

def upper (bs : Bytes) : Bytes := bs.map fun c => if 97 ≤ c && c ≤ 122 then c - 32 else c

/-- Everything up to the last `.`: `s.rsplit(".", 1)[0]`. -/
def beforeLastDot (bs : Bytes) : Bytes := ((rsplit [46] bs).map (·.1)).getD bs

def serializerSuite (file cls : String) (mk : Option (List SignerKwargs) → Option SignerKwargs →
    SerializerUnderTest) (values : List String) : List Case :=
  let up (t : String) := s!"tests/test_itsdangerous/{file}::{cls}::{t}"
  let s := mk none none
  let perValue (t : String) (f : String → IO Bool) : Case :=
    ⟨up t, s!"{cls}: {t}", do
      let mut ok := true
      for v in values do
        ok := ok && (← f v)
      return ok⟩
  [ ⟨up "test_serializer", s!"{cls}: round trip of null, true, strings, list, object", do
      let vals := ["null", "true", "\"str\"", "\"text\"", "[1,2,3]", "{\"id\":42}"] ++ values
      ensure (vals.all fun v => s.loads (s.dumps v none) none == .ok v) "round trip failed"⟩,
    perValue "test_changed_value" fun v => do
      let signed := s.dumps v none
      let changed := [upper signed, signed ++ b "a", b "a" ++ signed.drop 1, signed.filter (· != 46)]
      ensure (s.loads signed none == .ok v && changed.all fun c => isBadSigS (s.loads c none))
        s!"tampered token accepted for {v}",
    perValue "test_bad_signature_exception" fun v => do
      match s.loads (s.dumps v none).dropLast none with
      | .error e => ensure (e.isBadSignature &&
          (e.payload.map fun p => s.loadPayload p == .ok v) == some true) "payload not recoverable"
      | .ok _ => ensure false "accepted",
    perValue "test_bad_payload_exception" fun v => do
      let payload := beforeLastDot (s.dumps v none)
      match s.loads (s.sign payload.dropLast) none with
      | .error (.badPayload _ (some _)) => pure true
      | r => ensure false s!"expected BadPayload, got {repr (r.toOption)}",
    perValue "test_loads_unsafe" fun v => do
      let signed := s.dumps v none
      let bad := s.sign (beforeLastDot signed).dropLast |>.dropLast
      ensure (s.loadsUnsafe signed == .ok (true, some v) &&
        s.loadsUnsafe signed.dropLast == .ok (false, some v) &&
        s.loadsUnsafe bad == .ok (false, none)) "loads_unsafe",
    perValue "test_alt_salt" fun v => do
      let signed := s.dumps v (some (b "other"))
      ensure (isBadSigS (s.loads signed none) && s.loads signed (some (b "other")) == .ok v) "salt",
    perValue "test_signer_cls" fun v => do
      let other := mk none (some ({ keyDerivation := .hmac }))
      ensure (other.loads (other.dumps v none) none == .ok v && other.dumps v none != s.dumps v none)
        "hmac key derivation",
    perValue "test_signer_kwargs" fun v => do
      let other := mk none (some ({ keyDerivation := .hmac }))
      ensure (other.loads (other.dumps v none) none == .ok v &&
        other.dumps "\"value\"" none != s.dumps "\"value\"" none) "signer kwargs",
    perValue "test_fallback_signers" fun v => do
      let s256 := mk none (some ({ digestMethod := sha256 }))
      let fb := mk (some [{ digestMethod := sha256 }]) (some ({ digestMethod := sha1 }))
      ensure (fb.loads (s256.dumps v none) none == .ok v) "fallback" ]

def serKey : Bytes := b "secret_key"

def mkPlain (codec : Codec String) (key : Bytes) (fbs : Option (List SignerKwargs))
    (kw : Option SignerKwargs) : SerializerUnderTest :=
  plainSer (Serializer.new key (serializer := codec) (signerKwargs := kw.getD {})
    (fallbackSigners := fbs.getD []))

def mkTimed (codec : Codec String) (key : Bytes) (fbs : Option (List SignerKwargs))
    (kw : Option SignerKwargs) : SerializerUnderTest :=
  timedSer (TimedSerializer.new key (serializer := codec) (signerKwargs := kw.getD {})
    (fallbackSigners := fbs.getD []))

def thousandA : String := "\"" ++ String.ofList (List.replicate 1000 'a') ++ "\""

def serializerCases : List Case :=
  serializerSuite "test_serializer.py" "TestSerializer" (mkPlain jsonText serKey) ["{\"id\":42}"] ++
  serializerSuite "test_timed.py" "TestTimedSerializer" (mkTimed jsonText serKey) ["{\"id\":42}"] ++
  serializerSuite "test_url_safe.py" "TestURLSafeSerializer" (mkPlain (urlSafeCodec jsonText) (b "secret-key"))
    ["{\"id\":42}", thousandA] ++
  serializerSuite "test_url_safe.py" "TestURLSafeTimedSerializer" (mkTimed (urlSafeCodec jsonText) (b "secret-key"))
    ["{\"id\":42}", thousandA]

def timedSer0 : TimedSerializer String := TimedSerializer.new serKey (serializer := jsonText)

def otherSerializerCases : List Case := [
  ⟨"tests/test_itsdangerous/test_serializer.py::TestSerializer::test_iter_unsigners",
   "TestSerializer: unsigner order (main, then each fallback per key)", do
      let s := Serializer.new serKey (serializer := jsonText)
        (fallbackSigners := [{ digestMethod := sha256 }, { digestMethod := sha256 }, { digestMethod := sha256 }])
      let names := (s.unsigners).map (·.digest.name)
      ensure (names == ["sha1", "sha256", "sha256", "sha256"]) s!"{names}"⟩,
  ⟨"tests/test_itsdangerous/test_serializer.py::test_digests", "test_digests: SHA-1 and SHA-512 tokens", do
      let mk (kw : SignerKwargs) := Serializer.new "dev key" (salt := "dev salt") (serializer := jsonText) (signerKwargs := kw)
      let dflt := (mk {}).dumps "[42]"
      let s1 := (mk ({ digestMethod := sha1 })).dumps "[42]"
      let s512 := (mk ({ digestMethod := sha512 })).dumps "[42]"
      ensure (dflt == s1 && s1 == b "[42].-9cNi0CxsSB3hZPNCe9a2eEs1ZM" &&
        s512 == b ("[42].MKCz_0nXQqv7wKpfHZcRtJRmpT2T5uvs9YQsJEhJimqxc" ++
          "9bCLxG31QzS5uC8OVBI1i6jyOLAFNoKaF5ckO9L5Q")) s!"{s1} {s512}"⟩,
  ⟨"tests/test_itsdangerous/test_timed.py::TestTimedSerializer::test_max_age",
   "TestTimedSerializer: max_age expiry keeps date and payload", do
      let signed := timedSer0.dumps "{\"id\":42}" frozen
      let ok1 := match timedSer0.loads signed (some 10) (frozen + 1) with
        | .ok r => r.val.1 == "{\"id\":42}" | .error _ => false
      let ok2 := match timedSer0.loads signed (some 10) (frozen + 11) with
        | .error e => e.isSignatureExpired && e.dateSigned == some frozen.toNat &&
            (e.payload.map fun p => timedSer0.toSerializer.loadPayload p == .ok "{\"id\":42}") == some true
        | .ok _ => false
      ensure (ok1 && ok2) "max_age"⟩,
  ⟨"tests/test_itsdangerous/test_timed.py::TestTimedSerializer::test_return_payload",
   "TestTimedSerializer: value and timestamp returned", do
      match timedSer0.loads (timedSer0.dumps "{\"id\":42}" frozen) none frozen with
      | .ok r => ensure (r.val == ("{\"id\":42}", frozen)) "wrong result"
      | .error e => ensure false e.message⟩
]

/-! ## Encoding (`test_encoding.py`) -/

def encodingCases : List Case := [
  ⟨"tests/test_itsdangerous/test_encoding.py::test_want_bytes", "want_bytes of text", do
      ensure (b "mañana" == [109, 97, 195, 177, 97, 110, 97]) "utf-8"⟩,
  ⟨"tests/test_itsdangerous/test_encoding.py::test_base64", "base64 round trip of text and bytes", do
      ensure (["無限", "infinite"].all fun v => base64Decode (base64Encode (b v)) == some (b v)) "round trip"⟩,
  ⟨"tests/test_itsdangerous/test_encoding.py::test_base64_bad", "base64_decode(\"12345\") is invalid", do
      ensure (base64Decode (b "12345") == none) "accepted"⟩,
  ⟨"tests/test_itsdangerous/test_encoding.py::test_int_bytes", "int_to_bytes / bytes_to_int", do
      let cases : List (UInt64 × Bytes) := [(0, []), (192, [0xc0]), (18446744073709551615, List.replicate 8 0xff)]
      ensure (cases.all fun (n, e) => intToBytes n == e && bytesToInt e == some n) "int bytes"⟩
]

/-! ## Known-answer tokens from upstream itsdangerous 2.2.0

Byte-exact tokens produced by upstream itsdangerous 2.2.0 (key `secret-key`
unless stated; timestamps fixed by overriding `get_timestamp`). The upstream
tests above check only round trips for these configurations; these pin the
bytes, so a swapped key-derivation formula, HMAC argument order or timestamp
byte order fails here. Each case also checks that `unsign`/`loads` accepts
the upstream token. -/

structure Kat where
  upstream : String
  name : String
  produced : Bytes
  expected : String
  accepts : Bool

def katCase (k : Kat) : Case :=
  ⟨k.upstream, s!"known answer: {k.name}", ensure (k.produced == b k.expected && k.accepts)
    s!"got {k.produced}, expected {k.expected}, accepts={k.accepts}"⟩

def signerKat (kd : KeyDerivation) (h : Hash) (kdName expected : String) : Kat :=
  let s := Signer.new "secret-key" (keyDerivation := kd) (digestMethod := h)
  { upstream := "tests/test_itsdangerous/test_signer.py::TestSigner::" ++
      (if h.name == "sha1" then "test_key_derivation" else "test_digest_method")
    name := s!"Signer {h.name} {kdName}"
    produced := s.sign (b "my string")
    expected
    accepts := s.validate (b expected) }

def tsKat (ts : UInt64) (v expected : String) : Kat :=
  let t := TimestampSigner.new "secret-key"
  { upstream := "tests/test_itsdangerous/test_timed.py::TestTimestampSigner::test_return_timestamp"
    name := s!"TimestampSigner ts={ts} {v}"
    produced := t.sign (b v) ts
    expected
    accepts := match t.unsign (b expected) none ts with
      | .ok r => r.val == (b v, ts) | .error _ => false }

def customSepSigner : Signer := Signer.new "secret-key" (salt := "custom-salt") (sep := "|")

def rotSigner : Signer := Signer.new ["old", "new"]

def urlSafe : URLSafeSerializer String := URLSafeSerializer.new "secret-key" (serializer := jsonText)
def urlSafeSalt : URLSafeSerializer String :=
  URLSafeSerializer.new "secret-key" (salt := "activate") (serializer := jsonText)
def urlSafeTimed : URLSafeTimedSerializer String :=
  URLSafeTimedSerializer.new "secret-key" (serializer := jsonText)
def timedPlain : TimedSerializer String := TimedSerializer.new "secret_key" (serializer := jsonText)
def starletteSigner : TimestampSigner := TimestampSigner.new "example"
def starletteData : String := "eyJ1c2VyIjogImFsaWNlIn0="

def kats : List Kat := [
  signerKat .concat sha1 "concat" "my string.WVn1orytePdJMO-gerBb0CoxFMs",
  signerKat .djangoConcat sha1 "django-concat" "my string.wh6tMHxLgJqB6oY1uT73iMlyrOA",
  signerKat .hmac sha1 "hmac" "my string.pFgSwq6wOZqq2WMqgkxNLVn16QY",
  signerKat .none sha1 "none" "my string.jdP_vbFmmLI4saUm2wcIut0z2MQ",
  signerKat .concat sha256 "concat" "my string.Dy-9UM0Xc6N5vpsCbSzG_vONu5By2MVMAFiUIbDPNrw",
  signerKat .djangoConcat sha256 "django-concat" "my string.PVHY4OzY_ekIpRd3A5G0vzTkhg8wSod5E3p90JgBCKw",
  signerKat .hmac sha256 "hmac" "my string.9gNXlg5H__tL4eudpMDWVAk9FCr72htCAUx80xrV9gM",
  signerKat .none sha256 "none" "my string.0A34Z7kdl36oAXGceNspSDf1wOz0IS0ASArypw7_Lms",
  { upstream := "tests/test_itsdangerous/test_signer.py::TestSigner::test_signer"
    name := "Signer sep '|' salt custom-salt"
    produced := customSepSigner.sign (b "my string")
    expected := "my string|KXoAxp_1PqthcdIhZEMH6jocYlQ"
    accepts := customSepSigner.validate (b "my string|KXoAxp_1PqthcdIhZEMH6jocYlQ") },
  { upstream := "tests/test_itsdangerous/test_signer.py::TestSigner::test_secret_keys"
    name := "Signer [old, new] signs with the newest key"
    produced := rotSigner.sign (b "v")
    expected := "v.36xUtSROzMo9IUv6FUAqcLcS7_Y"
    accepts := (Signer.new "new").validate (b "v.36xUtSROzMo9IUv6FUAqcLcS7_Y") },
  tsKat 0 "v" "v..laaFEvAn6iGJwjqtau5N2YmZ0A8",
  tsKat 255 "v" "v._w.u0GYwMSLW0hJhBJF9vicXI0nzfA",
  tsKat 256 "v" "v.AQA.oTwPDMwTbTNdviKzH2UM_1ECDSs",
  tsKat 4294967296 "v" "v.AQAAAAA.gF5qB1AFkyPib47h3CIK88R7gN8",
  tsKat 1700000000 "v" "v.ZVPxAA.1riky2Uj5pB3LQJugNYKQDv4fvM",
  tsKat 1700000000 "my string" "my string.ZVPxAA.jr6oPKNI4x66_7OoEQCvO5o789s",
  { upstream := "tests/test_itsdangerous/test_url_safe.py::TestURLSafeSerializer::test_serializer"
    name := "URLSafeSerializer {\"id\":42}"
    produced := urlSafe.dumps "{\"id\":42}"
    expected := "eyJpZCI6NDJ9.Z-HaNt236Oj5pFDPW25MouYkrcA"
    accepts := (urlSafe.loads (b "eyJpZCI6NDJ9.Z-HaNt236Oj5pFDPW25MouYkrcA")).map (·.val) == .ok "{\"id\":42}" },
  { upstream := "tests/test_itsdangerous/test_url_safe.py::TestURLSafeSerializer::test_alt_salt"
    name := "URLSafeSerializer salt activate"
    produced := urlSafeSalt.dumps "{\"id\":42}"
    expected := "eyJpZCI6NDJ9.lXMQDXurRwywHccJV6dRfCQk0eQ"
    accepts := (urlSafeSalt.loads (b "eyJpZCI6NDJ9.lXMQDXurRwywHccJV6dRfCQk0eQ")).map (·.val) == .ok "{\"id\":42}" },
  { upstream := "tests/test_itsdangerous/test_url_safe.py::TestURLSafeTimedSerializer::test_return_payload"
    name := "URLSafeTimedSerializer {\"a\":1} at 1700000000"
    produced := urlSafeTimed.dumps "{\"a\":1}" 1700000000
    expected := "eyJhIjoxfQ.ZVPxAA.qIAQK7X87cwO6blIj4letDtfsCI"
    accepts := (urlSafeTimed.loads (b "eyJhIjoxfQ.ZVPxAA.qIAQK7X87cwO6blIj4letDtfsCI") none 1700000000).map (·.val)
      == .ok ("{\"a\":1}", 1700000000) },
  { upstream := "tests/test_itsdangerous/test_timed.py::TestTimedSerializer::test_return_payload"
    name := "TimedSerializer {\"id\": 42} at 1700000000"
    produced := timedPlain.dumps "{\"id\": 42}" 1700000000
    expected := "{\"id\": 42}.ZVPxAA.aFESr2OogwT9RtL_Xt98-zUL8QI"
    accepts := (timedPlain.loads (b "{\"id\": 42}.ZVPxAA.aFESr2OogwT9RtL_Xt98-zUL8QI") none 1700000000).map (·.val)
      == .ok ("{\"id\": 42}", 1700000000) },
  { upstream := "README.md::A Simple Example"
    name := "README: URLSafeSerializer(\"secret key\", \"auth\")"
    produced := (URLSafeSerializer.new "secret key" "auth" (serializer := jsonText) : URLSafeSerializer String).dumps
      "{\"id\":5,\"name\":\"itsdangerous\"}"
    expected := "eyJpZCI6NSwibmFtZSI6Iml0c2Rhbmdlcm91cyJ9.6YP6T0BaO67XP--9UzTrmurXSmg"
    accepts := true },
  { upstream := "starlette:tests/middleware/test_session.py::test_session"
    name := "Starlette SessionMiddleware cookie (TimestampSigner(\"example\"))"
    produced := starletteSigner.sign (b starletteData) 1700000000
    expected := starletteData ++ ".ZVPxAA.vA70g_JgN4tTucTzi3dRghALTvE"
    accepts := match starletteSigner.unsign (b (starletteData ++ ".ZVPxAA.vA70g_JgN4tTucTzi3dRghALTvE"))
        (some 1209600) 1700000100 with
      | .ok r => r.val.1 == b starletteData | .error _ => false }
]

def cases : List Case :=
  encodingCases ++ signerSuite "TestSigner" (fun s => plainSUT s) ++
  signerSuite "TestTimestampSigner" (fun s => timedSUT s) ++ timedSignerCases ++
  serializerCases ++ otherSerializerCases ++ kats.map katCase

def main : IO UInt32 := do
  let mut failures := 0
  for c in cases do
    let ok ← try c.run catch e => do IO.println s!"      {e}"; pure false
    IO.println s!"{if ok then "ok  " else "FAIL"}  {c.name}  [{c.upstream}]"
    unless ok do failures := failures + 1
  IO.println s!"{cases.length} cases, {failures} failing"
  return if failures == 0 then 0 else 1
