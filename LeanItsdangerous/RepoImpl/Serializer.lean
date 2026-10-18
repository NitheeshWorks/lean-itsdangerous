import LeanItsdangerous.RepoImpl.Signer

/-!
# Serializer, TimedSerializer, URL-safe serializers

Transcriptions of `itsdangerous/serializer.py`, the `TimedSerializer` half of
`timed.py`, and `url_safe.py`. The payload codec is a parameter (`Codec α`);
upstream's default is `json`, which the caller supplies (lean-starlette plugs
in lean-json).

The URL-safe serializers are a codec transformer: `urlSafeCodec c` base64url
encodes `c`'s output. Upstream additionally zlib-compresses a payload when
that makes it shorter, marking it with a leading `.`; zlib is out of scope, so
`dumps` never compresses and `loads` rejects a compressed payload with
`BadPayload` (recorded as a deviation).
-/

namespace LeanItsdangerous

/-- Upstream's default signer salt, used when a serializer's salt is `None`. -/
def defaultSignerSalt : Bytes := Bytes.ofString "itsdangerous.Signer"

/-- The URL-safe payload wrapping: base64url; a leading `.` marks a
zlib-compressed payload, which is not supported. -/
def urlSafeLoads (p : Bytes) : Except String Bytes :=
  match p with
  | 46 :: _ => .error "zlib-compressed payloads are not supported"
  | _ => match base64Decode p with
    | some json => .ok json
    | none => .error "Could not base64 decode the payload"

/-- base64url payloads, rejecting the compressed form. -/
@[instance_reducible] def urlSafeBase64 : Codec Bytes := ⟨base64Encode, urlSafeLoads⟩

/-- `URLSafeSerializerMixin`'s payload handling around a codec. -/
@[instance_reducible] def urlSafeCodec {α : Type} (c : Codec α) : Codec α := c.andThen urlSafeBase64

namespace Serializer

variable {α : Type}

/-- The signer for a configuration, this serializer's keys, and a salt. -/
def mkSigner (s : Serializer α) (cfg : SignerConfig) (keys : List Bytes) (h : keys ≠ [])
    (salt : Option Bytes) : Signer :=
  { cfg with secretKeys := keys, h_keys := h, salt := (salt <|> s.salt).getD defaultSignerSalt }

/-- `make_signer(salt)`. -/
def makeSigner (s : Serializer α) (salt : Option Bytes := none) : Signer :=
  s.mkSigner s.signer s.secretKeys s.h_keys salt

/-- `iter_unsigners(salt)`: the main signer with every key, then each
fallback configuration once per secret key. -/
def unsigners (s : Serializer α) (salt : Option Bytes := none) : List Signer :=
  s.makeSigner salt ::
    s.fallbacks.flatMap fun cfg =>
      s.secretKeys.map fun k => s.mkSigner cfg [k] (List.cons_ne_nil k []) salt

/-- `load_payload(payload)`. -/
def loadPayload (s : Serializer α) (payload : Bytes) : Except BadData α :=
  match s.codec.loads payload with
  | .ok x => .ok x
  | .error e => .error (.badPayload
      "Could not load the payload because an exception occurred on unserializing the data."
      (some e))

/-- `dump_payload(obj)`. -/
def dumpPayload (s : Serializer α) (x : α) : Bytes := s.codec.dumps x

/-- `dumps(obj, salt)`. -/
def dumps (s : Serializer α) (x : α) (salt : Option Bytes := none) : Bytes :=
  (s.makeSigner salt).sign (s.dumpPayload x)

/-- The `loads` loop over a list of unsigners: the first that verifies wins
(its payload error, if any, propagates); otherwise the last signature error. -/
def loadsWith (s : Serializer α) (input : Bytes) : List Signer → Option BadSignature →
    Except BadData α
  | [], last => .error (last.getD ⟨"no signer", none⟩).toBadData
  | u :: us, _ =>
    match u.unsignImpl input with
    | .ok p => s.loadPayload p
    | .error e => s.loadsWith input us (some e)

/-- `loads(s, salt)`. The public `Serializer.loads` refines this. -/
def loadsImpl (s : Serializer α) (input : Bytes) (salt : Option Bytes := none) : Except BadData α :=
  s.loadsWith input (s.unsigners salt) none

/-- `loads_unsafe(s, salt)`: `(signature_valid, payload)`. A valid signature
over an unloadable payload still raises `BadPayload`, as upstream. -/
def loadsUnsafe (s : Serializer α) (input : Bytes) (salt : Option Bytes := none) :
    Except BadData (Bool × Option α) :=
  match s.loadsImpl input salt with
  | .ok x => .ok (true, some x)
  | .error e =>
    if e.isBadSignature then
      match e.payload with
      | none => .ok (false, none)
      | some p =>
        match s.loadPayload p with
        | .ok x => .ok (false, some x)
        | .error _ => .ok (false, none)
    else .error e

end Serializer

namespace TimedSerializer

variable {α : Type}

/-- `make_signer(salt)`, as a timestamp signer. -/
def makeSigner (s : TimedSerializer α) (salt : Option Bytes := none) : TimestampSigner :=
  ⟨s.toSerializer.makeSigner salt⟩

/-- `dumps(obj, salt)` at time `now`. -/
def dumps (s : TimedSerializer α) (x : α) (now : UInt64) (salt : Option Bytes := none) : Bytes :=
  (s.makeSigner salt).sign (s.toSerializer.dumpPayload x) now

/-- The timed `loads` loop: like `Serializer.loadsWith`, but a
`SignatureExpired` stops the search (the signature was good, only old). -/
def loadsWith (s : TimedSerializer α) (maxAge : Option Nat) (now : UInt64) (input : Bytes) :
    List Signer → Option BadData → Except BadData (α × UInt64)
  | [], last => .error (last.getD (.badSignature "no signer" none))
  | u :: us, _ =>
    match (TimestampSigner.mk u).unsignImpl maxAge now input with
    | .ok (p, ts) => (s.toSerializer.loadPayload p).map fun x => (x, ts)
    | .error e =>
      if e.isSignatureExpired then .error e
      else if e.isBadSignature then s.loadsWith maxAge now input us (some e)
      else .error e

/-- `loads(s, max_age, return_timestamp=True, salt)` at time `now`. The
public `TimedSerializer.loads` refines this. -/
def loadsImpl (s : TimedSerializer α) (input : Bytes) (maxAge : Option Nat := none) (now : UInt64)
    (salt : Option Bytes := none) : Except BadData (α × UInt64) :=
  s.loadsWith maxAge now input (s.toSerializer.unsigners salt) none

/-- `loads_unsafe(s, max_age, salt)`. -/
def loadsUnsafe (s : TimedSerializer α) (input : Bytes) (maxAge : Option Nat := none)
    (now : UInt64) (salt : Option Bytes := none) : Except BadData (Bool × Option α) :=
  match s.loadsImpl input maxAge now salt with
  | .ok (x, _) => .ok (true, some x)
  | .error e =>
    if e.isBadSignature then
      match e.payload with
      | none => .ok (false, none)
      | some p =>
        match s.toSerializer.loadPayload p with
        | .ok x => .ok (false, some x)
        | .error _ => .ok (false, none)
    else .error e

end TimedSerializer

end LeanItsdangerous
