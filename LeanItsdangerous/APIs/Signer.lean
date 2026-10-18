import LeanItsdangerous.Proofs.Verified

/-!
# APIs: constructors and the refined decoders

What users call. Constructors check upstream's constructor errors at
runtime (`ValueError` for a bad separator, `IndexError` for an empty key
list) and return a value whose invariants then hold by type. The decoders
(`unsign`, `loads`) return refinements: an `ok` result carries the proof of
what it means, from `Proofs/`.

Signing (`Signer.sign`, `TimestampSigner.sign`, `Serializer.dumps`,
`TimedSerializer.dumps`) needs no refinement: its result is its defining
equation, and the round trip theorems are stated about it.

Time is explicit: the timestamped operations take `now`, seconds since the
Unix epoch, where upstream reads `time.time()`.
-/

namespace LeanItsdangerous

/-- Upstream's `ValueError` message for a separator that may occur inside a
signature. -/
def separatorError : String :=
  "The given separator cannot be used because it may be contained in the signature itself. " ++
  "ASCII letters, digits, and '-_=' must not be used."

/-- Upstream's default serializer salt `b"itsdangerous"`. -/
def defaultSerializerSalt : Bytes := Bytes.ofString "itsdangerous"

namespace SignerConfig

/-- A configuration with the default separator `.`, which needs no check.
`algorithm = none` means upstream's default `HMACAlgorithm(digest)`. -/
def default (keyDerivation : KeyDerivation := .djangoConcat) (digest : Hash := sha1)
    (algorithm : Option SigningAlgorithm := none) : SignerConfig where
  sep := defaultSep
  h_sep := defaultSep_valid
  keyDerivation := keyDerivation
  digest := digest
  algorithm := algorithm.getD (hmacAlgorithm digest)

/-- A configuration with a chosen separator: `ValueError` (here an `error`)
if the separator is empty or contains an alphabet byte. -/
def new (sep : Bytes) (keyDerivation : KeyDerivation := .djangoConcat) (digest : Hash := sha1)
    (algorithm : Option SigningAlgorithm := none) : Except String SignerConfig :=
  if h : ValidSep sep then
    .ok { sep, h_sep := h, keyDerivation, digest, algorithm := algorithm.getD (hmacAlgorithm digest) }
  else .error separatorError

end SignerConfig

namespace Signer

/-- A signer from a configuration, keys and salt. `IndexError` (here an
`error`) for an empty key list, which upstream raises on first use. -/
def ofConfig (cfg : SignerConfig) (secretKeys : List Bytes) (salt : Bytes := defaultSignerSalt) :
    Except String Signer :=
  if h : secretKeys = [] then .error "list index out of range"
  else .ok { cfg with secretKeys, h_keys := h, salt }

/-- `Signer(secret_key)` with every default (`.`, django-concat, HMAC-SHA1,
salt `itsdangerous.Signer`). -/
def ofKey (secretKey : Bytes) (salt : Bytes := defaultSignerSalt)
    (cfg : SignerConfig := SignerConfig.default) : Signer :=
  { cfg with secretKeys := [secretKey], h_keys := List.cons_ne_nil _ _, salt }

/-- `Signer([k1, k2, ...])`, oldest to newest; the newest signs. -/
def ofKeys (secretKeys : List Bytes) (h : secretKeys ≠ []) (salt : Bytes := defaultSignerSalt)
    (cfg : SignerConfig := SignerConfig.default) : Signer :=
  { cfg with secretKeys, h_keys := h, salt }

/-- `unsign(signed_value)`. On success, the value together with the proof
that a key in the list signed it. -/
def unsign (s : Signer) (input : Bytes) :
    Except BadSignature {v : Bytes // ∃ k ∈ s.secretKeys, s.signWith k v = input} :=
  match h : s.unsignImpl input with
  | .ok v => .ok ⟨v, unsign_sound h⟩
  | .error e => .error e

theorem unsign_map_val (s : Signer) (input : Bytes) :
    (s.unsign input).map Subtype.val = s.unsignImpl input := by
  unfold unsign; split <;> rename_i h <;> simp [h, Except.map]

/-- The round trip, through the refined API. -/
theorem unsign_sign_val (s : Signer) (v : Bytes) :
    (s.unsign (s.sign v)).map Subtype.val = .ok v := by
  rw [unsign_map_val, unsign_sign]

end Signer

namespace TimestampSigner

/-- `TimestampSigner(secret_key)` with every default: what Starlette's
`SessionMiddleware` constructs. -/
def ofKey (secretKey : Bytes) (salt : Bytes := defaultSignerSalt)
    (cfg : SignerConfig := SignerConfig.default) : TimestampSigner :=
  ⟨Signer.ofKey secretKey salt cfg⟩

/-- `TimestampSigner([k1, k2, ...])`. -/
def ofKeys (secretKeys : List Bytes) (h : secretKeys ≠ []) (salt : Bytes := defaultSignerSalt)
    (cfg : SignerConfig := SignerConfig.default) : TimestampSigner :=
  ⟨Signer.ofKeys secretKeys h salt cfg⟩

/-- `unsign(signed_value, max_age, return_timestamp=True)` at time `now`. On
success, the value and timestamp, with the proof that a key in the list
signed them and that the timestamp passes the age check. -/
def unsign (t : TimestampSigner) (input : Bytes) (maxAge : Option Nat := none) (now : UInt64) :
    Except BadData {r : Bytes × UInt64 // t.SignedBy input r.1 r.2 ∧ AgeOk maxAge now r.2} :=
  match h : t.unsignImpl maxAge now input with
  | .ok r => .ok ⟨r, unsign_sound h⟩
  | .error e => .error e

theorem unsign_map_val (t : TimestampSigner) (input : Bytes) (maxAge : Option Nat) (now : UInt64) :
    (t.unsign input maxAge now).map Subtype.val = t.unsignImpl maxAge now input := by
  unfold unsign; split <;> rename_i h <;> simp [h, Except.map]

end TimestampSigner

namespace Serializer

variable {α : Type}

/-- `Serializer(secret_key, salt, serializer, signer_kwargs, fallback_signers)`.
`salt = none` is upstream's `salt=None` (the signer's own default). -/
def new (secretKeys : List Bytes) (codec : Codec α) (salt : Option Bytes := some defaultSerializerSalt)
    (signer : SignerConfig := SignerConfig.default) (fallbacks : List SignerConfig := []) :
    Except String (Serializer α) :=
  if h : secretKeys = [] then .error "list index out of range"
  else .ok { secretKeys, h_keys := h, salt, codec, signer, fallbacks }

/-- A serializer with a single key and every other default. -/
def ofKey (secretKey : Bytes) (codec : Codec α) (salt : Option Bytes := some defaultSerializerSalt)
    (signer : SignerConfig := SignerConfig.default) (fallbacks : List SignerConfig := []) :
    Serializer α :=
  { secretKeys := [secretKey], h_keys := List.cons_ne_nil _ _, salt, codec, signer, fallbacks }

/-- `loads(s, salt)`. On success, the object with the proof that it is a
payload signed by one of the unsigners. -/
def loads (s : Serializer α) (input : Bytes) (salt : Option Bytes := none) :
    Except BadData {x : α // s.SignedBy salt input x} :=
  match h : s.loadsImpl input salt with
  | .ok x => .ok ⟨x, loads_sound h⟩
  | .error e => .error e

theorem loads_map_val (s : Serializer α) (input : Bytes) (salt : Option Bytes) :
    (s.loads input salt).map Subtype.val = s.loadsImpl input salt := by
  unfold loads; split <;> rename_i h <;> simp [h, Except.map]

end Serializer

/-- `URLSafeSerializer`: a serializer whose payload is base64url-encoded,
safe in URLs and cookies. -/
def URLSafeSerializer.ofKey {α : Type} (secretKey : Bytes) (codec : Codec α)
    (salt : Option Bytes := some defaultSerializerSalt)
    (signer : SignerConfig := SignerConfig.default) (fallbacks : List SignerConfig := []) :
    Serializer α :=
  Serializer.ofKey secretKey (urlSafeCodec codec) salt signer fallbacks

namespace TimedSerializer

variable {α : Type}

/-- `TimedSerializer(secret_key, ...)` with a single key. -/
def ofKey (secretKey : Bytes) (codec : Codec α) (salt : Option Bytes := some defaultSerializerSalt)
    (signer : SignerConfig := SignerConfig.default) (fallbacks : List SignerConfig := []) :
    TimedSerializer α :=
  ⟨Serializer.ofKey secretKey codec salt signer fallbacks⟩

/-- `loads(s, max_age, return_timestamp=True, salt)` at time `now`. On
success, the object and its timestamp with the proof that they come from a
signed, fresh payload. -/
def loads (s : TimedSerializer α) (input : Bytes) (maxAge : Option Nat := none) (now : UInt64)
    (salt : Option Bytes := none) :
    Except BadData {r : α × UInt64 // s.SignedBy salt maxAge now input r.1 r.2} :=
  match h : s.loadsImpl input maxAge now salt with
  | .ok r => .ok ⟨r, loads_sound h⟩
  | .error e => .error e

theorem loads_map_val (s : TimedSerializer α) (input : Bytes) (maxAge : Option Nat) (now : UInt64)
    (salt : Option Bytes) :
    (s.loads input maxAge now salt).map Subtype.val = s.loadsImpl input maxAge now salt := by
  unfold loads; split <;> rename_i h <;> simp [h, Except.map]

end TimedSerializer

/-- `URLSafeTimedSerializer`. -/
def URLSafeTimedSerializer.ofKey {α : Type} (secretKey : Bytes) (codec : Codec α)
    (salt : Option Bytes := some defaultSerializerSalt)
    (signer : SignerConfig := SignerConfig.default) (fallbacks : List SignerConfig := []) :
    TimedSerializer α :=
  TimedSerializer.ofKey secretKey (urlSafeCodec codec) salt signer fallbacks

end LeanItsdangerous
