import LeanItsdangerous.Proofs.Serializer

/-!
# APIs: the public surface, shaped like itsdangerous

```python
s = Signer("secret-key")                       # Signer.new "secret-key"
s.sign("my string")                            # s.sign "my string"
s.unsign(token)                                # s.unsign token
TimestampSigner("secret-key").unsign(t, max_age=5)   # (TimestampSigner.new "secret-key").unsign t (maxAge := some 5) now
URLSafeTimedSerializer("secret-key", salt="auth")    # URLSafeTimedSerializer.new "secret-key" (salt := "auth")
```

Names, argument order and defaults follow upstream. With `open
LeanItsdangerous`, a string literal is accepted for any bytes argument (as
upstream accepts `str`), a secret key may be one key or a non-empty list of
keys (oldest to newest), and a separator literal is checked at compile time
(`by decide`), where upstream raises `ValueError` at construction.

The decoders (`unsign`, `loads`) return refinements: an `ok` result carries
the proof of what it means. `Except.val` forgets the proof; the headline
theorems (`Proofs/Public.lean`) are stated with it, e.g.
`(s.unsign (s.sign v)).val = .ok v`.

Time is an argument `now` (seconds since the epoch); `getTimestamp`
(`Clock.lean`) reads it.
-/

namespace LeanItsdangerous

/-- Forget the proof carried by a refined result. -/
def _root_.Except.val {ε α : Type} {p : α → Prop} (r : Except ε {x : α // p x}) : Except ε α :=
  r.map Subtype.val

/-- Refine a result by a property every `ok` value is proved to have. -/
def _root_.Except.refine {ε α : Type} {p : α → Prop} (r : Except ε α)
    (h : ∀ x, r = .ok x → p x) : Except ε {x : α // p x} :=
  match r, h with
  | .ok x, h => .ok ⟨x, h x rfl⟩
  | .error e, _ => .error e

/-- Refining then forgetting is the identity: the one lemma behind every
public decoder's `*_val` equation. -/
theorem _root_.Except.val_refine {ε α : Type} {p : α → Prop} (r : Except ε α)
    (h : ∀ x, r = .ok x → p x) : (r.refine h).val = r := by
  cases r <;> rfl

/-- With `open LeanItsdangerous`, `(maxAge := 5)` reads as upstream's
`max_age=5`. -/
scoped instance {n : Nat} : OfNat (Option Nat) n := ⟨some n⟩

/-- Upstream's `ValueError` message for a separator that may occur inside a
signature. -/
def separatorError : String :=
  "The given separator cannot be used because it may be contained in the signature itself. " ++
  "ASCII letters, digits, and '-_=' must not be used."

/-- Check a separator only known at run time (a literal is checked at compile
time instead): upstream's `ValueError`. -/
def checkSeparator (sep : Bytes) : Except String {s : Bytes // ValidSep s} :=
  if h : ValidSep sep then .ok ⟨sep, h⟩ else .error separatorError

/-- Upstream's default serializer salt `b"itsdangerous"`. -/
def defaultSerializerSalt : Bytes := Bytes.ofString "itsdangerous"

/-- What upstream's `secret_key` accepts (`_make_keys_list`): one key as text
or bytes, or a list of keys from oldest to newest (the newest signs). -/
class IntoKeys (κ : Type) where
  keys : κ → List Bytes

instance : IntoKeys String := ⟨fun k => [Bytes.ofString k]⟩
instance : IntoKeys Bytes := ⟨fun k => [k]⟩
instance : IntoKeys (List String) := ⟨List.map Bytes.ofString⟩
instance : IntoKeys (List Bytes) := ⟨id⟩

/-- The default proof that a key list is non-empty (upstream raises
`IndexError` on first use otherwise): `simp` for a single key, `decide` for
a list, literal or defined. -/
macro "keys_nonempty" : tactic => `(tactic| first | decide | (simp [IntoKeys.keys]; done))

/-- Upstream's `signer_kwargs`: everything about a signer but its keys and
salt, with upstream's defaults. -/
structure SignerKwargs where
  /-- `sep`, default `b"."` -/
  sep : Bytes := defaultSep
  h_sep : ValidSep sep := by decide
  /-- `key_derivation`, default `"django-concat"` -/
  keyDerivation : KeyDerivation := .djangoConcat
  /-- `digest_method`, default SHA-1 -/
  digestMethod : Hash := sha1
  /-- `algorithm`, default `HMACAlgorithm(digest_method)` -/
  algorithm : Option SigningAlgorithm := none

/-- The configuration the implementation uses. -/
def SignerKwargs.toConfig (k : SignerKwargs) : SignerConfig where
  sep := k.sep
  h_sep := k.h_sep
  keyDerivation := k.keyDerivation
  digest := k.digestMethod
  algorithm := k.algorithm.getD (hmacAlgorithm k.digestMethod)

namespace Signer

/-- `Signer(secret_key, salt, sep, key_derivation, digest_method, algorithm)`. -/
def new {κ : Type} [IntoKeys κ] (secretKey : κ) (salt : Bytes := defaultSignerSalt)
    (sep : Bytes := defaultSep) (keyDerivation : KeyDerivation := .djangoConcat)
    (digestMethod : Hash := sha1) (algorithm : Option SigningAlgorithm := none)
    (h_keys : IntoKeys.keys secretKey ≠ [] := by keys_nonempty)
    (h_sep : ValidSep sep := by decide) : Signer :=
  { ({ sep, h_sep, keyDerivation, digestMethod, algorithm } : SignerKwargs).toConfig with
    secretKeys := IntoKeys.keys secretKey, h_keys, salt }

/-- `unsign(signed_value)`. On success, the value together with the proof
that a key in the list signed it. -/
def unsign (s : Signer) (signedValue : Bytes) :
    Except BadSignature {v : Bytes // ∃ k ∈ s.secretKeys, s.signWith k v = signedValue} :=
  (s.unsignImpl signedValue).refine fun _ h => unsignImpl_sound h

theorem unsign_val (s : Signer) (signedValue : Bytes) :
    (s.unsign signedValue).val = s.unsignImpl signedValue := Except.val_refine _ _

end Signer

namespace TimestampSigner

/-- `TimestampSigner(secret_key, salt, sep, key_derivation, digest_method,
algorithm)`: what Starlette's `SessionMiddleware` constructs. -/
def new {κ : Type} [IntoKeys κ] (secretKey : κ) (salt : Bytes := defaultSignerSalt)
    (sep : Bytes := defaultSep) (keyDerivation : KeyDerivation := .djangoConcat)
    (digestMethod : Hash := sha1) (algorithm : Option SigningAlgorithm := none)
    (h_keys : IntoKeys.keys secretKey ≠ [] := by keys_nonempty)
    (h_sep : ValidSep sep := by decide) : TimestampSigner :=
  ⟨Signer.new secretKey salt sep keyDerivation digestMethod algorithm h_keys h_sep⟩

/-- `unsign(signed_value, max_age, return_timestamp=True)` at time `now`. On
success, the value and timestamp, with the proof that a key in the list
signed them and that the timestamp passes the age check. -/
def unsign (t : TimestampSigner) (signedValue : Bytes) (maxAge : Option Nat := none)
    (now : UInt64) :
    Except BadData {r : Bytes × UInt64 // t.SignedBy signedValue r.1 r.2 ∧ AgeOk maxAge now r.2} :=
  (t.unsignImpl maxAge now signedValue).refine fun _ h => unsignImpl_sound h

theorem unsign_val (t : TimestampSigner) (signedValue : Bytes) (maxAge : Option Nat) (now : UInt64) :
    (t.unsign signedValue maxAge now).val = t.unsignImpl maxAge now signedValue :=
  Except.val_refine _ _

end TimestampSigner

namespace Serializer

variable {α : Type}

/-- `Serializer(secret_key, salt, serializer, signer_kwargs, fallback_signers)`.
The payload codec is found by type (`Codec α`), as upstream defaults to
`json`; pass `serializer` to choose another. `salt := none` is
upstream's `salt=None` (the signer's own default salt). -/
def new {κ : Type} [IntoKeys κ] [c : Codec α] (secretKey : κ)
    (salt : Option Bytes := some defaultSerializerSalt) (serializer : Codec α := c)
    (signerKwargs : SignerKwargs := {}) (fallbackSigners : List SignerKwargs := [])
    (h_keys : IntoKeys.keys secretKey ≠ [] := by keys_nonempty) : Serializer α where
  secretKeys := IntoKeys.keys secretKey
  h_keys := h_keys
  salt := salt
  codec := serializer
  signer := signerKwargs.toConfig
  fallbacks := fallbackSigners.map SignerKwargs.toConfig

/-- `loads(s, salt)`. On success, the object with the proof that it is a
payload signed by one of the unsigners. -/
def loads (s : Serializer α) (token : Bytes) (salt : Option Bytes := none) :
    Except BadData {x : α // s.SignedBy salt token x} :=
  (s.loadsImpl token salt).refine fun _ h => loadsImpl_sound h

theorem loads_val (s : Serializer α) (token : Bytes) (salt : Option Bytes) :
    (s.loads token salt).val = s.loadsImpl token salt := Except.val_refine _ _

end Serializer

/-- `URLSafeSerializer`: a serializer whose payload is base64url-encoded,
safe in URLs and cookies. -/
abbrev URLSafeSerializer (α : Type) := Serializer α

/-- `URLSafeSerializer(secret_key, salt, serializer, signer_kwargs,
fallback_signers)`. The default payload codec is the type's `CompactCodec`
(upstream's `_CompactJSON`). -/
def URLSafeSerializer.new {α κ : Type} [IntoKeys κ] [compact : CompactCodec α] (secretKey : κ)
    (salt : Option Bytes := some defaultSerializerSalt) (serializer : Codec α := compact.codec)
    (signerKwargs : SignerKwargs := {}) (fallbackSigners : List SignerKwargs := [])
    (h_keys : IntoKeys.keys secretKey ≠ [] := by keys_nonempty) : URLSafeSerializer α :=
  Serializer.new (c := urlSafeCodec serializer) secretKey salt (urlSafeCodec serializer) signerKwargs
    fallbackSigners h_keys

namespace TimedSerializer

variable {α : Type}

/-- `TimedSerializer(secret_key, salt, serializer, signer_kwargs,
fallback_signers)`. -/
def new {κ : Type} [IntoKeys κ] [c : Codec α] (secretKey : κ)
    (salt : Option Bytes := some defaultSerializerSalt) (serializer : Codec α := c)
    (signerKwargs : SignerKwargs := {}) (fallbackSigners : List SignerKwargs := [])
    (h_keys : IntoKeys.keys secretKey ≠ [] := by keys_nonempty) : TimedSerializer α :=
  ⟨Serializer.new (c := serializer) secretKey salt serializer signerKwargs fallbackSigners h_keys⟩

/-- `loads(s, max_age, return_timestamp=True, salt)` at time `now`. On
success, the object and its timestamp with the proof that they come from a
signed, fresh payload. -/
def loads (s : TimedSerializer α) (token : Bytes) (maxAge : Option Nat := none) (now : UInt64)
    (salt : Option Bytes := none) :
    Except BadData {r : α × UInt64 // s.SignedBy salt maxAge now token r.1 r.2} :=
  (s.loadsImpl token maxAge now salt).refine fun _ h => loadsImpl_sound h

theorem loads_val (s : TimedSerializer α) (token : Bytes) (maxAge : Option Nat) (now : UInt64)
    (salt : Option Bytes) :
    (s.loads token maxAge now salt).val = s.loadsImpl token maxAge now salt :=
  Except.val_refine _ _

end TimedSerializer

/-- `URLSafeTimedSerializer`. -/
abbrev URLSafeTimedSerializer (α : Type) := TimedSerializer α

/-- `URLSafeTimedSerializer(secret_key, salt, serializer, signer_kwargs,
fallback_signers)`. -/
def URLSafeTimedSerializer.new {α κ : Type} [IntoKeys κ] [compact : CompactCodec α]
    (secretKey : κ) (salt : Option Bytes := some defaultSerializerSalt)
    (serializer : Codec α := compact.codec) (signerKwargs : SignerKwargs := {})
    (fallbackSigners : List SignerKwargs := [])
    (h_keys : IntoKeys.keys secretKey ≠ [] := by keys_nonempty) : URLSafeTimedSerializer α :=
  TimedSerializer.new (c := urlSafeCodec serializer) secretKey salt (urlSafeCodec serializer)
    signerKwargs fallbackSigners h_keys

end LeanItsdangerous
