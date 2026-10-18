# lean-itsdangerous

[![Lean 4](https://img.shields.io/badge/built%20with-Lean%204-blue.svg)](https://lean-lang.org)
[![Proofs](https://img.shields.io/badge/proofs-machine%20checked-brightgreen.svg)](CONTRIBUTING.md#verification)

A clean-room port of [itsdangerous](https://github.com/pallets/itsdangerous) to Lean 4: HMAC-signed and timestamped payloads (Signer, TimestampSigner) with a proved signature-format round trip.

Part of the verified FastAPI stack: [lean-fastapi](https://github.com/NitheeshWorks/lean-fastapi)
and its dependencies, each ported as its own repo with its proofs. This one
depends on: none (Lean core only).

## A simple example

itsdangerous's own example, translated:

```python
from itsdangerous import URLSafeSerializer
auth_s = URLSafeSerializer("secret key", "auth")
token = auth_s.dumps({"id": 5, "name": "itsdangerous"})
# eyJpZCI6NSwibmFtZSI6Iml0c2Rhbmdlcm91cyJ9.6YP6T0BaO67XP--9UzTrmurXSmg
data = auth_s.loads(token)
```

```lean
import LeanItsdangerous
open LeanItsdangerous

def authS := URLSafeSerializer.new "secret key" "auth"
def token := authS.dumps "{\"id\":5,\"name\":\"itsdangerous\"}"
-- b'eyJpZCI6NSwibmFtZSI6Iml0c2Rhbmdlcm91cyJ9.6YP6T0BaO67XP--9UzTrmurXSmg'
#eval authS.loads token            -- Except.ok "{\"id\":5,\"name\":\"itsdangerous\"}"
```

The token is byte-identical to upstream's. The payload type picks its codec
(`[Codec α]`): `String` is UTF-8 text such as JSON you have rendered, `Bytes`
is raw, and lean-json provides `Json`.

## Signing, timestamps, rotation

```lean
def s := Signer.new "secret-key"
#eval s.sign "my string"                          -- b'my string.wh6tMHxLgJqB6oY1uT73iMlyrOA'
#eval s.unsign "my string.wh6tMHxLgJqB6oY1uT73iMlyrOA"   -- Except.ok b'my string'

-- TimestampSigner("secret-key"): what Starlette's SessionMiddleware uses
def ts := TimestampSigner.new "secret-key"
def stamped := ts.sign "foo" 1700000000            -- sign(value) at time now
#eval ts.unsign stamped (maxAge := 5) (now := 1700000010)
-- Except.error (BadData.signatureExpired "Signature age 10 > 5 seconds" ...)

-- Signer(["old key", "new key"], sep="|"): verifies with either, signs with the newest
def rotated := Signer.new ["old key", "new key"] (sep := "|")

-- URLSafeTimedSerializer(SECRET_KEY, salt="activate") with the real clock
def main : IO Unit := do
  let now ← getTimestamp                           -- upstream's get_timestamp()
  let u := URLSafeTimedSerializer.new "secret-key" (salt := "activate")
  let t := u.dumps "{\"user\":42}" now
  IO.println (repr (u.loads t (maxAge := 3600) now)).pretty
```

`examples/Quickstart.lean` (`lake exe quickstart`) is this page, compiled.
[`examples/`](examples/README.md) translates the rest of the itsdangerous
docs (signer, timed, serializer, URL-safe, concepts, exceptions), each checked
against upstream's output.

Names, argument order and defaults are upstream's: `salt`
(`"itsdangerous.Signer"` for signers, `"itsdangerous"` for serializers),
`sep` (`"."`), `keyDerivation` (`.djangoConcat`), `digestMethod` (`sha1`),
`algorithm` (HMAC), `signerKwargs`, `fallbackSigners`. A string is accepted
wherever upstream accepts `str` or `bytes`, and a non-empty list of keys
wherever it accepts a list. What differs, and why, is listed in
[CONTRIBUTING.md](CONTRIBUTING.md#deviations-from-upstream): time is an
argument `now`; a separator literal is checked at compile time rather than
raising `ValueError`; there is no zlib.

`unsign` and `loads` return refinements: an `ok` result carries the proof of
what it means (`{v // ∃ k ∈ s.secretKeys, s.signWith k v = token}` for
`Signer.unsign`). It prints and coerces as the plain value; `.val` forgets
the proof explicitly.

## What is proved

Every theorem is machine-checked; CI fails on `sorry` and on any axiom beyond
`propext`, `Quot.sound` and `Classical.choice`. The headline theorems, each
with its slot in `LeanItsdangerous/Proofs/Verified.lean`:

| Property | Lean statement |
|---|---|
| Unsigning what was signed returns it | `Signer.unsign_sign : (s.unsign (s.sign v)).val = .ok v` |
| Key rotation: any listed key verifies | `Signer.unsign_signWith : k ∈ s.secretKeys → (s.unsign (s.signWith k v)).val = .ok v` |
| `unsign` succeeds exactly on signed values | `Signer.unsign_eq_ok_iff : (s.unsign t).val = .ok v ↔ ∃ k ∈ s.secretKeys, s.signWith k v = t` |
| A one-byte forgery is an HMAC collision | `Signer.unsign_tampered : (s.unsign ((s.signWith k v).set i b)).val = .ok r → r = v ∨ ∃ k' ∈ s.secretKeys, r ≠ v ∧ s.rawSignature k' r = s.rawSignature k v` |
| The signature comparison is equality | `ctEq_iff : ctEq a b = true ↔ a = b` |
| Timestamped round trip within `max_age` | `TimestampSigner.unsign_sign : AgeOk maxAge now ts → (t.unsign (t.sign v ts) maxAge now).val = .ok (v, ts)` |
| `max_age` is monotone | `TimestampSigner.unsign_maxAge_mono : m ≤ m' → (t.unsign x (some m) now).val = .ok r → (t.unsign x (some m') now).val = .ok r` |
| Expired signatures raise `SignatureExpired` | `TimestampSigner.unsign_expired` |
| `loads (dumps x) = x` | `Serializer.loads_dumps : s.codec.Lawful → (s.loads (s.dumps x salt) salt).val = .ok x`, and `TimedSerializer.loads_dumps` |
| Strings are encoded as UTF-8, exactly as Lean core does | `Bytes.ofString_eq_toUTF8 : Bytes.ofString s = s.toUTF8.data.toList` |
| The codec law composes | `Codec.Lawful.andThen : inner.Lawful → outer.Lawful → (inner.andThen outer).Lawful` |
| base64url, integer and timestamp codecs are lawful | `base64Codec_lawful`, `intCodec_lawful`, `timestampCodec_lawful`, `urlSafeCodec_lawful` |

The tampering theorem assumes nothing about HMAC: it shows a successful
one-byte forgery *is* a collision. SHA-1/SHA-256/SHA-512 and HMAC are tested
against FIPS 180-4 and RFC 2202/4231 vectors, not proved; tokens are checked
byte for byte against upstream itsdangerous 2.2.0.

## Getting started

```
lake build            # library, proofs, tests and the quickstart
lake exe props        # property tests (seeded; `lake exe props 42`)
lake exe conformance  # cases re-expressed from the upstream test suite
scripts/check.sh      # the whole CI gate, locally
```

Toolchain: `leanprover/lean4:v4.35.0` (pinned in `lean-toolchain`; `elan` installs it).

## License

MIT, see [LICENSE](LICENSE). Upstream attribution is in [NOTICE](NOTICE).
