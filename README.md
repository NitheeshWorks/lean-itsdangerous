# lean-itsdangerous

[![Lean 4](https://img.shields.io/badge/built%20with-Lean%204-blue.svg)](https://lean-lang.org)
[![Proofs](https://img.shields.io/badge/proofs-machine%20checked-brightgreen.svg)](CONTRIBUTING.md#verification)

A clean-room port of [itsdangerous](https://github.com/pallets/itsdangerous) to Lean 4: HMAC-signed and timestamped payloads (Signer, TimestampSigner) with a proved signature-format round trip.

Part of the verified FastAPI stack: [lean-fastapi](https://github.com/NitheeshWorks/lean-fastapi)
and its dependencies, each ported as its own repo with its proofs. This one
depends on: none (Lean core only).

## What "verified" means here

* Public functions take the weakest precondition they need and return the
  strongest postcondition, as a refinement type `{r // Post r}` or an
  `Except` of one. Invariants live in types, not comments.
* Every theorem is machine-checked. CI fails on `sorry` and on any axiom
  beyond Lean's own `propext`, `Quot.sound` and `Classical.choice`.
* What is tested rather than proved is listed, with the reason, in
  [CONTRIBUTING.md](CONTRIBUTING.md#verification) and in
  `docs/traceability.toml`.

## Getting started

```
lake build            # library, proofs, and both test executables
lake exe props        # property tests (seeded; `lake exe props 42`)
lake exe conformance  # cases re-expressed from the upstream test suite
scripts/check.sh      # the whole CI gate, locally
```

Toolchain: `leanprover/lean4:v4.35.0` (pinned in `lean-toolchain`; `elan` installs it).

## Usage

```lean
import LeanItsdangerous
open LeanItsdangerous

-- Starlette's SessionMiddleware: TimestampSigner(secret_key)
def signer := TimestampSigner.ofKey (Bytes.ofString "secret-key")

def token := signer.sign 1308874145 (Bytes.ofString "payload")   -- now = 1308874145

-- unsign returns a refinement: on success, a proof that a listed key signed it
#eval match signer.unsign token (maxAge := some 3600) (now := 1308874200) with
  | .ok r => s!"ok {r.val.1}"
  | .error e => e.message
```

Public API (`LeanItsdangerous.APIs`): `Signer.ofKey`/`ofKeys`/`ofConfig`,
`Signer.sign`/`unsign`/`validate`; `TimestampSigner.ofKey`/`sign`/`unsign`;
`Serializer.ofKey`/`new`/`dumps`/`loads`/`loadsUnsafe`; `TimedSerializer`,
`URLSafeSerializer.ofKey`, `URLSafeTimedSerializer.ofKey`; `SignerConfig.default`
/ `SignerConfig.new` (separator, key derivation, digest, algorithm); the
`BadData` hierarchy; `sha1`, `sha256`, `sha512`, `hmac`; `b64encode`,
`base64Decode`. A serializer takes a `Codec α` (a `dumps`/`loads` pair):
bring your own JSON (lean-json).

## Status

Signer, TimestampSigner, Serializer, TimedSerializer and the URL-safe
serializers, with key rotation and fallback signers. What is proved, what is
tested, and the deviations from upstream (no zlib, explicit time, stricter
separator check) are listed in [CONTRIBUTING.md](CONTRIBUTING.md#verification).

## License

MIT, see [LICENSE](LICENSE). Upstream attribution is in [NOTICE](NOTICE).
