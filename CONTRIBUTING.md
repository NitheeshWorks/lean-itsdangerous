# Contributing to lean-itsdangerous

`README.md` covers usage. This file covers the architecture, the verification
rules, the repository layout and the conventions, and is the document to keep
current when the code changes.

## Architecture

`LeanItsdangerous/` is layered bottom-up; each layer imports only the ones below it, so a
proof at one layer rewrites with lemmas from beneath it instead of unfolding
to bytes:

| Directory | Holds | Proved? |
|---|---|---|
| `DataTypes/` | structures and inductives; invariants are fields; the `Codec` class and its law | n/a |
| `RepoImpl/` | executable definitions (`*Impl` for the decoders); total, structural recursion | subject of proofs |
| `Specifications/Timed.lean`, `Serializer.lean` | the predicates the refined results carry (`SignedBy`, `AgeOk`) | the contract |
| `Proofs/` (all but `Public`, `Verified`) | lemmas about the implementation (`unsignImpl_*`, `loadsImpl_*`) and the codec theory | yes |
| `APIs/` | the public surface, shaped like itsdangerous, returning refinements | by construction |
| `Specifications/Spec.lean` | the headline properties, stated about the public functions | the contract |
| `Proofs/Public.lean` | the headline theorems; `Proofs/Verified.lean` bundles one `Verified<Layer>` per layer | yes |
| `Clock.lean` | the only effectful module: `getTimestamp` reads the wall clock | no; one line over `Std.Time` |

The public decoders need the implementation's soundness lemmas to build their
refinements, and the headline theorems are stated about the public
decoders, which is why the headline specification and proofs sit above
`APIs/`.

The codec theory (`DataTypes/Codec.lean`, `Proofs/Codec.lean`) is the
general lemma behind every round trip: `Codec.Lawful.andThen` is proved once,
and the base64url, integer, timestamp and URL-safe payload codecs are
instances. It is shaped to move into the shared theory library (STYLE.md
section 2) unchanged; tokens are separator-delimited, so the law is the
whole-buffer form and the separator split is the lemma `rsplit_append`.

Everything except `Clock.lean` is a pure function. This is
load-bearing: a round-trip property of a function is an equation that
`omega` and `simp` attack directly; the same property of a procedure would
be a Hoare triple over a heap.

## Verification <a name="verification"></a>

* **Weak preconditions, strong postconditions.** A public function takes the
  minimal hypothesis its body needs (usually none; the refinement lives in the
  input type) and returns the strongest useful statement, typically a round
  trip or a membership, as `{r // Post r}` or `Except Err {r // Post r}`.
* **Refinement types are subtypes with `Decidable` predicates**, so the same
  predicate is checked at runtime (`if h : P x`) and used in proofs.
* **Totality.** No `partial def` or `unsafe` under `LeanItsdangerous/`. Byte parsers recurse
  on a `Nat` fuel equal to the remaining input, with a progress lemma per
  production.
* **`_ext` lemmas.** A decoder lemma holds on any continuation of the buffer and
  reports the final position, so field lemmas compose. Do not add a lemma that
  only holds at the end of a buffer; it is unusable one field later.
* **Numbers.** `Nat`/`Int`/decimal-as-rational in proofs. `Float` only at the
  boundary via `Float.toBits`. Never `bv_decide` or `native_decide`.
* **The gate.** `scripts/check.sh` runs what CI runs: build, `sorry` grep,
  `scripts/Axioms.lean` (every theorem under `LeanItsdangerous` reaches only `propext`,
  `Quot.sound`, `Classical.choice`), `lake exe props`, `lake exe conformance`,
  the traceability check.

### What is proved

`Proofs/Verified.lean` has one slot per headline property of
`Specifications/Spec.lean`, in four bundles. Each is an equation or an `↔`
about a public function (`Except.val` forgets a refined result's proof):

* `VerifiedCodec`: `Codec.Lawful.andThen`; `base64Codec_lawful`,
  `intCodec_lawful`, `timestampCodec_lawful`; `urlSafeCodec_lawful`;
  `base64Decode_base64Encode`; `Bytes.ofString_eq_toUTF8` (the structural
  UTF-8 encoder, which the kernel can evaluate on a separator literal, is
  core's `String.toUTF8` on every string).
* `VerifiedSigner`: `Signer.unsign_sign`, `Signer.unsign_signWith` (key
  rotation), `Signer.unsign_eq_ok_iff` (`unsign` succeeds exactly on values
  signed with a listed key), `Signer.unsign_tampered_value`,
  `Signer.unsign_tampered` (a one-byte change that still unsigns returns the
  original value or exhibits an explicit collision: a different value with
  the same raw signature under a listed key), `Signer.unsign_tampered_single`
  (with one key: `unsign` fails, or there is such a collision), `ctEq_iff`.
* `VerifiedTimestampSigner`: `TimestampSigner.unsign_sign` (with rotation)
  within `max_age`, `unsign_maxAge_mono`, `unsign_expired`.
* `VerifiedSerializer`: `Serializer.loads_dumps` and
  `TimedSerializer.loads_dumps` for any lawful payload codec.

Soundness of `unsign` and `loads` has no slot because it is the type: each
returns `{r // P r}`. `Signer.session_sign_verify` is the plan's name for
`Signer.unsign_sign`.

The tampering theorems assume nothing about collision resistance, which HMAC
can never be shown to have (a fixed-length output over an infinite domain has
collisions). They prove instead that a successful one-byte forgery *is* an
explicit collision of the signing algorithm, so tamper resistance reduces
exactly to collision resistance. Their only hypothesis about the algorithm is
a fixed signature length, discharged for HMAC by
`Signer.rawSignature_length_hmac` from the proved `Hash.h_len`.
`unsign_tampered_value` (any value `v'` put in front of `v`'s signature) is
the same: `unsign` fails, or `v'` collides with `v`.

### Tested, not proved

Listed here with the reason, and in `docs/traceability.toml` with
`status = "tested"`.

* **SHA-1, SHA-256, SHA-512** (`RepoImpl/Hash.lean`): bit-level hash
  correctness is out of scope for the proof effort. Tested against the
  FIPS 180-4 example vectors (`abc`, empty, the 448/896-bit messages, one
  million `a`) in `tests/Props.lean`. Their fixed output length is proved.
* **HMAC** (`RepoImpl/Hash.lean`): trusted for the same reason. Tested
  against RFC 2202 (HMAC-SHA1) and RFC 4231 cases 1–7 (HMAC-SHA256,
  HMAC-SHA512), plus seeded properties (long keys are hashed; a sampled
  no-collision smoke test on random pairs; flipping a byte of a signed string
  makes `unsign` fail) in `tests/Props.lean` and `tests/pbt/`.
* **Key derivations, timestamp signer and URL-safe tokens**: their bytes
  depend on the trusted hashes, so exact interoperability is checked by
  known-answer tokens generated from upstream itsdangerous 2.2.0 (every key
  derivation with SHA-1 and SHA-256, timestamps 0, 255, 256 and 2^32, a custom
  separator and salt, URL-safe serializers) in `tests/Conformance.lean`.

### Deviations from upstream

Each is a `status = "deviation"` or `"excluded"` row in
`docs/traceability.toml`.

* **Separator check is stricter.** Upstream rejects a separator only if it is
  a substring of the base64 alphabet; here any byte of it in the alphabet
  (or an empty separator) is rejected. This is what makes the split provably
  recover the signature. A separator literal is checked at compile time
  (`by decide`) instead of raising `ValueError`; `checkSeparator` checks one
  known only at run time.
* **Signature comparison** is `ctEq` on the canonical base64url encoding,
  where upstream runs `hmac.compare_digest` on decoded bytes. It agrees with
  upstream on every signature upstream emits and rejects the non-canonical
  spellings Python's lenient decoder accepts. Like `compare_digest` it
  checks the length first, then visits every byte pair, ORing their XORs,
  with no early exit; `ctEq_iff` proves it is equality. Lean's compiler gives
  no timing guarantee, so constant time is a property of the algorithm, not
  a promise about the machine code.
* **No zlib.** URL-safe `dumps` never compresses; `loads` rejects a
  compressed (`.`-prefixed) payload with `BadPayload`.
* **No built-in JSON.** The payload codec is a class (`Codec α`), found by
  type as upstream finds `json` by default; `String` (UTF-8 text) and
  `Bytes` instances are built in, and lean-json provides `Json`.
* **Time is explicit** (`now : UInt64`, seconds since the epoch, the last
  argument of `sign`/`dumps`/`unsign`/`loads`); `getTimestamp` reads the
  clock, as upstream's `get_timestamp`. Timestamps are returned as seconds,
  not `datetime`. `max_age` is a `Nat`.
* **base64 decoding** rejects bytes outside the alphabet, where Python's
  non-validating decoder skips them; trailing `=` is accepted as upstream.
* **MD5 is not provided** (SHA-1, SHA-256, SHA-512, or any `Hash`).
* **Unrepresentable or not applicable:** unknown key derivation (an
  inductive), the abstract `SigningAlgorithm` base, signer subclassing (a
  `SignerConfig` value instead), `dump`/`load` to file objects,
  `serializer_kwargs`.

## Tests

* `tests/Props.lean`: seeded property tests, no dependencies, under a second.
* `tests/Conformance.lean`: cases re-expressed from the upstream suite; each
  names the upstream test (`tests/test_x.py::test_y`).
* `tests/pbt/`: a separate Lake package, the one place an external dependency
  (`plausible`) is taken.

## Traceability

`docs/traceability.toml` links upstream behaviour to the Lean symbol, theorem
and test that realise it. Add a row when behaviour is newly implemented,
tested-only, excluded, or deviates. CI fails if a registered symbol does not
resolve.

## Conventions

* Lean 4 `leanprover/lean4:v4.35.0`; no Mathlib; the core library depends only on Lean
  core and the sibling `lean-*` repos listed in `lakefile.toml`, pinned by
  commit in `lake-manifest.json`.
* Choose the definition that suits the automation over a prettier one with a
  harder proof.
* No upstream code is copied; the upstream test suite and docs are the spec.
