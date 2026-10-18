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
| `DataTypes/` | structures and inductives; invariants are fields | n/a |
| `RepoImpl/` | executable definitions; total, structural recursion | subject of proofs |
| `Specifications/` | the properties, in `Prop` | the contract |
| `Proofs/` | theorems; `Proofs/Verified.lean` bundles one `Verified<Layer>` per layer | yes |
| `APIs/` | the public surface, returning refinements | by construction |
| `Transport.lean` (if present) | the only effectful module | no; tested (none here: the library is pure) |

Everything except the transport module is a pure function. This is
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
`Specifications/Spec.lean`, in four bundles:

* `VerifiedEncoding`: `b64decode_b64encode` (base64url round trip, also
  through the padding-tolerant `base64Decode`), `bytesToInt_intToBytes`,
  `decodeTimestamp_encodeTimestamp`, and base64url output never containing a
  separator byte.
* `VerifiedSigner`: `unsign_sign`, `unsign_signWith` (key rotation: any key
  in the list), `unsign_sound` (an `ok v` means some listed key signed `v`;
  the refinement `Signer.unsign` returns), `unsign_tampered_value`,
  `unsign_tampered` (changing one byte never yields a different value) and
  `unsign_tampered_single` (with one key it fails).
* `VerifiedTimestampSigner`: round trip with rotation within `max_age`,
  soundness (signed by a listed key, timestamp within the age bound),
  `max_age` monotonicity, expiry.
* `VerifiedSerializer`: URL-safe codec round trip, `loads (dumps x) = x`
  (plain and timed) for any codec whose `loads` inverts `dumps`, and
  soundness of both `loads`.

The tampering theorems are about the trusted signing algorithm, so they take
what they need of it as explicit hypotheses: distinct values give distinct
raw signatures (the HMAC-outputs-differ hypothesis), and raw signatures have a
fixed length (discharged for HMAC by `Signer.rawSignature_length_hmac`, from
the proved `Hash.h_len`).

### Tested, not proved

Listed here with the reason, and in `docs/traceability.toml` with
`status = "tested"`.

* **SHA-1, SHA-256, SHA-512** (`RepoImpl/Hash.lean`): bit-level hash
  correctness is out of scope for the proof effort. Tested against the
  FIPS 180-4 example vectors (`abc`, empty, the 448/896-bit messages, one
  million `a`) in `tests/Props.lean`. Their fixed output length is proved.
* **HMAC** (`RepoImpl/Hash.lean`): trusted for the same reason. Tested
  against RFC 2202 (HMAC-SHA1) and RFC 4231 cases 1–7 (HMAC-SHA256,
  HMAC-SHA512), plus seeded properties (long keys are hashed; distinct
  messages give distinct MACs; flipping a byte of a signed string makes
  `unsign` fail) in `tests/Props.lean` and `tests/pbt/`.

### Deviations from upstream

Each is a `status = "deviation"` or `"excluded"` row in
`docs/traceability.toml`.

* **Separator check is stricter.** Upstream rejects a separator only if it is
  a substring of the base64 alphabet; here any byte of it in the alphabet
  (or an empty separator) is rejected. This is what makes the split provably
  recover the signature.
* **Signature comparison** is equality of the canonical base64url encoding,
  not `hmac.compare_digest` of decoded bytes: the same on every signature
  upstream emits, rejects the non-canonical spellings Python's lenient
  decoder accepts, and is not constant-time.
* **No zlib.** URL-safe `dumps` never compresses; `loads` rejects a
  compressed (`.`-prefixed) payload with `BadPayload`.
* **No built-in JSON.** The payload codec is a parameter (`Codec α`);
  lean-starlette plugs in lean-json.
* **Time is explicit** (`now : UInt64`, seconds since the epoch) and
  timestamps are returned as seconds, not `datetime`. `max_age` is a `Nat`.
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
