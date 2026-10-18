# Examples: the itsdangerous docs, translated

Each file translates one page of the itsdangerous documentation
(`docs/*.rst` in [pallets/itsdangerous](https://github.com/pallets/itsdangerous),
version 2.2.0), and names the page it translates. Read them in this order.

| # | File | Upstream page | Covers |
|---|---|---|---|
| 1 | [`Quickstart.lean`](Quickstart.lean) | `README.md` "A Simple Example", `docs/index.rst` | `URLSafeSerializer` dumps/loads, `Signer`, `TimestampSigner`, rotation; a `main` with the real clock (`lake exe quickstart`) |
| 2 | [`Signer.lean`](Signer.lean) | `docs/signer.rst` "Signing Interface" | `Signer.sign`/`unsign`, a changed value, UTF-8 text, `NoneAlgorithm`, other digests |
| 3 | [`Timed.lean`](Timed.lean) | `docs/timed.rst` "Signing With Timestamps" | `TimestampSigner`, `max_age`, `SignatureExpired`, `return_timestamp`, `TimedSerializer` |
| 4 | [`Serializer.lean`](Serializer.lean) | `docs/serializer.rst` "Serialization Interface", "Responding to Failure", "Fallback Signers" | `Serializer.dumps`/`loads`, the payload of a `BadSignature`, `loadPayload`, `loadsUnsafe`, `fallbackSigners` |
| 5 | [`UrlSafe.lean`](UrlSafe.lean) | `docs/url_safe.rst` "URL Safe Serialization" | `URLSafeSerializer`, `URLSafeTimedSerializer` |
| 6 | [`Concepts.lean`](Concepts.lean) | `docs/concepts.rst` "The Salt", "Key Rotation" | salts separate contexts; rotating keys in and out |
| 7 | [`Exceptions.lean`](Exceptions.lean) | `docs/exceptions.rst` "Exceptions" | `BadSignature`, `BadTimeSignature`, `SignatureExpired`, `BadPayload`, the separator `ValueError` |

Every example is built by CI (`lake build Examples`, and `lake exe quickstart`).
Every token and value an example prints is checked byte for byte against
upstream itsdangerous 2.2.0's output for the same snippet, by the `docs:`
cases in `tests/Conformance.lean`.

Two differences from the Python snippets, both documented deviations
(CONTRIBUTING.md):

* **Payloads.** Upstream's default serializer is Python's `json`, so
  `s.dumps([1, 2, 3, 4])` takes a Python list. This library has no JSON of its
  own; its default payload type is `String`, and the examples pass the JSON
  text `json.dumps` would write (`"[1, 2, 3, 4]"`, compact `"[1,2,3,4]"` for
  the URL-safe serializers), which is why the tokens match. lean-json's `Json`
  plugs in as another `Codec` (lean-starlette does this).
* **Time.** Upstream reads the clock inside `sign` and `unsign`; here `now`
  is the last argument. The examples fix it so their output is reproducible;
  `getTimestamp` reads the real clock (see `main` in `Quickstart.lean` and
  `Timed.lean`).
