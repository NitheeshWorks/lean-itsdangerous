# Examples: itsdangerous's own, ported

itsdangerous ships no example programs, so its examples are the Python code
blocks of its README and docs pages (version 2.2.0). Each is ported 1:1, one
Lean file per page, in the order of upstream's docs; each file's first comment
names the page, and each block appears with its Python above its Lean.
[`MANIFEST.toml`](MANIFEST.toml) maps every upstream block to its port
(`stack-tools/check-examples.py` checks it).

| # | Upstream | Lean | Blocks |
|---|---|---|---|
| 1 | `README.md` "A Simple Example" | [`json/Quickstart.lean`](json/Quickstart.lean) | 1 |
| 2 | `docs/concepts.rst` (secret key, salt, key rotation) | [`json/Concepts.lean`](json/Concepts.lean) | 5 |
| 3 | `docs/serializer.rst` (dumps/loads, responding to failure, fallback signers) | [`json/Serializer.lean`](json/Serializer.lean) | 5 |
| 4 | `docs/signer.rst` "Signing Interface" | [`Signer.lean`](Signer.lean) | 3 |
| 5 | `docs/timed.rst` "Signing With Timestamps" | [`Timed.lean`](Timed.lean) | 2 |
| 6 | `docs/url_safe.rst` "URL Safe Serialization" | [`json/UrlSafe.lean`](json/UrlSafe.lean) | 1 |
| – | `docs/encoding.rst`, `docs/exceptions.rst` | excluded: autodoc pages, no code blocks | – |

The functions and exception attributes those two autodoc pages document are
covered by `tests/Conformance.lean` (`autodocCases`) instead.

## Two packages

* `examples/*.lean` (the `Examples` library of this package) need nothing but
  the library.
* `examples/json/` is a separate Lake package, like `tests/pbt`, that also
  requires [lean-json](https://github.com/NitheeshWorks/lean-json), so the
  serializer examples pass real values, as upstream does:
  `s.dumps (json% [1, 2, 3, 4])`. Its helper `ItsdangerousJson.lean` gives
  `Json` the two payload codecs upstream's serializers use (`json.dumps` for
  `Serializer`, `_CompactJSON` for the URL-safe ones) and makes them the
  default, so no example names a type. The core library stays dependency-free.

```
lake build Examples                              # the core examples
cd examples/json && lake build && lake exe check # the JSON examples, checked
lake exe quickstart                              # README.md's example as a program
```

## Checked against upstream

Every token, value and message an example prints is compared byte for byte
with what itsdangerous 2.2.0 prints for the same block (generated with
`upstream-spec/.venv/bin/python -I`): the `docs:` cases of
`tests/Conformance.lean` for the core examples, `lake exe check` for the JSON
ones. Both run in CI.

One difference from the Python blocks remains, a documented deviation:
**time is an argument.** Upstream reads the clock inside `sign` and
`unsign`; here `now` is the last argument, fixed in the examples so their
output is reproducible (`getTimestamp` reads the real clock).
