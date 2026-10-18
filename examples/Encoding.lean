import LeanItsdangerous
open LeanItsdangerous

/-!
# Encoding Utilities

Port of itsdangerous `docs/encoding.rst` ("Encoding Utilities"). The page
documents two functions and has no code block of its own, so this file
exercises exactly them, as their docstrings in `src/itsdangerous/encoding.py`
describe: `base64_encode` "Base64 encode a string of bytes or text. The
resulting bytes are safe to use in URLs.", and `base64_decode` "Base64 decode
a URL-safe string of bytes or text. The result is bytes." (raising `BadData`
on invalid input).
-/

namespace Examples.Encoding

/-- `base64_encode("無限")` -/
def encoded := base64Encode "無限"
#eval encoded                   -- b'54Sh6ZmQ'

/-- `base64_decode(b"54Sh6ZmQ")` -/
def decoded := base64Decode "54Sh6ZmQ"
#eval decoded.map Bytes.toString?   -- some (some "無限")

/-- `base64_decode("12345")` raises `BadData`: here `none`. -/
def invalid := base64Decode "12345"
#eval invalid                   -- none

end Examples.Encoding
