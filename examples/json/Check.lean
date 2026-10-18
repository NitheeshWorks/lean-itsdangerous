import Quickstart
import Serializer
import UrlSafe
import Concepts

/-!
Helper: checks every value the JSON examples print against what upstream
itsdangerous 2.2.0 prints for the same docs block (generated with
`upstream-spec/.venv/bin/python -I`). Run by CI as `lake exe check`.
-/

open LeanItsdangerous LeanJson

def b (s : String) : Bytes := Bytes.ofString s

def checks : List (String × Bool) := [
  ("README.md: token", Examples.Quickstart.token ==
    b "eyJpZCI6NSwibmFtZSI6Iml0c2Rhbmdlcm91cyJ9.6YP6T0BaO67XP--9UzTrmurXSmg"),
  ("README.md: data[\"name\"]", Examples.Quickstart.name == some "itsdangerous"),
  ("docs/serializer.rst block 1", Examples.Serializer.token == b "[1, 2, 3, 4].r7R9RhGgDPvvWl3iNzLuIIfELmo"),
  ("docs/serializer.rst block 2", Examples.Serializer.loaded.val.toOption == some (json% [1, 2, 3, 4])),
  ("docs/serializer.rst block 3", Examples.Serializer.decodedPayload == some (json% {"id": 5})),
  ("docs/serializer.rst block 4", (match Examples.Serializer.unsafeResult with
      | .ok (false, some v) => v == json% {"id": 5} | _ => false)),
  ("docs/serializer.rst block 5", Examples.Serializer.newToken == b ("[1, 2, 3, 4].yiq3I159517XUuAUCH5_Kl8NJmANC-vT2H6yUors1WSyjcaXLaNni" ++
      "Z29jI_NwpJ_37CBvnkD3IAV6YCjG1x67A") && Examples.Serializer.oldTokenLoads.val.toOption == some (json% [1, 2, 3, 4])),
  ("docs/url_safe.rst block 1", Examples.UrlSafe.token == b "WzEsMiwzLDRd.wSPHqC0gR7VUqivlSukJ0IeTDgo" &&
      Examples.UrlSafe.loaded.val.toOption == some (json% [1, 2, 3, 4])),
  ("docs/concepts.rst block 2", Examples.Concepts.activate == b "NDI.MHQqszw6Wc81wOBQszCrEE_RlzY" &&
      Examples.Concepts.upgrade == b "NDI.c0MpsD6gzpilOAeUPra3NShPXsE"),
  ("docs/concepts.rst block 3", (match Examples.Concepts.crossSalt with
      | .error e => e.isBadSignature && e.message == "Signature b'MHQqszw6Wc81wOBQszCrEE_RlzY' does not match"
      | .ok _ => false)),
  ("docs/concepts.rst block 4", Examples.Concepts.sameSalt.val.toOption == some (json% 42)),
  ("docs/concepts.rst block 5", Examples.Concepts.t == b "{\"id\": 42}.vPnMXi_7YWhvSPnrl9Bcf1-2I44" &&
      Examples.Concepts.stillValid.val.toOption == some (json% {"id": 42}))
]

def main : IO UInt32 := do
  let mut failures := 0
  for (name, ok) in checks do
    IO.println s!"{if ok then "ok  " else "FAIL"}  {name}"
    unless ok do failures := failures + 1
  IO.println s!"{checks.length} checks against itsdangerous 2.2.0, {failures} failing"
  return if failures == 0 then 0 else 1
