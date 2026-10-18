import LeanItsdangerous

/-!
# Property tests: fast feedback where there is no proof

Two kinds of check live here.

* **Known-answer vectors** for what is trusted rather than proved: SHA-1,
  SHA-256 and SHA-512 against the FIPS 180-4 examples (and the NIST
  one-million-`a` messages), HMAC-SHA1 against RFC 2202, HMAC-SHA256 and
  HMAC-SHA512 against RFC 4231. A vector property ignores the generator.
* **Seeded properties** on random inputs: the proved round trips as smoke
  tests of the definitions, a sampled no-collision smoke test of HMAC-SHA1,
  and that flipping a byte of a signed string makes `unsign` fail on the
  real HMAC-SHA1.

Run with `lake exe props`, or a different seed with `lake exe props 12345`.
A failure prints the seed and the value, so it reproduces exactly.
-/

open LeanItsdangerous

/-- xorshift64*: four lines, no dependency, deterministic from the seed. -/
structure Rng where
  s : UInt64
  deriving Inhabited

def Rng.next (r : Rng) : UInt64 × Rng :=
  let x := r.s
  let x := x ^^^ (x >>> 12)
  let x := x ^^^ (x <<< 25)
  let x := x ^^^ (x >>> 27)
  (x * 2685821657736338717, { s := x })

def Rng.nat (r : Rng) (bound : Nat) : Nat × Rng :=
  let (v, r) := r.next
  (if bound == 0 then 0 else v.toNat % bound, r)

def Rng.bytes (r : Rng) (maxLen : Nat) : Bytes × Rng := Id.run do
  let (n, r) := r.nat (maxLen + 1)
  let mut r := r
  let mut out : Bytes := []
  for _ in [0:n] do
    let (b, r') := r.nat 256
    r := r'
    out := UInt8.ofNat b :: out
  return (out, r)

/-- A property: a name and a check that, given a generator, either passes or
returns a description of the failing value. -/
structure Property where
  name : String
  check : Rng → Option String × Rng
  /-- How many times to run it (1 for a fixed vector). -/
  cases : Nat := 200

def b (s : String) : Bytes := Bytes.ofString s

def vector (name : String) (got : Bytes) (expectHex : String) : Property where
  name := name
  cases := 1
  check r := (if got.toHex == expectHex then none else some s!"got {got.toHex}", r)

def million : Bytes := List.replicate 1000000 97

def fipsVectors : List Property := [
  vector "FIPS 180-4 SHA-1 \"abc\"" (sha1.digest (b "abc"))
    "a9993e364706816aba3e25717850c26c9cd0d89d",
  vector "FIPS 180-4 SHA-1 empty" (sha1.digest [])
    "da39a3ee5e6b4b0d3255bfef95601890afd80709",
  vector "FIPS 180-4 SHA-1 448-bit" (sha1.digest (b "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"))
    "84983e441c3bd26ebaae4aa1f95129e5e54670f1",
  vector "FIPS 180-4 SHA-1 million a" (sha1.digest million)
    "34aa973cd4c4daa4f61eeb2bdbad27316534016f",
  vector "FIPS 180-4 SHA-256 \"abc\"" (sha256.digest (b "abc"))
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
  vector "FIPS 180-4 SHA-256 empty" (sha256.digest [])
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
  vector "FIPS 180-4 SHA-256 448-bit" (sha256.digest (b "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"))
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1",
  vector "FIPS 180-4 SHA-256 million a" (sha256.digest million)
    "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0",
  vector "FIPS 180-4 SHA-512 \"abc\"" (sha512.digest (b "abc"))
    ("ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a" ++
     "2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"),
  vector "FIPS 180-4 SHA-512 empty" (sha512.digest [])
    ("cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce" ++
     "47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"),
  vector "FIPS 180-4 SHA-512 896-bit" (sha512.digest (b ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmn" ++
      "hijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu")))
    ("8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018" ++
     "501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909")
]

def k4 : Bytes := (List.range 25).map fun i => UInt8.ofNat (i + 1)
def tc6 : String := "Test Using Larger Than Block-Size Key - Hash Key First"
def tc7 : String := "This is a test using a larger than block-size key and a larger than block-size data. " ++
  "The key needs to be hashed before being used by the HMAC algorithm."

def rfcVectors : List Property := [
  vector "RFC 2202 HMAC-SHA1 case 1" (hmac sha1 (List.replicate 20 0x0b) (b "Hi There"))
    "b617318655057264e28bc0b6fb378c8ef146be00",
  vector "RFC 2202 HMAC-SHA1 case 2" (hmac sha1 (b "Jefe") (b "what do ya want for nothing?"))
    "effcdf6ae5eb2fa2d27416d5f184df9c259a7c79",
  vector "RFC 2202 HMAC-SHA1 case 3" (hmac sha1 (List.replicate 20 0xaa) (List.replicate 50 0xdd))
    "125d7342b9ac11cd91a39af48aa17b4f63f175d3",
  vector "RFC 4231 HMAC-SHA256 case 1" (hmac sha256 (List.replicate 20 0x0b) (b "Hi There"))
    "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7",
  vector "RFC 4231 HMAC-SHA256 case 2" (hmac sha256 (b "Jefe") (b "what do ya want for nothing?"))
    "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843",
  vector "RFC 4231 HMAC-SHA256 case 3" (hmac sha256 (List.replicate 20 0xaa) (List.replicate 50 0xdd))
    "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe",
  vector "RFC 4231 HMAC-SHA256 case 4" (hmac sha256 k4 (List.replicate 50 0xcd))
    "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b",
  vector "RFC 4231 HMAC-SHA256 case 5 (truncated)"
    ((hmac sha256 (List.replicate 20 0x0c) (b "Test With Truncation")).take 16)
    "a3b6167473100ee06e0c796c2955552b",
  vector "RFC 4231 HMAC-SHA256 case 6" (hmac sha256 (List.replicate 131 0xaa) (b tc6))
    "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54",
  vector "RFC 4231 HMAC-SHA256 case 7" (hmac sha256 (List.replicate 131 0xaa) (b tc7))
    "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2",
  vector "RFC 4231 HMAC-SHA512 case 1" (hmac sha512 (List.replicate 20 0x0b) (b "Hi There"))
    ("87aa7cdea5ef619d4ff0b4241a1d6cb02379f4e2ce4ec2787ad0b30545e17cde" ++
     "daa833b7d6b8a702038b274eaea3f4e4be9d914eeb61f1702e696c203a126854"),
  vector "RFC 4231 HMAC-SHA512 case 2" (hmac sha512 (b "Jefe") (b "what do ya want for nothing?"))
    ("164b7a7bfcf819e2e395fbe73b56e0a387bd64222e831fd610270cd7ea250554" ++
     "9758bf75c05a994a6d034f65f8f0e6fdcaeab1a34d4a6b4b636e070a38bce737"),
  vector "RFC 4231 HMAC-SHA512 case 3" (hmac sha512 (List.replicate 20 0xaa) (List.replicate 50 0xdd))
    ("fa73b0089d56a284efb0f0756c890be9b1b5dbdd8ee81a3655f83e33b2279d39" ++
     "bf3e848279a722c806b485a47e67c807b946a337bee8942674278859e13292fb"),
  vector "RFC 4231 HMAC-SHA512 case 4" (hmac sha512 k4 (List.replicate 50 0xcd))
    ("b0ba465637458c6990e5a8c5f61d4af7e576d97ff94b872de76f8050361ee3db" ++
     "a91ca5c11aa25eb4d679275cc5788063a5f19741120c4f2de2adebeb10a298dd"),
  vector "RFC 4231 HMAC-SHA512 case 5 (truncated)"
    ((hmac sha512 (List.replicate 20 0x0c) (b "Test With Truncation")).take 16)
    "415fad6271580a531d4179bc891d87a6",
  vector "RFC 4231 HMAC-SHA512 case 6" (hmac sha512 (List.replicate 131 0xaa) (b tc6))
    ("80b24263c7c1a3ebb71493c1dd7be8b49b46d1f41b4aeec1121b013783f8f352" ++
     "6b56d037e05f2598bd0fd2215d6a1e5295e64f73f63f0aec8b915a985d786598"),
  vector "RFC 4231 HMAC-SHA512 case 7" (hmac sha512 (List.replicate 131 0xaa) (b tc7))
    ("e37b6a775dc87dbaa4dfa9f96e5e3ffddebd71f8867289865df5a32d20cdc944" ++
     "b6022cac3c4982b10d5eeb55c3e4de15134676fb6de0446065c97440fa8c6a58")
]

def signer : Signer := Signer.new ["old-key", "secret-key"]

/-- A random string mixing ASCII, two-, three- and four-byte code points. -/
def Rng.string (r : Rng) (maxLen : Nat) : String × Rng := Id.run do
  let (n, r) := r.nat (maxLen + 1)
  let mut r := r
  let mut out : List Char := []
  for _ in [0:n] do
    let (kind, r1) := r.nat 4
    let (x, r2) := r1.nat 0x10000
    r := r2
    let cp := match kind with
      | 0 => x % 0x80
      | 1 => 0x80 + x % 0x780
      | 2 => let y := 0x800 + x % 0xF800; if 0xD800 ≤ y ∧ y < 0xE000 then 0x41 else y
      | _ => 0x10000 + x * 16
    out := Char.ofNat cp :: out
  return (String.ofList out, r)

def randomProps : List Property := [
  { name := "Bytes.ofString (structural UTF-8) agrees with String.toUTF8"
    check := fun r =>
      let (str, r) := r.string 40
      ((if Bytes.ofString str == str.toUTF8.toList then none else some (repr str).pretty), r) },
  { name := "hash output lengths are fixed (sha1/sha256/sha512)"
    check := fun r =>
      let (m, r) := r.bytes 300
      ((if (sha1.digest m).length == 20 && (sha256.digest m).length == 32 &&
           (sha512.digest m).length == 64 then none else some s!"{m.toHex}"), r) },
  { name := "HMAC long key = HMAC of hashed key (RFC 2104)"
    check := fun r =>
      let (k, r) := r.bytes 200
      let (m, r) := r.bytes 100
      let k := k ++ List.replicate 65 7
      ((if hmac sha256 k m == hmac sha256 (sha256.digest k) m then none else some s!"{k.toHex}"), r) },
  { name := "HMAC-SHA1 no collision on sampled random pairs (smoke test; cannot test a for-all)"
    check := fun r =>
      let (k, r) := r.bytes 40
      let (m₁, r) := r.bytes 60
      let (m₂, r) := r.bytes 60
      ((if m₁ == m₂ || hmac sha1 k m₁ != hmac sha1 k m₂ then none
        else some s!"{k.toHex} {m₁.toHex} {m₂.toHex}"), r) },
  { name := "base64url round trip (smoke test of a proved property)"
    check := fun r =>
      let (m, r) := r.bytes 100
      ((if b64decode (base64Encode m) == some m then none else some m.toHex), r) },
  { name := "unsign (sign v) = v with HMAC-SHA1 (smoke test of a proved property)"
    check := fun r =>
      let (v, r) := r.bytes 80
      ((match signer.unsignImpl (signer.sign v) with
        | .ok w => if w == v then none else some v.toHex
        | .error _ => some v.toHex), r) },
  { name := "flipping one byte of a signed string makes unsign fail (HMAC-SHA1)"
    check := fun r =>
      let (v, r) := r.bytes 80
      let s := signer.sign v
      let (i, r) := r.nat s.length
      let (d, r) := r.nat 255
      let s' : Bytes := s.set i (s.getD i 0 + UInt8.ofNat (d + 1))
      ((match signer.unsignImpl s' with
        | .ok w => if w == v then none else some s!"accepted {s'.toHex}"
        | .error _ => none), r) },
  { name := "timestamp signer round trip within max_age"
    check := fun r =>
      let (v, r) := r.bytes 60
      let (ts, r) := r.nat 4000000000
      let (age, r) := r.nat 100
      let t : TimestampSigner := ⟨signer⟩
      let now := UInt64.ofNat (ts + age)
      ((match t.unsignImpl (some 100) now (t.sign v (UInt64.ofNat ts)) with
        | .ok (w, ts') => if w == v && ts'.toNat == ts then none else some v.toHex
        | .error e => some e.message), r) }
]

def properties : List Property := fipsVectors ++ rfcVectors ++ randomProps

def main (args : List String) : IO UInt32 := do
  let seed := (args.head? >>= String.toNat?).getD 88172645463325252
  let mut rng : Rng := { s := UInt64.ofNat seed }
  let mut failures := 0
  for p in properties do
    let mut failed : Option String := none
    for _ in [0:p.cases] do
      if failed.isSome then break
      let (res, rng') := p.check rng
      rng := rng'
      failed := res
    match failed with
    | none => IO.println s!"ok    {p.name} ({p.cases} cases)"
    | some why =>
      failures := failures + 1
      IO.println s!"FAIL  {p.name}: {why}  (seed {seed})"
  IO.println s!"{properties.length} properties, {failures} failing (seed {seed})"
  return if failures == 0 then 0 else 1
