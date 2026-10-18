import LeanItsdangerous.DataTypes.Hash

/-!
# SHA-1, SHA-256, SHA-512 and HMAC

Straight transcriptions of FIPS 180-4 and RFC 2104. They are trusted, not
proved: their correctness is checked against the FIPS 180-4 example vectors
and the RFC 2202 / RFC 4231 HMAC vectors in `tests/Props.lean`. What *is*
proved here is the one structural fact the signer proofs need, the fixed
output length (`Hash.h_len`).

The compression loops index arrays with `getD`, so nothing here can panic,
and every loop is a bounded `for` over a range.
-/

namespace LeanItsdangerous.Sha

/-- Big-endian bytes of a 32-bit word. -/
def be32 (w : UInt32) : Bytes :=
  [(w >>> 24).toUInt8, (w >>> 16).toUInt8, (w >>> 8).toUInt8, w.toUInt8]

/-- Big-endian bytes of a 64-bit word. -/
def be64 (w : UInt64) : Bytes :=
  [(w >>> 56).toUInt8, (w >>> 48).toUInt8, (w >>> 40).toUInt8, (w >>> 32).toUInt8,
   (w >>> 24).toUInt8, (w >>> 16).toUInt8, (w >>> 8).toUInt8, w.toUInt8]

/-- Concatenated big-endian bytes of a list of 32-bit words. -/
def out32 : List UInt32 → Bytes
  | [] => []
  | w :: ws => be32 w ++ out32 ws

/-- Concatenated big-endian bytes of a list of 64-bit words. -/
def out64 : List UInt64 → Bytes
  | [] => []
  | w :: ws => be64 w ++ out64 ws

theorem length_out32 (ws : List UInt32) : (out32 ws).length = 4 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [out32, be32, ih]; omega

theorem length_out64 (ws : List UInt64) : (out64 ws).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [out64, be64, ih]; omega

/-- Merkle–Damgård padding: the message, `0x80`, zeros, and the bit length
in `lenBytes` big-endian bytes, to a multiple of `block`. -/
def mdPad (msg : Bytes) (block lenBytes : Nat) : Array UInt8 :=
  let n := msg.length
  let zeros := (2 * block - lenBytes - 1 - n % block) % block
  let bits := n * 8
  (msg ++ [0x80] ++ List.replicate zeros 0 ++
    (List.range lenBytes).reverse.map (fun i => UInt8.ofNat (bits / 256 ^ i % 256))).toArray

def word32 (m : Array UInt8) (o : Nat) : UInt32 :=
  ((m.getD o 0).toUInt32 <<< 24) ||| ((m.getD (o+1) 0).toUInt32 <<< 16) |||
  ((m.getD (o+2) 0).toUInt32 <<< 8) ||| (m.getD (o+3) 0).toUInt32

def word64 (m : Array UInt8) (o : Nat) : UInt64 :=
  ((word32 m o).toUInt64 <<< 32) ||| (word32 m (o+4)).toUInt64

def rotl32 (x : UInt32) (n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))
def rotr32 (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))
def rotr64 (x : UInt64) (n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))

/-! ## SHA-1 -/

def sha1Block (h : Array UInt32) (m : Array UInt8) (o : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.mkEmpty 80
  for t in [0:16] do
    w := w.push (word32 m (o + 4 * t))
  for t in [16:80] do
    w := w.push (rotl32 (w.getD (t-3) 0 ^^^ w.getD (t-8) 0 ^^^ w.getD (t-14) 0 ^^^ w.getD (t-16) 0) 1)
  let mut a := h.getD 0 0
  let mut b := h.getD 1 0
  let mut c := h.getD 2 0
  let mut d := h.getD 3 0
  let mut e := h.getD 4 0
  for t in [0:80] do
    let (f, k) : UInt32 × UInt32 :=
      if t < 20 then ((b &&& c) ||| (~~~b &&& d), 0x5A827999)
      else if t < 40 then (b ^^^ c ^^^ d, 0x6ED9EBA1)
      else if t < 60 then ((b &&& c) ||| (b &&& d) ||| (c &&& d), 0x8F1BBCDC)
      else (b ^^^ c ^^^ d, 0xCA62C1D6)
    let tmp := rotl32 a 5 + f + e + k + w.getD t 0
    e := d
    d := c
    c := rotl32 b 30
    b := a
    a := tmp
  return #[h.getD 0 0 + a, h.getD 1 0 + b, h.getD 2 0 + c, h.getD 3 0 + d, h.getD 4 0 + e]

def sha1Digest (msg : Bytes) : Bytes :=
  let m := mdPad msg 64 8
  let h := Id.run do
    let mut h : Array UInt32 := #[0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0]
    for i in [0:m.size / 64] do
      h := sha1Block h m (64 * i)
    return h
  out32 ((List.range 5).map (h.getD · 0))

/-! ## SHA-256 -/

def k256 : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def sha256Block (h : Array UInt32) (m : Array UInt8) (o : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.mkEmpty 64
  for t in [0:16] do
    w := w.push (word32 m (o + 4 * t))
  for t in [16:64] do
    let x := w.getD (t-15) 0
    let y := w.getD (t-2) 0
    let s0 := rotr32 x 7 ^^^ rotr32 x 18 ^^^ (x >>> 3)
    let s1 := rotr32 y 17 ^^^ rotr32 y 19 ^^^ (y >>> 10)
    w := w.push (w.getD (t-16) 0 + s0 + w.getD (t-7) 0 + s1)
  let mut a := h.getD 0 0
  let mut b := h.getD 1 0
  let mut c := h.getD 2 0
  let mut d := h.getD 3 0
  let mut e := h.getD 4 0
  let mut f := h.getD 5 0
  let mut g := h.getD 6 0
  let mut hh := h.getD 7 0
  for t in [0:64] do
    let S1 := rotr32 e 6 ^^^ rotr32 e 11 ^^^ rotr32 e 25
    let ch := (e &&& f) ^^^ (~~~e &&& g)
    let t1 := hh + S1 + ch + k256.getD t 0 + w.getD t 0
    let S0 := rotr32 a 2 ^^^ rotr32 a 13 ^^^ rotr32 a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := S0 + maj
    hh := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #[h.getD 0 0 + a, h.getD 1 0 + b, h.getD 2 0 + c, h.getD 3 0 + d,
           h.getD 4 0 + e, h.getD 5 0 + f, h.getD 6 0 + g, h.getD 7 0 + hh]

def sha256Digest (msg : Bytes) : Bytes :=
  let m := mdPad msg 64 8
  let h := Id.run do
    let mut h : Array UInt32 := #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
                                  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
    for i in [0:m.size / 64] do
      h := sha256Block h m (64 * i)
    return h
  out32 ((List.range 8).map (h.getD · 0))

/-! ## SHA-512 -/

def k512 : Array UInt64 := #[
  0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
  0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
  0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
  0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
  0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
  0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
  0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
  0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
  0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
  0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
  0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
  0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
  0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
  0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
  0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
  0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
  0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
  0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
  0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
  0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

def sha512Block (h : Array UInt64) (m : Array UInt8) (o : Nat) : Array UInt64 := Id.run do
  let mut w : Array UInt64 := Array.mkEmpty 80
  for t in [0:16] do
    w := w.push (word64 m (o + 8 * t))
  for t in [16:80] do
    let x := w.getD (t-15) 0
    let y := w.getD (t-2) 0
    let s0 := rotr64 x 1 ^^^ rotr64 x 8 ^^^ (x >>> 7)
    let s1 := rotr64 y 19 ^^^ rotr64 y 61 ^^^ (y >>> 6)
    w := w.push (w.getD (t-16) 0 + s0 + w.getD (t-7) 0 + s1)
  let mut a := h.getD 0 0
  let mut b := h.getD 1 0
  let mut c := h.getD 2 0
  let mut d := h.getD 3 0
  let mut e := h.getD 4 0
  let mut f := h.getD 5 0
  let mut g := h.getD 6 0
  let mut hh := h.getD 7 0
  for t in [0:80] do
    let S1 := rotr64 e 14 ^^^ rotr64 e 18 ^^^ rotr64 e 41
    let ch := (e &&& f) ^^^ (~~~e &&& g)
    let t1 := hh + S1 + ch + k512.getD t 0 + w.getD t 0
    let S0 := rotr64 a 28 ^^^ rotr64 a 34 ^^^ rotr64 a 39
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := S0 + maj
    hh := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #[h.getD 0 0 + a, h.getD 1 0 + b, h.getD 2 0 + c, h.getD 3 0 + d,
           h.getD 4 0 + e, h.getD 5 0 + f, h.getD 6 0 + g, h.getD 7 0 + hh]

def sha512Digest (msg : Bytes) : Bytes :=
  let m := mdPad msg 128 16
  let h := Id.run do
    let mut h : Array UInt64 := #[0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b,
      0xa54ff53a5f1d36f1, 0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b,
      0x5be0cd19137e2179]
    for i in [0:m.size / 128] do
      h := sha512Block h m (128 * i)
    return h
  out64 ((List.range 8).map (h.getD · 0))

end Sha

open Sha in
/-- SHA-1, upstream's default `digest_method`. -/
def sha1 : Hash where
  name := "sha1"
  blockSize := 64
  digestSize := 20
  digest := sha1Digest
  h_len m := by simp [sha1Digest, length_out32]

open Sha in
/-- SHA-256. -/
def sha256 : Hash where
  name := "sha256"
  blockSize := 64
  digestSize := 32
  digest := sha256Digest
  h_len m := by simp [sha256Digest, length_out32]

open Sha in
/-- SHA-512. -/
def sha512 : Hash where
  name := "sha512"
  blockSize := 128
  digestSize := 64
  digest := sha512Digest
  h_len m := by simp [sha512Digest, length_out64]

/-- HMAC (RFC 2104) over a hash. A key longer than the block is hashed
first; the key is then zero-padded to the block size. -/
def hmac (H : Hash) (key msg : Bytes) : Bytes :=
  let k := if key.length > H.blockSize then H.digest key else key
  let k := k ++ List.replicate (H.blockSize - k.length) 0
  H.digest (k.map (· ^^^ 0x5c) ++ H.digest (k.map (· ^^^ 0x36) ++ msg))

theorem length_hmac (H : Hash) (key msg : Bytes) : (hmac H key msg).length = H.digestSize :=
  H.h_len _

/-- Upstream's `HMACAlgorithm(digest_method)`. -/
def hmacAlgorithm (H : Hash) : SigningAlgorithm where
  name := "hmac-" ++ H.name
  getSignature key value := hmac H key value

/-- Upstream's `NoneAlgorithm`: the empty signature. -/
def noneAlgorithm : SigningAlgorithm where
  name := "none"
  getSignature _ _ := []

end LeanItsdangerous
