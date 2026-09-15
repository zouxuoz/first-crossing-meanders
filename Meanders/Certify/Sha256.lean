import Lean.Data.Json

/-!
SHA-256 (FIPS 180-4) for file commitments. This implementation is tested against
standard and cross-language vectors; no numerical theorem relies on its collision
resistance or on these bytes authenticating a mathematical transition.
-/

namespace Meanders.Certify.Sha256

private def constants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

private def rotate (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- SHA-256 of bytes, as 32 bytes in big-endian order. -/
def digest (input : ByteArray) : ByteArray := Id.run do
  let size := input.size
  let mut data := input.push 0x80
  for _ in [:((55 + 64 - size % 64) % 64)] do data := data.push 0
  for i in [:8] do data := data.push (((size.toUInt64 * 8) >>> ((7 - i) * 8).toUInt64).toUInt8)
  let mut hash : Array UInt32 := #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
  for block in [:data.size / 64] do
    let mut w : Array UInt32 := #[]
    for i in [:16] do
      let mut x : UInt32 := 0
      for j in [:4] do x := (x <<< 8) ||| data[block * 64 + i * 4 + j]!.toUInt32
      w := w.push x
    for i in [16:64] do
      let x := w[i - 15]!
      let y := w[i - 2]!
      let s₀ := rotate x 7 ^^^ rotate x 18 ^^^ (x >>> 3)
      let s₁ := rotate y 17 ^^^ rotate y 19 ^^^ (y >>> 10)
      w := w.push (w[i - 16]! + s₀ + w[i - 7]! + s₁)
    let mut a := hash[0]!
    let mut b := hash[1]!
    let mut c := hash[2]!
    let mut d := hash[3]!
    let mut e := hash[4]!
    let mut f := hash[5]!
    let mut g := hash[6]!
    let mut h := hash[7]!
    for i in [:64] do
      let s₁ := rotate e 6 ^^^ rotate e 11 ^^^ rotate e 25
      let ch := (e &&& f) ^^^ ((~~~e) &&& g)
      let t₁ := h + s₁ + ch + constants[i]! + w[i]!
      let s₀ := rotate a 2 ^^^ rotate a 13 ^^^ rotate a 22
      let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
      h := g
      g := f
      f := e
      e := d + t₁
      d := c
      c := b
      b := a
      a := t₁ + s₀ + maj
    hash := (hash.zip #[a, b, c, d, e, f, g, h]).map fun (x, y) => x + y
  let mut out := ByteArray.empty
  for x in hash do
    for i in [:4] do out := out.push ((x >>> ((3 - i) * 8).toUInt32).toUInt8)
  return out

/-- Lowercase hexadecimal bytes. -/
def hex (bytes : ByteArray) : String :=
  String.join (bytes.data.toList.map fun x =>
    let s := String.ofList (Nat.toDigits 16 x.toNat)
    "".pushn '0' (2 - s.length) ++ s)

/-- SHA-256 as 64 lowercase hexadecimal digits. -/
def hash (input : ByteArray) : String := hex (digest input)

private def pairNodes : List ByteArray → List ByteArray
  | a :: b :: rest => digest ((ByteArray.empty.push 1) ++ a ++ b) :: pairNodes rest
  | rest => rest

/-- RFC 9162 Merkle tree: separate leaf/internal prefixes and promote an odd
last node without duplicating it. This gives the largest-power-of-two split. -/
def merkle (leaves : List ByteArray) : ByteArray := Id.run do
  if leaves.isEmpty then return digest ByteArray.empty
  let mut nodes := leaves.map fun leaf => digest ((ByteArray.empty.push 0) ++ leaf)
  for _ in [:leaves.length] do
    if nodes.length > 1 then nodes := pairNodes nodes
  return nodes.head!

end Meanders.Certify.Sha256
