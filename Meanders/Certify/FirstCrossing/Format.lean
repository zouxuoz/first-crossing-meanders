import Meanders.Certify.FirstCrossing.Sector

/-!
First-Crossing rows have the exact form
`PL,PR,QL,QR|MATE_CSV ORDINARY LOWER_RETURNS` followed by LF.
Counters and mates use raw storage order; rows use numeric Key.sortCode order.
The empty mate list is the empty field after `|`. Empty layers are empty files.
All decimals are canonical unsigned ASCII and ordinary multiplicity is positive.
The fixed sector and physical layer index belong to the external cursor metadata.
-/

namespace Meanders.Certify.FirstCrossingSectorTable

open FirstCrossing

private def natListText (xs : List ℕ) : String :=
  String.intercalate "," (xs.map toString)

/-- Canonical raw-key bytes retain all four original counters and the full mate list. -/
def keyText (key : Key) : String :=
  natListText [key.counters.pl, key.counters.pr, key.counters.ql, key.counters.qr] ++
    "|" ++ natListText key.mate

/-- Render exact paired rows without changing their supplied order or combining keys. -/
def formatLayer (rows : FirstCrossing.Layer) : String :=
  String.join (rows.map fun (key, ordinary, lowerReturns) =>
    s!"{keyText key} {ordinary} {lowerReturns}\n")

private def parseNat (text : String) : Except String ℕ := do
  if text.isEmpty || !text.toList.all Char.isDigit then
    throw "expected an unsigned ASCII natural"
  let some value := text.toNat? | throw "expected a natural"
  pure value

private def parseKey (text : String) : Except String Key := do
  let [counts, mates] := text.splitOn "|" | throw "expected one mate separator"
  let [pl, pr, ql, qr] := counts.splitOn "," | throw "expected four original counters"
  let counters : Counters := ⟨← parseNat pl, ← parseNat pr, ← parseNat ql, ← parseNat qr⟩
  let mate ← if mates.isEmpty then pure [] else (mates.splitOn ",").mapM parseNat
  if !pairingValid mate then throw "mate list is not a fixed-point-free involution"
  pure ⟨counters, mate⟩

private def parseRow (line : String) : Except String FirstCrossing.Row := do
  let [key, ordinary, lowerReturns] := line.splitOn " " | throw "expected key and two channels"
  let key ← parseKey key
  let ordinary ← parseNat ordinary
  let lowerReturns ← parseNat lowerReturns
  if ordinary = 0 then throw "ordinary multiplicity must be positive"
  pure (key, ordinary, lowerReturns)

/-- Parse only exact canonical paired rows. Duplicate and out-of-order evidence
is rejected; the parser never sorts or merges a supplied layer. -/
def parseLayer (text : String) : Except String FirstCrossing.Layer := do
  if text.isEmpty then return []
  if !text.endsWith "\n" then throw "no trailing newline"
  let rows ← ((text.splitOn "\n").dropLast).mapM parseRow
  if !(rows.zip rows.tail).all (fun (a, b) =>
      codeLE a.1.sortCode b.1.sortCode && !(a.1 == b.1)) then
    throw "keys are not strictly ascending in numeric storage order"
  if formatLayer rows != text then throw "noncanonical First-Crossing row bytes"
  pure rows

/-- Parsing and local exact checking compose without a new numerical trust boundary. -/
def checkText (spec : RunSpec) (layers : List String) (claimed : Summary) :
    Except String Summary := do
  let rows ← layers.mapM parseLayer
  check spec rows claimed

end Meanders.Certify.FirstCrossingSectorTable
