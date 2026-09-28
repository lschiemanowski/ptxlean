import PoissonPTX.ContractionText

open Lean PtxTorchLean.Poisson.PTX

def main (args : List String) : IO UInt32 := do
  if !args.isEmpty then return 2
  let input ← (← IO.getStdin).getLine
  let parsed : Except String (Array Json) := do
    let requests ← Json.parse input >>= Json.getArr?
    requests.mapM fun request => do
      let width ← request.getObjValAs? Nat "width"
      let b ← request.getObjValAs? Nat "B"
      let d ← request.getObjValAs? Nat "D"
      if width < 2 || width > 5 || b ≥ 2^64 || d ≥ 2^64 then
        throw "expected Q1--Q4 width and 64-bit offsets"
      return toJson (Contraction.rendered width (BitVec.ofNat 64 b) (BitVec.ofNat 64 d))
  match parsed with
  | .error e => (← IO.getStderr).putStrLn e; return 1
  | .ok results => (← IO.getStdout).putStrLn (Json.compress (.arr results)); return 0

#print axioms main
