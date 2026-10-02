import PoissonPTX.CellGatherText
import PoissonPTX.CellPrologueEntry
import PoissonPTX.ContractionText
import PoissonPTX.CellMiddleChecks
import PoissonPTX.CellFinalText

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
      let w ← request.getObjValAs? Nat "W"
      let output ← request.getObjValAs? Nat "output"
      let cells ← request.getObjValAs? Nat "cells"
      let sources ← request.getObjValAs? (Array Nat) "sources"
      if width < 2 || width > 5 || b ≥ 2^64 || d ≥ 2^64 || w ≥ 2^64 || output ≥ 2^64 || cells ≥ 2^64 || sources.size != 3 || sources.any (· ≥ 2^64) then
        throw "expected Q1--Q4 width and 64-bit offsets"
      return Json.mkObj [("gathers", toJson (sources.toList.map fun source => CellGather.rendered width (BitVec.ofNat 64 cells) (BitVec.ofNat 64 source))), ("prologue", toJson (CellPrologue.rendered width)), ("contractions", toJson (Contraction.rendered width (BitVec.ofNat 64 b) (BitVec.ofNat 64 d))),
        ("stores", toJson (Contraction.renderedStores width)),
        ("final", toJson (CellFinal.rendered width (BitVec.ofNat 64 b) (BitVec.ofNat 64 d) (BitVec.ofNat 64 output))),
        ("middle", toJson (Concurrent.CellMiddle.rendered width (BitVec.ofNat 64 b) (BitVec.ofNat 64 d) (BitVec.ofNat 64 w)))]
  match parsed with
  | .error e => (← IO.getStderr).putStrLn e; return 1
  | .ok results => (← IO.getStdout).putStrLn (Json.compress (.arr results)); return 0

#print axioms main
