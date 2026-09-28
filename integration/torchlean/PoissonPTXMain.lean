import PoissonPTX.Text

open Lean PtxTorchLean.Poisson.PTX

def main (args : List String) : IO UInt32 := do
  let input ← (← IO.getStdin).getLine
  let parsed : Except String (Array Json) := do
    let requests ← Json.parse input >>= Json.getArr?
    requests.mapM fun request => do
      let count ← request.getObjValAs? Nat "count"
      let rhs ← request.getObjValAs? Nat "rhs"
      let ap ← request.getObjValAs? Nat "ap"
      let output ← request.getObjValAs? Nat "output"
      if count ≥ 2^32 || rhs ≥ 2^64 || ap ≥ 2^64 || output ≥ 2^64 then
        throw "instruction parameter exceeds its bit width"
      return toJson (Text.residual (BitVec.ofNat 32 count) (BitVec.ofNat 64 rhs)
        (BitVec.ofNat 64 ap) (BitVec.ofNat 64 output))
  if !args.isEmpty then return 2
  match parsed with
  | .error e => (← IO.getStderr).putStrLn e; return 1
  | .ok results => (← IO.getStdout).putStrLn (Json.compress (.arr results)); return 0

#print axioms main
