import PtxHardwareDense
open Lean

def main (args : List String) : IO Unit := do
  let [input,output] := args | throw (IO.userError "usage: HardwareDenseMain.lean REQUEST.json OUTPUT.json")
  let text ← IO.FS.readFile input
  let result := do
    let request ← Json.parse text
    let cases ← request.getArr?
    let exported ← cases.toList.mapM Ptx.Hardware.Dense.exportCase
    pure (toJson exported)
  match result with
  | .error message => throw (IO.userError message)
  | .ok result => IO.FS.writeFile output (result.pretty ++ "\n")
