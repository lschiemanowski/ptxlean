import PoissonResidualInput

open Lean PtxTorchLean.Poisson.Certificate

/-- The proof-backed exact checker, driven by serialized GPU input/output words. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [input,output] =>
    let text ← IO.FS.readFile input
    let requests := Json.parse text >>= Json.getArr?
    let mut failed := false
    let mut results := #[]
    match requests with
    | .error e =>
      (← IO.getStderr).putStrLn e
      return 1
    | .ok requests =>
      for request in requests do
        match Input.parse request with
        | .error e =>
          failed := true
          results := results.push (Json.mkObj [("error",toJson e)])
        | .ok parsed =>
          let result := Input.evaluate parsed
          if result.getObjValAs? Bool "accepted" != .ok true then failed := true
          results := results.push result
    IO.FS.writeFile output (Json.pretty (Json.arr results) ++ "\n")
    return if failed then 1 else 0
  | _ =>
    (← IO.getStderr).putStrLn "Usage: poissonResidual INPUT.json OUTPUT.json"
    return 2

#print axioms main
