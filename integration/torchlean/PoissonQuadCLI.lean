import PoissonQuad
import Lean

namespace PtxTorchLean.Poisson.CLI
open Lean

private def field [FromJson α] (j : Json) (name : String) (fallback : α) : Except String α :=
  match j.getObjVal? name with
  | .ok value => fromJson? value
  | .error _ => pure fallback

/-- Exact finite binary64-to-decimal encoding. Lean's default Float JSON writer
prints six decimal places, which would destroy the comparison evidence. -/
def jsonFloat (x : Float) : Json :=
  if !x.isFinite then Json.null else if x == 0 then toJson (0 : Nat) else
  let bits := x.toBits.toNat
  let biased : Nat := bits / 2^52 % 2048
  let significand : Nat := bits % 2^52 + (if biased == 0 then 0 else 2^52)
  let exponent : Int := if biased == 0 then -1074 else (biased : Int)-1075
  let sign : Int := if bits / 2^63 == 0 then 1 else -1
  if exponent ≥ 0 then
    .num ⟨sign * (significand * 2^exponent.toNat : Nat),0⟩
  else .num ⟨sign * (significand * 5^exponent.natAbs : Nat),exponent.natAbs⟩

private def numbers (xs : Array Float) : Json :=
  toJson (xs.map jsonFloat)

/-- A complete numerical solve and inspectable setup/operator observations. -/
def evaluate (j : Json) : Except String Json := do
  let obj ← j.getObj?
  for (key,_) in obj.toList do
    if !(["n","degree","rtol","atol","maxiter","check_every","source","load","values"].contains key) then
      throw s!"unsupported option: {key}"
  let n ← field j "n" (8 : Nat)
  let degree ← field j "degree" (4 : Nat)
  let opts : Options := {
    rtol := ← field j "rtol" (1e-10 : Float), atol := ← field j "atol" (0 : Float),
    maxiter := ← field j "maxiter" (1000 : Nat), checkEvery := ← field j "check_every" (10 : Nat) }
  let sourceName ← field j "source" "sine"
  let source ← match sourceName with
    | "sine" => pure sineSource
    | "zero" => pure (fun _ _ => 0)
    | "constant" => pure (fun _ _ => 1)
    | "polynomial" => pure (fun x y => 2*(x*(1-x)+y*(1-y)))
    | _ => throw "unknown source: use sine, polynomial, constant or zero"
  let o ← makeOperator n degree
  let rhs ← load o source
  let rhs ← field j "load" rhs
  let result ← solvePCG o rhs opts
  let canMeasure := result.solution.all Float.isFinite && (j.getObjVal? "load").toOption.isNone
  let errors ← if canMeasure && sourceName == "sine" then
    errorNorms o result.solution
    else if canMeasure && sourceName == "polynomial" then
      errorNorms o result.solution (fun x y => x*(1-x)*y*(1-y))
        (fun x y => ((1-2*x)*y*(1-y),x*(1-x)*(1-2*y)))
    else pure (0,0)
  let probe ← field j "values" (o.mesh.points.map fun (x,y) => x*x+2*x*y-3*y+1)
  let applied ← apply o probe
  let flat := fun {m n} (a : Mat Float m n) =>
    Array.ofFn fun (k : Fin (m*n)) =>
      if hi : k.val/n < m then if hj : k.val%n < n then
        Spec.get2 a ⟨k.val/n,hi⟩ ⟨k.val%n,hj⟩ else 0 else 0
  let reason := match result.reason with | .converged => "converged" | .breakdown => "breakdown" | .maxiter => "maxiter"
  let hasExact := canMeasure && (sourceName == "sine" || sourceName == "polynomial")
  let finite := jsonFloat
  return Json.mkObj [
    ("n",toJson n),("degree",toJson degree),("dtype",toJson "binary64"),
    ("source",toJson sourceName),("nodes",toJson o.mesh.points.size),
    ("interior_unknowns",toJson o.mesh.interior.size),("points",toJson (o.mesh.points.map fun (x,y) => Json.arr #[jsonFloat x,jsonFloat y])),
    ("cells",toJson o.mesh.cells),("boundary",toJson o.mesh.boundary),("interior",toJson o.mesh.interior),
    ("lobatto",numbers o.nodes),("q",numbers o.q),("weights",numbers o.weights),
    ("B",numbers (flat o.b)),("D",numbers (flat o.d)),("diagonal",numbers o.diagonal),
    ("load",numbers rhs),("probe",numbers probe),("applied",numbers applied),
    ("solution",numbers result.solution),("converged",toJson (result.reason == .converged)),
    ("reason",toJson reason),("iterations",toJson result.iterations),
    ("true_residual_norm",finite result.residualNorm),("relative_residual",finite result.relativeResidual),
    ("tolerance",finite result.tolerance),
    ("l2_error",if hasExact then finite errors.1 else Json.null),
    ("h1_seminorm_error",if hasExact then finite errors.2 else Json.null)]

/-- Positional demo, or a JSON array request for reproducible comparison tests. -/
def run (args : List String) : IO UInt32 := do
  let stdout ← IO.getStdout
  let runOne := fun request => match evaluate request with
    | .ok result => result
    | .error message => Json.mkObj [("error",toJson message)]
  match args with
  | ["--request",input,"--output",output] =>
    let text ← IO.FS.readFile input
    match Json.parse text >>= Json.getArr? with
    | .error message => throw (IO.userError message)
    | .ok requests =>
      IO.FS.writeFile output ((toJson (requests.map runOne)).pretty ++ "\n")
      return 0
  | [] | [_] | [_,_] =>
    let n := args[0]?.getD "8"
    let p := args[1]?.getD "4"
    match n.toNat?,p.toNat? with
    | some n,some p =>
      match evaluate (Json.mkObj [("n",toJson n),("degree",toJson p)]) with
      | .error message => (← IO.getStderr).putStrLn message; return 2
      | .ok result =>
        stdout.putStrLn result.pretty
        return if (result.getObjValAs? Bool "converged").toOption == some true then 0 else 1
    | _,_ => (← IO.getStderr).putStrLn "n and degree must be natural numbers"; return 2
  | _ =>
    (← IO.getStderr).putStrLn "Usage: poissonQuad [n [degree]] | --request INPUT.json --output OUTPUT.json"
    return 2

end PtxTorchLean.Poisson.CLI
