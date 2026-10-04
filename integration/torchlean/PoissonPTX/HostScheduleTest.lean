import PoissonPTX.HostScheduleEval
import Lean

namespace PtxTorchLean.Poisson.PTX.Host.Test
open Lean

/-- A small physical scalar arena used only in differential scheduling tests. -/
def offset : Scalar.Field → Word
  | .rhsSquare => 0 | .trueSquare => 8 | .rhsNorm => 16 | .residual => 24
  | .rtol => 32 | .atol => 40 | .tolerance => 48 | .rho => 56 | .rhoNext => 64
  | .denominator => 72 | .rr => 80 | .alpha => 88 | .beta => 96
  | .active => 104 | .broken => 112 | .useStep => 120

def arena : Scalar.Arena where
  base := 0
  bytes := 128
  offset := offset
  baseAligned := by decide
  aligned := by intro f; cases f <;> decide
  fit := by intro f; cases f <;> decide
  noWrap := by decide
  apart := by intro f g h; cases f <;> cases g <;> simp_all [offset,Scalar.Field.width]

def field (j : Json) (name : String) : Except String Nat := do (← j.getObjVal? name).getNat?

def word (j : Json) (name : String) : Except String Word := do
  let value ← field j name
  if value < 2^64 then pure (BitVec.ofNat 64 value) else throw "word overflow"

def reasonName : Reason → String
  | .converged => "converged" | .breakdown => "breakdown" | .maxiter => "maxiter"

/-- Every mock residual-norm launch publishes the supplied status words.
All other launches are identities. This isolates host control from arithmetic. -/
def runCase (j : Json) : Except String Json := do
  let maximum ← field j "maximum"
  let interval ← field j "interval"
  if hi : 0 < interval then
    let norm ← word j "norm"
    let tolerance ← word j "tolerance"
    let residual ← word j "residual"
    let active ← field j "active"
    let broken ← field j "broken"
    let memory := write64 (write64 (fun _ => 0) (arena.slot .rhsNorm) norm) (arena.slot .tolerance) tolerance
    let step : Entry → Memory → Memory := fun entry memory =>
      if entry = .residualNorm then
        write32 (write32 (write64 memory (arena.slot .residual) residual)
          (arena.slot .active) (BitVec.ofNat 32 active)) (arena.slot .broken) (BitVec.ofNat 32 broken)
      else memory
    let (trace,report,_) := evaluate step (program arena ⟨maximum,interval,hi⟩) memory
    pure (Json.mkObj [
      ("launches",toJson (trace.map Entry.name)),
      ("iterations",toJson report.iterations),("reason",toJson (reasonName report.reason)),
      ("restarts",toJson report.restarts),("residual",toJson report.residual.toNat),
      ("checks",toJson (report.checks.map fun check => Json.mkObj [
        ("iteration",toJson check.iteration),("residual",toJson check.residual.toNat),
        ("active",toJson (check.active != 0)),("broken",toJson (check.broken != 0))]))])
  else throw "interval must be positive"

end PtxTorchLean.Poisson.PTX.Host.Test
