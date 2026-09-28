import PoissonQuad

namespace PtxTorchLean.Poisson.Checks
open PtxTorchLean.Poisson

private def require (ok : Bool) (message : String) : IO Unit :=
  if ok then pure () else throw (IO.userError message)

private def get (x : Except String α) : IO α :=
  match x with | .ok v => pure v | .error e => throw (IO.userError e)

private def rejected (x : Except String α) : Bool := x.toOption.isNone

/-- Structural, quadrature, assembly and solver edge checks; numerical tests, not proofs. -/
def run : IO Unit := do
  require (rejected (makeOperator 0 2) && rejected (makeOperator 2 0) &&
    rejected (makeOperator 2 5)) "invalid mesh accepted"
  require (rejected (gaussRule 0) && rejected (gaussRule 7)) "invalid rule accepted"
  for q in [1:7] do
    let (xs,ws) ← get (gaussRule q)
    for k in [0:2*q] do
      let actual := (xs.zip ws).foldl (fun acc (x,w) => acc+w*x^(Float.ofNat k)) 0
      require ((actual-1/Float.ofNat (k+1)).abs < 3e-14) s!"quadrature moment {q}/{k}"
  for p in [1:5] do
    let o ← get (makeOperator 2 p)
    let (b,d) := lagrangeBasis o.nodes o.nodes
    for i in [:o.nodes.size] do
      let mut derivative := 0.0
      for j in [:o.nodes.size] do
        if hi : i < o.nodes.size then if hj : j < o.nodes.size then
          require ((Spec.get2 b ⟨i,hi⟩ ⟨j,hj⟩-(if i==j then 1 else 0)).abs < 1e-13) "nodal basis identity"
          derivative := derivative+Spec.get2 d ⟨i,hi⟩ ⟨j,hj⟩
      require (derivative.abs < 1e-13) "derivative partition"
    let constant ← get (apply o (Array.replicate o.mesh.points.size 1))
    require (constant.all fun x => x.abs < 2e-13) "constant in operator nullspace"
    let rhs ← get (load o (fun _ _ => 1))
    require (((rhs.foldl (· + ·) 0)-1).abs < 1e-13) "constant source integral"
    let zero ← get (solvePCG o (Array.replicate o.mesh.points.size 0))
    require (zero.reason == .converged && zero.iterations == 0 && zero.residualNorm == 0) "zero rhs"
    let limited ← get (solvePCG o rhs {maxiter := 0})
    require (limited.reason == .maxiter && limited.iterations == 0) "iteration limit"
    require (rejected (apply o #[]) && rejected (applyInterior o #[]) &&
      rejected (solvePCG o rhs {checkEvery := 0}) && rejected (solvePCG o rhs {rtol := 0}) &&
      rejected (solvePCG o rhs {rtol := -1}) &&
      rejected (load o (fun _ _ => 0/0))) "invalid vector/options/source accepted"
  let empty ← get (makeOperator 1 1)
  let solved ← get (solvePCG empty (← get (load empty)))
  require (solved.reason == .converged && solved.iterations == 0 && solved.solution.all (· == 0)) "no interior unknowns"
  let o ← get (makeOperator 2 2)
  let rhs ← get (load o)
  let tiny ← get (solvePCG o rhs {maxiter := 1, rtol := 1e-30})
  require (tiny.reason == .maxiter && tiny.residualNorm > tiny.tolerance) "false convergence"
  let overflow ← get (solvePCG o (Array.replicate o.mesh.points.size 1e308))
  require (overflow.reason == .breakdown) "nonfinite norm must report breakdown"
  -- Recover the actual small global matrix by applying the operator to basis vectors.
  let size := o.mesh.points.size
  let mut columns := #[]
  for j in [:size] do
    columns := columns.push (← get (apply o ((Array.replicate size 0).set! j 1)))
  for i in [:size] do
    require (((columns[i]!)[i]!-o.diagonal[i]!).abs < 2e-13) "assembled diagonal"
    for j in [:size] do
      require (((columns[i]!)[j]!-(columns[j]!)[i]!).abs < 2e-13) "operator symmetry"
  IO.println "Poisson checks passed: quadrature moments, basis, assembly, boundary and PCG edge cases."

#eval run
end PtxTorchLean.Poisson.Checks
