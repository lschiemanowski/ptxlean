import PoissonPTX.ScalarArena

namespace PtxTorchLean.Poisson.PTX.Host

/-- Entry names are distinct even when they share an instruction template:
their physical input and output arguments differ. -/
inductive Entry where
  | elementProbe | assembleProbe | initialize | dotRhs | dotRz | start
  | elementP | assembleAp | dotPap | coefficientAlpha | updateXRZ
  | dotNext | dotRR | coefficientBeta | updateP
  | elementX | trueResidual | dotTrue | residualNorm | restartVectors | restartFlag
  deriving DecidableEq, Repr

def Entry.name : Entry → String
  | .elementProbe => "element_probe" | .assembleProbe => "assemble_probe"
  | .initialize => "initialize" | .dotRhs => "dot_rhs" | .dotRz => "dot_rz" | .start => "start"
  | .elementP => "element_p" | .assembleAp => "assemble_ap" | .dotPap => "dot_pap"
  | .coefficientAlpha => "coefficient_alpha" | .updateXRZ => "update_xrz"
  | .dotNext => "dot_next" | .dotRR => "dot_rr" | .coefficientBeta => "coefficient_beta" | .updateP => "update_p"
  | .elementX => "element_x" | .trueResidual => "true_residual" | .dotTrue => "dot_true"
  | .residualNorm => "residual_norm" | .restartVectors => "restart_vectors" | .restartFlag => "restart_flag"

def preparation : List Entry := [.elementProbe,.assembleProbe,.initialize,.dotRhs,.dotRz,.start]
def iteration : List Entry := [.elementP,.assembleAp,.dotPap,.coefficientAlpha,.updateXRZ,.dotNext,.dotRR,.coefficientBeta,.updateP]
def checkResidual : List Entry := [.elementX,.assembleAp,.trueResidual,.dotTrue,.residualNorm]
def restart : List Entry := [.restartVectors,.dotRz,.restartFlag]

structure Options where
  maximum : Nat
  interval : Nat
  positive : 0 < interval

inductive Reason where
  | converged | breakdown | maxiter
  deriving DecidableEq, Repr

structure Check where
  iteration : Nat
  residual : Word
  active : BitVec 32
  broken : BitVec 32

structure Report where
  iterations : Nat
  reason : Reason
  rhsNorm : Word
  tolerance : Word
  residual : Word
  restarts : Nat
  checks : List Check

/-- A host program can request a launch, inspect the current published bytes,
or return. Inspection does not change memory. Kernel execution is defined
separately and must supply actual instruction histories. -/
inductive Plan where
  | finish (report : Report)
  | launch (entry : Entry) (next : Plan)
  | inspect (next : Memory → Plan)

def launches (entries : List Entry) (next : Plan) : Plan := entries.foldr Plan.launch next

/-- Host comparisons use the same decoded binary64 values as the status bytes.
NaNs fail the ordered comparison; nonfinite norms trigger breakdown first. -/
def finite (word : Word) : Bool := (decode word).isFinite

def within (norm tolerance : Word) : Bool := Scalar.Comparison.apply .le norm tolerance

def inspectCheck (a : Scalar.Arena) (memory : Memory) (it : Nat) : Check :=
  ⟨it,read64 memory (a.slot .residual),read32 memory (a.slot .active),read32 memory (a.slot .broken)⟩

/-- Structural recursion uses the real iteration budget. At the final
iteration the fresh residual is checked regardless of the check interval. -/
def loop (a : Scalar.Arena) (interval : Nat) : Nat → Report → Plan
  | 0,report => .finish {report with reason:=.maxiter}
  | remaining+1,report =>
    let next := {report with iterations:=report.iterations+1}
    launches iteration (
      if next.iterations%interval=0 ∨ remaining=0 then
        launches checkResidual (.inspect fun memory =>
          let check := inspectCheck a memory next.iterations
          let checked := {next with residual:=check.residual,checks:=next.checks++[check]}
          if !finite check.residual then .finish {checked with reason:=.breakdown}
          else if within check.residual checked.tolerance then .finish {checked with reason:=.converged}
          else if check.broken != 0 then .finish {checked with reason:=.breakdown}
          else if check.active=0 then
            launches restart (loop a interval remaining {checked with restarts:=checked.restarts+1})
          else loop a interval remaining checked)
      else loop a interval remaining next)

/-- The program of solve after argument validation. Every branch consumes the
actual published status bytes. A numerical convergence flag is not a certificate. -/
def program (a : Scalar.Arena) (options : Options) : Plan :=
  launches preparation (.inspect fun memory =>
    let norm := read64 memory (a.slot .rhsNorm)
    let tolerance := read64 memory (a.slot .tolerance)
    let report : Report := ⟨0,.maxiter,norm,tolerance,norm,0,[]⟩
    if !finite norm then .finish {report with reason:=.breakdown}
    else if within norm tolerance then .finish {report with reason:=.converged}
    else loop a options.interval options.maximum report)

end PtxTorchLean.Poisson.PTX.Host
