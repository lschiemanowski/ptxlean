import PoissonPTX.GlobalPublication
import PoissonPTX.RoundedLaunch
import PoissonPTX.HostUpdateLayout
import PoissonPTX.HostAssemblyLayout
import PoissonPTX.ObservedParallel
import PoissonPTX.GlobalThreadSources
import PoissonPTX.ScalarNormAdmission
import PoissonPTX.ScalarControlAdmission

namespace PtxTorchLean.Poisson.PTX.Host

/-- One standard vector launch starts from the preceding published global
bytes and fresh local registers. No output or load value is installed. -/
def Layout.flowStart (a : Layout n e w) (memory : Memory) (regs : Registers) : Flow.State :=
  ⟨{pc:=0,regs:=regs,global:=memory,shared:=fun _ => 0,globalStart:=a.base.toNat,
    globalBytes:=a.bytes,sharedStart:=0,sharedBytes:=0},fun _ => false,false⟩

/-- A full rounded launch with actual instructions, all returns and necessary
word/index source admission. The output is its actual byte publication. -/
def VectorLaunch (a : Layout n e w) (code : List Flow.Instr) (memory output : Memory) : Prop :=
  ∃ (regs : Fin (Rounded.count n) → Registers), ∃ words indices final wordSource indexSource,
    Flow.Parallel.Runs (Rounded.context a.base) code (fun i => a.flowStart memory (regs i)) words indices final ∧
    (∀ i, (final i).halted=true) ∧
    Concurrent.Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0) words wordSource ∧
    IndexSources.Compatible memory words indices indexSource ∧
    Concurrent.Visibility.GlobalThreadSources words wordSource ∧
    output=Concurrent.GlobalPublication.publish memory words

/-- The scalar entries use their proved mixed-width observations, including
four-byte flags, and the actual chronological source condition. -/
def ScalarLaunch (a : Layout n e w) (code : List Scalar.Instr) (memory output : Memory) : Prop :=
  ∃ regs events final source,
    Scalar.Observed.Runs a.scalar.context code (a.scalar.start memory regs) events final ∧
    final.halted=true ∧
    Scalar.Sources.Compatible (a.scalar.start memory regs).core.memory events source ∧
    Scalar.Sources.NoFuture events source ∧
    output=Scalar.Sources.publish (a.scalar.start memory regs).core.memory events .global

inductive VectorEntry where
  | initialize | updateXRZ | updateP | restart | residual | assembly (probe : Bool)
  deriving DecidableEq, Repr

def VectorEntry.entry : VectorEntry → Entry
  | .initialize => .initialize | .updateXRZ => .updateXRZ | .updateP => .updateP
  | .restart => .restartVectors | .residual => .trueResidual
  | .assembly probe => if probe then .assembleProbe else .assembleAp

def Layout.vectorCode (a : Layout n e w) : VectorEntry → List Flow.Instr
  | .initialize => Initialize.Arena.program a.initialize
  | .updateXRZ => a.updateXRZ.program
  | .updateP => a.updateP.program
  | .restart => RestartVectors.Arena.program a.restart
  | .residual => FreshResidual.Arena.program a.residual
  | .assembly probe =>
    let b := a.assembly probe
    Assembly.entryCode (BitVec.ofNat 32 n) b.offsets b.entries b.element (!probe) b.boundary b.output

inductive ScalarEntry where
  | start | alpha | beta | norm | restart
  deriving DecidableEq, Repr

def ScalarEntry.entry : ScalarEntry → Entry
  | .start => .start | .alpha => .coefficientAlpha | .beta => .coefficientBeta
  | .norm => .residualNorm | .restart => .restartFlag

def Layout.scalarCode (a : Layout n e w) : ScalarEntry → List Scalar.Instr
  | .start => Scalar.Start.entry a.scalar.offset
  | .alpha => Scalar.Alpha.entry a.scalar.offset
  | .beta => Scalar.Beta.entry a.scalar.offset
  | .norm => Scalar.Norm.entry (a.scalar.offset .trueSquare) (a.scalar.offset .residual)
  | .restart => Scalar.RestartFlag.entry (a.scalar.offset .active)

end PtxTorchLean.Poisson.PTX.Host
