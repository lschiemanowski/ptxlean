import PoissonPTX.CellWitnessBody
import PoissonPTX.CellEntryRecorded
import PoissonPTX.CellWholeBounds
import PoissonPTX.CellFinalLayout

namespace PtxTorchLean.Poisson.PTX.CellEntry

theorem Local.finish_allocation (space : Space) :
    (Local.finish ctx width cells source s).core.start space=s.core.start space ∧
    (Local.finish ctx width cells source s).core.bytes space=s.core.bytes space := by
  simp only [Local.finish]
  split <;> cases space <;> exact ⟨rfl,rfl⟩

/-- Derive physical allocation and initial symbolic addresses for the body
from a completed real gather. No arithmetic output or shared snapshot is an
input to this conversion. -/
theorem witness_ready {start final : State 32}
    (launch : Concurrent.CellMiddle.Numeric.Launch width bases (resume final))
    (result : ∀ u, lane final u=Local.finish (CellPrologue.threadContext bases cell u)
      width cells source (lane start u))
    (physical : ∀ u, Concurrent.CellConsumer.Witness.Allocation width bases (start.core.lanes u)) :
    Concurrent.CellConsumer.Witness.Ready width bases (resume final) := by
  constructor
  · intro u space
    have frame := Local.finish_allocation (ctx:=CellPrologue.threadContext bases cell u)
      (width:=width) (cells:=cells) (source:=source) (s:=lane start u) space
    have same := congrArg (fun s : CellPrologue.State => s.core) (result u)
    have starts : (final.core.lanes u).start space=(start.core.lanes u).start space := by
      exact (congrArg (fun s : PTX.State => s.start space) same).trans frame.1
    have sizes : (final.core.lanes u).bytes space=(start.core.lanes u).bytes space := by
      exact (congrArg (fun s : PTX.State => s.bytes space) same).trans frame.2
    have old := physical u space
    have resumedStart : ((resume final).lanes u).start space=(final.core.lanes u).start space := by cases space <;> rfl
    have resumedBytes : ((resume final).lanes u).bytes space=(final.core.lanes u).bytes space := by cases space <;> rfl
    simpa only [resumedStart,resumedBytes,starts,sizes] using old
  · intro u active
    have symbolic := launch.symbolic .addresses (fun _ _ => 0) u active
    simpa only [launch.pcs,Concurrent.Symbolic.at_zero] using symbolic

end PtxTorchLean.Poisson.PTX.CellEntry
