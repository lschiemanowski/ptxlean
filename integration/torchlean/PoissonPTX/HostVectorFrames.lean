import PoissonPTX.HostStorage
import PoissonPTX.InitializeRoundedCorrect
import PoissonPTX.RestartVectorsRoundedCorrect
import PoissonPTX.UpdateXRZRoundedCorrect
import PoissonPTX.AffineUpdateRoundedCorrect
import PoissonPTX.FreshResidualRoundedCorrect
import PoissonPTX.AssemblyRoundedCorrect

namespace PtxTorchLean.Poisson.PTX.Host

variable {n e w : Nat} {a : Layout n e w}

/-- Every completed actual vector launch writes only its named working
buffers. Padding contributes no hidden writes. -/
theorem vector_frame (actual : VectorLaunch a (a.vectorCode kind) memory output) :
    a.Writes kind.writes memory output := by
  obtain ⟨regs,words,indices,final,source,indexSource,run,done,compatible,indexCompatible,admitted,rfl⟩ := actual
  intro byte outside
  cases kind with
  | «initialize» =>
    apply Initialize.Arena.rounded_outside (a:=a.initialize) (regs:=regs) run done
    intro f written
    rcases written with rfl|rfl|rfl|rfl|rfl
    · exact outside .rhs (by simp [VectorEntry.writes])
    · exact outside .r (by simp [VectorEntry.writes])
    · exact outside .z (by simp [VectorEntry.writes])
    · exact outside .p (by simp [VectorEntry.writes])
    · exact outside .x (by simp [VectorEntry.writes])
  | updateXRZ =>
    apply UpdateXRZ.Arena.rounded_outside (a:=a.updateXRZ) (regs:=regs) run done
    intro f written
    rcases written with rfl|rfl|rfl
    · exact outside .x (by simp [VectorEntry.writes])
    · exact outside .r (by simp [VectorEntry.writes])
    · exact outside .z (by simp [VectorEntry.writes])
  | restart =>
    apply RestartVectors.Arena.rounded_outside (a:=a.restart) (regs:=regs) run done
    intro f written
    rcases written with rfl|rfl|rfl
    · exact outside .r (by simp [VectorEntry.writes])
    · exact outside .z (by simp [VectorEntry.writes])
    · exact outside .p (by simp [VectorEntry.writes])
  | updateP => exact AffineUpdate.Arena.rounded_outside (a:=a.updateP) (regs:=regs) run done (outside .p (by simp [VectorEntry.writes]))
  | residual => exact FreshResidual.Arena.rounded_outside (a:=a.residual) (regs:=regs) run done (outside .trueR (by simp [VectorEntry.writes]))
  | assembly probe =>
    apply Assembly.Arena.rounded_outside (a:=a.assembly probe) (regs:=regs) run done
    have h := outside (assemblyOutput probe) (by simp [VectorEntry.writes])
    cases probe <;> exact h

theorem vector_static (actual : VectorLaunch a (a.vectorCode kind) memory output) : a.Static memory output :=
  (vector_frame actual).static (vector_writes_mutable kind)

end PtxTorchLean.Poisson.PTX.Host
