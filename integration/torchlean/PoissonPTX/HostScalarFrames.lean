import PoissonPTX.HostStorage
import PoissonPTX.ScalarAdmittedPublication

namespace PtxTorchLean.Poisson.PTX.Host

variable {n e w : Nat} {a : Layout n e w}

/-- Mixed-width scalar publications preserve all bytes outside the fields
actually written by the emitted entry. -/
theorem scalar_frame (actual : ScalarLaunch a (a.scalarCode kind) memory output) :
    a.Writes (kind.writes.map Field.scalar) memory output := by
  obtain ⟨regs,events,final,source,run,done,compatible,admitted,rfl⟩ := actual
  intro byte outside
  have apart (f : Scalar.Field) (member : f∈kind.writes) :
      byte<a.scalar.slot f ∨ a.scalar.slot f+f.width≤byte := by
    have h := outside (.scalar f) (List.mem_map.mpr ⟨f,member,rfl⟩)
    simpa [Field.count,Field.width,Layout.slot,Layout.scalar,Scalar.Arena.slot] using h
  cases kind with
  | start =>
    obtain ⟨norm,product,tolerance,_,_,_,publication⟩ := Scalar.Start.admitted_publication (a:=a.scalar) (regs:=regs) run done compatible admitted
    rw [publication]
    exact Scalar.Start.published_outside a.scalar memory norm tolerance byte apart
  | alpha =>
    obtain ⟨value,_,publication⟩ := Scalar.Alpha.admitted_publication (a:=a.scalar) (regs:=regs) run done compatible admitted
    rw [publication]
    exact Scalar.Alpha.published_outside a.scalar memory value byte apart
  | beta =>
    obtain ⟨value,square,_,_,publication⟩ := Scalar.Beta.admitted_publication (a:=a.scalar) (regs:=regs) run done compatible admitted
    rw [publication]
    exact Scalar.Beta.published_outside a.scalar memory value square byte apart
  | norm =>
    exact (Scalar.Norm.admitted_publication (a:=a.scalar) (regs:=regs) run done compatible admitted).2 byte (apart .residual (by simp [ScalarEntry.writes]))
  | restart =>
    exact (Scalar.RestartFlag.admitted_publication (a:=a.scalar) (regs:=regs) run done compatible admitted).2 byte (apart .active (by simp [ScalarEntry.writes]))

theorem scalar_static (actual : ScalarLaunch a (a.scalarCode kind) memory output) : a.Static memory output :=
  (scalar_frame actual).static (scalar_writes_mutable kind)

end PtxTorchLean.Poisson.PTX.Host
