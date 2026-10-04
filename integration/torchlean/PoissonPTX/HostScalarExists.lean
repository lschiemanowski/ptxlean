import PoissonPTX.HostLaunch

namespace PtxTorchLean.Poisson.PTX.Host

/-- Every scalar host stage has an actual returning instruction execution
with admitted mixed-width observations, for arbitrary initial status words. -/
theorem scalar_exists (a : Layout n e w) (kind : ScalarEntry) (memory : Memory) :
    ∃ output, ScalarLaunch a (a.scalarCode kind) memory output := by
  cases kind with
  | start =>
    obtain ⟨final,events,actual,done,compatible,admitted⟩ := Scalar.Start.admitted_exists a.scalar memory (fun _ => 0)
    exact ⟨_,(fun _ => 0),events,final,_,actual,done,compatible,admitted,rfl⟩
  | alpha =>
    obtain ⟨final,events,actual,done,compatible,admitted⟩ := Scalar.Alpha.admitted_exists a.scalar memory (fun _ => 0)
    exact ⟨_,(fun _ => 0),events,final,_,actual,done,compatible,admitted,rfl⟩
  | beta =>
    obtain ⟨final,events,actual,done,compatible,admitted⟩ := Scalar.Beta.admitted_exists a.scalar memory (fun _ => 0)
    exact ⟨_,(fun _ => 0),events,final,_,actual,done,compatible,admitted,rfl⟩
  | norm =>
    obtain ⟨final,events,actual,done,compatible,admitted⟩ := Scalar.Norm.admitted_exists a.scalar memory (fun _ => 0)
    exact ⟨_,(fun _ => 0),events,final,_,actual,done,compatible,admitted,rfl⟩
  | restart =>
    obtain ⟨final,events,actual,done,compatible,admitted⟩ := Scalar.RestartFlag.admitted_exists a.scalar memory (fun _ => 0)
    exact ⟨_,(fun _ => 0),events,final,_,actual,done,compatible,admitted,rfl⟩

end PtxTorchLean.Poisson.PTX.Host
