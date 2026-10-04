import PoissonPTX.ScalarControlAdmission
import PoissonPTX.ScalarNormSources

namespace PtxTorchLean.Poisson.PTX.Scalar.Start
variable {a : Arena}

theorem admitted_publication
    (actual : Observed.Runs a.context (entry a.offset) (a.start memory regs) events final)
    (done : final.halted=true) (compatible : Sources.Compatible (a.start memory regs).core.memory events source)
    (admitted : Sources.NoFuture events source) :
    ∃ norm product tolerance,
      decode norm=Float.sqrt (decode (read64 memory (a.slot .rhsSquare))) ∧
      decode product=decode (read64 memory (a.slot .rtol))*decode norm ∧
      decode tolerance=maximum product (read64 memory (a.slot .atol)) ∧
      Sources.publish (a.start memory regs).core.memory events .global=publish a memory norm tolerance := by
  obtain ⟨norm,product,tolerance,hn,hp,ht,global⟩ := entry_publication (admitted_replay actual done compatible admitted) done
  have bytes := congrArg (fun m : Space → Memory => m .global) (Observed.runs_memory actual)
  exact ⟨norm,product,tolerance,hn,hp,ht,bytes.symm.trans global⟩

end PtxTorchLean.Poisson.PTX.Scalar.Start

namespace PtxTorchLean.Poisson.PTX.Scalar.Alpha
variable {a : Arena}

theorem admitted_publication
    (actual : Observed.Runs a.context (entry a.offset) (a.start memory regs) events final)
    (done : final.halted=true) (compatible : Sources.Compatible (a.start memory regs).core.memory events source)
    (admitted : Sources.NoFuture events source) :
    ∃ value, Allowed a memory value ∧ Sources.publish (a.start memory regs).core.memory events .global=publish a memory value := by
  obtain ⟨value,allowed,global⟩ := entry_publication (admitted_replay actual done compatible admitted) done
  have bytes := congrArg (fun m : Space → Memory => m .global) (Observed.runs_memory actual)
  exact ⟨value,allowed,bytes.symm.trans global⟩

end PtxTorchLean.Poisson.PTX.Scalar.Alpha

namespace PtxTorchLean.Poisson.PTX.Scalar.Beta
variable {a : Arena}

theorem admitted_publication
    (actual : Observed.Runs a.context (entry a.offset) (a.start memory regs) events final)
    (done : final.halted=true) (compatible : Sources.Compatible (a.start memory regs).core.memory events source)
    (admitted : Sources.NoFuture events source) :
    ∃ value square, Allowed a memory value ∧
      decode square=decode (read64 memory (a.slot .tolerance))*decode (read64 memory (a.slot .tolerance)) ∧
      Sources.publish (a.start memory regs).core.memory events .global=publish a memory value square := by
  obtain ⟨value,square,allowed,rounded,global⟩ := entry_publication (admitted_replay actual done compatible admitted) done
  have bytes := congrArg (fun m : Space → Memory => m .global) (Observed.runs_memory actual)
  exact ⟨value,square,allowed,rounded,bytes.symm.trans global⟩

end PtxTorchLean.Poisson.PTX.Scalar.Beta
