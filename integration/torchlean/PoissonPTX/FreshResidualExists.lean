import PoissonPTX.GlobalThreadSources
import PoissonPTX.FreshResidualParallel
import PoissonPTX.FreshResidualRecorded
import PoissonPTX.ObservedParallelExists

namespace PtxTorchLean.Poisson.PTX.FreshResidual
open Concurrent

theorem Arena.local_exists (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n) :
    ∃ t, Flow.Runs (a.context i) a.program (a.start memory regs) t ∧ t.halted=true := by
  let old := Weak.Residual.Parallel.Arena.start a memory (fun _ => regs) i
  have hr := (Weak.Residual.Parallel.Arena.inputs a memory (fun _ => regs)).valid i a.rhs (by simp [Weak.Residual.Parallel.Arena.inputs])
  have ha := (Weak.Residual.Parallel.Arena.inputs a memory (fun _ => regs)).valid i a.ap (by simp [Weak.Residual.Parallel.Arena.inputs])
  have ho := (Weak.Residual.Parallel.Arena.inputs a memory (fun _ => regs)).valid i a.output (by simp [Weak.Residual.Parallel.Arena.inputs])
  obtain ⟨t,run⟩ := Kernel.Residual.fetched_exists (a.context i) old (BitVec.ofNat 32 n) a.rhs a.ap a.output
    rfl rfl (a.live i) hr ha ho
  have done := (Kernel.Residual.fetched_correct (a.context i) old t (BitVec.ofNat 32 n) a.rhs a.ap a.output
    rfl rfl (a.live i) hr ha ho run).2
  refine ⟨Kernel.ToFlow.state t,?_,done⟩
  simpa [Arena.program,entry,Arena.start,old,Weak.Residual.Parallel.Arena.start,Kernel.ToFlow.state] using Kernel.ToFlow.run_lift run

/-- A finite actual execution exists for all valid input words, including NaNs
and infinities. Its reads have initial-byte sources; termination is constructive. -/
theorem Arena.parallel_exists (a : Arena n) (memory : Memory) (regs : Fin n → Registers) :
    ∃ words indices final,
      Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices final ∧
      (∀ i, (final i).halted=true) ∧
      Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0)
        words (fun _ _ => .initial) ∧
      Visibility.GlobalThreadSources words (fun _ _ => .initial) ∧
      indices=[] ∧
      ∀ i, decode (read64 (GlobalPublication.publish memory words) (a.slot a.output i))=a.value memory i := by
  classical
  choose final runs done using fun i => a.local_exists memory (regs i) i
  have recorded := fun i => recorded_witness (runs i) (address_initial rfl)
    (show BeforeStore memory (a.start memory (regs i)) from by intro _; rfl)
  choose localWords localIndices observed wordValues empty using recorded
  obtain ⟨words,indices,actual,wordMembers,indexMembers⟩ := Flow.Parallel.all_threads localWords localIndices observed
  have compatible : Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0)
      words (fun _ _ => .initial) := by
    intro r reader read located load k
    have value := wordValues reader read (wordMembers reader read (List.mem_of_getElem? located)) load
    change byte read.data.value k.val=(match read.space with | .global => memory | .shared => fun _ => 0) (read.data.address+k.val)
    rw [value.1,value.2,Sources.byte_read64]
  exact ⟨words,indices,final,actual,done,compatible,Visibility.initial_thread_sources,
    a.indices_empty actual,a.parallel_value actual compatible done⟩

end PtxTorchLean.Poisson.PTX.FreshResidual
