import PoissonPTX.DotStoreProtection

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

/-- No branch jumps across the output store. This is checked from syntax,
independently of the value eventually written. -/
theorem protects_output : NativeFlow.Protects ctx (program count left right output scratch) 102 s := by
  intro i t access index fetch actual early
  apply NativeFlow.eval_upper actual early
  by_cases before : s.core.pc<96
  · have bounded := barrier_stops (count:=count) (left:=left) (right:=right) (output:=output) (scratch:=scratch)
      8 s.core.pc i fetch (by change s.core.pc≤95; omega)
    cases i <;> simp_all [NativeFlow.targets,barrierSite] <;> omega
  · have position : s.core.pc=96+(s.core.pc-96) := by omega
    rw [position,tail_fetch] at fetch
    obtain ⟨op,found,equal⟩ := Option.map_eq_some_iff.mp fetch
    cases equal
    have member := List.mem_of_getElem? found
    simp only [tail,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> trivial

/-- Reaching lane zero's final return entails a real global store occurrence.
The candidate existence theorem therefore cannot succeed with an empty output. -/
theorem output_exists {start : NativeFlow.State 256}
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (reset : start.core.barrier=Ptx.Barrier.reset generation)
    (entry : (start.core.lanes 0).pc=0) (returned : (final.core.lanes 0).pc=104) :
    ∃ access, Event.data 0 access∈events ∧ access.data.pc=102 ∧ access.data.store=true ∧ access.space=.global := by
  apply NativeFlow.crossed_store run (by intro t h; simp [reset,Ptx.Barrier.reset] at h)
    (sp:=.global) (addr:=.reg 2) (src:=.reg 8)
  · rw [show 102=96+6 by rfl,tail_fetch]; rfl
  · intro before earlier earlierIndices prior; exact protects_output
  · rw [entry]; decide
  · rw [returned]; decide

end PtxTorchLean.Poisson.PTX.Concurrent.Dot
