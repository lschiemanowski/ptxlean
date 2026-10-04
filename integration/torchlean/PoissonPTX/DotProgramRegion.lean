import PoissonPTX.DotProgram
import PoissonPTX.NativeFlowPrefixComplete

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

/-- Input control flow either repeats its own loop or exits at position 20.
No return or barrier can silently end the prefix. -/
theorem input_syntax (member : i∈DotInput.inputProgram count left right scratch) :
    NativeFlow.targets (·≤20) i ∧ NativeFlow.continues i := by
  simp only [DotInput.inputProgram,Flow.OperandWindow.program,Flow.OperandWindow.header,
    DotInput.setupCode,DotInput.body,loadCode,addressCode,List.map_cons,List.map_nil,
    List.map_append,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [NativeFlow.targets,NativeFlow.continues]

theorem tree_targets (fetch : treeInstruction native=.flow i) : NativeFlow.targets (20≤·) i := by
  cases native <;> cases fetch <;> simp [NativeFlow.targets]

theorem tail_targets (member : i∈tail output) : NativeFlow.targets (20≤·) i := by
  simp only [tail,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> trivial

theorem input_region : NativeFlow.Region (program count left right output scratch)
    (DotInput.inputProgram count left right scratch) := by
  constructor
  · intro pc before
    exact input_fetch (by simpa only [DotInput.input_length] using before)
  · intro pc i before fetch
    simpa only [DotInput.input_length] using (input_syntax (List.mem_of_getElem? fetch)).1
  · intro pc i past fetch
    have after : 20≤pc := by simpa only [DotInput.input_length] using past
    by_cases inside : pc<96
    · have position : pc=20+(pc-20) := by omega
      rw [position,tree_fetch (by omega)] at fetch
      obtain ⟨native,_,equal⟩ := Option.map_eq_some_iff.mp fetch
      simpa only [DotInput.input_length] using tree_targets equal
    · have position : pc=96+(pc-96) := by omega
      rw [position,tail_fetch] at fetch
      obtain ⟨op,found,equal⟩ := Option.map_eq_some_iff.mp fetch
      cases equal
      simpa only [DotInput.input_length] using tail_targets (List.mem_of_getElem? found)

theorem completed_input
    (actual : NativeFlow.Runs cfg ctx (program count left right output scratch) s events indices t)
    (aligned : Aligned s.core) (start : (s.core.lanes owner).pc=0)
    (live : s.halted owner=false) (returned : t.halted owner=true) :
    ∃ next words localIndices,
      Flow.Observed.Runs (ctx owner) (DotInput.inputProgram count left right scratch)
        (NativeFlow.lane s owner) words localIndices next ∧
      next.core.pc=20 ∧ next.halted=false ∧
      (∀ a∈words, Event.data owner a∈events) ∧ (∀ a∈localIndices, (owner,a)∈indices) := by
  simpa only [DotInput.input_length] using NativeFlow.prefix_complete input_region
    (fun i member => (input_syntax member).2) actual aligned (by simp [start]) live returned

end PtxTorchLean.Poisson.PTX.Concurrent.Dot
