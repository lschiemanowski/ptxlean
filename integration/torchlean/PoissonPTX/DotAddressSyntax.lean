import PoissonPTX.DotProgramRegion
import PoissonPTX.NativeFlowFrame

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

/-- The arena base is loaded once, at position 1, and is never overwritten. -/
theorem input_keeps_base (fetch : (DotInput.inputProgram count left right scratch)[pc]?=some i)
    (other : pc≠1) : NativeFlow.keeps 0 i := by
  have small : pc<20 := by
    have := (List.getElem?_eq_some_iff.mp fetch).1
    simpa only [DotInput.input_length] using this
  interval_cases pc <;>
    simp_all [DotInput.inputProgram,Flow.OperandWindow.program,Flow.OperandWindow.header,
      DotInput.setupCode,DotInput.body,loadCode,addressCode]
  all_goals cases fetch; simp [NativeFlow.keeps,Indexed.keeps,SharedStore.keeps]

/-- These checks concern only the fixed native tree's instruction syntax. -/
theorem checked_tree : ∀ slot : Fin 76,
    (match Reduction.Native.code[slot.val]? with
    | some (.data op) => AddressHold.keep 0 op
    | some (.branch target) => decide (target≤76)
    | _ => true)=true := by decide +kernel

theorem tree_base {slot : Nat} (fetch : Reduction.Native.code[slot]?=some native)
    (ordinary : treeInstruction native=.flow i) :
    NativeFlow.keeps 0 i ∧ NativeFlow.targets (·≤96) i := by
  have bound := (List.getElem?_eq_some_iff.mp fetch).1
  rw [Reduction.Native.length] at bound
  have checked := checked_tree ⟨slot,bound⟩
  rw [fetch] at checked
  cases native <;> cases ordinary
  · exact ⟨AddressHold.keep_correct.mp checked,trivial⟩
  · exact ⟨trivial,trivial⟩
  · simp only [decide_eq_true_eq] at checked
    exact ⟨trivial,by change 20+_≤96; omega⟩

end PtxTorchLean.Poisson.PTX.Concurrent.Dot
