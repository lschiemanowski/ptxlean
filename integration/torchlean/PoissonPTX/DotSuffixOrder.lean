import PoissonPTX.DotPublicationSyntax
import PoissonPTX.NativeFlowAccessOrder

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

theorem checked_forward_targets : ∀ slot : Fin 76,
    (match Reduction.Native.code[slot.val]? with
    | some (.branch target) => decide (slot.val≤target)
    | _ => true)=true := by decide +kernel

/-- The native input loop may move backward, but no instruction can move back
through the shared publication or tree. The check covers the actual targets. -/
theorem suffix_forward : NativeFlow.ForwardFrom (program count left right output scratch) 20 := by
  intro pc i fetch
  by_cases input : pc<20
  · rw [input_fetch input] at fetch
    obtain ⟨op,found,equal⟩ := Option.map_eq_some_iff.mp fetch
    cases equal
    cases i <;> simp_all [NativeFlow.targets] <;> omega
  · by_cases inside : pc<96
    · have position : pc=20+(pc-20) := by omega
      rw [position,tree_fetch (by omega)] at fetch
      obtain ⟨native,found,equal⟩ := Option.map_eq_some_iff.mp fetch
      have checked := checked_forward_targets ⟨pc-20,by omega⟩
      rw [found] at checked
      cases native <;> cases equal
      · trivial
      · trivial
      · simp only [decide_eq_true_eq] at checked
        change max 20 pc≤max 20 (20+_)
        omega
    · have position : pc=96+(pc-96) := by omega
      rw [position,tail_fetch] at fetch
      obtain ⟨op,found,equal⟩ := Option.map_eq_some_iff.mp fetch
      cases equal
      have member := List.mem_of_getElem? found
      simp only [tail,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> trivial

end PtxTorchLean.Poisson.PTX.Concurrent.Dot
