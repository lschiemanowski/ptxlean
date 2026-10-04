import PoissonPTX.DotAddressSyntax

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

/-- No tree branch jumps back into its initial three-instruction publication. -/
theorem checked_tree_entry : ∀ slot : Fin 76,
    (match Reduction.Native.code[slot.val]? with
    | some (.branch target) => decide (3≤target)
    | _ => true)=true := by decide +kernel

theorem outside_publication_targets {pc : Nat}
    (after : 20≤pc) (fetch : (program count left right output scratch)[pc]?=some (.flow i)) :
    NativeFlow.targets (23≤·) i := by
  by_cases inside : pc<96
  · have position : pc=20+(pc-20) := by omega
    rw [position,tree_fetch (by omega)] at fetch
    obtain ⟨native,found,equal⟩ := Option.map_eq_some_iff.mp fetch
    have checked := checked_tree_entry ⟨pc-20,by omega⟩
    rw [found] at checked
    cases native <;> cases equal
    · trivial
    · trivial
    · simp only [decide_eq_true_eq] at checked
      change 23≤20+_
      omega
  · have position : pc=96+(pc-96) := by omega
    rw [position,tail_fetch] at fetch
    obtain ⟨op,found,equal⟩ := Option.map_eq_some_iff.mp fetch
    cases equal
    have member := List.mem_of_getElem? found
    simp only [tail,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> trivial

theorem publication_prefix {pc : Nat} (after : 20≤pc) (before : pc≤22) :
    ∃ op, (program count left right output scratch)[pc]?=some (.flow (.data (.data op))) ∧
      (∀ r, r≠1 → r≠2 → SharedStore.keeps r op) := by
  have position : pc=20+(pc-20) := by omega
  rw [position,tree_fetch (by omega)]
  generalize h : pc-20=k
  have small : k≤2 := by omega
  interval_cases k
  · exact ⟨.wide8 1 (.reg 14),rfl,fun _ h _ => h⟩
  · exact ⟨.add64 2 (.reg 3) (.reg 1),rfl,fun _ _ h => h⟩
  · exact ⟨.store64 .shared (.offset 2 0) (.reg 8),rfl,fun _ _ _ => trivial⟩

theorem publication_keeps {pc r : Nat} (after : 20≤pc) (before : pc≤22)
    (fetch : (program count left right output scratch)[pc]?=some (.flow i))
    (notOffset : r≠1) (notAddress : r≠2) :
    NativeFlow.keeps r i := by
  obtain ⟨op,found,kept⟩ := publication_prefix after before (count:=count) (left:=left)
    (right:=right) (output:=output) (scratch:=scratch)
  rw [found] at fetch
  cases fetch
  exact kept r notOffset notAddress

theorem no_early_sync {pc : Nat} (before : pc≤22) :
    (program count left right output scratch)[pc]?≠some (.sync resource) := by
  by_cases input : pc<20
  · exact NativeFlow.no_prefix_sync input_region (by simpa only [DotInput.input_length] using input)
  · obtain ⟨op,found,_⟩ := publication_prefix (by omega) before (count:=count) (left:=left)
      (right:=right) (output:=output) (scratch:=scratch)
    rw [found]
    simp

end PtxTorchLean.Poisson.PTX.Concurrent.Dot
