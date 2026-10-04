import PoissonPTX.DotProgramRegion

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

/-- The input prefix only reads global memory; it never stores or reads shared
memory, and contains no narrow index loads. -/
def inputSafe : Flow.Instr → Bool
  | .data (.data (.store64 ..)) | .data (.data (.load64 .shared ..)) | .data (.load32 ..) => false
  | _ => true

theorem input_safe (member : i∈DotInput.inputProgram count left right scratch) : inputSafe i=true := by
  simp only [DotInput.inputProgram,Flow.OperandWindow.program,Flow.OperandWindow.header,
    DotInput.setupCode,DotInput.body,loadCode,addressCode,List.map_cons,List.map_nil,
    List.map_append,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals rfl

theorem checked_tree_stores : ∀ slot : Fin 76,
    (match Reduction.Native.code[slot.val]? with
    | some (.data (.store64 sp ..)) => decide (sp=.shared)
    | _ => true)=true := by decide +kernel

/-- There is just one global store instruction in the complete entry. -/
theorem global_store_site
    (fetch : (program count left right output scratch)[pc]?=
      some (.flow (.data (.data (.store64 .global addr src))))) :
    pc=102 ∧ addr=.reg 2 ∧ src=.reg 8 := by
  by_cases before : pc<20
  · rw [input_fetch before] at fetch
    obtain ⟨i,found,equal⟩ := Option.map_eq_some_iff.mp fetch
    cases equal
    have safe := input_safe (List.mem_of_getElem? found)
    cases safe
  · by_cases inside : pc<96
    · have position : pc=20+(pc-20) := by omega
      rw [position,tree_fetch (by omega)] at fetch
      obtain ⟨native,found,equal⟩ := Option.map_eq_some_iff.mp fetch
      have bound : pc-20<76 := by omega
      have checked := checked_tree_stores ⟨pc-20,bound⟩
      rw [found] at checked
      cases native <;> cases equal
      cases checked
    · have position : pc=96+(pc-96) := by omega
      rw [position,tail_fetch] at fetch
      obtain ⟨i,found,equal⟩ := Option.map_eq_some_iff.mp fetch
      cases equal
      have bound : pc-96<8 := by
        have h := (List.getElem?_eq_some_iff.mp found).1
        simpa [tail] using h
      generalize hslot : pc-96=slot at found bound
      interval_cases slot <;> simp [tail] at found
      obtain ⟨rfl,rfl⟩ := found
      exact ⟨by omega,rfl,rfl⟩

end PtxTorchLean.Poisson.PTX.Concurrent.Dot
