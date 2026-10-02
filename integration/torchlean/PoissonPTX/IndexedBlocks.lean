import PoissonPTX.IndexedMemory

namespace PtxTorchLean.Poisson.PTX.Indexed

theorem append (a : Block left s t) (b : Block right t u) : Block (left++right) s u := by
  induction a with
  | nil => exact b
  | cons one rest ih => exact .cons one (ih b)

theorem split (left right : List Instr) (run : Block (left++right) s t) :
    ∃ middle, Block left s middle ∧ Block right middle t := by
  induction left generalizing s with
  | nil => exact ⟨s,.nil,run⟩
  | cons i rest ih =>
    cases run with
    | cons one tail =>
      obtain ⟨middle,first,last⟩ := ih tail
      exact ⟨middle,.cons one first,last⟩

end PtxTorchLean.Poisson.PTX.Indexed
