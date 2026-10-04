import PoissonPTX.DotInputTraversal
import PoissonPTX.ControlFlowOperandWindowExists

namespace PtxTorchLean.Poisson.PTX.DotInput

theorem traversal_exists (s : State) (bounded : count<2^30) (frame : Stable initial s)
    (safe : ∀ index<count, Valid (atCursor initial index) left right) :
    ∃ t, Flow.OperandWindow.Traversal origin 12 (.imm (BitVec.ofNat 64 count))
      ((body left right).map Indexed.Instr.data) s t := by
  have construct : ∀ remaining, ∀ s : State, count-cursor s=remaining → Stable initial s →
      ∃ t, Flow.OperandWindow.Traversal origin 12 (.imm (BitVec.ofNat 64 count))
        ((body left right).map Indexed.Instr.data) s t := by
    intro remaining
    induction remaining using Nat.strong_induction_on with
    | h remaining ih =>
      intro s distance frame
      by_cases inside : cursor s<count
      · have valid : Valid {s with pc:=origin+2} left right := valid_at frame (safe _ inside)
        obtain ⟨middle,block⟩ := exists_execution {s with pc:=origin+2} valid
        obtain ⟨_,increment,kept⟩ := correct block valid
        have incremented : cursor middle=cursor s+256 := progress inside bounded increment
        have smaller : count-cursor {middle with pc:=origin}<remaining := by
          change count-cursor middle<remaining
          rw [incremented]; omega
        obtain ⟨final,rest⟩ := ih _ smaller {middle with pc:=origin} rfl (stable_trans frame kept)
        refine ⟨final,.more ?_ (Indexed.scalar_block block) rest⟩
        simp only [test bounded,decide_eq_false_iff_not]; omega
      · exact ⟨_,.done (by simp only [test bounded,decide_eq_true_eq]; omega)⟩
  exact construct _ s rfl frame

end PtxTorchLean.Poisson.PTX.DotInput
