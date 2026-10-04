import PoissonPTX.ByteHistoryAdmission

namespace PtxTorchLean.Poisson.PTX.Concurrent.ByteHistory.Checks

/-- These exercise the byte-publication helper, not aligned PTX execution. -/
def writes : List (Event 1) :=
  [.data 0 ⟨.global,⟨0,true,8,0x1122334455667788⟩⟩,
   .data 0 ⟨.global,⟨1,true,12,0x8899aabbccddeeff⟩⟩]

theorem partial_overlap : read64 (publish (fun _ _ => 0) writes .global) 8=0xccddeeff55667788 := by decide +kernel

theorem real_offsets : (∀ k : Fin 4, origin writes .global (8+k.val)=.store 0 ⟨k.val,by omega⟩) ∧
    (∀ k : Fin 4, origin writes .global (12+k.val)=.store 1 ⟨k.val,by omega⟩) := by decide +kernel

theorem spaces_remain_separate : origin writes .shared 12=.initial ∧
    read64 (publish (fun _ _ => 0) writes .shared) 8=0 := by decide +kernel

theorem store_end_is_exclusive : origin writes .global 20=.initial := by decide +kernel

end PtxTorchLean.Poisson.PTX.Concurrent.ByteHistory.Checks
