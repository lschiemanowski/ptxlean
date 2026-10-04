import PoissonPTX.DotInputAccess

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

/-- Every observation in the actual fetched input trace belongs to an input
array element. This is independent of the candidate words chosen by loads. -/
theorem input_observations
    (run : Flow.Observed.Runs ctx (DotInput.inputProgram count left right scratch) s words indices t)
    (entry : s.core.pc=0) (bounded : count<2^30)
    (room : ∀ off∈[left,right], ctx.arena.toNat+off.toNat+count*8≤2^64) :
    (∀ a∈words, InputWord ctx.arena count left right a) ∧ indices=[] := by
  have walked := Flow.Observed.walk (P:=fun u => AddressReady ctx.arena 0 u ∧ InputReady count left right u)
    (W:=InputWord ctx.arena count left right) (I:=fun _ => False)
    run (fun _ member => member) (fun _ member => member)
    ⟨address_ready_initial entry,input_ready_initial entry⟩ (by
      intro before after access index step _ _ ready
      obtain ⟨_,i,fetch,actual⟩ := step
      refine ⟨⟨input_address fetch actual ready.1,input_footprint_step fetch actual bounded ready.2⟩,?_,?_⟩
      · intro a observed
        rw [observed] at actual
        exact input_access fetch actual bounded ready.2 ready.1.1 room
      · intro a observed
        have absent := input_no_index actual (input_safe (List.mem_of_getElem? fetch))
        rw [observed] at absent
        cases absent)
  refine ⟨walked.2.1,?_⟩
  cases indices with
  | nil => rfl
  | cons a rest => exact False.elim (walked.2.2 a (by simp))

end PtxTorchLean.Poisson.PTX.Concurrent.Dot
