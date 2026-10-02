import PoissonPTX.ControlFlowObserved

namespace PtxTorchLean.Poisson.PTX.Flow.Observed

/-- Four-byte observations come only from the actual unsigned global load;
the record retains its fetched counter and register-computed byte address. -/
theorem index_shape (execution : Eval ctx op s t access (some a)) :
    ∃ dst addr, op=.data (.load32 dst addr) ∧ a.pc=s.core.pc ∧ a.address=(s.core.regs addr).toNat := by
  cases execution with
  | data one => cases one with
    | load32 => exact ⟨_,_,rfl,rfl,rfl⟩

theorem load_shape (execution : Eval ctx op s t (some a) index) (read : a.data.store=false) :
    ∃ dst addr, op=.data (.data (.load64 a.space dst addr)) ∧ a.data.pc=s.core.pc ∧
      a.data.address=(addr.eval s.core).toNat := by
  cases execution with
  | data one => cases one with
    | data one => cases one with
      | load => exact ⟨_,_,rfl,rfl,rfl⟩
      | store => simp at read

end PtxTorchLean.Poisson.PTX.Flow.Observed
