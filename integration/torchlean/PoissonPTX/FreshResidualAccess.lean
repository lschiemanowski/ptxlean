import PoissonPTX.FreshResidualAddress
import PoissonPTX.ObservedParallelReplay

namespace PtxTorchLean.Poisson.PTX.FreshResidual
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Both input loads and the sole output store are derived from the fetched
instructions and launch registers. -/
def AccessAt (ctx : Kernel.Context) (rhs ap output : Word) (a : Concurrent.Access) : Prop :=
  a.space=.global ∧
  (if a.data.store then a.data.pc=18 ∧ a.data.address=(address64 ctx.arena (Kernel.Residual.index ctx) output).toNat
   else (a.data.pc=9 ∧ a.data.address=(address64 ctx.arena (Kernel.Residual.index ctx) rhs).toNat) ∨
     (a.data.pc=13 ∧ a.data.address=(address64 ctx.arena (Kernel.Residual.index ctx) ap).toNat))

theorem access_step (step : Flow.Observed.Step ctx (entry count rhs ap output) s t (some a) index)
    (ready : AddressReady ctx rhs ap output s) : AccessAt ctx rhs ap output a := by
  obtain ⟨running,op,fetch,actual⟩ := step
  have bound := (List.getElem?_eq_some_iff.mp fetch).1
  rw [entry_length] at bound
  interval_cases pc : s.core.pc
  all_goals simp only [entry,Kernel.Residual.program,Kernel.Residual.prologue,Kernel.ToFlow.instruction,Residual.code,loadCode,storeCode,PTX.addressCode,
    List.map_cons,List.map_nil,List.cons_append,List.nil_append,List.getElem?_cons_zero,List.getElem?_cons_succ] at fetch
  all_goals cases fetch
  all_goals cases actual
  all_goals try cases_type* Indexed.Candidate.Data Concurrent.Data
  all_goals simp_all [AddressReady,AccessAt,Operand.eval,address,wide,address64,BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Kernel.Residual.index ctx).isLt]

theorem accesses (run : Flow.Observed.Runs ctx (entry count rhs ap output) s words indices t)
    (ready : AddressReady ctx rhs ap output s) (member : a∈words) :
    AccessAt ctx rhs ap output a := by
  induction run with
  | nil => simp at member
  | @cons s middle access index words indices t step rest ih =>
    rcases List.mem_append.mp member with first | later
    · have observed : access=some a := by simpa using first
      exact access_step (observed ▸ step) ready
    · exact ih (address_step step ready) later

theorem no_index_step (step : Flow.Observed.Step ctx (entry count rhs ap output) s t access index) :
    index=none := by
  cases index with
  | none => rfl
  | some a =>
    obtain ⟨_,op,fetch,actual⟩ := step
    obtain ⟨dst,addr,eq,_,_⟩ := Flow.Observed.index_shape actual
    subst op
    have member := List.mem_of_getElem? fetch
    simp [entry,Kernel.Residual.program,Kernel.Residual.prologue,Kernel.ToFlow.instruction,Residual.code,loadCode,storeCode,PTX.addressCode] at member

theorem no_indices (run : Flow.Observed.Runs ctx (entry count rhs ap output) s words indices t) : indices=[] := by
  induction run with
  | nil => rfl
  | cons step rest ih => simp [no_index_step step,ih]

theorem entry_linear : ∀ i∈entry count rhs ap output, Flow.linear i=true := by
  simp [entry,Kernel.Residual.program,Kernel.Residual.prologue,Kernel.ToFlow.instruction,Residual.code,loadCode,storeCode,PTX.addressCode,Flow.linear]

end PtxTorchLean.Poisson.PTX.FreshResidual
