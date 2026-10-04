import PoissonPTX.AffineUpdateAddress
import PoissonPTX.ObservedParallelReplay

namespace PtxTorchLean.Poisson.PTX.AffineUpdate
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Actual reads are the coefficient, old direction and shifted vector; the
only write is the final direction value. Addresses come from launch registers. -/
def AccessAt (ctx : Kernel.Context) (coefficient input shift output : Word) (a : Concurrent.Access) : Prop :=
  a.space=.global ∧
  (if a.data.store then a.data.pc=23 ∧ a.data.address=(address64 ctx.arena (Kernel.Residual.index ctx) output).toNat
   else (a.data.pc=9 ∧ a.data.address=(ctx.arena+coefficient).toNat) ∨
     (a.data.pc=13 ∧ a.data.address=(address64 ctx.arena (Kernel.Residual.index ctx) input).toNat) ∨
     (a.data.pc=17 ∧ a.data.address=(address64 ctx.arena (Kernel.Residual.index ctx) shift).toNat))

theorem access_step (step : Flow.Observed.Step ctx (entry count coefficient input shift output) s t (some a) index)
    (ready : AddressReady ctx coefficient input shift output s) : AccessAt ctx coefficient input shift output a := by
  obtain ⟨running,op,fetch,actual⟩ := step
  have bound := (List.getElem?_eq_some_iff.mp fetch).1
  rw [entry_length] at bound
  interval_cases pc : s.core.pc
  all_goals simp only [entry,VectorEntry.program,Assembly.prologue,code,ScalarLoad.code,loadCode,storeCode,PTX.addressCode,
    List.map_cons,List.map_nil,List.cons_append,List.nil_append,List.getElem?_cons_zero,List.getElem?_cons_succ] at fetch
  all_goals cases fetch
  all_goals cases actual
  all_goals try cases_type* Indexed.Candidate.Data Concurrent.Data
  all_goals simp_all [AddressReady,AccessAt,Operand.eval,address,wide,address64,BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Kernel.Residual.index ctx).isLt]

theorem accesses (run : Flow.Observed.Runs ctx (entry count coefficient input shift output) s words indices t)
    (ready : AddressReady ctx coefficient input shift output s) (member : a∈words) :
    AccessAt ctx coefficient input shift output a := by
  induction run with
  | nil => simp at member
  | @cons s middle access index words indices t step rest ih =>
    rcases List.mem_append.mp member with first | later
    · have observed : access=some a := by simpa using first
      exact access_step (observed ▸ step) ready
    · exact ih (address_step step ready) later

theorem no_index_step (step : Flow.Observed.Step ctx (entry count coefficient input shift output) s t access index) :
    index=none := by
  cases index with
  | none => rfl
  | some a =>
    obtain ⟨_,op,fetch,actual⟩ := step
    obtain ⟨dst,addr,eq,_,_⟩ := Flow.Observed.index_shape actual
    subst op
    have member := List.mem_of_getElem? fetch
    simp [entry,VectorEntry.program,Assembly.prologue,code,ScalarLoad.code,loadCode,storeCode,PTX.addressCode] at member

theorem no_indices (run : Flow.Observed.Runs ctx (entry count coefficient input shift output) s words indices t) : indices=[] := by
  induction run with
  | nil => rfl
  | cons step rest ih => simp [no_index_step step,ih]

theorem entry_linear : ∀ i∈entry count coefficient input shift output, Flow.linear i=true := by
  simp [entry,VectorEntry.program,Assembly.prologue,code,ScalarLoad.code,loadCode,storeCode,PTX.addressCode,Flow.linear]

end PtxTorchLean.Poisson.PTX.AffineUpdate
