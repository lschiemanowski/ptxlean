import PoissonPTX.InitializeAddress
import PoissonPTX.ObservedParallelReplay

namespace PtxTorchLean.Poisson.PTX.Initialize
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- Every word observation names an actual input or store at its launch-derived
address. Numerical values remain unconstrained until source admission. -/
def AccessAt (ctx : Kernel.Context) (_boundary input rhs r diagonal z p x : Word) (a : Concurrent.Access) : Prop :=
  a.space=.global ∧
  (if a.data.store then
     (a.data.pc=19 ∧ a.data.address=(address64 ctx.arena (Kernel.Residual.index ctx) rhs).toNat) ∨
     (a.data.pc=23 ∧ a.data.address=(address64 ctx.arena (Kernel.Residual.index ctx) r).toNat) ∨
     (a.data.pc=33 ∧ a.data.address=(address64 ctx.arena (Kernel.Residual.index ctx) z).toNat) ∨
     (a.data.pc=37 ∧ a.data.address=(address64 ctx.arena (Kernel.Residual.index ctx) p).toNat) ∨
     (a.data.pc=41 ∧ a.data.address=(address64 ctx.arena (Kernel.Residual.index ctx) x).toNat)
   else (a.data.pc=13 ∧ a.data.address=(address64 ctx.arena (Kernel.Residual.index ctx) input).toNat) ∨
     (a.data.pc=27 ∧ a.data.address=(address64 ctx.arena (Kernel.Residual.index ctx) diagonal).toNat))

theorem access_step (step : Flow.Observed.Step ctx (entry count boundary input rhs r diagonal z p x) s t (some a) index)
    (ready : AddressReady ctx boundary input rhs r diagonal z p x s) : AccessAt ctx boundary input rhs r diagonal z p x a := by
  obtain ⟨running,op,fetch,actual⟩ := step
  have bound := (List.getElem?_eq_some_iff.mp fetch).1
  rw [entry_length] at bound
  interval_cases pc : s.core.pc
  all_goals simp only [entry,VectorFlowEntry.program,body,prefixCode,Assembly.prologue,StorePair.code,StoreZero.code,DividePair.code,Assembly.maskLoad,loadCode,storeCode,PTX.addressCode,
    List.map_cons,List.map_nil,Function.comp_apply,List.cons_append,List.nil_append,List.getElem?_cons_zero,List.getElem?_cons_succ] at fetch
  all_goals cases fetch
  all_goals cases actual
  all_goals try cases_type* Indexed.Candidate.Data Concurrent.Data
  all_goals simp_all [AddressReady,AccessAt,Operand.eval,address,wide,address64,BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Kernel.Residual.index ctx).isLt]

theorem accesses (run : Flow.Observed.Runs ctx (entry count boundary input rhs r diagonal z p x) s words indices t)
    (ready : AddressReady ctx boundary input rhs r diagonal z p x s) (member : a∈words) :
    AccessAt ctx boundary input rhs r diagonal z p x a := by
  induction run with
  | nil => simp at member
  | @cons s middle access index words indices t step rest ih =>
    rcases List.mem_append.mp member with first | later
    · have observed : access=some a := by simpa using first
      exact access_step (observed ▸ step) ready
    · exact ih (address_step step ready) later

/-- The sole four-byte observation is the actual boundary-mask input. -/
theorem index_step (step : Flow.Observed.Step ctx (entry count boundary input rhs r diagonal z p x) s t access (some a))
    (ready : AddressReady ctx boundary input rhs r diagonal z p x s) :
    a.pc=9 ∧ a.address=(address32 ctx.arena (Kernel.Residual.index ctx) boundary).toNat := by
  obtain ⟨_,op,fetch,actual⟩ := step
  obtain ⟨dst,addr,eq,position,location⟩ := Flow.Observed.index_shape actual
  subst op
  have bound := (List.getElem?_eq_some_iff.mp fetch).1
  rw [entry_length] at bound
  interval_cases pc : s.core.pc
  all_goals simp only [entry,VectorFlowEntry.program,body,prefixCode,Assembly.prologue,StorePair.code,StoreZero.code,DividePair.code,Assembly.maskLoad,loadCode,storeCode,PTX.addressCode,
    List.map_cons,List.map_nil,Function.comp_apply,List.cons_append,List.nil_append,
    List.getElem?_cons_zero,List.getElem?_cons_succ] at fetch
  all_goals simp at fetch
  rcases fetch with ⟨rfl,rfl⟩
  simp [AddressReady,pc] at ready
  constructor
  · exact position
  · rw [location]
    simp_all [Assembly.maskAddress,Kernel.u32,BitVec.setWidth_setWidth_of_le _ (by decide : 32≤64)]

theorem index_accesses (run : Flow.Observed.Runs ctx (entry count boundary input rhs r diagonal z p x) s words indices t)
    (ready : AddressReady ctx boundary input rhs r diagonal z p x s) (member : a∈indices) :
    a.pc=9 ∧ a.address=(address32 ctx.arena (Kernel.Residual.index ctx) boundary).toNat := by
  induction run with
  | nil => simp at member
  | @cons s middle access index words indices t step rest ih =>
    rcases List.mem_append.mp member with first | later
    · have observed : index=some a := by simpa using first
      exact index_step (observed ▸ step) ready
    · exact ih (address_step step ready) later

theorem entry_linear : ∀ i∈entry count boundary input rhs r diagonal z p x, Flow.linear i=true := by
  simp [entry,VectorFlowEntry.program,body,prefixCode,Assembly.prologue,StorePair.code,StoreZero.code,DividePair.code,Assembly.maskLoad,loadCode,storeCode,PTX.addressCode,Flow.linear]

end PtxTorchLean.Poisson.PTX.Initialize
