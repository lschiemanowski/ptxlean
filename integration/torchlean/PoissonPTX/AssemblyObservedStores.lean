import PoissonPTX.AssemblyObservedAddress

namespace PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Store ownership follows from the actual fetched instruction and the
address-register invariant. It does not depend on candidate read choices. -/
theorem store_address (step : Flow.Observed.Step ctx
    (entryCode count offsets entries element mask boundary output) s t (some a) indexRecord)
    (ready : Ready ctx mask output s) (store : a.data.store=true) :
    a.space=.global ∧ a.data.address=(address64 ctx.arena (Kernel.Residual.index ctx) output).toNat := by
  obtain ⟨_,op,fetch,execution⟩ := step
  obtain ⟨sp,addr,src,opEq,accessEq⟩ := Flow.Observed.store_shape execution store
  subst op
  have bound := (List.getElem?_eq_some_iff.mp fetch).1
  cases mask <;>
    simp only [entryCode,Flow.Window.program,entryPrefix,prologue,prepareCode,Flow.Window.header,
      body,lookupCode,tailCode,maskCode,maskLoad,outputCode,storeCode,addressCode,
      List.length_append,List.length_map,List.length_cons,List.length_nil,ite_true,ite_false,Bool.false_eq_true] at bound
  all_goals interval_cases pc : s.core.pc
  all_goals simp only [entryCode,Flow.Window.program,entryPrefix,prologue,prepareCode,Flow.Window.header,
    body,lookupCode,tailCode,maskCode,maskLoad,outputCode,storeCode,addressCode,pc,
    List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    List.getElem?_cons_zero,List.getElem?_cons_succ,ite_true,ite_false,Bool.false_eq_true] at fetch
  all_goals simp at fetch
  all_goals rcases fetch with ⟨rfl,rfl,rfl⟩
  all_goals simp [Ready,pc] at ready
  all_goals rw [accessEq]
  all_goals constructor
  all_goals try rfl
  all_goals simp [Operand.eval,ready,address,wide,address64,BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Kernel.Residual.index ctx).isLt]

/-- Every write in the complete trace belongs to this launch-derived node. -/
theorem stores (run : Flow.Observed.Runs ctx
    (entryCode count offsets entries element mask boundary output) s words indices t)
    (ready : Ready ctx mask output s) (a : Concurrent.Access) (member : a∈words) (store : a.data.store=true) :
    a.space=.global ∧ a.data.address=(address64 ctx.arena (Kernel.Residual.index ctx) output).toNat := by
  induction run with
  | nil => simp at member
  | @cons s middle access indexRecord words indices t step rest ih =>
    rcases List.mem_append.mp member with first | later
    · have observed : access=some a := by simpa using first
      exact store_address (observed ▸ step) ready store
    · exact ih (step_ready step ready) later

end PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress
