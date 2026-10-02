import PoissonPTX.AssemblyObservedReadAddress
import PoissonPTX.ObservedAccessShape

namespace PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem index_site (step : Flow.Observed.Step ctx
    (entryCode count offsets entries element mask boundary output) s t access (some a)) :
    a.pc=s.core.pc ∧ a.address=(s.core.regs 2).toNat ∧
      (s.core.pc=9 ∨ s.core.pc=14 ∨ s.core.pc=21 ∨ (mask=true ∧ s.core.pc=32)) := by
  obtain ⟨_,op,fetch,execution⟩ := step
  obtain ⟨dst,addr,opEq,pcEq,addressEq⟩ := Flow.Observed.index_shape execution
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

  all_goals rcases fetch with ⟨rfl,rfl⟩
  all_goals simp_all

/-- The only eight-byte input load is the loop's element-value load. -/
theorem word_site (step : Flow.Observed.Step ctx
    (entryCode count offsets entries element mask boundary output) s t (some a) indexRecord)
    (read : a.data.store=false) :
    a.space=.global ∧ s.core.pc=25 ∧ a.data.address=(s.core.regs 2).toNat := by
  obtain ⟨_,op,fetch,execution⟩ := step
  obtain ⟨dst,addr,opEq,pcEq,addressEq⟩ := Flow.Observed.load_shape execution read
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

  all_goals rcases fetch with ⟨spaceEq,dstEq,addrEq⟩
  all_goals subst addr
  all_goals simp_all [Operand.eval]

end PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress
