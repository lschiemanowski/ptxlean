import PoissonPTX.AssemblyObservedAddress

namespace PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def IndexReady (count : Nat) (s : Flow.State) : Prop :=
  22≤s.core.pc → s.core.pc≤25 → (Kernel.u32 (s.core.regs 13)).toNat<count

theorem index_initial (pc : s.core.pc=0) : IndexReady elements s := by simp [IndexReady,pc]

/-- The admitted contribution-index read bounds the following element load.
No property of its floating-point value is needed for address safety. -/
theorem index_step (step : Flow.Observed.Step ctx
    (entryCode count offsets entries element mask boundary output) s t access indexRecord)
    (ready : IndexReady elements s)
    (reads : ∀ a, indexRecord=some a → a.pc=21 → a.value.toNat<elements) : IndexReady elements t := by
  obtain ⟨running,op,fetch,execution⟩ := step
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
  all_goals cases fetch
  all_goals cases execution
  all_goals try {rename_i ordinary; exact False.elim (ordinary _ rfl)}
  all_goals try cases_type* Indexed.Candidate.Data Concurrent.Data PTX.Eval
  all_goals simp_all [IndexReady,Flow.simple,Flow.source,Flow.next,Flow.goto,Flow.halt,
    assign,advance,put,Operand.eval,Indexed.mad,Indexed.wide,Kernel.u32,Kernel.Residual.index,address,wide,
    Concurrent.ordinary,Nat.add_assoc]
  all_goals split_ifs <;> simp_all

end PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress
