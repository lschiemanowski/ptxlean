import PoissonPTX.AssemblyReadSites
import PoissonPTX.ObservedPublication

namespace PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- The only write is the final output store. Every load occurs before it. -/
def BeforeStore (memory : Memory) (mask : Bool) (s : Flow.State) : Prop :=
  s.core.pc≤(if mask then 38 else 32) → s.core.global=memory

theorem before_store_step (step : Flow.Observed.Step ctx
    (entryCode count offsets entries element mask boundary output) s t access indexRecord)
    (ready : BeforeStore memory mask s) : BeforeStore memory mask t := by
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
  all_goals simp_all [BeforeStore,Flow.simple,Flow.next,Flow.goto,Flow.halt,
    assign,advance,put,Concurrent.ordinary]
  all_goals split_ifs <;> simp_all

end PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress
