import PoissonPTX.AssemblyObservedAddress

namespace PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def BoundsReady (finish : Nat) (s : Flow.State) : Prop :=
  (10≤s.core.pc → cursor s.core≤finish) ∧
  (15≤s.core.pc → limit s.core=finish) ∧
  (s.core.pc=17 → s.predicates 0=decide (finish≤cursor s.core)) ∧
  (18≤s.core.pc → s.core.pc≤27 → cursor s.core<finish)

theorem bounds_initial (pc : s.core.pc=0) : BoundsReady finish s := by simp [BoundsReady,pc]

/-- The two admitted offset loads determine the loop range. The actual
comparison and branch guard every body iteration, and the unsigned increment
cannot wrap because the admitted endpoint fits in a 32-bit index. -/
theorem bounds_step (step : Flow.Observed.Step ctx
    (entryCode count offsets entries element mask boundary output) s t access indexRecord)
    (ready : BoundsReady finish s) (ordered : begin≤finish) (small : finish<2^32)
    (reads : ∀ a, indexRecord=some a → (a.pc=9 → a.value.toNat=begin) ∧ (a.pc=14 → a.value.toNat=finish)) :
    BoundsReady finish t := by
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
  all_goals simp_all [BoundsReady,cursor,limit,Flow.Compare.apply,Flow.simple,Flow.source,Flow.next,Flow.goto,Flow.halt,
    assign,advance,put,Operand.eval,Indexed.mad,Indexed.wide,Kernel.u32,Kernel.Residual.index,address,wide,
    Concurrent.ordinary,Nat.add_assoc]
  all_goals try split_ifs
  all_goals simp_all [add32]
  all_goals omega

end PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress
