import Mathlib.Tactic.CasesM
import PoissonPTX.AssemblyEntry
import PoissonPTX.ObservedParallel

namespace PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Only integer address registers are constrained. Candidate loaded values
and arithmetic accumulators remain unrestricted. -/
def Ready (ctx : Kernel.Context) (mask : Bool) (output : Word) (s : Flow.State) : Prop :=
  let cut := if mask then 35 else 29
  (1≤s.core.pc → s.core.regs 0=ctx.arena) ∧
  (2≤s.core.pc → s.core.regs 14=ctx.lane.setWidth 64) ∧
  (3≤s.core.pc → s.core.regs 15=ctx.group.setWidth 64) ∧
  (4≤s.core.pc → s.core.regs 12=(Kernel.Residual.index ctx).setWidth 64) ∧
  (s.core.pc=cut+1 → s.core.regs 1=wide s.core 12) ∧
  (s.core.pc=cut+2 → s.core.regs 2=s.core.regs 0+wide s.core 12) ∧
  (s.core.pc=cut+3 → s.core.regs 2=address s.core 12 output)

theorem initial (pc : s.core.pc=0) : Ready ctx mask output s := by
  cases mask <;> simp [Ready,pc]

/-- The native control graph preserves launch-derived output addressing even
when all four/eight-byte load choices are still unconstrained. -/
theorem step_ready (step : Flow.Observed.Step ctx
    (entryCode count offsets entries element mask boundary output) s t access indexRecord)
    (ready : Ready ctx mask output s) : Ready ctx mask output t := by
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
  all_goals simp_all [Ready,Flow.simple,Flow.source,Flow.next,Flow.goto,Flow.halt,
    assign,advance,put,Operand.eval,Indexed.mad,Indexed.wide,Kernel.u32,Kernel.Residual.index,address,wide,
    Concurrent.ordinary,Nat.add_assoc]
  all_goals split_ifs <;> simp_all

end PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress
