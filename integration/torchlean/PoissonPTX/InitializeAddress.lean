import Mathlib.Tactic.CasesM
import PoissonPTX.InitializeText
import PoissonPTX.ObservedAccessShape
import PoissonPTX.ObservedParallel

namespace PtxTorchLean.Poisson.PTX.Initialize
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- Only launch and address registers are constrained. Candidate input bits
and floating-point results remain unrestricted until source admission. -/
def AddressReady (ctx : Kernel.Context) (boundary input rhs r diagonal z p x : Word) (s : Flow.State) : Prop :=
  (1≤s.core.pc → s.core.regs 0=ctx.arena) ∧
  (2≤s.core.pc → s.core.regs 14=ctx.lane.setWidth 64) ∧
  (3≤s.core.pc → s.core.regs 15=ctx.group.setWidth 64) ∧
  (4≤s.core.pc → s.core.regs 12=(Kernel.Residual.index ctx).setWidth 64) ∧
  ((s.core.pc=11 ∨ s.core.pc=17 ∨ s.core.pc=21 ∨ s.core.pc=25 ∨ s.core.pc=31 ∨ s.core.pc=35 ∨ s.core.pc=39) → s.core.regs 1=wide s.core 12) ∧
  ((s.core.pc=12 ∨ s.core.pc=18 ∨ s.core.pc=22 ∨ s.core.pc=26 ∨ s.core.pc=32 ∨ s.core.pc=36 ∨ s.core.pc=40) → s.core.regs 2=s.core.regs 0+wide s.core 12) ∧
  (s.core.pc=7 → s.core.regs 1=Indexed.wide s.core 12) ∧
  (s.core.pc=8 → s.core.regs 2=s.core.regs 0+Indexed.wide s.core 12) ∧
  (s.core.pc=9 → s.core.regs 2=Assembly.maskAddress s.core boundary) ∧
  (s.core.pc=13 → s.core.regs 2=address s.core 12 input) ∧
  (s.core.pc=19 → s.core.regs 2=address s.core 12 rhs) ∧
  (s.core.pc=23 → s.core.regs 2=address s.core 12 r) ∧
  (s.core.pc=27 → s.core.regs 2=address s.core 12 diagonal) ∧
  (s.core.pc=33 → s.core.regs 2=address s.core 12 z) ∧
  (s.core.pc=37 → s.core.regs 2=address s.core 12 p) ∧
  (s.core.pc=41 → s.core.regs 2=address s.core 12 x)

theorem address_initial (pc : s.core.pc=0) : AddressReady ctx boundary input rhs r diagonal z p x s := by
  simp [AddressReady,pc]

theorem address_step (step : Flow.Observed.Step ctx (entry count boundary input rhs r diagonal z p x) s t access index)
    (ready : AddressReady ctx boundary input rhs r diagonal z p x s) : AddressReady ctx boundary input rhs r diagonal z p x t := by
  obtain ⟨running,op,fetch,actual⟩ := step
  have bound := (List.getElem?_eq_some_iff.mp fetch).1
  rw [entry_length] at bound
  interval_cases pc : s.core.pc
  all_goals simp only [entry,VectorFlowEntry.program,body,prefixCode,Assembly.prologue,StorePair.code,StoreZero.code,DividePair.code,Assembly.maskLoad,loadCode,storeCode,PTX.addressCode,
    List.map_cons,List.map_nil,Function.comp_apply,List.cons_append,List.nil_append,List.getElem?_cons_zero,List.getElem?_cons_succ] at fetch
  all_goals cases fetch
  all_goals cases actual
  all_goals try {rename_i ordinary; exact False.elim (ordinary _ rfl)}
  all_goals try cases_type* Indexed.Candidate.Data Concurrent.Data PTX.Eval
  all_goals simp_all [AddressReady,Flow.simple,Flow.source,Flow.next,Flow.halt,
    assign,advance,put,Operand.eval,Indexed.mad,Indexed.wide,Assembly.maskAddress,address32,Kernel.u32,Kernel.Residual.index,address,wide,
    Concurrent.ordinary,Nat.add_assoc]
  all_goals split_ifs <;> simp_all

end PtxTorchLean.Poisson.PTX.Initialize
