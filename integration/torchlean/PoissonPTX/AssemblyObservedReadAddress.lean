import PoissonPTX.AssemblyObservedAddress

namespace PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def scaled4 (s : State) (r : Nat) : Word := BitVec.ofNat 64 ((Kernel.u32 (s.regs r)).toNat*4)
def scaled8 (s : State) (r : Nat) : Word := BitVec.ofNat 64 ((Kernel.u32 (s.regs r)).toNat*8)

/-- Scratch-address facts for the loop's index/value reads and optional
boundary read. Bounds and source values are proved separately. -/
def ReadAddressReady (ctx : Kernel.Context) (entries element : Word) (mask : Bool) (boundary : Word) (s : Flow.State) : Prop :=
  (s.core.pc=19 → s.core.regs 1=scaled4 s.core 19) ∧
  (s.core.pc=20 → s.core.regs 2=ctx.arena+scaled4 s.core 19) ∧
  (s.core.pc=21 → s.core.regs 2=address32 ctx.arena (Kernel.u32 (s.core.regs 19)) entries) ∧
  (s.core.pc=23 → s.core.regs 1=scaled8 s.core 13) ∧
  (s.core.pc=24 → s.core.regs 2=ctx.arena+scaled8 s.core 13) ∧
  (s.core.pc=25 → s.core.regs 2=address64 ctx.arena (Kernel.u32 (s.core.regs 13)) element) ∧
  (mask=true → s.core.pc=30 → s.core.regs 1=scaled4 s.core 12) ∧
  (mask=true → s.core.pc=31 → s.core.regs 2=ctx.arena+scaled4 s.core 12) ∧
  (mask=true → s.core.pc=32 → s.core.regs 2=address32 ctx.arena (Kernel.Residual.index ctx) boundary)

theorem read_address_initial (pc : s.core.pc=0) : ReadAddressReady ctx entries element mask boundary s := by
  cases mask <;> simp [ReadAddressReady,pc]

theorem read_address_step (step : Flow.Observed.Step ctx
    (entryCode count offsets entries element mask boundary output) s t access indexRecord)
    (launch : Ready ctx mask output s) (ready : ReadAddressReady ctx entries element mask boundary s) :
    ReadAddressReady ctx entries element mask boundary t := by
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
  all_goals simp_all [Ready,ReadAddressReady,scaled4,scaled8,Flow.simple,Flow.source,Flow.next,Flow.goto,Flow.halt,
    assign,advance,put,Operand.eval,Indexed.mad,Indexed.wide,Kernel.u32,Kernel.Residual.index,address,address32,address64,wide,
    Concurrent.ordinary,Nat.add_assoc]
  all_goals split_ifs <;> simp_all

end PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress
