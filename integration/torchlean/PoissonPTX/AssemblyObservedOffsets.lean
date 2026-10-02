import PoissonPTX.AssemblyObservedAddress

namespace PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def nodeWord (ctx : Kernel.Context) : Word := (Kernel.Residual.index ctx).setWidth 64
def nextWord (ctx : Kernel.Context) : Word := add32 (nodeWord ctx) 1
def nodeScale (ctx : Kernel.Context) : Word := BitVec.ofNat 64 ((Kernel.Residual.index ctx).toNat*4)
def nextScale (ctx : Kernel.Context) : Word := BitVec.ofNat 64 ((Kernel.u32 (nextWord ctx)).toNat*4)

/-- Address-only facts for the two initial offset loads. These hold before
source admission and do not specify either loaded offset value. -/
def OffsetsReady (ctx : Kernel.Context) (offsets : Word) (s : Flow.State) : Prop :=
  (s.core.pc=7 → s.core.regs 1=nodeScale ctx) ∧
  (s.core.pc=8 → s.core.regs 2=ctx.arena+nodeScale ctx) ∧
  (s.core.pc=9 → s.core.regs 2=address32 ctx.arena (Kernel.Residual.index ctx) offsets) ∧
  (s.core.pc=11 → s.core.regs 13=nextWord ctx) ∧
  (s.core.pc=12 → s.core.regs 1=nextScale ctx) ∧
  (s.core.pc=13 → s.core.regs 2=ctx.arena+nextScale ctx) ∧
  (s.core.pc=14 → s.core.regs 2=address32 ctx.arena (Kernel.u32 (nextWord ctx)) offsets)

theorem offsets_initial (pc : s.core.pc=0) : OffsetsReady ctx offsets s := by simp [OffsetsReady,pc]

theorem offsets_step (step : Flow.Observed.Step ctx
    (entryCode count offsets entries element mask boundary output) s t access indexRecord)
    (launch : Ready ctx mask output s) (ready : OffsetsReady ctx offsets s) : OffsetsReady ctx offsets t := by
  have indexNarrow : (Kernel.Residual.index ctx).toNat%4294967296=(Kernel.Residual.index ctx).toNat :=
    Nat.mod_eq_of_lt (Kernel.Residual.index ctx).isLt
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
  all_goals simp_all [Ready,OffsetsReady,nodeWord,nextWord,nodeScale,nextScale,Flow.simple,Flow.source,Flow.next,Flow.goto,Flow.halt,
    assign,advance,put,Operand.eval,Indexed.mad,Indexed.wide,Kernel.u32,Kernel.Residual.index,address,address32,wide,
    Concurrent.ordinary,Nat.add_assoc,indexNarrow]
  all_goals split_ifs <;> simp_all

end PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress
