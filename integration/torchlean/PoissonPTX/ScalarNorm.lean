import PoissonPTX.ScalarEntry
import PoissonPTX.ScalarFrames

namespace PtxTorchLean.Poisson.PTX.Scalar.Norm

def body (source output : Word) : List Instr := load64Code 4 source++[.sqrt 4 (.reg 4)]++store64Code output (.reg 4)
def entry (source output : Word) : List Instr := program (body source output)
def result (s : Flow.State) (source : Word) : Float := Float.sqrt (decode (read64 s.core.global (s.core.regs 0+source).toNat))
def rooted (s : Flow.State) (source value : Word) : Flow.State :=
  {loaded64 s 4 source with core:=assign (loaded64 s 4 source).core 4 value}
def finish (s : Flow.State) (source output value : Word) : Flow.State := stored64 (rooted s source value) output (.reg 4)

theorem rooted_frame : (rooted s source value).core.global=s.core.global ∧
    (rooted s source value).core.globalStart=s.core.globalStart ∧ (rooted s source value).core.globalBytes=s.core.globalBytes ∧
    (rooted s source value).core.regs 0=s.core.regs 0 ∧ (rooted s source value).halted=s.halted ∧
    (rooted s source value).core.regs 4=value := by
  simp [rooted,loaded64,ScalarLoad.loaded,ScalarLoad.addressed,assign,advance]

theorem body_segment : ∀ i∈body source output, segment i=true := by
  simp [body,load64Code,ops,ScalarLoad.code,store64Code,store64Ops,segment,Flow.segment]

theorem body_trace (running : s.halted=false)
    (sourceValid : Valid64 s.core.globalStart s.core.globalBytes (s.core.regs 0+source).toNat)
    (outputValid : Valid64 s.core.globalStart s.core.globalBytes (s.core.regs 0+output).toNat) :
    Sequence ctx (body source output) s (finish s source output (encode (result s source))) := by
  have first := load64_trace (ctx:=ctx) (dst:=4) running sourceValid
  have sqrt : Sequence ctx [.sqrt 4 (.reg 4)] (loaded64 s 4 source) (rooted s source (encode (result s source))) :=
    .cons running (.sqrt (by simp [Operand.eval,loaded64_reg,result])) .nil
  have last := store64_trace (ctx:=ctx) (s:=rooted s source (encode (result s source))) (value:=.reg 4)
    (rooted_frame.2.2.2.2.1.trans running)
    (by simpa only [rooted_frame.2.1,rooted_frame.2.2.1,rooted_frame.2.2.2.1] using outputValid)
  exact sequence_append (sequence_append first sqrt) last

theorem body_result (actual : Sequence ctx (body source output) s final)
    (running : s.halted=false)
    (outputValid : Valid64 s.core.globalStart s.core.globalBytes (s.core.regs 0+output).toNat) :
    ∃ value, final=finish s source output value ∧ decode value=result s source := by
  have form : body source output=load64Code 4 source++(.sqrt 4 (.reg 4)::store64Code output (.reg 4)) := by simp [body,List.append_assoc]
  rw [form] at actual
  obtain ⟨middle,first,rest⟩ := sequence_split _ _ actual
  have same := load64_state first
  subst middle
  cases rest with
  | cons alive step tail =>
    cases step with
    | simple ordinary => simp [Scalar.ordinary] at ordinary
    | @sqrt value _ _ _ allowed =>
      have valueEq : decode value=result s source := by simpa only [Operand.eval,loaded64_reg,result] using allowed
      have eq := store64_state (s:=rooted s source value) tail
        (by simpa only [rooted_frame.2.1,rooted_frame.2.2.1,rooted_frame.2.2.2.1] using outputValid)
        (rooted_frame.2.2.2.2.1.trans running)
      exact ⟨value,eq,valueEq⟩

theorem finish_global : (finish s source output value).core.global=write64 s.core.global (s.core.regs 0+output).toNat value := by
  simp only [finish,stored64_global,rooted_frame.1,rooted_frame.2.2.2.1,Operand.eval,addressed_reg (by decide : 4≠1) (by decide : 4≠2),rooted_frame.2.2.2.2.2]

theorem entry_correct (run : Runs ctx (entry source output) s final)
    (pc : s.core.pc=0) (running : s.halted=false) (done : final.halted=true)
    (outputValid : Valid64 s.core.globalStart s.core.globalBytes (ctx.arena+output).toNat) :
    decode (read64 final.core.global (ctx.arena+output).toNat)=Float.sqrt (decode (read64 s.core.global (ctx.arena+source).toNat)) ∧
    (∀ byte, byte<(ctx.arena+output).toNat ∨ (ctx.arena+output).toNat+8≤byte → final.core.global byte=s.core.global byte) := by
  obtain ⟨middle,trace,eq⟩ := entry_result run pc running done body_segment
  obtain ⟨value,same,decoded⟩ := body_result trace running
    (by simpa only [setup_frame.2.1,setup_frame.2.2.1,setup_frame.2.2.2.1] using outputValid)
  subst final middle
  simp only [Flow.halt,Flow.next,advance,finish_global,setup_frame.1,setup_frame.2.2.2.1,read64_write64]
  refine ⟨?_,?_⟩
  · simpa only [result,setup_frame.1,setup_frame.2.2.2.1] using decoded
  · intro byte outside; exact write64_outside _ _ _ _ outside

theorem entry_exists (s : Flow.State) (pc : s.core.pc=0) (running : s.halted=false)
    (sourceValid : Valid64 s.core.globalStart s.core.globalBytes (ctx.arena+source).toNat)
    (outputValid : Valid64 s.core.globalStart s.core.globalBytes (ctx.arena+output).toNat) :
    ∃ final, Runs ctx (entry source output) s final ∧ final.halted=true := by
  have trace := body_trace (ctx:=ctx) (s:=setup ctx s) running
    (by simpa only [setup_frame.2.1,setup_frame.2.2.1,setup_frame.2.2.2.1] using sourceValid)
    (by simpa only [setup_frame.2.1,setup_frame.2.2.1,setup_frame.2.2.2.1] using outputValid)
  exact ⟨_,entry_executes trace body_segment pc running,rfl⟩

theorem entry_length : (entry source output).length=13 := by
  simp [entry,program,prologue,body,load64Code,ops,ScalarLoad.code,store64Code,store64Ops]

end PtxTorchLean.Poisson.PTX.Scalar.Norm
