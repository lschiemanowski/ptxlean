import PoissonPTX.ControlFlowObserved
import PoissonPTX.Kernel

namespace PtxTorchLean.Poisson.PTX.Kernel.ToFlow

/-- The existing one-predicate kernel language in the indexed Flow language.
Predicate zero carries the original predicate; all memory opcodes are retained. -/
def instruction : Kernel.Instr → Flow.Instr
  | .parameter dst => .context dst .arena
  | .lane dst => .context dst .lane
  | .group dst => .context dst .group
  | .mad32 dst a scale b => .data (.mad32 dst a scale b)
  | .ge32 src limit => .compare 0 .ge (.reg src) (.imm (limit.setWidth 64))
  | .predRet => .predRet 0 true
  | .data op => .data (.data op)
  | .ret => .ret

def state (s : Kernel.State) : Flow.State :=
  ⟨s.core,fun r => if r=0 then s.predicate else false,s.halted⟩

def project (s : Flow.State) : Kernel.State := ⟨s.core,s.predicates 0,s.halted⟩

theorem project_state (s : Kernel.State) : project (state s)=s := by
  cases s; simp [project,state]

/-- The translation changes representation only; it is not an additional
PTX primitive rule. -/
theorem eval_project (actual : Flow.Eval ctx (instruction i) s t) :
    Kernel.Eval ctx i (project s) (project t) := by
  cases i with
  | data op =>
    cases actual with
    | data actual => cases actual with | data actual => exact .data actual
    | simple ordinary => exact False.elim (ordinary (.data op) rfl)
  | mad32 dst a scale b =>
    cases actual with
    | data actual =>
      cases actual
      exact .simple (by intro op same; cases same)
    | simple ordinary => exact False.elim (ordinary (.mad32 dst a scale b) rfl)
  | parameter dst =>
    cases actual with
    | simple ordinary => exact .simple (by intro op same; cases same)
  | lane dst =>
    cases actual with
    | simple ordinary => exact .simple (by intro op same; cases same)
  | group dst =>
    cases actual with
    | simple ordinary => exact .simple (by intro op same; cases same)
  | ret =>
    cases actual with
    | simple ordinary => exact .simple (by intro op same; cases same)
  | predRet =>
    cases actual with
    | simple ordinary =>
      cases predicate : s.predicates 0 <;>
        simpa [instruction,project,Flow.simple,Kernel.simple,predicate,Flow.halt,Flow.next,Kernel.halt,Kernel.advance] using
          (Kernel.Eval.simple (ctx:=ctx) (s:=project s) (instruction:=.predRet) (by intro op same; cases same))
  | ge32 src limit =>
    cases actual with
    | simple ordinary =>
      simpa [instruction,project,Flow.simple,Flow.next,Flow.Compare.apply,Operand.eval,Kernel.u32,
        Kernel.simple,Kernel.advance] using
          (Kernel.Eval.simple (ctx:=ctx) (s:=project s) (instruction:=.ge32 src limit) (by intro op same; cases same))

end PtxTorchLean.Poisson.PTX.Kernel.ToFlow
