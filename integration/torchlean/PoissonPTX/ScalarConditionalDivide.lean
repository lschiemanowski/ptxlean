import PoissonPTX.ScalarArithmetic
import PoissonPTX.ScalarFlagFrames

namespace PtxTorchLean.Poisson.PTX.Scalar.ConditionalDivide
variable {a : Arena}

def code (numerator denominator : Nat) : List Instr :=
  [.base (.data (.data (.mov 6 (.imm 0)))),.predFP 0 true .div 6 (.reg numerator) (.reg denominator)]

def zeroed (s : Flow.State) : Flow.State := {s with core:=assign s.core 6 0}
def finish (s : Flow.State) (value : Word) : Flow.State := {zeroed s with core:=assign (zeroed s).core 6 value}

def Allowed (s : Flow.State) (numerator denominator : Nat) (value : Word) : Prop :=
  (s.predicates 0=true ∧ FP.Result .div (s.core.regs numerator) (s.core.regs denominator) value) ∨
  (s.predicates 0=false ∧ value=0)

theorem result (actual : Sequence ctx (code numerator denominator) s t)
    (hn : numerator≠6) (hd : denominator≠6) :
    ∃ value, Allowed s numerator denominator value ∧ t=finish s value := by
  cases actual with
  | cons running first rest =>
    cases first with
    | simple ordinary => simp [Scalar.ordinary] at ordinary
    | base first =>
      cases first with
      | simple ordinary => exact False.elim (ordinary _ rfl)
      | data first =>
        cases first with
        | data first =>
          cases first
          cases rest with
          | cons alive second last =>
            cases last
            cases second with
            | predFP enabled allowed =>
              refine ⟨_,Or.inl ⟨enabled,?_⟩,rfl⟩
              simpa [Operand.eval,assign,advance,hn,hd] using allowed
            | skipFP disabled =>
              refine ⟨0,Or.inr ⟨by cases h:s.predicates 0 <;> simp_all, rfl⟩,?_⟩
              simp [finish,zeroed,assign,advance,Flow.next,Function.update_idem,Operand.eval]
            | simple ordinary => simp [Scalar.ordinary] at ordinary

theorem trace (running : s.halted=false) (allowed : Allowed s numerator denominator value)
    (hn : numerator≠6) (hd : denominator≠6) : Sequence ctx (code numerator denominator) s (finish s value) := by
  refine .cons running (.base (.data (.data .mov))) ?_
  rcases allowed with ⟨enabled,allowed⟩ | ⟨disabled,rfl⟩
  · exact .cons running (.predFP enabled (by simpa [Operand.eval,assign,advance,hn,hd] using allowed)) .nil
  · have skip : Eval ctx (.predFP 0 true .div 6 (.reg numerator) (.reg denominator)) (zeroed s) (Flow.next (zeroed s)) :=
      .skipFP (by simp [zeroed,disabled])
    have same : Flow.next (zeroed s)=finish s 0 := by simp [finish,zeroed,assign,advance,Flow.next,Function.update_idem]
    rw [same] at skip
    exact .cons running skip .nil

theorem exists_allowed (s : Flow.State) (numerator denominator : Nat) : ∃ value, Allowed s numerator denominator value := by
  cases active:s.predicates 0 with
  | false => exact ⟨0,Or.inr ⟨active,rfl⟩⟩
  | true => exact ⟨encode (decode (s.core.regs numerator)/decode (s.core.regs denominator)),Or.inl ⟨active,by simp [FP.Result,FP.apply]⟩⟩

theorem frame : (finish s value).core.global=s.core.global ∧
    (finish s value).core.globalStart=s.core.globalStart ∧ (finish s value).core.globalBytes=s.core.globalBytes ∧
    (finish s value).core.regs 0=s.core.regs 0 ∧ (finish s value).halted=s.halted ∧
    (finish s value).core.regs 6=value := by simp [finish,zeroed,assign,advance]

theorem ready (h : a.Ready s) : a.Ready (finish s value) := by
  simpa only [Arena.Ready,frame.2.1,frame.2.2.1,frame.2.2.2.1] using h

end PtxTorchLean.Poisson.PTX.Scalar.ConditionalDivide
