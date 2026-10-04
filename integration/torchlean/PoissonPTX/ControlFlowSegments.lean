import PoissonPTX.ControlFlowSequence

namespace PtxTorchLean.Poisson.PTX.Flow

/-- A segment may set predicates but cannot branch or return. Its individual
floating-point instructions retain all permitted result encodings. -/
def segment : Instr → Bool
  | .ret | .predRet .. | .branch .. | .jump .. => false
  | _ => true

theorem segment_linear (h : segment i=true) : linear i=true := by cases i <;> simp_all [segment,linear]

theorem segment_running (step : Eval ctx i s t) (plain : segment i=true) : t.halted=s.halted := by
  cases step with
  | data => rfl
  | simple ordinary =>
    cases i <;> simp_all [segment,simple,next]
    split <;> rfl

/-- Recover a mixed data/predicate segment from a completed fetched execution.
No canonical floating result or supplied intermediate state is used. -/
theorem peel_segment (code pre post : List Instr)
    (plain : ∀ i∈code, segment i=true)
    (run : Counted ctx (pre++code++post) k s t)
    (pc : s.core.pc=pre.length) (running : s.halted=false) (done : t.halted=true) :
    ∃ remaining middle, k=code.length+remaining ∧ Sequence ctx code s middle ∧
      middle.core.pc=pre.length+code.length ∧ middle.halted=false ∧
      Counted ctx (pre++code++post) remaining middle t := by
  induction code generalizing pre k s with
  | nil => exact ⟨k,s,by simp,.nil,by simpa using pc,running,run⟩
  | cons i code ih =>
    obtain ⟨steps,middle,number,one,last⟩ := peel run running done (i:=i) (by simp [pc])
    have plainI := plain i (by simp)
    have midPC : middle.core.pc=(pre++[i]).length := by rw [linear_pc one (segment_linear plainI),pc]; simp
    have midRunning : middle.halted=false := (segment_running one plainI).trans running
    obtain ⟨remaining,final,length,trace,finalPC,finalRunning,rest⟩ := ih (pre++[i])
      (fun j member => plain j (by simp [member])) (by simpa [List.append_assoc] using last) midPC midRunning
    refine ⟨remaining,final,by simp only [List.length_cons]; omega,.cons running one trace,?_,finalRunning,?_⟩
    · simp only [List.length_append,List.length_cons,List.length_nil] at finalPC ⊢; omega
    · simpa [List.append_assoc] using rest

theorem sequence_split (left right : List Instr) (run : Sequence ctx (left++right) s t) :
    ∃ middle, Sequence ctx left s middle ∧ Sequence ctx right middle t := by
  induction left generalizing s with
  | nil => exact ⟨s,.nil,run⟩
  | cons i left ih =>
    cases run with
    | cons running step rest =>
      obtain ⟨middle,first,last⟩ := ih rest
      exact ⟨middle,.cons running step first,last⟩

theorem sequence_pc (run : Sequence ctx code s t) (plain : ∀ i∈code, linear i=true) :
    t.core.pc=s.core.pc+code.length := by
  induction run with
  | nil => simp
  | cons running step rest ih =>
    rw [ih (fun j member => plain j (by simp [member])),linear_pc step (plain _ (by simp))]
    simp [Nat.add_comm,Nat.add_left_comm]

theorem sequence_running (run : Sequence ctx code s t) (plain : ∀ i∈code, segment i=true) :
    t.halted=s.halted := by
  induction run with
  | nil => rfl
  | cons running step rest ih =>
    exact (ih (fun j member => plain j (by simp [member]))).trans (segment_running step (plain _ (by simp)))

theorem sequence_unique (one : Sequence ctx code s t) (two : Sequence ctx code s u)
    (plain : ∀ i∈code, noFP i=true) : t=u := by
  induction one generalizing u with
  | nil => cases two; rfl
  | cons running step rest ih =>
    cases two with
    | cons alive actual tail =>
      have same := eval_unique step actual (plain _ (by simp))
      subst_vars
      exact ih tail (fun i member => plain i (by simp [member]))

/-- Extract the actual indexed block from a data-only segment. -/
theorem sequence_data_block (run : Sequence ctx (code.map Instr.data) s t) :
    Indexed.Block code s.core t.core ∧ t.predicates=s.predicates ∧ t.halted=s.halted := by
  induction code generalizing s with
  | nil => cases run; exact ⟨.nil,rfl,rfl⟩
  | cons i code ih =>
    cases run with
    | cons running step rest =>
      cases step with
      | simple ordinary => exact False.elim (ordinary _ rfl)
      | data actual =>
        obtain ⟨tail,pred,halt⟩ := ih rest
        exact ⟨.cons actual tail,pred,halt⟩

end PtxTorchLean.Poisson.PTX.Flow
