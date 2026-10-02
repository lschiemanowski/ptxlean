import PoissonPTX.ControlFlowBlocks

namespace PtxTorchLean.Poisson.PTX.Flow

def noFP : Instr → Bool | .data op => Indexed.noFP op | _ => true
def linear : Instr → Bool | .branch .. | .jump .. => false | _ => true

inductive Sequence (ctx : Kernel.Context) : List Instr → State → State → Prop where
  | nil : Sequence ctx [] s s
  | cons (running : s.halted=false) (step : Eval ctx i s middle) (rest : Sequence ctx code middle t) :
      Sequence ctx (i::code) s t

def sequence (ctx : Kernel.Context) : List Instr → State → Option State
  | [],s => some s
  | i::code,s => if s.halted then none else eval ctx i s >>= sequence ctx code

theorem sequence_sound (h : sequence ctx code s=some t) : Sequence ctx code s t := by
  induction code generalizing s with
  | nil => cases h; exact .nil
  | cons i code ih =>
    simp only [sequence] at h
    split at h
    · simp at h
    · rename_i running
      change ((eval ctx i s).bind (sequence ctx code))=some t at h
      obtain ⟨middle,first,rest⟩ := Option.bind_eq_some_iff.mp h
      exact .cons (by cases he : s.halted <;> simp_all) (eval_sound first) (ih rest)

theorem eval_complete (step : Eval ctx i s t) (plain : noFP i=true) : eval ctx i s=some t := by
  cases step with
  | data one => simp [eval,Indexed.eval_complete one plain]
  | simple ordinary => cases i <;> simp_all [eval]

theorem eval_unique (a : Eval ctx i s t) (b : Eval ctx i s u) (plain : noFP i=true) : t=u :=
  Option.some.inj ((eval_complete a plain).symm.trans (eval_complete b plain))

theorem linear_pc (step : Eval ctx i s t) (forward : linear i=true) : t.core.pc=s.core.pc+1 := by
  cases step with
  | data one => exact Indexed.eval_pc one
  | simple ordinary =>
    cases i <;> simp_all [linear,simple,next,halt,goto,assign,advance]
    all_goals split <;> rfl

theorem sequence_run (trace : Sequence ctx code s t) (forward : ∀ i∈code, linear i=true)
    (pre post : List Instr) (pc : s.core.pc=pre.length) : Runs ctx (pre++code++post) s t := by
  induction trace generalizing pre with
  | nil => exact .nil
  | @cons i s middle code t running step rest ih =>
    apply Runs.cons (s:=s) (t:=middle) ⟨running,i,by simp [pc],step⟩
    have nextPC : middle.core.pc=(pre++[i]).length := by rw [linear_pc step (forward i (by simp)),pc]; simp
    simpa [List.append_assoc] using ih (fun j member => forward j (by simp [member])) (pre++[i]) nextPC

/-- Deterministic straight-line setup is recovered from the whole fetched run.
The canonical sequence is proved executable first, including memory bounds. -/
theorem consume_sequence (trace : Sequence ctx code s middle)
    (plain : ∀ i∈code, noFP i=true) (forward : ∀ i∈code, linear i=true)
    (run : Counted ctx (pre++code++post) k s t) (pc : s.core.pc=pre.length) (done : t.halted=true) :
    ∃ remaining, k=code.length+remaining ∧ Counted ctx (pre++code++post) remaining middle t := by
  induction trace generalizing pre k with
  | nil => exact ⟨k,by simp,run⟩
  | @cons i s next code middle running step rest ih =>
    obtain ⟨count,actual,number,one,last⟩ := peel run running done (i:=i) (by simp [pc])
    have same := eval_unique one step (plain i (by simp))
    subst actual
    have nextPC : next.core.pc=(pre++[i]).length := by rw [linear_pc step (forward i (by simp)),pc]; simp
    obtain ⟨remaining,length,tail⟩ := ih
      (fun j member => plain j (by simp [member]))
      (fun j member => forward j (by simp [member]))
      (pre:=pre++[i]) (by simpa [List.append_assoc] using last) nextPC
    exact ⟨remaining,by simp only [List.length_cons]; omega,by simpa [List.append_assoc] using tail⟩

theorem sequence_append (first : Sequence ctx left s t) (second : Sequence ctx right t u) :
    Sequence ctx (left++right) s u := by
  induction first with
  | nil => exact second
  | cons running step rest ih => exact .cons running step (ih second)

theorem sequence_data (block : Indexed.Block code s.core t) (running : s.halted=false) :
    Sequence ctx (code.map Instr.data) s {s with core:=t} := by
  induction code generalizing s with
  | nil => cases block; exact .nil
  | cons op code ih =>
    cases block with
    | cons step rest => exact .cons running (.data step) (ih rest running)

end PtxTorchLean.Poisson.PTX.Flow
