import PtxBinary32.ParallelAddressControl
import PtxBinary32.ParallelMemory

/-! Connect actual emitted store addresses to the proved control projection.
Store values remain the actual values and are not supplied by the projection. -/
namespace Ptx.Scalar.Parallel.AddressControl

private theorem eval_store (h : Agree actual model)
    (evaluated : Scalar.eval candidate i actual=.next next occ)
    (memory : occ.memory=some effect) (store : effect.kind=.store) :
    ∃ address value, occ.instruction.op=.store address value ∧
      effect.address=address.eval model ∧ occ.pc=actual.pc ∧
      (occ.instruction.guard=.pred 0 true → model.preds 0=true) := by
  have origin := Memory.Prior.eval_effect_origin candidate i actual next occ effect evaluated memory
  have kind := origin.2.2.2
  rw [store] at kind
  rcases i with ⟨guard,op⟩
  cases op <;> simp only [Ptx.Scalar.SharedReduction.Machine.Control.memoryKind] at kind
  all_goals first | contradiction | skip
  rename_i address value
  cases enabled : guard.eval actual <;> simp only [Scalar.eval,enabled,↓reduceIte] at evaluated
  · obtain ⟨_,rfl⟩ := Scalar.StepResult.next.inj evaluated
    simp [Scalar.occurrence] at memory
  · split at evaluated
    · contradiction
    · obtain ⟨_,rfl⟩ := Scalar.StepResult.next.inj evaluated
      simp only [Scalar.occurrence,Option.some.injEq] at memory
      subst effect
      refine ⟨address,value,rfl,operand64_eq h address,rfl,?_⟩
      intro guardEq
      have enabled0 : actual.preds 0=true := by
        simpa [Scalar.occurrence,show guard=.pred 0 true from guardEq,Scalar.Guard.eval] using enabled
      exact h.pred ▸ enabled0

private theorem scalar_store {s : State n} {seeds : Fin n → Scalar.State} (inv : Invariant program seeds s) (selected : Fin n) (space : Option Space)
    (i : Scalar.Instr) (owner : Fin n) (seenSpace : Option Space) (occ : Scalar.Occurrence)
    (member : .scalar owner seenSpace occ ∈ (scalarStep candidate selected space i s).events)
    (memory : occ.memory=some effect) (store : effect.kind=.store) :
    ∃ address value, occ.instruction.op=.store address value ∧
      effect.address=address.eval (atPC program (seeds owner) occ.pc) ∧
      (occ.instruction.guard=.pred 0 true → (atPC program (seeds owner) occ.pc).preds 0=true) := by
  have old := inv selected
  have input : Agree {(s.lanes selected).scalar with memory := arena s space}
      (atPC program (seeds selected) (s.lanes selected).scalar.pc) := ⟨old.pc,old.regs,old.addrs,old.pred⟩
  cases ev : Scalar.eval candidate i {(s.lanes selected).scalar with memory := arena s space} with
  | next next emitted =>
    have eq : owner=selected ∧ seenSpace=space ∧ occ=emitted := by
      cases space with
      | none => simpa only [scalarStep,ev,List.mem_singleton,Event.scalar.injEq] using member
      | some space => cases space <;> simpa only [scalarStep,ev,List.mem_singleton,Event.scalar.injEq] using member
    obtain ⟨rfl,rfl,rfl⟩ := eq
    obtain ⟨address,value,op,addr,pc,gate⟩ := eval_store input ev memory store
    exact ⟨address,value,op,by simpa only [pc] using addr,by simpa only [pc] using gate⟩
  | halted next emitted =>
    have eq : owner=selected ∧ seenSpace=space ∧ occ=emitted := by
      simpa only [scalarStep,ev,List.mem_singleton,Event.scalar.injEq] using member
    obtain ⟨rfl,rfl,rfl⟩ := eq
    rw [(Scalar.eval_halted ev).2] at memory
    contradiction
  | fault reason => simp [scalarStep,ev] at member
  | unsupported spelling => simp [scalarStep,ev] at member

private theorem dispatch_store {s : State n} {seeds : Fin n → Scalar.State}
    (step : Dispatch cfg candidate selected i s out) (inv : Invariant program seeds s)
    (member : .scalar owner space occ ∈ out.events) (memory : occ.memory=some effect) (store : effect.kind=.store) :
    ∃ address value, occ.instruction.op=.store address value ∧
      effect.address=address.eval (atPC program (seeds owner) occ.pc) ∧
      (occ.instruction.guard=.pred 0 true → (atPC program (seeds owner) occ.pc).preds 0=true) := by
  cases step with
  | localStep => exact scalar_store inv _ _ _ _ _ _ member memory store
  | memory => exact scalar_store inv _ _ _ _ _ _ member memory store
  | binary32 _ => simp at member
  | exit => simp at member
  | sync =>
    rename_i resource
    cases hd : (Barrier.step (barrierConfig cfg s selected) s.barrier (barrierRequest cfg s selected resource)).disposition <;>
      simp [synchronize,hd] at member

theorem step_store {s : State n} {seeds : Fin n → Scalar.State}
    (step : Step cfg program candidate selected s out) (inv : Invariant program seeds s)
    (member : .scalar owner space occ ∈ out.events) (memory : occ.memory=some effect) (store : effect.kind=.store) :
    ∃ address value, occ.instruction.op=.store address value ∧
      effect.address=address.eval (atPC program (seeds owner) occ.pc) ∧
      (occ.instruction.guard=.pred 0 true → (atPC program (seeds owner) occ.pc).preds 0=true) := by
  have h := step.2
  split at h
  · subst out; simp at member
  · split at h
    · subst out; simp at member
    · split at h
      · subst out; simp at member
      · exact dispatch_store h inv member memory store

/-- The emitted byte address is calculated from the same thread's projected
prefix. No read-source or output-value assumption is used. -/
theorem run_store {s final : State n} {events : List (Event n)} {seeds : Fin n → Scalar.State}
    (run : Runs cfg program s events final) (compatible : ProgramCompatible program)
    (inv : Invariant program seeds s) (aligned : Aligned s)
    (member : .scalar owner space occ ∈ events) (memory : occ.memory=some effect) (store : effect.kind=.store) :
    ∃ address value, occ.instruction.op=.store address value ∧
      effect.address=address.eval (atPC program (seeds owner) occ.pc) ∧
      (occ.instruction.guard=.pred 0 true → (atPC program (seeds owner) occ.pc).preds 0=true) := by
  induction run with
  | nil => simp at member
  | cons step _ ih =>
    rcases List.mem_append.mp member with now | later
    · exact step_store step inv now memory store
    · exact ih (step_invariant step compatible inv aligned) (step_aligned step aligned) later

end Ptx.Scalar.Parallel.AddressControl
