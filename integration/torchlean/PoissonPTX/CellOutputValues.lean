import PoissonPTX.CellTailOwners

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication
open Ptx
variable {n : Nat} {cfg : Config n} {ctx : Fin n → Kernel.Context}
  {s start final : WithTail.State n} {out : WithTail.Outcome n}
  {events : List (Event n)} {selected owner : Fin n}

/-- Once a lane reaches the tail, subsequent execution cannot change its
arithmetic result, even while other lanes continue through the front. -/
theorem step_after (step : WithTail.Step cfg ctx (front width) (CellFinal.tail width output) selected s out)
    (past : (front width).length≤(s.core.lanes owner).pc) :
    (front width).length≤(out.state.core.lanes owner).pc ∧
      (out.state.core.lanes owner).regs 11=(s.core.lanes owner).regs 11 := by
  cases step with
  | front _ h =>
    obtain ⟨fresh,i,fetch,dispatch⟩ := h
    have before := (List.getElem?_eq_some_iff.mp fetch).1
    have different : owner≠selected := by intro eq; subst owner; omega
    cases dispatch with
    | data => simp [setLane,Function.update,different,past]
    | skip => simp [setLane,Function.update,different,past]
    | sync =>
      simp only [synchronize]
      split
      · exact ⟨past,rfl⟩
      · exact ⟨past,rfl⟩
      · exact ⟨by change _≤(s.core.lanes owner).pc+1; omega,rfl⟩
  | tail _ _ _ fetch eval =>
    by_cases eq : owner=selected
    · subst owner
      have pc := Kernel.eval_pc eval
      have frame := WithTail.eval_keeps eval (tail_keeps _ (List.mem_of_getElem? fetch))
      simp only [WithTail.update,WithTail.lane,setLane,Function.update_self] at pc frame ⊢
      exact ⟨by omega,frame⟩
    · simp [WithTail.update,setLane,Function.update,eq,past]

theorem runs_after (run : WithTail.Runs cfg ctx (front width) (CellFinal.tail width output) start events final)
    (past : (front width).length≤(start.core.lanes owner).pc) :
    (front width).length≤(final.core.lanes owner).pc ∧
      (final.core.lanes owner).regs 11=(start.core.lanes owner).regs 11 := by
  induction run with
  | nil => exact ⟨past,rfl⟩
  | cons step _ ih =>
    have next := step_after step past
    have last := ih next.1
    exact ⟨last.1,last.2.trans next.2⟩

theorem step_value (lo : 2≤width) (hi : width≤5)
    (step : WithTail.Step cfg ctx (front width) (CellFinal.tail width output) selected s out)
    (ready : Address.Invariant width output s)
    (member : Event.data owner a∈out.events) (store : a.data.store=true) (global : a.space=.global) :
    (front width).length≤(s.core.lanes owner).pc ∧ a.data.value=(s.core.lanes owner).regs 11 := by
  cases step with
  | front _ h =>
    obtain ⟨eq,op,next,fetch,hd⟩ := step_access_origin h member
    obtain ⟨sp,addr,src,he,ha,valid,hnext⟩ := store_origin hd store
    rw [he] at fetch
    have shape := (Address.checked lo hi _ (List.mem_of_getElem? fetch)).2.2.2
    simp [ha,shape] at global
  | tail _ _ past fetch eval =>
    simp only [List.mem_map,Option.mem_toList] at member
    obtain ⟨a',observed,eq⟩ := member
    cases eq
    exact ⟨past,(Address.tail_address (ready selected) past fetch observed).2⟩

/-- A recorded output word equals its writer's final arithmetic register.
This is a property of actual events, not a fabricated publication payload. -/
theorem store_value (lo : 2≤width) (hi : width≤5)
    (run : WithTail.Runs cfg ctx (front width) (CellFinal.tail width output) start events final)
    (aligned : Aligned start.core) (pcs : ∀ t, (start.core.lanes t).pc=0)
    (member : Event.data owner a∈events) (store : a.data.store=true) (global : a.space=.global) :
    a.data.value=(final.core.lanes owner).regs 11 := by
  obtain ⟨before,earlier,selected,out,rest,prior,step,observed,suffix⟩ := Address.access_prefix run member
  have ready := Address.runs_ready lo hi prior aligned (Address.initial_ready pcs)
  obtain ⟨past,value⟩ := step_value lo hi step ready observed store global
  exact value.trans (runs_after (.cons step suffix) past).2.symm

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication
