import PoissonPTX.CellOutputValues

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication
open Ptx
variable {n : Nat} {cfg : Config n} {ctx : Fin n → Kernel.Context}
  {s start final : WithTail.State n} {out : WithTail.Outcome n}
  {events : List (Event n)} {selected owner : Fin n}

def Wrote (events : List (Event n)) (owner : Fin n) : Prop :=
  ∃ a, Event.data owner a∈events ∧ a.data.store=true ∧ a.space=.global

theorem front_before_store {actual : Concurrent.State n} {result : Concurrent.Outcome n}
    (lo : 2≤width) (hi : width≤5)
    (step : Concurrent.Step cfg (front width) selected actual result)
    (aligned : Aligned actual) (active : owner.val<width*width)
    (before : (actual.lanes owner).pc<(front width).length+5) :
    (result.state.lanes owner).pc<(front width).length+5 := by
  obtain ⟨fresh,i,fetch,dispatch⟩ := step
  have live := (List.getElem?_eq_some_iff.mp fetch).1
  cases dispatch with
  | data hd =>
    by_cases eq : owner=selected
    · subst owner; simp only [setLane,Function.update_self,data_pc hd]; omega
    · simpa [setLane,Function.update,eq] using before
  | @skip count target =>
    by_cases eq : owner=selected
    · subst owner
      simp only [setLane,Function.update_self]
      split
      · omega
      · rename_i inactive
        have shape := Address.checked lo hi _ (List.mem_of_getElem? fetch)
        rcases shape with bound|⟨countEq,ret⟩
        · omega
        · simp [countEq,active] at inactive
    · simpa [setLane,Function.update,eq] using before
  | @sync resource =>
    simp only [synchronize]
    split
    · exact before
    · exact before
    · rename_i release
      have same := release_aligned cfg actual selected resource aligned release owner
      change (actual.lanes owner).pc+1<(front width).length+5
      rw [same]; omega

/-- An active lane cannot get past its store without recording it. Inactive
return branches and barrier releases cannot create a false completion. -/
theorem step_without_store (lo : 2≤width) (hi : width≤5)
    (step : WithTail.Step cfg ctx (front width) (CellFinal.tail width output) selected s out)
    (aligned : Aligned s.core) (active : owner.val<width*width)
    (before : (s.core.lanes owner).pc<(front width).length+5)
    (absent : ¬Wrote out.events owner) :
    (out.state.core.lanes owner).pc<(front width).length+5 := by
  cases step with
  | front _ h => exact front_before_store lo hi h aligned active before
  | tail _ _ past fetch eval =>
    by_cases eq : owner=selected
    · subst owner
      have pc := Kernel.eval_pc eval
      simp only [WithTail.lane] at pc
      simp only [WithTail.update,setLane,Function.update_self]
      by_cases earlier : (s.core.lanes selected).pc<(front width).length+4
      · omega
      · have pos : (s.core.lanes selected).pc=(front width).length+4 := by omega
        have idx : (s.core.lanes selected).pc-(front width).length=4 := by omega
        rw [idx] at fetch
        simp only [CellFinal.tail,storeCode,addressCode,List.map_cons,List.map_nil,
          List.cons_append,List.nil_append,List.getElem?_cons_succ,List.getElem?_cons_zero] at fetch
        cases fetch
        exfalso
        apply absent
        simp [Wrote,WithTail.access]
    · simpa [WithTail.update,setLane,Function.update,eq] using before

theorem runs_without_store (lo : 2≤width) (hi : width≤5)
    (run : WithTail.Runs cfg ctx (front width) (CellFinal.tail width output) start events final)
    (aligned : Aligned start.core) (active : owner.val<width*width)
    (before : (start.core.lanes owner).pc<(front width).length+5)
    (absent : ¬Wrote events owner) :
    (final.core.lanes owner).pc<(front width).length+5 := by
  induction run with
  | nil => exact before
  | @cons thread s out restEvents final step rest ih =>
    have first : ¬Wrote out.events owner := by
      rintro ⟨a,member,store,global⟩
      exact absent ⟨a,List.mem_append_left _ member,store,global⟩
    have remaining : ¬Wrote restEvents owner := by
      rintro ⟨a,member,store,global⟩
      exact absent ⟨a,List.mem_append_right _ member,store,global⟩
    exact ih (WithTail.step_aligned step aligned)
      (step_without_store lo hi step aligned active before first) remaining

/-- Store existence is derived from the completed run, not supplied as a
publication-completeness premise. Other lanes need not have completed. -/
theorem completed_wrote (lo : 2≤width) (hi : width≤5)
    (run : WithTail.Runs cfg ctx (front width) (CellFinal.tail width output) start events final)
    (aligned : Aligned start.core) (pcs : ∀ t, (start.core.lanes t).pc=0)
    (active : owner.val<width*width)
    (finished : (front width).length+5≤(final.core.lanes owner).pc) : Wrote events owner := by
  classical
  by_contra absent
  have before : (start.core.lanes owner).pc<(front width).length+5 := by rw [pcs]; omega
  have low := runs_without_store lo hi run aligned active before absent
  omega

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication
