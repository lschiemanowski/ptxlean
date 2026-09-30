import PoissonPTX.TailFrontProjection

namespace PtxTorchLean.Poisson.PTX.Concurrent.WithTail

/-- A fetched tail instruction advances beyond the cutoff and preserves the
arithmetic result. Its memory and scratch effects need not match the shadow. -/
theorem tail_related (related : Related cut tracked s.core shadow)
    (past : cut≤(s.core.lanes selected).pc)
    (eval : Kernel.Eval ctx i (lane s selected) next) (frame : keeps tracked i) :
    Related cut tracked (update s selected next).core shadow := by
  refine ⟨related.1,related.2.1,?_⟩
  intro t
  by_cases eq : t=selected
  · subst t
    have old := related.2.2 selected
    simp only [show ¬(s.core.lanes selected).pc<cut by omega,ite_false] at old
    have pc := Kernel.eval_pc eval
    have regs := eval_keeps eval frame
    have after : ¬next.core.pc<cut := by change next.core.pc=(s.core.lanes selected).pc+1 at pc; omega
    simpa only [update,setLane,Function.update_self,after,ite_false] using
      And.intro old.1 (regs.trans old.2)
  · simpa [update,setLane,Function.update,eq] using related.2.2 t

/-- Extract the arithmetic execution and its ordered event occurrences from a
single concurrent execution. Output steps may occur while other lanes are
still in the front; they stutter in the extracted execution. -/
theorem project_filtered {n : Nat} {cfg : Config n} {P : Event n → Prop}
    {ctx : Fin n → Kernel.Context} {front : List Instr} {tail : List Kernel.Instr}
    {start final : State n} {events : List (Event n)} {shadowStart : Concurrent.State n} {tracked : Nat}
    (run : Runs cfg ctx front tail start events final)
    (tailEvents : ∀ i∈tail, ∀ (thread : Fin n) (s t : Kernel.State) (a : Access),
      access i s t=some a → P (Event.data thread a))
    (aligned : Aligned start.core)
    (frame : ∀ i∈tail, keeps tracked i)
    (related : Related front.length tracked start.core shadowStart) :
    ∃ projectedEvents shadowFinal,
      Concurrent.Runs cfg (front.map (clip front.length)) shadowStart projectedEvents shadowFinal ∧
      ∃ embedding : Projection.Embedding projectedEvents events,
        Projection.Omitted P embedding ∧ Related front.length tracked final.core shadowFinal := by
  induction run generalizing shadowStart with
  | nil => exact ⟨[],shadowStart,.nil,Projection.empty [],by intro w e fetch; simp at fetch,related⟩
  | @cons thread s out rest final step run ih =>
    have aligned' := step_aligned step aligned
    cases step with
    | front running actual =>
      obtain ⟨projected,step',related',eventsEq⟩ := front_step actual related aligned
      obtain ⟨small,last,run',embedding,omitted,lastRelated⟩ := ih aligned' related'
      refine ⟨projected.events++small,last,.cons step' run',?_⟩
      rw [eventsEq]
      exact ⟨Projection.keep embedding projected.events,Projection.omitted_keep omitted,lastRelated⟩
    | tail running fresh past fetch eval =>
      have related' := tail_related related past eval (frame _ (List.mem_of_getElem? fetch))
      obtain ⟨small,last,run',embedding,omitted,lastRelated⟩ := ih aligned' related'
      refine ⟨small,last,run',Projection.drop embedding _,Projection.omitted_drop omitted ?_,lastRelated⟩
      intro e member
      simp only [List.mem_map,Option.mem_toList] at member
      obtain ⟨a,ha,rfl⟩ := member
      exact tailEvents _ (List.mem_of_getElem? fetch) _ _ _ a ha


theorem project (run : Runs cfg ctx front tail start events final)
    (aligned : Aligned start.core)
    (frame : ∀ i∈tail, keeps tracked i)
    (related : Related front.length tracked start.core shadowStart) :
    ∃ projectedEvents shadowFinal,
      Concurrent.Runs cfg (front.map (clip front.length)) shadowStart projectedEvents shadowFinal ∧
      Nonempty (Projection.Embedding projectedEvents events) ∧
      Related front.length tracked final.core shadowFinal := by
  obtain ⟨small,shadow,run',embedding,_,rel⟩ :=
    project_filtered (P:=fun _ => True) run (by intros; trivial) aligned frame related
  exact ⟨small,shadow,run',⟨embedding⟩,rel⟩

end PtxTorchLean.Poisson.PTX.Concurrent.WithTail
