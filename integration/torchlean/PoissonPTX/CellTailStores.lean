import PoissonPTX.CellTailFrame

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address
variable {n : Nat} {cfg : Config n} {ctx : Fin n → Kernel.Context}
  {start final s : WithTail.State n} {out : WithTail.Outcome n}
  {events : List (Event n)} {selected owner : Fin n}

/-- Locate an actual access step in the combined execution. -/
theorem access_prefix (run : WithTail.Runs cfg ctx code tail start events final)
    (member : Event.data owner a∈events) :
    ∃ before earlier selected out rest,
      WithTail.Runs cfg ctx code tail start earlier before ∧
      WithTail.Step cfg ctx code tail selected before out ∧
      Event.data owner a∈out.events ∧ WithTail.Runs cfg ctx code tail out.state rest final := by
  induction run with
  | nil => simp at member
  | @cons thread s out rest final step tail ih =>
    rcases List.mem_append.mp member with now|later
    · exact ⟨s,[],thread,out,rest,.nil,step,now,tail⟩
    · obtain ⟨before,earlier,selected,next,suffix,hp,hs,hm,ht⟩ := ih later
      exact ⟨before,out.events++earlier,selected,next,suffix,.cons step hp,hs,hm,ht⟩

theorem tail_address {active : Prop} (ready : Ready cut width output active before.core)
    (past : cut≤before.core.pc)
    (fetch : (CellFinal.tail width output)[before.core.pc-cut]?=some i)
    (observed : WithTail.access i before next=some a) :
    a.data.address=(CellFinal.location before.core width output).toNat ∧
      a.data.value=before.core.regs 11 := by
  have bound := (List.getElem?_eq_some_iff.mp fetch).1
  rw [tail_length] at bound
  interval_cases index : before.core.pc-cut <;>
    simp only [CellFinal.tail,storeCode,addressCode,List.map_cons,List.map_nil,
      List.cons_append,List.nil_append,List.getElem?_cons_zero,List.getElem?_cons_succ] at fetch
  all_goals cases fetch
  all_goals simp only [WithTail.access] at observed
  all_goals cases observed
  have pc : before.core.pc=cut+4 := by omega
  exact ⟨congrArg BitVec.toNat (ready.2.2.2.1 pc),rfl⟩

/-- All global stores come from the fetched tail. The address is calculated by
that thread's actual integer instructions, not supplied as an event premise. -/
theorem step_address (lo : 2≤width) (hi : width≤5)
    (step : WithTail.Step cfg ctx (front width) (CellFinal.tail width output) selected s out)
    (ready : Invariant width output s) (member : Event.data owner a∈out.events)
    (store : a.data.store=true) (global : a.space=.global) :
    a.data.address=(CellFinal.location (s.core.lanes owner) width output).toNat := by
  cases step with
  | front _ h =>
    obtain ⟨eq,op,next,fetch,hd⟩ := step_access_origin h member
    obtain ⟨sp,addr,src,he,ha,valid,hnext⟩ := store_origin hd store
    rw [he] at fetch
    have shape := (checked lo hi _ (List.mem_of_getElem? fetch)).2.2.2
    simp [ha,shape] at global
  | tail _ _ past fetch eval =>
    simp only [List.mem_map,Option.mem_toList] at member
    obtain ⟨a',observed,eq⟩ := member
    cases eq
    exact (tail_address (ready selected) past fetch observed).1

/-- Every observed global store addresses exactly the word determined by its
writer's launch registers, for arbitrary admitted instruction interleavings. -/
theorem store_address (lo : 2≤width) (hi : width≤5)
    (run : WithTail.Runs cfg ctx (front width) (CellFinal.tail width output) start events final)
    (aligned : Aligned start.core) (pcs : ∀ t, (start.core.lanes t).pc=0)
    (member : Event.data owner a∈events) (store : a.data.store=true) (global : a.space=.global) :
    a.data.address=(CellFinal.location (start.core.lanes owner) width output).toNat := by
  obtain ⟨before,earlier,selected,out,rest,prior,step,observed,suffix⟩ := access_prefix run member
  have ready := runs_ready lo hi prior aligned (initial_ready pcs)
  rw [step_address lo hi step ready observed store global,runs_location lo hi prior owner]

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address
