import PoissonPTX.CellConsumerSources

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer
open Ptx CellMiddle Symbolic

theorem combined (middle : Runs cfg (Checks.program width) start before ready)
    (rest : Runs cfg (program width) ready after final) :
    Runs cfg (program width) start (before++after) final :=
  runs_append (Extension.run_append_code middle (suffix width)) rest

theorem tail_late (lo : 2≤width) (hi : width≤5)
    (rest : Runs cfg (program width) ready after final)
    (done : ∀ t, (ready.lanes t).pc=(Checks.program width).length)
    (member : Event.data thread access∈after) :
    (Checks.program width).length≤access.data.pc := by
  obtain ⟨before,earlier,selected,out,suffix,hp,hs,hm,ht,he⟩ := run_access_prefix rest member
  obtain ⟨eq,op,next,fetch,hd⟩ := step_access_origin hs hm
  subst selected
  have mono := runs_pc_mono hp (checked_forward (checked width lo hi)) thread
  rw [done] at mono
  rw [access_pc hd]
  exact mono

theorem tail_readonly (lo : 2≤width) (hi : width≤5)
    (rest : Runs cfg (program width) ready after final)
    (done : ∀ t, (ready.lanes t).pc=(Checks.program width).length) : Extension.ReadOnly after := by
  intro thread access member
  have late := tail_late lo hi rest done member
  cases write : access.data.store with
  | false => rfl
  | true =>
    obtain ⟨before,earlier,selected,out,suffix,hp,hs,hm,ht,he⟩ := run_access_prefix rest member
    obtain ⟨eq,op,next,fetch,hd⟩ := step_access_origin hs hm
    subst selected
    have pc := access_pc hd
    obtain ⟨sp,addr,src,rfl,record,valid,result⟩ := store_origin hd write
    obtain ⟨bound,atPC⟩ := List.getElem?_eq_some_iff.mp fetch
    have check := no_tail_stores width lo hi ⟨(before.lanes thread).pc,bound⟩ (by change (Checks.program width).length≤(before.lanes thread).pc; simpa only [pc] using late)
    simp [atPC,Replay.noStore] at check

/-- One source assignment covers the entire concatenated execution. Its
restriction to the middle history is derived; later loads add no new writers. -/
theorem all_reads (launch : Numeric.Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (middle : Runs cfg (Checks.program width) start before ready)
    (done : ∀ t, (ready.lanes t).pc=(Checks.program width).length)
    (rest : Runs cfg (program width) ready after final)
    (compatible : Visibility.Compatible initial (before++after) source)
    (performed : Visibility.Performed (before++after) source) :
    Symbolic.Reads (Numeric.view width bases initial (before++after)) (before++after) := by
  have readonly := tail_readonly lo hi rest done
  have prefixCompatible := Extension.compatible_prefix compatible readonly
  have prefixPerformed := Extension.performed_prefix performed
  intro thread access member read
  rcases List.mem_append.mp member with early|late
  · have value := Numeric.all_reads launch lo hi middle prefixCompatible prefixPerformed thread access early read
    simpa only [Numeric.view,Extension.view_append readonly] using value
  · obtain ⟨index,observed⟩ := List.mem_iff_getElem?.mp (List.mem_append_right before late)
    exact load_view launch lo hi (combined middle rest) observed read (tail_late lo hi rest done late) compatible performed

/-- The final arithmetic result is derived from actual concurrent registers and
loads. No supplied scalar trace or final-register equation is a premise. -/
theorem register_value (launch : Numeric.Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (middle : Runs cfg (Checks.program width) start before ready)
    (done : ∀ t, (ready.lanes t).pc=(Checks.program width).length)
    (rest : Runs cfg (program width) ready after final)
    (compatible : Visibility.Compatible initial (before++after) source)
    (performed : Visibility.Performed (before++after) source)
    (thread : Fin 32) (live : thread.val<width*width)
    (finished : (final.lanes thread).pc=(program width).length) :
    decode ((final.lanes thread).regs 11)=
      (expected width thread.val).eval bases (Numeric.view width bases initial before) := by
  have inv := Symbolic.runs_invariant (combined middle rest) launch.aligned
    (symbolic launch .values (Numeric.view width bases initial (before++after))) (guards width lo hi)
    (fun _ => all_reads launch lo hi middle done rest compatible performed) thread live 11
  rw [finished] at inv
  have result := number_sound inv (results width lo hi ⟨thread.val,live⟩)
  simpa only [Numeric.view,Extension.view_append (tail_readonly lo hi rest done)] using result

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer
