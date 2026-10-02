import PoissonPTX.CellEntryOccurrence

namespace PtxTorchLean.Poisson.PTX.CellEntry.Local

theorem Avoid.trans (first : Avoid ctx code pc s t) (second : Avoid ctx code pc t u) : Avoid ctx code pc s u := by
  induction first with
  | nil => exact second
  | cons step away _ ih => exact .cons step away (ih second)

theorem prologue_avoids (run : CellPrologue.Runs ctx pre fuel s t) (suffix : List Instr)
    (short : pre.length≤forbidden) : Avoid ctx (pre.map .setup++suffix) forbidden s t := by
  induction run with
  | nil => exact .nil
  | cons step rest ih =>
    obtain ⟨i,fetch,he⟩ := step
    have bound := (List.getElem?_eq_some_iff.mp fetch).1
    apply Avoid.cons ⟨.setup i,?_,he⟩ (by omega) ih
    rw [List.getElem?_append_left (by simpa using bound),List.getElem?_map,fetch]
    rfl

theorem padding_avoids (ctx : CellPrologue.Context) (s : CellPrologue.State) (pc : s.core.pc=0)
    (positive : 0<width) (fits : width*width<2^32) (inactive : ¬ctx.lane.toNat<width*width) :
    Avoid ctx (program width cells source) 19 s (finish ctx width cells source s) := by
  let ready := CellPrologue.finish ctx width s
  have live : ready.live=false := by simp [ready,CellPrologue.finish,inactive]
  have readyPC : ready.core.pc=7 := by simp [ready,CellPrologue.finish,pc]
  have first := prologue_avoids (CellPrologue.fetched_exists ctx s pc positive fits)
    ([.skip 20]++(CellGather.code width cells source).map .gather++[.sync])
    (by simp [CellPrologue.program] : (CellPrologue.program width).length≤19)
  apply Avoid.trans (by simpa [program,List.append_assoc] using first)
  apply Avoid.cons ⟨.skip 20,?_,rfl⟩ ?_
  · apply Avoid.cons ⟨.sync,?_,?_⟩ ?_ Avoid.nil
    · simpa [CellPrologue.finish,inactive] using (barrier_fetch (width:=width) (cells:=cells) (source:=source))
    · simp [eval,finish,ready,live,advance]
    · simp [CellPrologue.finish,inactive]
  · simp [program,CellPrologue.program,CellPrologue.finish,pc]
  · simp [CellPrologue.finish,pc]

end PtxTorchLean.Poisson.PTX.CellEntry.Local

namespace PtxTorchLean.Poisson.PTX.CellEntry
variable {n : Nat} {s t : State n} {cfg : Concurrent.Config n}
  {ctx : Fin n → CellPrologue.Context}

/-- A recorded store gives a real local path to its counter. -/
theorem recorded_path (run : Runs cfg ctx (program width cells source) s events indices t)
    (aligned : Concurrent.Aligned s.core) (initial : ∀ u, (s.core.lanes u).global=memory)
    (words : Words memory events) (indexValues : Indices memory indices)
    (member : Concurrent.Event.data owner access∈events) (store : access.data.store=true) :
    ∃ mid, Local.Runs (ctx owner) (program width cells source) (lane s owner) mid ∧ mid.core.pc=19 := by
  induction run with
  | nil => simp at member
  | @cons selected s out rest indices final step tail ih =>
    rcases List.mem_append.mp member with first | later
    · have pc := (store_origin step first store).2.1
      exact ⟨lane s owner,.nil,pc⟩
    · obtain ⟨mid,path,pc⟩ := ih (step_aligned step aligned)
        (fun u => (step_global step u).trans (initial u))
        (fun u a member read global => words u a (List.mem_append_right _ member) read global)
        (fun u a member => indexValues u a (List.mem_append_right _ member)) later
      rcases step_local step aligned initial
        (fun u a member read global => words u a (List.mem_append_left _ member) read global)
        (fun u a member => indexValues u a (List.mem_append_left _ member)) owner with equal | one
      · exact ⟨mid,equal ▸ path,pc⟩
      · exact ⟨mid,.cons one path,pc⟩

theorem store_active (run : Runs cfg ctx (program width cells source) s events indices t)
    (aligned : Concurrent.Aligned s.core) (initial : ∀ u, (s.core.lanes u).global=memory .global)
    (words : Concurrent.Visibility.Compatible memory events chosen)
    (indexSources : IndexSources.Compatible (memory .global) events indices selected)
    (pc : (s.core.lanes owner).pc=0) (positive : 0<width) (fits : width*width<2^32)
    (member : Concurrent.Event.data owner access∈events) (store : access.data.store=true) :
    (ctx owner).lane.toNat<width*width := by
  by_contra inactive
  have wordValues : Words (memory .global) events := by
    intro u a member read global
    obtain ⟨r,observed⟩ := List.mem_iff_getElem?.mp member
    exact word_value run words observed read global
  have indexValues : Indices (memory .global) indices := by
    intro u a member
    obtain ⟨r,observed⟩ := List.mem_iff_getElem?.mp member
    exact index_value run indexSources observed
  obtain ⟨mid,path,atStore⟩ := recorded_path run aligned initial wordValues indexValues member store
  exact Local.cannot_avoid path atStore (by rw [store_fetch]; simp)
    (Local.padding_avoids (ctx owner) (lane s owner) pc positive fits inactive)
    (by simp [Local.finish_pc (s:=lane s owner) pc,program_length])

end PtxTorchLean.Poisson.PTX.CellEntry
