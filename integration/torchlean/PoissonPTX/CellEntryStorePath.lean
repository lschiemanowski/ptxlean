import PoissonPTX.CellEntryLocal

namespace PtxTorchLean.Poisson.PTX.Indexed

theorem block_split (pre rest : List Instr) (run : Block (pre++rest) s t) :
    ∃ mid, Block pre s mid ∧ Block rest mid t := by
  induction pre generalizing s with
  | nil => exact ⟨s,.nil,run⟩
  | cons i pre ih =>
    cases run with
    | cons step rest =>
      obtain ⟨mid,first,last⟩ := ih rest
      exact ⟨mid,.cons step first,last⟩

end PtxTorchLean.Poisson.PTX.Indexed

namespace PtxTorchLean.Poisson.PTX.CellEntry.Local

/-- A local trace which never executes an instruction at the forbidden counter. -/
inductive Avoid (ctx : CellPrologue.Context) (code : List Instr) (forbidden : Nat) :
    CellPrologue.State → CellPrologue.State → Prop
  | nil : Avoid ctx code forbidden s s
  | cons : Step ctx code s t → s.core.pc≠forbidden → Avoid ctx code forbidden t u → Avoid ctx code forbidden s u

/-- Determinism prevents a terminating trace from bypassing a reachable
instruction. No progress or scheduling fairness assumption is used. -/
theorem cannot_avoid (firstTrace : Runs ctx code s mid) (atForbidden : mid.core.pc=forbidden)
    (present : code[forbidden]?≠none) (actual : Avoid ctx code forbidden s final)
    (terminal : code[final.core.pc]?=none) : False := by
  induction firstTrace with
  | nil => cases actual with
    | nil => rw [atForbidden] at terminal; exact present terminal
    | cons _ away _ => exact away atForbidden
  | cons step rest ih => cases actual with
    | nil => obtain ⟨i,fetch,_⟩ := step; rw [terminal] at fetch; cases fetch
    | cons step' away tail =>
      have same := deterministic step step'
      subst_vars
      exact ih rfl tail

/-- The already-proved local gather has a prefix ending immediately before
its actual store at instruction 19. -/
theorem reaches_store (ctx : CellPrologue.Context) (s : CellPrologue.State) (pc : s.core.pc=0)
    (positive : 0<width) (fits : width*width<2^32) (active : ctx.lane.toNat<width*width)
    (valid : CellGather.Valid (beforeGather ctx width s) width cells source) :
    ∃ mid, Runs ctx (program width cells source) s mid ∧ mid.core.pc=19 := by
  let ready := CellPrologue.finish ctx width s
  let body : CellPrologue.State := ⟨beforeGather ctx width s,ready.live⟩
  have live : ready.live=true := by simp [ready,CellPrologue.finish,active]
  have readyPC : ready.core.pc=7 := by simp [ready,CellPrologue.finish,pc]
  have bodyPC : body.core.pc=8 := by simp [body,beforeGather,advance,CellPrologue.finish,pc]
  let ops := CellGather.code width cells source
  have whole := Indexed.run_sound (CellGather.execution valid)
  obtain ⟨mid,first,last⟩ := Indexed.block_split (ops.take 11) (ops.drop 11)
    (by simpa [List.take_append_drop,ops] using whole)
  have midPC : mid.pc=19 := by
    have h := Indexed.block_pc first
    change mid.pc=body.core.pc+(ops.take 11).length at h
    simp [ops,CellGather.code,bodyPC] at h
    exact h
  refine ⟨⟨mid,ready.live⟩,?_,midPC⟩
  have setup := prologue (CellPrologue.fetched_exists ctx s pc positive fits)
    ([.skip 20]++ops.map .gather++[.sync])
  apply trans (by simpa [program,ops,List.append_assoc] using setup)
  apply Runs.cons (t:=body) ⟨.skip 20,?_,?_⟩
  · have gathered := gather (ctx:=ctx) (s:=body) first
      (by intro i member; have all : ∀ i∈ops, Indexed.noFP i=true := by simp [ops,CellGather.code,Indexed.noFP,PTX.noFP]
          exact all i (List.mem_of_mem_take member))
      ((CellPrologue.program width).map .setup++[.skip 20])
      ((ops.drop 11).map .gather++[.sync])
      (by simpa [CellPrologue.program] using bodyPC)
    convert gathered using 1
    simp [program,ops,CellGather.code,List.append_assoc]
  · simp [program,CellPrologue.program,CellPrologue.finish,pc]
  · simp [eval,live,body,beforeGather,ready,advance]

end PtxTorchLean.Poisson.PTX.CellEntry.Local
