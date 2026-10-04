import PoissonPTX.CellEntryLocal

namespace PtxTorchLean.Poisson.PTX.CellEntry.Before

def code (width : Nat) (cells source : Word) : List Instr :=
  (CellPrologue.program width).map .setup ++ [.skip 20] ++
    (CellGather.code width cells source).map .gather

def finish (ctx : CellPrologue.Context) (width : Nat) (cells source : Word)
    (s : CellPrologue.State) : CellPrologue.State :=
  let ready := CellPrologue.finish ctx width s
  if ready.live then ⟨CellGather.finish (Local.beforeGather ctx width s) width cells source,ready.live⟩
  else ⟨{ready.core with pc:=20},ready.live⟩

theorem length : (code width cells source).length=20 := by
  simp [code,CellPrologue.program,CellGather.code]

theorem program_eq : program width cells source=code width cells source++[.sync] := rfl

theorem no_sync : ∀ i∈code width cells source, i≠.sync := by
  intro i member same
  subst i
  simp [code] at member

theorem finish_pc (pc : s.core.pc=0) :
    (finish ctx width cells source s).core.pc=20 := by
  simp only [finish]
  split <;> simp [CellGather.finish,Local.beforeGather,CellPrologue.finish,advance,pc]

/-- Stop before the barrier. No projected single-lane sync is treated as an
actual collective release. Both active and padding lanes reach instruction 20. -/
theorem exists_trace (ctx : CellPrologue.Context) (s : CellPrologue.State) (pc : s.core.pc=0)
    (positive : 0<width) (fits : width*width<2^32)
    (valid : ctx.lane.toNat<width*width → CellGather.Valid (Local.beforeGather ctx width s) width cells source) :
    Local.Runs ctx (code width cells source) s (finish ctx width cells source s) := by
  let ready := CellPrologue.finish ctx width s
  have readyPC : ready.core.pc=7 := by simp [ready,CellPrologue.finish,pc]
  have first := Local.prologue (CellPrologue.fetched_exists ctx s pc positive fits)
    ([.skip 20]++(CellGather.code width cells source).map .gather)
  apply Local.trans (by simpa [code,List.append_assoc] using first)
  have guard : (code width cells source)[ready.core.pc]?=some (.skip 20) := by
    simp [readyPC,code,CellPrologue.program]
  by_cases live : ready.live=true
  · have active : ctx.lane.toNat<width*width := by simpa [ready,CellPrologue.finish] using live
    let body : CellPrologue.State := ⟨Local.beforeGather ctx width s,ready.live⟩
    have prePC : body.core.pc=8 := by simp [body,Local.beforeGather,advance,CellPrologue.finish,pc]
    apply Local.Runs.cons (t:=body) ⟨.skip 20,guard,?_⟩
    · have gathered := Local.gather (ctx:=ctx) (s:=body) (Indexed.run_sound (CellGather.execution (valid active)))
        (by simp [CellGather.code,Indexed.noFP,PTX.noFP])
        ((CellPrologue.program width).map .setup++[.skip 20]) []
        (by simpa [CellPrologue.program] using prePC)
      simpa [code,finish,ready,live,body] using gathered
    · simp [Local.eval,live,body,Local.beforeGather,ready,advance]
  · have inactive : ready.live=false := Bool.eq_false_iff.mpr live
    apply Local.Runs.cons ⟨.skip 20,guard,rfl⟩
    simpa [finish,ready,inactive] using (Local.Runs.nil (ctx:=ctx) (code:=code width cells source)
      (s:=⟨{ready.core with pc:=20},ready.live⟩))

end PtxTorchLean.Poisson.PTX.CellEntry.Before
