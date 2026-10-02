import PoissonPTX.CellEntryActive

namespace PtxTorchLean.Poisson.PTX.CellEntry.Control

/-- The exact low-32-bit index calculation before any connectivity load. -/
def indexWord (ctx : CellPrologue.Context) (width : Nat) : BitVec 32 :=
  ctx.cell*BitVec.ofNat 32 (width*width)+ctx.lane

def indexScale (ctx : CellPrologue.Context) (width : Nat) : Word :=
  BitVec.ofNat 64 ((indexWord ctx width).toNat*4)

/-- Scratch-register meanings only while they hold the connectivity address.
Later source and shared addresses deliberately reuse these registers. -/
def IndexReady (ctx : CellPrologue.Context) (width : Nat) (cells : Word)
    (s : CellPrologue.State) : Prop :=
  (9≤s.core.pc → s.core.pc≤12 → s.core.regs 13=(indexWord ctx width).setWidth 64) ∧
  (10≤s.core.pc → s.core.pc≤11 → s.core.regs 1=indexScale ctx width) ∧
  (s.core.pc=11 → s.core.regs 2=ctx.arena+indexScale ctx width) ∧
  (s.core.pc=12 → s.core.regs 2=ctx.arena+indexScale ctx width+cells)

theorem index_initial (pc : s.core.pc=0) : IndexReady ctx width cells s := by
  simp [IndexReady,pc]

theorem index_outside (low : s.core.pc≤8 ∨ 13≤s.core.pc) : IndexReady ctx width cells s := by
  rcases low with low|high <;> simp only [IndexReady] <;> omega

theorem gather_index (control : Ready ctx width s) (ready : IndexReady ctx width cells s)
    (fetch : (program width cells source)[s.core.pc]?=some (.gather op))
    (step : Indexed.Candidate.Data op s.core next access ix) :
    IndexReady ctx width cells ⟨next,s.live⟩ := by
  have bound := (List.getElem?_eq_some_iff.mp fetch).1
  rw [program_length] at bound
  have past := gather_past fetch
  have nextPC := Indexed.Candidate.data_pc step
  by_cases late : 12≤s.core.pc
  · apply index_outside; right; change 13≤next.pc; omega
  have before : s.core.pc≤11 := by omega
  obtain ⟨scratch,arena,lane,cell,active,row,col⟩ := control
  obtain ⟨idx,scale,baseAdded,complete⟩ := ready
  generalize here : s.core.pc=j at fetch past before
  interval_cases j <;> simp only [program,CellPrologue.program,CellGather.code,List.map_cons,List.map_nil,
    List.cons_append,List.nil_append,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.some.injEq,
    Instr.gather.injEq] at fetch
  all_goals try cases fetch
  all_goals cases step
  all_goals try cases ‹Concurrent.Data _ _ _ _›
  all_goals try cases ‹PTX.Eval _ _ _›
  all_goals simp_all [IndexReady,Indexed.mad,Indexed.wide,assign,advance,Function.update,
    Operand.eval,indexWord,indexScale,Kernel.u32,BitVec.setWidth_setWidth_of_le]

variable {n : Nat} {s t : State n} {out : Outcome n} {cfg : Concurrent.Config n}
  {ctx : Fin n → CellPrologue.Context}

theorem index_step (actual : Step cfg ctx (program width cells source) selected s out)
    (aligned : Concurrent.Aligned s.core) (control : ∀ u, Ready (ctx u) width (lane s u))
    (ready : ∀ u, IndexReady (ctx u) width cells (lane s u)) :
    ∀ u, IndexReady (ctx u) width cells (lane out.state u) := by
  intro owner
  obtain ⟨fresh,i,fetch,dispatch⟩ := actual
  cases dispatch with
  | setup he =>
    by_cases same : owner=selected
    · subst owner
      have next := setup_next he
      have before := setup_pc fetch
      apply index_outside; left
      simp only [lane,setLane,Concurrent.setLane,Function.update_self]
      change (lane s selected).core.pc<7 at before
      omega
    · simpa [lane,setLane,Concurrent.setLane,Function.update,same] using ready owner
  | gather he =>
    by_cases same : owner=selected
    · subst owner
      simpa only [lane,Concurrent.setLane,Function.update_self] using
        gather_index (control selected) (ready selected) fetch he
    · simpa [lane,Concurrent.setLane,Function.update,same] using ready owner
  | skip =>
    have pc := skip_pc fetch
    have target : ‹Nat›=20 := by simpa [pc,program,CellPrologue.program,CellGather.code] using fetch.symm
    by_cases same : owner=selected
    · subst owner
      apply index_outside
      simp [lane,Concurrent.setLane,pc,target]
      cases s.live selected <;> decide
    · simpa [lane,Concurrent.setLane,Function.update,same] using ready owner
  | sync =>
    simp only [synchronize,Concurrent.synchronize]
    split
    · exact ready owner
    · exact ready owner
    · rename_i released
      have pc := (Concurrent.release_aligned cfg s.core selected 0 aligned released owner).trans (sync_pc fetch)
      apply index_outside; right
      change 13≤(s.core.lanes owner).pc+1
      omega

theorem index_run (run : Runs cfg ctx (program width cells source) s events indices t)
    (aligned : Concurrent.Aligned s.core) (control : ∀ u, Ready (ctx u) width (lane s u))
    (ready : ∀ u, IndexReady (ctx u) width cells (lane s u))
    (positive : 0<width) (fits : width*width<2^32) :
    ∀ u, IndexReady (ctx u) width cells (lane t u) := by
  induction run with
  | nil => exact ready
  | cons one _ ih =>
    exact ih (step_aligned one aligned) (step one aligned control positive fits)
      (index_step one aligned control ready)

end PtxTorchLean.Poisson.PTX.CellEntry.Control
