import PoissonPTX.CellEntryIndexInputs

namespace PtxTorchLean.Poisson.PTX.CellEntry.Control

def nodeWord (memory : Memory) (ctx : CellPrologue.Context) (width : Nat) (cells : Word) : BitVec 32 :=
  read32 memory (ctx.arena+indexScale ctx width+cells).toNat

def sourceScale (memory : Memory) (ctx : CellPrologue.Context) (width : Nat) (cells : Word) : Word :=
  BitVec.ofNat 64 ((nodeWord memory ctx width cells).toNat*8)

/-- After the justified four-byte read, these registers describe the source
address. No eight-byte source value is assumed. -/
def SourceReady (memory : Memory) (ctx : CellPrologue.Context) (width : Nat) (cells source : Word)
    (s : CellPrologue.State) : Prop :=
  (13≤s.core.pc → s.core.pc≤16 → s.core.regs 18=(nodeWord memory ctx width cells).setWidth 64) ∧
  (14≤s.core.pc → s.core.pc≤15 → s.core.regs 1=sourceScale memory ctx width cells) ∧
  (s.core.pc=15 → s.core.regs 2=ctx.arena+sourceScale memory ctx width cells) ∧
  (s.core.pc=16 → s.core.regs 2=ctx.arena+sourceScale memory ctx width cells+source)

theorem source_initial (pc : s.core.pc=0) : SourceReady memory ctx width cells source s := by
  simp [SourceReady,pc]

theorem source_outside (low : s.core.pc≤12 ∨ 17≤s.core.pc) : SourceReady memory ctx width cells source s := by
  rcases low with low|high <;> simp only [SourceReady] <;> omega

theorem gather_source (control : Ready ctx width s) (index : IndexReady ctx width cells s)
    (ready : SourceReady memory ctx width cells source s)
    (fetch : (program width cells source)[s.core.pc]?=some (.gather op))
    (step : Indexed.Candidate.Data op s.core next access ix)
    (values : ∀ a, ix=some a → a.value=read32 memory a.address) :
    SourceReady memory ctx width cells source ⟨next,s.live⟩ := by
  have nextPC := Indexed.Candidate.data_pc step
  by_cases early : s.core.pc≤11
  · apply source_outside; left; change next.pc≤12; omega
  by_cases late : 16≤s.core.pc
  · apply source_outside; right; change 17≤next.pc; omega
  have lo : 12≤s.core.pc := by omega
  have hi : s.core.pc≤15 := by omega
  obtain ⟨scratch,arena,lane,cell,active,row,col⟩ := control
  obtain ⟨idx,scale,baseAdded,complete⟩ := index
  obtain ⟨node,bytes,sourceBase,sourceComplete⟩ := ready
  generalize here : s.core.pc=j at fetch lo hi
  interval_cases j <;> simp only [program,CellPrologue.program,CellGather.code,List.map_cons,List.map_nil,
    List.cons_append,List.nil_append,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.some.injEq,
    Instr.gather.injEq] at fetch
  all_goals cases fetch
  all_goals cases step
  all_goals try cases ‹Concurrent.Data _ _ _ _›
  all_goals try cases ‹PTX.Eval _ _ _›
  all_goals simp_all [SourceReady,assign,advance,Function.update,Operand.eval,sourceScale,nodeWord]
  all_goals simp only [show ∀ v : BitVec 32, v.toNat%4294967296=v.toNat from
    fun v => Nat.mod_eq_of_lt v.isLt]

variable {n : Nat} {s t : State n} {out : Outcome n} {cfg : Concurrent.Config n}
  {ctx : Fin n → CellPrologue.Context}

theorem source_step (actual : Step cfg ctx (program width cells source) selected s out)
    (aligned : Concurrent.Aligned s.core) (control : ∀ u, Ready (ctx u) width (lane s u))
    (index : ∀ u, IndexReady (ctx u) width cells (lane s u))
    (ready : ∀ u, SourceReady memory (ctx u) width cells source (lane s u))
    (values : Indices memory out.indices) :
    ∀ u, SourceReady memory (ctx u) width cells source (lane out.state u) := by
  intro owner
  obtain ⟨fresh,i,fetch,dispatch⟩ := actual
  cases dispatch with
  | setup he =>
    by_cases same : owner=selected
    · subst owner
      have next := setup_next he
      have before := setup_pc fetch
      apply source_outside; left
      simp only [lane,setLane,Concurrent.setLane,Function.update_self]
      change (lane s selected).core.pc<7 at before
      omega
    · simpa [lane,setLane,Concurrent.setLane,Function.update,same] using ready owner
  | gather he =>
    by_cases same : owner=selected
    · subst owner
      simpa only [lane,Concurrent.setLane,Function.update_self] using
        gather_source (control selected) (index selected) (ready selected) fetch he
          (fun a ha => values selected a (by simp [ha]))
    · simpa [lane,Concurrent.setLane,Function.update,same] using ready owner
  | skip =>
    have pc := skip_pc fetch
    have target : ‹Nat›=20 := by simpa [pc,program,CellPrologue.program,CellGather.code] using fetch.symm
    by_cases same : owner=selected
    · subst owner
      apply source_outside
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
      apply source_outside; right
      change 17≤(s.core.lanes owner).pc+1
      omega

end PtxTorchLean.Poisson.PTX.CellEntry.Control
