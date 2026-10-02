import PoissonPTX.CellEntryBarrier
import PoissonPTX.CellEntryLaunch
import PoissonPTX.CellEntryStoreValue

namespace PtxTorchLean.Poisson.PTX.CellEntry.Control
open Ptx

/-- Facts established progressively by the seven actual setup instructions.
These registers and the branch flag never depend on loaded memory values. -/
def Ready (ctx : CellPrologue.Context) (width : Nat) (s : CellPrologue.State) : Prop :=
  (1≤s.core.pc → s.core.regs 3=ctx.scratch) ∧
  (2≤s.core.pc → s.core.regs 0=ctx.arena) ∧
  (3≤s.core.pc → s.core.regs 14=ctx.lane.setWidth 64) ∧
  (4≤s.core.pc → s.core.regs 15=ctx.cell.setWidth 64) ∧
  (5≤s.core.pc → s.live=decide (ctx.lane.toNat<width*width)) ∧
  (6≤s.core.pc → s.core.regs 16=BitVec.ofNat 64 (ctx.lane.toNat/width)) ∧
  (7≤s.core.pc → s.core.regs 17=BitVec.ofNat 64 (ctx.lane.toNat%width))

theorem initial (pc : s.core.pc=0) : Ready ctx width s := by simp [Ready,pc]

/-- Once all setup instructions have run, moving the counter cannot lose the
established facts. This lemma alone makes no claim about an actual transition. -/
theorem later (ready : Ready ctx width s) (past : 7≤s.core.pc)
    (regs : t.core.regs=s.core.regs) (live : t.live=s.live) : Ready ctx width t := by
  rcases ready with ⟨scratch,arena,lane,cell,active,row,col⟩
  refine ⟨fun _ => regs ▸ scratch (by omega),fun _ => regs ▸ arena (by omega),
    fun _ => regs ▸ lane (by omega),fun _ => regs ▸ cell (by omega),
    fun _ => live ▸ active (by omega),fun _ => regs ▸ row (by omega),fun _ => regs ▸ col past⟩

/-- Inspect the actual fetched setup opcode, rather than presuming its results. -/
theorem setup (ready : Ready ctx width s)
    (fetch : (program width cells source)[s.core.pc]?=some (.setup op))
    (step : CellPrologue.eval ctx op s=some t) (positive : 0<width) (fits : width*width<2^32) :
    Ready ctx width t := by
  have small : width<2^32 := by nlinarith
  have val : (BitVec.ofNat 32 width).toNat=width := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  have count : (BitVec.ofNat 32 (width*width)).toNat=width*width := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt fits]
  have nonzero : BitVec.ofNat 32 width≠0#32 := by
    intro h; have := congrArg BitVec.toNat h; simp [val] at this; omega
  have laneMod : ctx.lane.toNat%4294967296=ctx.lane.toNat := Nat.mod_eq_of_lt ctx.lane.isLt
  have bound := (List.getElem?_eq_some_iff.mp fetch).1
  rw [program_length] at bound
  generalize here : s.core.pc=j at fetch bound
  interval_cases j <;> simp only [program,CellPrologue.program,CellGather.code,List.map_cons,List.map_nil,
    List.cons_append,List.nil_append,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.some.injEq,
    Instr.setup.injEq] at fetch
  all_goals try cases fetch
  all_goals simp_all [Ready,CellPrologue.eval,CellPrologue.assign,CellPrologue.Context.value,
    PTX.assign,advance,Kernel.u32,BitVec.toNat_setWidth,nonzero,val,count,laneMod]

  all_goals subst t
  all_goals simp_all [Function.update,Nat.mod_eq_of_lt fits,Nat.mod_eq_of_lt small]

def preserves (r : Nat) : Indexed.Instr → Prop
  | .data op => SharedStore.keeps r op
  | .mad32 dst _ _ _ | .wide4 dst _ | .load32 dst _ => r≠dst

theorem preserves_data (step : Indexed.Candidate.Data i s t access index) (kept : preserves r i) :
    t.regs r=s.regs r := by
  cases step with
  | data hd => exact Concurrent.Address.data_keeps hd kept
  | _ => simp_all [preserves,assign,advance,Function.update]

theorem gather_preserves (member : i∈CellGather.code width cells source)
    (reg : r=0 ∨ r=3 ∨ r=14 ∨ r=15 ∨ r=16 ∨ r=17) : preserves r i := by
  simp only [CellGather.code,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals rcases reg with rfl|rfl|rfl|rfl|rfl|rfl <;> simp [preserves,SharedStore.keeps]

theorem gather (ready : Ready ctx width s) (past : 7≤s.core.pc)
    (member : i∈CellGather.code width cells source)
    (step : Indexed.Candidate.Data i s.core next access index) : Ready ctx width ⟨next,s.live⟩ := by
  rcases ready with ⟨scratch,arena,lane,cell,active,row,col⟩
  have kept r (reg : r=0 ∨ r=3 ∨ r=14 ∨ r=15 ∨ r=16 ∨ r=17) :=
    preserves_data step (gather_preserves member reg)
  exact ⟨fun _ => (kept 3 (by simp)).trans (scratch (by omega)),
    fun _ => (kept 0 (by simp)).trans (arena (by omega)),
    fun _ => (kept 14 (by simp)).trans (lane (by omega)),
    fun _ => (kept 15 (by simp)).trans (cell (by omega)),
    fun _ => active (by omega),fun _ => (kept 16 (by simp)).trans (row (by omega)),
    fun _ => (kept 17 (by simp)).trans (col past)⟩

theorem gather_past (fetch : (program width cells source)[pc]?=some (.gather op)) : 7≤pc := by
  by_contra early
  have bound : pc≤6 := by omega
  interval_cases pc <;> simp_all [program,CellPrologue.program,CellGather.code]

theorem skip_pc (fetch : (program width cells source)[pc]?=some (.skip target)) : pc=7 := by
  have bound := (List.getElem?_eq_some_iff.mp fetch).1
  rw [program_length] at bound
  interval_cases pc <;> simp_all [program,CellPrologue.program,CellGather.code]

theorem sync_pc (fetch : (program width cells source)[pc]?=some .sync) : pc=20 := by
  have bound := (List.getElem?_eq_some_iff.mp fetch).1
  rw [program_length] at bound
  interval_cases pc <;> simp_all [program,CellPrologue.program,CellGather.code]

variable {n : Nat} {s t : State n} {out : Outcome n} {cfg : Concurrent.Config n}
  {ctx : Fin n → CellPrologue.Context}

/-- Candidate load words are unrestricted in this control proof. -/
theorem step (actual : Step cfg ctx (program width cells source) selected s out)
    (aligned : Concurrent.Aligned s.core) (ready : ∀ u, Ready (ctx u) width (lane s u))
    (positive : 0<width) (fits : width*width<2^32) :
    ∀ u, Ready (ctx u) width (lane out.state u) := by
  intro owner
  obtain ⟨fresh,i,fetch,dispatch⟩ := actual
  cases dispatch with
  | setup he =>
    by_cases same : owner=selected
    · subst owner
      simpa only [lane,setLane,Concurrent.setLane,Function.update_self] using
        setup (ready selected) fetch he positive fits
    · simpa [lane,setLane,Concurrent.setLane,Function.update,same] using ready owner
  | gather he =>
    by_cases same : owner=selected
    · subst owner
      simpa only [lane,Concurrent.setLane,Function.update_self] using
        gather (ready selected) (gather_past fetch) (gather_member fetch) he
    · simpa [lane,Concurrent.setLane,Function.update,same] using ready owner
  | skip =>
    by_cases same : owner=selected
    · subst owner
      apply later (ready selected) (by change 7≤(s.core.lanes selected).pc; rw [skip_pc fetch])
      · simp [lane,Concurrent.setLane]
      · rfl
    · simpa [lane,Concurrent.setLane,Function.update,same] using ready owner
  | sync =>
    simp only [synchronize,Concurrent.synchronize]
    split
    · exact ready owner
    · exact ready owner
    · rename_i released
      have pc := (Concurrent.release_aligned cfg s.core selected 0 aligned released owner).trans (sync_pc fetch)
      apply later (ready owner) (by change 7≤(s.core.lanes owner).pc; omega) <;> rfl

/-- Control invariants are established by actual instructions from counter zero,
without any compatibility or memory-value assumption. -/
theorem from_run (run : Runs cfg ctx (program width cells source) s events indices t)
    (aligned : Concurrent.Aligned s.core) (ready : ∀ u, Ready (ctx u) width (lane s u))
    (positive : 0<width) (fits : width*width<2^32) :
    ∀ u, Ready (ctx u) width (lane t u) := by
  induction run with
  | nil => exact ready
  | cons one _ ih => exact ih (step_aligned one aligned) (step one aligned ready positive fits)

/-- Derive the continuation's address/control registers without admitting any
input reads first. This prevents circular use of input correctness to justify
the output addresses needed for the input-source separation proof. -/
theorem launch {s t : State 32} {cfg : Concurrent.Config 32}
    (run : Runs cfg (CellPrologue.threadContext bases cell) (program width cells source) s events indices t)
    (aligned : Concurrent.Aligned s.core) (pcs : ∀ u, (s.core.lanes u).pc=0)
    (done : ∀ u, (t.core.lanes u).pc=21) (positive : 0<width) (fits : width*width<2^32)
    (space : (bases .shared).toNat+7*width*width*8≤2^64) :
    Nonempty (Concurrent.CellMiddle.Numeric.Launch width bases (resume t)) := by
  have ready := from_run run aligned (fun u => initial (s:=lane s u) (pcs u)) positive fits
  obtain ⟨allPC,site,generation,key,barrier,_,_⟩ := completed_barrier run aligned
    (fun u => by rw [pcs]; omega) (0 : Fin 32) (by rw [done]; omega)
  have before (u : Fin 32) : 7≤(lane t u).core.pc := by change 7≤(t.core.lanes u).pc; rw [done]; decide
  refine ⟨⟨generation+1,barrier,?_,?_,?_,?_,?_,?_,space⟩⟩
  · intro u; simp [resume,done]
  · intro u; exact (ready u).2.1 (by have := before u; omega)
  · intro u; exact (ready u).1 (by have := before u; omega)
  · intro u
    have h := (ready u).2.2.1 (by have := before u; omega)
    have small : u.val<4294967296 := by have := u.isLt; omega
    have large : u.val<18446744073709551616 := by have := u.isLt; omega
    have widened : (BitVec.ofNat 32 u.val).setWidth 64=BitVec.ofNat 64 u.val := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_setWidth,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,Nat.mod_eq_of_lt large]
    simpa only [resume,lane,CellPrologue.threadContext,widened] using h
  · intro u
    have h := (ready u).2.2.2.2.2.1 (by have := before u; omega)
    simpa only [resume,lane,context_lane] using h
  · intro u
    have h := (ready u).2.2.2.2.2.2 (before u)
    simpa only [resume,lane,context_lane] using h

end PtxTorchLean.Poisson.PTX.CellEntry.Control
