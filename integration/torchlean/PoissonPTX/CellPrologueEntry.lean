import PoissonPTX.CellPrologue

namespace PtxTorchLean.Poisson.PTX.CellPrologue

/-- Register and live-predicate contract before gather. Neither a barrier reset
nor gathered shared bytes are part of this contract. -/
structure Ready (width : Nat) (ctx : Context) (s : State) : Prop where
  pc : s.core.pc=7
  arena : s.core.regs 0=ctx.arena
  scratch : s.core.regs 3=ctx.scratch
  lane : s.core.regs 14=ctx.lane.setWidth 64
  cell : s.core.regs 15=ctx.cell.setWidth 64
  row : s.core.regs 16=BitVec.ofNat 64 (ctx.lane.toNat/width)
  column : s.core.regs 17=BitVec.ofNat 64 (ctx.lane.toNat%width)
  live : s.live=decide (ctx.lane.toNat<width*width)

theorem ready (run : Runs ctx (program width) 7 s t) (pc : s.core.pc=0)
    (positive : 0<width) (fits : width*width<2^32) : Ready width ctx t := by
  rw [fetched_correct run pc positive fits]
  constructor <;> simp [finish,pc]

/-- Active lanes' division/remainder coordinates are within the cell and
reconstruct exactly the original row-major lane index. -/
theorem coordinates (run : Runs ctx (program width) 7 s t) (pc : s.core.pc=0)
    (positive : 0<width) (fits : width*width<2^32) (active : t.live=true) :
    ctx.lane.toNat/width<width ∧ ctx.lane.toNat%width<width ∧
      ctx.lane.toNat/width*width+ctx.lane.toNat%width=ctx.lane.toNat := by
  have h := ready run pc positive fits
  rw [h.live] at active
  have bound : ctx.lane.toNat<width*width := of_decide_eq_true active
  exact ⟨(Nat.div_lt_iff_lt_mul positive).mpr bound,Nat.mod_lt _ positive,
    Nat.div_add_mod' _ _⟩

/-- Special-register inputs for one 32-thread cell. -/
def threadContext (bases : Space → Word) (cell : BitVec 32) (thread : Fin 32) : Context :=
  ⟨bases .global,bases .shared,BitVec.ofNat 32 thread.val,cell⟩

/-- The actual prologue produces all six registers used by the arithmetic
entry contract; preserving them through the gather is a separate obligation. -/
theorem thread_registers
    (run : Runs (threadContext bases cell thread) (program width) 7 s t) (pc : s.core.pc=0)
    (positive : 0<width) (fits : width*width<2^32) :
    t.core.regs 0=bases .global ∧ t.core.regs 3=bases .shared ∧
    t.core.regs 14=BitVec.ofNat 64 thread.val ∧ t.core.regs 15=cell.setWidth 64 ∧
    t.core.regs 16=BitVec.ofNat 64 (thread.val/width) ∧
    t.core.regs 17=BitVec.ofNat 64 (thread.val%width) ∧
    t.live=decide (thread.val<width*width) := by
  have h := ready run pc positive fits
  have lane : (BitVec.ofNat 32 thread.val).toNat=thread.val := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := thread.isLt; omega)]
  have extend : (BitVec.ofNat 32 thread.val).setWidth 64=BitVec.ofNat 64 thread.val := by
    apply BitVec.eq_of_toNat_eq
    simp [lane]
  have all := And.intro h.arena (And.intro h.scratch (And.intro h.lane
    (And.intro h.cell (And.intro h.row (And.intro h.column h.live)))))
  simpa [threadContext,lane,extend] using all

/-- Renderer follows the same typed instruction list as the fetched proof. -/
def render : Instr → String
  | .context dst .arena => s!"ld.param.u64 {Text.register dst}, [arena];"
  | .context dst .scratch => s!"mov.u64 {Text.register dst}, scratch;"
  | .context dst .lane => s!"mov.u32 {Text.register dst}, %tid.x;"
  | .context dst .cell => s!"mov.u32 {Text.register dst}, %ctaid.x;"
  | .lt32 src limit => s!"setp.lt.u32 %live, {Text.register src}, {limit.toNat};"
  | .div32 dst src divisor => s!"div.u32 {Text.register dst}, {Text.register src}, {divisor.toNat};"
  | .rem32 dst src divisor => s!"rem.u32 {Text.register dst}, {Text.register src}, {divisor.toNat};"

def rendered (width : Nat) : List String := (program width).map render

end PtxTorchLean.Poisson.PTX.CellPrologue
