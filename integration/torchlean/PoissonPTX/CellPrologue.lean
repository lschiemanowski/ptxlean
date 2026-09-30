import PoissonPTX.CellLaunch
import PoissonPTX.Text

namespace PtxTorchLean.Poisson.PTX.CellPrologue

/-- Launch and symbol resolution inputs. Resolving the parameter, special
registers and shared symbol is not a CUDA driver/ABI theorem. -/
structure Context where
  arena : Word
  scratch : Word
  lane : BitVec 32
  cell : BitVec 32

inductive Source where
  | arena | scratch | lane | cell
  deriving DecidableEq, Repr

def Context.value (ctx : Context) : Source → Word
  | .arena => ctx.arena
  | .scratch => ctx.scratch
  | .lane => ctx.lane.setWidth 64
  | .cell => ctx.cell.setWidth 64

/-- Only the nonbranching entry forms used by the element kernel. A zero
unsigned divisor has no supported step; no claim about its unspecified result
is made. This does not extend the ISA coverage ledger. -/
inductive Instr where
  | context (dst : Nat) (source : Source)
  | lt32 (src : Nat) (limit : BitVec 32)
  | div32 (dst src : Nat) (divisor : BitVec 32)
  | rem32 (dst src : Nat) (divisor : BitVec 32)
  deriving DecidableEq, Repr

structure State where
  core : PTX.State
  live : Bool

def assign (s : State) (dst : Nat) (value : Word) : State :=
  {s with core:=PTX.assign s.core dst value}

def eval (ctx : Context) : Instr → State → Option State
  | .context dst source, s => some (assign s dst (ctx.value source))
  | .lt32 src limit, s => some {core:=PTX.advance s.core, live:=decide ((Kernel.u32 (s.core.regs src)).toNat<limit.toNat)}
  | .div32 dst src divisor, s => if divisor=0 then none else
      some (assign s dst (BitVec.ofNat 64 ((Kernel.u32 (s.core.regs src)).toNat/divisor.toNat)))
  | .rem32 dst src divisor, s => if divisor=0 then none else
      some (assign s dst (BitVec.ofNat 64 ((Kernel.u32 (s.core.regs src)).toNat%divisor.toNat)))

def Step (ctx : Context) (program : List Instr) (s t : State) : Prop :=
  ∃ i, program[s.core.pc]?=some i ∧ eval ctx i s=some t

inductive Runs (ctx : Context) (program : List Instr) : Nat → State → State → Prop where
  | nil : Runs ctx program 0 s s
  | cons : Step ctx program s t → Runs ctx program fuel t u → Runs ctx program (fuel+1) s u

def execute (ctx : Context) (program : List Instr) : Nat → State → Option State
  | 0,s => some s
  | fuel+1,s => do
    let i ← program[s.core.pc]?
    let t ← eval ctx i s
    execute ctx program fuel t

theorem execute_sound (h : execute ctx program fuel s=some t) : Runs ctx program fuel s t := by
  induction fuel generalizing s with
  | zero => simp [execute] at h; subst t; exact .nil
  | succ fuel ih =>
    cases fetch : program[s.core.pc]? with
    | none => simp [execute,fetch] at h
    | some i =>
      cases step : eval ctx i s with
      | none => simp [execute,fetch,step] at h
      | some middle =>
        exact .cons ⟨i,fetch,step⟩ (ih (by simpa [execute,fetch,step] using h))

theorem execute_complete (run : Runs ctx program fuel s t) : execute ctx program fuel s=some t := by
  induction run with
  | nil => rfl
  | cons step _ ih =>
    obtain ⟨i,fetch,step⟩ := step
    simp [execute,fetch,step,ih]

/-- The actual seven entry instructions, before the first guarded gather. -/
def program (width : Nat) : List Instr :=
  [.context 3 .scratch,.context 0 .arena,.context 14 .lane,.context 15 .cell,
   .lt32 14 (BitVec.ofNat 32 (width*width)),
   .div32 16 14 (BitVec.ofNat 32 width),.rem32 17 14 (BitVec.ofNat 32 width)]

def finish (ctx : Context) (width : Nat) (s : State) : State :=
  let regs := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update s.core.regs 3 ctx.scratch) 0 ctx.arena)
    14 (ctx.lane.setWidth 64)) 15 (ctx.cell.setWidth 64))
    16 (BitVec.ofNat 64 (ctx.lane.toNat/width))) 17 (BitVec.ofNat 64 (ctx.lane.toNat%width))
  {core:={s.core with pc:=s.core.pc+7, regs:=regs}, live:=decide (ctx.lane.toNat<width*width)}

/-- Nonzero widths and 32-bit live counts cover Q1--Q4 without depending on
any initial register or memory content. -/
theorem execution (ctx : Context) (s : State) (pc : s.core.pc=0)
    (positive : 0<width) (fits : width*width<2^32) :
    execute ctx (program width) 7 s=some (finish ctx width s) := by
  have small : width<2^32 := by nlinarith
  have val : (BitVec.ofNat 32 width).toNat=width := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  have count : (BitVec.ofNat 32 (width*width)).toNat=width*width := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt fits]
  have nonzero : BitVec.ofNat 32 width≠0 := by
    intro h; have := congrArg BitVec.toNat h; simp [val] at this; omega
  change BitVec.ofNat 32 width ≠ 0#32 at nonzero
  have lane : ctx.lane.toNat % 4294967296=ctx.lane.toNat := Nat.mod_eq_of_lt ctx.lane.isLt
  simp [execute,program,eval,assign,PTX.assign,PTX.advance,Context.value,
    Kernel.u32,finish,pc,lane,val,count,nonzero]

theorem fetched_exists (ctx : Context) (s : State) (pc : s.core.pc=0)
    (positive : 0<width) (fits : width*width<2^32) :
    Runs ctx (program width) 7 s (finish ctx width s) :=
  execute_sound (execution ctx s pc positive fits)

theorem fetched_correct (run : Runs ctx (program width) 7 s t) (pc : s.core.pc=0)
    (positive : 0<width) (fits : width*width<2^32) : t=finish ctx width s := by
  have a := execute_complete run
  rw [execution ctx s pc positive fits] at a
  exact (Option.some.inj a).symm

/-- These instructions do not load or store global or shared array bytes. -/
theorem memories (run : Runs ctx (program width) 7 s t) (pc : s.core.pc=0)
    (positive : 0<width) (fits : width*width<2^32) :
    t.core.global=s.core.global ∧ t.core.shared=s.core.shared := by
  rw [fetched_correct run pc positive fits]; exact ⟨rfl,rfl⟩

theorem other_register (run : Runs ctx (program width) 7 s t) (pc : s.core.pc=0)
    (positive : 0<width) (fits : width*width<2^32)
    (other : r≠0 ∧ r≠3 ∧ r≠14 ∧ r≠15 ∧ r≠16 ∧ r≠17) :
    t.core.regs r=s.core.regs r := by
  rw [fetched_correct run pc positive fits]; simp [finish,Function.update,other]

end PtxTorchLean.Poisson.PTX.CellPrologue
