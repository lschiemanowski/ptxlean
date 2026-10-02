import PoissonPTX.AssemblyLayout

namespace PtxTorchLean.Poisson.PTX.Assembly.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def memory (reordered : Bool) : Memory :=
  write64 (write64 (write64
    (write32 (write32 (write32 (fun _ => 0) 0 (if reordered then 2 else 0))
      4 (if reordered then 0 else 1)) 8 (if reordered then 1 else 2))
    32 0x4340000000000000) 40 0x3ff0000000000000) 48 0xc340000000000000

def start (reordered : Bool) : Flow.State :=
  ⟨{pc:=0,regs:=fun r => if r=20 then 3 else 0,global:=memory reordered,shared:=fun _ => 0,
    globalStart:=0,globalBytes:=64,sharedStart:=0,sharedBytes:=0},fun _ => false,false⟩
def ctx : Kernel.Context := ⟨0,0,0⟩
def code := Flow.Loop.program 19 20 (body 0 32)
def candidate (reordered : Bool) := Flow.execute ctx code 43 (start reordered)
def result (reordered : Bool) := (candidate reordered).getD (start reordered)

theorem executed (reordered : Bool) : candidate reordered=some (result reordered) := by
  have yes : (candidate reordered).isSome=true := by cases reordered <;> decide +kernel
  cases h : candidate reordered with
  | none => simp [h] at yes
  | some out => simp [result,h]

theorem actual (reordered : Bool) : Flow.Runs ctx code (start reordered) (result reordered) ∧
    (result reordered).halted=true := Flow.execute_sound (executed reordered)

/-- Same three contributions, different order: no associativity is used. -/
theorem cancellation : decode ((result false).core.regs 8)=0 ∧
    decode ((result true).core.regs 8)=1 := by decide +kernel

def layout (reordered : Bool) : Layout (start reordered).core 0 32 := by
  refine ⟨3,3,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals cases reordered <;> decide +kernel

theorem fold_result (reordered : Bool) : decode ((result reordered).core.regs 8)=
    (List.range' 0 3).foldl (fun acc k => acc+contribution (start reordered).core 0 32 k) 0 := by
  have h := layout_correct (actual reordered).1 rfl rfl (actual reordered).2 (by decide +revert) (layout reordered)
  have zero : decode ((start reordered).core.regs 8)=(0 : Float) := by cases reordered <;> decide +kernel
  rw [zero] at h
  simpa [cursor,limit,start,Kernel.u32] using h

/-- Early exhaustion of witness-search fuel is failure, not a partial answer. -/
theorem fuel_rejected : Flow.execute ctx code 41 (start false)=none := by decide +kernel

theorem bad_index_rejected : Flow.execute ctx code 43
    {start false with core:={(start false).core with global:=write32 (memory false) 0 4}}=none := by decide +kernel

theorem empty : Flow.execute ctx code 3
    {start false with core:={(start false).core with regs:=fun _ => 0}}=
    some {core:={(start false).core with pc:=14,regs:=fun _ => 0},predicates:=Function.update (fun _ => false) 0 true,halted:=true} := by rfl

end PtxTorchLean.Poisson.PTX.Assembly.Checks
