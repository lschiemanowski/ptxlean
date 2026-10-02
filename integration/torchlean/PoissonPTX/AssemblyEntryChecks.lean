import PoissonPTX.AssemblyEntryExists
import PoissonPTX.AssemblyInactive
import PoissonPTX.AssemblyChecks

namespace PtxTorchLean.Poisson.PTX.Assembly.EntryChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-- One node with three contributions and one boundary flag. -/
def memory (reordered boundary : Bool) : Memory :=
  write32 (write32 (write32 (Checks.memory reordered) 64 0) 68 3) 72 (if boundary then 1 else 0)

def start (reordered boundary : Bool) : Flow.State :=
  {Checks.start reordered with core:={(Checks.start reordered).core with global:=memory reordered boundary,globalBytes:=88}}

def ctx : Kernel.Context := ⟨0,0,0⟩
def code (masked : Bool) := entryCode 1 64 0 32 masked 72 80
def candidate (reordered boundary masked : Bool) := Flow.execute ctx (code masked) 70 (start reordered boundary)
def result (reordered boundary masked : Bool) := (candidate reordered boundary masked).getD (start reordered boundary)

theorem executed (reordered boundary masked : Bool) :
    candidate reordered boundary masked=some (result reordered boundary masked) := by
  have yes : (candidate reordered boundary masked).isSome=true := by
    cases reordered <;> cases boundary <;> cases masked <;> decide +kernel
  cases h : candidate reordered boundary masked with
  | none => simp [h] at yes
  | some out => simp [result,h]

theorem actual (reordered boundary masked : Bool) :
    Flow.Runs ctx (code masked) (start reordered boundary) (result reordered boundary masked) ∧
      (result reordered boundary masked).halted=true := Flow.execute_sound (executed reordered boundary masked)

theorem stored : decode (read64 (result false false false).core.global 80)=0 ∧
    decode (read64 (result true false false).core.global 80)=1 ∧
    decode (read64 (result true true true).core.global 80)=0 ∧
    decode (read64 (result true false true).core.global 80)=1 := by decide +kernel

def layout (reordered boundary : Bool) : Layout (ready ctx 1 64 (start reordered boundary)).core 0 32 := by
  refine ⟨3,3,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals cases reordered <;> cases boundary <;> decide +kernel

theorem full_result (reordered boundary masked : Bool) :
    ∃ word, (result reordered boundary masked).core.global=write64 (start reordered boundary).core.global 80 word ∧
      decode word=entryValue ctx 1 64 0 32 masked 72 (start reordered boundary) := by
  apply entry_written (actual reordered boundary masked).1 rfl rfl (actual reordered boundary masked).2
    (by unfold Kernel.Residual.live; decide +kernel) (by unfold PrepareValid; cases reordered <;> cases boundary <;> decide +kernel) (layout reordered boundary)
    (by cases reordered <;> cases boundary <;> decide +kernel)
    (by intro _; cases reordered <;> cases boundary <;> decide +kernel)
    (by cases reordered <;> cases boundary <;> decide +kernel)

theorem exists_for_inputs (reordered boundary masked : Bool) :
    ∃ t, Flow.Runs ctx (code masked) (start reordered boundary) t ∧ t.halted=true := by
  exact entry_exists _ rfl rfl (by unfold Kernel.Residual.live; decide +kernel)
    (by unfold PrepareValid; cases reordered <;> cases boundary <;> decide +kernel) (layout reordered boundary)
    (by cases reordered <;> cases boundary <;> decide +kernel)
    (by intro _; cases reordered <;> cases boundary <;> decide +kernel)
    (by cases reordered <;> cases boundary <;> decide +kernel)

/-- Launch padding can return with no allocated global memory at all. -/
theorem padding : (Flow.execute ⟨0,1,0⟩ (code true) 6
    {start false false with core:={(start false false).core with globalBytes:=0}}).isSome=true := by decide +kernel

theorem bad_offset_rejected : Flow.execute ctx (code false) 70
    {start false false with core:={(start false false).core with globalBytes:=64}}=none := by decide +kernel

theorem bad_output_rejected : Flow.execute ctx (code false) 70
    {start false false with core:={(start false false).core with globalBytes:=80}}=none := by decide +kernel

theorem bad_index_rejected : Flow.execute ctx (code false) 70
    {start false false with core:={(start false false).core with global:=write32 (memory false false) 0 20}}=none := by decide +kernel

end PtxTorchLean.Poisson.PTX.Assembly.EntryChecks
