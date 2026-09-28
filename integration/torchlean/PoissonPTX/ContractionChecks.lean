import PoissonPTX.ContractionFetched
import PoissonPTX.ContractionLayout
import PoissonPTX.ContractionText

namespace PtxTorchLean.Poisson.PTX.Contraction.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def memory4 (a b c d : Word) : Memory :=
  write64 (write64 (write64 (write64 (fun _=>0) 0 a) 8 b) 16 c) 24 d

def state : State where
  pc := 0
  regs := fun r => if r=16 then 1 else if r=8 || r=9 then 0x7ff0000000000000 else 0
  global := memory4 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 0x4010000000000000
  shared := memory4 0x4014000000000000 0x4018000000000000 0x401c000000000000 0x4020000000000000
  globalStart := 0
  globalBytes := 32
  sharedStart := 0
  sharedBytes := 32

def a : Matrix := ⟨.global,0,.row,.inner⟩
def b : Matrix := ⟨.shared,0,.inner,.column⟩

theorem matrix_coordinate :
    (run (program 2 8 a b) state).map (fun s => s.regs 8) = some 0x4045800000000000 := by
  decide +kernel

theorem second_accumulator :
    (run (program 2 9 a b) state).map (fun s => s.regs 9) = some 0x4045800000000000 := by
  decide +kernel

/-- A wrong shared plane is rejected at the actual load, not treated as zero. -/
theorem outside_shared_rejected :
    run (program 2 8 a {b with offset:=32}) state = none := by decide +kernel

theorem unaligned_rejected :
    run (program 2 8 {a with offset:=1} b) state = none := by decide +kernel

theorem index_wrap : mul32 0xffffffff 2 = 0xfffffffe ∧ add32 0xffffffff 1 = 0 := by decide +kernel

/-- Cancellation preserves sequential addition, rather than regrouping products. -/
def cancellation : State :=
  {state with
    regs := fun _=>0
    globalBytes := 72
    sharedBytes := 72
    global := write64 (write64 (write64 (fun _=>0) 0 0x4341c37937e08000) 8 0x3ff0000000000000) 16 0xc341c37937e08000
    shared := write64 (write64 (write64 (fun _=>0) 0 0x3ff0000000000000) 24 0x3ff0000000000000) 48 0x3ff0000000000000}

theorem cancellation_order :
    (run (program 3 8 a b) cancellation).map (fun s => s.regs 8) = some 0 := by decide +kernel

theorem all_plans_have_eight_blocks :
    (plans 2 0 32).length=8 ∧ (plans 5 0 200).length=8 := by decide +kernel

end PtxTorchLean.Poisson.PTX.Contraction.Checks
