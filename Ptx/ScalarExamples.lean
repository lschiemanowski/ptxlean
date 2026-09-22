import Ptx.ScalarKernels
import Ptx.ScalarText

/-! Kernel-checked boundary regressions for the scalar machine. These initial
register values belong to individual examples; they are not PTX initialization defaults. -/
namespace Ptx.Scalar.Examples

open Kernels

/-- This example explicitly supplies every initial register and predicate. -/
def initial (memory : List Word) (count : Word := 0) (accumulator : Word := 0)
    (pointer : Address := 0) : State :=
  ⟨0, fun register => if register = 0 then count else if register = 1 then accumulator else 0,
    fun _ => pointer, fun _ => false, memory⟩

/-- Empty traversal does not dereference even an invalid, misaligned cursor. -/
theorem zero_count_no_access :
    let result := run 3 sumLoop (initial [] 0 17 3)
    result.status = .halted ∧ result.state.regs 1 = 17 ∧
      result.trace.filterMap Occurrence.memory = [] := by decide

/-- Three executed loads and additions wrap modulo 2^32, preserving the input. -/
theorem modular_sum :
    let result := run 24 sumLoop (initial [4294967295, 2, 4] 3 10)
    result.status = .halted ∧ result.state.regs 1 = 15 ∧
      result.state.memory = [4294967295, 2, 4] := by decide

/-- An incomplete budget and a completed run of the same program stay distinct. -/
theorem fuel_exhaustion_is_not_halt :
    (run 2 sumLoop (initial [7] 1)).status = .exhausted ∧
    (run 2 sumLoop (initial [7] 1)).status ≠ .halted ∧
    (run 10 sumLoop (initial [7] 1)).status = .halted := by decide

def loadThenExit (pointer : Address) : List Instr :=
  [.plain (.load 0 (.imm pointer)), .plain .exit]

theorem misaligned_load_fault :
    (run 2 (loadThenExit 2) (initial [7])).status = .fault (.misaligned 2) := by decide

theorem out_of_bounds_load_fault :
    (run 2 (loadThenExit 4) (initial [7])).status = .fault (.outOfBounds 4) := by decide

/-- False predication skips the invalid address, then the actual exit runs. -/
theorem skipped_load_no_fault :
    let result := run 2 [⟨.pred 0 true, .load 0 (.imm 3)⟩, .plain .exit] (initial [])
    result.status = .halted ∧ result.trace.filterMap Occurrence.memory = [] ∧
      result.state.regs 0 = 0 := by decide

theorem invalid_pc_is_explicit :
    (run 1 [] (initial [])).status = .fault (.invalidPC 0) := by decide

/-- Unknown instruction legality cannot be hidden behind a false predicate. -/
theorem unsupported_is_explicit :
    (run 1 [⟨.pred 0 true, .unsupported "bar.sync"⟩] (initial [])).status =
      .unsupported "bar.sync" := by decide

/-- The actual kernel instruction lists cross the typed mnemonic boundary exactly. -/
theorem add_lane_text_roundtrip :
    addLane.map (fun instruction => Text.decode (Text.encode instruction)) =
      addLane.map (fun instruction => (Except.ok instruction : Except Text.DecodeError Instr)) := rfl

theorem sum_loop_text_roundtrip :
    sumLoop.map (fun instruction => Text.decode (Text.encode instruction)) =
      sumLoop.map (fun instruction => (Except.ok instruction : Except Text.DecodeError Instr)) := rfl

end Ptx.Scalar.Examples
